#!/usr/bin/env python3
"""
Fix non-local breakage from set_option removal.

Given failing modules, this script:
1. Adds the option to all their Mathlib dependencies that don't already have it
2. Verifies the failing modules build
3. Bisect-removes the newly-added options (leaving pre-existing ones untouched)

Pre-existing options (already committed) are never removed, only newly-added
ones are candidates for bisect removal.

Usage:
    python3 scripts/fix_nonlocal_set_option.py MODULE1 MODULE2 ...
"""

import argparse
import subprocess
import sys
from pathlib import Path

from dag_traversal import DAG
from set_option_utils import PROJECT_DIR
from add_module_set_option import add_to_file
from rm_module_set_option import module_set_option_pattern


DEFAULT_OPTION = "backward.defeq.atInstanceTransparency"


def collect_all_dependencies(dag: DAG, module_name: str) -> set[str]:
    """Collect all transitive dependencies (imports) of a module."""
    collected: set[str] = set()
    frontier = {module_name}
    while frontier:
        next_frontier: set[str] = set()
        for m in frontier:
            info = dag.modules.get(m)
            if info is None:
                continue
            for imp in info.imports:
                if imp not in collected and imp != module_name:
                    collected.add(imp)
                    next_frontier.add(imp)
        frontier = next_frontier
    return collected


def lake_build_modules(modules: list[str], timeout: int = 600) -> bool:
    """Build specific modules. Returns True if all succeed."""
    for mod in modules:
        result = subprocess.run(
            ["lake", "build", mod],
            cwd=PROJECT_DIR,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if result.returncode != 0:
            return False
    return True


def has_option(filepath: Path, option: str) -> bool:
    """Check if a file has the module-level set_option line."""
    pat = module_set_option_pattern(option)
    text = filepath.read_text()
    for line in text.splitlines():
        if pat.match(line):
            return True
    return False


def remove_option(filepath: Path, option: str) -> str | None:
    """Remove the module-level set_option line. Returns original text or None."""
    pat = module_set_option_pattern(option)
    text = filepath.read_text()
    lines = text.splitlines(keepends=True)
    for i, line in enumerate(lines):
        if pat.match(line.rstrip('\n')):
            new_lines = list(lines)
            del new_lines[i]
            # Remove double blank line
            if (i < len(new_lines) and i > 0
                    and new_lines[i - 1].strip() == ""
                    and new_lines[i].strip() == ""):
                del new_lines[i]
            filepath.write_text("".join(new_lines))
            return text
    return None


def restore_file(filepath: Path, original_text: str):
    """Restore a file to its original content."""
    filepath.write_text(original_text)


def _remove_options(dag: DAG, modules: list[str], option: str) -> dict[str, str]:
    """Remove option from modules. Returns dict of module -> original text."""
    originals: dict[str, str] = {}
    for mod in modules:
        info = dag.modules.get(mod)
        if info is None:
            continue
        fp = dag.project_root / info.filepath
        orig = remove_option(fp, option)
        if orig is not None:
            originals[mod] = orig
    return originals


def _revert_options(dag: DAG, originals: dict[str, str]):
    """Restore files to original content."""
    for mod, orig in originals.items():
        info = dag.modules.get(mod)
        if info:
            restore_file(dag.project_root / info.filepath, orig)


def bisect_remove(
    dag: DAG,
    candidates: list[str],
    check_modules: list[str],
    option: str,
    timeout: int,
    _known_fail: bool = False,
) -> list[str]:
    """Binary-search remove options from candidates while check_modules build.

    Returns list of modules that must keep the option.
    Only candidates (newly-added) are touched; pre-existing options are left alone.
    _known_fail: if True, skip the initial "try removing all" (caller already tried).
    """
    if not candidates:
        return []

    if not _known_fail:
        # Try removing all at once
        print(f"    Trying to remove all {len(candidates)} at once...", flush=True)
        originals = _remove_options(dag, candidates, option)

        if lake_build_modules(check_modules, timeout):
            print(f"    All {len(candidates)} removed successfully!", flush=True)
            return []

        # Revert all
        _revert_options(dag, originals)
        lake_build_modules(check_modules, timeout)

    if len(candidates) == 1:
        print(f"    Must keep: {candidates[0]}", flush=True)
        return candidates

    # Split and recurse
    mid = len(candidates) // 2
    left = candidates[:mid]
    right = candidates[mid:]

    print(f"    Bisecting: trying left half ({len(left)})...", flush=True)
    left_originals = _remove_options(dag, left, option)

    left_ok = lake_build_modules(check_modules, timeout)
    if not left_ok:
        # Revert left, some in left are needed
        _revert_options(dag, left_originals)
        lake_build_modules(check_modules, timeout)
        # Skip initial try in recursive call — we just proved it fails
        needed_left = bisect_remove(dag, left, check_modules, option, timeout,
                                    _known_fail=True)
    else:
        needed_left = []

    # Now try right half (left removals that succeeded are still in effect)
    print(f"    Bisecting: trying right half ({len(right)})...", flush=True)
    right_originals = _remove_options(dag, right, option)

    right_ok = lake_build_modules(check_modules, timeout)
    if not right_ok:
        # Revert right, some in right are needed
        _revert_options(dag, right_originals)
        lake_build_modules(check_modules, timeout)
        needed_right = bisect_remove(dag, right, check_modules, option, timeout,
                                     _known_fail=True)
    else:
        needed_right = []

    return needed_left + needed_right


def main():
    parser = argparse.ArgumentParser(
        description="Fix non-local breakage by adding+minimizing set_option in deps"
    )
    parser.add_argument(
        "modules",
        nargs="+",
        help="Failing module names (e.g. Mathlib.Foo.Bar)",
    )
    parser.add_argument(
        "--option",
        default=DEFAULT_OPTION,
        help=f"Option name (default: {DEFAULT_OPTION})",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=600,
        help="Build timeout per module in seconds (default: 600)",
    )
    args = parser.parse_args()

    option = args.option

    print("Building import DAG...", flush=True)
    dag = DAG.from_directories(PROJECT_DIR)
    print(f"  {len(dag.modules)} modules parsed")

    check_modules = list(args.modules)

    # Step 1: collect all deps of all failing modules
    all_deps: set[str] = set()
    for mod in args.modules:
        all_deps |= collect_all_dependencies(dag, mod)

    # Filter to Mathlib files that don't already have the option
    newly_added: list[str] = []
    pre_existing = 0
    for d in sorted(all_deps):
        info = dag.modules.get(d)
        if info and str(info.filepath).startswith("Mathlib/"):
            fp = dag.project_root / info.filepath
            if fp.exists():
                if has_option(fp, option):
                    pre_existing += 1
                else:
                    if add_to_file(fp, option, dry_run=False):
                        newly_added.append(d)

    print(f"  Pre-existing options in dep cone: {pre_existing}", flush=True)
    print(f"  Newly added options: {len(newly_added)}", flush=True)

    if not newly_added:
        print("  Nothing to add — all deps already have the option.")
        return

    # Step 2: verify all check modules build
    print(f"  Verifying build of {check_modules}...", flush=True)
    if not lake_build_modules(check_modules, args.timeout):
        print("  ERROR: modules still fail after adding option to all deps!")
        print("  Cannot proceed.")
        return

    print(f"  Build OK. Now bisect-removing {len(newly_added)} newly-added options...",
          flush=True)
    print(f"  (Pre-existing {pre_existing} options are untouched.)", flush=True)

    # Step 3: binary search remove unnecessary newly-added options
    needed = bisect_remove(dag, newly_added, check_modules, option, args.timeout)

    removed_count = len(newly_added) - len(needed)
    print(f"\n{'='*60}")
    print("RESULT")
    print(f"{'='*60}")
    print(f"  Check modules:          {len(check_modules)}")
    print(f"  Pre-existing (kept):    {pre_existing}")
    print(f"  Newly added:            {len(newly_added)}")
    print(f"  Removed (unnecessary):  {removed_count}")
    print(f"  Kept (needed):          {len(needed)}")
    if needed:
        print("\n  Needed modules (newly identified):")
        for n in needed:
            print(f"    - {n}")


if __name__ == "__main__":
    main()
