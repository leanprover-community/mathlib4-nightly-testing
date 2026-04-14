#!/usr/bin/env python3
"""
Fix non-local breakage from set_option removal.

Given failing modules, this script:
1. Adds the option to all their Mathlib dependencies that don't already have it
2. Verifies the failing modules build
3. Bisect-removes the newly-added options (leaving pre-existing ones untouched)

After finding each must-keep, the bisect restarts from scratch on the remaining
candidates (rather than continuing to bisect the current subtree).

Pre-existing options (already committed) are never removed, only newly-added
ones are candidates for bisect removal.

Usage:
    python3 scripts/fix_nonlocal_set_option.py MODULE1 MODULE2 ...
"""

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

from dag_traversal import DAG
from set_option_utils import PROJECT_DIR
from add_module_set_option import add_to_file
from rm_module_set_option import module_set_option_pattern


DEFAULT_OPTION = "backward.defeq.atInstanceTransparency"

# Global build counter
_build_count = 0
_build_start_time = 0.0


def _elapsed() -> str:
    """Return elapsed time since start as HH:MM:SS."""
    elapsed = time.time() - _build_start_time
    h, rem = divmod(int(elapsed), 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}"


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


_last_failed_module: str | None = None

# Dedicated cache directory for bisect runs (wipeable, sandbox-friendly)
_BISECT_CACHE_DIR = PROJECT_DIR / "_bisect_cache"


def _lake_env() -> dict[str, str]:
    """Environment variables for lake build with local artifact cache."""
    env = dict(os.environ)
    env["LAKE_ARTIFACT_CACHE"] = "true"
    env["LAKE_CACHE_DIR"] = str(_BISECT_CACHE_DIR)
    return env


def lake_build_modules(modules: list[str], timeout: int = 600) -> bool:
    """Build specific modules. Returns True if all succeed.

    Tries the last-failed module first to fail fast.
    Uses a local Lake artifact cache for content-hash based olean reuse.
    """
    global _build_count, _last_failed_module
    _build_count += 1

    # Reorder: try last-failed module first
    ordered = list(modules)
    if _last_failed_module and _last_failed_module in ordered:
        ordered.remove(_last_failed_module)
        ordered.insert(0, _last_failed_module)

    env = _lake_env()
    for mod in ordered:
        result = subprocess.run(
            ["lake", "build", mod],
            cwd=PROJECT_DIR,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
        if result.returncode != 0:
            _last_failed_module = mod
            return False
    _last_failed_module = None
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


def _find_one_must_keep(
    dag: DAG,
    candidates: list[str],
    check_modules: list[str],
    option: str,
    timeout: int,
    total_candidates: int,
    already_resolved: int,
    found_so_far: int,
    _known_fail: bool = False,
) -> tuple[str | None, list[str]]:
    """Find a single must-keep module via binary search.

    Returns (must_keep, unresolved) where:
    - must_keep: the module name, or None if all candidates can be removed
    - unresolved: candidates not yet resolved (need further bisection)

    After return, all resolved-as-removable candidates have been removed
    from disk. The must-keep (if any) still has its option.

    already_resolved: number of candidates already resolved (removed or kept)
                      in earlier rounds/siblings, for progress display.
    """
    if not candidates:
        return None, []

    pct = 100.0 * already_resolved / total_candidates if total_candidates else 0

    if not _known_fail:
        print(f"    [{_elapsed()}] build#{_build_count+1} "
              f"try removing {len(candidates)} "
              f"({pct:.0f}% resolved, {found_so_far} kept)",
              flush=True)
        originals = _remove_options(dag, candidates, option)

        if lake_build_modules(check_modules, timeout):
            print(f"    [{_elapsed()}] All {len(candidates)} removed!", flush=True)
            return None, []

        # Revert all
        _revert_options(dag, originals)
        lake_build_modules(check_modules, timeout)

    if len(candidates) == 1:
        print(f"    [{_elapsed()}] *** Must keep: {candidates[0]} ***", flush=True)
        return candidates[0], []

    # Split and try left half
    mid = len(candidates) // 2
    left = candidates[:mid]
    right = candidates[mid:]

    print(f"    [{_elapsed()}] build#{_build_count+1} "
          f"try left {len(left)}/{len(candidates)} "
          f"({pct:.0f}% resolved, {found_so_far} kept)",
          flush=True)
    left_originals = _remove_options(dag, left, option)

    left_ok = lake_build_modules(check_modules, timeout)
    if not left_ok:
        # Left half has a must-keep; revert and recurse into left
        # Right half is unresolved
        _revert_options(dag, left_originals)
        lake_build_modules(check_modules, timeout)
        found, left_unresolved = _find_one_must_keep(
            dag, left, check_modules, option, timeout,
            total_candidates, already_resolved, found_so_far,
            _known_fail=True)
        return found, left_unresolved + right

    # Left removed OK (stays removed). Update resolved count.
    resolved_after_left = already_resolved + len(left)
    pct_after_left = 100.0 * resolved_after_left / total_candidates if total_candidates else 0

    print(f"    [{_elapsed()}] build#{_build_count+1} "
          f"try right {len(right)}/{len(candidates)} "
          f"({pct_after_left:.0f}% resolved, {found_so_far} kept)",
          flush=True)
    right_originals = _remove_options(dag, right, option)

    right_ok = lake_build_modules(check_modules, timeout)
    if not right_ok:
        # Right half has a must-keep; revert right and recurse
        _revert_options(dag, right_originals)
        lake_build_modules(check_modules, timeout)
        found, right_unresolved = _find_one_must_keep(
            dag, right, check_modules, option, timeout,
            total_candidates, resolved_after_left, found_so_far,
            _known_fail=True)
        return found, right_unresolved

    # Both halves removed OK
    return None, []


def minimize_with_restart(
    dag: DAG,
    candidates: list[str],
    check_modules: list[str],
    option: str,
    timeout: int,
) -> list[str]:
    """Find minimal set of must-keep modules using bisect-with-restart.

    After finding each must-keep, restarts bisection from scratch on
    the remaining candidates. This avoids wasting time on right-half
    cascades deep in the tree.
    """
    global _build_start_time
    _build_start_time = time.time()

    remaining = list(candidates)
    total = len(candidates)
    needed: list[str] = []

    while remaining:
        print(f"\n  [{_elapsed()}] === Round {len(needed)+1}: "
              f"{len(remaining)} candidates remaining, "
              f"{len(needed)} found so far ===",
              flush=True)

        found, unresolved = _find_one_must_keep(
            dag, remaining, check_modules, option, timeout,
            total_candidates=total,
            already_resolved=total - len(remaining),
            found_so_far=len(needed),
        )

        if found is None:
            # All remaining were removed successfully
            print(f"  [{_elapsed()}] All remaining {len(remaining)} removed!",
                  flush=True)
            break

        needed.append(found)
        # Continue with only the unresolved candidates (not the full list).
        # Successfully removed candidates stay removed on disk.
        remaining = unresolved

        # Sanity check: with the must-keep in place and all remaining
        # candidates still present, the build should succeed.
        # If it doesn't, something is wrong (stale oleans, unrelated failure).
        if remaining:
            print(f"    [{_elapsed()}] Sanity check: verifying build with "
                  f"{len(needed)} kept + {len(remaining)} remaining...",
                  flush=True)
            if not lake_build_modules(check_modules, timeout):
                print(f"    [{_elapsed()}] ERROR: sanity check failed!")
                print(f"    Build fails even with all remaining candidates present.")
                print(f"    This suggests a problem unrelated to bisection.")
                print(f"    Stopping. Found so far: {needed}")
                break

    return needed


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
    print(f"  Verifying build of {len(check_modules)} modules...", flush=True)
    if not lake_build_modules(check_modules, args.timeout):
        print("  ERROR: modules still fail after adding option to all deps!")
        print("  Cannot proceed.")
        return

    print(f"  Build OK. Now bisect-removing {len(newly_added)} newly-added options...",
          flush=True)
    print(f"  (Pre-existing {pre_existing} options are untouched.)", flush=True)

    # Step 3: minimize with restart-after-find
    needed = minimize_with_restart(
        dag, newly_added, check_modules, option, args.timeout)

    removed_count = len(newly_added) - len(needed)
    print(f"\n{'='*60}")
    print("RESULT")
    print(f"{'='*60}")
    print(f"  Elapsed:                {_elapsed()}")
    print(f"  Builds:                 {_build_count}")
    print(f"  Check modules:          {len(check_modules)}")
    print(f"  Pre-existing (kept):    {pre_existing}")
    print(f"  Newly added:            {len(newly_added)}")
    print(f"  Removed (unnecessary):  {removed_count}")
    print(f"  Kept (needed):          {len(needed)}")
    if needed:
        print("\n  Needed modules (newly identified):")
        for n in needed:
            print(f"    - {n}")

    # Remind about bisect cache
    if _BISECT_CACHE_DIR.exists():
        print(f"\n  NOTE: Bisect cache still at {_BISECT_CACHE_DIR}")
        print(f"  Remove manually when done: rm -rf {_BISECT_CACHE_DIR}")


if __name__ == "__main__":
    main()
