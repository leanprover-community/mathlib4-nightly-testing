#!/usr/bin/env bash
#
# dump_decls.sh — dump the public declarations of every built Mathlib module.
#
# For each module `Mathlib.Foo.Bar` it runs the `printDecls` executable and writes
# the result to `./decls/Mathlib.Foo.Bar.txt` (one `name : type` line per
# non-internal, non-private declaration the module adds).
#
# Run from the repository root:
#
#     scripts/dump_decls.sh
#
# Options (environment variables):
#     JOBS=N      number of parallel workers for the main pass (default: 6).
#                 Each worker imports a full module with all extension state
#                 loaded, which is memory-hungry; too many workers can trigger
#                 OOM kills. Transient failures are retried automatically at
#                 lower concurrency, so the main knob is just throughput.
#     OUTDIR=dir  output directory (default: decls)
#     PREFIX=p    only dump modules whose name starts with `p`
#                 (e.g. PREFIX=Mathlib.Topology)
#
# Modules that still fail after the retry passes are listed in
# `<OUTDIR>/FAILED.txt`, with per-module stderr kept in `<OUTDIR>/<module>.err`.

set -uo pipefail

OUTDIR="${OUTDIR:-decls}"
JOBS="${JOBS:-6}"
PREFIX="${PREFIX:-Mathlib}"

# Build the tool once, then resolve the binary and search path so that the
# thousands of invocations below skip per-call `lake` overhead.
lake build printDecls || { echo "failed to build printDecls" >&2; exit 1; }
BIN="$PWD/.lake/build/bin/printDecls"
export BIN OUTDIR
export LEAN_PATH; LEAN_PATH="$(lake env printenv LEAN_PATH)"

mkdir -p "$OUTDIR"

# Worker invoked by xargs for a single module name. On failure (e.g. an OOM
# kill under load) the module name is appended to $FAILLIST for a later retry.
dump_one() {
  local mod="$1"
  if "$BIN" "$mod" > "$OUTDIR/$mod.txt" 2> "$OUTDIR/$mod.err"; then
    rm -f "$OUTDIR/$mod.err"
  else
    echo "$mod" >> "$FAILLIST"   # short line, O_APPEND -> atomic across workers
  fi
}
export -f dump_one

# run_pass <jobs> <faillist> : read module names from stdin, dump each, and
# leave the names that failed in <faillist> (deduplicated).
run_pass() {
  export FAILLIST="$2"
  : > "$FAILLIST"
  xargs -P "$1" -I{} bash -c 'dump_one "$@"' _ {}
  sort -u "$FAILLIST" -o "$FAILLIST"
}

# Enumerate modules from source files: `Mathlib/Foo/Bar.lean` -> `Mathlib.Foo.Bar`.
todo="$(mktemp)"
find Mathlib -name '*.lean' \
  | sed 's/\.lean$//; s#/#.#g' \
  | grep "^${PREFIX//./\\.}" \
  | sort > "$todo"
echo "Dumping $(wc -l < "$todo") modules with $JOBS workers (+ retry passes)..."

# Main pass, then retries at decreasing concurrency to mop up transient OOM kills.
fail="$(mktemp)"
for jobs in "$JOBS" 2 1; do
  run_pass "$jobs" "$fail" < "$todo"
  n=$(wc -l < "$fail")
  [ "$n" -eq 0 ] && break
  echo "  $n module(s) failed; retrying at $([ "$jobs" = "$JOBS" ] && echo 2 || echo 1) worker(s)..."
  cp "$fail" "$todo"
done

if [ -s "$fail" ]; then
  cp "$fail" "$OUTDIR/FAILED.txt"
  echo "Done with $(wc -l < "$fail") persistent failure(s); see $OUTDIR/FAILED.txt and *.err."
else
  rm -f "$OUTDIR/FAILED.txt"
  echo "Done. Wrote $(find "$OUTDIR" -name '*.txt' | wc -l) files to $OUTDIR/ with no failures."
fi
