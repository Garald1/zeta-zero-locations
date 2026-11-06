#!/usr/bin/env bash
# Kernel benchmarks for ZetaEval2 (Lean 4 core only; tested with Lean v4.36.0-rc2).
# Usage: bash prototype/run_bench.sh   (needs `lean` on PATH, e.g. via elan)
set -euo pipefail
cd "$(dirname "$0")"
lean -o ZetaEval2.olean ZetaEval2.lean
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
for f in B2_1000 B2_10000; do echo "== $f"; time lean "$f.lean"; done
echo "== B2_1000_bad (must be rejected)"
if lean B2_1000_bad.lean >/dev/null 2>&1; then echo "UNEXPECTED: accepted"; exit 1; else echo "rejected, as expected"; fi
