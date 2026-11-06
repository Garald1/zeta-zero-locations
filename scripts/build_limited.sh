#!/usr/bin/env bash
# Build the given Lean modules with at most P concurrent `lake build` processes (P = $1).
# Heavy `decide +kernel` modules near t = 10^4 take about 8 GB each; plain `lake build` runs one
# job per core and can exhaust memory. Finished modules are not rebuilt.
# Usage: scripts/build_limited.sh P Module1 Module2 ...
P=$1; shift
printf '%s\n' "$@" | xargs -P "$P" -I{} sh -c 'lake build {} > /dev/null 2>&1 && echo "ok {}" || echo "FAIL {}"'
