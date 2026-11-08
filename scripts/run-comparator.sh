#!/usr/bin/env bash
# Run Comparator (with NanoDa) on one configuration, using the tools built in .cache/comparator
# (comparator and lean4export at tag v4.35.0-rc2, nanoda_lib 68d5ca9, landrun 811cfff; see
# vendor-src/zeta-23-lean/zeta23/scripts/verify-comparator.sh for the original layout).
#   scripts/run-comparator.sh challenge/comparator-Zeros0to1000.json
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
C="$root/.cache/comparator"
cfg=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
cd "$root"
PALOMAR_LANDRUN_BIN="$C/bin/landrun" \
COMPARATOR_LEAN4EXPORT="$C/lean4export/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="${COMPARATOR_NANODA:-$C/nanoda/target/release/nanoda_bin}" \
COMPARATOR_LANDRUN="$root/scripts/landrun-wrapper.sh" \
  lake env "$C/comparator/.lake/build/bin/comparator" "$cfg"
