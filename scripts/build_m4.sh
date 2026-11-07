#!/usr/bin/env bash
# Driver for the full build (M3 and M4): for each range, the leg chunks and certificate modules with at most P
# concurrent `lake build`s (scripts/build_limited.sh), then the legs' top modules, the window count
# and the solution one at a time; finally Count10000Solution. Finished modules are skipped, so it
# can be rerun after an interruption. P = 3 below 6000 and 2 above (about 8 GB per process near
# t = 10^4, on a 32 GB laptop). Usage: scripts/build_m4.sh > build.log 2>&1
cd "$(dirname "$0")/.."
rng() { a=$1; b=$2; P=$3; shift 3
  mods=""
  for leg in "$@"; do for f in ZetaCert/Legs/$leg/L*.lean; do mods="$mods ZetaCert.Legs.$leg.$(basename $f .lean)"; done; done
  n=$(ls ZetaCert/Zeros${a}to${b}/Z*.lean | wc -l)
  for j in $(seq 0 $((n-1))); do mods="$mods ZetaCert.Zeros${a}to${b}.Z$j"; done
  echo "== $a-$b $(date +%T)"
  scripts/build_limited.sh $P $mods | grep FAIL
  for leg in "$@"; do scripts/build_limited.sh 1 ZetaCert.Legs.$leg | grep FAIL; done
  scripts/build_limited.sh 1 ZetaCert.Windows.W${a}to${b} Zeros${a}to${b}Solution
}
# shared dependencies first, in one process (ZetaCert.BernTable alone takes about 10 GB)
echo "== deps $(date +%T)"
scripts/build_limited.sh 1 "ZetaCert.Window ZetaCert.Leg ZetaCert.Assembly ZetaCert.LegCertSound ZetaCert.OnLine"
# range 0-1000 (certificates in ZetaCert/Zeros1000, leg ZetaCert/Leg1000)
echo "== 0-1000 $(date +%T)"
mods=""; for f in ZetaCert/Leg1000/L*.lean ZetaCert/Zeros1000/Z*.lean; do m=${f%.lean}; mods="$mods ${m//\//.}"; done
scripts/build_limited.sh 3 $mods | grep FAIL
scripts/build_limited.sh 1 ZetaCert.Leg1000 ZetaCert.Count1000 Zeros0to1000Solution
rng 1000 2000 3 B1000 B2000
rng 2000 3000 3 B3000
rng 3000 4000 3 B4000U
rng 4000 5000 3 B4000L B5000
rng 5000 6000 3 B6000
rng 6000 7000 2 B7000
rng 7000 8000 2 B8000U
rng 8000 9000 2 B8000L B9000
rng 9000 10000 2 B10000U
scripts/build_limited.sh 1 Count10000Solution
echo "== done $(date +%T)"
