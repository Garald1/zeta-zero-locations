"""Generate a kernel benchmark for ZetaCert/Eval/Core.lean: checks `sums` equals the mirror's output."""
import sys, math
sys.path.insert(0, 'scripts')
from evalmirror import *
from mpmath import mp, mpf
t = mpf(sys.argv[1]); N = int(sys.argv[2]); out = sys.argv[3]
mp.dps = 60
T = int(mp.nint(t * 2**128)); tt = mpf(T)/2**128
K = max(0, math.ceil(math.log2(float(tt) * math.log(N))) + 4)
pr = prime_data(N)
acc = sums(N, K, T, pr)
with open(out, 'w') as f:
    f.write("import ZetaCert.Eval.Core\nopen ZetaCert.Eval\n\n")
    chunks = [pr[i:i+300] for i in range(0, len(pr), 300)]
    for ci, ch in enumerate(chunks):
        f.write(f"def pd{ci} : List (Nat × Nat × Nat) := [\n" + ",\n".join(f"  ({p}, {w}, {L})" for p, w, L in ch) + "]\n\n")
    f.write("def pd : List (Nat × Nat × Nat) := " + " ++ ".join(f"pd{i}" for i in range(len(chunks))) + "\n\n")
    f.write(f"theorem bench : (let a := sums {N} {K} {T} 2000 pd; a.sr == {acc[0]} && a.si == {acc[1]} && a.dr == {acc[2]} && a.di == {acc[3]}) = true := by decide +kernel\n")
