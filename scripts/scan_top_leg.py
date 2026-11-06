# Quick non-rigorous scan (Arb, 53-bit): top-leg candidates T2 with Re zeta(sigma+iT2) > 0 on [1/2,2]
from flint import acb, ctx
ctx.prec = 53
def leg_min(T2, m):
    return min((float(acb(0.5 + 1.5*j/m, T2).zeta().real.mid()), 0.5 + 1.5*j/m) for j in range(m+1))
for T, nxt in ((1000, 1001.3494826), (10000, 10000.0653454)):
    best = max(((leg_min(T + (nxt - 1e-3 - T)*i/40, 300)), T + (nxt - 1e-3 - T)*i/40) for i in range(41))
    (mn, sg), T2 = best
    print(f"T={T}: best T2={T2:.6f} coarse min Re zeta={mn:.4f} at sigma={sg:.3f}; fine min={leg_min(T2, 3000)[0]:.4f}", flush=True)
