# Non-rigorous scans (Arb at 53-64 bits) used only to choose parameters for the formal proof.
from flint import acb, arb, ctx
ctx.prec = 53
def leg_min(T2, m):
    return min((float(acb(0.5 + 1.5*j/m, T2).zeta().real.mid()), 0.5 + 1.5*j/m) for j in range(m+1))
# zeros above 10^4 (from Arb): find the first gap containing a T2 with Re zeta > 0 on [1/2,2] + i T2
ctx.prec = 96
zs = [float(z.imag.mid()) for z in acb.zeta_zeros(10143, 12)]
ctx.prec = 53
print("zeros 10143..10154:", [round(z, 4) for z in zs])
found = None
for k in range(len(zs) - 1):
    a, b = zs[k], zs[k+1]
    cands = [a + (b - a) * i / 24 for i in range(1, 24)]
    best = max((leg_min(T2, 300)[0], T2) for T2 in cands)
    print(f"gap ({a:.4f}, {b:.4f}) [zeros up to index {10143 + k}]: best coarse min Re = {best[0]:.4f} at T2 = {best[1]:.4f}", flush=True)
    if best[0] > 0.02 and found is None:
        found = (best[1], 10143 + k)
        print("   fine check:", leg_min(best[1], 4000), flush=True)
        break
# |zeta'(rho)| minima and minimal gaps (finite differences, rough)
def load(path):
    return [line.split()[1] for line in open(path) if not line.startswith('#')]
ctx.prec = 64
for path in ("data/zeros_T1000.txt", "data/zeros_T10000.txt"):
    gs = load(path); h = arb("1e-7")
    best = None; gap = None
    prev = None
    for i, g in enumerate(gs):
        t = arb(g)
        d = (acb(arb("0.5"), t + h).zeta() - acb(arb("0.5"), t - h).zeta()) / (2 * h)
        v = float(abs(d).mid())
        if best is None or v < best[0]: best = (v, i + 1, g[:14])
        tf = float(t.mid())
        if prev is not None and (gap is None or tf - prev < gap[0]): gap = (tf - prev, i, g[:14])
        prev = tf
    print(f"{path}: min |zeta'(rho)| ~ {best[0]:.4g} (index {best[1]}, gamma {best[2]}); min gap ~ {gap[0]:.4g} (indices {gap[1]},{gap[1]+1}, gamma {gap[2]})", flush=True)
