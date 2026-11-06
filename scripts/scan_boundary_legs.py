# Non-rigorous scan (Arb, 53 bits) for the range challenges: for each boundary B = 1000 j,
# find heights T near B, in zero-free gaps, with Re zeta(sigma + iT) > 0 for sigma in [1/2, 2]
# (the hypothesis of zeta-lab's exact_argument). Reports the first such gap at or above B.
from flint import acb, ctx
ctx.prec = 53

def load(paths):
    out = []
    for p in paths:
        for line in open(p):
            if not line.startswith('#'):
                k, g, r = line.split()
                out.append((int(k), float(g)))
    out.sort()
    return out

def leg_min(T, m=300):
    return min(float(acb(0.5 + 1.5 * j / m, T).zeta().real.mid()) for j in range(m + 1))

zs = load(["data/zeros_T10000.txt", "data/zeros_above_10000.txt"])
gam = [g for _, g in zs]
for B in range(1000, 11000, 1000):
    i = next(i for i, g in enumerate(gam) if g > B)          # first zero above B
    for gap in range(i - 1, min(i + 6, len(gam) - 1)):
        a, b = gam[gap], gam[gap + 1]
        if b <= B: continue
        lo = max(a, B)
        cands = [lo + (b - lo) * k / 24 for k in range(1, 24)]
        best = max((leg_min(T), T) for T in cands)
        if best[0] > 0.05:
            n_below = gap + 1                                 # zeros with ordinate < T
            print(f"B={B}: T={best[1]:.4f} in gap ({a:.4f}, {b:.4f}); min Re zeta on leg ~ {best[0]:.3f}; "
                  f"N(T) = {n_below}; zeros in (B, T]: {sum(1 for g in gam if B < g <= best[1])}", flush=True)
            break
    else:
        print(f"B={B}: no positive leg found in the first gaps above B", flush=True)
