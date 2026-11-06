# Rigorous isolation of the nontrivial zeros of zeta with 0 < Im s <= T, via Arb
# (acb_dirichlet_zeta_zeros: Platt's isolation + Turing's method, ball arithmetic).
# Output: one line per zero, "index  midpoint  radius" for the imaginary part.
import sys, time
from flint import arb, acb, ctx

def run(T, prec_bits, out):
    ctx.prec = prec_bits
    n = int(arb(T).zeta_nzeros().unique_fmpz())
    t0 = time.time()
    zs = acb.zeta_zeros(1, n)
    dt = time.time() - t0
    worst = arb(0)
    with open(out, "w") as f:
        f.write(f"# zeros of zeta with 0 < Im s <= {T}: N = {n}; Arb prec = {prec_bits} bits\n")
        f.write("# index  Im(rho) midpoint  radius   (Re(rho) = 1/2 certified by Arb)\n")
        for k, z in enumerate(zs, 1):
            im = z.imag
            assert z.real.contains(arb(0.5)) and z.real.rad() == 0, k
            f.write(f"{k} {im.mid().str(40, radius=False)} {im.rad().str(3, radius=False)}\n")
            if im.rad() > worst: worst = im.rad()
    print(f"T={T}: N={n}, time {dt:.1f}s, max radius {worst.str(3, radius=False)}; last zero {zs[-1].imag.str(20, radius=False)}", flush=True)
    # sanity: next zero above T
    nxt = acb.zeta_zero(n + 1).imag
    print(f"   next zero {nxt.str(20, radius=False)} > {T}: {bool(nxt > T)}", flush=True)
    return n

if __name__ == "__main__":
    run(1000, 160, "data/zeros_T1000.txt")
    run(10000, 160, "data/zeros_T10000.txt")
