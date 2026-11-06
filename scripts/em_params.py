# Size of the Euler-Maclaurin remainder bound of riemannZeta_EM_real (rh-up-to-15-lean, ZetaZeros/EM2.lean)
# R(N,k) = prod_{i<2k+2}(|sigma+i|+|t|) / (2k+2)! * |B_{2k+2}| * N^(-sigma-2k-1) / (sigma+2k+1)
from mpmath import mp, mpf, bernoulli, factorial
mp.dps = 50
def R(N, k, t, sigma=mpf(1)/2):
    pr = mpf(1)
    for i in range(2*k+2): pr *= (abs(sigma+i) + t)
    return pr / factorial(2*k+2) * abs(bernoulli(2*k+2)) * mpf(N)**(-sigma-2*k-1) / (sigma+2*k+1)
for t in (1000.1348, 10000.2608):
    for frac in (0.35, 0.5, 1.0):
        N = int(frac*t)
        k = next(k for k in range(1, 200) if R(N, k, mpf(t)) < mpf('1e-26'))
        print(f"t={t:9.2f}  N={N:5d} ({frac}t): smallest k with bound < 1e-26 is k={k} (Bernoulli up to B_{2*k+2}); bound={float(R(N,k,mpf(t))):.2e}")
