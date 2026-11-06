"""Per-zero certificate parameters for ZetaCert.zc and a Python mirror of the checker.

Candidate data only: the kernel recomputes everything. Usage:
  python3 scripts/zeroparams.py <index> [T]   (T = 1000 or 10000; reads data/zeros_T*.txt)
"""
import sys, math
from fractions import Fraction as Fr
from mpmath import mp, mpf, bernoulli as mbern, factorial as mfact, log as mlog
sys.path.insert(0, 'scripts')
import evalmirror as em
from gen_primedata import primes_upto, entry

mp.dps = 60
PRIMES = primes_upto(4000)
PSET = set(PRIMES)


def load_zeros(T):
    fn = 'data/zeros_T1000.txt' if T == 1000 else 'data/zeros_T10000.txt'
    out = []
    for line in open(fn):
        if line.startswith('#'): continue
        i, g, r = line.split()
        out.append((int(i), g))
    return out


def E0f(N, k, t):
    s = mpf(1) / 2
    pr = mpf(1)
    for i in range(2*k+2): pr *= (s + i + t)
    return pr / mfact(2*k+2) * abs(mbern(2*k+2)) * mpf(N)**(-s-2*k-1) / (2*k + mpf(3)/2)


def E1f(N, k, t):
    pr = mpf(1)
    for i in range(2*k+2): pr *= (i + 1 + t)
    return pr / mfact(2*k+2) * abs(mbern(2*k+2)) / mpf(N)**(2*k+1) / (2*k+1)


def _ok(N, t):
    for k in range(1, 61):
        if E0f(N, k, t) <= mpf('1e-23') and E1f(N, k, t) <= mpf('1e-8'):
            return k
    return None


def choose(t):
    """a small prime N (and k ≤ 60) with E0 ≤ 1e-23 and E1 ≤ 1e-8: binary search over the primes
    (the errors decrease with N); the smallest such N when that predicate is monotone"""
    ps = [p for p in PRIMES if p >= 5]
    lo, hi = 0, len(ps) - 1
    if _ok(ps[hi], t) is None:
        raise ValueError("no parameters")
    while lo < hi:
        mid = (lo + hi) // 2
        if _ok(ps[mid], t) is None: lo = mid + 1
        else: hi = mid
    return ps[lo], _ok(ps[lo], t)


def params(gstr, m):
    g = mpf(gstr)
    G = int(mp.nint(g * 2**80))
    t = mpf(G) / 2**80
    N, k = choose(t)
    K = max(0, math.ceil(math.log2(8 * float(t) * math.log(N)))) + 1
    Dp = N.bit_length()
    return dict(m=m, G=G, N=N, K=K, k=k, fuel=1000, Dp=Dp)


if __name__ == "__main__":
    idx = int(sys.argv[1]); T = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    zs = load_zeros(T)
    i, g = zs[idx - 1]
    m = int(mp.nint(mpf(g) * 10**24))
    print(params(g, m))
