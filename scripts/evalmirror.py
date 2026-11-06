"""Bit-exact Python mirror of ZetaCert/Eval/Core.lean (candidate data and testing only).

The Lean kernel re-does every computation; this file only predicts its output.
"""
from mpmath import mp, mpf, log, sqrt, zeta, exp, mpc
import math

P = 128
O = 2**192
O2 = 2**193
ONE = 2**128
KO = 2**384 + 2**320
OP = 2**320
NTAYLOR = 24


def nsub(a, b):
    return a - b if a >= b else 0


def addO(X, Y): return nsub(X + Y, O)
def subO(X, Y): return nsub(X + O, Y)
def mulO(X, Y): return nsub(X * Y + KO, (X + Y) << 192) >> 128
def mulOP(X, y): return nsub(X * y + OP, y << 192) >> 128
def mulPP(x, y): return (x * y) >> 128


def taylorI(x, fuel, j, t, rp, rn, ip, im):
    while fuel > 0:
        r = j % 4
        if r == 0: rp += t
        elif r == 1: im += t
        elif r == 2: rn += t
        else: ip += t
        t = mulPP(t, x) // (j + 1)
        j += 1
        fuel -= 1
    return nsub(rp + O, rn), nsub(ip + O, im)


def sqIter(k, a, b):
    for _ in range(k):
        re = subO(mulO(a, a), mulO(b, b))
        ab = mulO(a, b)
        im = addO(ab, ab)
        if re + im == 0:
            return 0, 0
        a, b = re, im
    return a, b


def expNegI(K, T, L):
    x = (T * L) >> (128 + K)
    if x > 2**125:
        return 0, 0
    c, s = taylorI(x, NTAYLOR, 0, ONE, 0, 0, 0, 0)
    return sqIter(K, c, s)


def primeTerm(K, T, w, L):
    c, s = expNegI(K, T, L)
    return mulOP(c, w), mulOP(s, w)


def isqrt(n):
    return math.isqrt(n)


def primes_upto(N):
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N**0.5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]


def prime_data(N):
    """(p, w, L): w = floor(2^128 / sqrt p) (so w^2 p <= 2^256 < (w+1)^2 p), L = round(2^128 log p)."""
    mp.dps = 80
    out = []
    for p in primes_upto(N):
        w = isqrt(2**256 // p)
        while (w + 1)**2 * p <= 2**256: w += 1
        while w * w * p > 2**256: w -= 1
        L = int(mp.nint(log(p) * 2**128))
        out.append((p, w, L))
    return out


def sums(N, K, T, primes):
    pts = []
    for (p, w, L) in primes:
        re, im = primeTerm(K, T, w, L)
        if re == 0:
            break
        pts.append((p, L, re, im))
    acc = [ONE + O, O, O, O]

    def push(ur, ui, ln):
        acc[0] = addO(acc[0], ur); acc[1] = addO(acc[1], ui)
        acc[2] = subO(acc[2], mulOP(ur, ln)); acc[3] = subO(acc[3], mulOP(ui, ln))

    def go(i, m, ur, ui, lm):
        while i < len(pts):
            p, L, qr, qi = pts[i]
            n = m * p
            if n > N:
                return
            vr = subO(mulO(ur, qr), mulO(ui, qi))
            vi = addO(mulO(ur, qi), mulO(ui, qr))
            ln = lm + L
            push(vr, vi, ln)
            go(i, n, vr, vi, ln)
            i += 1
    import sys
    sys.setrecursionlimit(10000)
    go(0, 1, ONE + O, O, 0)
    return acc


def dec(X):
    return mpf(X - O) / 2**128


if __name__ == "__main__":
    import sys
    t = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf('999.791571557412940463163147')
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 350
    mp.dps = 60
    T = int(mp.nint(t * 2**128))
    tt = mpf(T) / 2**128
    K = max(0, math.ceil(math.log2(float(tt) * math.log(N))) + 4)
    pr = prime_data(N)
    acc = sums(N, K, T, pr)
    s = mpc(mpf(1)/2, tt)
    S = sum(mpf(n)**(-s) for n in range(1, N + 1))
    D = sum(-log(n) * mpf(n)**(-s) for n in range(1, N + 1))
    print("K =", K)
    print("S err", abs(mpc(dec(acc[0]), dec(acc[1])) - S))
    print("D err", abs(mpc(dec(acc[2]), dec(acc[3])) - D))
