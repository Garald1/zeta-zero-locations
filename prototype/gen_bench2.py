# Generate benchmarks for ZetaEval2.lean: prime tables and expected values
from mpmath import mp, mpf, mpc, log, sqrt, pi, floor, power
mp.prec = 300
P, Q = 96, 128
S = mpf(2) ** P
O = 2 ** Q

def plain(x):
    return int(floor(x * S + mpf(1) / 2))

def off(x):
    return plain(x) + O

def primes_upto(N):
    sieve = bytearray([1]) * (N + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(N + 1) if sieve[i]]

def expected(N, t):
    s = mpc(mpf(1) / 2, t)
    Ssum, Dsum = mpc(0), mpc(0)
    for n in range(1, N + 1):
        v = power(n, -s)
        Ssum += v
        Dsum -= log(n) * v
    return Ssum, Dsum

def write(name, N, ts, chunk=300):
    ps = primes_upto(N)
    ents = [f"⟨{p}, {plain(log(p))}, {plain(1 / sqrt(p))}⟩" for p in ps]
    chunks = [ents[i:i + chunk] for i in range(0, len(ents), chunk)]
    L = ["import ZetaEval2", "open ZB2", "", f"def twoPi : Nat := {plain(2 * pi)}", ""]
    for i, ch in enumerate(chunks):
        L.append(f"def pr{i} : List PrimeData := [\n  " + ",\n  ".join(ch) + "]")
    L.append("def primes : List PrimeData := " + " ++ ".join(f"pr{i}" for i in range(len(chunks))))
    L.append("")
    for j, t in enumerate(ts):
        tq = plain(mpf(t))           # t is the dyadic rational tq / 2^P exactly
        tex = mpf(tq) / S
        Ssum, Dsum = expected(N, tex)
        L.append(f"-- t = {t}, N = {N}: S = {mp.nstr(Ssum, 15)}, S' = {mp.nstr(Dsum, 15)}")
        L.append(f"theorem bench{j} : check {N} twoPi {tq} primes {off(Ssum.real)} {off(Ssum.imag)} "
                 f"{off(Dsum.real)} {off(Dsum.imag)} {2**40} = true := by decide +kernel")
        L.append("")
    open(f"{name}.lean", "w").write("\n".join(L))
    print(name, "primes:", len(ps))

if __name__ == "__main__":
    write("B2_1000", 350, ["999.79157155741294046"])
    write("B2_10000", 3500, ["9998.8503970896740491"])
