# Generate table literals and kernel benchmarks for ZetaEval.lean
import sys
from mpmath import mp, mpf, log, sqrt, pi, floor

mp.prec = 200
P = 80
SCALE = mpf(2) ** P

def fx(x):
    return int(floor(x * SCALE + mpf(1) / 2))

def table_chunks(N, chunk=400):
    entries = []
    for n in range(1, N):
        entries.append(f"⟨⟨{fx(log(n))}, 1⟩, ⟨{fx(1/sqrt(n))}, 1⟩⟩")
    return [entries[i:i + chunk] for i in range(0, len(entries), chunk)]

def write_bench(name, N, ts):
    chunks = table_chunks(N)
    lines = ["import ZetaEval", "open ZB", "", f"def twoPi : Ball := ⟨{fx(2 * pi)}, 1⟩", ""]
    for i, ch in enumerate(chunks):
        lines.append(f"def tab{i} : List Entry := [\n  " + ",\n  ".join(ch) + "]")
        lines.append("")
    lines.append("def tab : List Entry := " + " ++ ".join(f"tab{i}" for i in range(len(chunks))))
    lines.append("")
    for j, t in enumerate(ts):
        lines.append(f"-- t = {t}")
        lines.append(f"theorem bench{j} : check twoPi {fx(mpf(t))} tab = true := by decide +kernel")
        lines.append("")
    open(f"{name}.lean", "w").write("\n".join(lines))

if __name__ == "__main__":
    # zeros near height 1000 and 10000 (approximate values are enough for timing)
    write_bench("Bench1000", 350, ["999.79157155741294046", "998.18063432902466", "996.96866667050418"])
    write_bench("Bench10000", 3500, ["9998.8503970896740491"])
