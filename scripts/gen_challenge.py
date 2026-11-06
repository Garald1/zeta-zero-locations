"""Generate challenge/Challenge{1000,10000}.lean and comparator configs from the Arb data.

Each ordinate gamma_k (40 significant digits, Arb radius <= 1.2e-44) is stored as the
integer m_k = round(10^24 * gamma_k); the statement then claims |Im rho - m_k/10^24| <= 10^-20.
"""
from decimal import Decimal, getcontext, ROUND_HALF_EVEN
import json, os
getcontext().prec = 100
SCALE, CHUNK = 24, 300

def load(path):
    rows = []
    for line in open(path):
        if line.startswith('#'):
            continue
        k, g, r = line.split()
        assert len(g.split('.')[1]) >= 30, g          # enough digits to round to 24 decimals
        assert float(r) < 1e-40
        rows.append((int(k), g))
    assert [k for k, _ in rows] == list(range(1, len(rows) + 1))
    return rows

def scaled(g):
    d = Decimal(g) * (Decimal(10) ** SCALE)
    m = int(d.to_integral_value(rounding=ROUND_HALF_EVEN))
    assert abs(abs(d - m) - Decimal('0.5')) > Decimal('1e-10')  # rounding is unambiguous
    return m

HEADER = '''/-
DRAFT. Written in a sandbox without Mathlib: this file has NOT been elaborated yet.
First job (milestone M0): make it elaborate against the pinned Mathlib, changing syntax only.
Never weaken the statements.

Trusted challenge statement (for leanprover/comparator): the location, to within 10^-20, of
every zero of Mathlib's `riemannZeta` with 0 < Im s <= {T}.

Data: `{lst}` lists, in increasing order, the integers m_k nearest to 10^24 * gamma_k, where
gamma_k = Im rho_k for the {n} zeros with 0 < Im rho <= {T}, as computed by Arb
(acb_dirichlet_zeta_zeros, 160-bit ball arithmetic, radius <= 1.2e-44 on each gamma_k).
The list is part of the statement; the proof must not assume it is correct.
-/
import Mathlib

namespace {ns}
'''

FOOTER = '''
/-- `{lst}` = `{parts}` ({n} entries). -/
def {lst} : List ℕ := {parts}

/-- The zeros of `riemannZeta` with `0 < Im s ≤ T` (no condition on `Re s`). -/
def zerosUpTo (T : ℝ) : Set ℂ := {{s | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im ≤ T}}

/-- Every zero of `ζ` with `0 < Im s ≤ {T}` is simple, lies on the critical line, and has its
ordinate within `10⁻²⁰` of `m / 10²⁴` for some `m` in the list. -/
theorem zeros_up_to_{T}_located :
    ∀ s ∈ zerosUpTo {T}, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ {lst}, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 := by
  sorry

/-- For each listed `m`, exactly one zero of `ζ` has its ordinate within `10⁻²⁰` of `m / 10²⁴`. -/
theorem zeros_up_to_{T}_unique :
    ∀ m ∈ {lst}, ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 := by
  sorry

/-- There are exactly {n} zeros of `ζ` with `0 < Im s ≤ {T}`. -/
theorem zeros_up_to_{T}_count : (zerosUpTo {T}).ncard = {n} := by
  sorry

end {ns}
'''

def write(T, path):
    rows = load(path)
    ms = [scaled(g) for _, g in rows]
    assert ms == sorted(ms) and len(set(ms)) == len(ms)
    n, ns, lst = len(ms), f"ZetaZeros{T}", f"ordinates{T}"
    out = [HEADER.format(T=T, n=n, ns=ns, lst=lst)]
    names = []
    for c in range(0, n, CHUNK):
        nm = f"ord{T}_{c // CHUNK}"
        names.append(nm)
        body = ",\n  ".join(str(m) for m in ms[c:c + CHUNK])
        out.append(f"/-- entries {c + 1}..{min(c + CHUNK, n)} -/\ndef {nm} : List ℕ := [\n  {body}]\n")
    out.append(FOOTER.format(T=T, n=n, ns=ns, lst=lst, parts=" ++ ".join(names)))
    os.makedirs("challenge", exist_ok=True)
    open(f"challenge/Challenge{T}.lean", "w").write("\n".join(out))
    cfg = {
        "challenge_module": f"Challenge{T}",
        "solution_module": f"Solution{T}",
        "theorem_names": [f"{ns}.zeros_up_to_{T}_{x}" for x in ("located", "unique", "count")],
        "definition_names": [],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": True,
    }
    json.dump(cfg, open(f"challenge/comparator-{T}.json", "w"), indent=2)
    print(f"T={T}: {n} ordinates; first {ms[0]}, last {ms[-1]}; min gap {min(b - a for a, b in zip(ms, ms[1:])) / 10**SCALE:.4f}")

write(1000, "data/zeros_T1000.txt")
write(10000, "data/zeros_T10000.txt")
