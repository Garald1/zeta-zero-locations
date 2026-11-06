# Kernel-checked locations of the zeros of ζ up to height 1000 and 10 000

Owner: Harald Helfgott (GitHub `Garald1`). At the start of every session read PLAN.md (goal,
proof architecture, reuse map, milestones) and STATUS.md (progress log). Update STATUS.md and
commit at the end of every milestone or work session.

## Rules (non-negotiable)
- Prove the statements in `challenge/Challenge1000.lean` and `challenge/Challenge10000.lean`.
  Fix syntax if they do not elaborate, but never weaken them; if one looks false or unprovable,
  stop and tell Harald.
- Lean kernel only. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`,
  `native_decide`, `Lean.ofReduceBool`, `implemented_by`/`extern` tricks, new axioms.
- No conditional inputs: no RH/qRH-type hypotheses, no external computation as a hypothesis.
  Arb/mpmath output is candidate data only; every inequality is re-proved in the kernel
  (`decide +kernel` on Nat-only checkers with soundness theorems).
- Do not claim success before: clean `lake build`, `#print axioms` on each final theorem, and a
  passing comparator run. Report failures and partial results plainly.
- Cite only files and theorems you have actually opened; never invent names or references.
- Keep copyright headers and licences of reused code (zeta-lab: MIT; zeta-23-lean,
  rh-up-to-15-lean, IEANTN: Apache-2.0); maintain NOTICE.

## Machine and commands
- 12 cores, 32 GB RAM. Heavy `decide +kernel` modules can take several GB each: keep about 50
  zero certificates per module and watch memory when running `lake build -j`.
- `lake exe cache get`, then `lake build`. Python numerics: `pip install python-flint mpmath`.

## Kernel-computation lessons (details in PLAN.md §2 and §5)
- Explicit `Nat` operations in hot loops; no `Int`, typeclass arithmetic or structures there.
- Force accumulators every step (`match Nat.add a b with | 0 => … | _ => …`), or the kernel
  reports deep recursion.
- Use `decide +kernel`; chunk long data lists (≤ 300 entries per `def`).

## GitHub
Repository `Garald1/zeta-zero-locations`, created with `gh repo create` (private until Harald
decides otherwise). Push at each milestone.
