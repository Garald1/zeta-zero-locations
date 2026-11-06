# zeta-zero-locations (work in progress)

Goal: a Lean 4 + Mathlib proof, checked by Lean's kernel with only the standard axioms, that every
zero of the Riemann zeta function with 0 < Im s ≤ 1000 (649 zeros), and then with
0 < Im s ≤ 10 000 (10 142 zeros), is simple, lies on the critical line, and has its ordinate
within 10⁻²⁰ of an explicit rational, with exactly one zero per listed interval. The statements
are in `challenge/` (one file per range of 1000 in height, plus a count up to 10⁴, to fit the
limits of the [Palomar](https://palomar-registry.org/) registry); they are checked with
[Comparator](https://github.com/leanprover/comparator).

Status: not yet proved. See `STATUS.md` for progress and `PLAN.md` for the proof architecture.

Layout:
- `challenge/`: trusted statements and comparator configurations (drafts until they elaborate).
- `data/`: zero ordinates isolated with Arb (candidate data; the proof does not trust them).
- `scripts/`: data generation and parameter scans (python-flint, mpmath).
- `prototype/`: Lean-core kernel-evaluation benchmarks that fixed the computational design.
