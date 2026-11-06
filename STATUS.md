# STATUS (progress log; newest entry first)

## 2026-11-06, late night: M4 in progress (window machinery done, generation and builds under way)

- `ZetaCert/Window.lean` (builds): `lcI` = leg checker with bounds on Im ζ (`lcI_spec`; `lc` is the
  special case), `arg_bounds_of_im_nonneg/neg` (|arg z| ≤ |Im z|/Re z via `Complex.tan_arg`,
  `Real.le_tan`), `log_pi_ok` (log π to 10⁻²⁰), `two_pi_dmu` (generic Γ increment), `ncount_window`
  (`exact_argument` + `abs_integral_mu_sub_le` + argument bounds at both ends), `wmain`
  (window assembly, `mem_and_simple_of_Ncount_le`), `range_located/unique/count` (statements of a
  range file (a, b] inside a window (L, U] with L ≤ a, b ≤ U).
- Windows (L, U] (`scripts/gen_window.py`, table `LEGS`): legs at exactly 1000, 2000, 3000, 5000,
  6000, 7000, 9000; at 4000 L = 15999/4 and U = 16003/4; at 8000 L = 31999/4 and U = 64003/8; at
  10⁴ U = 40001/4. Windows ending at 4000.75, 8000.375, 10000.25 contain one extra zero above b
  (4000.0173, 8000.0868, #10143), certified and filtered out. Numeric margins of the count
  (in radians, need > 0): all ≥ 1.5 for the windows generated so far.
- Generated: legs `ZetaCert/Legs/B*` (`scripts/gen_bleg.py`, 234–884 points each; EM parameters
  with E0 ≤ 1e-6), window counts `ZetaCert/Windows/W*`, solutions `solution/Zeros{a}to{b}Solution.lean`
  for 1000–6000, `solution/Count10000Solution.lean` (combines the ten range solutions);
  certificates `ZetaCert/Zeros{a}to{b}/Z*.lean` for 1000–7000 (`scripts/gen_zero_modules.py a b [U]`,
  parameter search now a binary search).
- Built and checked so far: `ZetaCert.Legs.B2000` (380 points, 2 min 54 s wall, 23 CPU-min).
- **Memory:** a `lake build` of all twelve legs at once was stopped by Claude Code because the laptop
  ran out of memory (12 parallel kernel checks at N up to 1789); the certificate generation running
  alongside was stopped too. No errors. Build legs and certificate modules in smaller groups.

Next step: finish `gen_zero_modules.py` for 7000–8000 (U = 64003/8), 8000–9000, 9000–10000
(U = 40001/4), and `gen_window.py` for 6000–10000; build legs a few at a time; build
W1000to2000 + Zeros1000to2000Solution first and fix the generated proofs; then the other ranges,
`#print axioms`, comparator per configuration (record times; Count10000 replays everything).

## 2026-11-06, night: M3 done: `Zeros0to1000` passes the comparator (NanoDa + Lean kernel)

- `scripts/run-comparator.sh challenge/comparator-Zeros0to1000.json`: "nanoda kernel accepts the
  solution", "Lean default kernel accepts the solution", "Your solution is okay!". Wall 58 min 34 s
  (user 7315 s, 214% CPU, dominated by the replay of the 649 certificates and the leg), peak RSS
  6.8 GB. Each of the nine other ranges has about 1000+ zeros at larger t (N up to ~3000), so
  expect several hours per range in the comparator; within PLAN §6's budget but to be measured.

Next step: M4. Generate the certificates for Zeros1000to2000 (`scripts/gen_zero_modules.py 1000
2000`), the boundary legs (PLAN §1.2; better T₂ near 8000), window version of the assembly.

## 2026-11-06, night: `Zeros0to1000` proved (comparator run pending)

- `solution/Zeros0to1000Solution.lean` proves `Zeros0to1000.located`, `.unique`, `.count`.
  `#print axioms` (solution/CheckAxioms0to1000.lean): `[propext, Classical.choice, Quot.sound]` for
  all three. `lake build` (default targets now include `Zeros0to1000` and its solution) is clean;
  no `sorry` in ZetaCert/, ZetaZeros/, solution/.
- Proof: `ZetaCert/Assembly.lean` (`main`): the 649 certificates, separation of the ordinates by
  more than 3·10⁻²⁰ (kernel-checked `IsChain`), 29 of them below 100, zeta-lab's
  `rh_height_hundred`/`zero_count_hundred` below 100, and `mem_and_simple_of_Ncount_le` with
  `Ncount 100 T₂ = 620` above 100.
- Build times on the laptop: the 13 certificate modules about 2 min wall (12 cores), the 6 leg
  modules about 2.5 min, the rest seconds.
- Comparator with NanoDa on `challenge/comparator-Zeros0to1000.json`: running (see next entry).

Next step: comparator result; then M4 (ten range files, boundary legs; the 8000 leg in PLAN §1.2
has a thin margin 0.08: look for a better T₂; Palomar needs a single root licence file).

## 2026-11-06, night: NanoDa test passed; leg, Γ increment and count up to T₂ done

- **M2 addendum (NanoDa).** `scripts/run-comparator.sh test/comparator-toy.json` on the toy pair
  `test/ToyChallenge.lean` / `test/ToySolution.lean` (zero #1 near 14.13, N = 17, and zero #10142
  near 9998.85, N = 2473, k = 60): "nanoda kernel accepts the solution", "Lean default kernel accepts
  the solution", "Your solution is okay!". Wall 6 min 21 s, user 499 s, peak RSS 6.7 GB (most of it
  the export and replay of the Mathlib closure). No design change needed. `scripts/landrun-wrapper.sh`
  (from zeta-23-lean) patched: Comparator v4.35.0-rc2 passes the outer `--` itself.
- `ZetaCert.Leg1000.leg`: Re ζ(σ + iT₂) > 0 on [1/2, 2], T₂ = 512069/512 (220 leg points, about
  2.5 min wall to build). `ZetaCert.Count1000.gamma_increment`: 619.55 ≤ ∫_{100}^{T₂} μ ≤ 619.9;
  `ZetaCert.Count1000.ncount`: `Zeta23.Ncount 100 T₂ = 620` (only Re ζ(1/2+iT₂) > 0 is needed for
  the argument there).

Next step: assembly of the three theorems of `Zeros0to1000` (solution module, comparator run).

## 2026-11-06, evening: revised handoff imported (statements split for Palomar)

From Harald's revised handoff (~/Documents/lean/zeta-new/zeta-cert): `challenge/` replaced by the
eleven files `Zeros{a}to{b}.lean` (ten ranges of 1000) and `Count10000.lean` with their comparator
configurations; the old `Challenge1000/10000.lean` and configs removed (they had needed no syntax
fixes, and none are needed now: all eleven elaborate unchanged, only `sorry` warnings). `scripts/`
(new `scan_boundary_legs.py`, revised `gen_challenge.py`), PLAN.md, CLAUDE.md and README.md
updated; lakefile now declares the eleven challenge libraries. The 649 ordinates of
`Zeros0to1000` are exactly those already certified in `ZetaCert/Zeros1000/`.
Consequences from the new PLAN: M2 now includes a comparator run *with NanoDa* on one certificate
near 14.13 and one near 10⁴ (Palomar always replays through NanoDa); Palomar wants exactly one
licence file at the root (we currently have LICENSE-zeta-lab and LICENSE-rh-up-to-15-lean there:
to be reorganised before submission); M4 needs positive legs near every multiple of 1000
(PLAN §1.2 table).
Comparator, lean4export (tag v4.35.0-rc2), NanoDa (68d5ca9) and Landrun (811cfff) were built by
Harald in `.cache/comparator/`.

Also since the previous entry: `ZetaCert/Leg.lean` fixed and building; leg modules
`ZetaCert/Leg1000/L0..L5` (220 points at T₂ = 512069/512) all build; only the final rewrite in
`ZetaCert/Leg1000.lean` (`leg`) still fails.

Next step: NanoDa/comparator test on a toy pair with one certificate (M2 addendum), then finish
the leg, Γ increment, count and assembly of `Zeros0to1000`.

## 2026-11-06, later: M3 in progress (session stopped at the usage limit)

Done and kernel-checked (`lake build` clean for these modules):
- All 649 zero certificates up to height 1000: `ZetaCert/Zeros1000/Z0..Z12.lean`, theorems `z_i` with
  `∃ t, |t - m_i/10^24| ≤ 10^-20 ∧ ζ(1/2 + it) = 0` (about 1 s each; 2 min wall on 12 cores).
  Generated by `scripts/gen_zero_modules.py` (parameters from `scripts/zeroparams.py`).
- Evaluator at general real part σ = j/4096 (needed for the horizontal leg): `powPP` (binary powering)
  and `rootOK` with soundness (`Eval/SigmaSound.lean`), `sums_spec_gen`, `primeTerm_spec_gen`;
  EM rational part for general σ (`remRS`, `remR1S`, `Eval/EMRestSSound.lean`); EM remainder bounds for
  general σ (`emErr_center_le_gen`, `emErr_circle_le_gen`); root data x_p ≈ p^{-1/4096}
  (`RootData.lean`, `RootDataCheck.lean`).
- Leg-point checker `lc` (`LegCert.lean`) and soundness `lc_spec` (`LegCertSound.lean`):
  `lc ... v d = true → v ≤ Re ζ(s) ∧ ‖ζ'(s)‖ ≤ d`. Tested: evaluates at T₂ = 512069/512 in about 1 s
  (note: d must bound |Re ζ'| + |Im ζ'|).

In progress: `ZetaCert/Leg.lean.wip` (renamed so the build stays clean): ζ'' bound near the leg,
`re_pos_of_point`, `seg_of_lc`, `cover2`. Three small proof errors left (an ill-formed `refine` chain
in `norm_zeta''_le_leg`, a `rw [abs_le]` on a goal that is not an abs, and the extraction of `2048 ≤ j`
from `lc` in `seg_of_lc`).

Remaining for M3: generate the leg samples at T₂ = 512069/512 (numerics, not rigorous: min Re ζ ≈ 0.95,
arg ζ(1/2+iT₂) ≈ 0.86, so Im > 0 suffices for the argument; ~150 points with M2(4, T₂) ≈ 7·10⁴);
Γ increment ∫_{100}^{T₂} μ (reuse zeta-lab `abs_integral_mu_sub_le`, `muPrim`); `exact_argument` with
zeta-lab's leg at 100 (`horizontalLegs100`) ⇒ Ncount 100 T₂ = 620; assembly with `zero_count_hundred`
and the separation of the ordinates into the three challenge theorems; `#print axioms`; comparator.
Comparator tooling is still blocked by the permission classifier (see the entry below).

## 2026-11-06 (Claude Code, Harald's laptop): M0 done except comparator; M1 and M2 done

**M2 reached.** `ZetaCert/Test/OneZero.lean` proves, kernel-checked, that ζ(1/2 + it) = 0 for some
real t with |t − 999791571557412940463163147/10²⁴| ≤ 10⁻²⁰ (zero #649).
`#print axioms z649`: `[propext, Classical.choice, Quot.sound]`. The kernel check (`decide +kernel`
on the per-zero checker `ZetaCert.zc`) takes about 1.5 s; the whole file about 5 s, most of it
Mathlib loading.

M0 (setup):
- Lake package at the repository root: Lean v4.35.0-rc2, Mathlib 065356127b1d; `lake exe cache get`
  works. Vendored, building unchanged: zeta-lab's `RHHeight`, `RHHeight100` (including
  `RHHeight100.Main100`, `zero_count_hundred`), `ZetaLean` (4 modules), `HardyFirstZero`,
  `HardyTenZeros`, and `vendor/zeta23` as a path dependency; rh-up-to-15-lean's `EM2`, `EMDeriv`,
  `Deriv` with the PNT+ import redirected to zeta23's copy. NOTICE and licences added.
- `challenge/Challenge1000.lean` and `Challenge10000.lean` elaborate unchanged (only `sorry`
  warnings); statements unchanged.
- GitHub: private repository Garald1/zeta-zero-locations created and pushed.
- **Not done: comparator.** Building Comparator/lean4export/NanoDa/Landrun from their upstream
  repositories was refused by the Claude Code permission classifier ("code from external"). Go
  1.24.5 and Rust (cargo 1.99) are installed under ~/.local/go and ~/.cargo. Harald: please allow
  this (or build the tools yourself), see the commands in
  vendor-src/zeta-23-lean/zeta23/scripts/verify-comparator.sh, with comparator and lean4export
  at tag v4.35.0-rc2.

M1 (evaluator, `ZetaCert/Eval/`), all proved sound:
- `Core.lean`: Nat-only fixed point (scale 2^-128, offset 2^192); e^{-ix} by Taylor (24 terms) at
  x/2^K and K complex squarings; p^{-s} from w ≈ p^{-1/2} (integer check w²p ≤ 2^256 < (w+1)²p);
  depth-first enumeration of n ≤ N for S = Σ n^{-s}, D = −Σ log n · n^{-s}; all forcing `match`es
  have identical branches (`force`), so no failure branch needs to be excluded in proofs.
- `CoreSound`, `ExpSound`, `DirSound`, `EnumSound`, `SumsSound`: error bounds;
  `sums_spec` gives |S − Σ_{n≤N} n^{-s}| ≤ N·Dp·(Ep + 4u). The enumeration is checked per N by a
  bitmap (`enumOK`), not proved from unique factorisation.
- `EMRest`, `EMRestSound`: the rational part of Euler–Maclaurin (`Rm`, `R1m`, see
  `ZetaCert/EMDecomp.lean`) in exact Gaussian integers over 2^80, rounded once per term.
- `ZetaCert/Bernoulli.lean`, `BernTable.lean`: B_0..B_123 by the recurrence, kernel-checked
  against Mathlib's `bernoulli` (about 20 s, 10 GB, once).
- `ZetaCert/LogCert.lean`, `PrimeData.lean`, `PrimeDataCheck.lean`: log p for the 550 primes
  ≤ 4000 to 2^-126 (atanh series in exact naturals), w ≈ p^{-1/2}; checked once (seconds).

M2 (one zero end to end):
- `ZetaCert/Contraction.lean`: unique zero in a disk by Banach's fixed point theorem.
- `ZetaCert/OnLine.lean`: the reflection s ↦ 1 − s̄ puts it on the critical line.
- `ZetaCert/ZeroCert.lean` (`zero_of_EM_bounds`), `EMErrBound.lean`, `Cert.lean` (checker `zc`),
  `CertSound.lean` (`zc_spec`): from the kernel computation to the zero.
- Design changes from PLAN.md: the target |ζ(c)| is about 10⁻²¹, not 10⁻²⁶ (the disk radius is
  r = 2^-67 ≈ 6.8·10⁻²¹ and κ = 1/2), so N ≈ 0.25–0.3 t with k up to 60 suffices; ζ'(c) is taken
  from the derivative of the EM main term (rh-up-to-15's `emMain1`) plus a Cauchy estimate on the
  circle of radius 1/4; |ζ''| on the disk from rh-up-to-15's `norm_deriv_deriv_zeta_le` (N = 1).
- Timing measured (idle machine): Dirichlet sums 0.6 s at t ≈ 1000 (N = 350), 4.2 s at t ≈ 10⁴
  (N = 3500), about 1 GB per check.

Next: M3 (all 649 certificates, the horizontal leg at T₂ ≈ 1000.13, the argument there, the Γ
increment over [100, T₂], assembly). The leg needs the evaluator at Re s ≠ 1/2 (p^{-σ} by an
integer root check).

## 2026-11-06: sandbox session (claude.ai), before moving to Claude Code on Harald's laptop

Nothing about ζ is formally proved yet. The sandbox had 2 cores and 7 GB of RAM, and its proxy
blocked Mathlib's binary cache, so no Mathlib-dependent file was compiled. Done:

- **Candidate data** (`data/`, `scripts/compute_zeros.py`): Arb (python-flint 0.9.0,
  `acb.zeta_zeros`, 160-bit balls) isolates all 649 zeros up to 1000 and all 10 142 up to 10⁴
  (Re = 1/2 certified by Arb; ordinate radii ≤ 1.2·10⁻⁴⁴), plus zeros #10143–#10154 above 10⁴.
  Arb's counts agree with the classical values N(1000) = 649 and N(10⁴) = 10 142.
- **Draft challenge statements** (`challenge/`, generated by `scripts/gen_challenge.py`): three
  theorems per height (located / unique / count), radius 10⁻²⁰ around 24-decimal centres, plus
  comparator configs modelled on zeta-23-lean's. Not yet elaborated.
- **Kernel feasibility prototype** (`prototype/`, Lean v4.36.0-rc2 core, no Mathlib):
  `decide +kernel` evaluates the Dirichlet sums S and S' at s = 1/2 + it in about 0.5 s at t ≈ 1000
  (N = 350) and about 3 s at t ≈ 10⁴ (N = 3500), whole file including start-up
  (`prototype/run_bench.sh`); a wrong expected
  value is rejected. The first version (Int balls in structures,
  `prototype/old/`) was about 20× slower; micro-benchmarks are in `prototype/micro/`.
- **Parameter scans** (Arb, not rigorous; `scripts/scan_top_leg.py`, `scripts/scan_above_1e4_and_stats.py`, `scripts/em_params.py`):
  - top leg: T₂ ≈ 1000.1348 has min Re ζ ≈ 0.95 on [1/2, 2] + iT₂; between 10⁴ and the next
    zero (10000.0653) no leg is positive (best ≈ −0.012), but T₂ ≈ 10000.2608 gives ≈ 0.236, so
    the 10⁴ count runs to T₂ and includes zero #10143;
  - min |ζ'(ρ)| ≈ 0.79 (zeros ≤ 1000), ≈ 0.40 (zeros ≤ 10⁴); minimal gaps 0.31 and 0.0377;
  - Euler–Maclaurin: with N ≈ t/2, k = 26 (Bernoulli numbers up to B₅₄) brings the formal
    remainder bound of `riemannZeta_EM_real` below 10⁻²⁶ at both heights.
- **Reuse survey** (PLAN.md §3): zeta-lab already proves, kernel-checked, RH up to height 100
  with exact count 29 and the argument-principle identity `exact_argument`; rh-up-to-15-lean has
  Euler–Maclaurin to any order with an explicit remainder; IEANTN has the strip lemmas.

Next: milestone M0 in PLAN.md §4.
