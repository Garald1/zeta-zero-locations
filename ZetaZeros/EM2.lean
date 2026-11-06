/-
Vendored from https://github.com/antoine-olivier/rh-up-to-15-lean at commit
dec8fa913b6c972c2d16f4d23f54d2174cef7718, file ZetaZeros/EM2.lean (Apache License 2.0,
see LICENSE-rh-up-to-15-lean). Local modifications: the PNT+ import is redirected to the copy
vendored in zeta23 (Zeta23.FromPNTPlus.ZetaBounds); any further changes are marked "(port)".
-/
import Zeta23.FromPNTPlus.ZetaBounds
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin of order `2k` for `riemannZeta` (L0-EM-A1, campaign rh-up-to-1)

For `0 < Re s`, `s ≠ 1`, `N ≥ 1`, `k : ℕ` (`riemannZeta_EM`):
`ζ(s) = ∑_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2
        + ∑_{i ≤ k} B_{2i+2}/(2i+2)! · s(s+1)⋯(s+2i) · N^{-(s+2i+1)} + R`,
`‖R‖ ≤ ‖s(s+1)⋯(s+2k+1)‖/(2k+2)! · |B_{2k+2}| · N^{1-σ-2k-2}/(σ+2k+1)`.
Starting point: PNT+ `Zeta0EqZeta` (order 1). Each step integrates by parts against the
periodized Bernoulli function `B_m({x})` (Mathlib `bernoulliFun`), and `|B_{2k}(x)| ≤ |B_{2k}|`
on `[0, 1]` comes from the Fourier series `hasSum_one_div_nat_pow_mul_cos`.
Real forms for LeanCert: `natCast_cpow_neg_eq`, `riemannZeta_EM_real`; explicit orders 4 and 8:
`riemannZeta_EM4`, `riemannZeta_EM8`.
Interface for L1 (v2): `emMain N k s` (main term P), `emErr` (sqrt-free, loose),
`emErrE` (exact, exp/log only), `riemannZeta_sub_emMain_le_exact`, `riemannZeta_eq_emMain_add`;
Bernoulli values up to `bernoulli_sixteen'`.
-/

open Complex MeasureTheory Set Filter Topology

namespace ZetaZeros.EM

/-- Periodized Bernoulli function `x ↦ B_m({x})`. -/
noncomputable def pB (m : ℕ) (x : ℝ) : ℝ := bernoulliFun m (Int.fract x)

theorem pB_bound (m : ℕ) : ∃ C, ∀ x, ‖pB m x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliFun m).continuousOn
  exact ⟨C, fun x => hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩⟩

theorem measurable_pB (m : ℕ) : Measurable (pB m) :=
  (continuous_bernoulliFun m).measurable.comp measurable_fract

theorem continuous_pB {m : ℕ} (hm : m ≠ 1) : Continuous (pB m) :=
  (continuous_bernoulliFun m).continuousOn.comp_fract''
    (bernoulliFun_endpoints_eq_of_ne_one hm).symm

theorem pB_natCast (m n : ℕ) : pB m n = bernoulli m := by
  simp [pB, Int.fract_natCast, bernoulliFun_eval_zero]

theorem hasDerivWithinAt_pB (m : ℕ) (x : ℝ) :
    HasDerivWithinAt (pB m) (m * pB (m - 1) x) (Ici x) x := by
  have h1 : HasDerivWithinAt (fun y => bernoulliFun m (y - ⌊x⌋))
      (m * bernoulliFun (m - 1) (x - ⌊x⌋)) (Ici x) x :=
    ((hasDerivAt_bernoulliFun m (x - ⌊x⌋)).comp_sub_const x (⌊x⌋ : ℝ)).hasDerivWithinAt
  have hev : pB m =ᶠ[𝓝[≥] x] fun y => bernoulliFun m (y - ⌊x⌋) := by
    have hI : Ico x ((⌊x⌋ : ℝ) + 1) ∈ 𝓝[≥] x := Ico_mem_nhdsGE (Int.lt_floor_add_one x)
    filter_upwards [hI] with y hy
    have hfl : ⌊y⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]; exact ⟨(Int.floor_le x).trans hy.1, hy.2⟩
    simp only [pB, ← Int.self_sub_floor, hfl]
  have h2 := h1.congr_of_eventuallyEq hev (by simp only [pB, ← Int.self_sub_floor])
  simpa only [pB, ← Int.self_sub_floor] using h2

/-- The Euler–Maclaurin integral `∫_N^∞ x^{-(s+m)} B_m({x}) dx`. -/
noncomputable def emInt (N m : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (N : ℝ), (x : ℂ) ^ (-(s + m)) * (pB m x : ℂ)

theorem integrableOn_emIntegrand {a : ℝ} (ha : 0 < a) (m : ℕ) {s : ℂ} (hs : 1 < s.re + m) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(s + m)) * (pB m x : ℂ)) (Ioi a) := by
  obtain ⟨C, hC⟩ := pB_bound m
  refine (integrableOn_Ioi_cpow_of_lt ?_ ha).mul_bdd (c := C) ?_ ?_
  · simp only [neg_re, add_re, natCast_re]; linarith
  · exact (Complex.measurable_ofReal.comp (measurable_pB m)).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by rw [Complex.norm_real]; exact hC x

theorem emIBP_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 0 < s.re + m) :
    ∫ x in a..b, (x : ℂ) ^ (-(s + m)) * (pB m x : ℂ) =
      (b : ℂ) ^ (-(s + m)) * ((pB (m + 1) b : ℂ) / (m + 1))
        - (a : ℂ) ^ (-(s + m)) * ((pB (m + 1) a : ℂ) / (m + 1))
        + (s + m) / (m + 1) * ∫ x in a..b, (x : ℂ) ^ (-(s + (m + 1 : ℕ))) * (pB (m + 1) x : ℂ) := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1
  have hr : -(s + m) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [neg_re, add_re, natCast_re, zero_re] at this
    linarith
  have hm1 : m + 1 ≠ 1 := by omega
  have hm0 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-(s + m))) (uIcc a b) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos x hx).ne')).continuousWithinAt
  have hcont' : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-(s + m) - 1)) (uIcc a b) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos x hx).ne')).continuousWithinAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := fun x : ℝ => (x : ℂ) ^ (-(s + m)))
    (v := fun x : ℝ => (pB (m + 1) x : ℂ) / (m + 1))
    (u' := fun x : ℝ => (-(s + m)) * (x : ℂ) ^ (-(s + m) - 1))
    (v' := fun x : ℝ => (pB m x : ℂ))
    (a := a) (b := b) hcont
    ((Complex.continuous_ofReal.comp (continuous_pB hm1)).div_const _).continuousOn ?_ ?_ ?_ ?_
  · rw [key]
    have e : ∫ x in a..b, (-(s + m)) * (x : ℂ) ^ (-(s + m) - 1) * ((pB (m + 1) x : ℂ) / (m + 1)) =
        -((s + m) / (m + 1)) *
          ∫ x in a..b, (x : ℂ) ^ (-(s + (m + 1 : ℕ))) * (pB (m + 1) x : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext x
      have : -(s + m) - 1 = -(s + (m + 1 : ℕ)) := by push_cast; ring
      rw [this]
      field_simp
    rw [e]
    ring
  · intro x hx
    have hx' : 0 < x := by
      rw [min_eq_left hab] at hx; exact ha.trans hx.1
    exact (hasDerivAt_ofReal_cpow_const hx'.ne' hr).hasDerivWithinAt
  · intro x _
    have h1 := ((hasDerivWithinAt_pB (m + 1) x).mono Ioi_subset_Ici_self).ofReal_comp
    have h2 := h1.div_const ((m : ℂ) + 1)
    convert h2 using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  · exact (continuousOn_const.mul hcont').intervalIntegrable
  · obtain ⟨C, hC⟩ := pB_bound m
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      (Complex.measurable_ofReal.comp (measurable_pB m)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      show ‖((pB m x : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real]; exact hC x

/-- One integration by parts on `(N, ∞)`. -/
theorem emInt_succ {N : ℕ} (hN : 0 < N) {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 0 < s.re) :
    emInt N m s = -((bernoulli (m + 1) : ℂ) / (m + 1)) * (N : ℂ) ^ (-(s + m))
      + (s + m) / (m + 1) * emInt N (m + 1) s := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 < s.re + m := by linarith
  have hs2 : 1 < s.re + ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨C, hC⟩ := pB_bound (m + 1)
  have L1 := intervalIntegral_tendsto_integral_Ioi (N : ℝ)
    (integrableOn_emIntegrand hNpos m hs1) tendsto_id
  have L2 := intervalIntegral_tendsto_integral_Ioi (N : ℝ)
    (integrableOn_emIntegrand hNpos (m + 1) hs2) tendsto_id
  have L3 : Tendsto (fun b : ℝ => (b : ℂ) ^ (-(s + m)) * ((pB (m + 1) b : ℂ) / (m + 1)))
      atTop (𝓝 0) := by
    have hr : Tendsto (fun b : ℝ => b ^ (-(s.re + m)) * C) atTop (𝓝 (0 * C)) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < s.re + m)).mul_const C
    rw [zero_mul] at hr
    refine squeeze_zero_norm' ?_ hr
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb, norm_div, Complex.norm_real]
    have h1 : ‖pB (m + 1) b‖ / ‖((m : ℂ) + 1)‖ ≤ C := by
      have : (1 : ℝ) ≤ ‖((m : ℂ) + 1)‖ := by
        rw [show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        exact_mod_cast Nat.succ_pos m
      calc _ ≤ ‖pB (m + 1) b‖ := div_le_self (norm_nonneg _) this
        _ ≤ C := hC b
    have h2 : (-(s + m)).re = -(s.re + m) := by simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hb.le _)
  have L4 := (L3.sub (tendsto_const_nhds (x := (N : ℂ) ^ (-(s + m)) *
      ((pB (m + 1) (N : ℝ) : ℂ) / (m + 1))))).add (L2.const_mul ((s + m) / (m + 1)))
  have heq : (fun b : ℝ => ∫ x in (N : ℝ)..id b, (x : ℂ) ^ (-(s + m)) * (pB m x : ℂ)) =ᶠ[atTop]
      fun b : ℝ => (b : ℂ) ^ (-(s + m)) * ((pB (m + 1) b : ℂ) / (m + 1))
        - (N : ℂ) ^ (-(s + m)) * ((pB (m + 1) (N : ℝ) : ℂ) / (m + 1))
        + (s + m) / (m + 1) *
          ∫ x in (N : ℝ)..id b, (x : ℂ) ^ (-(s + (m + 1 : ℕ))) * (pB (m + 1) x : ℂ) := by
    filter_upwards [eventually_ge_atTop (N : ℝ)] with b hb
    have := emIBP_interval hNpos hb hm (s := s) (by linarith)
    simp only [id]
    rw [this]
    push_cast
    ring
  have H := tendsto_nhds_unique (L1.congr' heq) L4
  unfold emInt
  rw [H, pB_natCast]
  push_cast
  ring

/-- The remainder bound: `‖∫_N^∞ x^{-(s+m)} B_m({x}) dx‖ ≤ M N^{1-σ-m}/(σ+m-1)`. -/
theorem norm_emInt_le {N : ℕ} (hN : 0 < N) {m : ℕ} {s : ℂ} (hs : 1 < s.re + m) {M : ℝ}
    (hM : ∀ y ∈ Icc (0 : ℝ) 1, |bernoulliFun m y| ≤ M) :
    ‖emInt N m s‖ ≤ M * ((N : ℝ) ^ (-(s.re + m) + 1) / (s.re + m - 1)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : IntegrableOn (fun x : ℝ => M * x ^ (-(s.re + m))) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNpos).const_mul M
  have hpt : ∀ x ∈ Ioi (N : ℝ),
      ‖(x : ℂ) ^ (-(s + m)) * (pB m x : ℂ)‖ ≤ M * x ^ (-(s.re + m)) := by
    intro x hx
    have hx0 : 0 < x := hNpos.trans hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
    simp only [neg_re, add_re, natCast_re]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩)
      (Real.rpow_nonneg hx0.le _)
  have h := norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  unfold emInt
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hNpos]
  congr 1
  rw [neg_div, ← div_neg]
  congr 1
  ring

/-- `|B_{2k}(x)| ≤ |B_{2k}|` on `[0, 1]`, from the Fourier series of `B_{2k}`. -/
theorem abs_bernoulliFun_le {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  have hx0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have H := hasSum_one_div_nat_pow_mul_cos hk hx
  have H0 := hasSum_one_div_nat_pow_mul_cos hk hx0
  set c : ℝ := (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / ((2 * k).factorial : ℝ) with hc
  change HasSum _ (c * bernoulliFun (2 * k) x) at H
  change HasSum _ (c * bernoulliFun (2 * k) 0) at H0
  simp only [mul_zero, Real.cos_zero, mul_one] at H0
  have hle : ∀ n : ℕ, 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * x) ≤
      1 / (n : ℝ) ^ (2 * k) := fun n => by
    have h1 := Real.cos_le_one (2 * Real.pi * n * x)
    have h2 : 0 ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
    nlinarith
  have hge : ∀ n : ℕ, -(1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * x)) ≤
      1 / (n : ℝ) ^ (2 * k) := fun n => by
    have h1 := Real.neg_one_le_cos (2 * Real.pi * n * x)
    have h2 : 0 ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
    nlinarith
  have A := hasSum_le hle H H0
  have B := hasSum_le hge H.neg H0
  have habs : |c * bernoulliFun (2 * k) x| ≤ c * bernoulliFun (2 * k) 0 :=
    abs_le.mpr ⟨by linarith, A⟩
  rw [abs_mul, bernoulliFun_eval_zero] at habs
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine div_ne_zero (div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by positivity))) two_ne_zero) ?_
    exact_mod_cast Nat.factorial_ne_zero _
  have h3 : c * (bernoulli (2 * k) : ℝ) ≤ |c| * |(bernoulli (2 * k) : ℝ)| := by
    rw [← abs_mul]; exact le_abs_self _
  exact le_of_mul_le_mul_left (habs.trans h3) (abs_pos.mpr hc0)

/-- Order-one formula in terms of `emInt`. -/
theorem zeta_eq_order1 {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) + (N : ℂ) ^ (1 - s) / (s - 1)
      - (N : ℂ) ^ (-s) / 2 - s * emInt N 1 s := by
  rw [← Zeta0EqZeta hN hs hs1, riemannZeta0]
  have hint : (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)) = -emInt N 1 s := by
    unfold emInt
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [pB, bernoulliFun_one, ← Int.self_sub_floor]
    push_cast
    rw [div_eq_mul_inv, ← cpow_neg]
    ring
  rw [hint, show (-(N : ℂ) ^ (1 - s)) / (1 - s) = (N : ℂ) ^ (1 - s) / (s - 1) by
    rw [neg_div, ← div_neg, neg_sub]]
  ring

/-- `s (s+1) ⋯ (s+j-1)`. -/
noncomputable def poch (s : ℂ) (j : ℕ) : ℂ := ∏ i ∈ Finset.range j, (s + i)

/-- The `j`-th correction term `B_{j+2}/(j+2)! · s ⋯ (s+j) · N^{-(s+j+1)}`. -/
noncomputable def emTerm (N : ℕ) (s : ℂ) (j : ℕ) : ℂ :=
  (bernoulli (j + 1 + 1) : ℂ) / ((j + 1 + 1).factorial : ℂ) * poch s (j + 1) *
    (N : ℂ) ^ (-(s + (j + 1 : ℕ)))

theorem emInt_one_expand {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    -s * emInt N 1 s = ∑ j ∈ Finset.range n, emTerm N s j
      - poch s (n + 1) / ((n + 1).factorial : ℂ) * emInt N (n + 1) s := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    rw [ih, emInt_succ hN (by omega : 1 ≤ n + 1) hs, Finset.sum_range_succ]
    have h1 : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((n : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    simp only [emTerm, poch, Finset.prod_range_succ, Nat.factorial_succ (n + 1)]
    push_cast
    field_simp
    ring

theorem sum_emTerm_odd_vanish (N : ℕ) (s : ℂ) (k : ℕ) :
    ∑ j ∈ Finset.range (2 * k + 1), emTerm N s j =
      ∑ i ∈ Finset.range (k + 1), emTerm N s (2 * i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (n := k + 1)]
    have h0 : emTerm N s (2 * k + 1) = 0 := by
      simp only [emTerm]
      rw [bernoulli_eq_zero_of_odd ⟨k + 1, by ring⟩ (by omega)]
      simp
    rw [h0, add_zero, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

/-- **Euler–Maclaurin of order `2k+2` for `ζ(s)`**, `0 < Re s`, `s ≠ 1`, `N ≥ 1`. -/
theorem riemannZeta_EM {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (k : ℕ) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
        + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
        + ∑ i ∈ Finset.range (k + 1), emTerm N s (2 * i))‖ ≤
      ‖poch s (2 * k + 2)‖ / ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)| *
        ((N : ℝ) ^ (-(s.re + (2 * k + 2 : ℕ)) + 1) / (s.re + (2 * k + 2 : ℕ) - 1)) := by
  have E := emInt_one_expand hN hs (2 * k + 1)
  rw [sum_emTerm_odd_vanish, show 2 * k + 1 + 1 = 2 * k + 2 from rfl] at E
  have key : riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
        + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
        + ∑ i ∈ Finset.range (k + 1), emTerm N s (2 * i)) =
      -(poch s (2 * k + 2) / ((2 * k + 2).factorial : ℂ) * emInt N (2 * k + 2) s) := by
    rw [zeta_eq_order1 hN hs hs1]
    linear_combination E
  rw [key, norm_neg, norm_mul, norm_div, Complex.norm_natCast, mul_assoc]
  have hB : ∀ y ∈ Icc (0 : ℝ) 1, |bernoulliFun (2 * k + 2) y| ≤ |(bernoulli (2 * k + 2) : ℝ)| :=
    fun y hy => abs_bernoulliFun_le (k := k + 1) (by omega) hy
  have hs' : 1 < s.re + ((2 * k + 2 : ℕ) : ℝ) := by push_cast; linarith
  refine mul_le_mul_of_nonneg_left (norm_emInt_le hN hs' hB) (by positivity)

/-- `‖s(s+1)⋯(s+j-1)‖ ≤ ∏ (|Re s + i| + |Im s|)`, a sqrt-free real bound. -/
theorem norm_poch_le (s : ℂ) (j : ℕ) :
    ‖poch s j‖ ≤ ∏ i ∈ Finset.range j, (|s.re + i| + |s.im|) := by
  unfold poch
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  have := Complex.norm_le_abs_re_add_abs_im (s + i)
  simpa using this

/-- `n^{-w}` through `Real.exp`, `Real.log`, `Real.cos`, `Real.sin`. -/
theorem natCast_cpow_neg_eq {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    (n : ℂ) ^ (-w) = ((Real.exp (-w.re * Real.log n) * Real.cos (w.im * Real.log n) : ℝ) : ℂ)
      - ((Real.exp (-w.re * Real.log n) * Real.sin (w.im * Real.log n) : ℝ) : ℂ) * I := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  apply Complex.ext
  · simp only [Complex.exp_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    have e1 : Real.log n * -w.re - 0 * -w.im = -w.re * Real.log n := by ring
    have e2 : Real.log n * -w.im + 0 * -w.re = -(w.im * Real.log n) := by ring
    rw [e1, e2, Real.cos_neg]
    ring
  · simp only [Complex.exp_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    have e1 : Real.log n * -w.re - 0 * -w.im = -w.re * Real.log n := by ring
    have e2 : Real.log n * -w.im + 0 * -w.re = -(w.im * Real.log n) := by ring
    rw [e1, e2, Real.sin_neg]
    ring

/-- Real form of the remainder bound of `riemannZeta_EM`. -/
theorem riemannZeta_EM_real {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (k : ℕ) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
        + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
        + ∑ i ∈ Finset.range (k + 1), emTerm N s (2 * i))‖ ≤
      (∏ i ∈ Finset.range (2 * k + 2), (|s.re + i| + |s.im|)) / ((2 * k + 2).factorial : ℝ)
        * |(bernoulli (2 * k + 2) : ℝ)| *
        (Real.exp ((-(s.re + (2 * k + 2 : ℕ)) + 1) * Real.log N)
          / (s.re + (2 * k + 2 : ℕ) - 1)) := by
  refine (riemannZeta_EM hN hs hs1 k).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hNpos, mul_comm (Real.log N)]
  have hd : 0 < s.re + ((2 * k + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  gcongr
  exact norm_poch_le s _

/-- The `n = 0` term of PNT+'s partial sum vanishes. -/
theorem sum_range_succ_eq_sum_Icc (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp [Complex.zero_cpow hs]
  rfl

theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

theorem bernoulli'_five : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, by norm_num⟩ (by norm_num)

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have c1 : Nat.choose 6 2 = 15 := by decide
  have c2 : Nat.choose 6 3 = 20 := by decide
  have c3 : Nat.choose 6 4 = 15 := by decide
  have c4 : Nat.choose 6 5 = 6 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, c1, c2, c3, c4, bernoulli'_five]

theorem bernoulli'_seven : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨3, by norm_num⟩ (by norm_num)

theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  have c1 : Nat.choose 8 2 = 28 := by decide
  have c2 : Nat.choose 8 3 = 56 := by decide
  have c3 : Nat.choose 8 4 = 70 := by decide
  have c4 : Nat.choose 8 5 = 56 := by decide
  have c5 : Nat.choose 8 6 = 28 := by decide
  have c6 : Nat.choose 8 7 = 8 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, c1, c2, c3, c4, c5, c6, bernoulli'_five, bernoulli'_six,
    bernoulli'_seven]

theorem bernoulli_six' : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]

theorem bernoulli_eight' : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_eight]

/-- **Order 4**, explicit. -/
theorem riemannZeta_EM4 {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
        + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
        + (s / 12 * (N : ℂ) ^ (-(s + 1))
          - s * (s + 1) * (s + 2) / 720 * (N : ℂ) ^ (-(s + 3))))‖ ≤
      ‖s * (s + 1) * (s + 2) * (s + 3)‖ / 720 * ((N : ℝ) ^ (-(s.re + 4) + 1) / (s.re + 3)) := by
  have h := riemannZeta_EM hN hs hs1 1
  have e1 : ∑ i ∈ Finset.range (1 + 1), emTerm N s (2 * i) =
      s / 12 * (N : ℂ) ^ (-(s + 1)) - s * (s + 1) * (s + 2) / 720 * (N : ℂ) ^ (-(s + 3)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, emTerm, poch, Finset.prod_range_succ,
      Finset.prod_range_zero]
    norm_num [bernoulli_four', Nat.factorial]
    ring
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  have hp : poch s (2 * 1 + 2) = s * (s + 1) * (s + 2) * (s + 3) := by
    simp only [poch, Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have hb : (bernoulli (2 * 1 + 2) : ℝ) = -1 / 30 := by
    rw [show 2 * 1 + 2 = 4 from rfl, bernoulli_four']
    norm_num
  rw [hp, hb]
  norm_num [Nat.factorial]
  ring_nf

/-- **Order 8**, explicit. -/
theorem riemannZeta_EM8 {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
        + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
        + (s / 12 * (N : ℂ) ^ (-(s + 1))
          - s * (s + 1) * (s + 2) / 720 * (N : ℂ) ^ (-(s + 3))
          + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240 * (N : ℂ) ^ (-(s + 5))
          - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 1209600
            * (N : ℂ) ^ (-(s + 7))))‖ ≤
      ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7)‖ / 1209600
        * ((N : ℝ) ^ (-(s.re + 8) + 1) / (s.re + 7)) := by
  have h := riemannZeta_EM hN hs hs1 3
  have e1 : ∑ i ∈ Finset.range (3 + 1), emTerm N s (2 * i) =
      s / 12 * (N : ℂ) ^ (-(s + 1))
          - s * (s + 1) * (s + 2) / 720 * (N : ℂ) ^ (-(s + 3))
          + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240 * (N : ℂ) ^ (-(s + 5))
          - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 1209600
            * (N : ℂ) ^ (-(s + 7)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, emTerm, poch, Finset.prod_range_succ,
      Finset.prod_range_zero]
    norm_num [bernoulli_four', bernoulli_six', bernoulli_eight', Nat.factorial]
    ring
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  have hp : poch s (2 * 3 + 2) =
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) := by
    simp only [poch, Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have hb : (bernoulli (2 * 3 + 2) : ℝ) = -1 / 30 := by
    rw [show 2 * 3 + 2 = 8 from rfl, bernoulli_eight']
    norm_num
  rw [hp, hb]
  norm_num [Nat.factorial]
  ring_nf

/-! ### Interface for L1: main term `P = emMain N k s`, real closed-form error `emErr` -/

/-- Main term of Euler–Maclaurin of order `2k+2` (Bernoulli terms `B_2, …, B_{2k+2}`). -/
noncomputable def emMain (N k : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) + (N : ℂ) ^ (1 - s) / (s - 1)
    - (N : ℂ) ^ (-s) / 2 + ∑ i ∈ Finset.range (k + 1), emTerm N s (2 * i)

/-- Real, sqrt-free bound on `‖ζ(s) - emMain N k s‖`, with `σ = Re s`, `τ = Im s`. -/
noncomputable def emErr (N k : ℕ) (σ τ : ℝ) : ℝ :=
  (∏ i ∈ Finset.range (2 * k + 2), (|σ + i| + |τ|)) / ((2 * k + 2).factorial : ℝ)
    * |(bernoulli (2 * k + 2) : ℝ)|
    * (Real.exp ((-(σ + (2 * k + 2 : ℕ)) + 1) * Real.log N) / (σ + (2 * k + 2 : ℕ) - 1))

theorem riemannZeta_sub_emMain_le {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (k : ℕ) : ‖riemannZeta s - emMain N k s‖ ≤ emErr N k s.re s.im :=
  riemannZeta_EM_real hN hs hs1 k

/-- `ζ(s) = P + R` with `‖R‖ ≤ ε`. -/
theorem riemannZeta_eq_emMain_add {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (k : ℕ) : ∃ R : ℂ, riemannZeta s = emMain N k s + R ∧ ‖R‖ ≤ emErr N k s.re s.im :=
  ⟨riemannZeta s - emMain N k s, by ring, riemannZeta_sub_emMain_le hN hs hs1 k⟩

theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven, bernoulli'_eight,
    bernoulli'_eq_zero_of_odd (n := 9) ⟨4, by norm_num⟩ (by norm_num)]

theorem bernoulli'_twelve : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven, bernoulli'_eight,
    bernoulli'_ten, bernoulli'_eq_zero_of_odd (n := 9) ⟨4, by norm_num⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 11) ⟨5, by norm_num⟩ (by norm_num)]

theorem bernoulli'_fourteen : bernoulli' 14 = 7 / 6 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven, bernoulli'_eight,
    bernoulli'_ten, bernoulli'_twelve,
    bernoulli'_eq_zero_of_odd (n := 9) ⟨4, by norm_num⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 11) ⟨5, by norm_num⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 13) ⟨6, by norm_num⟩ (by norm_num)]

theorem bernoulli'_sixteen : bernoulli' 16 = -3617 / 510 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven, bernoulli'_eight,
    bernoulli'_ten, bernoulli'_twelve, bernoulli'_fourteen,
    bernoulli'_eq_zero_of_odd (n := 9) ⟨4, by norm_num⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 11) ⟨5, by norm_num⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 13) ⟨6, by norm_num⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 15) ⟨7, by norm_num⟩ (by norm_num)]

theorem bernoulli_sixteen' : bernoulli 16 = -3617 / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_sixteen]

/-- `‖z‖ = exp (log (re² + im²) / 2)` for `z ≠ 0`: exp/log form, no sqrt. -/
theorem norm_eq_exp_log {z : ℂ} (hz : z ≠ 0) :
    ‖z‖ = Real.exp (Real.log (z.re ^ 2 + z.im ^ 2) / 2) := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h2, Real.log_pow]
  push_cast
  rw [show (2 : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by ring, Real.exp_log hpos]

/-- Exact real form of the bound of `riemannZeta_EM` (only `exp`, `log`, rationals). -/
noncomputable def emErrE (N k : ℕ) (σ τ : ℝ) : ℝ :=
  Real.exp ((∑ i ∈ Finset.range (2 * k + 2), Real.log ((σ + i) ^ 2 + τ ^ 2)) / 2)
    / ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)|
    * (Real.exp ((-(σ + (2 * k + 2 : ℕ)) + 1) * Real.log N) / (σ + (2 * k + 2 : ℕ) - 1))

theorem norm_poch_eq_exp {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    ‖poch s j‖ = Real.exp ((∑ i ∈ Finset.range j, Real.log ((s.re + i) ^ 2 + s.im ^ 2)) / 2) := by
  unfold poch
  rw [norm_prod, Finset.sum_div, Real.exp_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hne : s + i ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, natCast_re, zero_re] at this
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  rw [norm_eq_exp_log hne]
  simp

theorem riemannZeta_sub_emMain_le_exact {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (k : ℕ) : ‖riemannZeta s - emMain N k s‖ ≤ emErrE N k s.re s.im := by
  refine (riemannZeta_EM hN hs hs1 k).trans (le_of_eq ?_)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_poch_eq_exp hs, Real.rpow_def_of_pos hNpos, mul_comm (Real.log N)]
  rfl

end ZetaZeros.EM

#print axioms ZetaZeros.EM.riemannZeta_EM
#print axioms ZetaZeros.EM.riemannZeta_EM_real
#print axioms ZetaZeros.EM.natCast_cpow_neg_eq
#print axioms ZetaZeros.EM.riemannZeta_EM4
#print axioms ZetaZeros.EM.riemannZeta_EM8
#print axioms ZetaZeros.EM.sum_range_succ_eq_sum_Icc
#print axioms ZetaZeros.EM.riemannZeta_sub_emMain_le
#print axioms ZetaZeros.EM.riemannZeta_eq_emMain_add
#print axioms ZetaZeros.EM.bernoulli'_ten
#print axioms ZetaZeros.EM.bernoulli_sixteen'
#print axioms ZetaZeros.EM.riemannZeta_sub_emMain_le_exact
