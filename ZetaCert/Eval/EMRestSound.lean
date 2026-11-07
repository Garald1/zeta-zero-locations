/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.EMDecomp
public import ZetaCert.Eval.EMRest
public import ZetaCert.Eval.CoreSound

@[expose] public section

/-!
# Soundness of `remR` and `remR1`

At `s = 1/2 + iγ`, `γ = G/2^80`: each component of `remR N G bern k / 2^128` is within
`(k + 2) u` of the corresponding component of `Rm N k s`, and likewise for `remR1` and `R1m`,
provided `bern` lists Mathlib's Bernoulli numbers up to index `2k + 2`.
-/

set_option exponentiation.threshold 600

namespace ZetaCert.Eval

open Complex ZetaCert ZetaZeros.EM ZetaZeros.EMDeriv

/-- The point `s = (2^79 + iG) / 2^80`. -/
noncomputable def sG (G : ℕ) : ℂ := 1 / 2 + ((G : ℝ) / 2 ^ 80 : ℝ) * I

/-- Complex value of a Gaussian integer. -/
noncomputable def gz (a : GZ) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * I

theorem gz_mul (a b : GZ) : gz (gmul a b) = gz a * gz b := by
  unfold gz gmul; push_cast; ring_nf; rw [I_sq]; ring

theorem gz_add (a b : GZ) : gz (gadd a b) = gz a + gz b := by
  unfold gz gadd; push_cast; ring

theorem gz_smul (c : ℤ) (a : GZ) : gz (gsmul c a) = (c : ℂ) * gz a := by
  unfold gz gsmul; push_cast; ring

theorem gz_fac (G m : ℕ) : gz (facZ G m) = 2 ^ 80 * (sG G + m) := by
  unfold gz facZ sG; push_cast; ring

theorem pochZ_spec (G m : ℕ) : gz (pochZ G m) = 2 ^ (80 * m) * poch (sG G) m := by
  induction m with
  | zero => simp [pochZ, gz, poch]
  | succ m ih =>
    rw [pochZ, gz_mul, ih, gz_fac, poch_succ]
    rw [show 80 * (m + 1) = 80 * m + 80 by ring, pow_add]; ring

theorem dpochZ_spec (G m : ℕ) : gz (dpochZ G m) = 2 ^ (80 * m) * dpoch (sG G) m := by
  induction m with
  | zero => simp [dpochZ, gz, dpoch]
  | succ m ih =>
    rw [dpochZ, gz_add, gz_mul, gz_smul, ih, gz_fac, pochZ_spec, dpoch]
    rw [show 80 * (m + 1) = 80 * m + 80 by ring, pow_add]; push_cast; ring

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fact, ih, Nat.factorial_succ]

/-- Floor division by a positive integer, in the reals. -/
theorem int_div_bounds (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (a : ℝ) / b - 1 < ((a / b : ℤ) : ℝ) ∧ ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Int.emod_nonneg a hb.ne'
  have h2 := Int.emod_lt_of_pos a hb
  have h3 := Int.mul_ediv_add_emod a b
  have e : (a : ℝ) = b * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by exact_mod_cast h3.symm
  have h1R : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast h1
  have h2R : ((a % b : ℤ) : ℝ) < b := by exact_mod_cast h2
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hbR, e]; nlinarith
  · rw [le_div_iff₀ hbR, e]; nlinarith

/-- Bernoulli table hypothesis. -/
def BernOK (bern : List (ℤ × ℕ)) (M : ℕ) : Prop :=
  ∀ j ≤ M, 0 < (bernAt bern j).2 ∧ (bernoulli j : ℚ) = (bernAt bern j).1 / (bernAt bern j).2

theorem beta_eq {bern : List (ℤ × ℕ)} {M j : ℕ} (hb : BernOK bern M) (hj : j + 2 ≤ M) :
    beta j = ((bernAt bern (j + 2)).1 : ℂ) / ((bernAt bern (j + 2)).2 * (j + 2).factorial : ℕ) := by
  obtain ⟨h0, h1⟩ := hb (j + 2) hj
  unfold beta
  have : (bernoulli (j + 1 + 1) : ℂ) = ((bernoulli (j + 2) : ℚ) : ℂ) := rfl
  rw [this, h1]
  push_cast
  field_simp

/-- The value of one Euler–Maclaurin term, as a complex number. -/
noncomputable def emTermC (N : ℕ) (s : ℂ) (i : ℕ) (P : ℂ) : ℂ :=
  beta (2 * i) * P / (N : ℂ) ^ (2 * i + 1)

/-- One rounded term: both components within one unit (at scale `2^128`). -/
theorem emTermZ_spec {N G : ℕ} (hN : 0 < N) {bern : List (ℤ × ℕ)} {M i : ℕ} (hb : BernOK bern M)
    (hi : 2 * i + 2 ≤ M) (z : GZ) (P : ℂ) (hz : gz z = 2 ^ (80 * (2 * i + 1)) * P) :
    let e := emTermZ N bern i z
    let v := emTermC N (sG G) i P * 2 ^ 128
    (v.re - 1 < (e.1 : ℝ) ∧ (e.1 : ℝ) ≤ v.re) ∧ (v.im - 1 < (e.2 : ℝ) ∧ (e.2 : ℝ) ≤ v.im) := by
  intro e v
  have hfe : fact (2 * i + 2) = (2 * i + 2).factorial := fact_eq _
  obtain ⟨h0, -⟩ := hb (2 * i + 2) hi
  have hbeta := beta_eq hb hi
  have he : e = emTermZ N bern i z := rfl
  unfold emTermZ at he
  rw [hfe] at he
  generalize bernAt bern (2 * i + 2) = b at h0 hbeta he
  obtain ⟨bn, bd⟩ := b
  simp only at h0 hbeta he
  set D : ℕ := bd * (2 * i + 2).factorial * 2 ^ (80 * (2 * i + 1)) * N ^ (2 * i + 1) with hDdef
  have hD : 0 < D := by positivity
  have hDZ : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hv : v = (bn : ℂ) * gz z * 2 ^ 128 / (D : ℂ) := by
    simp only [v, emTermC, hbeta, hz, hDdef]
    push_cast
    field_simp
  have hre : v.re = ((bn * z.1 * 2 ^ 128 : ℤ) : ℝ) / (D : ℝ) := by
    rw [hv]
    have : (bn : ℂ) * gz z * 2 ^ 128 / (D : ℂ) =
        (((bn * z.1 * 2 ^ 128 : ℤ) : ℝ) / (D : ℝ) : ℝ) + (((bn * z.2 * 2 ^ 128 : ℤ) : ℝ) / (D : ℝ) : ℝ) * I := by
      unfold gz; push_cast; ring
    rw [this]; simp
  have him : v.im = ((bn * z.2 * 2 ^ 128 : ℤ) : ℝ) / (D : ℝ) := by
    rw [hv]
    have : (bn : ℂ) * gz z * 2 ^ 128 / (D : ℂ) =
        (((bn * z.1 * 2 ^ 128 : ℤ) : ℝ) / (D : ℝ) : ℝ) + (((bn * z.2 * 2 ^ 128 : ℤ) : ℝ) / (D : ℝ) : ℝ) * I := by
      unfold gz; push_cast; ring
    rw [this]; simp
  have b1 := int_div_bounds (bn * z.1 * 2 ^ 128) hDZ
  have b2 := int_div_bounds (bn * z.2 * 2 ^ 128) hDZ
  rw [he, hre, him]
  push_cast at b1 b2 ⊢
  exact ⟨b1, b2⟩

theorem int_div_bounds_nat (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) - 1 < ((a / (b : ℤ) : ℤ) : ℝ) ∧ ((a / (b : ℤ) : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have := int_div_bounds a (b := (b : ℤ)) (by exact_mod_cast hb)
  simpa using this

theorem foldr_gadd (l : List GZ) :
    l.foldr gadd (0, 0) = ((l.map Prod.fst).sum, (l.map Prod.snd).sum) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, gadd, List.map_cons, List.sum_cons]

theorem list_sum_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- Componentwise bounds for a sum of rounded terms. -/
theorem sum_bounds {k : ℕ} (e : ℕ → GZ) (v : ℕ → ℂ)
    (h : ∀ i ∈ Finset.range (k + 1), ((v i).re - 1 < ((e i).1 : ℝ) ∧ ((e i).1 : ℝ) ≤ (v i).re) ∧
      ((v i).im - 1 < ((e i).2 : ℝ) ∧ ((e i).2 : ℝ) ≤ (v i).im)) :
    let S := ((List.range (k + 1)).map e).foldr gadd (0, 0)
    let V := ∑ i ∈ Finset.range (k + 1), v i
    (V.re - (k + 1) ≤ (S.1 : ℝ) ∧ (S.1 : ℝ) ≤ V.re) ∧ (V.im - (k + 1) ≤ (S.2 : ℝ) ∧ (S.2 : ℝ) ≤ V.im) := by
  intro S V
  have hS : S = (∑ i ∈ Finset.range (k + 1), (e i).1, ∑ i ∈ Finset.range (k + 1), (e i).2) := by
    simp only [S, foldr_gadd, List.map_map]
    rw [list_sum_range', list_sum_range']; rfl
  rw [hS]
  simp only [V, Complex.re_sum, Complex.im_sum]
  push_cast
  have hc : ((k : ℝ) + 1) = ∑ i ∈ Finset.range (k + 1), (1 : ℝ) := by simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hc, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i hi => (h i hi).1.1.le
  · exact Finset.sum_le_sum fun i hi => (h i hi).1.2
  · rw [hc, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i hi => (h i hi).2.1.le
  · exact Finset.sum_le_sum fun i hi => (h i hi).2.2

theorem re_two_pow (n : ℕ) : ((2 : ℂ) ^ n).re = 2 ^ n := by
  rw [show (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) by push_cast; ring]; exact Complex.ofReal_re _

theorem im_two_pow (n : ℕ) : ((2 : ℂ) ^ n).im = 0 := by
  rw [show (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) by push_cast; ring]; exact Complex.ofReal_im _

theorem sG_sub_one (G : ℕ) : sG G - 1 = (-(2 : ℂ) ^ 79 + (G : ℂ) * I) / 2 ^ 80 := by
  unfold sG; push_cast; field_simp; ring

theorem W2_pos (G : ℕ) : (0 : ℝ) < (W2 G : ℕ) := by unfold W2; positivity

theorem mul_conj_w (G : ℕ) :
    (-(2 : ℂ) ^ 79 + (G : ℂ) * I) * (-(2 : ℂ) ^ 79 - (G : ℂ) * I) = ((W2 G : ℕ) : ℂ) := by
  unfold W2; push_cast; ring_nf; rw [I_sq]; ring

theorem w_ne_zero (G : ℕ) : (-(2 : ℂ) ^ 79 + (G : ℂ) * I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [re_two_pow] at this

theorem pole_eq (N G : ℕ) :
    (N : ℂ) / (sG G - 1) * 2 ^ 128 =
      ((-((N * 2 ^ 287 : ℕ) : ℝ) / (W2 G : ℕ) : ℝ) : ℂ) + ((-((N * G * 2 ^ 208 : ℕ) : ℝ) / (W2 G : ℕ) : ℝ) : ℂ) * I := by
  have hW : ((W2 G : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (W2_pos G).ne'
  rw [sG_sub_one]
  have hw := w_ne_zero G
  have e1 : (N : ℂ) / ((-(2 : ℂ) ^ 79 + (G : ℂ) * I) / 2 ^ 80) =
      (N : ℂ) * 2 ^ 80 * (-(2 : ℂ) ^ 79 - (G : ℂ) * I) / ((W2 G : ℕ) : ℂ) := by
    rw [← mul_conj_w G]; field_simp
    have : (-(2 : ℂ) ^ 79 - (G : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [re_two_pow] at this
    field_simp
  rw [e1]
  push_cast
  field_simp
  ring

theorem pole2_eq (N G : ℕ) :
    -(N : ℂ) / (sG G - 1) ^ 2 * 2 ^ 128 =
      ((-((N * 2 ^ 288 : ℕ) : ℝ) * ((2 : ℝ) ^ 158 - (G : ℝ) * G) / ((W2 G * W2 G : ℕ) : ℝ) : ℝ) : ℂ) +
      ((-((N * G * 2 ^ 368 : ℕ) : ℝ) / ((W2 G * W2 G : ℕ) : ℝ) : ℝ) : ℂ) * I := by
  have hW : ((W2 G : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (W2_pos G).ne'
  rw [sG_sub_one]
  have hw := w_ne_zero G
  have hc : (-(2 : ℂ) ^ 79 - (G : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [re_two_pow] at this
  have e1 : -(N : ℂ) / ((-(2 : ℂ) ^ 79 + (G : ℂ) * I) / 2 ^ 80) ^ 2 =
      -(N : ℂ) * 2 ^ 160 * (-(2 : ℂ) ^ 79 - (G : ℂ) * I) ^ 2 / (((W2 G : ℕ) : ℂ) * ((W2 G : ℕ) : ℂ)) := by
    rw [← mul_conj_w G]; field_simp; try ring
  rw [e1]
  push_cast
  field_simp
  ring_nf
  try rw [I_sq]
  try ring

/-- **`remR`**: each component within `k + 2` units (scale `2^128`) of `Rm N k s · 2^128`. -/
theorem remR_spec {N G k : ℕ} (hN : 0 < N) {bern : List (ℤ × ℕ)} (hb : BernOK bern (2 * k + 2)) :
    let r := remR N G bern k
    let V := Rm N k (sG G) * 2 ^ 128
    |(r.1 : ℝ) - V.re| ≤ k + 2 ∧ |(r.2 : ℝ) - V.im| ≤ k + 2 := by
  intro r V
  set vfun : ℕ → ℂ := fun i => emTermC N (sG G) i (poch (sG G) (2 * i + 1)) * 2 ^ 128 with hvf
  set efun : ℕ → GZ := fun i => emTermZ N bern i (pochZ G (2 * i + 1)) with hef
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((vfun i).re - 1 < ((efun i).1 : ℝ) ∧ ((efun i).1 : ℝ) ≤ (vfun i).re) ∧
      ((vfun i).im - 1 < ((efun i).2 : ℝ) ∧ ((efun i).2 : ℝ) ≤ (vfun i).im) := by
    intro i hi
    have hi' : 2 * i + 2 ≤ 2 * k + 2 := by have := Finset.mem_range.mp hi; omega
    exact emTermZ_spec hN hb hi' _ _ (pochZ_spec G _)
  have hs := sum_bounds (k := k) efun vfun hterm
  have hW : 0 < W2 G := by have := W2_pos G; exact_mod_cast this
  have p1 := int_div_bounds_nat (-((N * 2 ^ 287 : ℕ) : ℤ)) hW
  have p2 := int_div_bounds_nat (-((N * G * 2 ^ 208 : ℕ) : ℤ)) hW
  simp only [Int.cast_neg, Int.cast_natCast] at p1 p2
  have hV : V = (N : ℂ) / (sG G - 1) * 2 ^ 128 - 2 ^ 127 +
      ∑ i ∈ Finset.range (k + 1), vfun i := by
    simp only [V, Rm, emTermC, hvf]; rw [← Finset.sum_mul]; ring
  have hVre : V.re = -((N * 2 ^ 287 : ℕ) : ℝ) / (W2 G : ℕ) - 2 ^ 127 +
      (∑ i ∈ Finset.range (k + 1), vfun i).re := by
    rw [hV, Complex.add_re, Complex.sub_re, pole_eq]; simp [re_two_pow]
  have hVim : V.im = -((N * G * 2 ^ 208 : ℕ) : ℝ) / (W2 G : ℕ) +
      (∑ i ∈ Finset.range (k + 1), vfun i).im := by
    rw [hV, Complex.add_im, Complex.sub_im, pole_eq]; simp [im_two_pow]
  set q1 := (-((N * 2 ^ 287 : ℕ) : ℤ)) / ((W2 G : ℕ) : ℤ)
  set q2 := (-((N * G * 2 ^ 208 : ℕ) : ℤ)) / ((W2 G : ℕ) : ℤ)
  set sp := (List.range (k + 1)).map efun |>.foldr gadd (0, 0)
  have hr1 : (r.1 : ℝ) = (q1 : ℝ) - 2 ^ 127 + (sp.1 : ℝ) := by
    show ((q1 - 2 ^ 127 + sp.1 : ℤ) : ℝ) = _; push_cast; ring
  have hr2 : (r.2 : ℝ) = (q2 : ℝ) + (sp.2 : ℝ) := by
    show ((q2 + sp.2 : ℤ) : ℝ) = _; push_cast; ring
  rw [hr1, hr2, hVre, hVim]
  obtain ⟨⟨s1, s2⟩, ⟨s3, s4⟩⟩ := hs
  constructor <;> rw [abs_le] <;> constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]

/-- **`remR1`**: each component within `k + 2` units of `R1m N k s · 2^128`. -/
theorem remR1_spec {N G k : ℕ} (hN : 0 < N) {bern : List (ℤ × ℕ)} (hb : BernOK bern (2 * k + 2)) :
    let r := remR1 N G bern k
    let V := R1m N k (sG G) * 2 ^ 128
    |(r.1 : ℝ) - V.re| ≤ k + 2 ∧ |(r.2 : ℝ) - V.im| ≤ k + 2 := by
  intro r V
  set vfun : ℕ → ℂ := fun i => emTermC N (sG G) i (dpoch (sG G) (2 * i + 1)) * 2 ^ 128 with hvf
  set efun : ℕ → GZ := fun i => emTermZ N bern i (dpochZ G (2 * i + 1)) with hef
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((vfun i).re - 1 < ((efun i).1 : ℝ) ∧ ((efun i).1 : ℝ) ≤ (vfun i).re) ∧
      ((vfun i).im - 1 < ((efun i).2 : ℝ) ∧ ((efun i).2 : ℝ) ≤ (vfun i).im) := by
    intro i hi
    have hi' : 2 * i + 2 ≤ 2 * k + 2 := by have := Finset.mem_range.mp hi; omega
    exact emTermZ_spec hN hb hi' _ _ (dpochZ_spec G _)
  have hs := sum_bounds (k := k) efun vfun hterm
  have hW : 0 < W2 G * W2 G := by have := W2_pos G; have : 0 < W2 G := by exact_mod_cast this
                                  positivity
  have p1 := int_div_bounds_nat (-(((N * 2 ^ 288 : ℕ) : ℤ) * ((2 ^ 158 : ℤ) - (G : ℤ) * G))) hW
  have p2 := int_div_bounds_nat (-((N * G * 2 ^ 368 : ℕ) : ℤ)) hW
  have hV : V = -(N : ℂ) / (sG G - 1) ^ 2 * 2 ^ 128 +
      ∑ i ∈ Finset.range (k + 1), vfun i := by
    simp only [V, R1m, emTermC, hvf]; rw [← Finset.sum_mul]; ring
  have hVre : V.re = -((N * 2 ^ 288 : ℕ) : ℝ) * ((2 : ℝ) ^ 158 - (G : ℝ) * G) / ((W2 G * W2 G : ℕ) : ℝ) +
      (∑ i ∈ Finset.range (k + 1), vfun i).re := by
    rw [hV, Complex.add_re, pole2_eq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have hVim : V.im = -((N * G * 2 ^ 368 : ℕ) : ℝ) / ((W2 G * W2 G : ℕ) : ℝ) +
      (∑ i ∈ Finset.range (k + 1), vfun i).im := by
    rw [hV, Complex.add_im, pole2_eq]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have ea : (((-(((N * 2 ^ 288 : ℕ) : ℤ) * ((2 ^ 158 : ℤ) - (G : ℤ) * G))) : ℤ) : ℝ) =
      -((N * 2 ^ 288 : ℕ) : ℝ) * ((2 : ℝ) ^ 158 - (G : ℝ) * G) := by push_cast; ring
  rw [ea] at p1
  simp only [Int.cast_neg, Int.cast_natCast] at p2
  set q1 := (-(((N * 2 ^ 288 : ℕ) : ℤ) * ((2 ^ 158 : ℤ) - (G : ℤ) * G))) / ((W2 G * W2 G : ℕ) : ℤ)
  set q2 := (-((N * G * 2 ^ 368 : ℕ) : ℤ)) / ((W2 G * W2 G : ℕ) : ℤ)
  set sp := (List.range (k + 1)).map efun |>.foldr gadd (0, 0)
  have hr1 : (r.1 : ℝ) = (q1 : ℝ) + (sp.1 : ℝ) := by
    show ((q1 + sp.1 : ℤ) : ℝ) = _; push_cast; ring
  have hr2 : (r.2 : ℝ) = (q2 : ℝ) + (sp.2 : ℝ) := by
    show ((q2 + sp.2 : ℤ) : ℝ) = _; push_cast; ring
  rw [hr1, hr2, hVre, hVim]
  obtain ⟨⟨s1, s2⟩, ⟨s3, s4⟩⟩ := hs
  have e2 : (-((N * 2 ^ 288 : ℕ) : ℝ) * ((2 : ℝ) ^ 158 - (G : ℝ) * G) / ((W2 G * W2 G : ℕ) : ℝ)) =
      (-((N * 2 ^ 288 : ℕ) : ℝ) * ((2 : ℝ) ^ 158 - (G : ℝ) * G) / ((W2 G * W2 G : ℕ) : ℝ)) := rfl
  constructor <;> rw [abs_le] <;> constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]

end ZetaCert.Eval
