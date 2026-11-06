/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.Eval.ExpSound

/-!
# Soundness of the Dirichlet sums `S = Σ n^{-s}` and `D = -Σ log n · n^{-s}`

* `primeTerm_spec`: `p^{-s}` at `s = 1/2 + it` from certified `w ≈ p^{-1/2}` and `L ≈ log p`.
* `go_spec`: the depth-first enumeration, for any `s` with `0 ≤ Re s`, given prime terms within
  `Ep` of `q^{-s}` and logarithms within `δL` of `log q`: the accumulators move by the sums over
  the visited `n` (the list `goNs`), up to explicit errors.
-/

set_option exponentiation.threshold 600

namespace ZetaCert.Eval

open Complex

/-! ## The prime terms on the critical line -/

theorem rpow_neg_half_sq {p : ℝ} (hp : 0 < p) :
    p ^ (-(1 / 2 : ℝ)) * p ^ (-(1 / 2 : ℝ)) * p = 1 := by
  rw [← Real.rpow_add hp, show (-(1 / 2 : ℝ)) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- `p^{-1/2}` from the integer check `w² p ≤ 2^256 < (w+1)² p`. -/
theorem w_spec {p w : ℕ} (hp : 0 < p) (h1 : w * w * p ≤ 2 ^ 256) (h2 : 2 ^ 256 < (w + 1) * (w + 1) * p) :
    |vP w - (p : ℝ) ^ (-(1 / 2 : ℝ))| ≤ u := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set r := (p : ℝ) ^ (-(1 / 2 : ℝ)) with hr
  have hr0 : 0 < r := by positivity
  have hrsq : r * r * p = 1 := rpow_neg_half_sq hpR
  have h1R : (w : ℝ) * w * p ≤ 2 ^ 256 := by exact_mod_cast h1
  have h2R : (2 : ℝ) ^ 256 < ((w : ℝ) + 1) * (w + 1) * p := by exact_mod_cast h2
  -- w ≤ 2^128 r < w + 1
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have key1 : (w : ℝ) ≤ 2 ^ 128 * r := by
    by_contra hc
    push Not at hc
    have : (2 ^ 128 * r) * (2 ^ 128 * r) * p < (w : ℝ) * w * p := by
      have h0 : 0 ≤ 2 ^ 128 * r := by positivity
      have := mul_self_lt_mul_self h0 hc
      exact mul_lt_mul_of_pos_right this hpR
    have e : (2 ^ 128 * r) * (2 ^ 128 * r) * (p : ℝ) = 2 ^ 256 := by
      have : (2 ^ 128 * r) * (2 ^ 128 * r) * (p : ℝ) = 2 ^ 256 * (r * r * p) := by ring
      rw [this, hrsq, mul_one]
    linarith
  have key2 : 2 ^ 128 * r < (w : ℝ) + 1 := by
    by_contra hc
    push Not at hc
    have : ((w : ℝ) + 1) * (w + 1) * p ≤ (2 ^ 128 * r) * (2 ^ 128 * r) * p := by
      have h0 : 0 ≤ (w : ℝ) + 1 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_self_le_mul_self h0 hc) hpR.le
    have e : (2 ^ 128 * r) * (2 ^ 128 * r) * (p : ℝ) = 2 ^ 256 := by
      have : (2 ^ 128 * r) * (2 ^ 128 * r) * (p : ℝ) = 2 ^ 256 * (r * r * p) := by ring
      rw [this, hrsq, mul_one]
    linarith
  unfold vP u
  rw [abs_le]
  constructor
  · have : r - 1 / 2 ^ 128 < (w : ℝ) / 2 ^ 128 := by
      rw [lt_div_iff₀ (by positivity)]
      have : (r - 1 / 2 ^ 128) * 2 ^ 128 = 2 ^ 128 * r - 1 := by field_simp
      rw [this]; linarith
    linarith
  · have : (w : ℝ) / 2 ^ 128 ≤ r := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith

theorem cpow_neg_crit {p : ℕ} (hp : 0 < p) (t : ℝ) :
    (p : ℂ) ^ (-(1 / 2 + t * I)) =
      (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-I * ((t * Real.log p : ℝ) : ℂ)) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp', Complex.ofReal_cpow (by positivity),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  rw [← Complex.exp_add]; congr 1
  rw [show ((p : ℝ) : ℂ) = (p : ℂ) by push_cast; rfl, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (by positivity)]
  push_cast; ring

/-- Multiplying an offset pair by a plain `w`. -/
theorem mulOP_pair_spec {a b w : ℕ} (ha : |vO a| ≤ 2) (hb : |vO b| ≤ 2) (hw : vP w ≤ 1) :
    ‖cv (mulOP a w) (mulOP b w) - (vP w : ℂ) * cv a b‖ ≤ 2 * u := by
  have hw0 := vP_nonneg w
  rw [abs_le] at ha hb
  obtain ⟨a1, a2⟩ := vO_mulOP (X := a) (y := w) (by nlinarith)
  obtain ⟨b1, b2⟩ := vO_mulOP (X := b) (y := w) (by nlinarith)
  rw [show 2 * u = u + u by ring]
  apply norm_le_of_parts
  · simp only [Complex.sub_re, cv_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, cv_im]
    rw [abs_le]; constructor <;> nlinarith
  · simp only [Complex.sub_im, cv_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, cv_re]
    rw [abs_le]; constructor <;> nlinarith

/-- **`p^{-s}` on the critical line.** -/
theorem primeTerm_spec {K T w L p : ℕ} {t δL : ℝ} (hp : 0 < p)
    (hw1 : w * w * p ≤ 2 ^ 256) (hw2 : 2 ^ 256 < (w + 1) * (w + 1) * p)
    (hT : vP T = t) (hL : |vP L - Real.log p| ≤ δL)
    (hx : halfArg K T L ≤ EIGHTH) (hK : K ≤ 40) (hδ : t * δL ≤ 1 / 2 ^ 42) :
    ‖cv (primeTerm K T w L).1 (primeTerm K T w L).2 - (p : ℂ) ^ (-(1 / 2 + t * I))‖ ≤
      2 ^ (K + 1) * (77 * u) + 2 * (t * δL) + 3 * u := by
  have ht0 : 0 ≤ t := hT ▸ vP_nonneg T
  have hθ : |vP T * vP L - t * Real.log p| ≤ t * δL := by
    rw [hT, ← mul_sub, abs_mul, abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_left hL ht0
  have he := expNegI_spec (θ := t * Real.log p) hθ hx hK hδ
  set c := expNegI K T L
  set E := 2 ^ (K + 1) * (77 * u) + 2 * (t * δL)
  have hwr := w_spec hp hw1 hw2
  set r := (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by norm_num)
  have hz : ‖cexp (-I * ((t * Real.log p : ℝ) : ℂ))‖ = 1 := by
    rw [show -I * ((t * Real.log p : ℝ) : ℂ) = ((-(t * Real.log p)) : ℝ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hE1 : E ≤ 1 := by
    have h2K : (2 : ℝ) ^ (K + 1) ≤ 2 ^ 41 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : 2 ^ (K + 1) * (77 * u) ≤ 2 ^ 41 * (77 * u) := by gcongr; linarith [u_pos]
    have : 2 ^ 41 * (77 * u) + 2 * (1 / 2 ^ 42) ≤ (1 : ℝ) := by unfold u; norm_num
    simp only [E]; linarith
  have hcn : ‖cv c.1 c.2‖ ≤ 2 := by
    have := norm_sub_norm_le (cv c.1 c.2) (cexp (-I * ((t * Real.log p : ℝ) : ℂ))); linarith
  have hw1' : vP w ≤ 1 := by
    have := (abs_le.mp hwr).2; have : vP w ≤ r + u := by linarith
    -- vP w ≤ 2^128 r / 2^128 ≤ r ≤ 1 (from w ≤ 2^128 r)
    have hwle : vP w ≤ r := by
      unfold vP
      have h1R : (w : ℝ) * w * p ≤ 2 ^ 256 := by exact_mod_cast hw1
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp
      have hrsq : r * r * p = 1 := rpow_neg_half_sq hpR
      rw [div_le_iff₀ (by positivity)]
      by_contra hc; push Not at hc
      have h0 : 0 ≤ r * 2 ^ 128 := by positivity
      have := mul_lt_mul_of_pos_right (mul_self_lt_mul_self h0 hc) hpR
      have e : (r * 2 ^ 128) * (r * 2 ^ 128) * (p : ℝ) = 2 ^ 256 := by
        have : (r * 2 ^ 128) * (r * 2 ^ 128) * (p : ℝ) = 2 ^ 256 * (r * r * p) := by ring
        rw [this, hrsq, mul_one]
      linarith
    linarith
  have hm := mulOP_pair_spec (a := c.1) (b := c.2) (w := w)
    ((Complex.abs_re_le_norm _).trans hcn) ((Complex.abs_im_le_norm _).trans hcn) hw1'
  rw [cpow_neg_crit hp t]
  unfold primeTerm
  simp only
  set z := cexp (-I * ((t * Real.log p : ℝ) : ℂ))
  have e : cv (mulOP c.1 w) (mulOP c.2 w) - (r : ℂ) * z =
      (cv (mulOP c.1 w) (mulOP c.2 w) - (vP w : ℂ) * cv c.1 c.2) + (vP w : ℂ) * (cv c.1 c.2 - z)
        + ((vP w - r : ℝ) : ℂ) * z := by push_cast; ring
  rw [e]
  have n1 := norm_add_le ((cv (mulOP c.1 w) (mulOP c.2 w) - (vP w : ℂ) * cv c.1 c.2) +
    (vP w : ℂ) * (cv c.1 c.2 - z)) (((vP w - r : ℝ) : ℂ) * z)
  have n2 := norm_add_le (cv (mulOP c.1 w) (mulOP c.2 w) - (vP w : ℂ) * cv c.1 c.2)
    ((vP w : ℂ) * (cv c.1 c.2 - z))
  have n3 : ‖(vP w : ℂ) * (cv c.1 c.2 - z)‖ ≤ E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vP_nonneg w)]
    calc vP w * ‖cv c.1 c.2 - z‖ ≤ 1 * E := mul_le_mul hw1' he (norm_nonneg _) (by norm_num)
      _ = E := one_mul _
  have n4 : ‖((vP w - r : ℝ) : ℂ) * z‖ ≤ u := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hwr
  linarith

/-! ## The depth-first enumeration -/

/-- Value of the `S` accumulator. -/
noncomputable def accS (a : Acc) : ℂ := cv a.sr a.si
/-- Value of the `D` accumulator. -/
noncomputable def accD (a : Acc) : ℂ := cv a.dr a.di

/-- One complex product of approximations, within `ea (1 + eb) + eb + 3u`. -/
theorem cmul_spec {ar ai br bi : ℕ} {a b : ℂ} {ea eb : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hea : ‖cv ar ai - a‖ ≤ ea) (heb : ‖cv br bi - b‖ ≤ eb) (hea1 : ea ≤ 1) (heb1 : eb ≤ 1) :
    ‖cv (subO (mulO ar br) (mulO ai bi)) (addO (mulO ar bi) (mulO ai br)) - a * b‖ ≤
      ea * (1 + eb) + eb + 3 * u := by
  have hna : ‖cv ar ai‖ ≤ 2 := by have := norm_sub_norm_le (cv ar ai) a; linarith
  have hnb : ‖cv br bi‖ ≤ 2 := by have := norm_sub_norm_le (cv br bi) b; linarith
  have h1 : |vO ar| ≤ 2 := (Complex.abs_re_le_norm (cv ar ai)).trans hna
  have h2 : |vO ai| ≤ 2 := (Complex.abs_im_le_norm (cv ar ai)).trans hna
  have h3 : |vO br| ≤ 2 := (Complex.abs_re_le_norm (cv br bi)).trans hnb
  have h4 : |vO bi| ≤ 2 := (Complex.abs_im_le_norm (cv br bi)).trans hnb
  rw [abs_le] at h1 h2 h3 h4
  have hu := u_pos
  have hu1 : u ≤ 1 := by unfold u; rw [div_le_one (by positivity)]; norm_num
  obtain ⟨p1, p2⟩ := vO_mulO (X := ar) (Y := br) (by nlinarith)
  obtain ⟨q1, q2⟩ := vO_mulO (X := ai) (Y := bi) (by nlinarith)
  obtain ⟨r1, r2⟩ := vO_mulO (X := ar) (Y := bi) (by nlinarith)
  obtain ⟨s1, s2⟩ := vO_mulO (X := ai) (Y := br) (by nlinarith)
  have hre : vO (subO (mulO ar br) (mulO ai bi)) = vO (mulO ar br) - vO (mulO ai bi) :=
    vO_subO (by nlinarith)
  have him : vO (addO (mulO ar bi) (mulO ai br)) = vO (mulO ar bi) + vO (mulO ai br) :=
    vO_addO (by nlinarith)
  have hround : ‖cv (subO (mulO ar br) (mulO ai bi)) (addO (mulO ar bi) (mulO ai br)) -
      cv ar ai * cv br bi‖ ≤ 3 * u := by
    rw [show 3 * u = u + 2 * u by ring]
    apply norm_le_of_parts
    · simp only [Complex.sub_re, cv_re, Complex.mul_re, cv_im, hre]
      rw [abs_le]; constructor <;> linarith
    · simp only [Complex.sub_im, cv_im, Complex.mul_im, cv_re, him]
      rw [abs_le]; constructor <;> linarith
  have hprod : ‖cv ar ai * cv br bi - a * b‖ ≤ ea * (1 + eb) + eb := by
    have e : cv ar ai * cv br bi - a * b = (cv ar ai - a) * cv br bi + a * (cv br bi - b) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hnb' : ‖cv br bi‖ ≤ 1 + eb := by have := norm_sub_norm_le (cv br bi) b; linarith
    have hea0 : 0 ≤ ea := (norm_nonneg _).trans hea
    have t1 : ‖cv ar ai - a‖ * ‖cv br bi‖ ≤ ea * (1 + eb) :=
      mul_le_mul hea hnb' (norm_nonneg _) hea0
    have t2 : ‖a‖ * ‖cv br bi - b‖ ≤ 1 * eb := mul_le_mul ha heb (norm_nonneg _) (by norm_num)
    linarith
  calc _ ≤ ‖cv (subO (mulO ar br) (mulO ai bi)) (addO (mulO ar bi) (mulO ai br)) -
        cv ar ai * cv br bi‖ + ‖cv ar ai * cv br bi - a * b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- Pushing one term into the accumulators. -/
theorem push_spec {acc : Acc} {vr vi ln : ℕ} {z : ℂ} {ℓ e dl Λ : ℝ}
    (hz : ‖z‖ ≤ 1) (he : ‖cv vr vi - z‖ ≤ e) (he1 : e ≤ 1) (hl : |vP ln - ℓ| ≤ dl)
    (hΛ : vP ln ≤ Λ) (hΛ1 : Λ ≤ 2 ^ 20)
    (hS : ‖accS acc‖ ≤ 2 ^ 60) (hD : ‖accD acc‖ ≤ 2 ^ 60) :
    accS (acc.push vr vi ln) = accS acc + cv vr vi ∧
    ‖accD (acc.push vr vi ln) - (accD acc - (ℓ : ℂ) * z)‖ ≤ Λ * e + dl + 2 * u ∧
    ‖accD (acc.push vr vi ln) - accD acc‖ ≤ 2 * Λ + 2 * u := by
  have hn : ‖cv vr vi‖ ≤ 2 := by have := norm_sub_norm_le (cv vr vi) z; linarith
  have h1 : |vO vr| ≤ 2 := (Complex.abs_re_le_norm (cv vr vi)).trans hn
  have h2 : |vO vi| ≤ 2 := (Complex.abs_im_le_norm (cv vr vi)).trans hn
  have hs1 : |vO acc.sr| ≤ 2 ^ 60 := (Complex.abs_re_le_norm (accS acc)).trans hS
  have hs2 : |vO acc.si| ≤ 2 ^ 60 := (Complex.abs_im_le_norm (accS acc)).trans hS
  have hd1 : |vO acc.dr| ≤ 2 ^ 60 := (Complex.abs_re_le_norm (accD acc)).trans hD
  have hd2 : |vO acc.di| ≤ 2 ^ 60 := (Complex.abs_im_le_norm (accD acc)).trans hD
  have hl0 := vP_nonneg ln
  rw [abs_le] at h1 h2 hs1 hs2 hd1 hd2
  have hu := u_pos
  have hu1 : u ≤ 1 := by unfold u; rw [div_le_one (by positivity)]; norm_num
  obtain ⟨m1, m2⟩ := vO_mulOP (X := vr) (y := ln) (by nlinarith)
  obtain ⟨n1, n2⟩ := vO_mulOP (X := vi) (y := ln) (by nlinarith)
  have eS1 : vO (addO acc.sr vr) = vO acc.sr + vO vr := vO_addO (by linarith)
  have eS2 : vO (addO acc.si vi) = vO acc.si + vO vi := vO_addO (by linarith)
  have eD1 : vO (subO acc.dr (mulOP vr ln)) = vO acc.dr - vO (mulOP vr ln) := vO_subO (by nlinarith)
  have eD2 : vO (subO acc.di (mulOP vi ln)) = vO acc.di - vO (mulOP vi ln) := vO_subO (by nlinarith)
  have hround : ‖accD (acc.push vr vi ln) - (accD acc - (vP ln : ℂ) * cv vr vi)‖ ≤ 2 * u := by
    rw [show 2 * u = u + u by ring]
    apply norm_le_of_parts
    · simp only [accD, Acc.push, Complex.sub_re, cv_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, cv_im, eD1]
      rw [abs_le]; constructor <;> linarith
    · simp only [accD, Acc.push, Complex.sub_im, cv_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, cv_re, eD2]
      rw [abs_le]; constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ext
    · simp only [accS, Acc.push, cv_re, Complex.add_re, eS1]
    · simp only [accS, Acc.push, cv_im, Complex.add_im, eS2]
  · have hp : ‖(vP ln : ℂ) * cv vr vi - (ℓ : ℂ) * z‖ ≤ Λ * e + dl := by
      have e1 : (vP ln : ℂ) * cv vr vi - (ℓ : ℂ) * z = (vP ln : ℂ) * (cv vr vi - z) + ((vP ln - ℓ : ℝ) : ℂ) * z := by
        push_cast; ring
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hl0]
      have hΛ0 : 0 ≤ Λ := hl0.trans hΛ
      have t1 : vP ln * ‖cv vr vi - z‖ ≤ Λ * e := mul_le_mul hΛ he (norm_nonneg _) hΛ0
      have t2 : |vP ln - ℓ| * ‖z‖ ≤ dl * 1 := mul_le_mul hl hz (norm_nonneg _) ((abs_nonneg _).trans hl)
      linarith
    have := norm_sub_le_norm_sub_add_norm_sub (accD (acc.push vr vi ln))
      (accD acc - (vP ln : ℂ) * cv vr vi) (accD acc - (ℓ : ℂ) * z)
    have e2 : accD acc - (vP ln : ℂ) * cv vr vi - (accD acc - (ℓ : ℂ) * z) =
        -((vP ln : ℂ) * cv vr vi - (ℓ : ℂ) * z) := by ring
    rw [e2, norm_neg] at this
    linarith
  · have := norm_sub_le_norm_sub_add_norm_sub (accD (acc.push vr vi ln))
      (accD acc - (vP ln : ℂ) * cv vr vi) (accD acc)
    rw [show accD acc - (vP ln : ℂ) * cv vr vi - accD acc = -((vP ln : ℂ) * cv vr vi) by ring,
      norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0] at this
    have : vP ln * ‖cv vr vi‖ ≤ Λ * 2 := mul_le_mul hΛ hn (norm_nonneg _) (hl0.trans hΛ)
    linarith

/-- Hypotheses on the prime list: each term within `Ep` of `q^{-s}`, each log within `δL`. -/
def PrimesOK (s : ℂ) (Ep δL : ℝ) (ps : List PT) : Prop :=
  ∀ q ∈ ps, 2 ≤ q.p ∧ ‖cv q.re q.im - (q.p : ℂ) ^ (-s)‖ ≤ Ep ∧ |vP q.L - Real.log q.p| ≤ δL

theorem natCast_cpow_neg_mul (m n : ℕ) (s : ℂ) :
    ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
  rw [Nat.cast_mul, ← Complex.natCast_mul_natCast_cpow]

theorem norm_natCast_cpow_neg_le {s : ℂ} (hs : 0 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
  simp only [Complex.neg_re]; linarith

/-- The term function of `S`. -/
noncomputable def fS (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)
/-- The term function of `D`. -/
noncomputable def fD (s : ℂ) (n : ℕ) : ℂ := -((Real.log n : ℝ) : ℂ) * (n : ℂ) ^ (-s)

/-- **The depth-first enumeration.** -/
theorem go_spec (N : ℕ) (s : ℂ) (hs : 0 ≤ s.re) (Ep δL Λ : ℝ) (Dp : ℕ)
    (hN : N < 2 ^ Dp) (hEp1 : Ep ≤ 1) (hδL : 0 ≤ δL)
    (hsmall : (Dp : ℝ) * (Ep + 4 * u) * Ep ≤ u) (hsmall1 : (Dp : ℝ) * (Ep + 4 * u) ≤ 1)
    (hΛ : Real.log N + Dp * δL ≤ Λ) (hΛ1 : Λ ≤ 2 ^ 20) :
    ∀ (fuel : ℕ) (ps : List PT) (m ur ui lm : ℕ) (acc : Acc) (d : ℕ), PrimesOK s Ep δL ps →
      1 ≤ m → m ≤ N → 2 ^ d ≤ m → ‖cv ur ui - (m : ℂ) ^ (-s)‖ ≤ d * (Ep + 4 * u) →
      |vP lm - Real.log m| ≤ d * δL →
      let ns := goNs N fuel (ps.map PT.p) m
      ‖accS acc‖ + 2 * ns.length ≤ 2 ^ 60 → ‖accD acc‖ + (2 * Λ + 2 * u) * ns.length ≤ 2 ^ 60 →
      let acc' := go N fuel ps m ur ui lm acc
      ‖accS acc' - accS acc - (ns.map (fS s)).sum‖ ≤ ns.length * (Dp * (Ep + 4 * u)) ∧
      ‖accD acc' - accD acc - (ns.map (fD s)).sum‖ ≤
        ns.length * (Λ * (Dp * (Ep + 4 * u)) + Dp * δL + 2 * u) ∧
      ‖accS acc' - accS acc‖ ≤ 2 * ns.length ∧
      ‖accD acc' - accD acc‖ ≤ (2 * Λ + 2 * u) * ns.length := by
  have hu := u_pos
  intro fuel
  induction fuel with
  | zero => intro ps m ur ui lm acc d _ _ _ _ _ _ ns _ _ acc'; simp [ns, acc', go, goNs]
  | succ fuel ih =>
    intro ps m ur ui lm acc d hps hm1 hmN hd hum hlm
    cases ps with
    | nil => intro ns _ _ acc'; simp [ns, acc', go, goNs]
    | cons q qs =>
      intro ns hS hD acc'
      obtain ⟨hq2, hqe, hql⟩ := hps q (List.mem_cons_self ..)
      have hqs : PrimesOK s Ep δL qs := fun r hr => hps r (List.mem_cons_of_mem _ hr)
      cases hble : Nat.ble (Nat.mul m q.p) N with
      | false =>
        have hns : ns = [] := by simp only [ns, List.map_cons, goNs, hble]
        have hacc : acc' = acc := by simp only [acc', go, hble]
        simp [hns, hacc]
      | true =>
        set n := m * q.p with hn
        have hnN : n ≤ N := Nat.le_of_ble_eq_true hble
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have hdD : d < Dp := by
          have : 2 ^ d < 2 ^ Dp := lt_of_le_of_lt (hd.trans hmN) hN
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
        have hd1D : d + 1 ≤ Dp := hdD
        have hdR : (d : ℝ) + 1 ≤ Dp := by exact_mod_cast hd1D
        set E' := Ep + 4 * u
        have hE'0 : 0 ≤ E' := by
          have : 0 ≤ Ep := (norm_nonneg _).trans hqe; simp only [E']; linarith
        have hEp0 : 0 ≤ Ep := (norm_nonneg _).trans hqe
        -- the new term
        set vr := subO (mulO ur q.re) (mulO ui q.im)
        set vi := addO (mulO ur q.im) (mulO ui q.re)
        set ln := Nat.add lm q.L
        have hzm := norm_natCast_cpow_neg_le hs hm1
        have hzq := norm_natCast_cpow_neg_le hs (by omega : 1 ≤ q.p)
        have hdE : (d : ℝ) * E' ≤ 1 := by
          have : (d : ℝ) * E' ≤ Dp * E' := by gcongr <;> linarith
          linarith
        have hv := cmul_spec hzm hzq hum hqe hdE hEp1
        rw [← natCast_cpow_neg_mul] at hv
        have hve : ‖cv vr vi - (n : ℂ) ^ (-s)‖ ≤ (d + 1 : ℕ) * E' := by
          refine hv.trans ?_
          push_cast
          have : (d : ℝ) * E' * Ep ≤ u := by
            have : (d : ℝ) * E' * Ep ≤ Dp * E' * Ep := by gcongr <;> linarith
            linarith
          simp only [E'] at *; linarith
        have hln : |vP ln - Real.log n| ≤ (d + 1 : ℕ) * δL := by
          have e : vP ln = vP lm + vP q.L := by
            show vP (lm + q.L) = _; exact vP_add _ _
          rw [e, hn]; push_cast
          rw [Real.log_mul (by positivity) (by positivity)]
          have := abs_add_le (vP lm - Real.log m) (vP q.L - Real.log q.p)
          rw [show vP lm + vP q.L - (Real.log m + Real.log q.p) =
            (vP lm - Real.log m) + (vP q.L - Real.log q.p) by ring]
          linarith
        have hnd : 2 ^ (d + 1) ≤ n := by rw [pow_succ, hn]; exact Nat.mul_le_mul hd hq2
        -- vP ln ≤ Λ
        have hlnΛ : vP ln ≤ Λ := by
          have h1 := (abs_le.mp hln).2
          have h2 : Real.log n ≤ Real.log N := Real.log_le_log (by positivity) (by exact_mod_cast hnN)
          have h3 : ((d + 1 : ℕ) : ℝ) * δL ≤ Dp * δL := by
            apply mul_le_mul_of_nonneg_right _ hδL; push_cast; exact hdR
          linarith
        have hveD : ‖cv vr vi - (n : ℂ) ^ (-s)‖ ≤ Dp * E' := by
          refine hve.trans ?_; apply mul_le_mul_of_nonneg_right _ hE'0; exact_mod_cast hd1D
        have hlnD : |vP ln - Real.log n| ≤ Dp * δL := by
          refine hln.trans ?_; apply mul_le_mul_of_nonneg_right _ hδL; exact_mod_cast hd1D
        have hn2 : ‖cv vr vi‖ ≤ 2 := by
          have := norm_sub_norm_le (cv vr vi) ((n : ℂ) ^ (-s))
          have := norm_natCast_cpow_neg_le hs hn1
          linarith
        -- lists
        set nsc := goNs N fuel ((q :: qs).map PT.p) n
        set nss := goNs N fuel (qs.map PT.p) m
        have hns : ns = n :: (nsc ++ nss) := by
          simp only [ns, nsc, nss, List.map_cons, goNs, hble, n]; rfl
        have hlen : ns.length = 1 + nsc.length + nss.length := by
          rw [hns]; simp; ring
        rw [hlen] at hS hD
        push_cast at hS hD
        have hS0 : ‖accS acc‖ ≤ 2 ^ 60 := by linarith
        have hD0 : ‖accD acc‖ ≤ 2 ^ 60 := by
          have : 0 ≤ (2 * Λ + 2 * u) * (1 + (nsc.length : ℝ) + nss.length) := by
            have : 0 ≤ Λ := (vP_nonneg _).trans hlnΛ; positivity
          linarith
        have hP := push_spec (acc := acc) (norm_natCast_cpow_neg_le hs hn1) hve
          (le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hd1D) hE'0) hsmall1)
          hln hlnΛ hΛ1 hS0 hD0
        obtain ⟨hP1, hP2, hP3⟩ := hP
        set acc1 := acc.push vr vi ln
        -- child
        have hS1 : ‖accS acc1‖ + 2 * nsc.length ≤ 2 ^ 60 := by
          rw [hP1]
          have := norm_add_le (accS acc) (cv vr vi)
          have : (0 : ℝ) ≤ nss.length := by positivity
          linarith
        have hD1 : ‖accD acc1‖ + (2 * Λ + 2 * u) * nsc.length ≤ 2 ^ 60 := by
          have := norm_sub_norm_le (accD acc1) (accD acc)
          have : 0 ≤ (2 * Λ + 2 * u) * (nss.length : ℝ) := by
            have : 0 ≤ Λ := (vP_nonneg _).trans hlnΛ; positivity
          linarith
        have IHc := ih (q :: qs) n vr vi ln acc1 (d + 1) hps hn1 hnN hnd hve hln hS1 hD1
        obtain ⟨c1, c2, c3, c4⟩ := IHc
        set acc2 := go N fuel (q :: qs) n vr vi ln acc1
        -- sibling
        have hS2 : ‖accS acc2‖ + 2 * nss.length ≤ 2 ^ 60 := by
          have := norm_sub_norm_le (accS acc2) (accS acc1)
          rw [hP1] at this
          have := norm_add_le (accS acc) (cv vr vi)
          rw [hP1] at c3
          linarith
        have hD2 : ‖accD acc2‖ + (2 * Λ + 2 * u) * nss.length ≤ 2 ^ 60 := by
          have := norm_sub_norm_le (accD acc2) (accD acc1)
          have := norm_sub_norm_le (accD acc1) (accD acc)
          linarith
        have IHs := ih qs m ur ui lm acc2 d hqs hm1 hmN hd hum hlm hS2 hD2
        obtain ⟨s1, s2, s3, s4⟩ := IHs
        have hacc : acc' = go N fuel qs m ur ui lm acc2 := by
          simp only [acc', go, hble, force_eq]; rfl
        rw [hacc, hns]
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append, List.length_cons,
          List.length_append]
        set acc3 := go N fuel qs m ur ui lm acc2
        push_cast
        refine ⟨?_, ?_, ?_, ?_⟩
        · have e : accS acc3 - accS acc - (fS s n + ((nsc.map (fS s)).sum + (nss.map (fS s)).sum)) =
              (accS acc1 - accS acc - fS s n) + (accS acc2 - accS acc1 - (nsc.map (fS s)).sum) +
              (accS acc3 - accS acc2 - (nss.map (fS s)).sum) := by ring
          rw [e]
          have t0 : ‖accS acc1 - accS acc - fS s n‖ ≤ Dp * E' := by
            rw [hP1]; simp only [fS]; rw [show accS acc + cv vr vi - accS acc = cv vr vi by ring]
            exact hveD
          have := norm_add_le ((accS acc1 - accS acc - fS s n) + (accS acc2 - accS acc1 - (nsc.map (fS s)).sum)) (accS acc3 - accS acc2 - (nss.map (fS s)).sum)
          have := norm_add_le (accS acc1 - accS acc - fS s n) (accS acc2 - accS acc1 - (nsc.map (fS s)).sum)
          linarith
        · have e : accD acc3 - accD acc - (fD s n + ((nsc.map (fD s)).sum + (nss.map (fD s)).sum)) =
              (accD acc1 - accD acc - fD s n) + (accD acc2 - accD acc1 - (nsc.map (fD s)).sum) +
              (accD acc3 - accD acc2 - (nss.map (fD s)).sum) := by ring
          rw [e]
          have t0 : ‖accD acc1 - accD acc - fD s n‖ ≤ Λ * (Dp * E') + Dp * δL + 2 * u := by
            have e2 : accD acc1 - accD acc - fD s n = accD acc1 - (accD acc - (Real.log n : ℂ) * (n : ℂ) ^ (-s)) := by
              simp only [fD]; ring
            rw [e2]
            refine hP2.trans ?_
            have hΛ0 : 0 ≤ Λ := (vP_nonneg _).trans hlnΛ
            have : Λ * (((d + 1 : ℕ) : ℝ) * E') ≤ Λ * (Dp * E') := by
              apply mul_le_mul_of_nonneg_left _ hΛ0
              apply mul_le_mul_of_nonneg_right _ hE'0; push_cast; exact hdR
            have : ((d + 1 : ℕ) : ℝ) * δL ≤ Dp * δL := by
              apply mul_le_mul_of_nonneg_right _ hδL; push_cast; exact hdR
            linarith
          have := norm_add_le ((accD acc1 - accD acc - fD s n) + (accD acc2 - accD acc1 - (nsc.map (fD s)).sum)) (accD acc3 - accD acc2 - (nss.map (fD s)).sum)
          have := norm_add_le (accD acc1 - accD acc - fD s n) (accD acc2 - accD acc1 - (nsc.map (fD s)).sum)
          linarith
        · have e : accS acc3 - accS acc = (accS acc1 - accS acc) + (accS acc2 - accS acc1) +
              (accS acc3 - accS acc2) := by ring
          rw [e]
          have t0 : ‖accS acc1 - accS acc‖ ≤ 2 := by
            rw [hP1, show accS acc + cv vr vi - accS acc = cv vr vi by ring]
            exact hn2
          have := norm_add_le ((accS acc1 - accS acc) + (accS acc2 - accS acc1)) (accS acc3 - accS acc2)
          have := norm_add_le (accS acc1 - accS acc) (accS acc2 - accS acc1)
          linarith
        · have e : accD acc3 - accD acc = (accD acc1 - accD acc) + (accD acc2 - accD acc1) +
              (accD acc3 - accD acc2) := by ring
          rw [e]
          have := norm_add_le ((accD acc1 - accD acc) + (accD acc2 - accD acc1)) (accD acc3 - accD acc2)
          have := norm_add_le (accD acc1 - accD acc) (accD acc2 - accD acc1)
          linarith

end ZetaCert.Eval
