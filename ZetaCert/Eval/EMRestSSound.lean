/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Eval.EMRestSound

@[expose] public section

/-!
# Soundness of `remRS`, `remR1S` (general real part `σ = S/2^80`)
-/

set_option exponentiation.threshold 600

namespace ZetaCert.Eval

open Complex ZetaCert ZetaZeros.EM ZetaZeros.EMDeriv

/-- The point `s = (S + iG) / 2^80`. -/
noncomputable def sSG (S G : ℕ) : ℂ := ((S : ℝ) / 2 ^ 80 : ℝ) + ((G : ℝ) / 2 ^ 80 : ℝ) * I

theorem gz_facS (S G m : ℕ) : gz (facZS S G m) = 2 ^ 80 * (sSG S G + m) := by
  unfold gz facZS sSG; push_cast; field_simp; ring

theorem pochZS_spec (S G m : ℕ) : gz (pochZS S G m) = 2 ^ (80 * m) * poch (sSG S G) m := by
  induction m with
  | zero => simp [pochZS, gz, poch]
  | succ m ih =>
    rw [pochZS, gz_mul, ih, gz_facS, poch_succ]
    rw [show 80 * (m + 1) = 80 * m + 80 by ring, pow_add]; ring

theorem dpochZS_spec (S G m : ℕ) : gz (dpochZS S G m) = 2 ^ (80 * m) * dpoch (sSG S G) m := by
  induction m with
  | zero => simp [dpochZS, gz, dpoch]
  | succ m ih =>
    rw [dpochZS, gz_add, gz_mul, gz_smul, ih, gz_facS, pochZS_spec, dpoch]
    rw [show 80 * (m + 1) = 80 * m + 80 by ring, pow_add]; push_cast; ring

theorem sSG_sub_one (S G : ℕ) : sSG S G - 1 = (((wsZ S : ℤ) : ℂ) + (G : ℂ) * I) / 2 ^ 80 := by
  unfold sSG wsZ; push_cast; field_simp; ring

theorem W2S_pos {S G : ℕ} (hG : 0 < G) : (0 : ℝ) < (W2S S G : ℕ) := by
  unfold W2S; have : 0 < G * G := by positivity
  exact_mod_cast (by omega : 0 < (wsZ S).natAbs * (wsZ S).natAbs + G * G)

theorem W2S_cast (S G : ℕ) : ((W2S S G : ℕ) : ℝ) = ((wsZ S : ℤ) : ℝ) ^ 2 + (G : ℝ) ^ 2 := by
  unfold W2S
  push_cast
  rw [← Int.cast_natCast (wsZ S).natAbs, Int.natCast_natAbs, Int.cast_abs, ← sq, sq_abs]; ring

theorem mul_conj_wS (S G : ℕ) :
    (((wsZ S : ℤ) : ℂ) + (G : ℂ) * I) * (((wsZ S : ℤ) : ℂ) - (G : ℂ) * I) = ((W2S S G : ℕ) : ℂ) := by
  have : ((W2S S G : ℕ) : ℂ) = (((W2S S G : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [this, W2S_cast]; push_cast; ring_nf; rw [I_sq]; ring

theorem poleS_eq (N S G : ℕ) (hG : 0 < G) :
    (N : ℂ) / (sSG S G - 1) * 2 ^ 128 =
      (((((N * 2 ^ 208 : ℕ) : ℝ) * ((wsZ S : ℤ) : ℝ)) / (W2S S G : ℕ) : ℝ) : ℂ) +
      ((-((N * G * 2 ^ 208 : ℕ) : ℝ) / (W2S S G : ℕ) : ℝ) : ℂ) * I := by
  have hW : ((W2S S G : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (W2S_pos (S := S) hG).ne'
  rw [sSG_sub_one]
  have hw : (((wsZ S : ℤ) : ℂ) + (G : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; omega
  have hc : (((wsZ S : ℤ) : ℂ) - (G : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; omega
  have e1 : (N : ℂ) / ((((wsZ S : ℤ) : ℂ) + (G : ℂ) * I) / 2 ^ 80) =
      (N : ℂ) * 2 ^ 80 * (((wsZ S : ℤ) : ℂ) - (G : ℂ) * I) / ((W2S S G : ℕ) : ℂ) := by
    rw [← mul_conj_wS S G]; field_simp
  rw [e1]
  push_cast
  field_simp
  ring

theorem pole2S_eq (N S G : ℕ) (hG : 0 < G) :
    -(N : ℂ) / (sSG S G - 1) ^ 2 * 2 ^ 128 =
      ((-((N * 2 ^ 288 : ℕ) : ℝ) * (((wsZ S : ℤ) : ℝ) * ((wsZ S : ℤ) : ℝ) - (G : ℝ) * G) /
        ((W2S S G * W2S S G : ℕ) : ℝ) : ℝ) : ℂ) +
      (((((N * G * 2 ^ 289 : ℕ) : ℝ) * ((wsZ S : ℤ) : ℝ)) / ((W2S S G * W2S S G : ℕ) : ℝ) : ℝ) : ℂ) * I := by
  have hW : ((W2S S G : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (W2S_pos (S := S) hG).ne'
  rw [sSG_sub_one]
  have hw : (((wsZ S : ℤ) : ℂ) + (G : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; omega
  have hc : (((wsZ S : ℤ) : ℂ) - (G : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; omega
  have e1 : -(N : ℂ) / ((((wsZ S : ℤ) : ℂ) + (G : ℂ) * I) / 2 ^ 80) ^ 2 =
      -(N : ℂ) * 2 ^ 160 * (((wsZ S : ℤ) : ℂ) - (G : ℂ) * I) ^ 2 /
        (((W2S S G : ℕ) : ℂ) * ((W2S S G : ℕ) : ℂ)) := by
    rw [← mul_conj_wS S G]; field_simp; try ring
  rw [e1]
  push_cast
  field_simp
  ring_nf
  try rw [I_sq]
  try ring

theorem remRS_spec {N S G k : ℕ} (hN : 0 < N) (hG : 0 < G) {bern : List (ℤ × ℕ)}
    (hb : BernOK bern (2 * k + 2)) :
    let r := remRS S N G bern k
    let V := Rm N k (sSG S G) * 2 ^ 128
    |(r.1 : ℝ) - V.re| ≤ k + 2 ∧ |(r.2 : ℝ) - V.im| ≤ k + 2 := by
  intro r V
  set vfun : ℕ → ℂ := fun i => emTermC N (sSG S G) i (poch (sSG S G) (2 * i + 1)) * 2 ^ 128 with hvf
  set efun : ℕ → GZ := fun i => emTermZ N bern i (pochZS S G (2 * i + 1)) with hef
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((vfun i).re - 1 < ((efun i).1 : ℝ) ∧ ((efun i).1 : ℝ) ≤ (vfun i).re) ∧
      ((vfun i).im - 1 < ((efun i).2 : ℝ) ∧ ((efun i).2 : ℝ) ≤ (vfun i).im) := by
    intro i hi
    have hi' : 2 * i + 2 ≤ 2 * k + 2 := by have := Finset.mem_range.mp hi; omega
    exact emTermZ_spec (G := G) hN hb hi' _ _ (pochZS_spec S G _)
  have hs := sum_bounds (k := k) efun vfun hterm
  have hW : 0 < W2S S G := by have := W2S_pos (S := S) hG; exact_mod_cast this
  have p1 := int_div_bounds_nat (((N * 2 ^ 208 : ℕ) : ℤ) * wsZ S) hW
  have p2 := int_div_bounds_nat (-((N * G * 2 ^ 208 : ℕ) : ℤ)) hW
  have ea : (((((N * 2 ^ 208 : ℕ) : ℤ) * wsZ S) : ℤ) : ℝ) = ((N * 2 ^ 208 : ℕ) : ℝ) * ((wsZ S : ℤ) : ℝ) := by
    push_cast; ring
  rw [ea] at p1
  simp only [Int.cast_neg, Int.cast_natCast] at p2
  have hV : V = (N : ℂ) / (sSG S G - 1) * 2 ^ 128 - 2 ^ 127 + ∑ i ∈ Finset.range (k + 1), vfun i := by
    simp only [V, Rm, emTermC, hvf]; rw [← Finset.sum_mul]; ring
  have hVre : V.re = ((N * 2 ^ 208 : ℕ) : ℝ) * ((wsZ S : ℤ) : ℝ) / (W2S S G : ℕ) - 2 ^ 127 +
      (∑ i ∈ Finset.range (k + 1), vfun i).re := by
    rw [hV, Complex.add_re, Complex.sub_re, poleS_eq N S G hG]; simp [re_two_pow]
  have hVim : V.im = -((N * G * 2 ^ 208 : ℕ) : ℝ) / (W2S S G : ℕ) +
      (∑ i ∈ Finset.range (k + 1), vfun i).im := by
    rw [hV, Complex.add_im, Complex.sub_im, poleS_eq N S G hG]; simp [im_two_pow]
  set q1 := (((N * 2 ^ 208 : ℕ) : ℤ) * wsZ S) / ((W2S S G : ℕ) : ℤ)
  set q2 := (-((N * G * 2 ^ 208 : ℕ) : ℤ)) / ((W2S S G : ℕ) : ℤ)
  set sp := (List.range (k + 1)).map efun |>.foldr gadd (0, 0)
  have hr1 : (r.1 : ℝ) = (q1 : ℝ) - 2 ^ 127 + (sp.1 : ℝ) := by
    show ((q1 - 2 ^ 127 + sp.1 : ℤ) : ℝ) = _; push_cast; ring
  have hr2 : (r.2 : ℝ) = (q2 : ℝ) + (sp.2 : ℝ) := by
    show ((q2 + sp.2 : ℤ) : ℝ) = _; push_cast; ring
  rw [hr1, hr2, hVre, hVim]
  obtain ⟨⟨s1, s2⟩, ⟨s3, s4⟩⟩ := hs
  constructor <;> rw [abs_le] <;> constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]

theorem remR1S_spec {N S G k : ℕ} (hN : 0 < N) (hG : 0 < G) {bern : List (ℤ × ℕ)}
    (hb : BernOK bern (2 * k + 2)) :
    let r := remR1S S N G bern k
    let V := R1m N k (sSG S G) * 2 ^ 128
    |(r.1 : ℝ) - V.re| ≤ k + 2 ∧ |(r.2 : ℝ) - V.im| ≤ k + 2 := by
  intro r V
  set vfun : ℕ → ℂ := fun i => emTermC N (sSG S G) i (dpoch (sSG S G) (2 * i + 1)) * 2 ^ 128 with hvf
  set efun : ℕ → GZ := fun i => emTermZ N bern i (dpochZS S G (2 * i + 1)) with hef
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((vfun i).re - 1 < ((efun i).1 : ℝ) ∧ ((efun i).1 : ℝ) ≤ (vfun i).re) ∧
      ((vfun i).im - 1 < ((efun i).2 : ℝ) ∧ ((efun i).2 : ℝ) ≤ (vfun i).im) := by
    intro i hi
    have hi' : 2 * i + 2 ≤ 2 * k + 2 := by have := Finset.mem_range.mp hi; omega
    exact emTermZ_spec (G := G) hN hb hi' _ _ (dpochZS_spec S G _)
  have hs := sum_bounds (k := k) efun vfun hterm
  have hW : 0 < W2S S G * W2S S G := by
    have := W2S_pos (S := S) hG; have : 0 < W2S S G := by exact_mod_cast this
    positivity
  have p1 := int_div_bounds_nat (-(((N * 2 ^ 288 : ℕ) : ℤ) * (wsZ S * wsZ S - (G : ℤ) * G))) hW
  have p2 := int_div_bounds_nat (((N * G * 2 ^ 289 : ℕ) : ℤ) * wsZ S) hW
  have hV : V = -(N : ℂ) / (sSG S G - 1) ^ 2 * 2 ^ 128 + ∑ i ∈ Finset.range (k + 1), vfun i := by
    simp only [V, R1m, emTermC, hvf]; rw [← Finset.sum_mul]; ring
  have hVre : V.re = -((N * 2 ^ 288 : ℕ) : ℝ) * (((wsZ S : ℤ) : ℝ) * ((wsZ S : ℤ) : ℝ) - (G : ℝ) * G) /
      ((W2S S G * W2S S G : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), vfun i).re := by
    rw [hV, Complex.add_re, pole2S_eq N S G hG]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have hVim : V.im = ((N * G * 2 ^ 289 : ℕ) : ℝ) * ((wsZ S : ℤ) : ℝ) / ((W2S S G * W2S S G : ℕ) : ℝ) +
      (∑ i ∈ Finset.range (k + 1), vfun i).im := by
    rw [hV, Complex.add_im, pole2S_eq N S G hG]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have ea : (((-(((N * 2 ^ 288 : ℕ) : ℤ) * (wsZ S * wsZ S - (G : ℤ) * G))) : ℤ) : ℝ) =
      -((N * 2 ^ 288 : ℕ) : ℝ) * (((wsZ S : ℤ) : ℝ) * ((wsZ S : ℤ) : ℝ) - (G : ℝ) * G) := by push_cast; ring
  have eb : (((((N * G * 2 ^ 289 : ℕ) : ℤ) * wsZ S) : ℤ) : ℝ) =
      ((N * G * 2 ^ 289 : ℕ) : ℝ) * ((wsZ S : ℤ) : ℝ) := by push_cast; ring
  rw [ea] at p1
  rw [eb] at p2
  set q1 := (-(((N * 2 ^ 288 : ℕ) : ℤ) * (wsZ S * wsZ S - (G : ℤ) * G))) / ((W2S S G * W2S S G : ℕ) : ℤ)
  set q2 := (((N * G * 2 ^ 289 : ℕ) : ℤ) * wsZ S) / ((W2S S G * W2S S G : ℕ) : ℤ)
  set sp := (List.range (k + 1)).map efun |>.foldr gadd (0, 0)
  have hr1 : (r.1 : ℝ) = (q1 : ℝ) + (sp.1 : ℝ) := by
    show ((q1 + sp.1 : ℤ) : ℝ) = _; push_cast; ring
  have hr2 : (r.2 : ℝ) = (q2 : ℝ) + (sp.2 : ℝ) := by
    show ((q2 + sp.2 : ℤ) : ℝ) = _; push_cast; ring
  rw [hr1, hr2, hVre, hVim]
  obtain ⟨⟨s1, s2⟩, ⟨s3, s4⟩⟩ := hs
  constructor <;> rw [abs_le] <;> constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]

end ZetaCert.Eval
