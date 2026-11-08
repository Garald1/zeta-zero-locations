/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Leg

@[expose] public section

/-!
# Leg points at low heights

Copies of `ZetaCert.norm_zeta''_le_leg` and `ZetaCert.seg_of_lc` (ZetaCert/Leg.lean) with the
height hypothesis `10 ≤ T` weakened to `3 ≤ T` (the proofs only need `T - 2 > 0`), for the leg at
`T = 3` that starts the window count of `Zeros0to1000`.
-/

open Complex Metric Set

namespace ZetaCert

open ZetaZeros.Deriv

theorem norm_zeta''_le_leg3 {m : ℕ} (hm : 1 ≤ m) {T : ℝ} (hT : 3 ≤ T) {z : ℂ} (hz : 7 / 16 ≤ z.re)
    (hzi : |z.im - T| ≤ 1 / 16) : ‖deriv (deriv riemannZeta) z‖ ≤ M2 m T := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  rw [abs_le] at hzi
  have h := norm_deriv_deriv_zeta_le (m ^ 4) (Nat.one_le_pow _ _ (by omega)) (σ₀ := 1 / 4)
    (T₀ := T + 1 / 4) (δ := T - 2) (R := 3 / 16) (by norm_num) (by linarith) (by norm_num) (z := z)
    (by linarith) ?_ ?_
  · refine h.trans ?_
    have hN : ((m ^ 4 : ℕ) : ℝ) = (m : ℝ) ^ 4 := by push_cast; ring
    have hq : ((m : ℝ) ^ 4) ^ (-(1 / 4 : ℝ)) = 1 / m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num; try rw [Real.rpow_neg_one]
    have hq3 : ((m : ℝ) ^ 4) ^ (1 - 1 / 4 : ℝ) = (m : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num; try rw [Real.rpow_neg_one]
    have hsum : ∑ k ∈ Finset.Icc 1 (m ^ 4), (k : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (m : ℝ) ^ 4 := by
      calc ∑ k ∈ Finset.Icc 1 (m ^ 4), (k : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ∑ k ∈ Finset.Icc 1 (m ^ 4), (1 : ℝ) := by
            apply Finset.sum_le_sum; intro k hk
            have : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
            exact Real.rpow_le_one_of_one_le_of_nonpos this (by norm_num)
        _ = (m : ℝ) ^ 4 := by simp
    rw [hN, hq, hq3]
    unfold M2
    have e : (1 + (T + 1 / 4) / (1 / 4)) * (1 / (m : ℝ)) = (1 + 4 * (T + 1 / 4)) / m := by field_simp
    have e2 : (1 / (m : ℝ)) / 2 = 1 / (2 * m) := by field_simp
    rw [e, e2]
    gcongr
  · rw [abs_of_pos (by linarith)]; linarith
  · have h1 : T - 2 + 3 / 16 ≤ |(z - 1).im| := by
      simp only [Complex.sub_im, Complex.one_im, sub_zero]
      rw [abs_of_pos (by linarith)]; linarith
    exact h1.trans (Complex.abs_im_le_norm _)

/-- A leg-point certificate gives positivity of `Re ζ` on `[σ - h, σ + h] + iγ`. -/
theorem seg_of_lc3 {j G N K k fuel Dp m : ℕ} {v d : ℚ} {h : ℝ} (hc : lc j G N K k fuel Dp v d = true)
    (hm : 1 ≤ m) (hj : (2048 : ℝ) ≤ j) (hγ : 3 ≤ (G : ℝ) / 2 ^ 80) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 16)
    (hpos : h * d + h ^ 2 * M2 m ((G : ℝ) / 2 ^ 80) < v) :
    ∀ σ ∈ Icc ((j : ℝ) / 4096 - h) ((j : ℝ) / 4096 + h),
      0 < (riemannZeta (σ + ((G : ℝ) / 2 ^ 80 : ℝ) * I)).re := by
  intro σ hσ
  obtain ⟨hv, hd⟩ := lc_spec hc
  set c : ℂ := (((j : ℝ) / 4096 : ℝ) : ℂ) + (((G : ℝ) / 2 ^ 80 : ℝ) : ℂ) * I
  have hball : ∀ z ∈ closedBall c h, 7 / 16 ≤ z.re ∧ |z.im - (G : ℝ) / 2 ^ 80| ≤ 1 / 16 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have a := Complex.abs_re_le_norm (z - c)
    have b := Complex.abs_im_le_norm (z - c)
    have hre : (z - c).re = z.re - (j : ℝ) / 4096 := by
      simp only [c, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
    have him : (z - c).im = z.im - (G : ℝ) / 2 ^ 80 := by
      simp only [c, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
    rw [hre] at a; rw [him] at b
    rw [abs_le] at a
    refine ⟨?_, by linarith⟩
    have : (1 / 2 : ℝ) ≤ (j : ℝ) / 4096 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hz : (σ : ℂ) + ((G : ℝ) / 2 ^ 80 : ℝ) * I ∈ closedBall c h := by
    rw [mem_closedBall, dist_eq_norm]
    have : (σ : ℂ) + ((G : ℝ) / 2 ^ 80 : ℝ) * I - c = ((σ - (j : ℝ) / 4096 : ℝ) : ℂ) := by
      simp only [c]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  refine re_pos_of_point hv hd hh0 (fun z hz => norm_zeta''_le_leg3 hm hγ (hball z hz).1 (hball z hz).2) ?_ hpos _ hz
  intro z hz h1
  have := (hball z hz).2
  rw [h1] at this; simp at this
  rw [abs_le] at this; linarith


end ZetaCert
