/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaZeros.EM2

/-!
# Explicit bounds for the Euler–Maclaurin remainder at `1/2 + iγ` and on the circle of radius `1/4`

* `emErr_center_le`: `emErr N k (1/2) γ ≤ Π_{i<2k+2}(1/2 + i + γ) / (2k+2)! · |B_{2k+2}| ·
  v / N^{2k+1} / (2k + 3/2)` whenever `N^{-1/2} ≤ v`;
* `emErr_circle_le`: for `w` on the circle of radius `1/4` about `1/2 + iγ`,
  `‖ζ w - emMain N k w‖ ≤ Π_{i<2k+2}(i + 1 + γ) / (2k+2)! · |B_{2k+2}| / N^{2k+1} / (2k+1)`.
-/

open Complex Metric

namespace ZetaCert

open ZetaZeros.EM

theorem exp_mul_log_nat {N : ℕ} (hN : 0 < N) (x : ℝ) : Real.exp (x * Real.log N) = (N : ℝ) ^ x := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hN), mul_comm]

theorem emErr_center_le {N : ℕ} (hN : 0 < N) (k : ℕ) {γ v : ℝ} (hγ : 0 ≤ γ)
    (hv : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ v) :
    emErr N k (1 / 2) γ ≤ (∏ i ∈ Finset.range (2 * k + 2), (1 / 2 + i + γ)) /
      ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)| * (v / (N : ℝ) ^ (2 * k + 1)) /
      (2 * k + 3 / 2) := by
  unfold emErr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : ∏ i ∈ Finset.range (2 * k + 2), (|1 / 2 + (i : ℝ)| + |γ|) =
      ∏ i ∈ Finset.range (2 * k + 2), (1 / 2 + (i : ℝ) + γ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg hγ]
  rw [hp, exp_mul_log_nat hN]
  have he : (N : ℝ) ^ (-(1 / 2 + ((2 * k + 2 : ℕ) : ℝ)) + 1) =
      (N : ℝ) ^ (-(1 / 2 : ℝ)) / (N : ℝ) ^ (2 * k + 1) := by
    rw [show -(1 / 2 + ((2 * k + 2 : ℕ) : ℝ)) + 1 = -(1 / 2 : ℝ) + -((2 * k + 1 : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_add hNR, Real.rpow_neg hNR.le ((2 * k + 1 : ℕ) : ℝ),
      Real.rpow_natCast, ← div_eq_mul_inv]
  rw [he]
  have hden : (1 / 2 + ((2 * k + 2 : ℕ) : ℝ) - 1) = 2 * k + 3 / 2 := by push_cast; ring
  rw [hden]
  have h0 : 0 ≤ (∏ i ∈ Finset.range (2 * k + 2), (1 / 2 + (i : ℝ) + γ)) /
      ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)| := by positivity
  have h1 : (0 : ℝ) < 2 * k + 3 / 2 := by positivity
  have e : ∀ x : ℝ, (∏ i ∈ Finset.range (2 * k + 2), (1 / 2 + (i : ℝ) + γ)) /
      ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)| * (x / (N : ℝ) ^ (2 * k + 1) /
      (2 * k + 3 / 2)) = (∏ i ∈ Finset.range (2 * k + 2), (1 / 2 + (i : ℝ) + γ)) /
      ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)| * (x / (N : ℝ) ^ (2 * k + 1)) /
      (2 * k + 3 / 2) := fun x => by ring
  rw [e]
  gcongr

theorem emErr_circle_le {N : ℕ} (hN : 0 < N) (k : ℕ) {γ : ℝ} (hγ : 2 ≤ γ) {w : ℂ}
    (hw : w ∈ sphere ((1 / 2 : ℂ) + γ * I) (1 / 4)) :
    ‖riemannZeta w - emMain N k w‖ ≤ (∏ i ∈ Finset.range (2 * k + 2), ((i : ℝ) + 1 + γ)) /
      ((2 * k + 2).factorial : ℝ) * |(bernoulli (2 * k + 2) : ℝ)| / (N : ℝ) ^ (2 * k + 1) /
      (2 * k + 1) := by
  rw [mem_sphere, dist_eq_norm] at hw
  have hre := Complex.abs_re_le_norm (w - ((1 / 2 : ℂ) + γ * I))
  have him := Complex.abs_im_le_norm (w - ((1 / 2 : ℂ) + γ * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hw] at hre him
  norm_num at hre him
  rw [abs_le] at hre him
  have hwre : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := by
    intro h; rw [h] at him; simp at him; linarith
  refine (riemannZeta_sub_emMain_le hN hwre hw1 k).trans ?_
  unfold emErr
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : ∏ i ∈ Finset.range (2 * k + 2), (|w.re + (i : ℝ)| + |w.im|) ≤
      ∏ i ∈ Finset.range (2 * k + 2), ((i : ℝ) + 1 + γ) := by
    apply Finset.prod_le_prod₀ (fun i _ => by positivity)
    intro i _
    rw [abs_of_pos (by positivity), abs_of_pos (by linarith)]
    linarith
  have he : Real.exp ((-(w.re + ((2 * k + 2 : ℕ) : ℝ)) + 1) * Real.log N) ≤ 1 / (N : ℝ) ^ (2 * k + 1) := by
    rw [exp_mul_log_nat hN, one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hNR
    push_cast; linarith
  have hden : (2 * k + 1 : ℝ) ≤ w.re + ((2 * k + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hB : 0 ≤ |(bernoulli (2 * k + 2) : ℝ)| := abs_nonneg _
  have hf : (0 : ℝ) < ((2 * k + 2).factorial : ℝ) := by positivity
  calc (∏ i ∈ Finset.range (2 * k + 2), (|w.re + (i : ℝ)| + |w.im|)) / ((2 * k + 2).factorial : ℝ)
        * |(bernoulli (2 * k + 2) : ℝ)| *
        (Real.exp ((-(w.re + ((2 * k + 2 : ℕ) : ℝ)) + 1) * Real.log N) / (w.re + ((2 * k + 2 : ℕ) : ℝ) - 1))
      ≤ (∏ i ∈ Finset.range (2 * k + 2), ((i : ℝ) + 1 + γ)) / ((2 * k + 2).factorial : ℝ)
        * |(bernoulli (2 * k + 2) : ℝ)| * ((1 / (N : ℝ) ^ (2 * k + 1)) / (2 * k + 1)) := by
        gcongr
        have : 0 < w.re + ((2 * k + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
        positivity
    _ = _ := by ring

end ZetaCert
