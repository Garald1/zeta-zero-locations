/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Contraction
public import ZetaCert.OnLine
public import ZetaZeros.EMDeriv
public import ZetaZeros.Deriv

@[expose] public section

/-!
# One zero on the critical line from bounds on the Euler–Maclaurin main term

`zero_of_EM_bounds`: let `c = 1/2 + iγ` with `γ ≥ 2`, and let `Fv`, `Fd` approximate
`emMain N k c` and its derivative `emMain1 N k c` to within `eF`, `eD`. If the remainder of
Euler–Maclaurin is at most `E0` at `c` and at most `E1` on the circle of radius `1/4` about `c`,
and
* (B1) `r M2 + 4 E1 + eD ≤ κ ‖Fd‖`, with `M2 = 112 + 160 (γ + 1)` (a bound for `|ζ''|` near `c`),
* (B2) `‖Fv‖ + eF + E0 ≤ (1 - κ) ‖Fd‖ r`,
with `0 ≤ κ < 1` and `0 < r ≤ 1/20`, then `ζ (1/2 + it) = 0` for some `t` with `|t - γ| ≤ r`.
-/

open Complex Metric

namespace ZetaCert

open ZetaZeros.EM ZetaZeros.EMDeriv ZetaZeros.Deriv

/-- `|ζ''| ≤ 112 + 160 (γ + 1)` on the disk of radius `1/20` about `1/2 + iγ`, `γ ≥ 2`. -/
theorem norm_zeta''_le {γ r : ℝ} (hγ : 2 ≤ γ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) {z : ℂ}
    (hz : z ∈ closedBall ((1 / 2 : ℂ) + γ * I) r) :
    ‖deriv (deriv riemannZeta) z‖ ≤ 112 + 160 * (γ + 1) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := Complex.abs_re_le_norm (z - ((1 / 2 : ℂ) + γ * I))
  have him := Complex.abs_im_le_norm (z - ((1 / 2 : ℂ) + γ * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
  norm_num at hre him
  rw [abs_le] at hre him
  have h := norm_deriv_deriv_zeta_le 1 le_rfl (σ₀ := 1 / 5) (T₀ := γ + 1) (δ := 1) (R := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (z := z) (by linarith) ?_ ?_
  · simp at h
    have e : (2 * (1 + 1 + 2⁻¹ + (1 + (γ + 1) * 5)) / (4 ^ 2)⁻¹ : ℝ) = 112 + 160 * (γ + 1) := by
      norm_num; ring
    linarith
  · have : |z.im| ≤ γ + 3 / 4 := by rw [abs_le]; constructor <;> linarith
    linarith
  · have : (1 : ℝ) + 1 / 4 ≤ |(z - 1).im| := by
      simp only [Complex.sub_im, Complex.one_im, sub_zero]
      rw [abs_of_pos (by linarith)]; linarith
    exact this.trans (Complex.abs_im_le_norm _)

theorem zero_of_EM_bounds {γ r κ E0 E1 eF eD : ℝ} {N k : ℕ} {Fv Fd : ℂ} (hN : 0 < N)
    (hγ : 2 ≤ γ) (hr0 : 0 < r) (hr : r ≤ 1 / 20) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hF : ‖emMain N k ((1 / 2 : ℂ) + γ * I) - Fv‖ ≤ eF)
    (hD : ‖emMain1 N k ((1 / 2 : ℂ) + γ * I) - Fd‖ ≤ eD)
    (hE0 : ‖riemannZeta ((1 / 2 : ℂ) + γ * I) - emMain N k ((1 / 2 : ℂ) + γ * I)‖ ≤ E0)
    (hE1 : ∀ w ∈ sphere ((1 / 2 : ℂ) + γ * I) (1 / 4), ‖riemannZeta w - emMain N k w‖ ≤ E1)
    (B1 : r * (112 + 160 * (γ + 1)) + 4 * E1 + eD ≤ κ * ‖Fd‖)
    (B2 : ‖Fv‖ + eF + E0 ≤ (1 - κ) * ‖Fd‖ * r) :
    ∃ t : ℝ, |t - γ| ≤ r ∧ riemannZeta (1 / 2 + t * I) = 0 := by
  set c : ℂ := (1 / 2 : ℂ) + γ * I with hc
  have hcre : c.re = 1 / 2 := by simp [c]
  have hcim : c.im = γ := by simp [c]
  have hc1 : (1 / 4 : ℝ) < ‖c - 1‖ := by
    have h1 : (c - 1).im = γ := by simp [c]
    have h2 := Complex.abs_im_le_norm (c - 1)
    rw [h1, abs_of_pos (by linarith)] at h2
    linarith
  -- `ζ'(c)` versus `Fd`
  have hEM1 : ‖deriv riemannZeta c - emMain1 N k c‖ ≤ E1 / (1 / 4) := by
    have hc0 : c ≠ 0 := by intro h; have := congrArg Complex.re h; simp [c] at this
    have hdiff : DifferentiableOn ℂ (emMain N k) (closedBall c (1 / 4)) := by
      intro w hw
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_emMain hN
      · intro h; subst h
        rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at hw
        have := Complex.abs_im_le_norm c; rw [hcim, abs_of_pos (by linarith)] at this; linarith
      · intro h; subst h
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw; linarith
    have := norm_deriv_zeta_sub_le (by norm_num) hc1 hdiff hE1
    rwa [deriv_emMain hN k hc0 (by intro h; rw [h] at hc1; simp at hc1; linarith)] at this
  have hFd0 : 0 < ‖Fd‖ := by
    have : 0 < r * (112 + 160 * (γ + 1)) := by positivity
    have h4 : 0 ≤ 4 * E1 := by
      have := hE1 (c + 1 / 4) (by simp [mem_sphere, dist_eq_norm])
      linarith [norm_nonneg (riemannZeta (c + 1 / 4) - emMain N k (c + 1 / 4))]
    have heD : 0 ≤ eD := (norm_nonneg _).trans hD
    by_contra h; push Not at h
    have : κ * ‖Fd‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ0 h
    linarith
  have hFd : Fd ≠ 0 := norm_pos_iff.mp hFd0
  -- the hypotheses of the contraction lemma
  have hball1 : ∀ z ∈ closedBall c r, z ≠ 1 := by
    intro z hz h; subst h
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hz; linarith
  have hdiff : ∀ z ∈ closedBall c r, DifferentiableAt ℂ riemannZeta z := fun z hz =>
    differentiableAt_riemannZeta (hball1 z hz)
  have hderiv : ∀ z ∈ closedBall c r, ‖deriv riemannZeta z - Fd‖ ≤ κ * ‖Fd‖ := by
    intro z hz
    have hmv : ‖deriv riemannZeta z - deriv riemannZeta c‖ ≤ (112 + 160 * (γ + 1)) * ‖z - c‖ :=
      (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
        (fun w hw => ZetaZeros.Deriv.differentiableAt_deriv_zeta (hball1 w hw))
        (fun w hw => norm_zeta''_le hγ hr0.le hr hw) (mem_closedBall_self hr0.le) hz
    have hzc : ‖z - c‖ ≤ r := by rw [← dist_eq_norm]; exact hz
    have h1 : (112 + 160 * (γ + 1)) * ‖z - c‖ ≤ r * (112 + 160 * (γ + 1)) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hzc (by positivity)
    calc ‖deriv riemannZeta z - Fd‖
        ≤ ‖deriv riemannZeta z - deriv riemannZeta c‖ + ‖deriv riemannZeta c - emMain1 N k c‖
          + ‖emMain1 N k c - Fd‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (deriv riemannZeta z) (deriv riemannZeta c) Fd
          have := norm_sub_le_norm_sub_add_norm_sub (deriv riemannZeta c) (emMain1 N k c) Fd
          linarith
      _ ≤ r * (112 + 160 * (γ + 1)) + 4 * E1 + eD := by
          have : E1 / (1 / 4) = 4 * E1 := by ring
          linarith
      _ ≤ κ * ‖Fd‖ := B1
  have hval : ‖riemannZeta c‖ ≤ (1 - κ) * ‖Fd‖ * r := by
    have := norm_sub_le_norm_sub_add_norm_sub (riemannZeta c) (emMain N k c) Fv
    have h2 : ‖riemannZeta c‖ ≤ ‖riemannZeta c - Fv‖ + ‖Fv‖ := by
      have := norm_add_le (riemannZeta c - Fv) Fv; simpa using this
    linarith
  have hu := unique_zero_of_deriv_near hr0.le hκ0 hκ1 hFd hdiff hderiv hval
  obtain ⟨ρ, hρD, hρ0, hρre⟩ := re_eq_half_of_unique hcre (by rw [hcim]; linarith) hu
  refine ⟨ρ.im, ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm] at hρD
    have := Complex.abs_im_le_norm (ρ - c)
    rw [Complex.sub_im, hcim] at this
    linarith
  · have : (1 / 2 : ℂ) + (ρ.im : ℂ) * I = ρ := by
      apply Complex.ext <;> simp [hρre]
    rw [this]; exact hρ0

end ZetaCert
