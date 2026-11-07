/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib

@[expose] public section

/-!
# Zeros of `ζ` in a disk centred on the critical line

`riemannZeta_one_sub_conj_eq_zero`: `ζ ρ = 0` with `Im ρ ≠ 0` implies `ζ (1 - conj ρ) = 0`.
`re_eq_half_of_unique`: if `ζ` has exactly one zero in `closedBall c r`, where `Re c = 1/2` and
`r < Im c`, that zero lies on the critical line (it equals its reflection `1 - conj ρ`, which
lies in the same disk).
-/

open Complex Metric ComplexConjugate

namespace ZetaCert

theorem riemannZeta_one_sub_conj_eq_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (him : ρ.im ≠ 0) :
    riemannZeta (1 - conj ρ) = 0 := by
  have h1 : ∀ n : ℕ, conj ρ ≠ -n := by
    intro n h
    have := congrArg Complex.im h
    simp at this
    exact him this
  have h2 : conj ρ ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact him this
  rw [riemannZeta_one_sub h1 h2, riemannZeta_conj, hρ, map_zero, mul_zero]

theorem re_eq_half_of_unique {c : ℂ} {r : ℝ} (hc : c.re = 1 / 2) (hr : r < c.im)
    (hu : ∃! z, z ∈ closedBall c r ∧ riemannZeta z = 0) :
    ∃ ρ, ρ ∈ closedBall c r ∧ riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 := by
  obtain ⟨ρ, ⟨hρD, hρ0⟩, huniq⟩ := hu
  refine ⟨ρ, hρD, hρ0, ?_⟩
  have him : ρ.im ≠ 0 := by
    intro h
    rw [mem_closedBall, dist_eq_norm] at hρD
    have := Complex.abs_im_le_norm (ρ - c)
    rw [Complex.sub_im, h, zero_sub, abs_neg] at this
    have hc0 : 0 < c.im := lt_of_le_of_lt (le_trans (abs_nonneg _) (this.trans hρD)) hr
    rw [abs_of_pos hc0] at this
    linarith
  have hrefl : 1 - conj ρ ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm] at hρD ⊢
    have e : 1 - conj ρ - c = -conj (ρ - c) := by
      apply Complex.ext <;> simp [hc] <;> ring
    rw [e, norm_neg, Complex.norm_conj]
    exact hρD
  have := huniq _ ⟨hrefl, riemannZeta_one_sub_conj_eq_zero hρ0 him⟩
  have h := congrArg Complex.re this
  simp at h
  linarith

end ZetaCert
