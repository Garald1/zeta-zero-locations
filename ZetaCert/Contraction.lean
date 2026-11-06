/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# A unique zero in a disk, by the contraction mapping principle

`unique_zero_of_deriv_near`: if `f` is complex differentiable on (a neighbourhood of each point
of) the closed disk `D = closedBall c r`, `‖f' z - a‖ ≤ κ ‖a‖` on `D` with `κ < 1`, and
`‖f c‖ ≤ (1 - κ) ‖a‖ r`, then `f` has exactly one zero in `D`, and `f'` does not vanish there.
The map `g z = z - f z / a` sends `D` into itself and is `κ`-Lipschitz on `D`.
-/

open Metric Complex

namespace ZetaCert

theorem unique_zero_of_deriv_near {f : ℂ → ℂ} {c a : ℂ} {r κ : ℝ} (hr : 0 ≤ r) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (ha : a ≠ 0)
    (hdiff : ∀ z ∈ closedBall c r, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ closedBall c r, ‖deriv f z - a‖ ≤ κ * ‖a‖)
    (h0 : ‖f c‖ ≤ (1 - κ) * ‖a‖ * r) :
    ∃! z, z ∈ closedBall c r ∧ f z = 0 := by
  set D := closedBall c r
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set g : ℂ → ℂ := fun z => z - f z / a with hg
  have hgdiff : ∀ z ∈ D, DifferentiableAt ℂ g z := fun z hz =>
    differentiableAt_id.sub ((hdiff z hz).div_const a)
  have hgderiv : ∀ z ∈ D, ‖deriv g z‖ ≤ κ := by
    intro z hz
    have : deriv g z = 1 - deriv f z / a := by
      have h1 : HasDerivAt g (1 - deriv f z / a) z :=
        (hasDerivAt_id z).sub ((hdiff z hz).hasDerivAt.div_const a)
      exact h1.deriv
    rw [this]
    have e : 1 - deriv f z / a = (a - deriv f z) / a := by field_simp
    rw [e, norm_div, norm_sub_rev, div_le_iff₀ ha0]
    exact hd z hz
  have hconv : Convex ℝ D := convex_closedBall c r
  have hlip : ∀ x ∈ D, ∀ y ∈ D, ‖g y - g x‖ ≤ κ * ‖y - x‖ := fun x hx y hy =>
    hconv.norm_image_sub_le_of_norm_deriv_le hgdiff hgderiv hx hy
  have hcD : c ∈ D := mem_closedBall_self hr
  have hmaps : ∀ z ∈ D, g z ∈ D := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    have h1 := hlip c hcD z (by rw [mem_closedBall, dist_eq_norm]; exact hz)
    have h2 : ‖g c - c‖ ≤ (1 - κ) * r := by
      simp only [hg, sub_sub_cancel_left, norm_neg, norm_div]
      rw [div_le_iff₀ ha0]; nlinarith
    calc ‖g z - c‖ ≤ ‖g z - g c‖ + ‖g c - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ κ * ‖z - c‖ + (1 - κ) * r := add_le_add h1 h2
      _ ≤ κ * r + (1 - κ) * r := by gcongr
      _ = r := by ring
  have hfix : ∀ z, g z = z ↔ f z = 0 := by
    intro z; simp only [hg, sub_eq_self, div_eq_zero_iff, ha, or_false]
  -- uniqueness
  have huniq : ∀ x ∈ D, ∀ y ∈ D, f x = 0 → f y = 0 → x = y := by
    intro x hx y hy hfx hfy
    have h := hlip x hx y hy
    rw [(hfix x).mpr hfx, (hfix y).mpr hfy] at h
    have : ‖y - x‖ = 0 := by
      have h0 : 0 ≤ ‖y - x‖ := norm_nonneg _
      nlinarith
    exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm
  -- existence: Banach's fixed point theorem on the complete space `D`
  haveI : CompleteSpace D := isClosed_closedBall.completeSpace_coe
  haveI : Nonempty D := ⟨⟨c, hcD⟩⟩
  set G : D → D := fun z => ⟨g z, hmaps z z.2⟩
  have hκnn : (⟨κ, hκ0⟩ : NNReal) < 1 := by exact_mod_cast hκ1
  have hG : ContractingWith ⟨κ, hκ0⟩ G := by
    refine ⟨hκnn, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [G, Subtype.dist_eq, dist_eq_norm]
    exact hlip y y.2 x x.2
  obtain ⟨z, hz⟩ : ∃ z : D, G z = z := ⟨_, hG.fixedPoint_isFixedPt⟩
  have hgz : g z = z := congrArg Subtype.val hz
  refine ⟨z, ⟨z.2, (hfix z).mp hgz⟩, ?_⟩
  rintro y ⟨hy, hfy⟩
  exact huniq y hy z z.2 hfy ((hfix z).mp hgz)

/-- In the same situation the derivative does not vanish on `D`. -/
theorem deriv_ne_zero_of_near {f : ℂ → ℂ} {a z : ℂ} {κ : ℝ} (hκ1 : κ < 1) (ha : a ≠ 0)
    (hd : ‖deriv f z - a‖ ≤ κ * ‖a‖) : deriv f z ≠ 0 := by
  intro h
  rw [h, zero_sub, norm_neg] at hd
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  nlinarith

end ZetaCert
