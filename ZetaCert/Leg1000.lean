/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Leg1000.L0
public import ZetaCert.Leg1000.L1
public import ZetaCert.Leg1000.L2
public import ZetaCert.Leg1000.L3
public import ZetaCert.Leg1000.L4
public import ZetaCert.Leg1000.L5

@[expose] public section

/-! `Re ζ(σ + iT₂) > 0` on `[1/2, 2]`, `T₂ = 512069/512`. -/

namespace ZetaCert.Leg1000

open ZetaCert Complex Set

theorem leg_all : ∀ σ ∈ Icc ((2048 : ℕ) / 4096 - (14 : ℝ) / 4096) ((8180 : ℕ) / 4096 + (14 : ℝ) / 4096),
    (fun σ : ℝ => 0 < (riemannZeta (σ + ((1209088741258288177466048512 : ℕ) / 2 ^ 80 : ℝ) * I)).re) σ :=
  cover2 (cover2 (cover2 (cover2 (cover2 (part_0) part_1 (by norm_num)) part_2 (by norm_num)) part_3 (by norm_num)) part_4 (by norm_num)) part_5 (by norm_num)

theorem leg : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + (((512069 : ℝ) / 512 : ℝ) : ℂ) * I)).re := by
  intro σ hσ
  have h := leg_all σ ⟨by norm_num at hσ ⊢; linarith [hσ.1], by norm_num at hσ ⊢; linarith [hσ.2]⟩
  have e : (((1209088741258288177466048512 : ℕ) : ℝ) / 2 ^ 80 : ℝ) = (512069 : ℝ) / 512 := by norm_num
  simp only at h; rw [e] at h; exact h

end ZetaCert.Leg1000
