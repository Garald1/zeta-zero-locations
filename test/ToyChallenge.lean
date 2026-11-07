/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib

@[expose] public section

/-! Toy challenge for the NanoDa/comparator test of milestone M2: two single-zero statements. -/

open Complex

namespace Toy

theorem zero1 : ∃ t : ℝ, |t - ((14134725141734693790457252 : ℕ) : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧
    riemannZeta (1 / 2 + t * I) = 0 := by
  sorry

theorem zero10142 : ∃ t : ℝ, |t - ((9998850397089674049057631757 : ℕ) : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧
    riemannZeta (1 / 2 + t * I) = 0 := by
  sorry

end Toy
