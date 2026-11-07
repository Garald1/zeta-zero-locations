/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.CertSound

@[expose] public section

/-! Milestone M2: the zero of ζ near `999.7915715574` (number 649), end to end. -/

open ZetaCert Complex

theorem z649 : ∃ t : ℝ, |t - (999791571557412940463163147 : ℕ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧
    riemannZeta (1 / 2 + t * I) = 0 :=
  zc_spec (G := 1208673845088843613075151169) (N := 263) (K := 17) (k := 57) (fuel := 1000) (Dp := 9)
    (by decide +kernel)

#print axioms z649
