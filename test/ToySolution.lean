/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.CertSound

/-! Toy solution for the NanoDa/comparator test of milestone M2. -/

open Complex ZetaCert

namespace Toy

theorem zero1 : ∃ t : ℝ, |t - ((14134725141734693790457252 : ℕ) : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧
    riemannZeta (1 / 2 + t * I) = 0 :=
  zc_spec (G := 17087834176999120219905779) (N := 17) (K := 10) (k := 22) (fuel := 1000) (Dp := 5)
    (by decide +kernel)

theorem zero10142 : ∃ t : ℝ, |t - ((9998850397089674049057631757 : ℕ) : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧
    riemannZeta (1 / 2 + t * I) = 0 :=
  zc_spec (G := 12087868411505694583773790192) (N := 2473) (K := 21) (k := 60) (fuel := 1000) (Dp := 12)
    (by decide +kernel)

end Toy
