/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaZeros.EMDeriv

/-!
# The Euler–Maclaurin main term as Dirichlet sum plus `N^{-s}` times a rational function

`emMain N k s = Σ_{n ≤ N} n^{-s} + N^{-s} · Rm N k s` and
`emMain1 N k s = Σ_{n ≤ N} A1 n s + N^{-s} · (R1m N k s - log N · Rm N k s)`, where
`Rm N k s = N/(s-1) - 1/2 + Σ_{i ≤ k} β_{2i} poch(s, 2i+1) / N^{2i+1}` and
`R1m N k s = -N/(s-1)^2 + Σ_{i ≤ k} β_{2i} dpoch(s, 2i+1) / N^{2i+1}`.
-/

open Complex

namespace ZetaCert

open ZetaZeros.EM ZetaZeros.EMDeriv

/-- The rational part of `emMain`. -/
noncomputable def Rm (N k : ℕ) (s : ℂ) : ℂ :=
  (N : ℂ) / (s - 1) - 1 / 2 +
    ∑ i ∈ Finset.range (k + 1), beta (2 * i) * poch s (2 * i + 1) / (N : ℂ) ^ (2 * i + 1)

/-- The rational part of the derivative. -/
noncomputable def R1m (N k : ℕ) (s : ℂ) : ℂ :=
  -(N : ℂ) / (s - 1) ^ 2 +
    ∑ i ∈ Finset.range (k + 1), beta (2 * i) * dpoch s (2 * i + 1) / (N : ℂ) ^ (2 * i + 1)

theorem cpow_neg_add_nat {N : ℕ} (hN : 0 < N) (s : ℂ) (j : ℕ) :
    (N : ℂ) ^ (-(s + (j : ℕ))) = (N : ℂ) ^ (-s) / (N : ℂ) ^ j := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [neg_add, Complex.cpow_add _ _ hN0, Complex.cpow_neg (N : ℂ) (j : ℂ), Complex.cpow_natCast]
  ring

theorem cpow_one_sub {N : ℕ} (hN : 0 < N) (s : ℂ) :
    (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0, Complex.cpow_one]

theorem emTerm_eq {N : ℕ} (hN : 0 < N) (s : ℂ) (j : ℕ) :
    emTerm N s j = (N : ℂ) ^ (-s) * (beta j * poch s (j + 1) / (N : ℂ) ^ (j + 1)) := by
  unfold emTerm beta
  rw [cpow_neg_add_nat hN]
  ring

theorem emTerm1_eq {N : ℕ} (hN : 0 < N) (s : ℂ) (j : ℕ) :
    emTerm1 N s j = (N : ℂ) ^ (-s) * (beta j * dpoch s (j + 1) / (N : ℂ) ^ (j + 1)) -
      Complex.log N * ((N : ℂ) ^ (-s) * (beta j * poch s (j + 1) / (N : ℂ) ^ (j + 1))) := by
  unfold emTerm1
  rw [cpow_neg_add_nat hN]
  ring

theorem emMain_eq {N : ℕ} (hN : 0 < N) (k : ℕ) (s : ℂ) :
    emMain N k s = (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) + (N : ℂ) ^ (-s) * Rm N k s := by
  unfold emMain Rm
  rw [cpow_one_sub hN]
  simp only [emTerm_eq hN, ← Finset.mul_sum]
  ring

theorem emMain1_eq {N : ℕ} (hN : 0 < N) (k : ℕ) (s : ℂ) :
    emMain1 N k s = (∑ n ∈ Finset.range (N + 1), A1 n s) +
      (N : ℂ) ^ (-s) * (R1m N k s - Complex.log N * Rm N k s) := by
  unfold emMain1 R1m Rm pole1
  rw [cpow_one_sub hN]
  simp only [emTerm1_eq hN, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end ZetaCert
