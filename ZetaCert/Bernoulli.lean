/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Bernoulli numbers by the recurrence, kernel-computable

`bernList M` lists `B_0, …, B_{M-1}` (Mathlib's `bernoulli`, `B_1 = -1/2`) computed by
`B_j = ([j = 0] - Σ_{k<j} C(j+1, k) B_k) / (j+1)`, with binomial coefficients computed
iteratively (`binom`), so that the kernel can evaluate it. `bernList_spec` identifies it with
Mathlib's `bernoulli`.
-/

namespace ZetaCert

/-- `C(n, k)` by the product formula, kernel-friendly. -/
def binom (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem binom_eq (n k : ℕ) : binom n k = n.choose k := by
  unfold binom; rw [Nat.choose_eq_descFactorial_div_factorial]

/-- One step of the recurrence, from the list of the previous values. -/
def bernStep (l : List ℚ) (j : ℕ) : ℚ :=
  ((if j = 0 then 1 else 0) -
    ((List.range j).map (fun k => (binom (j + 1) k : ℚ) * l.getD k 0)).sum) / (j + 1)

/-- `B_0, …, B_{M-1}`. -/
def bernList : ℕ → List ℚ
  | 0 => []
  | M + 1 => bernList M ++ [bernStep (bernList M) M]

theorem bernList_length (M : ℕ) : (bernList M).length = M := by
  induction M with
  | zero => rfl
  | succ M ih => simp [bernList, ih]

theorem bernList_getD_of_lt {M j : ℕ} (h : j < M) (M' : ℕ) (hM : M ≤ M') :
    (bernList M').getD j 0 = (bernList M).getD j 0 := by
  induction M' with
  | zero => omega
  | succ M' ih =>
    rcases Nat.lt_or_ge M (M' + 1) with h' | h'
    · rw [← ih (by omega)]
      simp only [bernList, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [bernList_length]; omega)]
    · have : M = M' + 1 := by omega
      subst this; rfl

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem bernList_spec : ∀ M j, j < M → (bernList M).getD j 0 = bernoulli j := by
  intro M
  induction M with
  | zero => intro j h; omega
  | succ M ih =>
    intro j hj
    rcases Nat.lt_or_ge j M with h | h
    · rw [bernList_getD_of_lt h (M + 1) (by omega)]; exact ih j h
    · have hjM : j = M := by omega
      subst hjM
      simp only [bernList, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [bernList_length]), bernList_length, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      have hs := sum_bernoulli (j + 1)
      rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at hs
      have hsum : ((List.range j).map (fun k => (binom (j + 1) k : ℚ) * (bernList j).getD k 0)).sum =
          ∑ k ∈ Finset.range j, ((j + 1).choose k : ℚ) * bernoulli k := by
        rw [list_sum_range]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [binom_eq, ih k (Finset.mem_range.mp hk)]
      unfold bernStep
      rw [hsum]
      have hj1 : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have e1 : (if j = 0 then (1 : ℚ) else 0) = if j + 1 = 1 then 1 else 0 := by
        simp
      rw [e1, ← hs]
      push_cast
      field_simp
      ring

end ZetaCert
