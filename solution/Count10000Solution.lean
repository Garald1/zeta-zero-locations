/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Zeros0to1000Solution
public import Zeros1000to2000Solution
public import Zeros2000to3000Solution
public import Zeros3000to4000Solution
public import Zeros4000to5000Solution
public import Zeros5000to6000Solution
public import Zeros6000to7000Solution
public import Zeros7000to8000Solution
public import Zeros8000to9000Solution
public import Zeros9000to10000Solution

@[expose] public section

/-!
# Solution of `challenge/Count10000.lean`

The definitions are copied verbatim from the challenge file. The ten range solutions
(`solution/Zeros{a}to{b}Solution.lean`) give, on each range `(1000 j, 1000 (j+1)]`, that every zero
is simple and on the critical line, and the number of zeros; the ranges are disjoint.
-/

namespace Count10000

/-- The zeros of `riemannZeta` with `a < Im s ≤ b` (no condition on `Re s`). -/
def zerosBetween (a b : ℝ) : Set ℂ := {s | riemannZeta s = 0 ∧ a < s.im ∧ s.im ≤ b}

theorem split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    zerosBetween a c = zerosBetween a b ∪ zerosBetween b c := by
  ext s
  simp only [zerosBetween, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, h1, h2⟩
    by_cases h : s.im ≤ b
    · exact Or.inl ⟨hz, h1, h⟩
    · exact Or.inr ⟨hz, lt_of_not_ge h, h2⟩
  · rintro (⟨hz, h1, h2⟩ | ⟨hz, h1, h2⟩)
    · exact ⟨hz, h1, h2.trans hbc⟩
    · exact ⟨hz, lt_of_le_of_lt hab h1, h2⟩

theorem card_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {m n : ℕ}
    (h1 : (zerosBetween a b).ncard = m) (h2 : (zerosBetween b c).ncard = n) (hm : 0 < m) (hn : 0 < n) :
    (zerosBetween a c).ncard = m + n := by
  rw [split hab hbc, Set.ncard_union_eq, h1, h2]
  · rw [Set.disjoint_left]
    rintro s ⟨-, -, h⟩ ⟨-, h', -⟩
    linarith
  · exact Set.finite_of_ncard_pos (by omega)
  · exact Set.finite_of_ncard_pos (by omega)

/-- Every zero of `ζ` with `0 < Im s ≤ 10000` is simple and lies on the critical line. -/
theorem on_line_and_simple :
    ∀ s ∈ zerosBetween 0 10000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 := by
  rintro s ⟨hz, h0, h1⟩
  by_cases h1000 : s.im ≤ 1000
  · exact ⟨(Zeros0to1000.located s ⟨hz, by linarith, h1000⟩).1,
      (Zeros0to1000.located s ⟨hz, by linarith, h1000⟩).2.1⟩
  push Not at h1000
  by_cases h2000 : s.im ≤ 2000
  · exact ⟨(Zeros1000to2000.located s ⟨hz, by linarith, h2000⟩).1,
      (Zeros1000to2000.located s ⟨hz, by linarith, h2000⟩).2.1⟩
  push Not at h2000
  by_cases h3000 : s.im ≤ 3000
  · exact ⟨(Zeros2000to3000.located s ⟨hz, by linarith, h3000⟩).1,
      (Zeros2000to3000.located s ⟨hz, by linarith, h3000⟩).2.1⟩
  push Not at h3000
  by_cases h4000 : s.im ≤ 4000
  · exact ⟨(Zeros3000to4000.located s ⟨hz, by linarith, h4000⟩).1,
      (Zeros3000to4000.located s ⟨hz, by linarith, h4000⟩).2.1⟩
  push Not at h4000
  by_cases h5000 : s.im ≤ 5000
  · exact ⟨(Zeros4000to5000.located s ⟨hz, by linarith, h5000⟩).1,
      (Zeros4000to5000.located s ⟨hz, by linarith, h5000⟩).2.1⟩
  push Not at h5000
  by_cases h6000 : s.im ≤ 6000
  · exact ⟨(Zeros5000to6000.located s ⟨hz, by linarith, h6000⟩).1,
      (Zeros5000to6000.located s ⟨hz, by linarith, h6000⟩).2.1⟩
  push Not at h6000
  by_cases h7000 : s.im ≤ 7000
  · exact ⟨(Zeros6000to7000.located s ⟨hz, by linarith, h7000⟩).1,
      (Zeros6000to7000.located s ⟨hz, by linarith, h7000⟩).2.1⟩
  push Not at h7000
  by_cases h8000 : s.im ≤ 8000
  · exact ⟨(Zeros7000to8000.located s ⟨hz, by linarith, h8000⟩).1,
      (Zeros7000to8000.located s ⟨hz, by linarith, h8000⟩).2.1⟩
  push Not at h8000
  by_cases h9000 : s.im ≤ 9000
  · exact ⟨(Zeros8000to9000.located s ⟨hz, by linarith, h9000⟩).1,
      (Zeros8000to9000.located s ⟨hz, by linarith, h9000⟩).2.1⟩
  push Not at h9000
  exact ⟨(Zeros9000to10000.located s ⟨hz, h9000, h1⟩).1, (Zeros9000to10000.located s ⟨hz, h9000, h1⟩).2.1⟩

/-- There are exactly 10142 zeros of `ζ` with `0 < Im s ≤ 10000`. -/
theorem count : (zerosBetween 0 10000).ncard = 10142 := by
  have c0 : (zerosBetween 0 1000).ncard = 649 := Zeros0to1000.count
  have c1 : (zerosBetween 1000 2000).ncard = 868 := Zeros1000to2000.count
  have c2 : (zerosBetween 2000 3000).ncard = 952 := Zeros2000to3000.count
  have c3 : (zerosBetween 3000 4000).ncard = 1005 := Zeros3000to4000.count
  have c4 : (zerosBetween 4000 5000).ncard = 1046 := Zeros4000to5000.count
  have c5 : (zerosBetween 5000 6000).ncard = 1078 := Zeros5000to6000.count
  have c6 : (zerosBetween 6000 7000).ncard = 1105 := Zeros6000to7000.count
  have c7 : (zerosBetween 7000 8000).ncard = 1127 := Zeros7000to8000.count
  have c8 : (zerosBetween 8000 9000).ncard = 1148 := Zeros8000to9000.count
  have c9 : (zerosBetween 9000 10000).ncard = 1164 := Zeros9000to10000.count
  have s1 : (zerosBetween 0 2000).ncard = 1517 := card_split (by norm_num) (by norm_num) c0 c1 (by norm_num) (by norm_num)
  have s2 : (zerosBetween 0 3000).ncard = 2469 := card_split (by norm_num) (by norm_num) s1 c2 (by norm_num) (by norm_num)
  have s3 : (zerosBetween 0 4000).ncard = 3474 := card_split (by norm_num) (by norm_num) s2 c3 (by norm_num) (by norm_num)
  have s4 : (zerosBetween 0 5000).ncard = 4520 := card_split (by norm_num) (by norm_num) s3 c4 (by norm_num) (by norm_num)
  have s5 : (zerosBetween 0 6000).ncard = 5598 := card_split (by norm_num) (by norm_num) s4 c5 (by norm_num) (by norm_num)
  have s6 : (zerosBetween 0 7000).ncard = 6703 := card_split (by norm_num) (by norm_num) s5 c6 (by norm_num) (by norm_num)
  have s7 : (zerosBetween 0 8000).ncard = 7830 := card_split (by norm_num) (by norm_num) s6 c7 (by norm_num) (by norm_num)
  have s8 : (zerosBetween 0 9000).ncard = 8978 := card_split (by norm_num) (by norm_num) s7 c8 (by norm_num) (by norm_num)
  have s9 : (zerosBetween 0 10000).ncard = 10142 := card_split (by norm_num) (by norm_num) s8 c9 (by norm_num) (by norm_num)
  exact s9

end Count10000
