/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.OnLine
import RHHeight100.Main100

/-!
# Assembly up to height 1000

`ZetaCert.Assembly.main`: from a list `ms` of ordinates (scaled by `10^24`), each within `10⁻²⁰` of
a zero `1/2 + i t_m` of `ζ` (`P m`), pairwise more than `3·10⁻²⁰` apart, away from the heights 0,
100 and 1000, with exactly 29 of them below 100, and from `Ncount 100 T₂ ≤ #{m > 100}` for some
`T₂ > 1000`: every zero of `ζ` with `0 < Im s ≤ 1000` is one of the `1/2 + i t_m`, each of which
is simple. The three statements of `challenge/Zeros0to1000.lean` follow
(`located_of`, `unique_of`, `count_of`). Below height 100 we use zeta-lab's
`RHHeight100.rh_height_hundred` and `RHHeight100.zero_count_hundred`; above it, zeta-lab's
`RHHeight.mem_and_simple_of_Ncount_le`.
-/

open Complex

namespace ZetaCert.Assembly

/-- A zero of `ζ` on the critical line within `10⁻²⁰` of `m / 10^24`. -/
def P (m : ℕ) : Prop := ∃ t : ℝ, |t - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧ riemannZeta (1 / 2 + t * I) = 0

open Classical in
/-- The chosen ordinate. -/
noncomputable def tOf (m : ℕ) : ℝ := if h : P m then Classical.choose h else 0

/-- The chosen zero. -/
noncomputable def ρOf (m : ℕ) : ℂ := 1 / 2 + (tOf m : ℂ) * I

theorem tOf_spec {m : ℕ} (h : P m) :
    |tOf m - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧ riemannZeta (ρOf m) = 0 := by
  unfold ρOf tOf; rw [dif_pos h]; exact Classical.choose_spec h

@[simp] theorem ρOf_re (m : ℕ) : (ρOf m).re = 1 / 2 := by simp [ρOf]
@[simp] theorem ρOf_im (m : ℕ) : (ρOf m).im = tOf m := by simp [ρOf]

/-- Nontrivial zeros lie in the open strip. -/
theorem re_strip {s : ℂ} (hz : riemannZeta s = 0) (him : 0 < s.im) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h; push Not at h
    have h1 := riemannZeta_one_sub_conj_eq_zero hz him.ne'
    have : (1 : ℝ) ≤ (1 - (starRingEnd ℂ) s).re := by simp; linarith
    exact riemannZeta_ne_zero_of_one_le_re this h1
  · by_contra h; push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hz

/-- The separation hypothesis. -/
def Sep (ms : List ℕ) : Prop := ms.Pairwise (fun a b => a + 30000 < b)

theorem eq_of_close {ms : List ℕ} (hs : Sep ms) {m m' : ℕ} (hm : m ∈ ms) (hm' : m' ∈ ms) {x : ℝ}
    (h1 : |x - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) (h2 : |x - (m' : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) :
    m = m' := by
  by_contra hne
  have hs' : ms.Pairwise (fun a b => a + 30000 < b ∨ b + 30000 < a) := hs.imp (fun h => Or.inl h)
  haveI : Std.Symm (fun a b : ℕ => a + 30000 < b ∨ b + 30000 < a) := ⟨fun a b h => h.symm⟩
  have hR := hs'.forall hm hm' hne
  rw [abs_le] at h1 h2
  rcases hR with h | h
  · have : ((m : ℝ) + 30000) < m' := by exact_mod_cast h
    have : (m' : ℝ) / 10 ^ 24 - (m : ℝ) / 10 ^ 24 ≤ 2 / 10 ^ 20 := by linarith
    have : (m' : ℝ) - m ≤ 20000 := by
      have e : (m' : ℝ) / 10 ^ 24 - (m : ℝ) / 10 ^ 24 = ((m' : ℝ) - m) / 10 ^ 24 := by ring
      rw [e, div_le_iff₀ (by positivity)] at this; linarith
    linarith
  · have : ((m' : ℝ) + 30000) < m := by exact_mod_cast h
    have : (m : ℝ) / 10 ^ 24 - (m' : ℝ) / 10 ^ 24 ≤ 2 / 10 ^ 20 := by linarith
    have : (m : ℝ) - m' ≤ 20000 := by
      have e : (m : ℝ) / 10 ^ 24 - (m' : ℝ) / 10 ^ 24 = ((m : ℝ) - m') / 10 ^ 24 := by ring
      rw [e, div_le_iff₀ (by positivity)] at this; linarith
    linarith

/-- Bounds on `t_m` from bounds on `m`. -/
theorem tOf_bounds {m : ℕ} (h : P m) {a : ℕ} :
    (a + 10 ^ 5 < m → (a : ℝ) / 10 ^ 24 < tOf m) ∧ (m + 10 ^ 5 < a → tOf m < (a : ℝ) / 10 ^ 24) := by
  have h1 := (abs_le.mp (tOf_spec h).1)
  constructor
  · intro ha
    have : ((a : ℝ) + 10 ^ 5) < m := by exact_mod_cast ha
    have : (a : ℝ) / 10 ^ 24 + 10 ^ 5 / 10 ^ 24 < (m : ℝ) / 10 ^ 24 := by
      rw [← add_div]; exact div_lt_div_of_pos_right this (by positivity)
    have : (1 : ℝ) / 10 ^ 20 < 10 ^ 5 / 10 ^ 24 := by norm_num
    linarith
  · intro ha
    have : ((m : ℝ) + 10 ^ 5) < a := by exact_mod_cast ha
    have : (m : ℝ) / 10 ^ 24 + 10 ^ 5 / 10 ^ 24 < (a : ℝ) / 10 ^ 24 := by
      rw [← add_div]; exact div_lt_div_of_pos_right this (by positivity)
    have : (1 : ℝ) / 10 ^ 20 < 10 ^ 5 / 10 ^ 24 := by norm_num
    linarith

theorem ρOf_inj {ms : List ℕ} (hs : Sep ms) (hP : ∀ m ∈ ms, P m) {m m' : ℕ} (hm : m ∈ ms)
    (hm' : m' ∈ ms) (h : ρOf m = ρOf m') : m = m' := by
  have him : tOf m = tOf m' := by have := congrArg Complex.im h; simpa using this
  exact eq_of_close hs hm hm' (tOf_spec (hP m hm)).1 (him ▸ (tOf_spec (hP m' hm')).1)

/-- Hypotheses on the list of ordinates up to height 1000. -/
structure Hyp (ms : List ℕ) (T₂ : ℝ) : Prop where
  hP : ∀ m ∈ ms, P m
  hsep : Sep ms
  hrange : ∀ m ∈ ms, 10 ^ 5 < m ∧ m + 10 ^ 5 < 1000 * 10 ^ 24 ∧
    (m + 10 ^ 5 < 100 * 10 ^ 24 ∨ 100 * 10 ^ 24 + 10 ^ 5 < m)
  hlow : (ms.filter (fun m => decide (m < 100 * 10 ^ 24))).length = 29
  hT₂ : 1000 < T₂
  hN : Zeta23.Ncount 100 T₂ ≤ (ms.filter (fun m => decide (100 * 10 ^ 24 < m))).length

theorem main {ms : List ℕ} {T₂ : ℝ} (H : Hyp ms T₂) :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.im → s.im ≤ 1000 → ∃ m ∈ ms, s = ρOf m) ∧
    (∀ m ∈ ms, analyticOrderAt riemannZeta (ρOf m) = 1) := by
  classical
  obtain ⟨hP, hsep, hrange, hlow, hT₂, hN⟩ := H
  have hnodup : ms.Nodup := hsep.imp (fun {a b} h => by omega)
  have ht : ∀ m ∈ ms, 0 < tOf m ∧ tOf m < 1000 ∧ (tOf m < 100 ∨ 100 < tOf m) ∧
      (m < 100 * 10 ^ 24 → tOf m < 100) ∧ (100 * 10 ^ 24 < m → 100 < tOf m) := by
    intro m hm
    obtain ⟨r1, r2, r3⟩ := hrange m hm
    have b0 := (tOf_bounds (hP m hm) (a := 0)).1 (by omega)
    have b1 := (tOf_bounds (hP m hm) (a := 1000 * 10 ^ 24)).2 r2
    have b100 := tOf_bounds (hP m hm) (a := 100 * 10 ^ 24)
    push_cast at b0 b1 b100
    norm_num at b0 b1 b100
    refine ⟨by simpa using b0, b1, ?_, ?_, ?_⟩
    · rcases r3 with h | h
      · exact Or.inl (b100.2 h)
      · exact Or.inr (b100.1 h)
    · intro h; rcases r3 with h' | h'
      · exact b100.2 h'
      · omega
    · intro h; rcases r3 with h' | h'
      · omega
      · exact b100.1 h'
  -- the 29 zeros below 100
  set low := (ms.filter (fun m => decide (m < 100 * 10 ^ 24)))
  set high := (ms.filter (fun m => decide (100 * 10 ^ 24 < m)))
  have hlowm : ∀ m ∈ low, m ∈ ms ∧ m < 100 * 10 ^ 24 := fun m hm => by
    simpa [low] using hm
  have hhighm : ∀ m ∈ high, m ∈ ms ∧ 100 * 10 ^ 24 < m := fun m hm => by
    simpa [high] using hm
  set Lset := low.toFinset.image ρOf
  set Hset := high.toFinset.image ρOf
  have hinjL : Set.InjOn ρOf (low.toFinset : Set ℕ) := fun a ha b hb h =>
    ρOf_inj hsep hP (hlowm a (List.mem_toFinset.mp ha)).1 (hlowm b (List.mem_toFinset.mp hb)).1 h
  have hinjH : Set.InjOn ρOf (high.toFinset : Set ℕ) := fun a ha b hb h =>
    ρOf_inj hsep hP (hhighm a (List.mem_toFinset.mp ha)).1 (hhighm b (List.mem_toFinset.mp hb)).1 h
  have hcardL : Lset.card = 29 := by
    rw [Finset.card_image_of_injOn hinjL, List.toFinset_card_of_nodup (hnodup.filter _), hlow]
  have hcardH : Hset.card = high.length := by
    rw [Finset.card_image_of_injOn hinjH, List.toFinset_card_of_nodup (hnodup.filter _)]
  have hLsub : (Lset : Set ℂ) ⊆ RHHeight.stripZerosUpTo 100 := by
    intro ρ hρ
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨hmms, hm100⟩ := hlowm m (List.mem_toFinset.mp hm)
    obtain ⟨t0, -, -, tl, -⟩ := ht m hmms
    exact ⟨(tOf_spec (hP m hmms)).2, by simp, by norm_num, by simpa using t0, by simpa using (tl hm100).le⟩
  have hLeq : (Lset : Set ℂ) = RHHeight.stripZerosUpTo 100 := by
    have hc := RHHeight100.zero_count_hundred
    unfold RHHeight.ZeroCountUpTo at hc
    have hfin : (RHHeight.stripZerosUpTo 100).Finite := Set.finite_of_ncard_pos (by omega)
    refine Set.eq_of_subset_of_ncard_le hLsub ?_ hfin
    rw [hc, Set.ncard_coe_finset, hcardL]
  -- the zeros between 100 and T₂
  have hHsub : ∀ ρ ∈ Hset, ρ ∈ Zeta23.zerosIn 100 T₂ := by
    intro ρ hρ
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨hmms, hm100⟩ := hhighm m (List.mem_toFinset.mp hm)
    obtain ⟨-, t1, -, -, th⟩ := ht m hmms
    exact ⟨⟨(tOf_spec (hP m hmms)).2, by simp, by norm_num⟩, by simpa using th hm100,
      by simp; linarith⟩
  have hmem := RHHeight.mem_and_simple_of_Ncount_le Hset hHsub hcardH hN
  refine ⟨?_, ?_⟩
  · intro s hz him hle
    obtain ⟨h0, h1⟩ := re_strip hz him
    by_cases hs100 : s.im ≤ 100
    · have : s ∈ (Lset : Set ℂ) := by rw [hLeq]; exact ⟨hz, h0, h1, him, hs100⟩
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp this)
      exact ⟨m, (hlowm m (List.mem_toFinset.mp hm)).1, rfl⟩
    · push Not at hs100
      have := (hmem s ⟨⟨hz, h0, h1⟩, hs100, by linarith⟩).1
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp this
      exact ⟨m, (hhighm m (List.mem_toFinset.mp hm)).1, rfl⟩
  · intro m hm
    obtain ⟨t0, t1, tlh, tl, th⟩ := ht m hm
    have hz := (tOf_spec (hP m hm)).2
    rcases tlh with h | h
    · exact (RHHeight100.rh_height_hundred (ρOf m) hz (by simp) (by norm_num) (by simpa using t0)
        (by simpa using h.le)).2
    · have hρ : ρOf m ∈ Zeta23.zerosIn 100 T₂ :=
        ⟨⟨hz, by simp, by norm_num⟩, by simpa using h, by simp; linarith⟩
      exact (RHHeight.toNat_analyticOrderAt_eq_one_iff _).mp (hmem _ hρ).2

end ZetaCert.Assembly
