/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib
public import ZetaCert.Eval.Core

@[expose] public section

/-! # Soundness of the enumeration check `enumOK` -/

namespace ZetaCert.Eval

theorem bitsOf_spec : ∀ (l : List ℕ) (b b' : ℕ), bitsOf l b = (true, b') →
    l.Nodup ∧ (∀ n ∈ l, Nat.testBit b n = false) ∧
      ∀ k, Nat.testBit b' k = (Nat.testBit b k || decide (k ∈ l)) := by
  intro l
  induction l with
  | nil => intro b b' h; simp [bitsOf] at h; subst h; simp
  | cons n l ih =>
    intro b b' h
    cases hb : Nat.testBit b n with
    | true => simp [bitsOf, hb] at h
    | false =>
      simp only [bitsOf, hb, force_eq] at h
      obtain ⟨h1, h2, h3⟩ := ih _ _ h
      have hbit : ∀ k, Nat.testBit (Nat.lor b (Nat.pow 2 n)) k = (Nat.testBit b k || decide (n = k)) := by
        intro k
        rw [show Nat.lor b (Nat.pow 2 n) = b ||| 2 ^ n from rfl, Nat.testBit_lor, Nat.testBit_two_pow]
      refine ⟨?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨fun hn => ?_, h1⟩
        have := h2 n hn; rw [hbit] at this; simp at this
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hb
        · have := h2 k hk; rw [hbit] at this; simp at this; exact this.1
      · intro k
        rw [h3, hbit]
        by_cases hk : k = n
        · subst hk; simp
        · simp [hk, Ne.symm hk]

theorem enumOK_spec {N fuel : ℕ} {ps : List ℕ} (h : enumOK N fuel ps = true) :
    (goNs N fuel ps 1).Perm (List.range' 2 (N - 1)) := by
  unfold enumOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e1 : bitsOf (goNs N fuel ps 1) 0 = (true, (bitsOf (goNs N fuel ps 1) 0).2) := by
    rw [← h1]
  have e2 : bitsOf (List.range' 2 (N - 1)) 0 = (true, (bitsOf (List.range' 2 (N - 1)) 0).2) := by
    rw [← h2]
  obtain ⟨n1, -, b1⟩ := bitsOf_spec _ _ _ e1
  obtain ⟨n2, -, b2⟩ := bitsOf_spec _ _ _ e2
  have heq : (bitsOf (goNs N fuel ps 1) 0).2 = (bitsOf (List.range' 2 (N - 1)) 0).2 :=
    Nat.eq_of_beq_eq_true h3
  rw [List.perm_ext_iff_of_nodup n1 n2]
  intro a
  have := b1 a
  rw [heq, b2 a] at this
  simp only [Nat.zero_testBit, Bool.false_or] at this
  rw [decide_eq_decide] at this
  exact this.symm

end ZetaCert.Eval
