/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.LogCert
public import ZetaCert.PrimeData
public import ZetaCert.Eval.SumsSound

@[expose] public section

/-!
# The prime data, checked once: `w ≈ p^{-1/2}` and `|L - log p| ≤ 2^-126` for all `p ≤ 4000`
-/

namespace ZetaCert.Data

open ZetaCert ZetaCert.Eval

/-- `(p, w, L)` for the primes `p ≤ 4000`. -/
def pdata : List (Nat × Nat × Nat) := pcAll.map (fun e => (e.1, e.2.1, e.2.2.1))

/-- The log certificates of a chunk. -/
def logsOK (l : List (Nat × Nat × Nat × Nat × Nat)) : Bool :=
  l.all fun e => logCheck L2 e.1 e.2.2.2.1 e.2.2.1 e.2.2.2.2

theorem log2_ok : |Real.log 2 - L2 / 2 ^ 160| ≤ 1 / 2 ^ 158 :=
  log2Check_spec (L2 := L2) (J := 52) (by decide +kernel)

theorem logs_pc0 : logsOK pc0 = true := by decide +kernel
theorem logs_pc1 : logsOK pc1 = true := by decide +kernel
theorem logs_pc2 : logsOK pc2 = true := by decide +kernel
theorem logs_pc3 : logsOK pc3 = true := by decide +kernel

theorem logsOK_append {l₁ l₂ : List (Nat × Nat × Nat × Nat × Nat)} (h₁ : logsOK l₁ = true)
    (h₂ : logsOK l₂ = true) : logsOK (l₁ ++ l₂) = true := by
  unfold logsOK at *; rw [List.all_append, h₁, h₂]; rfl

theorem logs_all : logsOK pcAll = true :=
  logsOK_append (logsOK_append (logsOK_append logs_pc0 logs_pc1) logs_pc2) logs_pc3

theorem pdata_log : LogOK (1 / 2 ^ 126) pdata := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have h := List.all_eq_true.mp logs_all e he
  have := logCheck_spec log2_ok h
  rw [abs_sub_comm]; simpa [vP] using this

theorem pdata_w : wOK pdata = true := by decide +kernel

theorem wOK_iff (l : List (Nat × Nat × Nat)) :
    wOK l = true ↔ ∀ d ∈ l, 2 ≤ d.1 ∧ d.2.1 * d.2.1 * d.1 ≤ 2 ^ 256 ∧
      2 ^ 256 < (d.2.1 + 1) * (d.2.1 + 1) * d.1 := by
  induction l with
  | nil => simp [wOK]
  | cons d l ih =>
    obtain ⟨p, w, L⟩ := d
    simp only [wOK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem wOK_sublist {l l' : List (Nat × Nat × Nat)} (h : wOK l = true) (hs : ∀ d ∈ l', d ∈ l) :
    wOK l' = true := (wOK_iff l').mpr fun d hd => (wOK_iff l).mp h d (hs d hd)

end ZetaCert.Data
