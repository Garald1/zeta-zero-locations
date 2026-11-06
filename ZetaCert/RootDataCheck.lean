/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.RootData
import ZetaCert.PrimeDataCheck
import ZetaCert.Eval.SigmaSound

/-! # The root data, checked once: `x ≈ p^{-1/4096}`, and its alignment with `pdata` -/

namespace ZetaCert.Data

open ZetaCert ZetaCert.Eval

/-- `(p, x, L)` for the primes `p ≤ 4000`, `x ≈ p^{-1/4096}`. -/
def rdata : List (Nat × Nat × Nat) :=
  List.zipWith (fun r d => (r.1, r.2, d.2.2)) rcAll pdata

def rootsOK (l : List (Nat × Nat)) : Bool := l.all fun e => Nat.ble 2 e.1 && rootOK e.1 e.2 4096

theorem roots_rc0 : rootsOK rc0 = true := by decide +kernel
theorem roots_rc1 : rootsOK rc1 = true := by decide +kernel
theorem roots_rc2 : rootsOK rc2 = true := by decide +kernel
theorem roots_rc3 : rootsOK rc3 = true := by decide +kernel

theorem rootsOK_append {l₁ l₂ : List (Nat × Nat)} (h₁ : rootsOK l₁ = true) (h₂ : rootsOK l₂ = true) :
    rootsOK (l₁ ++ l₂) = true := by
  unfold rootsOK at *; rw [List.all_append, h₁, h₂]; rfl

theorem roots_all : rootsOK rcAll = true :=
  rootsOK_append (rootsOK_append (rootsOK_append roots_rc0 roots_rc1) roots_rc2) roots_rc3

/-- The primes of `rcAll` and `pdata` agree, in order. -/
theorem rc_primes : rcAll.map Prod.fst = pdata.map Prod.fst := by decide +kernel

theorem rdata_L : rdata.map (fun d => (d.1, d.2.2)) = pdata.map (fun d => (d.1, d.2.2)) := by
  decide +kernel

theorem rdata_roots : rdata.all (fun d => Nat.ble 2 d.1 && rootOK d.1 d.2.1 4096) = true := by
  decide +kernel

theorem rdata_mem {d : Nat × Nat × Nat} (hd : d ∈ rdata) :
    2 ≤ d.1 ∧ rootOK d.1 d.2.1 4096 = true ∧ |vP d.2.2 - Real.log d.1| ≤ 1 / 2 ^ 126 := by
  have h := List.all_eq_true.mp rdata_roots d hd
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  refine ⟨h.1, h.2, ?_⟩
  have hm : (d.1, d.2.2) ∈ pdata.map (fun d => (d.1, d.2.2)) := by
    rw [← rdata_L]; exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨e, he, hed⟩ := List.mem_map.mp hm
  have := pdata_log e he
  simp only [Prod.mk.injEq] at hed
  rw [← hed.1, ← hed.2]; exact this

end ZetaCert.Data
