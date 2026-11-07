/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Eval.DirSound
public import ZetaCert.Eval.EnumSound

@[expose] public section

/-!
# The Dirichlet sums at `s = 1/2 + it`: `sums_spec`

From the prime data checks (`w ≈ p^{-1/2}` by an integer check, `|L - log p| ≤ δL`), the
argument check `smallArgs`, and the enumeration check `enumOK`, the accumulators of `sums` are
within explicit errors of `Σ_{n ≤ N} n^{-s}` and `-Σ_{n ≤ N} log n · n^{-s}`.
-/

set_option exponentiation.threshold 600

namespace ZetaCert.Eval

open Complex

/-- The integer check for `w ≈ p^{-1/2}`, and `p ≥ 2`. -/
def wOK : List (Nat × Nat × Nat) → Bool
  | [] => true
  | (p, w, _) :: ds =>
    Nat.ble 2 p && Nat.ble (w * w * p) (2 ^ 256) && Nat.blt (2 ^ 256) ((w + 1) * (w + 1) * p) && wOK ds

/-- The logarithm hypothesis on the data. -/
def LogOK (δL : ℝ) (data : List (Nat × Nat × Nat)) : Prop :=
  ∀ d ∈ data, |vP d.2.2 - Real.log d.1| ≤ δL

theorem primeTerms_p (K T : ℕ) : ∀ data : List (Nat × Nat × Nat),
    (primeTerms K T data).map PT.p = data.map Prod.fst := by
  intro data
  induction data with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨p, w, L⟩ := d
    simp only [primeTerms, force_eq, List.map_cons, ih]

/-- The error of one prime term. -/
noncomputable def Ep (K : ℕ) (t δL : ℝ) : ℝ := 2 ^ (K + 1) * (77 * u) + 2 * (t * δL) + 3 * u

theorem primeTerms_ok {K T : ℕ} {t δL : ℝ} (hT : vP T = t) (hK : K ≤ 40) (hδ : t * δL ≤ 1 / 2 ^ 42) :
    ∀ data : List (Nat × Nat × Nat), wOK data = true → LogOK δL data → smallArgs K T data = true →
      PrimesOK (1 / 2 + t * I) (Ep K t δL) δL (primeTerms K T data) := by
  intro data
  induction data with
  | nil => intro _ _ _ q hq; simp [primeTerms] at hq
  | cons d ds ih =>
    obtain ⟨p, w, L⟩ := d
    intro hw hl hsm q hq
    simp only [wOK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hw
    obtain ⟨⟨⟨h2, h1⟩, h3⟩, hw'⟩ := hw
    simp only [smallArgs, Bool.and_eq_true, Nat.ble_eq] at hsm
    simp only [primeTerms, force_eq, List.mem_cons] at hq
    rcases hq with rfl | hq
    · have hL := hl (p, w, L) (List.mem_cons_self ..)
      refine ⟨h2, ?_, hL⟩
      exact primeTerm_spec (lt_of_lt_of_le (by norm_num) h2) h1 h3 hT hL hsm.1 hK hδ
    · exact ih hw' (fun d hd => hl d (List.mem_cons_of_mem _ hd)) hsm.2 q hq

theorem sum_range'_two (f : ℕ → ℂ) : ∀ N : ℕ, 1 ≤ N →
    ((List.range' 2 (N - 1)).map f).sum + f 0 + f 1 = ∑ n ∈ Finset.range (N + 1), f n := by
  intro N hN
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Finset.sum_range_succ]
    · have := ih hn
      rw [Finset.sum_range_succ, ← this, show n + 1 - 1 = (n - 1) + 1 by omega, List.range'_concat]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      rw [show 2 + 1 * (n - 1) = n + 1 by omega]
      ring

/-- **The Dirichlet sums at `s = 1/2 + it`.** -/
theorem sums_spec {N K T fuel Dp : ℕ} {data : List (Nat × Nat × Nat)} {t δL Λ : ℝ}
    (hT : vP T = t) (hK : K ≤ 40) (hδ : t * δL ≤ 1 / 2 ^ 42) (hδL : 0 ≤ δL)
    (hw : wOK data = true) (hl : LogOK δL data) (hsm : smallArgs K T data = true)
    (hen : enumOK N fuel (data.map Prod.fst) = true) (hN1 : 1 ≤ N) (hN20 : N ≤ 2 ^ 20)
    (hN : N < 2 ^ Dp) (hsmall : (Dp : ℝ) * (Ep K t δL + 4 * u) * Ep K t δL ≤ u)
    (hsmall1 : (Dp : ℝ) * (Ep K t δL + 4 * u) ≤ 1)
    (hΛ : Real.log N + Dp * δL ≤ Λ) (hΛ1 : Λ ≤ 2 ^ 20) :
    let a := sums N K T fuel data
    ‖accS a - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ (1 / 2 + t * I)‖ ≤
        N * (Dp * (Ep K t δL + 4 * u)) ∧
    ‖accD a - ∑ n ∈ Finset.range (N + 1), -Complex.log n * (n : ℂ) ^ (-(1 / 2 + t * I))‖ ≤
        N * (Λ * (Dp * (Ep K t δL + 4 * u)) + Dp * δL + 2 * u) := by
  intro a
  set s : ℂ := 1 / 2 + t * I
  have hs : 0 ≤ s.re := by simp [s]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [s] at this
  have hu := u_pos
  have hEp1 : Ep K t δL ≤ 1 := by
    have h2K : (2 : ℝ) ^ (K + 1) ≤ 2 ^ 41 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : 2 ^ (K + 1) * (77 * u) ≤ 2 ^ 41 * (77 * u) := by gcongr <;> linarith
    have : 2 ^ 41 * (77 * u) + 2 * (1 / 2 ^ 42) + 3 * u ≤ (1 : ℝ) := by unfold u; norm_num
    unfold Ep; linarith
  have hok := primeTerms_ok hT hK hδ data hw hl hsm
  have hperm := enumOK_spec hen
  rw [← primeTerms_p K T data] at hperm
  set ns := goNs N fuel ((primeTerms K T data).map PT.p) 1
  have hlen : ns.length = N - 1 := by rw [hperm.length_eq]; simp
  have hlenR : (ns.length : ℝ) ≤ N := by rw [hlen]; exact_mod_cast Nat.sub_le N 1
  have hNR : (N : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hN20
  have h1 : ‖cv (Nat.add ONE O) O - ((1 : ℕ) : ℂ) ^ (-s)‖ ≤ (0 : ℕ) * (Ep K t δL + 4 * u) := by
    have hc1 : cv (Nat.add ONE O) O = 1 := by
      apply Complex.ext
      · rw [cv_re, vO_ONE_O]; rfl
      · rw [cv_im, vO_O]; rfl
    rw [hc1]; simp
  have h2 : |vP 0 - Real.log (1 : ℕ)| ≤ (0 : ℕ) * δL := by simp [vP]
  have hacc0S : accS ⟨Nat.add ONE O, O, O, O⟩ = 1 := by
    apply Complex.ext <;> simp [accS, cv, vO_ONE_O, vO_ONE_add_O, vO_O]
  have hacc0D : accD ⟨Nat.add ONE O, O, O, O⟩ = 0 := by
    apply Complex.ext <;> simp [accD, cv, vO_O]
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have : 0 ≤ (Dp : ℝ) * δL := by positivity
    linarith
  have hpre1 : ‖accS ⟨Nat.add ONE O, O, O, O⟩‖ + 2 * ns.length ≤ 2 ^ 60 := by
    rw [hacc0S]; simp; linarith
  have hpre2 : ‖accD ⟨Nat.add ONE O, O, O, O⟩‖ + (2 * Λ + 2 * u) * ns.length ≤ 2 ^ 60 := by
    rw [hacc0D, norm_zero, zero_add]
    have hu1 : u ≤ 1 := by unfold u; rw [div_le_one (by positivity)]; norm_num
    have : (2 * Λ + 2 * u) * ns.length ≤ (2 * 2 ^ 20 + 2) * 2 ^ 20 := by
      apply mul_le_mul (by linarith) (hlenR.trans hNR) (by positivity) (by positivity)
    linarith
  obtain ⟨g1, g2, -, -⟩ := go_spec N s hs (Ep K t δL) δL Λ Dp hN hEp1 hδL hsmall hsmall1 hΛ hΛ1 fuel
    (primeTerms K T data) 1 _ _ 0 ⟨Nat.add ONE O, O, O, O⟩ 0 hok le_rfl hN1 (by simp) h1 h2 hpre1 hpre2
  rw [hacc0S] at g1
  rw [hacc0D, sub_zero] at g2
  have hsumS : (ns.map (fS s)).sum + 1 = ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s := by
    rw [hperm.map (fS s) |>.sum_eq]
    have := sum_range'_two (fun n => 1 / (n : ℂ) ^ s) N hN1
    rw [← this]
    have hf : ∀ n : ℕ, fS s n = 1 / (n : ℂ) ^ s := fun n => by simp [fS, Complex.cpow_neg]
    rw [List.map_congr_left (fun n _ => hf n)]
    simp [Complex.zero_cpow hs0]
  have hsumD : (ns.map (fD s)).sum = ∑ n ∈ Finset.range (N + 1), -Complex.log n * (n : ℂ) ^ (-s) := by
    rw [hperm.map (fD s) |>.sum_eq]
    have := sum_range'_two (fun n => -Complex.log n * (n : ℂ) ^ (-s)) N hN1
    rw [← this]
    have hf : ∀ n : ℕ, fD s n = -Complex.log n * (n : ℂ) ^ (-s) := fun n => by
      simp [fD, Complex.natCast_log]
    rw [List.map_congr_left (fun n _ => hf n)]
    simp
  have hE0 : 0 ≤ (Dp : ℝ) * (Ep K t δL + 4 * u) := by
    have : 0 ≤ Ep K t δL := by
      unfold Ep; have : 0 ≤ t := hT ▸ vP_nonneg T; positivity
    positivity
  constructor
  · rw [← hsumS]
    have e : accS a - ((ns.map (fS s)).sum + 1) = accS a - 1 - (ns.map (fS s)).sum := by ring
    rw [e]
    exact g1.trans (mul_le_mul_of_nonneg_right hlenR hE0)
  · rw [← hsumD]
    refine g2.trans (mul_le_mul_of_nonneg_right hlenR ?_)
    positivity

end ZetaCert.Eval
