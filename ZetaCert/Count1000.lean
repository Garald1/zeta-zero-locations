/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Leg1000
public import RHHeight.ExactArgument
public import RHHeight.GammaIncrement
public import RHHeight100.HorizontalLegs100

@[expose] public section

/-!
# The number of zeros with `100 < Im ρ ≤ T₂`, `T₂ = 512069/512`: `Ncount 100 T₂ = 620`

From zeta-lab's `exact_argument` (hunt #137): the leg at height 100 and its argument
(`horizontalLegs100`), our leg at `T₂` (`ZetaCert.Leg1000.leg`), and an enclosure of
`∫_{100}^{T₂} μ` from zeta-lab's `abs_integral_mu_sub_le` with logarithms certified by `logCheck`.
Numerically (not used): `∫ μ ≈ 619.7226`, `(arg ζ(1/2+iT₂) - arg ζ(1/2+100i))/π ≈ 0.2774`.
-/

open Complex Set

namespace ZetaCert.Count1000

open ZetaCert ZetaCert.Data RHHeight RHHeight.GammaSide

/-- `T₂ = 512069/512 ≈ 1000.1348`. -/
noncomputable def T2 : ℝ := 512069 / 512

theorem logA : |Real.log (1048858905188 : ℕ) - (9418581692995353850456017789306064970257 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 39) (J := 37) (by decide +kernel)
theorem log40001 : |Real.log (40001 : ℕ) - (3605856455327395411566799875468339383532 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 15) (J := 19) (by decide +kernel)
theorem log5 : |Real.log (5 : ℕ) - (547663342255369772667394339939292885492 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 2) (J := 20) (by decide +kernel)
theorem logPa : |Real.log (314159265358979323846 : ℕ) - (16060113504659630929199571625156681839648 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 68) (J := 13) (by decide +kernel)
theorem logPb : |Real.log (314159265358979323847 : ℕ) - (16060113504659630929200654777571531387828 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 68) (J := 13) (by decide +kernel)

theorem log_pi_bounds :
    Real.log (314159265358979323846 : ℕ) - 20 * (Real.log 2 + Real.log (5 : ℕ)) ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ Real.log (314159265358979323847 : ℕ) - 20 * (Real.log 2 + Real.log (5 : ℕ)) := by
  have h10 : Real.log ((10 : ℝ) ^ 20) = 20 * (Real.log 2 + Real.log (5 : ℕ)) := by
    rw [Real.log_pow, show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    push_cast; ring
  have ha := Real.pi_gt_d20
  have hb := Real.pi_lt_d20
  constructor
  · rw [← h10, ← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_log (by norm_num) (by push_cast; norm_num at ha ⊢; linarith)
  · rw [← h10, ← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_log Real.pi_pos (by push_cast; norm_num at hb ⊢; linarith)

theorem two_pi_mul_muPrim_sub :
    2 * Real.pi * (muPrim T2 - muPrim 100) =
      T2 / 2 * (Real.log (1048858905188 : ℕ) - 22 * Real.log 2) - 50 * (Real.log (40001 : ℕ) - 4 * Real.log 2)
      - (T2 - 100) - (1 / 2) * (Real.arctan (2 * T2) - Real.arctan 200) - (T2 - 100) * Real.log Real.pi := by
  have hπ := Real.pi_pos
  have e1 : Real.log ((1 + 4 * T2 ^ 2) / 16) = Real.log (1048858905188 : ℕ) - 22 * Real.log 2 := by
    rw [show (1 + 4 * T2 ^ 2) / 16 = ((1048858905188 : ℕ) : ℝ) / 2 ^ 22 by unfold T2; norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have e2 : Real.log ((1 + 4 * (100 : ℝ) ^ 2) / 16) = Real.log (40001 : ℕ) - 4 * Real.log 2 := by
    rw [show (1 + 4 * (100 : ℝ) ^ 2) / 16 = ((40001 : ℕ) : ℝ) / 2 ^ 4 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  unfold muPrim
  rw [e1, e2, show (2 : ℝ) * 100 = 200 by norm_num]
  field_simp
  ring

/-- **The Γ increment**: `619.55 ≤ ∫_{100}^{T₂} μ ≤ 619.9`. -/
theorem gamma_increment :
    (61955 / 100 : ℝ) ≤ ∫ t in (100 : ℝ)..T2, Zeta23.mu t ∧ ∫ t in (100 : ℝ)..T2, Zeta23.mu t ≤ 6199 / 10 := by
  have hπ := Real.pi_pos
  have hT2 : T2 = 512069 / 512 := rfl
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_integral_mu_sub_le (T₁ := 100) (T₂ := T2) (by norm_num)
    (by rw [hT2]; norm_num))
  have hF := two_pi_mul_muPrim_sub
  have hA := abs_le.mp logA
  have h40 := abs_le.mp log40001
  have h5 := abs_le.mp log5
  have hpa := abs_le.mp logPa
  have hpb := abs_le.mp logPb
  have h2 := abs_le.mp log2_ok
  obtain ⟨lp1, lp2⟩ := log_pi_bounds
  have ha1 : Real.arctan (2 * T2) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have ha2 : Real.pi / 2 - 1 / 200 ≤ Real.arctan 200 := by
    have := Real.arctan_inv_of_pos (x := (200 : ℝ)) (by norm_num)
    have h3 := Real.arctan_le_self (x := (200 : ℝ)⁻¹) (by norm_num)
    norm_num at this h3 ⊢; linarith
  have ha3 : Real.arctan 200 ≤ Real.arctan (2 * T2) :=
    Real.arctan_strictMono.monotone (by rw [hT2]; norm_num)
  have pi1 := Real.pi_gt_d20
  have pi2 := Real.pi_lt_d20
  set G := ∫ t in (100 : ℝ)..T2, Zeta23.mu t
  set M := muPrim T2 - muPrim 100
  set X := 2 * Real.pi * M
  have hX := hF
  rw [hT2] at hX ha1 ha3
  norm_num [L2] at hA h40 h5 hpa hpb h2 pi1 pi2 hX lp1 lp2 ha1
  have ha3' : Real.arctan 200 ≤ Real.arctan (512069 / 256) := Real.arctan_strictMono.monotone (by norm_num)
  have herr : 6 / Real.pi * (1 / 100 - 1 / T2) = (6 * (1 / 100 - 512 / 512069)) / Real.pi := by
    rw [hT2]; field_simp
  rw [herr] at hlo hhi
  have hM : M = X / (2 * Real.pi) := by simp only [X]; field_simp
  rw [hM] at hlo hhi
  have hXlo : 38938 / 10 ≤ X := by rw [hX]; linarith
  have hXhi : X ≤ 38939 / 10 := by rw [hX]; linarith
  set δ : ℝ := 6 * (1 / 100 - 512 / 512069) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; norm_num
  have hδ1 : δ ≤ 6 / 100 := by rw [hδ]; norm_num
  have e1 : X / (2 * Real.pi) - δ / Real.pi = (X - 2 * δ) / (2 * Real.pi) := by field_simp
  have e2 : X / (2 * Real.pi) + δ / Real.pi = (X + 2 * δ) / (2 * Real.pi) := by field_simp
  constructor
  · have : (61955 / 100 : ℝ) ≤ (X - 2 * δ) / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  · have : (X + 2 * δ) / (2 * Real.pi) ≤ 6199 / 10 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-- **The count**: exactly 620 zeros (with multiplicity) with `0 < Re ρ < 1`, `100 < Im ρ ≤ T₂`. -/
theorem ncount : Zeta23.Ncount 100 T2 = 620 := by
  obtain ⟨-, hleg100, -, -, ha1lo, ha1hi⟩ := RHHeight100.horizontalLegs100
  have hT2 : T2 = 512069 / 512 := rfl
  have h100 : ((100 : ℝ) : ℂ) = 100 := by norm_num
  have hlegT : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + (T2 : ℂ) * I)).re := by
    intro σ hσ; have := ZetaCert.Leg1000.leg σ hσ; rw [hT2]; exact this
  have hid := exact_argument 100 T2 (by norm_num) (by rw [hT2]; norm_num)
    (fun σ hσ => by simpa only [h100] using hleg100 σ hσ) hlegT
  rw [h100] at hid
  obtain ⟨hGlo, hGhi⟩ := gamma_increment
  have hre : 0 < (riemannZeta (1 / 2 + (T2 : ℂ) * I)).re := by
    have := hlegT (1 / 2) ⟨le_rfl, by norm_num⟩; simpa using this
  have harg := (Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hre)
  rw [abs_lt] at harg
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  set a1 := (riemannZeta (1 / 2 + 100 * I)).arg
  set a2 := (riemannZeta (1 / 2 + (T2 : ℂ) * I)).arg
  set G := ∫ t in (100 : ℝ)..T2, Zeta23.mu t
  have hD1 : (a2 - a1) / Real.pi < 1 / 2 + 1 / 15 := by
    rw [div_lt_iff₀ hπ]; nlinarith
  have hD2 : -(1 / 2) < (a2 - a1) / Real.pi := by
    rw [lt_div_iff₀ hπ]; nlinarith
  have hlt : (Zeta23.Ncount 100 T2 : ℝ) < 621 := by rw [hid]; linarith
  have hgt : (619 : ℝ) < Zeta23.Ncount 100 T2 := by rw [hid]; linarith
  have h1 : Zeta23.Ncount 100 T2 < 621 := by exact_mod_cast hlt
  have h2 : 619 < Zeta23.Ncount 100 T2 := by exact_mod_cast hgt
  omega

end ZetaCert.Count1000
