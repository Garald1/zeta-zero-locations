/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.Assembly
import ZetaCert.LegCertSound
import ZetaCert.PrimeDataCheck
import RHHeight.ExactArgument
import RHHeight.GammaIncrement

/-!
# Counting windows `(L, U]` and the range statements

* `arg_bounds_of_im_nonneg`, `arg_bounds_of_im_neg`: bounds on `arg z` from `Re z ≥ v > 0` and
  bounds on `Im z` (as given by `lcI_spec`).
* `two_pi_dmu`: `2π (muPrim U - muPrim L)` to within an explicit error, from certified logarithms.
* `ncount_window`: `Ncount L U = n` from zeta-lab's `exact_argument`, the two legs, an enclosure
  of `2π (muPrim U - muPrim L)` (via zeta-lab's `abs_integral_mu_sub_le`) and bounds on the
  arguments of `ζ(1/2 + iL)` and `ζ(1/2 + iU)`.
* `wmain`: every zero with `L < Im s ≤ U` is one of the certified zeros of a list, all simple
  (zeta-lab's `mem_and_simple_of_Ncount_le`).
* `rmain`: the three statements of a range file `(a, b]` with `L ≤ a`, `b ≤ U`.
-/

open Complex Set

namespace ZetaCert.Window

open ZetaCert ZetaCert.Assembly ZetaCert.Data RHHeight RHHeight.GammaSide

/-! ## Arguments -/

theorem arg_bounds_of_im_nonneg {z : ℂ} {v whi : ℝ} (hv : 0 < v) (hre : v ≤ z.re) (him : 0 ≤ z.im)
    (hwhi : z.im ≤ whi) : 0 ≤ z.arg ∧ z.arg ≤ whi / v := by
  have hre0 : 0 < z.re := by linarith
  have h0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him
  have hlt : z.arg < Real.pi / 2 :=
    (abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hre0))).2
  have ht := Real.le_tan h0 hlt
  rw [Complex.tan_arg] at ht
  refine ⟨h0, ht.trans ?_⟩
  rw [div_le_div_iff₀ hre0 hv]
  nlinarith

theorem arg_bounds_of_im_neg {z : ℂ} {v wlo : ℝ} (hv : 0 < v) (hre : v ≤ z.re) (him : z.im < 0)
    (hwlo : wlo ≤ z.im) : wlo / v ≤ z.arg ∧ z.arg ≤ 0 := by
  have hre0 : 0 < z.re := by linarith
  have h0 : z.arg < 0 := Complex.arg_neg_iff.mpr him
  have hlt : -(Real.pi / 2) < z.arg :=
    (abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hre0))).1
  have ht := Real.le_tan (x := -z.arg) (by linarith) (by linarith)
  rw [Real.tan_neg, Complex.tan_arg] at ht
  refine ⟨?_, h0.le⟩
  have : -z.im / z.re ≤ -wlo / v := by
    rw [div_le_div_iff₀ hre0 hv]; nlinarith
  have e1 : -(z.im / z.re) = -z.im / z.re := by ring
  have e2 : wlo / v = -(-wlo / v) := by ring
  rw [e2]; linarith

/-- The point `1/2 + iγ` of a leg certificate, with bounds on real and imaginary parts. -/
theorem half_point {G N K k fuel Dp : ℕ} {v d wlo whi : ℚ}
    (h : lcI 2048 G N K k fuel Dp v d wlo whi = true) :
    ((v : ℝ) ≤ (riemannZeta (1 / 2 + (((G : ℝ) / 2 ^ 80 : ℝ) : ℂ) * I)).re) ∧
      ((wlo : ℝ) ≤ (riemannZeta (1 / 2 + (((G : ℝ) / 2 ^ 80 : ℝ) : ℂ) * I)).im ∧
        (riemannZeta (1 / 2 + (((G : ℝ) / 2 ^ 80 : ℝ) : ℂ) * I)).im ≤ whi) := by
  have := lcI_spec h
  simp only at this
  have e : ((((2048 : ℕ) : ℝ) / 4096 : ℝ) : ℂ) = 1 / 2 := by push_cast; norm_num
  rw [e] at this
  exact ⟨this.1.1, this.2⟩

/-! ## The Γ side -/

/-- `round(2^128 log π)`, to within `10⁻²⁰` (from `π` to 20 decimals). -/
def LP : ℕ := 389531395041969593093088289785991088536

theorem logPa : |Real.log (314159265358979323846 : ℕ) - (16060113504659630929199571625156681839648 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 68) (J := 13) (by decide +kernel)
theorem logPb : |Real.log (314159265358979323847 : ℕ) - (16060113504659630929200654777571531387828 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 68) (J := 13) (by decide +kernel)
theorem log5 : |Real.log (5 : ℕ) - (547663342255369772667394339939292885492 : ℕ) / 2 ^ 128| ≤ 1 / 2 ^ 126 :=
  logCheck_spec log2_ok (k := 2) (J := 20) (by decide +kernel)

theorem log_pi_ok : |Real.log Real.pi - (LP : ℝ) / 2 ^ 128| ≤ 1 / 10 ^ 20 := by
  have h10 : Real.log ((10 : ℝ) ^ 20) = 20 * (Real.log 2 + Real.log (5 : ℕ)) := by
    rw [Real.log_pow, show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    push_cast; ring
  have ha := Real.pi_gt_d20
  have hb := Real.pi_lt_d20
  have lp1 : Real.log (314159265358979323846 : ℕ) - 20 * (Real.log 2 + Real.log (5 : ℕ)) ≤ Real.log Real.pi := by
    rw [← h10, ← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_log (by norm_num) (by push_cast; norm_num at ha ⊢; linarith)
  have lp2 : Real.log Real.pi ≤ Real.log (314159265358979323847 : ℕ) - 20 * (Real.log 2 + Real.log (5 : ℕ)) := by
    rw [← h10, ← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_log Real.pi_pos (by push_cast; norm_num at hb ⊢; linarith)
  have hpa := abs_le.mp logPa
  have hpb := abs_le.mp logPb
  have h5 := abs_le.mp log5
  have h2 := abs_le.mp log2_ok
  unfold LP
  norm_num [L2] at hpa hpb h5 h2 lp1 lp2 ⊢
  rw [abs_le]; constructor <;> linarith

theorem arctan_two_mul_sub {L U : ℝ} (hL : 1 ≤ L) (hLU : L ≤ U) :
    0 ≤ Real.arctan (2 * U) - Real.arctan (2 * L) ∧
      Real.arctan (2 * U) - Real.arctan (2 * L) ≤ 1 / (2 * L) := by
  have hL0 : 0 < 2 * L := by linarith
  have h1 := Real.arctan_lt_pi_div_two (2 * U)
  have h2 := Real.arctan_inv_of_pos hL0
  have h3 := Real.arctan_le_self (x := (2 * L)⁻¹) (by positivity)
  have h4 : Real.arctan (2 * L) ≤ Real.arctan (2 * U) :=
    Real.arctan_strictMono.monotone (by linarith)
  rw [one_div]
  constructor <;> linarith

/-- `2π (muPrim U - muPrim L)` from certified values of `log nL`, `log nU`, `log 2`, `log π`,
where `(1 + 4T²)/16 = n_T / 2^{e_T}`. -/
theorem two_pi_dmu {L U : ℝ} {nL nU eL eU lL lU : ℕ} (hL : 1 ≤ L) (hLU : L ≤ U)
    (hnL : (1 + 4 * L ^ 2) / 16 = (nL : ℝ) / 2 ^ eL) (hnU : (1 + 4 * U ^ 2) / 16 = (nU : ℝ) / 2 ^ eU)
    (hlL : |Real.log nL - (lL : ℝ) / 2 ^ 128| ≤ 1 / 2 ^ 126)
    (hlU : |Real.log nU - (lU : ℝ) / 2 ^ 128| ≤ 1 / 2 ^ 126) :
    |2 * Real.pi * (muPrim U - muPrim L) -
        (U / 2 * ((lU : ℝ) / 2 ^ 128 - eU * ((L2 : ℝ) / 2 ^ 160)) -
          L / 2 * ((lL : ℝ) / 2 ^ 128 - eL * ((L2 : ℝ) / 2 ^ 160)) - (U - L) - (U - L) * ((LP : ℝ) / 2 ^ 128))| ≤
      U / 2 * (1 / 2 ^ 126 + eU / 2 ^ 158) + L / 2 * (1 / 2 ^ 126 + eL / 2 ^ 158) + (U - L) / 10 ^ 20 +
        1 / (4 * L) := by
  have hπ := Real.pi_pos
  have hL0 : 0 < L := by linarith
  have hnL0 : (0 : ℝ) < nL := by
    have : (0 : ℝ) < (1 + 4 * L ^ 2) / 16 := by positivity
    rw [hnL] at this; exact (div_pos_iff_of_pos_right (by positivity)).mp this
  have hnU0 : (0 : ℝ) < nU := by
    have : (0 : ℝ) < (1 + 4 * U ^ 2) / 16 := by positivity
    rw [hnU] at this; exact (div_pos_iff_of_pos_right (by positivity)).mp this
  have e1 : Real.log ((1 + 4 * L ^ 2) / 16) = Real.log nL - eL * Real.log 2 := by
    rw [hnL, Real.log_div hnL0.ne' (by positivity), Real.log_pow]
  have e2 : Real.log ((1 + 4 * U ^ 2) / 16) = Real.log nU - eU * Real.log 2 := by
    rw [hnU, Real.log_div hnU0.ne' (by positivity), Real.log_pow]
  have hX : 2 * Real.pi * (muPrim U - muPrim L) =
      U / 2 * (Real.log nU - eU * Real.log 2) - L / 2 * (Real.log nL - eL * Real.log 2) - (U - L)
        - (1 / 2) * (Real.arctan (2 * U) - Real.arctan (2 * L)) - (U - L) * Real.log Real.pi := by
    unfold muPrim; rw [e1, e2]; field_simp; ring
  rw [hX]
  obtain ⟨a1, a2⟩ := arctan_two_mul_sub hL hLU
  have hl2 := abs_le.mp log2_ok
  have hlp := abs_le.mp log_pi_ok
  have hlL' := abs_le.mp hlL
  have hlU' := abs_le.mp hlU
  have heL : (0 : ℝ) ≤ eL := by positivity
  have heU : (0 : ℝ) ≤ eU := by positivity
  have hUL : 0 ≤ U - L := by linarith
  have h4L : 1 / (2 * L) = 2 * (1 / (4 * L)) := by field_simp; ring
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl2.1 heU, mul_le_mul_of_nonneg_left hl2.2 heU,
      mul_le_mul_of_nonneg_left hl2.1 heL, mul_le_mul_of_nonneg_left hl2.2 heL,
      mul_le_mul_of_nonneg_left hlp.1 hUL, mul_le_mul_of_nonneg_left hlp.2 hUL]
  · nlinarith [mul_le_mul_of_nonneg_left hl2.1 heU, mul_le_mul_of_nonneg_left hl2.2 heU,
      mul_le_mul_of_nonneg_left hl2.1 heL, mul_le_mul_of_nonneg_left hl2.2 heL,
      mul_le_mul_of_nonneg_left hlp.1 hUL, mul_le_mul_of_nonneg_left hlp.2 hUL]

/-! ## The count in a window -/

theorem ncount_window {L U : ℝ} {n : ℕ} (h1 : 1 ≤ L) (hLU : L < U)
    (hlegL : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + L * I)).re)
    (hlegU : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + U * I)).re)
    {Xlo Xhi α1 β1 α2 β2 : ℝ}
    (hX : Xlo ≤ 2 * Real.pi * (muPrim U - muPrim L) ∧ 2 * Real.pi * (muPrim U - muPrim L) ≤ Xhi)
    (ha1 : α1 ≤ (riemannZeta (1 / 2 + L * I)).arg ∧ (riemannZeta (1 / 2 + L * I)).arg ≤ β1)
    (ha2 : α2 ≤ (riemannZeta (1 / 2 + U * I)).arg ∧ (riemannZeta (1 / 2 + U * I)).arg ≤ β2)
    (hlo : Real.pi * ((n : ℝ) - 1) < Xlo / 2 - 6 * (1 / L - 1 / U) + α2 - β1)
    (hhi : Xhi / 2 + 6 * (1 / L - 1 / U) + β2 - α1 < Real.pi * ((n : ℝ) + 1)) :
    Zeta23.Ncount L U = n := by
  have hπ := Real.pi_pos
  have hid := exact_argument L U h1 hLU hlegL hlegU
  have habs0 := abs_integral_mu_sub_le h1 hLU.le
  have k1 : |Real.pi * ((∫ t in L..U, Zeta23.mu t) - (muPrim U - muPrim L))| ≤ 6 * (1 / L - 1 / U) := by
    rw [abs_mul, abs_of_pos hπ]
    calc Real.pi * |(∫ t in L..U, Zeta23.mu t) - (muPrim U - muPrim L)|
        ≤ Real.pi * (6 / Real.pi * (1 / L - 1 / U)) := mul_le_mul_of_nonneg_left habs0 hπ.le
      _ = 6 * (1 / L - 1 / U) := by field_simp
  have habs := abs_le.mp k1
  set G := ∫ t in L..U, Zeta23.mu t
  set M := muPrim U - muPrim L
  set c := 1 / L - 1 / U
  set a1 := (riemannZeta (1 / 2 + L * I)).arg
  set a2 := (riemannZeta (1 / 2 + U * I)).arg
  have e1 : Real.pi * (Zeta23.Ncount L U : ℝ) = Real.pi * G + (a2 - a1) := by
    rw [hid]; field_simp
  have g1 : Real.pi * M - 6 * c ≤ Real.pi * G := by linarith [habs.1]
  have g2 : Real.pi * G ≤ Real.pi * M + 6 * c := by linarith [habs.2]
  have hM : Real.pi * M = (2 * Real.pi * M) / 2 := by ring
  have hlt : Real.pi * (Zeta23.Ncount L U : ℝ) < Real.pi * ((n : ℝ) + 1) := by
    rw [e1]; linarith [ha1.1, ha2.2, hX.2]
  have hgt : Real.pi * ((n : ℝ) - 1) < Real.pi * (Zeta23.Ncount L U : ℝ) := by
    rw [e1]; linarith [ha1.2, ha2.1, hX.1]
  have b1 : (Zeta23.Ncount L U : ℝ) < n + 1 := lt_of_mul_lt_mul_left hlt hπ.le
  have b2 : (n : ℝ) - 1 < Zeta23.Ncount L U := lt_of_mul_lt_mul_left hgt hπ.le
  have c1 : Zeta23.Ncount L U < n + 1 := by exact_mod_cast b1
  have c2 : n < Zeta23.Ncount L U + 1 := by
    have : (n : ℝ) < Zeta23.Ncount L U + 1 := by linarith
    exact_mod_cast this
  omega

/-! ## Assembly in a window -/

/-- Hypotheses on the list `ws` of the certified zeros in the window `(L, U]`. -/
structure WHyp (ws : List ℕ) (L U : ℝ) (cL cU : ℕ) : Prop where
  hP : ∀ m ∈ ws, P m
  hsep : Sep ws
  hrange : ∀ m ∈ ws, cL + 10 ^ 5 < m ∧ m + 10 ^ 5 < cU
  hcL : L ≤ (cL : ℝ) / 10 ^ 24
  hcU : (cU : ℝ) / 10 ^ 24 ≤ U
  hL : 1 ≤ L
  hN : Zeta23.Ncount L U ≤ ws.length

theorem wmain {ws : List ℕ} {L U : ℝ} {cL cU : ℕ} (H : WHyp ws L U cL cU) :
    (∀ s : ℂ, riemannZeta s = 0 → L < s.im → s.im ≤ U → ∃ m ∈ ws, s = ρOf m) ∧
    (∀ m ∈ ws, analyticOrderAt riemannZeta (ρOf m) = 1) := by
  classical
  obtain ⟨hP, hsep, hrange, hcL, hcU, hL, hN⟩ := H
  have hnodup : ws.Nodup := hsep.imp (fun {a b} h => by omega)
  have ht : ∀ m ∈ ws, L < tOf m ∧ tOf m < U := by
    intro m hm
    obtain ⟨r1, r2⟩ := hrange m hm
    have b0 := (tOf_bounds (hP m hm) (a := cL)).1 r1
    have b1 := (tOf_bounds (hP m hm) (a := cU)).2 r2
    exact ⟨by linarith, by linarith⟩
  set Hset := ws.toFinset.image ρOf
  have hinj : Set.InjOn ρOf (ws.toFinset : Set ℕ) := fun a ha b hb h =>
    ρOf_inj hsep hP (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) h
  have hcard : Hset.card = ws.length := by
    rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hnodup]
  have hsub : ∀ ρ ∈ Hset, ρ ∈ Zeta23.zerosIn L U := by
    intro ρ hρ
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hρ
    have hmm := List.mem_toFinset.mp hm
    obtain ⟨t0, t1⟩ := ht m hmm
    exact ⟨⟨(tOf_spec (hP m hmm)).2, by simp, by norm_num⟩, by simpa using t0, by simp; linarith⟩
  have hmem := RHHeight.mem_and_simple_of_Ncount_le Hset hsub hcard hN
  refine ⟨?_, ?_⟩
  · intro s hz hL' hU'
    have him : 0 < s.im := by linarith
    obtain ⟨h0, h1⟩ := re_strip hz him
    have := (hmem s ⟨⟨hz, h0, h1⟩, hL', hU'⟩).1
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp this
    exact ⟨m, List.mem_toFinset.mp hm, rfl⟩
  · intro m hm
    obtain ⟨t0, t1⟩ := ht m hm
    have hρ : ρOf m ∈ Zeta23.zerosIn L U :=
      ⟨⟨(tOf_spec (hP m hm)).2, by simp, by norm_num⟩, by simpa using t0, by simp; linarith⟩
    exact (RHHeight.toNat_analyticOrderAt_eq_one_iff _).mp (hmem _ hρ).2

/-! ## A range `(a, b]` inside a window -/

/-- Hypotheses for the range `(a, b]`: the window list is `pre ++ ords ++ post`. -/
structure RHyp (pre ords post : List ℕ) (a b : ℕ) (L U : ℝ) : Prop where
  hL : L ≤ a
  hU : (b : ℝ) ≤ U
  hord : ∀ m ∈ ords, a * 10 ^ 24 + 10 ^ 5 < m ∧ m + 10 ^ 5 < b * 10 ^ 24
  hpre : ∀ m ∈ pre, m + 10 ^ 5 < a * 10 ^ 24
  hpost : ∀ m ∈ post, b * 10 ^ 24 + 10 ^ 5 < m

section Range

variable {pre ords post : List ℕ} {a b : ℕ} {L U : ℝ} {cL cU : ℕ}
  (W : WHyp (pre ++ ords ++ post) L U cL cU) (R : RHyp pre ords post a b L U)
include W R

theorem mem_ords {s : ℂ} (hz : riemannZeta s = 0) (ha : (a : ℝ) < s.im) (hb : s.im ≤ b) :
    ∃ m ∈ ords, s = ρOf m := by
  obtain ⟨m, hm, rfl⟩ := (wmain W).1 s hz (by linarith [R.hL]) (by linarith [R.hU])
  refine ⟨m, ?_, rfl⟩
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · have := (tOf_bounds (W.hP m (by simp [hm])) (a := a * 10 ^ 24)).2 (R.hpre m hm)
    push_cast at this; simp at ha; norm_num at this; linarith
  · exact hm
  · have := (tOf_bounds (W.hP m (by simp [hm])) (a := b * 10 ^ 24)).1 (R.hpost m hm)
    push_cast at this; simp at hb; norm_num at this; linarith

theorem ords_P {m : ℕ} (hm : m ∈ ords) : P m := W.hP m (by simp [hm])

theorem ords_im {m : ℕ} (hm : m ∈ ords) : (a : ℝ) < tOf m ∧ tOf m < b := by
  obtain ⟨r1, r2⟩ := R.hord m hm
  have b0 := (tOf_bounds (ords_P W R hm) (a := a * 10 ^ 24)).1 r1
  have b1 := (tOf_bounds (ords_P W R hm) (a := b * 10 ^ 24)).2 r2
  push_cast at b0 b1; norm_num at b0 b1
  exact ⟨b0, b1⟩

theorem range_located :
    ∀ s : ℂ, riemannZeta s = 0 → (a : ℝ) < s.im → s.im ≤ b →
      s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
        ∃ m ∈ ords, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 := by
  intro s hz ha hb
  obtain ⟨m, hm, rfl⟩ := mem_ords W R hz ha hb
  exact ⟨by simp, (wmain W).2 m (by simp [hm]), m, hm, by simpa using (tOf_spec (ords_P W R hm)).1⟩

theorem range_unique :
    ∀ m ∈ ords, ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 := by
  intro m hm
  refine ⟨ρOf m, ⟨(tOf_spec (ords_P W R hm)).2, by simpa using (tOf_spec (ords_P W R hm)).1⟩, ?_⟩
  rintro y ⟨hy, hyc⟩
  obtain ⟨r1, r2⟩ := R.hord m hm
  have hyim : (a : ℝ) < y.im ∧ y.im ≤ b := by
    rw [abs_le] at hyc
    have a1 : (a : ℝ) * 10 ^ 24 + 10 ^ 5 < m := by exact_mod_cast r1
    have a2 : (m : ℝ) + 10 ^ 5 < b * 10 ^ 24 := by exact_mod_cast r2
    have q : (1 : ℝ) / 10 ^ 20 < 10 ^ 5 / 10 ^ 24 := by norm_num
    constructor
    · have : ((a : ℝ) * 10 ^ 24 + 10 ^ 5) / 10 ^ 24 < (m : ℝ) / 10 ^ 24 :=
        div_lt_div_of_pos_right a1 (by positivity)
      rw [add_div, mul_div_cancel_right₀ _ (by positivity)] at this
      linarith
    · have : ((m : ℝ) + 10 ^ 5) / 10 ^ 24 < (b : ℝ) * 10 ^ 24 / 10 ^ 24 :=
        div_lt_div_of_pos_right a2 (by positivity)
      rw [add_div, mul_div_cancel_right₀ _ (by positivity)] at this
      linarith
  obtain ⟨m', hm', rfl⟩ := mem_ords W R hy hyim.1 hyim.2
  have := eq_of_close W.hsep (m := m) (m' := m') (by simp [hm]) (by simp [hm']) (by simpa using hyc)
    (tOf_spec (ords_P W R hm')).1
  rw [this]

theorem range_count :
    {s : ℂ | riemannZeta s = 0 ∧ (a : ℝ) < s.im ∧ s.im ≤ b}.ncard = ords.length := by
  classical
  have hset : {s : ℂ | riemannZeta s = 0 ∧ (a : ℝ) < s.im ∧ s.im ≤ b} =
      ((ords.toFinset.image ρOf : Finset ℂ) : Set ℂ) := by
    ext s
    simp only [Set.mem_setOf_eq, Finset.coe_image, List.coe_toFinset, Set.mem_image]
    constructor
    · rintro ⟨hz, ha, hb⟩
      obtain ⟨m, hm, rfl⟩ := mem_ords W R hz ha hb
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨t0, t1⟩ := ords_im W R hm
      exact ⟨(tOf_spec (ords_P W R hm)).2, by simpa using t0, by simpa using t1.le⟩
  have hsep' : Sep ords := (List.pairwise_append.mp (List.pairwise_append.mp W.hsep).1).2.1
  have hnodup : ords.Nodup := hsep'.imp (fun {a b} h => by omega)
  have hinj : Set.InjOn ρOf (ords.toFinset : Set ℕ) := fun x hx y hy h =>
    ρOf_inj hsep' (fun m hm => ords_P W R hm) (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) h
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hnodup]

end Range

end ZetaCert.Window
