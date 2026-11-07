/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Eval.SumsSound

@[expose] public section

/-!
# The Dirichlet sums at `s = σ + it`, `σ = j/q`

* `rootOK_spec`: `x ≈ p^{-1/q}` from below, within one ulp;
* `powPP_spec`: `x^j` by binary powering, one-sided error `(2j - 1)(e + u)`;
* `primeTerm_spec_gen`, `sums_spec_gen`: `primeTerm` and `sums` for a general real part, given
  `|vP w - p^{-σ}| ≤ ew` for every prime datum.
-/

set_option exponentiation.threshold 600

namespace ZetaCert.Eval

open Complex

theorem rootOK_spec {p x q : ℕ} (hp : 0 < p) (hq : 0 < q) (h : rootOK p x q = true) :
    vP x ≤ (p : ℝ) ^ (-(1 / q : ℝ)) ∧ (p : ℝ) ^ (-(1 / q : ℝ)) ≤ vP x + u := by
  unfold rootOK at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set a := (p : ℝ) ^ (-(1 / q : ℝ))
  have ha0 : 0 < a := by positivity
  have haq : a ^ q * p = 1 := by
    simp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpR.le]
    rw [show (-(1 / (q : ℝ)) * q) = -1 by field_simp, Real.rpow_neg_one]
    field_simp
  have h1R : ((x : ℝ)) ^ q * p ≤ (2 ^ 128) ^ q := by
    rw [← pow_mul]; exact_mod_cast h1
  have h2R : ((2 : ℝ) ^ 128) ^ q < ((x : ℝ) + 1) ^ q * p := by
    rw [← pow_mul]; exact_mod_cast h2
  have key1 : (x : ℝ) ≤ 2 ^ 128 * a := by
    by_contra hc; push Not at hc
    have : (2 ^ 128 * a) ^ q < (x : ℝ) ^ q := pow_lt_pow_left₀ hc (by positivity) hq.ne'
    have e : (2 ^ 128 * a) ^ q * (p : ℝ) = (2 ^ 128) ^ q := by rw [mul_pow, mul_assoc, haq, mul_one]
    nlinarith [mul_lt_mul_of_pos_right this hpR]
  have key2 : 2 ^ 128 * a ≤ (x : ℝ) + 1 := by
    by_contra hc; push Not at hc
    have : ((x : ℝ) + 1) ^ q < (2 ^ 128 * a) ^ q := pow_lt_pow_left₀ hc (by positivity) hq.ne'
    have e : (2 ^ 128 * a) ^ q * (p : ℝ) = (2 ^ 128) ^ q := by rw [mul_pow, mul_assoc, haq, mul_one]
    nlinarith [mul_lt_mul_of_pos_right this hpR]
  unfold vP u
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · have : a ≤ ((x : ℝ) + 1) / 2 ^ 128 := by rw [le_div_iff₀ (by positivity)]; linarith
    calc a ≤ ((x : ℝ) + 1) / 2 ^ 128 := this
      _ = (x : ℝ) / 2 ^ 128 + 1 / 2 ^ 128 := by ring

theorem vP_mulPP_le_one {x y : ℕ} (hx : vP x ≤ 1) (hy : vP y ≤ 1) : vP (mulPP x y) ≤ 1 := by
  have := (vP_mulPP x y).2
  have : vP x * vP y ≤ 1 := by nlinarith [vP_nonneg x, vP_nonneg y]
  linarith

/-- **Binary powering.** With `vP x ≤ a ≤ vP x + e`, `a ≤ 1`: for `0 < j < 2^fuel`,
`a^j - (2j - 1)(e + u) ≤ vP (powPP x fuel j) ≤ a^j`. -/
theorem powPP_spec {x : ℕ} {a e : ℝ} (hxa : vP x ≤ a) (hax : a ≤ vP x + e) (ha1 : a ≤ 1) :
    ∀ fuel j : ℕ, 0 < j → j < 2 ^ fuel →
      a ^ j - (2 * j - 1) * (e + u) ≤ vP (powPP x fuel j) ∧ vP (powPP x fuel j) ≤ a ^ j := by
  have hx0 := vP_nonneg x
  have ha0 : 0 ≤ a := hx0.trans hxa
  have he0 : 0 ≤ e := by linarith
  have hu := u_pos
  intro fuel
  induction fuel with
  | zero => intro j hj hj2; simp at hj2; omega
  | succ fuel ih =>
    intro j hj hj2
    set m := j / 2 with hm
    have hm2 : m < 2 ^ fuel := by rw [pow_succ] at hj2; omega
    -- the half power
    have hy : (m = 0 ∧ powPP x fuel m = ONE) ∨
        (0 < m ∧ a ^ m - (2 * m - 1) * (e + u) ≤ vP (powPP x fuel m) ∧ vP (powPP x fuel m) ≤ a ^ m) := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · left; refine ⟨h0, ?_⟩; rw [h0]; cases fuel <;> rfl
      · right; exact ⟨h0, ih m h0 hm2⟩
    have hpow : powPP x (fuel + 1) j =
        if j % 2 = 0 then mulPP (powPP x fuel m) (powPP x fuel m)
        else mulPP (mulPP (powPP x fuel m) (powPP x fuel m)) x := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      show (match (j' + 1) % 2 with
        | 0 => mulPP (powPP x fuel ((j' + 1) / 2)) (powPP x fuel ((j' + 1) / 2))
        | _ => mulPP (mulPP (powPP x fuel ((j' + 1) / 2)) (powPP x fuel ((j' + 1) / 2))) x) = _
      split
      · rename_i h; rw [if_pos h]
      · rename_i h; rw [if_neg h]
    rcases hy with ⟨hm0, hy1⟩ | ⟨hm0, hyl, hyu⟩
    · -- j = 1
      have hj1 : j = 1 := by omega
      subst hj1
      have h1 : (1 : ℕ) % 2 ≠ 0 := by norm_num
      rw [hpow, if_neg h1, hm0, hy1]
      have hO : mulPP ONE ONE = ONE := by unfold mulPP ONE; norm_num
      have hOx : mulPP ONE x = x := by
        show (ONE * x) >>> 128 = x
        rw [Nat.shiftRight_eq_div_pow, ONE_eq, Nat.mul_div_cancel_left _ (by positivity)]
      rw [hO, hOx]; simp; constructor <;> linarith
    · set y := powPP x fuel m
      have hy0 := vP_nonneg y
      have hya : vP y ≤ 1 := hyu.trans (pow_le_one₀ ha0 ha1)
      obtain ⟨s1, s2⟩ := vP_mulPP y y
      have ham : a ^ m ≤ 1 := pow_le_one₀ ha0 ha1
      have ham0 : 0 ≤ a ^ m := pow_nonneg ha0 m
      set B := (2 * (m : ℝ) - 1) * (e + u)
      have hB0 : 0 ≤ B := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        simp only [B]; nlinarith
      -- `y² ≥ a^{2m} - 2B`
      have hsq : a ^ (2 * m) - 2 * B ≤ vP y * vP y := by
        rw [pow_mul', sq]
        rcases le_or_gt (a ^ m) B with h | h
        · nlinarith
        · have : a ^ m - B ≤ vP y := hyl
          have : (a ^ m - B) * (a ^ m - B) ≤ vP y * vP y := mul_self_le_mul_self (by linarith) this
          nlinarith
      have hsq' : vP y * vP y ≤ a ^ (2 * m) := by
        rw [pow_mul', sq]; exact mul_self_le_mul_self hy0 hyu
      rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hjm : j = 2 * m := by omega
        have h0 : j % 2 = 0 := by omega
        rw [hpow, if_pos h0, hjm]
        constructor
        · have : (2 * ((2 * m : ℕ) : ℝ) - 1) * (e + u) = 2 * B + (e + u) := by
            simp only [B]; push_cast; ring
          rw [this]; linarith
        · linarith
      · have hjm : j = 2 * m + 1 := by omega
        have h1 : j % 2 ≠ 0 := by omega
        rw [hpow, if_neg h1, hjm]
        obtain ⟨t1, t2⟩ := vP_mulPP (mulPP y y) x
        have hy2 := vP_nonneg (mulPP y y)
        have hy21 : vP (mulPP y y) ≤ 1 := vP_mulPP_le_one hya hya
        have hp1 : a ^ (2 * m + 1) = a ^ (2 * m) * a := pow_succ _ _
        constructor
        · -- vP(mulPP (y y) x) ≥ (y² - u)(a - e) - u ≥ a^{2m+1} - (2B + u) - e - u
          have hlow : (a ^ (2 * m) - 2 * B - u) * a - e ≤ vP (mulPP y y) * vP x := by
            have hxe : a - e ≤ vP x := by linarith
            rcases le_or_gt (a ^ (2 * m) - 2 * B - u) 0 with h | h
            · nlinarith [mul_nonneg hy2 hx0]
            · rcases le_or_gt (a - e) 0 with h' | h'
              · have hA1 : a ^ (2 * m) - 2 * B - u ≤ 1 := by
                  have : a ^ (2 * m) ≤ 1 := pow_le_one₀ ha0 ha1
                  linarith
                have : (a ^ (2 * m) - 2 * B - u) * a ≤ a := by nlinarith
                nlinarith [mul_nonneg hy2 hx0]
              · have := mul_le_mul (show a ^ (2 * m) - 2 * B - u ≤ vP (mulPP y y) by linarith) hxe
                  h'.le hy2
                nlinarith
          have : (2 * ((2 * m + 1 : ℕ) : ℝ) - 1) * (e + u) = 2 * B + 3 * (e + u) := by
            simp only [B]; push_cast; ring
          rw [this, hp1]
          have : a ^ (2 * m) * a - (2 * B + u) * a ≥ a ^ (2 * m) * a - (2 * B + u) := by nlinarith
          nlinarith
        · rw [hp1]
          have : vP (mulPP y y) * vP x ≤ a ^ (2 * m) * a :=
            mul_le_mul (s2.trans hsq') hxa hx0 (pow_nonneg ha0 _)
          linarith

/-! ## General real part -/

/-- The error of one prime term at real part `σ`, with `|w - p^{-σ}| ≤ ew`. -/
noncomputable def EpG (K : ℕ) (t δL ew : ℝ) : ℝ := 2 ^ (K + 1) * (77 * u) + 2 * (t * δL) + ew + 2 * u

theorem cpow_neg_gen {p : ℕ} (hp : 0 < p) (σ t : ℝ) :
    (p : ℂ) ^ (-((σ : ℂ) + t * I)) =
      (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * cexp (-I * ((t * Real.log p : ℝ) : ℂ)) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp', Complex.ofReal_cpow (by positivity),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  rw [← Complex.exp_add]; congr 1
  rw [show ((p : ℝ) : ℂ) = (p : ℂ) by push_cast; rfl, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (by positivity)]
  push_cast; ring

theorem primeTerm_spec_gen {K T w L p : ℕ} {t δL σ ew : ℝ} (hp : 0 < p)
    (hw : |vP w - (p : ℝ) ^ (-σ)| ≤ ew) (hw1 : vP w ≤ 1)
    (hT : vP T = t) (hL : |vP L - Real.log p| ≤ δL)
    (hx : halfArg K T L ≤ EIGHTH) (hK : K ≤ 40) (hδ : t * δL ≤ 1 / 2 ^ 42) :
    ‖cv (primeTerm K T w L).1 (primeTerm K T w L).2 - (p : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤
      EpG K t δL ew := by
  have ht0 : 0 ≤ t := hT ▸ vP_nonneg T
  have hθ : |vP T * vP L - t * Real.log p| ≤ t * δL := by
    rw [hT, ← mul_sub, abs_mul, abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_left hL ht0
  have he := expNegI_spec (θ := t * Real.log p) hθ hx hK hδ
  set c := expNegI K T L
  set E := 2 ^ (K + 1) * (77 * u) + 2 * (t * δL)
  set r := (p : ℝ) ^ (-σ)
  have hz : ‖cexp (-I * ((t * Real.log p : ℝ) : ℂ))‖ = 1 := by
    rw [show -I * ((t * Real.log p : ℝ) : ℂ) = ((-(t * Real.log p)) : ℝ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hE1 : E ≤ 1 := by
    have h2K : (2 : ℝ) ^ (K + 1) ≤ 2 ^ 41 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : 2 ^ (K + 1) * (77 * u) ≤ 2 ^ 41 * (77 * u) := by gcongr; linarith [u_pos]
    have : 2 ^ 41 * (77 * u) + 2 * (1 / 2 ^ 42) ≤ (1 : ℝ) := by unfold u; norm_num
    simp only [E]; linarith
  have hcn : ‖cv c.1 c.2‖ ≤ 2 := by
    have := norm_sub_norm_le (cv c.1 c.2) (cexp (-I * ((t * Real.log p : ℝ) : ℂ))); linarith
  have hm := mulOP_pair_spec (a := c.1) (b := c.2) (w := w)
    ((Complex.abs_re_le_norm _).trans hcn) ((Complex.abs_im_le_norm _).trans hcn) hw1
  rw [cpow_neg_gen hp σ t]
  unfold primeTerm
  simp only
  set z := cexp (-I * ((t * Real.log p : ℝ) : ℂ))
  have e : cv (mulOP c.1 w) (mulOP c.2 w) - (r : ℂ) * z =
      (cv (mulOP c.1 w) (mulOP c.2 w) - (vP w : ℂ) * cv c.1 c.2) + (vP w : ℂ) * (cv c.1 c.2 - z)
        + ((vP w - r : ℝ) : ℂ) * z := by push_cast; ring
  rw [e]
  have n1 := norm_add_le ((cv (mulOP c.1 w) (mulOP c.2 w) - (vP w : ℂ) * cv c.1 c.2) +
    (vP w : ℂ) * (cv c.1 c.2 - z)) (((vP w - r : ℝ) : ℂ) * z)
  have n2 := norm_add_le (cv (mulOP c.1 w) (mulOP c.2 w) - (vP w : ℂ) * cv c.1 c.2)
    ((vP w : ℂ) * (cv c.1 c.2 - z))
  have n3 : ‖(vP w : ℂ) * (cv c.1 c.2 - z)‖ ≤ E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vP_nonneg w)]
    calc vP w * ‖cv c.1 c.2 - z‖ ≤ 1 * E := mul_le_mul hw1 he (norm_nonneg _) (by norm_num)
      _ = E := one_mul _
  have n4 : ‖((vP w - r : ℝ) : ℂ) * z‖ ≤ ew := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hw
  unfold EpG
  linarith

theorem primeTerms_ok_gen {K T : ℕ} {t δL σ ew : ℝ} (hσ : 0 ≤ σ) (hT : vP T = t) (hK : K ≤ 40)
    (hδ : t * δL ≤ 1 / 2 ^ 42) (hew : ew ≤ 1 / 2 ^ 60) :
    ∀ data : List (Nat × Nat × Nat),
      (∀ d ∈ data, 2 ≤ d.1 ∧ |vP d.2.1 - (d.1 : ℝ) ^ (-σ)| ≤ ew ∧ vP d.2.1 ≤ 1) →
      LogOK δL data → smallArgs K T data = true →
      PrimesOK ((σ : ℂ) + t * I) (EpG K t δL ew) δL (primeTerms K T data) := by
  intro data
  induction data with
  | nil => intro _ _ _ q hq; simp [primeTerms] at hq
  | cons d ds ih =>
    obtain ⟨p, w, L⟩ := d
    intro hd hl hsm q hq
    simp only [smallArgs, Bool.and_eq_true, Nat.ble_eq] at hsm
    simp only [primeTerms, force_eq, List.mem_cons] at hq
    rcases hq with rfl | hq
    · obtain ⟨h2, hw, hw1⟩ := hd (p, w, L) (List.mem_cons_self ..)
      have hL := hl (p, w, L) (List.mem_cons_self ..)
      refine ⟨h2, ?_, hL⟩
      exact primeTerm_spec_gen (lt_of_lt_of_le (by norm_num) h2) hw hw1 hT hL hsm.1 hK hδ
    · exact ih (fun d hd' => hd d (List.mem_cons_of_mem _ hd')) (fun d hd' => hl d (List.mem_cons_of_mem _ hd'))
        hsm.2 q hq

set_option maxRecDepth 20000 in
/-- **The Dirichlet sums at `s = σ + it`.** -/
theorem sums_spec_gen {N K T fuel Dp : ℕ} {data : List (Nat × Nat × Nat)} {t δL Λ σ ew : ℝ}
    (hσ : 0 ≤ σ) (hσ0 : 0 < σ)
    (hT : vP T = t) (hK : K ≤ 40) (hδ : t * δL ≤ 1 / 2 ^ 42) (hδL : 0 ≤ δL)
    (hdat : ∀ d ∈ data, 2 ≤ d.1 ∧ |vP d.2.1 - (d.1 : ℝ) ^ (-σ)| ≤ ew ∧ vP d.2.1 ≤ 1) (hew : ew ≤ 1 / 2 ^ 60)
    (hew0 : 0 ≤ ew) (hl : LogOK δL data) (hsm : smallArgs K T data = true)
    (hen : enumOK N fuel (data.map Prod.fst) = true) (hN1 : 1 ≤ N) (hN20 : N ≤ 2 ^ 20)
    (hN : N < 2 ^ Dp) (hsmall : (Dp : ℝ) * (EpG K t δL ew + 4 * u) * EpG K t δL ew ≤ u)
    (hsmall1 : (Dp : ℝ) * (EpG K t δL ew + 4 * u) ≤ 1)
    (hΛ : Real.log N + Dp * δL ≤ Λ) (hΛ1 : Λ ≤ 2 ^ 20) :
    let a := sums N K T fuel data
    ‖accS a - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ (σ + t * I)‖ ≤
        N * (Dp * (EpG K t δL ew + 4 * u)) ∧
    ‖accD a - ∑ n ∈ Finset.range (N + 1), -Complex.log n * (n : ℂ) ^ (-(σ + t * I))‖ ≤
        N * (Λ * (Dp * (EpG K t δL ew + 4 * u)) + Dp * δL + 2 * u) := by
  intro a
  set s : ℂ := σ + t * I
  have hs : 0 ≤ s.re := by simp [s]; exact hσ
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [s] at this; linarith
  have hu := u_pos
  have hEp1 : EpG K t δL ew ≤ 1 := by
    have h2K : (2 : ℝ) ^ (K + 1) ≤ 2 ^ 41 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : 2 ^ (K + 1) * (77 * u) ≤ 2 ^ 41 * (77 * u) := by gcongr <;> linarith
    have : 2 ^ 41 * (77 * u) + 2 * (1 / 2 ^ 42) + 1 / 2 ^ 60 + 2 * u ≤ (1 : ℝ) := by unfold u; norm_num
    unfold EpG; linarith
  have hok := primeTerms_ok_gen hσ hT hK hδ hew data hdat hl hsm
  have hperm := enumOK_spec hen
  rw [← primeTerms_p K T data] at hperm
  set ns := goNs N fuel ((primeTerms K T data).map PT.p) 1
  have hlen : ns.length = N - 1 := by rw [hperm.length_eq]; simp
  have hlenR : (ns.length : ℝ) ≤ N := by rw [hlen]; exact_mod_cast Nat.sub_le N 1
  have hNR : (N : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hN20
  have h1 : ‖cv (Nat.add ONE O) O - ((1 : ℕ) : ℂ) ^ (-s)‖ ≤ (0 : ℕ) * (EpG K t δL ew + 4 * u) := by
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
  obtain ⟨g1, g2, -, -⟩ := go_spec N s hs (EpG K t δL ew) δL Λ Dp hN hEp1 hδL hsmall hsmall1 hΛ hΛ1 fuel
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
  have hE0 : 0 ≤ (Dp : ℝ) * (EpG K t δL ew + 4 * u) := by
    have : 0 ≤ EpG K t δL ew := by
      unfold EpG; have : 0 ≤ t := hT ▸ vP_nonneg T
      positivity
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
