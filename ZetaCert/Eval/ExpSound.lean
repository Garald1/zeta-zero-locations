/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Eval.CoreSound

@[expose] public section

/-!
# Soundness of `taylorI`, `sqIter` and `expNegI`

* `taylorI_spec`: the Taylor loop at a plain `x` with `a = vP x ≤ 1/8` returns a pair whose
  complex value is within `3u · n` of `Σ_{m<n} (-ia)^m/m!` (`n` terms).
* `sqIter_spec`: `k` squarings of an approximation of `ẑ` with `‖ẑ‖ = 1` amplify the error
  from `E` to at most `2^k (E + 3u)(1 + k η) - 3u`.
* `expNegI_spec`: `e^{-iθ}` from `T`, `L` with `|vP T · vP L - θ| ≤ δ`.
-/

set_option exponentiation.threshold 600

namespace ZetaCert.Eval

open Complex

/-- Complex value of a pair of offset numbers. -/
noncomputable def cv (a b : ℕ) : ℂ := ⟨vO a, vO b⟩

theorem cv_re (a b : ℕ) : (cv a b).re = vO a := rfl
theorem cv_im (a b : ℕ) : (cv a b).im = vO b := rfl

theorem vP_add (x y : ℕ) : vP (x + y) = vP x + vP y := by unfold vP; push_cast; ring

theorem vP_mono {x y : ℕ} (h : x ≤ y) : vP x ≤ vP y := by
  unfold vP; gcongr

/-- The Taylor partial sum of `e^{-ia}`. -/
noncomputable def tpart (a : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ Finset.range j, (-I * a) ^ m / m.factorial

theorem tpart_succ (a : ℝ) (j : ℕ) :
    tpart a (j + 1) = tpart a j + (-I) ^ j * ((a ^ j / j.factorial : ℝ) : ℂ) := by
  unfold tpart; rw [Finset.sum_range_succ, mul_pow]; push_cast; ring

theorem negI_pow (j : ℕ) : (-I) ^ j = (-I) ^ (j % 4) := by
  conv_lhs => rw [← Nat.div_add_mod j 4, pow_add, pow_mul]
  have : (-I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
  rw [this, one_pow, one_mul]

/-- The accumulator value. -/
noncomputable def accv (rp rn ip im : ℕ) : ℂ :=
  ((vP rp - vP rn : ℝ) : ℂ) + ((vP ip - vP im : ℝ) : ℂ) * I

/-- Invariant of the Taylor loop at index `j`. -/
def TInv (a : ℝ) (j t rp rn ip im : ℕ) : Prop :=
  |vP t - a ^ j / j.factorial| ≤ 3 * u ∧
  ‖accv rp rn ip im - tpart a j‖ ≤ 3 * u * j ∧
  vP rp + vP rn + vP ip + vP im ≤ 8 / 7 * (1 - (1 / 8) ^ j) + 3 * u * j

theorem TInv_zero (a : ℝ) : TInv a 0 ONE 0 0 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vP_ONE]; simp; linarith [u_pos]
  · simp [accv, tpart, vP]
  · simp [vP]

/-- The next Taylor term is within `3u` of `a^{j+1}/(j+1)!`. -/
theorem next_term {x t j : ℕ} {a : ℝ} (ha : vP x = a) (ha0 : 0 ≤ a) (ha8 : a ≤ 1 / 8)
    (ht : |vP t - a ^ j / j.factorial| ≤ 3 * u) :
    |vP (Nat.div (mulPP t x) (Nat.add j 1)) - a ^ (j + 1) / (j + 1).factorial| ≤ 3 * u := by
  have hj : 0 < j + 1 := Nat.succ_pos j
  obtain ⟨m1, m2⟩ := vP_mulPP t x
  obtain ⟨d1, d2⟩ := vP_div (mulPP t x) hj
  rw [ha] at m1 m2
  have hjR : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast hj
  have hjR0 : (0 : ℝ) < (j + 1 : ℕ) := by linarith
  set q := vP (Nat.div (mulPP t x) (Nat.add j 1))
  have hq : q = vP (mulPP t x / (j + 1)) := rfl
  rw [← hq] at d1 d2
  have hfac : a ^ (j + 1) / ((j + 1).factorial : ℝ) = a ^ j / j.factorial * a / (j + 1 : ℕ) := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  rw [hfac]
  set b := a ^ j / (j.factorial : ℝ)
  have hu := u_pos
  rw [abs_le] at ht ⊢
  obtain ⟨ht1, ht2⟩ := ht
  constructor
  · -- q > (vP t * a - u)/(j+1) - u ≥ (b - 3u) a/(j+1) - u/(j+1) - u
    have h1 : (vP t * a - u) / (j + 1 : ℕ) - u < q := by
      have := div_le_div_of_nonneg_right m1.le hjR0.le
      linarith
    have h2 : ((b - 3 * u) * a - u) / (j + 1 : ℕ) - u ≤ (vP t * a - u) / (j + 1 : ℕ) - u := by
      have : (b - 3 * u) * a - u ≤ vP t * a - u := by nlinarith
      linarith [div_le_div_of_nonneg_right this hjR0.le]
    have h3 : (3 * u * a + u) / (j + 1 : ℕ) + u ≤ 3 * u := by
      have e1 : (3 * u * a + u) / (j + 1 : ℕ) ≤ 3 * u * a + u := div_le_self (by positivity) hjR
      nlinarith
    have e : ((b - 3 * u) * a - u) / (j + 1 : ℕ) = b * a / (j + 1 : ℕ) - (3 * u * a + u) / (j + 1 : ℕ) := by ring
    linarith
  · have h1 : q ≤ vP t * a / (j + 1 : ℕ) := d2.trans (div_le_div_of_nonneg_right m2 hjR0.le)
    have h2 : vP t * a / (j + 1 : ℕ) ≤ (b + 3 * u) * a / (j + 1 : ℕ) := by
      apply div_le_div_of_nonneg_right _ hjR0.le; nlinarith
    have h3 : 3 * u * a / (j + 1 : ℕ) ≤ 3 * u := by
      have e1 : 3 * u * a / (j + 1 : ℕ) ≤ 3 * u * a := div_le_self (by positivity) hjR
      nlinarith
    have e : (b + 3 * u) * a / (j + 1 : ℕ) = b * a / (j + 1 : ℕ) + 3 * u * a / (j + 1 : ℕ) := by ring
    linarith

/-- Bound on the current term from the invariant. -/
theorem term_le {t j : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha8 : a ≤ 1 / 8)
    (ht : |vP t - a ^ j / j.factorial| ≤ 3 * u) : vP t ≤ (1 / 8) ^ j + 3 * u := by
  have h1 : a ^ j / (j.factorial : ℝ) ≤ (1 / 8) ^ j := by
    have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
    calc a ^ j / (j.factorial : ℝ) ≤ a ^ j := div_le_self (by positivity) hf
      _ ≤ (1 / 8) ^ j := pow_le_pow_left₀ ha0 ha8 j
  have := (abs_le.mp ht).2
  linarith

theorem tot_step {j : ℕ} {S v : ℝ} (hS : S ≤ 8 / 7 * (1 - (1 / 8) ^ j) + 3 * u * j)
    (hv : v ≤ (1 / 8) ^ j + 3 * u) :
    S + v ≤ 8 / 7 * (1 - (1 / 8) ^ (j + 1)) + 3 * u * ((j + 1 : ℕ) : ℝ) := by
  push_cast; rw [pow_succ]; nlinarith

/-- One step of the Taylor loop preserves the invariant (the four residues of `j mod 4`). -/
theorem TInv_step {x : ℕ} {a : ℝ} (ha : vP x = a) (ha0 : 0 ≤ a) (ha8 : a ≤ 1 / 8)
    {j t rp rn ip im : ℕ} (hI : TInv a j t rp rn ip im) :
    let t' := Nat.div (mulPP t x) (Nat.add j 1)
    (j % 4 = 0 → TInv a (j + 1) t' (Nat.add rp t) rn ip im) ∧
    (j % 4 = 1 → TInv a (j + 1) t' rp rn ip (Nat.add im t)) ∧
    (j % 4 = 2 → TInv a (j + 1) t' rp (Nat.add rn t) ip im) ∧
    (j % 4 = 3 → TInv a (j + 1) t' rp rn (Nat.add ip t) im) := by
  obtain ⟨ht, hacc, htot⟩ := hI
  have hnext := next_term ha ha0 ha8 ht
  have hv := term_le ha0 ha8 ht
  have hsucc : (3 : ℝ) * u * ((j + 1 : ℕ) : ℝ) = 3 * u * j + 3 * u := by push_cast; ring
  have key : ∀ A : ℂ, A = accv rp rn ip im + (-I) ^ j * (vP t : ℂ) →
      ‖A - tpart a (j + 1)‖ ≤ 3 * u * ((j + 1 : ℕ) : ℝ) := by
    intro A hA
    rw [hA, tpart_succ, hsucc]
    have e : accv rp rn ip im + (-I) ^ j * (vP t : ℂ) - (tpart a j + (-I) ^ j * ((a ^ j / j.factorial : ℝ) : ℂ))
        = (accv rp rn ip im - tpart a j) + (-I) ^ j * (((vP t - a ^ j / j.factorial : ℝ)) : ℂ) := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow, norm_neg, norm_I, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    linarith
  refine ⟨fun h => ⟨hnext, key _ ?_, ?_⟩, fun h => ⟨hnext, key _ ?_, ?_⟩,
    fun h => ⟨hnext, key _ ?_, ?_⟩, fun h => ⟨hnext, key _ ?_, ?_⟩⟩
  · rw [negI_pow, h]; unfold accv; rw [show Nat.add rp t = rp + t from rfl, vP_add]; push_cast; ring
  · rw [show Nat.add rp t = rp + t from rfl, vP_add]
    have := tot_step htot hv; linarith
  · rw [negI_pow, h]; unfold accv; rw [show Nat.add im t = im + t from rfl, vP_add]; push_cast; ring
  · rw [show Nat.add im t = im + t from rfl, vP_add]
    have := tot_step htot hv; linarith
  · rw [negI_pow, h]; unfold accv; rw [show Nat.add rn t = rn + t from rfl, vP_add]; push_cast
    rw [show (-I) ^ 2 = -1 by rw [neg_pow_two, I_sq]]; ring
  · rw [show Nat.add rn t = rn + t from rfl, vP_add]
    have := tot_step htot hv; linarith
  · rw [negI_pow, h]; unfold accv; rw [show Nat.add ip t = ip + t from rfl, vP_add]; push_cast
    rw [show (-I) ^ 3 = I by rw [pow_succ, neg_pow_two, I_sq]; ring]; ring
  · rw [show Nat.add ip t = ip + t from rfl, vP_add]
    have := tot_step htot hv; linarith

/-- The Taylor loop: after `fuel` more steps from an invariant state at index `j`. -/
theorem taylorI_spec {x : ℕ} {a : ℝ} (ha : vP x = a) (ha0 : 0 ≤ a) (ha8 : a ≤ 1 / 8)
    (hu : 3 * u * 64 ≤ 1 / 8) :
    ∀ (fuel j t rp rn ip im : ℕ), j + fuel ≤ 64 → TInv a j t rp rn ip im →
      let r := taylorI x fuel j t rp rn ip im
      ‖cv r.1 r.2 - tpart a (j + fuel)‖ ≤ 3 * u * (j + fuel : ℕ) ∧
        |vO r.1| ≤ 2 ∧ |vO r.2| ≤ 2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro j t rp rn ip im hj hI
    obtain ⟨-, hacc, htot⟩ := hI
    have hjR : (j : ℝ) ≤ 64 := by exact_mod_cast (by omega : j ≤ 64)
    have hpos : 0 ≤ (1 / 8 : ℝ) ^ j := by positivity
    have hsmall : 3 * u * j ≤ 1 / 8 := by nlinarith [u_pos]
    have hrp := vP_nonneg rp; have hrn := vP_nonneg rn
    have hip := vP_nonneg ip; have him := vP_nonneg im
    -- the final subtractions do not truncate
    have hsub : ∀ p n : ℕ, vP p + vP n ≤ 2 → vO (Nat.sub (Nat.add p O) n) = vP p - vP n := by
      intro p n hpn
      apply vO_eq_of_cast
      have hn : ((n : ℕ) : ℝ) ≤ ((p + O : ℕ) : ℝ) := by
        rw [O_eq]; push_cast; rw [cast_eq_vP n, cast_eq_vP p]
        nlinarith [vP_nonneg p, vP_nonneg n]
      show ((p + O - n : ℕ) : ℝ) = _
      have : n ≤ p + O := by exact_mod_cast hn
      push_cast [this]; rw [O_eq, cast_eq_vP n, cast_eq_vP p]; push_cast; ring
    have h1 : vP rp + vP rn ≤ 2 := by nlinarith
    have h2 : vP ip + vP im ≤ 2 := by nlinarith
    show ‖cv (Nat.sub (Nat.add rp O) rn) (Nat.sub (Nat.add ip O) im) - tpart a j‖ ≤ 3 * u * j ∧
      |vO (Nat.sub (Nat.add rp O) rn)| ≤ 2 ∧ |vO (Nat.sub (Nat.add ip O) im)| ≤ 2
    rw [hsub rp rn h1, hsub ip im h2]
    refine ⟨?_, ?_, ?_⟩
    · have : cv (Nat.sub (Nat.add rp O) rn) (Nat.sub (Nat.add ip O) im) = accv rp rn ip im := by
        apply Complex.ext
        · rw [cv_re, hsub rp rn h1]; simp [accv]
        · rw [cv_im, hsub ip im h2]; simp [accv]
      rw [this]; exact hacc
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  | succ n ih =>
    intro j t rp rn ip im hj hI
    have hstep := TInv_step ha ha0 ha8 hI
    have hj' : j + 1 + n ≤ 64 := by omega
    have e : j + (n + 1) = j + 1 + n := by omega
    simp only [taylorI, force_eq]
    rw [e]
    rcases (by omega : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3) with h | h | h | h
    · rw [show Nat.mod j 4 = 0 from h]; exact ih _ _ _ _ _ _ hj' (hstep.1 h)
    · rw [show Nat.mod j 4 = 1 from h]; exact ih _ _ _ _ _ _ hj' (hstep.2.1 h)
    · rw [show Nat.mod j 4 = 2 from h]; exact ih _ _ _ _ _ _ hj' (hstep.2.2.1 h)
    · rw [show Nat.mod j 4 = 3 from h]; exact ih _ _ _ _ _ _ hj' (hstep.2.2.2 h)

end ZetaCert.Eval

namespace ZetaCert.Eval

open Complex

theorem norm_le_of_parts {z : ℂ} {a b : ℝ} (ha : |z.re| ≤ a) (hb : |z.im| ≤ b) : ‖z‖ ≤ a + b :=
  (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add ha hb)

/-- One complex squaring: error `e ↦ 2e + e² + 3u` around a target of norm at most `1`. -/
theorem csq_spec {a b : ℕ} {z : ℂ} {e : ℝ} (hz : ‖z‖ ≤ 1) (he : ‖cv a b - z‖ ≤ e) (he1 : e ≤ 1) :
    ‖cv (subO (mulO a a) (mulO b b)) (addO (mulO a b) (mulO a b)) - z ^ 2‖ ≤ 2 * e + e ^ 2 + 3 * u := by
  have hn : ‖cv a b‖ ≤ 2 := by
    have := norm_sub_norm_le (cv a b) z; linarith
  have ha : |vO a| ≤ 2 := (Complex.abs_re_le_norm (cv a b)).trans hn
  have hb : |vO b| ≤ 2 := (Complex.abs_im_le_norm (cv a b)).trans hn
  rw [abs_le] at ha hb
  have hu := u_pos
  have hu1 : u ≤ 1 := by unfold u; rw [div_le_one (by positivity)]; norm_num
  obtain ⟨aa1, aa2⟩ := vO_mulO (X := a) (Y := a) (by nlinarith)
  obtain ⟨bb1, bb2⟩ := vO_mulO (X := b) (Y := b) (by nlinarith)
  obtain ⟨ab1, ab2⟩ := vO_mulO (X := a) (Y := b) (by nlinarith)
  have hre : vO (subO (mulO a a) (mulO b b)) = vO (mulO a a) - vO (mulO b b) :=
    vO_subO (by nlinarith)
  have him : vO (addO (mulO a b) (mulO a b)) = vO (mulO a b) + vO (mulO a b) :=
    vO_addO (by nlinarith)
  have hsq : (cv a b) ^ 2 = ⟨vO a * vO a - vO b * vO b, 2 * (vO a * vO b)⟩ := by
    apply Complex.ext <;> simp [cv, pow_two] <;> ring
  have h1 : ‖cv (subO (mulO a a) (mulO b b)) (addO (mulO a b) (mulO a b)) - (cv a b) ^ 2‖ ≤ 3 * u := by
    rw [hsq]
    have : 3 * u = u + 2 * u := by ring
    rw [this]
    apply norm_le_of_parts
    · simp only [Complex.sub_re, cv_re, hre]; rw [abs_le]; constructor <;> linarith
    · simp only [Complex.sub_im, cv_im, him]; rw [abs_le]; constructor <;> linarith
  have h2 : ‖(cv a b) ^ 2 - z ^ 2‖ ≤ 2 * e + e ^ 2 := by
    have e1 : (cv a b) ^ 2 - z ^ 2 = (cv a b - z) * ((cv a b - z) + 2 * z) := by ring
    rw [e1, norm_mul]
    have : ‖(cv a b - z) + 2 * z‖ ≤ e + 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]; simp; linarith
    calc ‖cv a b - z‖ * ‖(cv a b - z) + 2 * z‖ ≤ e * (e + 2) :=
          mul_le_mul he this (norm_nonneg _) ((norm_nonneg _).trans he)
      _ = 2 * e + e ^ 2 := by ring
  calc _ ≤ ‖cv (subO (mulO a a) (mulO b b)) (addO (mulO a b) (mulO a b)) - (cv a b) ^ 2‖
        + ‖(cv a b) ^ 2 - z ^ 2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- `η = 2^-40`, the smallness parameter of the squaring bound. -/
noncomputable def η : ℝ := 1 / 2 ^ 40

theorem η_pos : 0 < η := by unfold η; positivity

/-- `k` squarings. -/
theorem sqIter_spec (k : ℕ) : ∀ (a b : ℕ) (z : ℂ) (E : ℝ), ‖z‖ = 1 → ‖cv a b - z‖ ≤ E →
    2 ^ k * (E + 3 * u) * (1 + k * η) ≤ η → (k : ℝ) * η ≤ 1 →
    ‖cv (sqIter k a b).1 (sqIter k a b).2 - z ^ (2 ^ k)‖ ≤
      2 ^ k * (E + 3 * u) * (1 + k * η) - 3 * u := by
  induction k with
  | zero =>
    intro a b z E _ hE _ _
    simp only [sqIter, pow_zero, pow_one, one_mul, Nat.cast_zero, zero_mul, add_zero, mul_one]
    linarith
  | succ k ih =>
    intro a b z E hz hE hsmall hk
    have hu := u_pos
    have hη := η_pos
    have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
    have hkη : (k : ℝ) * η ≤ 1 := by push_cast at hk; nlinarith
    have hpow : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hEη : E ≤ η := by
      have : E + 3 * u ≤ 2 ^ (k + 1) * (E + 3 * u) * (1 + ((k + 1 : ℕ) : ℝ) * η) := by
        have h1 : (1 : ℝ) ≤ 1 + ((k + 1 : ℕ) : ℝ) * η := by
          have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * η := by positivity
          linarith
        have hAB : (1 : ℝ) ≤ 2 ^ (k + 1) * (1 + ((k + 1 : ℕ) : ℝ) * η) :=
          one_le_mul_of_one_le_of_one_le hpow h1
        have hE3 : 0 ≤ E + 3 * u := by linarith
        calc E + 3 * u = (E + 3 * u) * 1 := (mul_one _).symm
          _ ≤ (E + 3 * u) * (2 ^ (k + 1) * (1 + ((k + 1 : ℕ) : ℝ) * η)) :=
            mul_le_mul_of_nonneg_left hAB hE3
          _ = _ := by ring
      linarith
    have hη1 : η ≤ 1 := by unfold η; rw [div_le_one (by positivity)]; norm_num
    have hsq := csq_spec (a := a) (b := b) (z := z) (e := E) hz.le hE (hEη.trans hη1)
    simp only [sqIter, force_eq]
    set E' := 2 * E + E ^ 2 + 3 * u
    have hz2 : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
    have key : 2 ^ k * (E' + 3 * u) * (1 + k * η) ≤
        2 ^ (k + 1) * (E + 3 * u) * (1 + ((k + 1 : ℕ) : ℝ) * η) := by
      have e1 : E' + 3 * u = 2 * (E + 3 * u) + E ^ 2 := by ring
      rw [e1, pow_succ (2 : ℝ) k]
      push_cast
      have hE2 : E ^ 2 * (1 + k * η) ≤ 2 * (E + 3 * u) * η := by nlinarith
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      have hin : (2 * (E + 3 * u) + E ^ 2) * (1 + k * η) ≤ 2 * (E + 3 * u) * (1 + (k + 1) * η) := by
        nlinarith
      calc (2 : ℝ) ^ k * (2 * (E + 3 * u) + E ^ 2) * (1 + k * η)
          = 2 ^ k * ((2 * (E + 3 * u) + E ^ 2) * (1 + k * η)) := by ring
        _ ≤ 2 ^ k * (2 * (E + 3 * u) * (1 + (k + 1) * η)) := mul_le_mul_of_nonneg_left hin h2k.le
        _ = _ := by ring
    have := ih _ _ (z ^ 2) E' hz2 hsq (key.trans hsmall) hkη
    rw [← pow_mul, ← pow_succ'] at this
    exact this.trans (by linarith)

end ZetaCert.Eval

namespace ZetaCert.Eval

open Complex

theorem norm_cexp_negI_sub (a b : ℝ) :
    ‖cexp (-I * a) - cexp (-I * b)‖ ≤ |a - b| := by
  have e : cexp (-I * a) - cexp (-I * b) = cexp (-I * b) * (cexp (I * ((b - a : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul]
  have h1 : ‖cexp (-I * b)‖ = 1 := by
    rw [show -I * (b : ℂ) = ((-b : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_sub_comm]

theorem exp_tail_24 {a : ℝ} (ha0 : 0 ≤ a) (ha8 : a ≤ 1 / 8) :
    ‖cexp (-I * a) - tpart a 24‖ ≤ u := by
  have hn : ‖-I * (a : ℂ)‖ = a := by
    rw [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  have h := Complex.exp_bound (x := -I * a) (by rw [hn]; linarith) (n := 24) (by norm_num)
  rw [hn] at h
  unfold tpart
  refine h.trans ?_
  have : a ^ 24 ≤ (1 / 8) ^ 24 := pow_le_pow_left₀ ha0 ha8 24
  calc a ^ 24 * ((Nat.succ 24 : ℕ) * ((Nat.factorial 24 : ℕ) * (24 : ℕ) : ℝ)⁻¹)
      ≤ (1 / 8) ^ 24 * ((Nat.succ 24 : ℕ) * ((Nat.factorial 24 : ℕ) * (24 : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ ≤ u := by unfold u; norm_num [Nat.factorial]

/-- The Taylor value at the halved argument is within `74u + δ/2^K` of `e^{-iθ/2^K}`. -/
theorem taylor_halved {K T L : ℕ} {θ δ : ℝ} (hθ : |vP T * vP L - θ| ≤ δ)
    (hx : halfArg K T L ≤ EIGHTH) :
    let cs := taylorI (halfArg K T L) nTaylor 0 ONE 0 0 0 0
    ‖cv cs.1 cs.2 - cexp (-I * ((θ / 2 ^ K : ℝ) : ℂ))‖ ≤ 74 * u + δ / 2 ^ K := by
  intro cs
  set a := vP (halfArg K T L) with ha
  have ha0 : 0 ≤ a := vP_nonneg _
  have ha8 : a ≤ 1 / 8 := by
    have := vP_mono hx; rw [← ha] at this
    refine this.trans (le_of_eq ?_); unfold vP; rw [EIGHTH_eq]; push_cast; norm_num
  have hu := u_pos
  have hu64 : 3 * u * 64 ≤ 1 / 8 := by unfold u; norm_num
  have ht := (taylorI_spec ha.symm ha0 ha8 hu64 nTaylor 0 ONE 0 0 0 0 (by norm_num [nTaylor])
    (TInv_zero a)).1
  simp only [zero_add, nTaylor] at ht
  have htail := exp_tail_24 ha0 ha8
  -- the halved argument
  have harg : |a - θ / 2 ^ K| ≤ u + δ / 2 ^ K := by
    obtain ⟨b1, b2⟩ := shiftRight_bounds (T * L) (128 + K)
    have hcast : ((T * L : ℕ) : ℝ) / 2 ^ (128 + K) = vP T * vP L / 2 ^ K * 2 ^ 128 := by
      push_cast; rw [cast_eq_vP T, cast_eq_vP L, pow_add]; field_simp
    rw [hcast, show (T * L) >>> (128 + K) = halfArg K T L from rfl, cast_eq_vP (halfArg K T L),
      ← ha] at b1 b2
    have hK : (0 : ℝ) < 2 ^ K := by positivity
    have c1 : vP T * vP L / 2 ^ K - u < a := by
      unfold u
      have : (vP T * vP L / 2 ^ K - 1 / 2 ^ 128) * 2 ^ 128 < a * 2 ^ 128 := by
        have e : (vP T * vP L / 2 ^ K - 1 / 2 ^ 128) * (2:ℝ) ^ 128 = vP T * vP L / 2 ^ K * 2 ^ 128 - 1 := by
          field_simp
        rw [e]; linarith
      exact lt_of_mul_lt_mul_right this (by positivity)
    have c2 : a ≤ vP T * vP L / 2 ^ K := le_of_mul_le_mul_right b2 (by positivity)
    have hd : |vP T * vP L / 2 ^ K - θ / 2 ^ K| ≤ δ / 2 ^ K := by
      rw [← sub_div, abs_div, abs_of_pos hK]; exact div_le_div_of_nonneg_right hθ hK.le
    rw [abs_le] at hd ⊢; constructor <;> linarith [hd.1, hd.2]
  have hexp := norm_cexp_negI_sub a (θ / 2 ^ K)
  have ht' : ‖cv cs.1 cs.2 - tpart a 24‖ ≤ 72 * u := by
    have : (3 : ℝ) * u * ((24 : ℕ) : ℝ) = 72 * u := by push_cast; ring
    exact ht.trans (le_of_eq (by simpa using this))
  have e1 := norm_sub_le_norm_sub_add_norm_sub (cv cs.1 cs.2) (tpart a 24)
    (cexp (-I * ((θ / 2 ^ K : ℝ) : ℂ)))
  have e2 := norm_sub_le_norm_sub_add_norm_sub (tpart a 24) (cexp (-I * (a : ℂ)))
    (cexp (-I * ((θ / 2 ^ K : ℝ) : ℂ)))
  have e3 : ‖tpart a 24 - cexp (-I * (a : ℂ))‖ ≤ u := by rw [norm_sub_rev]; exact htail
  linarith [hexp.trans harg]

/-- **`e^{-iθ}`**: if `|vP T · vP L - θ| ≤ δ ≤ 2^-42`, the halved argument is at most `1/8` and
`K ≤ 40`, then `expNegI K T L` is within `2^(K+1) · 77u + 2δ` of `e^{-iθ}`. -/
theorem expNegI_spec {K T L : ℕ} {θ δ : ℝ} (hθ : |vP T * vP L - θ| ≤ δ)
    (hx : halfArg K T L ≤ EIGHTH) (hK : K ≤ 40) (hδ : δ ≤ 1 / 2 ^ 42) :
    ‖cv (expNegI K T L).1 (expNegI K T L).2 - cexp (-I * θ)‖ ≤ 2 ^ (K + 1) * (77 * u) + 2 * δ := by
  have hu := u_pos
  have hη := η_pos
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hθ
  have hT := taylor_halved hθ hx
  set E := 74 * u + δ / 2 ^ K
  have hKR : (K : ℝ) ≤ 40 := by exact_mod_cast hK
  have hKη : (K : ℝ) * η ≤ 1 := by unfold η; rw [mul_one_div, div_le_one (by positivity)]; linarith
  have h2K : (2 : ℝ) ^ K ≤ 2 ^ 40 := pow_le_pow_right₀ (by norm_num) hK
  have h2K0 : (0 : ℝ) < 2 ^ K := by positivity
  have hEu : 2 ^ K * (E + 3 * u) = 2 ^ K * (77 * u) + δ := by
    simp only [E]; field_simp; ring
  have hsmall : 2 ^ K * (E + 3 * u) * (1 + K * η) ≤ η := by
    rw [hEu]
    have h1 : 1 + (K : ℝ) * η ≤ 2 := by linarith
    have h2 : 2 ^ K * (77 * u) + δ ≤ 2 ^ 40 * (77 * u) + 1 / 2 ^ 42 := by gcongr
    have h3 : (2 ^ 40 * (77 * u) + 1 / 2 ^ 42) * 2 ≤ η := by unfold u η; norm_num
    have h4 : 0 ≤ 2 ^ K * (77 * u) + δ := by positivity
    nlinarith
  have hz : ‖cexp (-I * ((θ / 2 ^ K : ℝ) : ℂ))‖ = 1 := by
    rw [show -I * ((θ / 2 ^ K : ℝ) : ℂ) = ((-(θ / 2 ^ K) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsq := sqIter_spec K _ _ _ E hz hT hsmall hKη
  have hpow : cexp (-I * ((θ / 2 ^ K : ℝ) : ℂ)) ^ (2 ^ K) = cexp (-I * θ) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [hpow] at hsq
  unfold expNegI
  refine hsq.trans ?_
  rw [hEu]
  have h1 : 1 + (K : ℝ) * η ≤ 2 := by linarith
  have h4 : 0 ≤ 2 ^ K * (77 * u) + δ := by positivity
  have : (2 ^ K * (77 * u) + δ) * (1 + K * η) ≤ (2 ^ K * (77 * u) + δ) * 2 :=
    mul_le_mul_of_nonneg_left h1 h4
  rw [pow_succ]; nlinarith

end ZetaCert.Eval
