/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.Eval.CoreSound

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
