/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ZetaCert.Cert
public import ZetaCert.ZeroCert
public import ZetaCert.EMErrBound

@[expose] public section

/-!
# Soundness of the per-zero checker: `zc_spec`

If `zc m G N K k fuel Dp = true` then `ζ (1/2 + it) = 0` for some real `t` with
`|t - G/2^80| ≤ 2^-67` and `|t - m/10^24| ≤ 10^-20`.
-/

set_option exponentiation.threshold 600

namespace ZetaCert

open Complex ZetaCert.Eval ZetaCert.Data ZetaZeros.EM ZetaZeros.EMDeriv

/-! ## Complex rationals -/

/-- The complex number of a pair of rationals. -/
noncomputable def toC (a : CQ) : ℂ := ⟨(a.1 : ℝ), (a.2 : ℝ)⟩

@[simp] theorem toC_re (a : CQ) : (toC a).re = a.1 := rfl
@[simp] theorem toC_im (a : CQ) : (toC a).im = a.2 := rfl

theorem toC_mul (a b : CQ) : toC (cqmul a b) = toC a * toC b := by
  apply Complex.ext <;> simp [cqmul, toC]

theorem toC_add (a b : CQ) : toC (cqadd a b) = toC a + toC b := by
  apply Complex.ext <;> simp [cqadd, toC]

theorem toC_sub (a b : CQ) : toC (cqsub a b) = toC a - toC b := by
  apply Complex.ext <;> simp [cqsub, toC]

theorem toC_smul (c : ℚ) (a : CQ) : toC (cqsmul c a) = (c : ℂ) * toC a := by
  apply Complex.ext <;> simp [cqsmul, toC]

theorem norm_toC_le (a : CQ) : ‖toC a‖ ≤ ((cqn1 a : ℚ) : ℝ) := by
  have := Complex.norm_le_abs_re_add_abs_im (toC a)
  simpa [cqn1] using this

theorem norm_toC_sq (a : CQ) : ‖toC a‖ ^ 2 = ((cqn2 a : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [cqn2]

theorem qO_cast (X : ℕ) : ((qO X : ℚ) : ℝ) = vO X := by
  unfold qO vO; push_cast; ring

theorem toC_qO (a b : ℕ) : toC (qO a, qO b) = cv a b := by
  apply Complex.ext <;> simp [toC, cv, qO_cast]

/-- From a squared rational inequality to a norm inequality. -/
theorem le_mul_norm_of_sq {x κ : ℝ} {z : ℂ} (hx : 0 ≤ x) (hκ : 0 ≤ κ)
    (h : x * x ≤ κ * κ * ‖z‖ ^ 2) : x ≤ κ * ‖z‖ := by
  have h2 : x ^ 2 ≤ (κ * ‖z‖) ^ 2 := by rw [mul_pow]; nlinarith
  exact (pow_le_pow_iff_left₀ hx (by positivity) (by norm_num)).mp h2

/-! ## Bits and pieces about the data -/

theorem smallArgs_mem {K T : ℕ} : ∀ {l : List (ℕ × ℕ × ℕ)}, smallArgs K T l = true →
    ∀ d ∈ l, halfArg K T d.2.2 ≤ EIGHTH := by
  intro l
  induction l with
  | nil => intro _ d hd; simp at hd
  | cons e l ih =>
    intro h d hd
    obtain ⟨p, w, L⟩ := e
    simp only [smallArgs, Bool.and_eq_true, Nat.ble_eq] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h.1
    · exact ih h.2 d hd

theorem BernOK_mono {bern : List (ℤ × ℕ)} {M M' : ℕ} (h : BernOK bern M) (hM : M' ≤ M) :
    BernOK bern M' := fun j hj => h j (hj.trans hM)

theorem log_le_of_lt_two_pow {N Dp : ℕ} (hN1 : 1 ≤ N) (hN : N < 2 ^ Dp) :
    Real.log N ≤ 7 / 10 * Dp := by
  have h1 : Real.log N ≤ Real.log ((2 : ℝ) ^ Dp) :=
    Real.log_le_log (by exact_mod_cast hN1) (by exact_mod_cast hN.le)
  rw [Real.log_pow] at h1
  have h2 := Real.log_two_lt_d9
  have : (Dp : ℝ) * Real.log 2 ≤ Dp * (7 / 10) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  linarith

theorem prodShift_cast (c : ℚ) (n : ℕ) :
    ((prodShift c n : ℚ) : ℝ) = ∏ i ∈ Finset.range n, ((c : ℝ) + i) := by
  induction n with
  | zero => simp [prodShift]
  | succ n ih => rw [prodShift, Rat.cast_mul, ih, Finset.prod_range_succ]; push_cast; ring

/-! ## Assembling the main term and its derivative -/

theorem assemble {N k : ℕ} (hN : 0 < N) {s S D u Rq R1q : ℂ} {ℓ errS errD Ep eR δL nR nX : ℝ}
    (hs : 0 ≤ s.re)
    (hS : ‖S - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ ≤ errS)
    (hD : ‖D - ∑ n ∈ Finset.range (N + 1), A1 n s‖ ≤ errD)
    (hu : ‖u - (N : ℂ) ^ (-s)‖ ≤ Ep) (hR : ‖Rq - Rm N k s‖ ≤ eR) (hR1 : ‖R1q - R1m N k s‖ ≤ eR)
    (hℓ : |ℓ - Real.log N| ≤ δL) (hℓ0 : 0 ≤ ℓ) (hnR : ‖Rq‖ ≤ nR) (hnX : ‖R1q - (ℓ : ℂ) * Rq‖ ≤ nX) :
    ‖emMain N k s - (S + u * Rq)‖ ≤ errS + Ep * nR + eR ∧
    ‖emMain1 N k s - (D + u * (R1q - (ℓ : ℂ) * Rq))‖ ≤
      errD + Ep * nX + (eR + ℓ * eR + δL * (nR + eR)) := by
  have hNs : ‖(N : ℂ) ^ (-s)‖ ≤ 1 := Eval.norm_natCast_cpow_neg_le hs (by omega)
  have hEp0 : 0 ≤ Ep := (norm_nonneg _).trans hu
  have heR0 : 0 ≤ eR := (norm_nonneg _).trans hR
  have hδ0 : 0 ≤ δL := (abs_nonneg _).trans hℓ
  constructor
  · rw [emMain_eq hN]
    have e : (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) + (N : ℂ) ^ (-s) * Rm N k s - (S + u * Rq) =
        -(S - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) - (u - (N : ℂ) ^ (-s)) * Rq
          - (N : ℂ) ^ (-s) * (Rq - Rm N k s) := by ring
    rw [e]
    have t1 := norm_sub_le (-(S - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) - (u - (N : ℂ) ^ (-s)) * Rq)
      ((N : ℂ) ^ (-s) * (Rq - Rm N k s))
    have t2 := norm_sub_le (-(S - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)) ((u - (N : ℂ) ^ (-s)) * Rq)
    rw [norm_neg] at t2
    have t3 : ‖(u - (N : ℂ) ^ (-s)) * Rq‖ ≤ Ep * nR := by
      rw [norm_mul]; exact mul_le_mul hu hnR (norm_nonneg _) hEp0
    have t4 : ‖(N : ℂ) ^ (-s) * (Rq - Rm N k s)‖ ≤ 1 * eR := by
      rw [norm_mul]; exact mul_le_mul hNs hR (norm_nonneg _) (by norm_num)
    linarith
  · rw [emMain1_eq hN]
    set X := R1q - (ℓ : ℂ) * Rq
    set Xt := R1m N k s - Complex.log N * Rm N k s
    have hlog : Complex.log (N : ℂ) = ((Real.log N : ℝ) : ℂ) := (Complex.natCast_log).symm
    have hX : ‖X - Xt‖ ≤ eR + ℓ * eR + δL * (nR + eR) := by
      have e : X - Xt = (R1q - R1m N k s) - (ℓ : ℂ) * (Rq - Rm N k s) - ((ℓ - Real.log N : ℝ) : ℂ) * Rm N k s := by
        simp only [X, Xt, hlog]; push_cast; ring
      rw [e]
      have hRm : ‖Rm N k s‖ ≤ nR + eR := by
        have := norm_sub_norm_le Rq (Rm N k s)
        have := norm_sub_rev Rq (Rm N k s); linarith [norm_le_insert' (Rm N k s) Rq]
      have t1 := norm_sub_le ((R1q - R1m N k s) - (ℓ : ℂ) * (Rq - Rm N k s)) (((ℓ - Real.log N : ℝ) : ℂ) * Rm N k s)
      have t2 := norm_sub_le (R1q - R1m N k s) ((ℓ : ℂ) * (Rq - Rm N k s))
      have t3 : ‖(ℓ : ℂ) * (Rq - Rm N k s)‖ ≤ ℓ * eR := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hℓ0]
        exact mul_le_mul_of_nonneg_left hR hℓ0
      have t4 : ‖((ℓ - Real.log N : ℝ) : ℂ) * Rm N k s‖ ≤ δL * (nR + eR) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hℓ hRm (norm_nonneg _) hδ0
      linarith
    have e : (∑ n ∈ Finset.range (N + 1), A1 n s) + (N : ℂ) ^ (-s) * Xt - (D + u * X) =
        -(D - ∑ n ∈ Finset.range (N + 1), A1 n s) - (u - (N : ℂ) ^ (-s)) * X
          - (N : ℂ) ^ (-s) * (X - Xt) := by ring
    rw [e]
    have t1 := norm_sub_le (-(D - ∑ n ∈ Finset.range (N + 1), A1 n s) - (u - (N : ℂ) ^ (-s)) * X)
      ((N : ℂ) ^ (-s) * (X - Xt))
    have t2 := norm_sub_le (-(D - ∑ n ∈ Finset.range (N + 1), A1 n s)) ((u - (N : ℂ) ^ (-s)) * X)
    rw [norm_neg] at t2
    have t3 : ‖(u - (N : ℂ) ^ (-s)) * X‖ ≤ Ep * nX := by
      rw [norm_mul]; exact mul_le_mul hu hnX (norm_nonneg _) hEp0
    have t4 : ‖(N : ℂ) ^ (-s) * (X - Xt)‖ ≤ 1 * (eR + ℓ * eR + δL * (nR + eR)) := by
      rw [norm_mul]; exact mul_le_mul hNs hX (norm_nonneg _) (by norm_num)
    linarith

/-! ## Casts of the rational quantities -/

section Casts
variable (G N K k Dp : ℕ) (acc : Acc) (uN : ℕ × ℕ) (wN LN : ℕ) (R R1 : GZ)

theorem cast_qt : ((qt G : ℚ) : ℝ) = (G : ℝ) / 2 ^ 80 := by unfold qt; push_cast; ring
theorem cast_quu : ((quu : ℚ) : ℝ) = u := by unfold quu u; push_cast; ring
theorem cast_qδL : ((qδL : ℚ) : ℝ) = 1 / 2 ^ 126 := by unfold qδL; push_cast; ring
theorem cast_qEp : ((qEp G K : ℚ) : ℝ) = Ep K ((G : ℝ) / 2 ^ 80) (1 / 2 ^ 126) := by
  unfold qEp Ep; push_cast [cast_qt, cast_quu, cast_qδL]; ring
theorem cast_qE' : ((qE' G K : ℚ) : ℝ) = Ep K ((G : ℝ) / 2 ^ 80) (1 / 2 ^ 126) + 4 * u := by
  unfold qE'; push_cast [cast_qEp, cast_quu]; ring
theorem cast_qerrS : ((qerrS G N K Dp : ℚ) : ℝ) =
    N * (Dp * (Ep K ((G : ℝ) / 2 ^ 80) (1 / 2 ^ 126) + 4 * u)) := by
  unfold qerrS; push_cast [cast_qE']; ring
theorem cast_qerrD : ((qerrD G N K Dp : ℚ) : ℝ) =
    N * ((Dp : ℝ) * (Dp * (Ep K ((G : ℝ) / 2 ^ 80) (1 / 2 ^ 126) + 4 * u)) + Dp * (1 / 2 ^ 126) + 2 * u) := by
  unfold qerrD; push_cast [cast_qE', cast_qδL, cast_quu]; ring
theorem cast_qeR : ((qeR k : ℚ) : ℝ) = 2 * (k + 2) * u := by unfold qeR; push_cast [cast_quu]; ring

end Casts

/-- From the componentwise `remR` bounds to a norm bound. -/
theorem norm_qR_sub {R : GZ} {V : ℂ} {k : ℕ} (h1 : |(R.1 : ℝ) - (V * 2 ^ 128).re| ≤ k + 2)
    (h2 : |(R.2 : ℝ) - (V * 2 ^ 128).im| ≤ k + 2) : ‖toC (qR R) - V‖ ≤ 2 * (k + 2) * u := by
  have hre : (V * 2 ^ 128).re = V.re * 2 ^ 128 := by simp [Complex.mul_re, Eval.re_two_pow, Eval.im_two_pow]
  have him : (V * 2 ^ 128).im = V.im * 2 ^ 128 := by simp [Complex.mul_im, Eval.re_two_pow, Eval.im_two_pow]
  rw [hre] at h1; rw [him] at h2
  have e1 : |(toC (qR R) - V).re| = |(R.1 : ℝ) - V.re * 2 ^ 128| / 2 ^ 128 := by
    have : (toC (qR R) - V).re = ((R.1 : ℝ) - V.re * 2 ^ 128) / 2 ^ 128 := by
      simp only [Complex.sub_re, toC_re, qR]; push_cast; field_simp
    rw [this, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ 128)]
  have e2 : |(toC (qR R) - V).im| = |(R.2 : ℝ) - V.im * 2 ^ 128| / 2 ^ 128 := by
    have : (toC (qR R) - V).im = ((R.2 : ℝ) - V.im * 2 ^ 128) / 2 ^ 128 := by
      simp only [Complex.sub_im, toC_im, qR]; push_cast; field_simp
    rw [this, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ 128)]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [e1, e2]
  unfold u
  have : |(R.1 : ℝ) - V.re * 2 ^ 128| / 2 ^ 128 + |(R.2 : ℝ) - V.im * 2 ^ 128| / 2 ^ 128 ≤
      ((k : ℝ) + 2) / 2 ^ 128 + ((k : ℝ) + 2) / 2 ^ 128 := by gcongr
  rw [show 2 * ((k : ℝ) + 2) * (1 / 2 ^ 128) = ((k : ℝ) + 2) / 2 ^ 128 + ((k : ℝ) + 2) / 2 ^ 128 by ring]
  exact this

/-- `N^{-1/2} ≤ (w+1)/2^128` from `2^256 < (w+1)^2 N`. -/
theorem rpow_neg_half_le {N w : ℕ} (hN : 0 < N) (h : 2 ^ 256 < (w + 1) * (w + 1) * N) :
    (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ((w + 1 : ℕ) : ℝ) / 2 ^ 128 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set r := (N : ℝ) ^ (-(1 / 2 : ℝ))
  have hr0 : 0 < r := by positivity
  have hrsq : r * r * N = 1 := Eval.rpow_neg_half_sq hNR
  have hR : (2 : ℝ) ^ 256 < ((w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) * N := by exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]
  by_contra hc; push Not at hc
  have h0 : (0 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by positivity
  have := mul_lt_mul_of_pos_right (mul_self_lt_mul_self h0 hc) hNR
  have e : (r * 2 ^ 128) * (r * 2 ^ 128) * (N : ℝ) = 2 ^ 256 := by
    have : (r * 2 ^ 128) * (r * 2 ^ 128) * (N : ℝ) = 2 ^ 256 * (r * r * N) := by ring
    rw [this, hrsq, mul_one]
  linarith

/-! ## The theorem -/

theorem zc_spec {m G N K k fuel Dp : ℕ} (h : zc m G N K k fuel Dp = true) :
    ∃ t : ℝ, |t - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 ∧ riemannZeta (1 / 2 + t * I) = 0 := by
  unfold zc at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  rename_i pN wN LN hlast
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpN, hN1⟩, hN20⟩, hNDp⟩, hK⟩, hk⟩, hG⟩, hsm⟩, hen⟩, hQ⟩ := h
  subst hpN
  unfold zcQ at hQ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
  obtain ⟨⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩, q7⟩ := hQ
  -- the data
  have hmemN : (pN, wN, LN) ∈ dataN pN := List.mem_of_getLast? hlast
  have hsub : ∀ d ∈ dataN pN, d ∈ pdata := fun d hd => List.takeWhile_subset _ hd
  have hw : wOK (dataN pN) = true := wOK_sublist pdata_w hsub
  have hl : LogOK (1 / 2 ^ 126) (dataN pN) := fun d hd => pdata_log d (hsub d hd)
  have hwN := (wOK_iff _).mp hw _ hmemN
  simp only at hwN
  obtain ⟨hN2, hwN1, hwN2⟩ := hwN
  have hLN : |vP LN - Real.log pN| ≤ 1 / 2 ^ 126 := hl _ hmemN
  -- the point
  set γ : ℝ := (G : ℝ) / 2 ^ 80 with hγ
  have hγ2 : 2 ≤ γ := by
    rw [hγ, le_div_iff₀ (by positivity)]
    have : ((2 ^ 81 : ℕ) : ℝ) ≤ G := by exact_mod_cast hG
    push_cast at this; linarith
  have hvT : vP (G * 2 ^ 48) = γ := by unfold vP; rw [hγ]; push_cast; field_simp; ring
  -- rational facts as real facts
  have r1 : γ * (1 / 2 ^ 126) ≤ 1 / 2 ^ 42 := by
    have := q1; rw [← Rat.cast_le (K := ℝ)] at this; push_cast [cast_qt, cast_qδL] at this; exact this
  set Ep' := Ep K γ (1 / 2 ^ 126) with hEp'
  have r2 : (Dp : ℝ) * (Ep' + 4 * u) * Ep' ≤ u := by
    have := q2; rw [← Rat.cast_le (K := ℝ)] at this; push_cast [cast_qE', cast_qEp, cast_quu] at this
    exact this
  have r3 : (Dp : ℝ) * (Ep' + 4 * u) ≤ 1 := by
    have := q3; rw [← Rat.cast_le (K := ℝ)] at this; push_cast [cast_qE', cast_qEp] at this; exact this
  have r4 : (Dp : ℝ) ≤ 2 ^ 20 := by
    have := q4; rw [← Rat.cast_le (K := ℝ)] at this; push_cast at this; exact this
  have hΛ : Real.log pN + Dp * (1 / 2 ^ 126) ≤ (Dp : ℝ) := by
    have := log_le_of_lt_two_pow hN1 hNDp
    have : (Dp : ℝ) * (1 / 2 ^ 126) ≤ 3 / 10 * Dp := by
      have : (0 : ℝ) ≤ Dp := by positivity
      nlinarith
    linarith
  -- the Dirichlet sums
  obtain ⟨hS, hD⟩ := sums_spec (N := pN) (K := K) (T := G * 2 ^ 48) (fuel := fuel) (Dp := Dp)
    (data := dataN pN) (t := γ) (δL := 1 / 2 ^ 126) (Λ := Dp) hvT hK r1 (by positivity) hw hl hsm hen hN1
    hN20 hNDp r2 r3 hΛ r4
  -- the term `N^{-s}`
  have hu := primeTerm_spec (K := K) (T := G * 2 ^ 48) (w := wN) (L := LN) (p := pN) (t := γ)
    (δL := 1 / 2 ^ 126) (by omega) hwN1 hwN2 hvT hLN (smallArgs_mem hsm _ hmemN) hK r1
  -- the rational parts
  have hbern : BernOK bern (2 * k + 2) := BernOK_mono bern_ok hk
  obtain ⟨hR1, hR2⟩ := remR_spec (N := pN) (G := G) (k := k) (by omega) hbern
  obtain ⟨hR11, hR12⟩ := remR1_spec (N := pN) (G := G) (k := k) (by omega) hbern
  have hRn := norm_qR_sub hR1 hR2
  have hR1n := norm_qR_sub hR11 hR12
  have hsG : sG G = (1 / 2 : ℂ) + (γ : ℂ) * I := by unfold sG; rw [hγ]
  rw [hsG] at hRn hR1n
  set c : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * I with hc
  set a := sums pN K (G * 2 ^ 48) fuel (dataN pN)
  set U := primeTerm K (G * 2 ^ 48) wN LN
  set R := remR pN G bern k
  set R1 := remR1 pN G bern k
  have hcre : c.re = 1 / 2 := by simp [c]
  have hcim : c.im = γ := by simp [c]
  have hℓ : ((qℓ LN : ℚ) : ℝ) = vP LN := by unfold qℓ vP; push_cast; ring
  have hℓ0 : 0 ≤ vP LN := vP_nonneg _
  have hnX : ‖toC (qR R1) - ((vP LN : ℝ) : ℂ) * toC (qR R)‖ ≤ ((cqn1 (qX LN R R1) : ℚ) : ℝ) := by
    have : toC (qX LN R R1) = toC (qR R1) - ((vP LN : ℝ) : ℂ) * toC (qR R) := by
      unfold qX; rw [toC_sub, toC_smul, ← hℓ]; push_cast; ring
    rw [← this]; exact norm_toC_le _
  have hD' : ‖accD a - ∑ n ∈ Finset.range (pN + 1), A1 n c‖ ≤
      pN * ((Dp : ℝ) * (Dp * (Ep' + 4 * u)) + Dp * (1 / 2 ^ 126) + 2 * u) := by
    simp only [A1]; exact hD
  have hu' : ‖cv U.1 U.2 - (pN : ℂ) ^ (-c)‖ ≤ Ep' := hu
  obtain ⟨hF, hDd⟩ := assemble (N := pN) (k := k) (by omega) (s := c) (S := accS a) (D := accD a)
    (u := cv U.1 U.2) (Rq := toC (qR R)) (R1q := toC (qR R1)) (ℓ := vP LN) (Ep := Ep') (by rw [hcre]; norm_num)
    hS hD' hu' hRn hR1n hLN hℓ0 (norm_toC_le _) hnX
  have hFv : toC (qFv a U R) = accS a + cv U.1 U.2 * toC (qR R) := by
    unfold qFv qS qu; rw [toC_add, toC_mul, toC_qO, toC_qO]; rfl
  have hFd : toC (qFd a U LN R R1) = accD a + cv U.1 U.2 * (toC (qR R1) - ((vP LN : ℝ) : ℂ) * toC (qR R)) := by
    unfold qFd qD qu qX; rw [toC_add, toC_mul, toC_sub, toC_smul, toC_qO, toC_qO, ← hℓ]; push_cast; rfl
  rw [← hFv] at hF
  rw [← hFd] at hDd
  -- the remainder of Euler–Maclaurin
  have hbk := (hbern (2 * k + 2) le_rfl)
  have hbAbs : ((qbAbs k : ℚ) : ℝ) = |(bernoulli (2 * k + 2) : ℝ)| := by
    obtain ⟨h0, h1⟩ := hbk
    unfold qbAbs
    have : (bernoulli (2 * k + 2) : ℝ) = ((bernAt bern (2 * k + 2)).1 : ℝ) / (bernAt bern (2 * k + 2)).2 := by
      have := congrArg (fun q : ℚ => (q : ℝ)) h1; push_cast at this; exact this
    rw [this, abs_div]; push_cast
    rw [abs_of_pos (by exact_mod_cast h0 : (0 : ℝ) < (bernAt bern (2 * k + 2)).2)]
  have hE0 : ‖riemannZeta c - emMain pN k c‖ ≤ ((qE0 G pN k wN : ℚ) : ℝ) := by
    have hc1 : c ≠ 1 := by intro h; have := congrArg Complex.im h; rw [hcim] at this; simp at this; linarith
    refine (riemannZeta_sub_emMain_le (by omega) (by rw [hcre]; norm_num) hc1 k).trans ?_
    rw [hcre, hcim]
    refine (emErr_center_le (by omega) k (by linarith) (rpow_neg_half_le (by omega) hwN2)).trans (le_of_eq ?_)
    unfold qE0
    push_cast [prodShift_cast, fact_eq, cast_qt, hbAbs]
    rw [← hγ]
    congr 1; congr 1; congr 1; congr 1
    refine Finset.prod_congr rfl fun i _ => by ring
  have hE1 : ∀ w ∈ Metric.sphere c (1 / 4), ‖riemannZeta w - emMain pN k w‖ ≤ ((qE1 G pN k : ℚ) : ℝ) := by
    intro w hw
    refine (emErr_circle_le (by omega) k hγ2 hw).trans (le_of_eq ?_)
    unfold qE1
    push_cast [prodShift_cast, fact_eq, cast_qt, hbAbs]
    rw [← hγ]
    congr 1; congr 1; congr 1; congr 1
    refine Finset.prod_congr rfl fun i _ => by ring
  -- casts of the error terms
  have heF : ((qeF G pN K k Dp R : ℚ) : ℝ) = pN * (Dp * (Ep' + 4 * u)) + Ep' * ((cqn1 (qR R) : ℚ) : ℝ)
      + 2 * (k + 2) * u := by
    unfold qeF; push_cast [cast_qerrS, cast_qEp, cast_qeR]; rw [← hγ]
  have heD : ((qeD G pN K k Dp LN R R1 : ℚ) : ℝ) =
      pN * ((Dp : ℝ) * (Dp * (Ep' + 4 * u)) + Dp * (1 / 2 ^ 126) + 2 * u) +
      Ep' * ((cqn1 (qX LN R R1) : ℚ) : ℝ) +
      (2 * (k + 2) * u + vP LN * (2 * (k + 2) * u) + 1 / 2 ^ 126 * (((cqn1 (qR R) : ℚ) : ℝ) + 2 * (k + 2) * u)) := by
    unfold qeD qeX; push_cast [cast_qerrD, cast_qEp, cast_qeR, cast_qδL, hℓ]; rw [← hγ]
  rw [← heF] at hF
  rw [← heD] at hDd
  have hEp0 : 0 ≤ Ep' := (norm_nonneg _).trans hu'
  have hu0 := u_pos
  have heD0 : 0 ≤ ((qeD G pN K k Dp LN R R1 : ℚ) : ℝ) := (norm_nonneg _).trans hDd
  have heF0 : 0 ≤ ((qeF G pN K k Dp R : ℚ) : ℝ) := (norm_nonneg _).trans hF
  have hE00 : 0 ≤ ((qE0 G pN k wN : ℚ) : ℝ) := (norm_nonneg _).trans hE0
  have hE10 : 0 ≤ ((qE1 G pN k : ℚ) : ℝ) :=
    (norm_nonneg _).trans (hE1 (c + 1 / 4) (by simp [Metric.mem_sphere, dist_eq_norm]))
  have hr : ((qr : ℚ) : ℝ) = 1 / 2 ^ 67 := by unfold qr; push_cast; ring
  -- (B1)
  have B1 : 1 / 2 ^ 67 * (112 + 160 * (γ + 1)) + 4 * ((qE1 G pN k : ℚ) : ℝ) + ((qeD G pN K k Dp LN R R1 : ℚ) : ℝ)
      ≤ 1 / 2 * ‖toC (qFd a U LN R R1)‖ := by
    have h5 := q5
    rw [← Rat.cast_le (K := ℝ)] at h5
    push_cast at h5
    rw [← norm_toC_sq] at h5
    have e : ((qlhs1 G pN K k Dp LN R R1 : ℚ) : ℝ) =
        1 / 2 ^ 67 * (112 + 160 * (γ + 1)) + 4 * ((qE1 G pN k : ℚ) : ℝ) + ((qeD G pN K k Dp LN R R1 : ℚ) : ℝ) := by
      unfold qlhs1; push_cast [cast_qt, hr]; rw [← hγ]
    rw [e] at h5
    exact le_mul_norm_of_sq (by positivity) (by norm_num) (by linarith)
  -- (B2)
  have B2 : ‖toC (qFv a U R)‖ + ((qeF G pN K k Dp R : ℚ) : ℝ) + ((qE0 G pN k wN : ℚ) : ℝ)
      ≤ (1 - 1 / 2) * ‖toC (qFd a U LN R R1)‖ * (1 / 2 ^ 67) := by
    have h6 := q6
    rw [← Rat.cast_le (K := ℝ)] at h6
    push_cast at h6
    rw [← norm_toC_sq] at h6
    have e : ((qlhs2 G pN K k Dp a U wN R : ℚ) : ℝ) =
        ((cqn1 (qFv a U R) : ℚ) : ℝ) + ((qeF G pN K k Dp R : ℚ) : ℝ) + ((qE0 G pN k wN : ℚ) : ℝ) := by
      unfold qlhs2; push_cast; rfl
    rw [e, hr] at h6
    have h0 : 0 ≤ ((cqn1 (qFv a U R) : ℚ) : ℝ) := (norm_nonneg _).trans (norm_toC_le _)
    have := le_mul_norm_of_sq (x := ((cqn1 (qFv a U R) : ℚ) : ℝ) + ((qeF G pN K k Dp R : ℚ) : ℝ) +
      ((qE0 G pN k wN : ℚ) : ℝ)) (κ := (1 - 1 / 2) * (1 / 2 ^ 67)) (z := toC (qFd a U LN R R1))
      (by positivity) (by norm_num) (by
        have e2 : (1 - 1 / 2 : ℝ) * (1 - 1 / 2) * (1 / 2 ^ 67) * (1 / 2 ^ 67) * ‖toC (qFd a U LN R R1)‖ ^ 2 =
            ((1 - 1 / 2) * (1 / 2 ^ 67)) * ((1 - 1 / 2) * (1 / 2 ^ 67)) * ‖toC (qFd a U LN R R1)‖ ^ 2 := by ring
        linarith)
    have := norm_toC_le (qFv a U R)
    linarith
  obtain ⟨t0, ht0, hz⟩ := zero_of_EM_bounds (N := pN) (k := k) (γ := γ) (r := 1 / 2 ^ 67) (κ := 1 / 2)
    (by omega) hγ2 (by positivity) (by norm_num) (by norm_num) (by norm_num) hF hDd hE0 hE1 B1 B2
  refine ⟨t0, ?_, hz⟩
  have h7 := q7
  rw [← Rat.cast_le (K := ℝ)] at h7
  push_cast [cast_qt, hr] at h7
  rw [← hγ] at h7
  have := abs_sub_le t0 γ ((m : ℝ) / 10 ^ 24)
  linarith

end ZetaCert
