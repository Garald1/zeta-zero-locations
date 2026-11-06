/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.LegCert
import ZetaCert.CertSound
import ZetaCert.Eval.EMRestSSound

/-!
# Soundness of the leg-point checker: `lc_spec`

If `lc j G N K k fuel Dp v d = true` then, at `s = j/4096 + i G/2^80`,
`v ≤ Re ζ(s)` and `‖ζ'(s)‖ ≤ d`.
-/

set_option exponentiation.threshold 600

namespace ZetaCert

open Complex Metric ZetaCert.Eval ZetaCert.Data ZetaZeros.EM ZetaZeros.EMDeriv ZetaZeros.Deriv

/-- Cauchy's estimate for `ζ' - (emMain)'` on the circle of radius `1/4`. -/
theorem deriv_zeta_sub_emMain1_le {N k : ℕ} (hN : 0 < N) {c : ℂ} {E1 : ℝ} (hcre : 1 / 2 ≤ c.re)
    (hcim : 2 ≤ c.im) (hE1 : ∀ w ∈ sphere c (1 / 4), ‖riemannZeta w - emMain N k w‖ ≤ E1) :
    ‖deriv riemannZeta c - emMain1 N k c‖ ≤ 4 * E1 := by
  have hc1 : (1 / 4 : ℝ) < ‖c - 1‖ := by
    have h1 : (c - 1).im = c.im := by simp
    have h2 := Complex.abs_im_le_norm (c - 1)
    rw [h1, abs_of_pos (by linarith)] at h2
    linarith
  have hc0 : c ≠ 0 := by intro h; rw [h] at hcre; simp at hcre; linarith
  have hdiff : DifferentiableOn ℂ (emMain N k) (closedBall c (1 / 4)) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_emMain hN
    · intro h; subst h
      rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at hw
      have := Complex.abs_im_le_norm c; rw [abs_of_pos (by linarith)] at this; linarith
    · intro h; subst h
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw; linarith
  have := norm_deriv_zeta_sub_le (by norm_num) hc1 hdiff hE1
  rw [deriv_emMain hN k hc0 (by intro h; rw [h] at hc1; simp at hc1; linarith)] at this
  linarith

theorem dataSigma_mem {j : ℕ} : ∀ {l : List (ℕ × ℕ × ℕ)} {d : ℕ × ℕ × ℕ}, d ∈ dataSigma j l →
    ∃ e ∈ l, d = (e.1, powPP e.2.1 16 j, e.2.2) := by
  intro l
  induction l with
  | nil => intro d hd; simp [dataSigma] at hd
  | cons e l ih =>
    intro d hd
    obtain ⟨p, x, L⟩ := e
    simp only [dataSigma, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨(p, x, L), List.mem_cons_self .., rfl⟩
    · obtain ⟨e', he', rfl⟩ := ih hd
      exact ⟨e', List.mem_cons_of_mem _ he', rfl⟩

theorem mem_dataSigma {j : ℕ} : ∀ {l : List (ℕ × ℕ × ℕ)} {e : ℕ × ℕ × ℕ}, e ∈ l →
    (e.1, powPP e.2.1 16 j, e.2.2) ∈ dataSigma j l := by
  intro l
  induction l with
  | nil => intro e he; simp at he
  | cons d l ih =>
    intro e he
    obtain ⟨p, x, L⟩ := d
    simp only [dataSigma, List.mem_cons] at he ⊢
    rcases he with rfl | he
    · left; rfl
    · right; exact ih he

theorem dataSigma_fst (j : ℕ) : ∀ l : List (ℕ × ℕ × ℕ), (dataSigma j l).map Prod.fst = l.map Prod.fst := by
  intro l; induction l with
  | nil => rfl
  | cons e l ih => obtain ⟨p, x, L⟩ := e; simp [dataSigma, ih]

/-- The `j`-th power of a root datum approximates `p^{-j/4096}`. -/
theorem powPP_root {p x j : ℕ} (hp : 0 < p) (hroot : rootOK p x 4096 = true) (hj0 : 0 < j)
    (hj : j < 2 ^ 16) :
    |vP (powPP x 16 j) - (p : ℝ) ^ (-((j : ℝ) / 4096))| ≤ (2 * j - 1) * (2 * u) ∧
      vP (powPP x 16 j) ≤ 1 := by
  obtain ⟨h1, h2⟩ := rootOK_spec hp (by norm_num) hroot
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set a := (p : ℝ) ^ (-(1 / (4096 : ℕ) : ℝ))
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by norm_num)
  obtain ⟨l1, l2⟩ := powPP_spec (x := x) (a := a) (e := u) h1 h2 ha1 16 j hj0 hj
  have hpow : a ^ j = (p : ℝ) ^ (-((j : ℝ) / 4096)) := by
    simp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpR.le]; congr 1; push_cast; ring
  rw [hpow] at l1 l2
  have hle : (p : ℝ) ^ (-((j : ℝ) / 4096)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by
      have : (0 : ℝ) ≤ (j : ℝ) / 4096 := by positivity
      linarith)
  refine ⟨?_, l2.trans hle⟩
  rw [abs_le]
  constructor
  · have : (2 * (j : ℝ) - 1) * (u + u) = (2 * j - 1) * (2 * u) := by ring
    linarith
  · have : 0 ≤ (2 * (j : ℝ) - 1) * (2 * u) := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj0
      have := u_pos
      nlinarith
    linarith

section CastsG
variable (G N K k Dp j : ℕ) (LN : ℕ) (R R1 : GZ)

theorem cast_qσ : ((qσ j : ℚ) : ℝ) = (j : ℝ) / 4096 := by unfold qσ; push_cast; ring
theorem cast_qew : ((qew j : ℚ) : ℝ) = (2 * j - 1) * (2 * u) := by unfold qew; push_cast [cast_quu]; ring
theorem cast_qEpG : ((qEpG G K j : ℚ) : ℝ) =
    EpG K ((G : ℝ) / 2 ^ 80) (1 / 2 ^ 126) ((2 * j - 1) * (2 * u)) := by
  unfold qEpG EpG; push_cast [cast_qt, cast_quu, cast_qδL, cast_qew]; ring
theorem cast_qE'G : ((qE'G G K j : ℚ) : ℝ) =
    EpG K ((G : ℝ) / 2 ^ 80) (1 / 2 ^ 126) ((2 * j - 1) * (2 * u)) + 4 * u := by
  unfold qE'G; push_cast [cast_qEpG, cast_quu]; ring

end CastsG

theorem lc_spec {j G N K k fuel Dp : ℕ} {v d : ℚ} (h : lc j G N K k fuel Dp v d = true) :
    let s : ℂ := (((j : ℝ) / 4096 : ℝ) : ℂ) + (((G : ℝ) / 2 ^ 80 : ℝ) : ℂ) * I
    (v : ℝ) ≤ (riemannZeta s).re ∧ ‖deriv riemannZeta s‖ ≤ d := by
  intro s
  unfold lc at h
  simp only at h
  split at h
  rotate_left
  · exact absurd h (by simp)
  rename_i pN wN LN' pN' xN LN hlast hrlast
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpN, hpN'⟩, hN1⟩, hN20⟩, hNDp⟩, hK⟩, hk⟩, hG⟩, hj1⟩, hj2⟩, hsm⟩, hen⟩, hQ⟩ := h
  subst hpN'
  subst hpN
  unfold lcQ at hQ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
  obtain ⟨⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩, q7⟩ := hQ
  -- the data
  have hmemN : (pN, wN, LN') ∈ dataN pN := List.mem_of_getLast? hlast
  have hsub : ∀ d ∈ dataN pN, d ∈ pdata := fun d hd => List.takeWhile_subset _ hd
  have hw : wOK (dataN pN) = true := wOK_sublist pdata_w hsub
  have hwN := (wOK_iff _).mp hw _ hmemN
  simp only at hwN
  obtain ⟨hN2, hwN1, hwN2⟩ := hwN
  have hrmemN : (pN, xN, LN) ∈ rdataN pN := List.mem_of_getLast? hrlast
  have hrsub : ∀ d ∈ rdataN pN, d ∈ rdata := fun d hd => List.takeWhile_subset _ hd
  obtain ⟨-, hrootN, hLN⟩ := rdata_mem (hrsub _ hrmemN)
  simp only at hrootN hLN
  set σ : ℝ := (j : ℝ) / 4096 with hσdef
  have hσ : 1 / 2 ≤ σ := by
    rw [hσdef, le_div_iff₀ (by norm_num)]; have : (2048 : ℝ) ≤ j := by exact_mod_cast hj1
    linarith
  have hj0 : 0 < j := by omega
  have hj16 : j < 2 ^ 16 := by omega
  set ew : ℝ := (2 * j - 1) * (2 * u) with hew
  have hdat : ∀ d ∈ dataSigma j (rdataN pN), 2 ≤ d.1 ∧ |vP d.2.1 - (d.1 : ℝ) ^ (-σ)| ≤ ew ∧ vP d.2.1 ≤ 1 := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := dataSigma_mem hd
    obtain ⟨h2, hr, -⟩ := rdata_mem (hrsub e he)
    obtain ⟨b1, b2⟩ := powPP_root (by omega) hr hj0 hj16
    exact ⟨h2, b1, b2⟩
  have hl : LogOK (1 / 2 ^ 126) (dataSigma j (rdataN pN)) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := dataSigma_mem hd
    exact (rdata_mem (hrsub e he)).2.2
  have hen' : enumOK pN fuel ((dataSigma j (rdataN pN)).map Prod.fst) = true := hen
  -- the point
  set γ : ℝ := (G : ℝ) / 2 ^ 80 with hγ
  have hγ2 : 2 ≤ γ := by
    rw [hγ, le_div_iff₀ (by positivity)]
    have : ((2 ^ 81 : ℕ) : ℝ) ≤ G := by exact_mod_cast hG
    push_cast at this; linarith
  have hvT : vP (G * 2 ^ 48) = γ := by unfold vP; rw [hγ]; push_cast; field_simp; ring
  have r1 : γ * (1 / 2 ^ 126) ≤ 1 / 2 ^ 42 := by
    have := q1; rw [← Rat.cast_le (K := ℝ)] at this; push_cast [cast_qt, cast_qδL] at this; exact this
  set Ep' := EpG K γ (1 / 2 ^ 126) ew with hEp'
  have r2 : (Dp : ℝ) * (Ep' + 4 * u) * Ep' ≤ u := by
    have := q2; rw [← Rat.cast_le (K := ℝ)] at this; push_cast [cast_qE'G, cast_qEpG, cast_quu] at this
    exact this
  have r3 : (Dp : ℝ) * (Ep' + 4 * u) ≤ 1 := by
    have := q3; rw [← Rat.cast_le (K := ℝ)] at this; push_cast [cast_qE'G, cast_qEpG] at this; exact this
  have r4 : (Dp : ℝ) ≤ 2 ^ 20 := by
    have := q4; rw [← Rat.cast_le (K := ℝ)] at this; push_cast at this; exact this
  have r5 : ew ≤ 1 / 2 ^ 60 := by
    have := q5; rw [← Rat.cast_le (K := ℝ)] at this; push_cast [cast_qew] at this; exact this
  have hew0 : 0 ≤ ew := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj0
    have := u_pos; simp only [hew]; nlinarith
  have hΛ : Real.log pN + Dp * (1 / 2 ^ 126) ≤ (Dp : ℝ) := by
    have := log_le_of_lt_two_pow hN1 hNDp
    have : (Dp : ℝ) * (1 / 2 ^ 126) ≤ 3 / 10 * Dp := by
      have : (0 : ℝ) ≤ Dp := by positivity
      nlinarith
    linarith
  -- the Dirichlet sums
  obtain ⟨hS, hD⟩ := sums_spec_gen (N := pN) (K := K) (T := G * 2 ^ 48) (fuel := fuel) (Dp := Dp)
    (data := dataSigma j (rdataN pN)) (t := γ) (δL := 1 / 2 ^ 126) (Λ := Dp) (σ := σ) (ew := ew)
    (by linarith) (by linarith) hvT hK r1 (by positivity) hdat r5 hew0 hl hsm hen' hN1
    hN20 hNDp r2 r3 hΛ r4
  -- the term `N^{-s}`
  obtain ⟨hwN', hwN1'⟩ := powPP_root (by omega) hrootN hj0 hj16
  have hxN : halfArg K (G * 2 ^ 48) LN ≤ EIGHTH := by
    exact smallArgs_mem hsm (pN, powPP xN 16 j, LN) (mem_dataSigma hrmemN)
  have hu := primeTerm_spec_gen (K := K) (T := G * 2 ^ 48) (w := powPP xN 16 j) (L := LN) (p := pN) (t := γ)
    (δL := 1 / 2 ^ 126) (σ := σ) (ew := ew) (by omega) hwN' hwN1' hvT hLN hxN hK r1
  -- the rational parts
  have hbern : BernOK bern (2 * k + 2) := BernOK_mono bern_ok hk
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hG
  obtain ⟨hR1, hR2⟩ := remRS_spec (N := pN) (S := j * 2 ^ 68) (G := G) (k := k) (by omega) hG0 hbern
  obtain ⟨hR11, hR12⟩ := remR1S_spec (N := pN) (S := j * 2 ^ 68) (G := G) (k := k) (by omega) hG0 hbern
  have hRn := norm_qR_sub hR1 hR2
  have hR1n := norm_qR_sub hR11 hR12
  have hsG : sSG (j * 2 ^ 68) G = s := by
    have e1 : (((j * 2 ^ 68 : ℕ) : ℝ) / 2 ^ 80) = (j : ℝ) / 4096 := by push_cast; ring
    unfold sSG; rw [e1]
  rw [hsG] at hRn hR1n
  set a := sums pN K (G * 2 ^ 48) fuel (dataSigma j (rdataN pN))
  set U := primeTerm K (G * 2 ^ 48) (powPP xN 16 j) LN
  set R := remRS (j * 2 ^ 68) pN G bern k
  set R1 := remR1S (j * 2 ^ 68) pN G bern k
  have hsre : s.re = σ := by
    show ((((j : ℝ) / 4096 : ℝ) : ℂ) + (((G : ℝ) / 2 ^ 80 : ℝ) : ℂ) * I).re = σ
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have hsim : s.im = γ := by
    show ((((j : ℝ) / 4096 : ℝ) : ℂ) + (((G : ℝ) / 2 ^ 80 : ℝ) : ℂ) * I).im = γ
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have hs' : s = (σ : ℂ) + (γ : ℂ) * I := rfl
  have hℓ : ((qℓ LN : ℚ) : ℝ) = vP LN := by unfold qℓ vP; push_cast; ring
  have hℓ0 : 0 ≤ vP LN := vP_nonneg _
  have hnX : ‖toC (qR R1) - ((vP LN : ℝ) : ℂ) * toC (qR R)‖ ≤ ((cqn1 (qX LN R R1) : ℚ) : ℝ) := by
    have : toC (qX LN R R1) = toC (qR R1) - ((vP LN : ℝ) : ℂ) * toC (qR R) := by
      unfold qX; rw [toC_sub, toC_smul, ← hℓ]; push_cast; ring
    rw [← this]; exact norm_toC_le _
  have hD' : ‖accD a - ∑ n ∈ Finset.range (pN + 1), A1 n s‖ ≤
      pN * ((Dp : ℝ) * (Dp * (Ep' + 4 * u)) + Dp * (1 / 2 ^ 126) + 2 * u) := by
    simp only [A1]; exact hD
  have hu' : ‖cv U.1 U.2 - (pN : ℂ) ^ (-s)‖ ≤ Ep' := hu
  obtain ⟨hF, hDd⟩ := assemble (N := pN) (k := k) (by omega) (s := s) (S := accS a) (D := accD a)
    (u := cv U.1 U.2) (Rq := toC (qR R)) (R1q := toC (qR R1)) (ℓ := vP LN) (Ep := Ep')
    (by rw [hsre]; linarith) hS hD' hu' hRn hR1n hLN hℓ0 (norm_toC_le _) hnX
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
  have hE0 : ‖riemannZeta s - emMain pN k s‖ ≤ ((qE0G G pN k j wN : ℚ) : ℝ) := by
    have hc1 : s ≠ 1 := by intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
    refine (riemannZeta_sub_emMain_le (by omega) (by rw [hsre]; linarith) hc1 k).trans ?_
    rw [hsre, hsim]
    refine (emErr_center_le_gen (by omega) k hσ (by linarith) (rpow_neg_half_le (by omega) hwN2)).trans (le_of_eq ?_)
    unfold qE0G
    push_cast [prodShift_cast, fact_eq, cast_qt, hbAbs, cast_qσ]
    rw [← hγ, ← hσdef]
    congr 1; congr 1; congr 1; congr 1
    refine Finset.prod_congr rfl fun i _ => by ring
  have hE1 : ∀ w ∈ Metric.sphere s (1 / 4), ‖riemannZeta w - emMain pN k w‖ ≤ ((qE1G G pN k j : ℚ) : ℝ) := by
    intro w hw
    refine (emErr_circle_le_gen (by omega) k hσ hγ2 (by rw [← hs']; exact hw)).trans (le_of_eq ?_)
    unfold qE1G
    push_cast [prodShift_cast, fact_eq, cast_qt, hbAbs, cast_qσ]
    rw [← hγ, ← hσdef]
    congr 1; congr 1; congr 1; congr 1
    refine Finset.prod_congr rfl fun i _ => by ring
  have hderiv := deriv_zeta_sub_emMain1_le (N := pN) (k := k) (by omega) (c := s)
    (by rw [hsre]; exact hσ) (by rw [hsim]; exact hγ2) hE1
  -- casts of the error terms
  have heF : ((qeFG G pN K k Dp j R : ℚ) : ℝ) = pN * (Dp * (Ep' + 4 * u)) + Ep' * ((cqn1 (qR R) : ℚ) : ℝ)
      + 2 * (k + 2) * u := by
    unfold qeFG qerrSG; push_cast [cast_qE'G, cast_qEpG, cast_qeR]; rw [← hγ]
  have heD : ((qeDG G pN K k Dp j LN R R1 : ℚ) : ℝ) =
      pN * ((Dp : ℝ) * (Dp * (Ep' + 4 * u)) + Dp * (1 / 2 ^ 126) + 2 * u) +
      Ep' * ((cqn1 (qX LN R R1) : ℚ) : ℝ) +
      (2 * (k + 2) * u + vP LN * (2 * (k + 2) * u) + 1 / 2 ^ 126 * (((cqn1 (qR R) : ℚ) : ℝ) + 2 * (k + 2) * u)) := by
    unfold qeDG qerrDG qeX; push_cast [cast_qE'G, cast_qEpG, cast_qeR, cast_qδL, hℓ, cast_quu]; rw [← hγ]
  rw [← heF] at hF
  rw [← heD] at hDd
  constructor
  · have h6 := q6
    rw [← Rat.cast_le (K := ℝ)] at h6
    push_cast at h6
    have hre : |(riemannZeta s).re - (toC (qFv a U R)).re| ≤ ‖riemannZeta s - toC (qFv a U R)‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have := norm_sub_le_norm_sub_add_norm_sub (riemannZeta s) (emMain pN k s) (toC (qFv a U R))
    rw [toC_re] at hre
    rw [abs_le] at hre
    linarith
  · have h7 := q7
    rw [← Rat.cast_le (K := ℝ)] at h7
    push_cast at h7
    have := norm_sub_le_norm_sub_add_norm_sub (deriv riemannZeta s) (emMain1 pN k s) (toC (qFd a U LN R R1))
    have hn : ‖deriv riemannZeta s‖ ≤ ‖deriv riemannZeta s - toC (qFd a U LN R R1)‖ + ‖toC (qFd a U LN R R1)‖ := by
      have := norm_add_le (deriv riemannZeta s - toC (qFd a U LN R R1)) (toC (qFd a U LN R R1))
      simpa using this
    have := norm_toC_le (qFd a U LN R R1)
    linarith

end ZetaCert
