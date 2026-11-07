/-
Vendored from https://github.com/antoine-olivier/rh-up-to-15-lean at commit
dec8fa913b6c972c2d16f4d23f54d2174cef7718, file ZetaZeros/Deriv.lean (Apache License 2.0,
see LICENSE-rh-up-to-15-lean). Local modifications: the PNT+ import is redirected to the copy
vendored in zeta23 (Zeta23.FromPNTPlus.ZetaBounds); any further changes are marked "(port)".
-/
module

public import Zeta23.FromPNTPlus.ZetaBounds

@[expose] public section

/-!
# Explicit bounds for `ζ`, `ζ'`, `ζ''` and zero-free boxes (card L0-Deriv)

* (a) `norm_zeta_le`: from PNT+ `Zeta0EqZeta` and `ZetaBnd_aux1b`, an explicit bound of `‖ζ s‖`
  on `σ₀ ≤ Re s`, `|Im s| ≤ T₀`, `δ ≤ ‖s - 1‖`; then Cauchy's estimates give
  `norm_deriv_zeta_le` and `norm_deriv_deriv_zeta_le`.
* (b) `ne_zero_of_norm_deriv_le` (order 1) and `ne_zero_of_taylor2` (order 2): a function whose
  value at the centre of a convex box dominates the Lipschitz (resp. Taylor) error has no zero
  in the box; `zeta_ne_zero_of_norm_deriv_le`, `zeta_ne_zero_of_taylor2` for `ζ`.
* (c) `norm_zeta_sub_pole_le`: `‖ζ s - 1/(s-1)‖ ≤ 1/2 + ‖s‖ / Re s` (Euler–Maclaurin, `N = 1`);
  `zeta_ne_zero_near_one`: `ζ s ≠ 0` for `‖s - 1‖ < ρ` whenever `ρ ^ 2 + 5 ρ ≤ 2`
  (best `ρ = (√33 - 5)/2 ≈ 0.3723`), instance `ρ = 37/100`.

All numerical hypotheses are real parameters, to be discharged by `norm_num` or LeanCert.
-/

open Complex Metric Set

namespace ZetaZeros.Deriv

/-! ## (b) Zero-free boxes -/

/-- Order 1: if `‖f'‖ ≤ M` on a convex set `B` of radius `r` about `c ∈ B` and `M r < ‖f c‖`,
then `f` has no zero on `B`. -/
theorem ne_zero_of_norm_deriv_le {f : ℂ → ℂ} {B : Set ℂ} {c : ℂ} {M r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B) (hf : ∀ x ∈ B, DifferentiableAt ℂ f x)
    (hM : ∀ x ∈ B, ‖deriv f x‖ ≤ M) (hr : ∀ z ∈ B, ‖z - c‖ ≤ r) (h : M * r < ‖f c‖) :
    ∀ z ∈ B, f z ≠ 0 := by
  intro z hz hfz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c hc)
  have h1 := hB.norm_image_sub_le_of_norm_deriv_le hf hM hc hz
  rw [hfz, zero_sub, norm_neg] at h1
  have h2 : M * ‖z - c‖ ≤ M * r := mul_le_mul_of_nonneg_left (hr z hz) hM0
  linarith

/-- Taylor at order 2 on a convex set, with the constant `1/2`. -/
theorem norm_taylor2_le {f : ℂ → ℂ} {B : Set ℂ} {c z : ℂ} {M₂ : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B) (hz : z ∈ B)
    (hf : ∀ x ∈ B, DifferentiableAt ℂ f x) (hf' : ∀ x ∈ B, DifferentiableAt ℂ (deriv f) x)
    (hM : ∀ x ∈ B, ‖deriv (deriv f) x‖ ≤ M₂) :
    ‖f z - f c - deriv f c * (z - c)‖ ≤ M₂ / 2 * ‖z - c‖ ^ 2 := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, c + (t : ℂ) * (z - c) ∈ B := by
    intro t ht
    have := hB.add_smul_sub_mem hc hz ht
    simpa [Complex.real_smul] using this
  let φ : ℝ → ℂ := fun t => f (c + t * (z - c)) - f c - t * (z - c) * deriv f c
  let φ' : ℝ → ℂ := fun t => (z - c) * (deriv f (c + t * (z - c)) - deriv f c)
  have hφ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' t) t := by
    intro t ht
    have hin : HasDerivAt (fun u : ℂ => c + u * (z - c)) (z - c) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (z - c)).const_add c
    have h1 : HasDerivAt (fun u : ℂ => f (c + u * (z - c))) (deriv f (c + t * (z - c)) * (z - c))
        (t : ℂ) :=
      (hf _ (hseg t ht)).hasDerivAt.comp (t : ℂ) hin
    have h2 := (h1.sub_const (f c)).sub
      (((hasDerivAt_id (t : ℂ)).mul_const (z - c)).mul_const (deriv f c))
    have h3 : HasDerivAt φ
        (deriv f (c + t * (z - c)) * (z - c) - 1 * (z - c) * deriv f c) t := h2.comp_ofReal
    refine h3.congr_deriv ?_
    show _ = (z - c) * (deriv f (c + t * (z - c)) - deriv f c)
    ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖φ' t‖ ≤ M₂ * ‖z - c‖ ^ 2 * t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have hmv := hB.norm_image_sub_le_of_norm_deriv_le hf' hM hc (hseg t htI)
    have e : c + (t : ℂ) * (z - c) - c = (t : ℂ) * (z - c) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] at hmv
    simp only [φ']
    rw [norm_mul]
    calc ‖z - c‖ * ‖deriv f (c + t * (z - c)) - deriv f c‖
        ≤ ‖z - c‖ * (M₂ * (t * ‖z - c‖)) := mul_le_mul_of_nonneg_left hmv (norm_nonneg _)
      _ = M₂ * ‖z - c‖ ^ 2 * t := by ring
  have hBd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => M₂ / 2 * ‖z - c‖ ^ 2 * (t * t))
      (M₂ * ‖z - c‖ ^ 2 * t) t := by
    intro t
    have := ((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (M₂ / 2 * ‖z - c‖ ^ 2)
    refine this.congr_deriv ?_
    show M₂ / 2 * ‖z - c‖ ^ 2 * (1 * t + t * 1) = _
    ring
  have hfin := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ) (f' := φ')
    (a := 0) (b := 1)
    (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := fun t : ℝ => M₂ / 2 * ‖z - c‖ ^ 2 * (t * t)) (by simp [φ]) hBd hbound
    (x := 1) ⟨zero_le_one, le_rfl⟩
  have e1 : φ 1 = f z - f c - deriv f c * (z - c) := by
    simp only [φ]
    rw [show c + ((1 : ℝ) : ℂ) * (z - c) = z by push_cast; ring]
    push_cast
    ring
  rw [e1] at hfin
  simpa using hfin

/-- Order 2: if `‖f''‖ ≤ M₂` on a convex set `B` of radius `r` about `c ∈ B` and
`‖f' c‖ r + M₂ r² / 2 < ‖f c‖`, then `f` has no zero on `B`. -/
theorem ne_zero_of_taylor2 {f : ℂ → ℂ} {B : Set ℂ} {c : ℂ} {M₂ r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B)
    (hf : ∀ x ∈ B, DifferentiableAt ℂ f x) (hf' : ∀ x ∈ B, DifferentiableAt ℂ (deriv f) x)
    (hM : ∀ x ∈ B, ‖deriv (deriv f) x‖ ≤ M₂) (hr : ∀ z ∈ B, ‖z - c‖ ≤ r)
    (h : ‖deriv f c‖ * r + M₂ / 2 * r ^ 2 < ‖f c‖) :
    ∀ z ∈ B, f z ≠ 0 := by
  intro z hz hfz
  have hM0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM c hc)
  have T := norm_taylor2_le hB hc hz hf hf' hM
  rw [hfz] at T
  have hw0 := norm_nonneg (z - c)
  have hwr := hr z hz
  have hsq : ‖z - c‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hw0 hwr 2
  have htri : ‖f c‖ ≤ ‖(0 : ℂ) - f c - deriv f c * (z - c)‖ + ‖deriv f c * (z - c)‖ := by
    calc ‖f c‖ = ‖-((0 : ℂ) - f c - deriv f c * (z - c)) - deriv f c * (z - c)‖ := by
          congr 1; ring
      _ ≤ ‖-((0 : ℂ) - f c - deriv f c * (z - c))‖ + ‖deriv f c * (z - c)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_neg]
  rw [norm_mul] at htri
  have h3 : ‖deriv f c‖ * ‖z - c‖ ≤ ‖deriv f c‖ * r := mul_le_mul_of_nonneg_left hwr (norm_nonneg _)
  have h4 : M₂ / 2 * ‖z - c‖ ^ 2 ≤ M₂ / 2 * r ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
  linarith

/-! ## Differentiability of `ζ` away from `1` -/

theorem differentiableOn_zeta : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
  fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt

theorem differentiableAt_deriv_zeta {x : ℂ} (hx : x ≠ 1) :
    DifferentiableAt ℂ (deriv riemannZeta) x :=
  (differentiableOn_zeta.deriv isOpen_ne).differentiableAt (isOpen_ne.mem_nhds hx)

/-- Order 1 box lemma for `ζ`. -/
theorem zeta_ne_zero_of_norm_deriv_le {B : Set ℂ} {c : ℂ} {M r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B) (h1 : (1 : ℂ) ∉ B)
    (hM : ∀ x ∈ B, ‖deriv riemannZeta x‖ ≤ M) (hr : ∀ z ∈ B, ‖z - c‖ ≤ r)
    (h : M * r < ‖riemannZeta c‖) : ∀ z ∈ B, riemannZeta z ≠ 0 :=
  ne_zero_of_norm_deriv_le hB hc
    (fun _ hx => differentiableAt_riemannZeta (fun e => h1 (e ▸ hx))) hM hr h

/-- Order 2 box lemma for `ζ`. -/
theorem zeta_ne_zero_of_taylor2 {B : Set ℂ} {c : ℂ} {M₂ r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B) (h1 : (1 : ℂ) ∉ B)
    (hM : ∀ x ∈ B, ‖deriv (deriv riemannZeta) x‖ ≤ M₂) (hr : ∀ z ∈ B, ‖z - c‖ ≤ r)
    (h : ‖deriv riemannZeta c‖ * r + M₂ / 2 * r ^ 2 < ‖riemannZeta c‖) :
    ∀ z ∈ B, riemannZeta z ≠ 0 :=
  ne_zero_of_taylor2 hB hc
    (fun _ hx => differentiableAt_riemannZeta (fun e => h1 (e ▸ hx)))
    (fun _ hx => differentiableAt_deriv_zeta (fun e => h1 (e ▸ hx))) hM hr h

/-! ## (a) Explicit bound for `‖ζ s‖`, then Cauchy -/

theorem sum_range_eq_sum_Icc (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℂ) ^ s := by
  rw [Finset.sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.cast_zero, Complex.zero_cpow hs, div_zero, add_zero, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm 1 i]

/-- **(a)** Euler–Maclaurin of order 1 with `N` terms:
`‖ζ s‖ ≤ ∑_{k=1}^N k^{-σ₀} + N^{1-σ₀}/δ + N^{-σ₀}/2 + (1 + T₀/σ₀) N^{-σ₀}`
for `σ₀ ≤ Re s`, `|Im s| ≤ T₀`, `δ ≤ ‖s - 1‖`. -/
theorem norm_zeta_le (N : ℕ) (hN : 1 ≤ N) {σ₀ T₀ δ : ℝ} (hσ₀ : 0 < σ₀) (hδ : 0 < δ)
    {s : ℂ} (hs : σ₀ ≤ s.re) (ht : |s.im| ≤ T₀) (h1 : δ ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ₀)) + (N : ℝ) ^ (1 - σ₀) / δ
      + (N : ℝ) ^ (-σ₀) / 2 + (1 + T₀ / σ₀) * (N : ℝ) ^ (-σ₀) := by
  have hσ : 0 < s.re := hσ₀.trans_le hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hσ
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1; linarith
  have hN0 : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 ≤ T₀ := (abs_nonneg _).trans ht
  have p1 : (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-σ₀) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have p2 : (N : ℝ) ^ (1 - s.re) ≤ (N : ℝ) ^ (1 - σ₀) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [← Zeta0EqZeta hN0 hσ hs1]
  unfold riemannZeta0
  rw [sum_range_eq_sum_Icc N hs0]
  have hA : ‖∑ k ∈ Finset.Icc 1 N, 1 / (k : ℂ) ^ s‖ ≤ ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ₀) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hk, one_div,
      ← Real.rpow_neg (Nat.cast_nonneg k)]
    exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  have hB : ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ (N : ℝ) ^ (1 - σ₀) / δ := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN0, norm_sub_rev]
    have e : (1 - s).re = 1 - s.re := by simp
    rw [e, div_le_div_iff₀ (by linarith) hδ]
    exact mul_le_mul p2 h1 hδ.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hC : ‖(-(N : ℂ) ^ (-s)) / 2‖ ≤ (N : ℝ) ^ (-σ₀) / 2 := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN0, Complex.neg_re]
    have e : ‖(2 : ℂ)‖ = 2 := by simp
    rw [e]
    linarith
  have hD : ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ (1 + T₀ / σ₀) * (N : ℝ) ^ (-σ₀) := by
    have hI := ZetaBnd_aux1b N hN hσ (t := s.im)
    rw [Complex.re_add_im] at hI
    rw [norm_mul]
    have hsn : ‖s‖ ≤ s.re + T₀ :=
      (Complex.norm_le_abs_re_add_abs_im s).trans (by rw [abs_of_pos hσ]; linarith)
    calc ‖s‖ * ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
        ≤ (s.re + T₀) * ((N : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul hsn hI (norm_nonneg _) (by linarith)
      _ = (1 + T₀ / s.re) * (N : ℝ) ^ (-s.re) := by field_simp
      _ ≤ (1 + T₀ / σ₀) * (N : ℝ) ^ (-σ₀) := by
          refine mul_le_mul ?_ p1 (Real.rpow_nonneg (Nat.cast_nonneg N) _)
            (add_nonneg zero_le_one (div_nonneg hT0 hσ₀.le))
          have := div_le_div_of_nonneg_left hT0 hσ₀ hs
          linarith
  refine (norm_add_le _ _).trans (add_le_add ?_ hD)
  refine (norm_add_le _ _).trans (add_le_add ?_ hC)
  exact (norm_add_le _ _).trans (add_le_add hA hB)

theorem closedBall_subset_ne_one {z : ℂ} {R : ℝ} (h : R < ‖z - 1‖) :
    closedBall z R ⊆ {w : ℂ | w ≠ 1} := by
  intro w hw
  show w ≠ 1
  rintro rfl
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw
  linarith

/-- Cauchy, order 1, for `ζ` on a circle avoiding `1`. -/
theorem norm_deriv_zeta_le_of_sphere {z : ℂ} {R C : ℝ} (hR : 0 < R) (h1 : R < ‖z - 1‖)
    (hC : ∀ w ∈ sphere z R, ‖riemannZeta w‖ ≤ C) : ‖deriv riemannZeta z‖ ≤ C / R :=
  norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (differentiableOn_zeta.diffContOnCl_ball (closedBall_subset_ne_one h1)) hC

/-- Cauchy, order 2, for `ζ` on a circle avoiding `1`. -/
theorem norm_deriv_deriv_zeta_le_of_sphere {z : ℂ} {R C : ℝ} (hR : 0 < R) (h1 : R < ‖z - 1‖)
    (hC : ∀ w ∈ sphere z R, ‖riemannZeta w‖ ≤ C) :
    ‖deriv (deriv riemannZeta) z‖ ≤ 2 * C / R ^ 2 := by
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR
    (differentiableOn_zeta.diffContOnCl_ball (closedBall_subset_ne_one h1)) hC
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  simpa [Nat.factorial] using h

theorem sphere_mem_region {z w : ℂ} {R σ₀ T₀ δ : ℝ} (hw : w ∈ sphere z R)
    (hre : σ₀ + R ≤ z.re) (him : |z.im| + R ≤ T₀) (h1 : δ + R ≤ ‖z - 1‖) :
    σ₀ ≤ w.re ∧ |w.im| ≤ T₀ ∧ δ ≤ ‖w - 1‖ := by
  rw [mem_sphere, dist_eq_norm] at hw
  have a := Complex.abs_re_le_norm (w - z)
  have b := Complex.abs_im_le_norm (w - z)
  rw [hw, Complex.sub_re] at a
  rw [hw, Complex.sub_im] at b
  have c := norm_sub_norm_le (z - 1) (z - w)
  rw [norm_sub_rev z w, hw, show z - 1 - (z - w) = w - 1 by ring] at c
  refine ⟨?_, ?_, ?_⟩
  · have := neg_abs_le (w.re - z.re); linarith
  · have := abs_sub_abs_le_abs_sub w.im z.im; linarith
  · linarith

/-- **(a)** Explicit bound for `‖ζ' z‖`: the circle of radius `R` about `z` stays in the region
of `norm_zeta_le`. -/
theorem norm_deriv_zeta_le (N : ℕ) (hN : 1 ≤ N) {σ₀ T₀ δ R : ℝ} (hσ₀ : 0 < σ₀) (hδ : 0 < δ)
    (hR : 0 < R) {z : ℂ} (hre : σ₀ + R ≤ z.re) (him : |z.im| + R ≤ T₀) (h1 : δ + R ≤ ‖z - 1‖) :
    ‖deriv riemannZeta z‖ ≤ ((∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ₀)) + (N : ℝ) ^ (1 - σ₀) / δ
      + (N : ℝ) ^ (-σ₀) / 2 + (1 + T₀ / σ₀) * (N : ℝ) ^ (-σ₀)) / R :=
  norm_deriv_zeta_le_of_sphere hR (by linarith) fun _ hw => by
    obtain ⟨a, b, c⟩ := sphere_mem_region hw hre him h1
    exact norm_zeta_le N hN hσ₀ hδ a b c

/-- **(a)** Explicit bound for `‖ζ'' z‖`. -/
theorem norm_deriv_deriv_zeta_le (N : ℕ) (hN : 1 ≤ N) {σ₀ T₀ δ R : ℝ} (hσ₀ : 0 < σ₀)
    (hδ : 0 < δ) (hR : 0 < R) {z : ℂ} (hre : σ₀ + R ≤ z.re) (him : |z.im| + R ≤ T₀)
    (h1 : δ + R ≤ ‖z - 1‖) :
    ‖deriv (deriv riemannZeta) z‖ ≤ 2 * ((∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ₀))
      + (N : ℝ) ^ (1 - σ₀) / δ + (N : ℝ) ^ (-σ₀) / 2 + (1 + T₀ / σ₀) * (N : ℝ) ^ (-σ₀)) / R ^ 2 :=
  norm_deriv_deriv_zeta_le_of_sphere hR (by linarith) fun _ hw => by
    obtain ⟨a, b, c⟩ := sphere_mem_region hw hre him h1
    exact norm_zeta_le N hN hσ₀ hδ a b c

/-! ## (a) Approach B: direct bound of `‖ζ' s‖` from PNT+ `ζ₀'` (no Cauchy loss) -/

theorem sum_range_succ_eq_sum_Icc (g : ℕ → ℂ) (h0 : g 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), g n = ∑ k ∈ Finset.Icc 1 N, g k := by
  rw [Finset.sum_range_succ', h0, add_zero, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm 1 i]

/-- The logarithmic integral of `ζ₀'`, after PNT+ `DerivUpperBnd_aux7_*`. -/
theorem norm_log_integral_le (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x : ℂ)‖
      ≤ 1 / s.re ^ 2 * (N : ℝ) ^ (-s.re) + 1 / s.re * (N : ℝ) ^ (-s.re) * Real.log N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  calc ∫ x in Ioi (N : ℝ), ‖(⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x : ℂ)‖
      = ∫ x in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-s.re - 1) * Real.log x := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have h := DerivUpperBnd_aux7_1 (σ := s.re) (t := s.im) (hN1.trans (le_of_lt hx))
        simp only [Complex.re_add_im] at h
        exact h
    _ ≤ ∫ x in Ioi (N : ℝ), x ^ (-s.re - 1) * Real.log x :=
        MeasureTheory.setIntegral_mono_on (DerivUpperBnd_aux7_5 hσ hN1)
          (DerivUpperBnd_aux7_4 hσ hN1) measurableSet_Ioi
          fun x hx => DerivUpperBnd_aux7_2 (hN1.trans (le_of_lt hx))
    _ = 1 / s.re ^ 2 * (N : ℝ) ^ (-s.re) + 1 / s.re * (N : ℝ) ^ (-s.re) * Real.log N :=
        DerivUpperBnd_aux7_integral_eq hN1 hσ

/-- The plain integral of `ζ₀'`, in the form of PNT+ `ZetaBnd_aux1b`. -/
theorem norm_plain_integral_le (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1)‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hI := ZetaBnd_aux1b N hN hσ (t := s.im)
  rw [Complex.re_add_im] at hI
  have e : (fun x : ℝ => (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))
      = fun x : ℝ => (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
    funext x
    rw [div_cpow_eq_cpow_neg, show -(s + 1) = -s - 1 by ring]
  rw [e]
  exact hI

/-- **(a), approach B** Direct bound of `‖ζ' s‖` (Euler–Maclaurin of order 1, differentiated),
for `σ₀ ≤ Re s`, `|Im s| ≤ T₀`, `δ ≤ ‖s - 1‖`. Numerically 3.5 to 9 times sharper than Cauchy
from `norm_zeta_le` (`lab/l0_deriv_direct.py`). -/
theorem norm_deriv_zeta_le_direct (N : ℕ) (hN : 1 ≤ N) {σ₀ T₀ δ : ℝ} (hσ₀ : 0 < σ₀)
    (hδ : 0 < δ) {s : ℂ} (hs : σ₀ ≤ s.re) (ht : |s.im| ≤ T₀) (h1 : δ ≤ ‖s - 1‖) :
    ‖deriv riemannZeta s‖ ≤ (∑ k ∈ Finset.Icc 1 N, Real.log k * (k : ℝ) ^ (-σ₀))
      + (N : ℝ) ^ (1 - σ₀) / δ ^ 2 + Real.log N * (N : ℝ) ^ (1 - σ₀) / δ
      + Real.log N * (N : ℝ) ^ (-σ₀) / 2 + (N : ℝ) ^ (-σ₀) / σ₀
      + (N : ℝ) ^ (-σ₀) * ((1 / σ₀ + T₀ / σ₀ ^ 2) + (1 + T₀ / σ₀) * Real.log N) := by
  have hσ : 0 < s.re := hσ₀.trans_le hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1; linarith
  have hN0 : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 ≤ T₀ := (abs_nonneg _).trans ht
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hd : 0 < ‖s - 1‖ := hδ.trans_le h1
  have hnr : ‖(Real.log N : ℂ)‖ = Real.log N := by
    rw [Complex.norm_real, Real.norm_of_nonneg hL]
  have p0 : 0 ≤ (N : ℝ) ^ (-σ₀) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have p0' : 0 ≤ (N : ℝ) ^ (1 - σ₀) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have p1 : (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-σ₀) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have p2 : (N : ℝ) ^ (1 - s.re) ≤ (N : ℝ) ^ (1 - σ₀) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hre1 : (1 - s).re = 1 - s.re := by simp
  have hn1 : ‖(1 : ℂ) - s‖ = ‖s - 1‖ := norm_sub_rev _ _
  rw [← DerivZeta0EqDerivZeta hN0 hσ hs1, (HasDerivAtZeta0 hN0 hσ hs1).deriv]
  unfold ζ₀'
  rw [sum_range_succ_eq_sum_Icc (fun n : ℕ => -1 / (n : ℂ) ^ s * (Real.log n : ℂ)) (by simp) N]
  have hA : ‖∑ k ∈ Finset.Icc 1 N, -1 / (k : ℂ) ^ s * (Real.log k : ℂ)‖
      ≤ ∑ k ∈ Finset.Icc 1 N, Real.log k * (k : ℝ) ^ (-σ₀) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlk : 0 ≤ Real.log k := Real.log_nonneg hk1
    rw [norm_mul, norm_div, norm_neg, norm_one, Complex.norm_natCast_cpow_of_pos hk,
      Complex.norm_real, Real.norm_of_nonneg hlk, one_div, ← Real.rpow_neg (Nat.cast_nonneg k),
      mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) hlk
  have hB1 : ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ ≤ (N : ℝ) ^ (1 - σ₀) / δ ^ 2 := by
    rw [norm_div, norm_neg, norm_pow, Complex.norm_natCast_cpow_of_pos hN0, hre1, hn1,
      div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul p2 (pow_le_pow_left₀ hδ.le h1 2) (by positivity) p0'
  have hB2 : ‖(Real.log N : ℂ) * (N : ℂ) ^ (1 - s) / (1 - s)‖
      ≤ Real.log N * (N : ℝ) ^ (1 - σ₀) / δ := by
    rw [norm_div, norm_mul, hnr, Complex.norm_natCast_cpow_of_pos hN0, hre1, hn1,
      div_le_div_iff₀ hd hδ]
    exact mul_le_mul (mul_le_mul_of_nonneg_left p2 hL) h1 hδ.le (mul_nonneg hL p0')
  have hC : ‖(Real.log N : ℂ) * (N : ℂ) ^ (-s) / 2‖ ≤ Real.log N * (N : ℝ) ^ (-σ₀) / 2 := by
    rw [norm_div, norm_mul, hnr, Complex.norm_natCast_cpow_of_pos hN0, Complex.neg_re]
    have e : ‖(2 : ℂ)‖ = 2 := by simp
    rw [e]
    have := mul_le_mul_of_nonneg_left p1 hL
    linarith
  have hD1 : ‖1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1)‖
      ≤ (N : ℝ) ^ (-σ₀) / σ₀ := by
    rw [one_mul]
    refine (norm_plain_integral_le N hN hσ).trans ?_
    rw [div_le_div_iff₀ hσ hσ₀]
    exact mul_le_mul p1 hs hσ₀.le p0
  have hD2 : ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x : ℂ)‖
      ≤ (N : ℝ) ^ (-σ₀) * ((1 / σ₀ + T₀ / σ₀ ^ 2) + (1 + T₀ / σ₀) * Real.log N) := by
    rw [norm_mul]
    have hsn : ‖s‖ ≤ s.re + T₀ :=
      (Complex.norm_le_abs_re_add_abs_im s).trans (by rw [abs_of_pos hσ]; linarith)
    have hK := norm_log_integral_le N hN hσ
    have hmono : (1 / s.re + T₀ / s.re ^ 2) + (1 + T₀ / s.re) * Real.log N
        ≤ (1 / σ₀ + T₀ / σ₀ ^ 2) + (1 + T₀ / σ₀) * Real.log N := by
      have a1 : 1 / s.re ≤ 1 / σ₀ := one_div_le_one_div_of_le hσ₀ hs
      have a2 : T₀ / s.re ^ 2 ≤ T₀ / σ₀ ^ 2 :=
        div_le_div_of_nonneg_left hT0 (by positivity) (pow_le_pow_left₀ hσ₀.le hs 2)
      have a3 : T₀ / s.re ≤ T₀ / σ₀ := div_le_div_of_nonneg_left hT0 hσ₀ hs
      have a4 : (1 + T₀ / s.re) * Real.log N ≤ (1 + T₀ / σ₀) * Real.log N :=
        mul_le_mul_of_nonneg_right (by linarith) hL
      linarith
    calc ‖s‖ * ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x : ℂ)‖
        ≤ (s.re + T₀) * (1 / s.re ^ 2 * (N : ℝ) ^ (-s.re)
            + 1 / s.re * (N : ℝ) ^ (-s.re) * Real.log N) :=
          mul_le_mul hsn hK (norm_nonneg _) (by linarith)
      _ = (N : ℝ) ^ (-s.re) * ((1 / s.re + T₀ / s.re ^ 2) + (1 + T₀ / s.re) * Real.log N) := by
          field_simp
      _ ≤ (N : ℝ) ^ (-σ₀) * ((1 / σ₀ + T₀ / σ₀ ^ 2) + (1 + T₀ / σ₀) * Real.log N) :=
          mul_le_mul p1 hmono (by positivity) p0
  have h2 := (norm_add_le _ _).trans (add_le_add hB1 hB2)
  have h4 := (norm_add_le _ _).trans (add_le_add hD1 hD2)
  refine (norm_add_le _ _).trans ?_
  refine le_trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hA h2)) hC)) h4) ?_
  linarith

/-! ## (b′) Boxes for a split `f = P + R` (scheme S4H: `P` main term, `‖R‖ ≤ ε`) -/

/-- Pointwise core: on a convex `B` of radius `r` about `c`, with `‖P'‖ ≤ L` on `B`,
`‖R z‖ ≤ ε` and `0 < ‖P c‖ - L r - ε`, one has `P z + R z ≠ 0`. -/
theorem add_ne_zero_of_box_at {P R : ℂ → ℂ} {B : Set ℂ} {c z : ℂ} {L ε r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B) (hz : z ∈ B) (hP : ∀ x ∈ B, DifferentiableAt ℂ P x)
    (hL : ∀ x ∈ B, ‖deriv P x‖ ≤ L) (hRz : ‖R z‖ ≤ ε) (hr : ‖z - c‖ ≤ r)
    (h : 0 < ‖P c‖ - L * r - ε) : P z + R z ≠ 0 := by
  intro h0
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL c hc)
  have h1 := hB.norm_image_sub_le_of_norm_deriv_le hP hL hc hz
  have h2 : L * ‖z - c‖ ≤ L * r := mul_le_mul_of_nonneg_left hr hL0
  have h5 : ‖P z‖ = ‖R z‖ := by rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
  have h4 : ‖P c‖ ≤ ‖P z‖ + ‖P z - P c‖ := by
    calc ‖P c‖ = ‖P z - (P z - P c)‖ := by congr 1; ring
      _ ≤ ‖P z‖ + ‖P z - P c‖ := norm_sub_le _ _
  linarith

/-- **(b′)** Box lemma for any `f` that splits as `P + R` on the box. -/
theorem ne_zero_of_box_split {f P R : ℂ → ℂ} {B : Set ℂ} {c : ℂ} {L ε r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B) (hf : ∀ z ∈ B, f z = P z + R z)
    (hP : ∀ x ∈ B, DifferentiableAt ℂ P x) (hL : ∀ x ∈ B, ‖deriv P x‖ ≤ L)
    (hR : ∀ z ∈ B, ‖R z‖ ≤ ε) (hr : ∀ z ∈ B, ‖z - c‖ ≤ r) (h : 0 < ‖P c‖ - L * r - ε) :
    ∀ z ∈ B, f z ≠ 0 := fun z hz => by
  rw [hf z hz]
  exact add_ne_zero_of_box_at hB hc hz hP hL (hR z hz) (hr z hz) h

/-- **(b′)** The same for `ζ`. -/
theorem zeta_ne_zero_of_box_split {P R : ℂ → ℂ} {B : Set ℂ} {c : ℂ} {L ε r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B) (hf : ∀ z ∈ B, riemannZeta z = P z + R z)
    (hP : ∀ x ∈ B, DifferentiableAt ℂ P x) (hL : ∀ x ∈ B, ‖deriv P x‖ ≤ L)
    (hR : ∀ z ∈ B, ‖R z‖ ≤ ε) (hr : ∀ z ∈ B, ‖z - c‖ ≤ r) (h : 0 < ‖P c‖ - L * r - ε) :
    ∀ z ∈ B, riemannZeta z ≠ 0 :=
  ne_zero_of_box_split hB hc hf hP hL hR hr h

/-- **(b′)** Near `s = 1`, for `h(s) = (s - 1) ζ(s) = P s + R s`. In Lean `(s - 1) * ζ s = 0` at
`s = 1` (junk value), so the split and the bound on `R` are only asked off `1`. -/
theorem zeta_ne_zero_of_box_split_near_one {P R : ℂ → ℂ} {B : Set ℂ} {c : ℂ} {L ε r : ℝ}
    (hB : Convex ℝ B) (hc : c ∈ B)
    (hf : ∀ z ∈ B, z ≠ 1 → (z - 1) * riemannZeta z = P z + R z)
    (hP : ∀ x ∈ B, DifferentiableAt ℂ P x) (hL : ∀ x ∈ B, ‖deriv P x‖ ≤ L)
    (hR : ∀ z ∈ B, z ≠ 1 → ‖R z‖ ≤ ε) (hr : ∀ z ∈ B, ‖z - c‖ ≤ r)
    (h : 0 < ‖P c‖ - L * r - ε) : ∀ z ∈ B, z ≠ 1 → riemannZeta z ≠ 0 := by
  intro z hz hz1 hζ
  have := add_ne_zero_of_box_at hB hc hz hP hL (hR z hz hz1) (hr z hz) h
  rw [← hf z hz hz1, hζ, mul_zero] at this
  exact this rfl

/-! ## (a′) Cauchy on the remainder `R` alone -/

/-- **(a′)** `‖R‖ ≤ ε` on the circle of radius `ρ` and `R` holomorphic on the closed disc give
`‖R' z‖ ≤ ε / ρ`. -/
theorem norm_deriv_le_of_closedBall {R : ℂ → ℂ} {z : ℂ} {ρ ε : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ R (closedBall z ρ)) (hR : ∀ w ∈ sphere z ρ, ‖R w‖ ≤ ε) :
    ‖deriv R z‖ ≤ ε / ρ :=
  norm_deriv_le_of_forall_mem_sphere_norm_le hρ (hd.diffContOnCl_ball subset_rfl) hR

/-- **(a′)** Same hypotheses: `‖R'' z‖ ≤ 2 ε / ρ²`. -/
theorem norm_deriv_deriv_le_of_closedBall {R : ℂ → ℂ} {z : ℂ} {ρ ε : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ R (closedBall z ρ)) (hR : ∀ w ∈ sphere z ρ, ‖R w‖ ≤ ε) :
    ‖deriv (deriv R) z‖ ≤ 2 * ε / ρ ^ 2 := by
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρ
    (hd.diffContOnCl_ball subset_rfl) hR
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  simpa [Nat.factorial] using h

/-- **(a′)** For `R = ζ - P` with `P` holomorphic on the closed disc (which avoids `1`):
`‖ζ' z - P' z‖ ≤ ε / ρ`. -/
theorem norm_deriv_zeta_sub_le {P : ℂ → ℂ} {z : ℂ} {ρ ε : ℝ} (hρ : 0 < ρ) (h1 : ρ < ‖z - 1‖)
    (hP : DifferentiableOn ℂ P (closedBall z ρ))
    (hR : ∀ w ∈ sphere z ρ, ‖riemannZeta w - P w‖ ≤ ε) :
    ‖deriv riemannZeta z - deriv P z‖ ≤ ε / ρ := by
  have hd : DifferentiableOn ℂ (fun w => riemannZeta w - P w) (closedBall z ρ) :=
    (differentiableOn_zeta.mono (closedBall_subset_ne_one h1)).sub hP
  have h := norm_deriv_le_of_closedBall hρ hd hR
  have hz1 : z ≠ 1 := closedBall_subset_ne_one h1 (mem_closedBall_self hρ.le)
  rw [deriv_fun_sub (differentiableAt_riemannZeta hz1)
    (hP.differentiableAt (closedBall_mem_nhds z hρ))] at h
  exact h

/-- **(a′)** For `R = ζ - P`: `‖ζ'' z - P'' z‖ ≤ 2 ε / ρ²`. -/
theorem norm_deriv_deriv_zeta_sub_le {P : ℂ → ℂ} {z : ℂ} {ρ ε : ℝ} (hρ : 0 < ρ)
    (h1 : ρ < ‖z - 1‖) (hP : DifferentiableOn ℂ P (closedBall z ρ))
    (hR : ∀ w ∈ sphere z ρ, ‖riemannZeta w - P w‖ ≤ ε) :
    ‖deriv (deriv riemannZeta) z - deriv (deriv P) z‖ ≤ 2 * ε / ρ ^ 2 := by
  have hd : DifferentiableOn ℂ (fun w => riemannZeta w - P w) (closedBall z ρ) :=
    (differentiableOn_zeta.mono (closedBall_subset_ne_one h1)).sub hP
  have h := norm_deriv_deriv_le_of_closedBall hρ hd hR
  have hz1 : z ≠ 1 := closedBall_subset_ne_one h1 (mem_closedBall_self hρ.le)
  have hball : ∀ w ∈ ball z ρ, deriv (fun w => riemannZeta w - P w) w
      = deriv riemannZeta w - deriv P w := fun w hw =>
    deriv_fun_sub (differentiableAt_riemannZeta
        (closedBall_subset_ne_one h1 (ball_subset_closedBall hw)))
      (hP.differentiableAt
        (Filter.mem_of_superset (isOpen_ball.mem_nhds hw) ball_subset_closedBall))
  have heq : deriv (fun w => riemannZeta w - P w) =ᶠ[nhds z]
      fun w => deriv riemannZeta w - deriv P w :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hρ)) hball
  have hPd : DifferentiableAt ℂ (deriv P) z :=
    ((hP.mono ball_subset_closedBall).deriv isOpen_ball).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hρ))
  rw [heq.deriv_eq, deriv_fun_sub (differentiableAt_deriv_zeta hz1) hPd] at h
  exact h

/-! ## (c) Neighbourhood of `s = 1` -/

/-- **(c)** `‖ζ s - 1/(s-1)‖ ≤ 1/2 + ‖s‖ / Re s` for `Re s > 0`, `s ≠ 1`. -/
theorem norm_zeta_sub_pole_le {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - 1 / (s - 1)‖ ≤ 1 / 2 + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hσ
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsub' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [← Zeta0EqZeta (N := 1) one_pos hσ hs1]
  unfold riemannZeta0
  have hI := ZetaBnd_aux1b 1 le_rfl hσ (t := s.im)
  rw [Complex.re_add_im] at hI
  simp only [Nat.cast_one, Real.one_rpow] at hI
  set J := ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  have e : (∑ n ∈ Finset.range (1 + 1), 1 / (n : ℂ) ^ s) + (-((1 : ℕ) : ℂ) ^ (1 - s)) / (1 - s)
      + (-((1 : ℕ) : ℂ) ^ (-s)) / 2 + s * J - 1 / (s - 1) = 1 / 2 + s * J := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Complex.zero_cpow hs0, Complex.one_cpow, div_zero, zero_add]
    field_simp
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2, norm_mul]
  have hJ' : ‖J‖ ≤ 1 / s.re := by
    rw [hJ]
    simpa using hI
  calc 1 / 2 + ‖s‖ * ‖J‖ ≤ 1 / 2 + ‖s‖ * (1 / s.re) := by
        gcongr
    _ = 1 / 2 + ‖s‖ / s.re := by ring

/-- **(c)** Zero-free disc about `s = 1`: `ζ s ≠ 0` for `0 < ‖s - 1‖ < ρ` when `ρ² + 5ρ ≤ 2`. -/
theorem zeta_ne_zero_near_one {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ^ 2 + 5 * ρ ≤ 2) {s : ℂ}
    (hs : ‖s - 1‖ < ρ) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hd0 : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hρ1 : ρ < 1 := by nlinarith
  have hre : 1 - ‖s - 1‖ ≤ s.re := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    have := neg_abs_le (s.re - 1)
    linarith
  have hσ : 0 < s.re := by linarith
  have hnorm : ‖s‖ ≤ 1 + ‖s - 1‖ := by
    have := norm_sub_norm_le s 1
    rw [norm_one] at this
    linarith
  have key := norm_zeta_sub_pole_le hσ hs1
  rw [hz, zero_sub, norm_neg, norm_div, norm_one] at key
  generalize ‖s - 1‖ = d at *
  have hq : ‖s‖ / s.re ≤ (1 + d) / (1 - d) := by
    rw [div_le_div_iff₀ hσ (by linarith)]
    have h0 : 0 ≤ ‖s‖ := norm_nonneg _
    nlinarith
  have key2 : 1 / d ≤ 1 / 2 + (1 + d) / (1 - d) := by linarith
  have hd1 : (1 : ℝ) - d ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by linarith))
  rw [show (1 : ℝ) / 2 + (1 + d) / (1 - d) = (1 - d + 2 * (1 + d)) / (2 * (1 - d)) by
    field_simp] at key2
  rw [div_le_div_iff₀ hd0 (by linarith)] at key2
  nlinarith [mul_pos (sub_pos.mpr hs) (add_pos hρ hd0)]

/-- **(c)** The card's form, with `ρ = 37/100` (`(√33 - 5)/2 ≈ 0.3723` is the supremum). -/
theorem zeta_ne_zero_near_one_strip {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re < 1) (_h3 : 0 ≤ s.im)
    (hs : ‖s - 1‖ < 37 / 100) : riemannZeta s ≠ 0 := by
  refine zeta_ne_zero_near_one (ρ := 37 / 100) (by norm_num) (by norm_num) hs ?_
  rintro rfl
  simp at h2

end ZetaZeros.Deriv

#print axioms ZetaZeros.Deriv.ne_zero_of_norm_deriv_le
#print axioms ZetaZeros.Deriv.ne_zero_of_taylor2
#print axioms ZetaZeros.Deriv.zeta_ne_zero_of_norm_deriv_le
#print axioms ZetaZeros.Deriv.zeta_ne_zero_of_taylor2
#print axioms ZetaZeros.Deriv.norm_zeta_le
#print axioms ZetaZeros.Deriv.norm_deriv_zeta_le
#print axioms ZetaZeros.Deriv.norm_deriv_deriv_zeta_le
#print axioms ZetaZeros.Deriv.norm_deriv_zeta_le_direct
#print axioms ZetaZeros.Deriv.ne_zero_of_box_split
#print axioms ZetaZeros.Deriv.zeta_ne_zero_of_box_split
#print axioms ZetaZeros.Deriv.zeta_ne_zero_of_box_split_near_one
#print axioms ZetaZeros.Deriv.norm_deriv_le_of_closedBall
#print axioms ZetaZeros.Deriv.norm_deriv_deriv_le_of_closedBall
#print axioms ZetaZeros.Deriv.norm_deriv_zeta_sub_le
#print axioms ZetaZeros.Deriv.norm_deriv_deriv_zeta_sub_le
#print axioms ZetaZeros.Deriv.norm_zeta_sub_pole_le
#print axioms ZetaZeros.Deriv.zeta_ne_zero_near_one
#print axioms ZetaZeros.Deriv.zeta_ne_zero_near_one_strip
