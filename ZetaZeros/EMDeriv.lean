/-
Vendored from https://github.com/antoine-olivier/rh-up-to-15-lean at commit
dec8fa913b6c972c2d16f4d23f54d2174cef7718, file ZetaZeros/EMDeriv.lean (Apache License 2.0,
see LICENSE-rh-up-to-15-lean). Local modifications: the PNT+ import is redirected to the copy
vendored in zeta23 (Zeta23.FromPNTPlus.ZetaBounds); any further changes are marked "(port)".
-/
import ZetaZeros.EM2

/-!
# First and second derivatives of the Euler–Maclaurin main term `emMain N k`

Explicit forms (`emMain1`, `emMain2`), with the derivatives of `poch s m = s (s+1) ⋯ (s+m-1)`
given by the recursions `dpoch (m+1) = dpoch m · (s+m) + poch m` and
`ddpoch (m+1) = ddpoch m · (s+m) + 2 dpoch m`.

* `hasDerivAt_emMain`: `s ≠ 0`, `s ≠ 1` ⇒ `HasDerivAt (emMain N k) (emMain1 N k s) s`.
* `hasDerivAt_emMain1`: `s ≠ 1` ⇒ `HasDerivAt (emMain1 N k) (emMain2 N k s) s`.
* `deriv_deriv_emMain`: `deriv (deriv (emMain N k)) s = emMain2 N k s`.
-/

open Complex Filter Topology

namespace ZetaZeros.EMDeriv

open ZetaZeros.EM

/-! ## `poch` and its derivatives -/

/-- Derivative of `w ↦ poch w m` at `s`. -/
noncomputable def dpoch (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 => dpoch s m * (s + m) + poch s m

/-- Second derivative of `w ↦ poch w m` at `s`. -/
noncomputable def ddpoch (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 => ddpoch s m * (s + m) + 2 * dpoch s m

theorem poch_zero (s : ℂ) : poch s 0 = 1 := by simp [poch]

theorem poch_succ (s : ℂ) (m : ℕ) : poch s (m + 1) = poch s m * (s + m) := by
  simp [poch, Finset.prod_range_succ]

theorem hasDerivAt_poch (s : ℂ) (m : ℕ) : HasDerivAt (fun w => poch w m) (dpoch s m) s := by
  induction m with
  | zero =>
    simp only [poch_zero, dpoch]
    exact hasDerivAt_const s (1 : ℂ)
  | succ m ih =>
    have hf : (fun w => poch w (m + 1)) = fun w => poch w m * (w + m) := by
      funext w
      exact poch_succ w m
    rw [hf]
    have h2 : HasDerivAt (fun w : ℂ => w + (m : ℂ)) 1 s := (hasDerivAt_id' (x := s)).add_const _
    refine (ih.mul h2).congr_deriv ?_
    simp only [dpoch]
    ring

theorem hasDerivAt_dpoch (s : ℂ) (m : ℕ) : HasDerivAt (fun w => dpoch w m) (ddpoch s m) s := by
  induction m with
  | zero =>
    simp only [dpoch, ddpoch]
    exact hasDerivAt_const s (0 : ℂ)
  | succ m ih =>
    have hf : (fun w => dpoch w (m + 1)) = fun w => dpoch w m * (w + m) + poch w m := by
      funext w
      rfl
    rw [hf]
    have h2 : HasDerivAt (fun w : ℂ => w + (m : ℂ)) 1 s := (hasDerivAt_id' (x := s)).add_const _
    refine ((ih.mul h2).add (hasDerivAt_poch s m)).congr_deriv ?_
    simp only [ddpoch]
    ring

/-! ## Powers of `N` -/

theorem hasDerivAt_natCast_cpow_neg (N : ℕ) (hN : 0 < N) (s : ℂ) :
    HasDerivAt (fun w : ℂ => (N : ℂ) ^ (-w)) (-(Complex.log N) * (N : ℂ) ^ (-s)) s := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hf : HasDerivAt (fun w : ℂ => -w) (-1) s := (hasDerivAt_id' (x := s)).neg
  refine (hf.const_cpow (Or.inl hN0)).congr_deriv ?_
  ring

theorem hasDerivAt_natCast_cpow_one_sub (N : ℕ) (hN : 0 < N) (s : ℂ) :
    HasDerivAt (fun w : ℂ => (N : ℂ) ^ (1 - w)) (-(Complex.log N) * (N : ℂ) ^ (1 - s)) s := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hf : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := by
    simpa using (hasDerivAt_id' (x := s)).const_sub (1 : ℂ)
  refine (hf.const_cpow (Or.inl hN0)).congr_deriv ?_
  ring

theorem hasDerivAt_natCast_cpow_neg_add (N : ℕ) (hN : 0 < N) (a s : ℂ) :
    HasDerivAt (fun w : ℂ => (N : ℂ) ^ (-(w + a))) (-(Complex.log N) * (N : ℂ) ^ (-(s + a))) s := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hf : HasDerivAt (fun w : ℂ => -(w + a)) (-1) s := ((hasDerivAt_id' (x := s)).add_const a).neg
  refine (hf.const_cpow (Or.inl hN0)).congr_deriv ?_
  ring

/-! ## The four pieces of `emMain` -/

/-- Derivative of `w ↦ 1 / n ^ w` (`0` for `n = 0`, since `Complex.log 0 = 0`). -/
noncomputable def A1 (n : ℕ) (s : ℂ) : ℂ := -(Complex.log n) * (n : ℂ) ^ (-s)

noncomputable def A2 (n : ℕ) (s : ℂ) : ℂ := Complex.log n ^ 2 * (n : ℂ) ^ (-s)

theorem hasDerivAt_A0 (n : ℕ) {s : ℂ} (hs0 : s ≠ 0) :
    HasDerivAt (fun w : ℂ => 1 / (n : ℂ) ^ w) (A1 n s) s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hev : (fun w : ℂ => 1 / ((0 : ℕ) : ℂ) ^ w) =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [isOpen_ne.mem_nhds hs0] with w hw
      have hw' : w ≠ 0 := hw
      simp [Complex.zero_cpow hw']
    have hA : A1 0 s = 0 := by simp [A1]
    rw [hA]
    exact (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq hev
  · have hf : (fun w : ℂ => 1 / (n : ℂ) ^ w) = fun w => (n : ℂ) ^ (-w) := by
      funext w
      rw [Complex.cpow_neg, one_div]
    rw [hf]
    exact hasDerivAt_natCast_cpow_neg n hn s

theorem hasDerivAt_A1 (n : ℕ) (s : ℂ) : HasDerivAt (A1 n) (A2 n s) s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : A1 0 = fun _ => 0 := by
      funext w
      simp [A1]
    have h2 : A2 0 s = 0 := by simp [A2]
    rw [h, h2]
    exact hasDerivAt_const s (0 : ℂ)
  · have := (hasDerivAt_natCast_cpow_neg n hn s).const_mul (-(Complex.log n))
    refine this.congr_deriv ?_
    simp only [A2]
    ring

/-- Derivative of the pole term `N^(1-s)/(s-1)`. -/
noncomputable def pole1 (N : ℕ) (s : ℂ) : ℂ :=
  -((N : ℂ) ^ (1 - s)) * (Complex.log N / (s - 1) + 1 / (s - 1) ^ 2)

noncomputable def pole2 (N : ℕ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (1 - s) * (Complex.log N ^ 2 / (s - 1) + 2 * Complex.log N / (s - 1) ^ 2
    + 2 / (s - 1) ^ 3)

theorem hasDerivAt_pole {N : ℕ} (hN : 0 < N) {s : ℂ} (hs1 : s ≠ 1) :
    HasDerivAt (fun w : ℂ => (N : ℂ) ^ (1 - w) / (w - 1)) (pole1 N s) s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hd : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id' (x := s)).sub_const 1
  refine ((hasDerivAt_natCast_cpow_one_sub N hN s).div hd h1).congr_deriv ?_
  simp only [pole1]
  field_simp
  ring

theorem hasDerivAt_pole1 {N : ℕ} (hN : 0 < N) {s : ℂ} (hs1 : s ≠ 1) :
    HasDerivAt (pole1 N) (pole2 N s) s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hd : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id' (x := s)).sub_const 1
  have hg1 : HasDerivAt (fun w : ℂ => Complex.log N / (w - 1))
      ((0 * (s - 1) - Complex.log N * 1) / (s - 1) ^ 2) s :=
    (hasDerivAt_const s (Complex.log N)).div hd h1
  have hg2 : HasDerivAt (fun w : ℂ => 1 / (w - 1) ^ 2)
      ((0 * (s - 1) ^ 2 - 1 * ((2 : ℕ) * (s - 1) ^ (2 - 1) * 1)) / ((s - 1) ^ 2) ^ 2) s :=
    (hasDerivAt_const s (1 : ℂ)).div (hd.pow 2) (pow_ne_zero 2 h1)
  have hp := (hasDerivAt_natCast_cpow_one_sub N hN s).neg
  refine (hp.mul (hg1.add hg2)).congr_deriv ?_
  simp only [pole2, Pi.add_apply, Pi.neg_apply]
  field_simp
  ring

/-- Bernoulli coefficient of `emTerm N s j`. -/
noncomputable def beta (j : ℕ) : ℂ := (bernoulli (j + 1 + 1) : ℂ) / ((j + 1 + 1).factorial : ℂ)

noncomputable def emTerm1 (N : ℕ) (s : ℂ) (j : ℕ) : ℂ :=
  beta j * (dpoch s (j + 1) - Complex.log N * poch s (j + 1)) * (N : ℂ) ^ (-(s + (j + 1 : ℕ)))

noncomputable def emTerm2 (N : ℕ) (s : ℂ) (j : ℕ) : ℂ :=
  beta j * (ddpoch s (j + 1) - 2 * Complex.log N * dpoch s (j + 1)
    + Complex.log N ^ 2 * poch s (j + 1)) * (N : ℂ) ^ (-(s + (j + 1 : ℕ)))

theorem hasDerivAt_emTerm {N : ℕ} (hN : 0 < N) (s : ℂ) (j : ℕ) :
    HasDerivAt (fun w => emTerm N w j) (emTerm1 N s j) s := by
  have hE := hasDerivAt_natCast_cpow_neg_add N hN (((j + 1 : ℕ) : ℂ)) s
  have hp := (hasDerivAt_poch s (j + 1)).const_mul (beta j)
  refine (hp.mul hE).congr_deriv ?_
  simp only [emTerm1]
  ring

theorem hasDerivAt_emTerm1 {N : ℕ} (hN : 0 < N) (s : ℂ) (j : ℕ) :
    HasDerivAt (fun w => emTerm1 N w j) (emTerm2 N s j) s := by
  have hE := hasDerivAt_natCast_cpow_neg_add N hN (((j + 1 : ℕ) : ℂ)) s
  have hq : HasDerivAt (fun w => dpoch w (j + 1) - Complex.log N * poch w (j + 1))
      (ddpoch s (j + 1) - Complex.log N * dpoch s (j + 1)) s :=
    (hasDerivAt_dpoch s (j + 1)).sub ((hasDerivAt_poch s (j + 1)).const_mul _)
  refine ((hq.const_mul (beta j)).mul hE).congr_deriv ?_
  simp only [emTerm2]
  ring

/-! ## `emMain` -/

/-- First derivative of `emMain N k`. -/
noncomputable def emMain1 (N k : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), A1 n s) + pole1 N s - (-(Complex.log N) * (N : ℂ) ^ (-s)) / 2
    + ∑ i ∈ Finset.range (k + 1), emTerm1 N s (2 * i)

/-- Second derivative of `emMain N k`. -/
noncomputable def emMain2 (N k : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), A2 n s) + pole2 N s
    - (-(Complex.log N) * (-(Complex.log N) * (N : ℂ) ^ (-s))) / 2
    + ∑ i ∈ Finset.range (k + 1), emTerm2 N s (2 * i)

theorem hasDerivAt_emMain {N : ℕ} (hN : 0 < N) (k : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    HasDerivAt (emMain N k) (emMain1 N k s) s := by
  have h1 := HasDerivAt.fun_sum (u := Finset.range (N + 1)) (A := fun n (w : ℂ) => 1 / (n : ℂ) ^ w)
    (fun n _ => hasDerivAt_A0 n hs0)
  have h2 := hasDerivAt_pole hN hs1
  have h3 := (hasDerivAt_natCast_cpow_neg N hN s).div_const 2
  have h4 := HasDerivAt.fun_sum (u := Finset.range (k + 1)) (A := fun i (w : ℂ) => emTerm N w (2 * i))
    (fun i _ => hasDerivAt_emTerm hN s (2 * i))
  exact ((h1.add h2).sub h3).add h4

theorem hasDerivAt_emMain1 {N : ℕ} (hN : 0 < N) (k : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    HasDerivAt (emMain1 N k) (emMain2 N k s) s := by
  have h1 := HasDerivAt.fun_sum (u := Finset.range (N + 1)) (A := fun n (w : ℂ) => A1 n w)
    (fun n _ => hasDerivAt_A1 n s)
  have h2 := hasDerivAt_pole1 hN hs1
  have h3 := ((hasDerivAt_natCast_cpow_neg N hN s).const_mul (-(Complex.log N))).div_const 2
  have h4 := HasDerivAt.fun_sum (u := Finset.range (k + 1))
    (A := fun i (w : ℂ) => emTerm1 N w (2 * i)) (fun i _ => hasDerivAt_emTerm1 hN s (2 * i))
  exact ((h1.add h2).sub h3).add h4

theorem deriv_emMain {N : ℕ} (hN : 0 < N) (k : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv (emMain N k) s = emMain1 N k s :=
  (hasDerivAt_emMain hN k hs0 hs1).deriv

theorem deriv_deriv_emMain {N : ℕ} (hN : 0 < N) (k : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv (deriv (emMain N k)) s = emMain2 N k s := by
  have hmem : s ∈ {x : ℂ | x ≠ 0} ∩ {x : ℂ | x ≠ 1} := ⟨hs0, hs1⟩
  have hev : deriv (emMain N k) =ᶠ[𝓝 s] emMain1 N k := by
    filter_upwards [(isOpen_ne.inter isOpen_ne).mem_nhds hmem] with w hw
    exact (hasDerivAt_emMain hN k hw.1 hw.2).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_emMain1 hN k hs1).deriv

theorem differentiableAt_emMain {N : ℕ} (hN : 0 < N) (k : ℕ) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (emMain N k) s :=
  (hasDerivAt_emMain hN k hs0 hs1).differentiableAt

end ZetaZeros.EMDeriv

#print axioms ZetaZeros.EMDeriv.hasDerivAt_emMain
#print axioms ZetaZeros.EMDeriv.hasDerivAt_emMain1
#print axioms ZetaZeros.EMDeriv.deriv_deriv_emMain
