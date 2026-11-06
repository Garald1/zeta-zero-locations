/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Certified logarithms of integers, checked by the kernel

`log((b + a)/(b - a)) = Σ_j 2/(2j+1) (a/b)^{2j+1}` (Mathlib `Real.hasSum_log_sub_log_of_abs_lt_one`).
The first `J` terms are `(a/b) · U/V` with `(U, V) = hornerUV a b J 0` in exact natural numbers;
the tail is at most `2 (a/b)^{2J+1} / ((2J+1)(1 - (a/b)^2))`.

* `log2Check L2 J`: `|log 2 - L2/2^160| ≤ 2^-158` (from `a = 1`, `b = 3`);
* `logCheck L2 p k L J`: given the above, `|log p - L/2^128| ≤ 2^-126`, using
  `log p = k log 2 + log((b + a)/(b - a))` with `a = p - 2^k`, `b = p + 2^k`.
-/

namespace ZetaCert

/-- Horner form of `Σ_{i<n} 2/(2(j+i)+1) · (a/b)^{2i}` as `U / V`. -/
def hornerUV (a b : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 1)
  | n + 1, j =>
    let r := hornerUV a b n (j + 1)
    (2 * b * b * r.2 + (2 * j + 1) * a * a * r.1, (2 * j + 1) * b * b * r.2)

theorem hornerUV_spec (a b : ℕ) (hb : 0 < b) : ∀ n j : ℕ,
    0 < (hornerUV a b n j).2 ∧
    ((hornerUV a b n j).1 : ℝ) / (hornerUV a b n j).2 =
      ∑ i ∈ Finset.range n, 2 / (2 * ((j + i : ℕ) : ℝ) + 1) * ((a : ℝ) / b) ^ (2 * i) := by
  intro n
  induction n with
  | zero => intro j; simp [hornerUV]
  | succ n ih =>
    intro j
    obtain ⟨h0, h1⟩ := ih (j + 1)
    simp only [hornerUV]
    refine ⟨by positivity, ?_⟩
    rw [Finset.sum_range_succ']
    have hshift : ∑ i ∈ Finset.range n, 2 / (2 * ((j + (i + 1) : ℕ) : ℝ) + 1) * ((a : ℝ) / b) ^ (2 * (i + 1))
        = ((a : ℝ) / b) ^ 2 * ∑ i ∈ Finset.range n, 2 / (2 * ((j + 1 + i : ℕ) : ℝ) + 1) * ((a : ℝ) / b) ^ (2 * i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [show j + (i + 1) = j + 1 + i by ring, show 2 * (i + 1) = 2 * i + 2 by ring, pow_add]; ring
    rw [hshift, ← h1]
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hV : (0 : ℝ) < (hornerUV a b n (j + 1)).2 := by exact_mod_cast h0
    push_cast
    field_simp
    ring

/-- The `atanh` series with its tail bound. -/
theorem log_ratio_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (J : ℕ) :
    let S := ∑ j ∈ Finset.range J, (2 : ℝ) * (1 / (2 * j + 1)) * x ^ (2 * j + 1)
    S ≤ Real.log (1 + x) - Real.log (1 - x) ∧
      Real.log (1 + x) - Real.log (1 - x) ≤ S + 2 * x ^ (2 * J + 1) / ((2 * J + 1) * (1 - x ^ 2)) := by
  intro S
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  set f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1)
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [f]; positivity
  have hsum := hs.summable
  have htail := (hsum.sum_add_tsum_nat_add J)
  rw [hs.tsum_eq] at htail
  -- tail is nonnegative and bounded by a geometric series
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hg : ∀ k, f (k + J) ≤ 2 / (2 * J + 1) * x ^ (2 * J + 1) * (x ^ 2) ^ k := by
    intro k
    simp only [f]
    have h1 : (1 : ℝ) / (2 * ((k + J : ℕ) : ℝ) + 1) ≤ 1 / (2 * J + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have h2 : x ^ (2 * (k + J) + 1) = x ^ (2 * J + 1) * (x ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [h2]
    have : 0 ≤ x ^ (2 * J + 1) * (x ^ 2) ^ k := by positivity
    calc 2 * (1 / (2 * ((k + J : ℕ) : ℝ) + 1)) * (x ^ (2 * J + 1) * (x ^ 2) ^ k)
        ≤ 2 * (1 / (2 * J + 1)) * (x ^ (2 * J + 1) * (x ^ 2) ^ k) := by gcongr
      _ = _ := by ring
  have hgs : Summable (fun k : ℕ => 2 / (2 * J + 1) * x ^ (2 * J + 1) * (x ^ 2) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hx2).mul_left _
  have htle : ∑' k, f (k + J) ≤ 2 / (2 * J + 1) * x ^ (2 * J + 1) * (1 - x ^ 2)⁻¹ := by
    rw [← tsum_geometric_of_lt_one (by positivity) hx2, ← tsum_mul_left]
    exact (hsum.comp_injective (add_left_injective J)).tsum_le_tsum hg hgs
  have ht0 : 0 ≤ ∑' k, f (k + J) := tsum_nonneg fun k => hf0 _
  have hS : S = ∑ i ∈ Finset.range J, f i := rfl
  constructor
  · rw [← htail, hS]; linarith
  · rw [← htail, hS]
    have : 2 / (2 * J + 1) * x ^ (2 * J + 1) * (1 - x ^ 2)⁻¹ =
        2 * x ^ (2 * J + 1) / ((2 * J + 1) * (1 - x ^ 2)) := by
      have : (1 - x ^ 2) ≠ 0 := by linarith
      field_simp
    linarith

/-- The partial sum through `hornerUV`. -/
theorem partial_sum_eq (a b J : ℕ) (hb : 0 < b) :
    ∑ j ∈ Finset.range J, (2 : ℝ) * (1 / (2 * j + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) =
      (a : ℝ) * (hornerUV a b J 0).1 / (b * (hornerUV a b J 0).2) := by
  obtain ⟨h0, h1⟩ := hornerUV_spec a b hb J 0
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hV : (0 : ℝ) < (hornerUV a b J 0).2 := by exact_mod_cast h0
  have : (a : ℝ) * (hornerUV a b J 0).1 / (b * (hornerUV a b J 0).2) =
      (a : ℝ) / b * (((hornerUV a b J 0).1 : ℝ) / (hornerUV a b J 0).2) := by field_simp
  rw [this, h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Nat.zero_add]
  rw [pow_succ, pow_mul]; ring

/-- `log 2` to within `2^-158`: `L2 / 2^160`. Cross-multiplied, all in `ℕ`.
`S = a U / (b V)`, tail `≤ 2 a^{2J+1} / ((2J+1) b^{2J-1} (b^2 - a^2))` with `a = 1`, `b = 3`. -/
def log2Check (L2 J : ℕ) : Bool :=
  let r := hornerUV 1 3 J 0
  let bV := 3 * r.2
  let W := (2 * J + 1) * 3 ^ (2 * J + 1) * 8
  -- upper: S + T ≤ L2/2^160 + 2^-158  ⟸  2^160 U W + 2^161 bV ≤ (L2 + 4) bV W
  Nat.ble (2 ^ 160 * r.1 * W + 2 ^ 161 * 9 * bV) ((L2 + 4) * bV * W) &&
  -- lower: L2/2^160 - 2^-158 ≤ S  ⟸  L2 bV ≤ 2^160 U + 4 bV
  Nat.ble (L2 * bV) (2 ^ 160 * r.1 + 4 * bV)

theorem log2Check_spec {L2 J : ℕ} (h : log2Check L2 J = true) :
    |Real.log 2 - L2 / 2 ^ 160| ≤ 1 / 2 ^ 158 := by
  unfold log2Check at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hV0, -⟩ := hornerUV_spec 1 3 (by norm_num) J 0
  set U := (hornerUV 1 3 J 0).1
  set V := (hornerUV 1 3 J 0).2
  have hb := log_ratio_bounds (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) J
  simp only at hb
  have hlog : Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hlog] at hb
  have hS := partial_sum_eq 1 3 J (by norm_num)
  simp only [Nat.cast_one, Nat.cast_ofNat] at hS
  rw [hS] at hb
  obtain ⟨b1, b2⟩ := hb
  have hVR : (0 : ℝ) < V := by exact_mod_cast hV0
  have h1R : (2 ^ 160 * U * ((2 * J + 1) * 3 ^ (2 * J + 1) * 8) + 2 ^ 161 * 9 * (3 * V) : ℝ) ≤
      (L2 + 4) * (3 * V) * ((2 * J + 1) * 3 ^ (2 * J + 1) * 8) := by exact_mod_cast h1
  have h2R : ((L2 : ℝ) * (3 * V)) ≤ 2 ^ 160 * U + 4 * (3 * V) := by exact_mod_cast h2
  have hW : (0 : ℝ) < (2 * J + 1) * 3 ^ (2 * J + 1) * 8 := by positivity
  have htail : 2 * (1 / 3 : ℝ) ^ (2 * J + 1) / ((2 * J + 1) * (1 - (1 / 3) ^ 2)) =
      18 / ((2 * J + 1) * 3 ^ (2 * J + 1) * 8) := by
    rw [div_pow, one_pow]; field_simp; ring
  rw [htail] at b2
  rw [abs_le]
  constructor
  · -- lower bound on log 2 - L2/2^160
    have : (L2 : ℝ) / 2 ^ 160 - 1 / 2 ^ 158 ≤ 1 * U / (3 * V) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · have : 1 * U / (3 * V) + 18 / ((2 * J + 1) * 3 ^ (2 * J + 1) * 8) ≤ (L2 : ℝ) / 2 ^ 160 + 1 / 2 ^ 158 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `|log p - L / 2^128| ≤ 2^-126`, from `|log 2 - L2/2^160| ≤ 2^-158`, with
`a = p - 2^k`, `b = p + 2^k` (requires `2^k ≤ p < 2^(k+1)` up to the check `a < b`). -/
def logCheck (L2 p k L J : ℕ) : Bool :=
  let a := p - 2 ^ k
  let b := p + 2 ^ k
  let r := hornerUV a b J 0
  let bV := b * r.2
  let W := (2 * J + 1) * b ^ (2 * J - 1) * (b * b - a * a)
  Nat.ble 1 J && Nat.ble (2 ^ k) p &&
  Nat.ble (k * (L2 + 4) * bV * W + 2 ^ 160 * (a * r.1) * W + 2 ^ 161 * a ^ (2 * J + 1) * bV)
    ((L * 2 ^ 32 + 2 ^ 34) * bV * W) &&
  Nat.ble (L * 2 ^ 32 * bV + 4 * k * bV) (k * L2 * bV + 2 ^ 160 * (a * r.1) + 2 ^ 34 * bV)

theorem logCheck_spec {L2 p k L J : ℕ} (h2 : |Real.log 2 - L2 / 2 ^ 160| ≤ 1 / 2 ^ 158)
    (h : logCheck L2 p k L J = true) : |Real.log p - L / 2 ^ 128| ≤ 1 / 2 ^ 126 := by
  unfold logCheck at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨hJ, hkp⟩, h1⟩, h3⟩ := h
  set a := p - 2 ^ k with ha
  set b := p + 2 ^ k with hb
  have hp : 0 < p := lt_of_lt_of_le (by positivity) hkp
  have h2k : 0 < 2 ^ k := by positivity
  have hb0 : 0 < b := by omega
  have hab : a < b := by omega
  obtain ⟨hV0, -⟩ := hornerUV_spec a b hb0 J 0
  set U := (hornerUV a b J 0).1
  set V := (hornerUV a b J 0).2
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have haR : (0 : ℝ) ≤ a := by positivity
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hx0 : (0 : ℝ) ≤ a / b := by positivity
  have hx1 : (a : ℝ) / b < 1 := by rw [div_lt_one hbR]; exact habR
  have hbd := log_ratio_bounds hx0 hx1 J
  simp only at hbd
  -- log(1 + x) - log(1 - x) = log p - k log 2
  have hlog : Real.log (1 + a / b) - Real.log (1 - a / b) = Real.log p - k * Real.log 2 := by
    have e1 : (1 : ℝ) + a / b = 2 * p / b := by
      rw [ha, hb]; push_cast [Nat.cast_sub hkp]; field_simp; ring
    have e2 : (1 : ℝ) - a / b = 2 ^ (k + 1) / b := by
      rw [ha, hb]; push_cast [Nat.cast_sub hkp]; field_simp; ring
    rw [e1, e2, ← Real.log_div (by positivity) (by positivity)]
    rw [show (2 * (p : ℝ) / b) / (2 ^ (k + 1) / b) = p / 2 ^ k by field_simp; ring]
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [hlog, partial_sum_eq a b J hb0] at hbd
  obtain ⟨b1, b2⟩ := hbd
  have hVR : (0 : ℝ) < V := by exact_mod_cast hV0
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hsq : (0 : ℝ) < (b : ℝ) * b - a * a := by nlinarith
  have hsqN : ((b * b - a * a : ℕ) : ℝ) = (b : ℝ) * b - a * a := by
    rw [Nat.cast_sub (Nat.mul_self_le_mul_self hab.le)]; push_cast; ring
  have hWpos : (0 : ℝ) < (2 * J + 1) * (b : ℝ) ^ (2 * J - 1) * ((b : ℝ) * b - a * a) := by positivity
  have htail : 2 * ((a : ℝ) / b) ^ (2 * J + 1) / ((2 * J + 1) * (1 - ((a : ℝ) / b) ^ 2)) =
      2 * (a : ℝ) ^ (2 * J + 1) / ((2 * J + 1) * (b : ℝ) ^ (2 * J - 1) * ((b : ℝ) * b - a * a)) := by
    have hbJ : (b : ℝ) ^ (2 * J + 1) = (b : ℝ) ^ (2 * J - 1) * (b * b) := by
      rw [← pow_two, ← pow_add]; congr 1; omega
    rw [div_pow, div_pow]
    rw [hbJ]
    field_simp
  rw [htail] at b2
  have h1R : ((k : ℝ) * (L2 + 4) * (b * V) * ((2 * J + 1) * (b : ℝ) ^ (2 * J - 1) * ((b : ℝ) * b - a * a))
      + 2 ^ 160 * (a * U) * ((2 * J + 1) * (b : ℝ) ^ (2 * J - 1) * ((b : ℝ) * b - a * a))
      + 2 ^ 161 * (a : ℝ) ^ (2 * J + 1) * (b * V)) ≤
      ((L : ℝ) * 2 ^ 32 + 2 ^ 34) * (b * V) * ((2 * J + 1) * (b : ℝ) ^ (2 * J - 1) * ((b : ℝ) * b - a * a)) := by
    have := h1
    rw [← hsqN]
    exact_mod_cast this
  have h3R : (L : ℝ) * 2 ^ 32 * (b * V) + 4 * k * (b * V) ≤ k * L2 * (b * V) + 2 ^ 160 * (a * U) + 2 ^ 34 * (b * V) := by
    exact_mod_cast h3
  rw [abs_le] at h2 ⊢
  obtain ⟨l2a, l2b⟩ := h2
  have hk0 : (0 : ℝ) ≤ k := by positivity
  set Wr := (2 * J + 1) * (b : ℝ) ^ (2 * J - 1) * ((b : ℝ) * b - a * a)
  have hbV : (0 : ℝ) < b * V := by positivity
  constructor
  · -- lower: log p ≥ k (L2 - 4)/2^160 + S ≥ L/2^128 - 2^-126
    have hlow : (L : ℝ) / 2 ^ 128 - 1 / 2 ^ 126 ≤ k * ((L2 : ℝ) / 2 ^ 160 - 1 / 2 ^ 158) + a * U / (b * V) := by
      have e : (L : ℝ) / 2 ^ 128 - 1 / 2 ^ 126 - (k * ((L2 : ℝ) / 2 ^ 160 - 1 / 2 ^ 158) + a * U / (b * V)) =
          ((L : ℝ) * 2 ^ 32 * (b * V) + 4 * k * (b * V) - (k * L2 * (b * V) + 2 ^ 160 * (a * U) + 2 ^ 34 * (b * V)))
            / (2 ^ 160 * (b * V)) := by field_simp; ring
      have : ((L : ℝ) * 2 ^ 32 * (b * V) + 4 * k * (b * V) - (k * L2 * (b * V) + 2 ^ 160 * (a * U) + 2 ^ 34 * (b * V)))
            / (2 ^ 160 * (b * V)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    have : k * ((L2 : ℝ) / 2 ^ 160 - 1 / 2 ^ 158) ≤ k * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left _ hk0; linarith
    linarith
  · have hup : k * ((L2 : ℝ) / 2 ^ 160 + 1 / 2 ^ 158) + a * U / (b * V) + 2 * (a : ℝ) ^ (2 * J + 1) / Wr
        ≤ (L : ℝ) / 2 ^ 128 + 1 / 2 ^ 126 := by
      have e : k * ((L2 : ℝ) / 2 ^ 160 + 1 / 2 ^ 158) + a * U / (b * V) + 2 * (a : ℝ) ^ (2 * J + 1) / Wr
          - ((L : ℝ) / 2 ^ 128 + 1 / 2 ^ 126) =
          ((k : ℝ) * (L2 + 4) * (b * V) * Wr + 2 ^ 160 * (a * U) * Wr + 2 ^ 161 * (a : ℝ) ^ (2 * J + 1) * (b * V)
            - ((L : ℝ) * 2 ^ 32 + 2 ^ 34) * (b * V) * Wr) / (2 ^ 160 * (b * V) * Wr) := by
        field_simp; ring
      have : ((k : ℝ) * (L2 + 4) * (b * V) * Wr + 2 ^ 160 * (a * U) * Wr + 2 ^ 161 * (a : ℝ) ^ (2 * J + 1) * (b * V)
            - ((L : ℝ) * 2 ^ 32 + 2 ^ 34) * (b * V) * Wr) / (2 ^ 160 * (b * V) * Wr) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    have : k * Real.log 2 ≤ k * ((L2 : ℝ) / 2 ^ 160 + 1 / 2 ^ 158) := by
      apply mul_le_mul_of_nonneg_left _ hk0; linarith
    linarith

end ZetaCert
