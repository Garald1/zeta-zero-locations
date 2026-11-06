/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import ZetaCert.Eval.Core

/-!
# Soundness of the fixed-point primitives of `ZetaCert.Eval.Core`

`vO X = (X - 2^192) / 2^128` is the value of an offset number, `vP x = x / 2^128` that of a
plain one. Each primitive is exact or floor-rounded with error below one ulp `u = 2^-128`,
provided the exact real result stays in range (a hypothesis on that real number).
-/

set_option exponentiation.threshold 600

namespace ZetaCert.Eval

/-- The unit in the last place, `2^-128`. -/
noncomputable def u : ℝ := 1 / 2 ^ 128

theorem O_eq : O = 2 ^ 192 := by norm_num [O]
theorem O2_eq : O2 = 2 ^ 193 := by norm_num [O2]
theorem ONE_eq : ONE = 2 ^ 128 := by norm_num [ONE]
theorem KO_eq : KO = 2 ^ 384 + 2 ^ 320 := by norm_num [KO]
theorem OP_eq : OP = 2 ^ 320 := by norm_num [OP]
theorem EIGHTH_eq : EIGHTH = 2 ^ 125 := by norm_num [EIGHTH]

/-- Value of an offset number. -/
noncomputable def vO (X : ℕ) : ℝ := ((X : ℝ) - 2 ^ 192) / 2 ^ 128

/-- Value of a plain number. -/
noncomputable def vP (x : ℕ) : ℝ := (x : ℝ) / 2 ^ 128

theorem u_pos : 0 < u := by unfold u; positivity

theorem vP_nonneg (x : ℕ) : 0 ≤ vP x := by unfold vP; positivity

/-- `X` in terms of its value. -/
theorem cast_eq_vO (X : ℕ) : (X : ℝ) = vO X * 2 ^ 128 + 2 ^ 192 := by
  unfold vO; field_simp; ring

theorem cast_eq_vP (x : ℕ) : (x : ℝ) = vP x * 2 ^ 128 := by
  unfold vP; field_simp

theorem vO_eq_of_cast {X : ℕ} {r : ℝ} (h : (X : ℝ) = r * 2 ^ 128 + 2 ^ 192) : vO X = r := by
  unfold vO; rw [h]; field_simp; ring

theorem vP_eq_of_cast {x : ℕ} {r : ℝ} (h : (x : ℝ) = r * 2 ^ 128) : vP x = r := by
  unfold vP; rw [h]; field_simp

theorem vP_ONE : vP ONE = 1 := by
  unfold vP ONE; norm_num

theorem vO_ofPlain (x : ℕ) : vO (ofPlain x) = vP x := by
  apply vO_eq_of_cast
  unfold ofPlain; rw [O_eq]; push_cast; rw [cast_eq_vP x]; ring

theorem vO_O : vO O = 0 := by
  apply vO_eq_of_cast; rw [O_eq]; push_cast; ring

theorem vO_ONE_O : vO (Nat.add ONE O) = 1 := by
  apply vO_eq_of_cast; rw [O_eq, ONE_eq]; push_cast; ring

theorem vO_ONE_add_O : vO (ONE + O) = 1 := vO_ONE_O

private theorem nat_sub_cast {a b : ℕ} (h : (b : ℝ) ≤ a) : ((a - b : ℕ) : ℝ) = a - b := by
  have : b ≤ a := by exact_mod_cast h
  push_cast [this]; ring

theorem vO_addO {X Y : ℕ} (h : -2 ^ 64 ≤ vO X + vO Y) : vO (addO X Y) = vO X + vO Y := by
  apply vO_eq_of_cast
  have hX := cast_eq_vO X
  have hY := cast_eq_vO Y
  have hle : ((O : ℕ) : ℝ) ≤ ((X + Y : ℕ) : ℝ) := by
    rw [O_eq]; push_cast; rw [hX, hY]; nlinarith
  show ((Nat.sub (Nat.add X Y) O : ℕ) : ℝ) = _
  rw [show Nat.sub (Nat.add X Y) O = (X + Y) - O from rfl, nat_sub_cast hle, O_eq]
  push_cast; rw [hX, hY]; ring

theorem vO_subO {X Y : ℕ} (h : -2 ^ 64 ≤ vO X - vO Y) : vO (subO X Y) = vO X - vO Y := by
  apply vO_eq_of_cast
  have hX := cast_eq_vO X
  have hY := cast_eq_vO Y
  have hle : ((Y : ℕ) : ℝ) ≤ ((X + O : ℕ) : ℝ) := by
    rw [O_eq]; push_cast; rw [hX, hY]; nlinarith
  show ((Nat.sub (Nat.add X O) Y : ℕ) : ℝ) = _
  rw [show Nat.sub (Nat.add X O) Y = (X + O) - Y from rfl, nat_sub_cast hle, O_eq]
  push_cast; rw [hX, hY]; ring

theorem vO_negO {X : ℕ} (h : vO X ≤ 2 ^ 64) : vO (negO X) = -vO X := by
  apply vO_eq_of_cast
  have hX := cast_eq_vO X
  have hle : ((X : ℕ) : ℝ) ≤ ((O2 : ℕ) : ℝ) := by
    rw [O2_eq]; push_cast; rw [hX]; nlinarith
  show ((Nat.sub O2 X : ℕ) : ℝ) = _
  rw [show Nat.sub O2 X = O2 - X from rfl, nat_sub_cast hle, O2_eq]
  push_cast; rw [hX]; ring

/-- Floor division by `2^k`, as reals: `n / 2^k - 1 < ⌊n / 2^k⌋ ≤ n / 2^k`. -/
theorem shiftRight_bounds (n k : ℕ) :
    (n : ℝ) / 2 ^ k - 1 < ((n >>> k : ℕ) : ℝ) ∧ ((n >>> k : ℕ) : ℝ) ≤ (n : ℝ) / 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow]
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hk : 0 < 2 ^ k := by positivity
  constructor
  · have h := Nat.lt_div_mul_add (a := n) hk
    have h' : (n : ℝ) < ((n / 2 ^ k : ℕ) : ℝ) * 2 ^ k + 2 ^ k := by exact_mod_cast h
    rw [sub_lt_iff_lt_add, div_lt_iff₀ h2]; linarith
  · rw [le_div_iff₀ h2]
    exact_mod_cast Nat.div_mul_le_self n (2 ^ k)

/-- Floor division by a positive natural, as reals. -/
theorem div_bounds (n j : ℕ) (hj : 0 < j) :
    (n : ℝ) / j - 1 < ((n / j : ℕ) : ℝ) ∧ ((n / j : ℕ) : ℝ) ≤ (n : ℝ) / j := by
  have h2 : (0 : ℝ) < j := by exact_mod_cast hj
  constructor
  · have h := Nat.lt_div_mul_add (a := n) hj
    have h' : (n : ℝ) < ((n / j : ℕ) : ℝ) * j + j := by exact_mod_cast h
    rw [sub_lt_iff_lt_add, div_lt_iff₀ h2]; linarith
  · rw [le_div_iff₀ h2]
    exact_mod_cast Nat.div_mul_le_self n j

/-- From `a 2^256 + 2^320` floor-divided by `2^128` to the rounding bounds on values. -/
theorem round_bounds {a z : ℝ}
    (hb : (a * 2 ^ 256 + 2 ^ 320) / 2 ^ 128 - 1 < z * 2 ^ 128 + 2 ^ 192 ∧
      z * 2 ^ 128 + 2 ^ 192 ≤ (a * 2 ^ 256 + 2 ^ 320) / 2 ^ 128) :
    a - u < z ∧ z ≤ a := by
  have e : (a * 2 ^ 256 + 2 ^ 320) / (2:ℝ) ^ 128 = a * 2 ^ 128 + 2 ^ 192 := by
    field_simp
  rw [e] at hb
  obtain ⟨h1, h2⟩ := hb
  unfold u
  constructor
  · have : (a - 1 / 2 ^ 128) * 2 ^ 128 < z * 2 ^ 128 := by
      have e2 : (a - 1 / 2 ^ 128) * (2:ℝ) ^ 128 = a * 2 ^ 128 - 1 := by field_simp
      rw [e2]; linarith
    exact lt_of_mul_lt_mul_right this (by positivity)
  · have : z * 2 ^ 128 ≤ a * 2 ^ 128 := by linarith
    exact le_of_mul_le_mul_right this (by positivity)

theorem vO_mulO {X Y : ℕ} (h : -2 ^ 64 ≤ vO X * vO Y) :
    vO X * vO Y - u < vO (mulO X Y) ∧ vO (mulO X Y) ≤ vO X * vO Y := by
  have hX := cast_eq_vO X
  have hY := cast_eq_vO Y
  set x := vO X
  set y := vO Y
  have hle : (((X + Y) <<< 192 : ℕ) : ℝ) ≤ ((X * Y + KO : ℕ) : ℝ) := by
    rw [Nat.shiftLeft_eq, KO_eq]; push_cast; rw [hX, hY]; nlinarith
  have hval : ((Nat.sub (Nat.add (Nat.mul X Y) KO) (Nat.shiftLeft (Nat.add X Y) 192) : ℕ) : ℝ)
      = (x * y) * 2 ^ 256 + 2 ^ 320 := by
    show (((X * Y + KO) - ((X + Y) <<< 192) : ℕ) : ℝ) = _
    rw [nat_sub_cast hle, Nat.shiftLeft_eq, KO_eq]; push_cast; rw [hX, hY]; ring
  have hb := shiftRight_bounds
    (Nat.sub (Nat.add (Nat.mul X Y) KO) (Nat.shiftLeft (Nat.add X Y) 192)) 128
  rw [show (Nat.sub (Nat.add (Nat.mul X Y) KO) (Nat.shiftLeft (Nat.add X Y) 192)) >>> 128
    = mulO X Y from rfl, hval, cast_eq_vO (mulO X Y)] at hb
  exact round_bounds hb

theorem vO_mulOP {X y : ℕ} (h : -2 ^ 64 ≤ vO X * vP y) :
    vO X * vP y - u < vO (mulOP X y) ∧ vO (mulOP X y) ≤ vO X * vP y := by
  have hX := cast_eq_vO X
  have hy := cast_eq_vP y
  set x := vO X
  set w := vP y
  have hle : ((y <<< 192 : ℕ) : ℝ) ≤ ((X * y + OP : ℕ) : ℝ) := by
    rw [Nat.shiftLeft_eq, OP_eq]; push_cast; rw [hX, hy]; nlinarith
  have hval : ((Nat.sub (Nat.add (Nat.mul X y) OP) (Nat.shiftLeft y 192) : ℕ) : ℝ)
      = (x * w) * 2 ^ 256 + 2 ^ 320 := by
    show (((X * y + OP) - (y <<< 192) : ℕ) : ℝ) = _
    rw [nat_sub_cast hle, Nat.shiftLeft_eq, OP_eq]; push_cast; rw [hX, hy]; ring
  have hb := shiftRight_bounds
    (Nat.sub (Nat.add (Nat.mul X y) OP) (Nat.shiftLeft y 192)) 128
  rw [show (Nat.sub (Nat.add (Nat.mul X y) OP) (Nat.shiftLeft y 192)) >>> 128
    = mulOP X y from rfl, hval, cast_eq_vO (mulOP X y)] at hb
  exact round_bounds hb

/-- Generic rounding step: `n` floor-divided, value bounds at scale `2^128`. -/
theorem round_bounds' {a z : ℝ}
    (hb : a * 2 ^ 128 - 1 < z * 2 ^ 128 ∧ z * 2 ^ 128 ≤ a * 2 ^ 128) :
    a - u < z ∧ z ≤ a := by
  obtain ⟨h1, h2⟩ := hb
  unfold u
  constructor
  · have : (a - 1 / 2 ^ 128) * 2 ^ 128 < z * 2 ^ 128 := by
      have e2 : (a - 1 / 2 ^ 128) * (2:ℝ) ^ 128 = a * 2 ^ 128 - 1 := by field_simp
      rw [e2]; linarith
    exact lt_of_mul_lt_mul_right this (by positivity)
  · exact le_of_mul_le_mul_right h2 (by positivity)

theorem vP_mulPP (x y : ℕ) :
    vP x * vP y - u < vP (mulPP x y) ∧ vP (mulPP x y) ≤ vP x * vP y := by
  have hb := shiftRight_bounds (Nat.mul x y) 128
  have hxy : ((Nat.mul x y : ℕ) : ℝ) / 2 ^ 128 = vP x * vP y * 2 ^ 128 := by
    show ((x * y : ℕ) : ℝ) / 2 ^ 128 = _
    push_cast; rw [cast_eq_vP x, cast_eq_vP y]; field_simp
  rw [show Nat.mul x y >>> 128 = mulPP x y from rfl, hxy, cast_eq_vP (mulPP x y)] at hb
  exact round_bounds' ⟨by linarith [hb.1], hb.2⟩

theorem vO_divO (X : ℕ) {j : ℕ} (hj : 0 < j) :
    vO X / j - u < vO (divO X j) ∧ vO (divO X j) ≤ vO X / j := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hb := div_bounds (Nat.add X (Nat.mul (Nat.sub j 1) O)) j hj
  have hn : ((Nat.add X (Nat.mul (Nat.sub j 1) O) : ℕ) : ℝ) / j
      = vO X / j * 2 ^ 128 + 2 ^ 192 := by
    show ((X + (j - 1) * O : ℕ) : ℝ) / j = _
    rw [O_eq]; push_cast [Nat.cast_sub (Nat.one_le_of_lt hj)]; rw [cast_eq_vO X]
    field_simp; ring
  rw [show Nat.add X (Nat.mul (Nat.sub j 1) O) / j = divO X j from rfl, hn,
    cast_eq_vO (divO X j)] at hb
  exact round_bounds' ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- Plain floor division by a positive natural. -/
theorem vP_div (x : ℕ) {j : ℕ} (hj : 0 < j) :
    vP x / j - u < vP (x / j) ∧ vP (x / j) ≤ vP x / j := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  obtain ⟨h1, h2⟩ := div_bounds x j hj
  unfold vP u
  constructor
  · have e : ((x : ℝ) / 2 ^ 128 / j - 1 / 2 ^ 128) = ((x : ℝ) / j - 1) / 2 ^ 128 := by
      field_simp
    rw [e]; exact div_lt_div_of_pos_right h1 (by positivity)
  · rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right h2 (by positivity)

end ZetaCert.Eval
