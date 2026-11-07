/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/

module

@[expose] public section

/-!
# Kernel evaluation of the rational part of Euler–Maclaurin (Lean core only)

At `s = 1/2 + iγ` with `γ = G / 2^80`, i.e. `s = (2^79 + iG) / 2^80`:

* `pochZ G m`, `dpochZ G m` are Gaussian integers with `pochZ G m = 2^(80m) poch(s, m)` and
  `dpochZ G m = 2^(80m) dpoch(s, m)` (`ZetaCert/Eval/EMRestSound.lean`);
* `remR`, `remR1` are the real and imaginary parts of `Rm N k s` and `R1m N k s` at scale
  `2^128`, each component floor-rounded `k + 2` times.

`bern` lists `(num, den)` of `B_0, B_1, …` (checked against Mathlib's `bernoulli` once).
-/

namespace ZetaCert.Eval

/-- Gaussian integers. -/
abbrev GZ := Int × Int

@[inline] def gmul (a b : GZ) : GZ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
@[inline] def gadd (a b : GZ) : GZ := (a.1 + b.1, a.2 + b.2)
@[inline] def gsmul (c : Int) (a : GZ) : GZ := (c * a.1, c * a.2)

/-- `2^80 (s + m)`. -/
@[inline] def facZ (G m : Nat) : GZ := (((2 ^ 79 + m * 2 ^ 80 : Nat) : Int), (G : Int))

def pochZ (G : Nat) : Nat → GZ
  | 0 => (1, 0)
  | m + 1 => gmul (pochZ G m) (facZ G m)

def dpochZ (G : Nat) : Nat → GZ
  | 0 => (0, 0)
  | m + 1 => gadd (gmul (dpochZ G m) (facZ G m)) (gsmul (2 ^ 80) (pochZ G m))

/-- `n!` (Lean core has no factorial). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The Bernoulli entry `B_j` as `(num, den)` (default `(0, 1)`). -/
def bernAt (bern : List (Int × Nat)) (j : Nat) : Int × Nat := bern.getD j (0, 1)

/-- `⌊β_{2i} · z / N^{2i+1} · 2^128⌋` componentwise, for `z = pochZ` or `dpochZ` at `2i+1`,
where `β_{2i} = B_{2i+2} / (2i+2)!`. -/
def emTermZ (N : Nat) (bern : List (Int × Nat)) (i : Nat) (z : GZ) : GZ :=
  let b := bernAt bern (2 * i + 2)
  let den : Int := ((b.2 * fact (2 * i + 2) * 2 ^ (80 * (2 * i + 1)) * N ^ (2 * i + 1) : Nat) : Int)
  ((b.1 * z.1 * 2 ^ 128) / den, (b.1 * z.2 * 2 ^ 128) / den)

/-- `Σ_{i ≤ k}` of `emTermZ` applied to `pochZ`. -/
def sumP (N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  ((List.range (k + 1)).map (fun i => emTermZ N bern i (pochZ G (2 * i + 1)))).foldr gadd (0, 0)

/-- `Σ_{i ≤ k}` of `emTermZ` applied to `dpochZ`. -/
def sumD (N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  ((List.range (k + 1)).map (fun i => emTermZ N bern i (dpochZ G (2 * i + 1)))).foldr gadd (0, 0)

/-- `|2^80 (s - 1)|^2 = 2^158 + G^2`. -/
@[inline] def W2 (G : Nat) : Nat := 2 ^ 158 + G * G

/-- `Rm N k s` at scale `2^128`. -/
def remR (N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  let sp := sumP N G bern k
  let w := ((W2 G : Nat) : Int)
  ((-((N * 2 ^ 287 : Nat) : Int)) / w - 2 ^ 127 + sp.1,
   (-((N * G * 2 ^ 208 : Nat) : Int)) / w + sp.2)

/-- `R1m N k s` at scale `2^128`. -/
def remR1 (N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  let sd := sumD N G bern k
  let w2 := ((W2 G * W2 G : Nat) : Int)
  ((-(((N * 2 ^ 288 : Nat) : Int) * ((2 ^ 158 : Int) - (G : Int) * G))) / w2 + sd.1,
   (-((N * G * 2 ^ 368 : Nat) : Int)) / w2 + sd.2)

/-! ## General real part `σ = S / 2^80` -/

/-- `2^80 (s + m)` at `s = (S + iG)/2^80`. -/
@[inline] def facZS (S G m : Nat) : GZ := (((S + m * 2 ^ 80 : Nat) : Int), (G : Int))

def pochZS (S G : Nat) : Nat → GZ
  | 0 => (1, 0)
  | m + 1 => gmul (pochZS S G m) (facZS S G m)

def dpochZS (S G : Nat) : Nat → GZ
  | 0 => (0, 0)
  | m + 1 => gadd (gmul (dpochZS S G m) (facZS S G m)) (gsmul (2 ^ 80) (pochZS S G m))

def sumPS (S N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  ((List.range (k + 1)).map (fun i => emTermZ N bern i (pochZS S G (2 * i + 1)))).foldr gadd (0, 0)

def sumDS (S N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  ((List.range (k + 1)).map (fun i => emTermZ N bern i (dpochZS S G (2 * i + 1)))).foldr gadd (0, 0)

/-- `2^80 (σ - 1)`. -/
@[inline] def wsZ (S : Nat) : Int := (S : Int) - 2 ^ 80

/-- `|2^80 (s - 1)|^2`. -/
@[inline] def W2S (S G : Nat) : Nat := (wsZ S).natAbs * (wsZ S).natAbs + G * G

/-- `Rm N k s` at scale `2^128`, `s = (S + iG)/2^80`. -/
def remRS (S N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  let sp := sumPS S N G bern k
  let w := ((W2S S G : Nat) : Int)
  ((((N * 2 ^ 208 : Nat) : Int) * wsZ S) / w - 2 ^ 127 + sp.1,
   (-((N * G * 2 ^ 208 : Nat) : Int)) / w + sp.2)

/-- `R1m N k s` at scale `2^128`. -/
def remR1S (S N G : Nat) (bern : List (Int × Nat)) (k : Nat) : GZ :=
  let sd := sumDS S N G bern k
  let w2 := ((W2S S G * W2S S G : Nat) : Int)
  ((-(((N * 2 ^ 288 : Nat) : Int) * (wsZ S * wsZ S - (G : Int) * G))) / w2 + sd.1,
   (((N * G * 2 ^ 289 : Nat) : Int) * wsZ S) / w2 + sd.2)

end ZetaCert.Eval
