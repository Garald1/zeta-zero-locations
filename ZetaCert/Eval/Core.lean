/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Kernel evaluator: fixed-point core (Lean core only, no Mathlib)

Everything here is meant to be reduced by the kernel (`decide +kernel`), so it only uses explicit
`Nat` operations, which the kernel evaluates with GMP.

**Representation.** A signed real `x` with `|x| < 2^64` is stored as the natural number
`X = ⌊x · 2^128⌋ + 2^192` ("offset form", scale `2^-128`, offset `2^192`). A nonnegative real is
sometimes stored "plain": `X = ⌊x · 2^128⌋`. The literals below are
`O = 2^192`, `O2 = 2^193`, `ONE = 2^128`, `KO = 2^384 + 2^320`, `OP = 2^320`.

The soundness statements are in `ZetaCert/Eval/CoreSound.lean`.
-/

namespace ZetaCert.Eval

/-- `2^192`, the offset. -/
def O : Nat := 6277101735386680763835789423207666416102355444464034512896
/-- `2^193`. -/
def O2 : Nat := 12554203470773361527671578846415332832204710888928069025792
/-- `2^128`, the unit at scale `2^-128`. -/
def ONE : Nat := 340282366920938463463374607431768211456
/-- `2^384 + 2^320`. -/
def KO : Nat := 39402006196394479214415027136064523887474760976634998782550997926602374541444252219236485980665556190829590077243392
/-- `2^320`. -/
def OP : Nat := 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576

/-- `x + y` in offset form. -/
@[inline] def addO (X Y : Nat) : Nat := Nat.sub (Nat.add X Y) O
/-- `x - y` in offset form. -/
@[inline] def subO (X Y : Nat) : Nat := Nat.sub (Nat.add X O) Y
/-- `-x` in offset form. -/
@[inline] def negO (X : Nat) : Nat := Nat.sub O2 X
/-- `⌊x y 2^128⌋ / 2^128` in offset form (both factors offset). -/
@[inline] def mulO (X Y : Nat) : Nat :=
  Nat.shiftRight (Nat.sub (Nat.add (Nat.mul X Y) KO) (Nat.shiftLeft (Nat.add X Y) 192)) 128
/-- offset `x` times plain nonnegative `y`, floor-rounded, in offset form. -/
@[inline] def mulOP (X y : Nat) : Nat :=
  Nat.shiftRight (Nat.sub (Nat.add (Nat.mul X y) OP) (Nat.shiftLeft y 192)) 128
/-- plain times plain, floor-rounded, plain. -/
@[inline] def mulPP (x y : Nat) : Nat := Nat.shiftRight (Nat.mul x y) 128
/-- offset `x` divided by a positive natural `j`, floor-rounded, offset form. -/
@[inline] def divO (X j : Nat) : Nat := Nat.div (Nat.add X (Nat.mul (Nat.sub j 1) O)) j
/-- plain to offset. -/
@[inline] def ofPlain (x : Nat) : Nat := Nat.add x O

/-- Forces the evaluation of `n` (the kernel must reduce it to a literal to choose a branch),
then returns `k`. Both branches are `k`, so `force n k = k` (`force_eq`). -/
@[inline] def force {α : Sort _} (n : Nat) (k : α) : α :=
  match n with
  | 0 => k
  | _ => k

theorem force_eq {α : Sort _} (n : Nat) (k : α) : force n k = k := by
  unfold force; split <;> rfl

/-! ## `e^{-ix}` for a small nonnegative `x` (plain), by a Taylor sum

State: `j` (index of the next term), `t ≈ x^j / j!` (plain), and four nonnegative accumulators
`rp, rn, ip, im` for the real and imaginary parts of `Σ_{m<j} (-i)^m t_m`
(`m ≡ 0, 1, 2, 3 mod 4` goes to `rp, im, rn, ip`). -/

/-- Taylor loop for `e^{-ix}`; returns the real and imaginary parts in offset form. -/
def taylorI (x : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, rp, rn, ip, im => (Nat.sub (Nat.add rp O) rn, Nat.sub (Nat.add ip O) im)
  | fuel+1, j, t, rp, rn, ip, im =>
    let t' := Nat.div (mulPP t x) (Nat.add j 1)
    match Nat.mod j 4 with
    | 0 => let rp := Nat.add rp t; force (Nat.add rp t') (taylorI x fuel (Nat.add j 1) t' rp rn ip im)
    | 1 => let im := Nat.add im t; force (Nat.add im t') (taylorI x fuel (Nat.add j 1) t' rp rn ip im)
    | 2 => let rn := Nat.add rn t; force (Nat.add rn t') (taylorI x fuel (Nat.add j 1) t' rp rn ip im)
    | _ => let ip := Nat.add ip t; force (Nat.add ip t') (taylorI x fuel (Nat.add j 1) t' rp rn ip im)

/-- One complex squaring in offset form. -/
@[inline] def csq (a b : Nat) : Nat × Nat :=
  let ab := mulO a b
  (subO (mulO a a) (mulO b b), addO ab ab)

/-- `k` complex squarings in offset form. -/
def sqIter : Nat → Nat → Nat → Nat × Nat
  | 0, a, b => (a, b)
  | k+1, a, b =>
    let re := subO (mulO a a) (mulO b b)
    let ab := mulO a b
    let im := addO ab ab
    force (Nat.add re im) (sqIter k re im)

/-- Number of Taylor terms. -/
def nTaylor : Nat := 24

/-- `2^125`, i.e. `1/8` at scale `2^-128`. -/
def EIGHTH : Nat := 42535295865117307932921825928971026432

/-- The halved argument `⌊T L / 2^(256+K)⌋` (plain, scale `2^-128`). -/
@[inline] def halfArg (K T L : Nat) : Nat := Nat.shiftRight (Nat.mul T L) (Nat.add 128 K)

/-- `e^{-i y}` where `y = T · L / 2^256` (`T` the height at scale `2^-128`, `L` a logarithm at
scale `2^-128`, both plain), by `K` halvings: Taylor at `y / 2^K`, then `K` squarings.
Only meaningful when `halfArg K T L ≤ 2^125`; `smallArgs` checks this. -/
def expNegI (K T L : Nat) : Nat × Nat :=
  let x := halfArg K T L
  let cs := taylorI x nTaylor 0 ONE 0 0 0 0
  sqIter K cs.1 cs.2

/-! ## Data for one prime and the Dirichlet sums -/

/-- `p^{-s}` at `s = 1/2 + i t` in offset form, from `w ≈ p^{-1/2}` (plain) and `L ≈ log p`. -/
@[inline] def primeTerm (K T w L : Nat) : Nat × Nat :=
  let cs := expNegI K T L
  (mulOP cs.1 w, mulOP cs.2 w)

/-- A prime with its data `(p, L ≈ log p, re, im)` where `re + i im ≈ p^{-s}` (offset). -/
structure PT where
  p : Nat
  L : Nat
  re : Nat
  im : Nat

/-- Prime data list from `(p, w, L)` triples. -/
def primeTerms (K T : Nat) : List (Nat × Nat × Nat) → List PT
  | [] => []
  | (p, w, L) :: ds =>
    let v := primeTerm K T w L
    force (Nat.add v.1 v.2) (⟨p, L, v.1, v.2⟩ :: primeTerms K T ds)

/-- Every halved argument is at most `1/8`. -/
def smallArgs (K T : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => true
  | (_, _, L) :: ds => Nat.ble (halfArg K T L) EIGHTH && smallArgs K T ds

/-- Accumulators: `S = Σ n^{-s}` and `D = -Σ log n · n^{-s}` (offset). -/
structure Acc where
  sr : Nat
  si : Nat
  dr : Nat
  di : Nat

/-- add `n^{-s} ≈ (ur, ui)` with `log n ≈ ln` (plain) to the accumulators -/
@[inline] def Acc.push (a : Acc) (ur ui ln : Nat) : Acc :=
  ⟨addO a.sr ur, addO a.si ui, subO a.dr (mulOP ur ln), subO a.di (mulOP ui ln)⟩

/-- Sum of the fields, used only to force an accumulator. -/
@[inline] def Acc.tot (a : Acc) : Nat := Nat.add (Nat.add a.sr a.si) (Nat.add a.dr a.di)

/-- Depth-first enumeration of the `n = m · q₁ ⋯ q_r ≤ N` with nondecreasing primes `qᵢ` taken
from the list; `(ur, ui) ≈ m^{-s}`, `lm ≈ log m`. -/
def go (N : Nat) : Nat → List PT → Nat → Nat → Nat → Nat → Acc → Acc
  | 0, _, _, _, _, _, acc => acc
  | _+1, [], _, _, _, _, acc => acc
  | fuel+1, q :: qs, m, ur, ui, lm, acc =>
    let n := Nat.mul m q.p
    match Nat.ble n N with
    | false => acc
    | true =>
      let vr := subO (mulO ur q.re) (mulO ui q.im)
      let vi := addO (mulO ur q.im) (mulO ui q.re)
      let ln := Nat.add lm q.L
      let acc := acc.push vr vi ln
      force acc.tot
        (let acc := go N fuel (q :: qs) n vr vi ln acc
         force acc.tot (go N fuel qs m ur ui lm acc))

/-- `S` and `D` at `s = 1/2 + i t` (the `n = 1` term included). -/
def sums (N K T fuel : Nat) (primes : List (Nat × Nat × Nat)) : Acc :=
  go N fuel (primeTerms K T primes) 1 (Nat.add ONE O) O 0 ⟨Nat.add ONE O, O, O, O⟩

/-- The `n` visited by `go` (ghost version, used only to check the enumeration once per `N`). -/
def goNs (N : Nat) : Nat → List Nat → Nat → List Nat
  | 0, _, _ => []
  | _+1, [], _ => []
  | fuel+1, q :: qs, m =>
    let n := Nat.mul m q
    match Nat.ble n N with
    | false => []
    | true => n :: (goNs N fuel (q :: qs) n ++ goNs N fuel qs m)

end ZetaCert.Eval
