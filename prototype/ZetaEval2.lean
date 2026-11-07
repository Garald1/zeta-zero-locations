module

@[expose] public section

/-!
# Kernel-evaluation prototype, version 2 (Lean core only)

Computes the Dirichlet partial sums
  S(s)  = Σ_{n ≤ N} n^{-s},   S'(s) = -Σ_{n ≤ N} (log n) n^{-s}
at s = 1/2 + i t, using only `Nat` operations (GMP-accelerated in the kernel):

* fixed point at scale 2^-P; signed quantities in offset binary `X = x·2^P + 2^Q`;
* `p^{-s}` for primes p ≤ N via reduction mod 2π, a Taylor sum and repeated squaring;
* `n^{-s}` for composite n by complete multiplicativity, enumerating every
  n ≤ N once as a non-decreasing product of primes (depth-first);
* accumulators are forced at each step so the kernel never builds deep thunks.

Error radii (in ulps) are carried alongside with additive rules that are valid
because every complex number involved has modulus ≤ 1 + 2^-60.
-/

namespace ZB2

abbrev P : Nat := 96            -- fractional bits
abbrev Q : Nat := 128           -- offset exponent: X = x·2^P + 2^Q
abbrev O : Nat := 2^Q
abbrev ONE : Nat := 2^P
abbrev KO : Nat := 2^(2*Q) + 2^(Q+P)

/-- offset × offset (signed × signed), floor-rounded -/
@[inline] def mulO (X Y : Nat) : Nat :=
  Nat.shiftRight (Nat.sub (Nat.add (Nat.mul X Y) KO) (Nat.shiftLeft (Nat.add X Y) Q)) P

/-- offset × nonnegative plain, floor-rounded -/
@[inline] def mulOP (X y : Nat) : Nat :=
  Nat.shiftRight (Nat.sub (Nat.add (Nat.mul X y) (2^(Q+P))) (Nat.shiftLeft y Q)) P

@[inline] def addO (X Y : Nat) : Nat := Nat.sub (Nat.add X Y) O
@[inline] def subO (X Y : Nat) : Nat := Nat.sub (Nat.add X O) Y

/-- Taylor sum of e^{-iz} for 0 ≤ z ≤ 2^-4 (plain Nat at scale 2^P):
accumulates cos⁺, cos⁻, sin⁺, sin⁻ -/
def taylor (z : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, cp, cn, sp, sn => (Nat.sub (Nat.add cp O) cn, Nat.sub (Nat.add sp O) sn)
  | fuel+1, j, term, cp, cn, sp, sn =>
    let t' := Nat.div (Nat.shiftRight (Nat.mul term z) P) j
    match Nat.mod j 4 with
    | 0 => taylor z fuel (j+1) t' (Nat.add cp t') cn sp sn
    | 1 => taylor z fuel (j+1) t' cp cn sp (Nat.add sn t')
    | 2 => taylor z fuel (j+1) t' cp (Nat.add cn t') sp sn
    | _ => taylor z fuel (j+1) t' cp cn (Nat.add sp t') sn

/-- repeated complex squaring in offset representation -/
def sqIter : Nat → Nat → Nat → Nat × Nat
  | 0, a, b => (a, b)
  | k+1, a, b =>
    let re := subO (mulO a a) (mulO b b)
    let ab := mulO a b
    let im := addO ab ab   -- 2ab in offset form
    match re with
    | 0 => (0, 0)
    | _ => sqIter k re im

/-- e^{-i x} for a nonnegative plain x (scale 2^P); `twoPi` plain at scale 2^P -/
def expNegI (twoPi x : Nat) : Nat × Nat :=
  let y := Nat.sub x (Nat.mul (Nat.div x twoPi) twoPi)
  let z := Nat.shiftRight y 7
  -- j = 0 term is 1 (cos⁺); start the loop at j = 1 with term = 1
  let (c, s) := taylor z 13 1 ONE ONE 0 0 0
  sqIter 7 c s

/-- data for one prime: p, log p and p^{-1/2} (plain, scale 2^P) -/
structure PrimeData where
  p  : Nat
  lg : Nat
  w  : Nat

/-- p^{-s} at s = 1/2 + it, in offset representation, together with p and log p -/
structure PVal where
  p  : Nat
  lg : Nat
  re : Nat
  im : Nat

def pval (twoPi t : Nat) (d : PrimeData) : PVal :=
  let x := Nat.shiftRight (Nat.mul t d.lg) P
  let (c, s) := expNegI twoPi x
  ⟨d.p, d.lg, mulOP c d.w, mulOP s d.w⟩

/-- accumulators: S (re, im) and S' (re, im), all in offset form -/
structure Acc where
  sr : Nat
  si : Nat
  dr : Nat
  di : Nat

/-- add n^{-s} = (ur, ui) with log n = ln into the accumulators -/
@[inline] def Acc.push (a : Acc) (ur ui ln : Nat) : Acc :=
  ⟨addO a.sr ur, addO a.si ui, subO a.dr (mulOP ur ln), subO a.di (mulOP ui ln)⟩

/-- depth-first enumeration of all n = m·p₁·p₂⋯ ≤ N with primes taken from `ps`
in non-decreasing order.  `fuel` bounds the recursion depth. -/
def go (N : Nat) : Nat → List PVal → Nat → Nat → Nat → Nat → Acc → Acc
  | 0, _, _, _, _, _, acc => acc
  | _+1, [], _, _, _, _, acc => acc
  | fuel+1, q :: qs, m, ur, ui, lm, acc =>
    let n := Nat.mul m q.p
    match Nat.ble n N with
    | false => acc
    | true =>
      let vr := subO (mulO ur q.re) (mulO ui q.im)
      let vi := addO (mulO ur q.im) (mulO ui q.re)
      let ln := Nat.add lm q.lg
      let acc := acc.push vr vi ln
      -- force the accumulator before recursing (keeps kernel terms shallow)
      match Nat.add (Nat.add acc.sr acc.si) (Nat.add acc.dr acc.di) with
      | 0 => acc
      | _ =>
        let acc := go N fuel (q :: qs) n vr vi ln acc
        match Nat.add (Nat.add acc.sr acc.si) (Nat.add acc.dr acc.di) with
        | 0 => acc
        | _ => go N fuel qs m ur ui lm acc

def mapPVal (twoPi t : Nat) : List PrimeData → List PVal
  | [] => []
  | d :: ds =>
    let v := pval twoPi t d
    match v.re with
    | 0 => []
    | _ => v :: mapPVal twoPi t ds

/-- S and S' at s = 1/2 + it (t plain, scale 2^P) -/
def sums (N twoPi t : Nat) (primes : List PrimeData) : Acc :=
  let pv := mapPVal twoPi t primes
  -- n = 1 contributes 1 to S and 0 to S'
  go N 10000 pv 1 (Nat.add ONE O) O 0 ⟨Nat.add ONE O, O, O, O⟩

/-- |X - E| ≤ tol for offset X and expected offset E -/
@[inline] def close (X E tol : Nat) : Bool :=
  Nat.ble (Nat.sub X E) tol && Nat.ble (Nat.sub E X) tol

def check (N twoPi t : Nat) (primes : List PrimeData) (esr esi edr edi tol : Nat) : Bool :=
  let a := sums N twoPi t primes
  close a.sr esr tol && close a.si esi tol && close a.dr edr tol && close a.di edi tol

end ZB2
