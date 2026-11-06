/-!
# Kernel-evaluation prototype (Lean core only, no Mathlib)

Dyadic ball arithmetic and the main Euler–Maclaurin sum for ζ(1/2+it):

  S(t)  = Σ_{n<N} n^{-1/2} e^{-i t log n}        (ζ main sum)
  S'(t) = Σ_{n<N} -log n · n^{-1/2} e^{-i t log n} (ζ' main sum)

Everything is computed on `Int` midpoints at scale 2^-P with `Nat` radii,
so the kernel only ever reduces GMP-accelerated `Nat` operations.
This file is a cost benchmark: the tables of log n and n^{-1/2} are taken
as given here; in the real checker they are verified once.
-/

namespace ZB

/-- working precision: values are stored as `m * 2^-P`. -/
abbrev P : Nat := 80

/-- a real ball `[m - r, m + r] * 2^-P` -/
structure Ball where
  m : Int
  r : Nat

/-- a complex ball (rectangular) -/
structure CBall where
  re : Ball
  im : Ball

@[inline] def Ball.add (a b : Ball) : Ball := ⟨a.m + b.m, a.r + b.r⟩
@[inline] def Ball.sub (a b : Ball) : Ball := ⟨a.m - b.m, a.r + b.r⟩
@[inline] def Ball.neg (a : Ball) : Ball := ⟨-a.m, a.r⟩

/-- product, rescaled by 2^-P with floor rounding (+2 ulp slack) -/
@[inline] def Ball.mul (a b : Ball) : Ball :=
  ⟨(a.m * b.m) >>> P,
   ((a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r) >>> P) + 2⟩

/-- division by a positive natural number -/
@[inline] def Ball.divNat (a : Ball) (d : Nat) : Ball :=
  ⟨a.m / (d : Int), a.r / d + 2⟩

/-- division by 2^k -/
@[inline] def Ball.shr (a : Ball) (k : Nat) : Ball :=
  ⟨a.m >>> k, (a.r >>> k) + 2⟩

@[inline] def CBall.add (a b : CBall) : CBall := ⟨a.re.add b.re, a.im.add b.im⟩
@[inline] def CBall.mulReal (a : CBall) (x : Ball) : CBall := ⟨a.re.mul x, a.im.mul x⟩
@[inline] def CBall.sq (a : CBall) : CBall :=
  let rr := a.re.mul a.re
  let ii := a.im.mul a.im
  let ri := a.re.mul a.im
  ⟨rr.sub ii, ri.add ri⟩

def CBall.zero : CBall := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
def one : Ball := ⟨(1 : Int) <<< P, 0⟩

/-- Taylor sum for e^{-i z}, z small real ball: Σ_{j ≤ J} (-i z)^j / j!.
`term` is the current term, `j` the index of the next term. -/
def expNegITaylor (z : Ball) : Nat → Nat → CBall → CBall → CBall
  | 0, _, _, acc => acc
  | fuel+1, j, term, acc =>
    -- next = term * (-i z) / j  ;  (a+ib)(-iz) = b z - i a z
    let nxt : CBall := ⟨(term.im.mul z).divNat j, ((term.re.mul z).neg).divNat j⟩
    expNegITaylor z fuel (j+1) nxt (acc.add nxt)

def iterSq : Nat → CBall → CBall
  | 0, a => a
  | k+1, a => iterSq k a.sq

/-- e^{-i x} for a real ball x ≥ 0, using reduction mod 2π, scaling by 2^-7,
a 13-term Taylor sum (+1 ulp remainder) and 7 squarings. -/
def expNegI (twoPi : Ball) (x : Ball) : CBall :=
  let k : Int := x.m / twoPi.m
  let y : Ball := x.sub ⟨k * twoPi.m, k.natAbs * twoPi.r⟩
  let z : Ball := y.shr 7
  let s := expNegITaylor z 12 1 ⟨one, ⟨0,0⟩⟩ ⟨one, ⟨0,0⟩⟩
  let s : CBall := ⟨⟨s.re.m, s.re.r + 1⟩, ⟨s.im.m, s.im.r + 1⟩⟩
  iterSq 7 s

/-- one table entry: (log n, n^{-1/2}) as balls -/
structure Entry where
  lg : Ball
  w  : Ball

/-- accumulate S and S' over the table -/
def mainSums (twoPi : Ball) (t : Int) : List Entry → CBall → CBall → CBall × CBall
  | [], s, s' => (s, s')
  | e :: es, s, s' =>
    let x := (Ball.mul ⟨t, 0⟩ e.lg)
    let c := (expNegI twoPi x).mulReal e.w
    mainSums twoPi t es (s.add c) (s'.add (c.mulReal e.lg.neg))

/-- crude magnitude bounds (scale 2^-P): upper bound of |z|_∞ and lower bound -/
def Ball.absHi (a : Ball) : Nat := a.m.natAbs + a.r
def Ball.absLo (a : Ball) : Nat := a.m.natAbs - a.r

/-- benchmark check: the computed balls for S and S' are tight (radius < 2^-40)
and S' is bounded away from 0.  (A stand-in for the Kantorovich test.) -/
def check (twoPi : Ball) (t : Int) (tab : List Entry) : Bool :=
  let (s, s') := mainSums twoPi t tab CBall.zero CBall.zero
  let tight := (1 : Nat) <<< (P - 40)
  decide (s.re.r < tight) && decide (s.im.r < tight) &&
  decide (s'.re.r < tight) && decide (s'.im.r < tight) &&
  decide (0 < s'.re.absLo + s'.im.absLo)

end ZB
