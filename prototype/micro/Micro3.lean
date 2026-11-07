module

@[expose] public section

/-! Micro-benchmarks: cost of a fixed-point complex multiply + accumulate in the kernel,
for several coding styles.  10^4 iterations each. -/

-- Style A: structures + typeclass operators (as in ZetaEval.lean)
structure C2 where
  re : Int
  im : Int

def mulA (a b : C2) : C2 :=
  ⟨(a.re * b.re - a.im * b.im) >>> 80, (a.re * b.im + a.im * b.re) >>> 80⟩

def loopA : Nat → C2 → C2 → C2 → C2
  | 0, _, _, acc => acc
  | k+1, w, z, acc =>
    let z' := mulA z w
    match z'.re with
    | .ofNat 0 => acc
    | _ => loopA k w z' ⟨acc.re + z'.re, acc.im + z'.im⟩

-- Style B: explicit Int functions, unboxed arguments
def loopB : Nat → Int → Int → Int → Int → Int → Int → Int
  | 0, _, _, _, _, sr, _ => sr
  | k+1, wr, wi, zr, zi, sr, si =>
    let r := Int.shiftRight (Int.sub (Int.mul zr wr) (Int.mul zi wi)) 80
    let i := Int.shiftRight (Int.add (Int.mul zr wi) (Int.mul zi wr)) 80
    match r with
    | .ofNat 0 => sr
    | _ => loopB k wr wi r i (Int.add sr r) (Int.add si i)

-- Style C: offset-binary Nat representation X = x + 2^100, explicit Nat ops
-- product: (X*Y + K - ((X+Y) <<< 100)) >>> 80 where K = 2^200 + 2^180
-- (valid when |x y| < 2^180, i.e. |x|,|y| < 2^90)
def K : Nat := 2^200 + 2^180
def mulC (X Y : Nat) : Nat :=
  Nat.shiftRight (Nat.sub (Nat.add (Nat.mul X Y) K) (Nat.shiftLeft (Nat.add X Y) 100)) 80

-- complex: (a+ib)(c+id) = (ac - bd) + i(ad + bc); offset reps: subtract offsets carefully
-- re = mul(a,c) - mul(b,d) + 2^100 ; im = mul(a,d) + mul(b,c) - 2^100
def loopC : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _, sr, _ => sr
  | k+1, wr, wi, zr, zi, sr, si =>
    let r := Nat.sub (Nat.add (mulC zr wr) (2^100)) (mulC zi wi)
    let i := Nat.sub (Nat.add (mulC zr wi) (mulC zi wr)) (2^100)
    match r with
    | 0 => sr
    | _ => loopC k wr wi r i (Nat.sub (Nat.add sr r) (2^100)) (Nat.sub (Nat.add si i) (2^100))

-- w = exp(i * 0.001) approx at scale 2^80, z = 1
def wr : Int := 1208925215426574779609286   -- cos(0.001)*2^80
def wi : Int := 1208925617830000000000      -- ~ sin(0.001)*2^80 (approx)
def one80 : Int := 2^80

theorem tA : (loopA 10000 ⟨wr, wi⟩ ⟨one80, 0⟩ ⟨0, 0⟩).re ≠ 0 := by decide +kernel
theorem tB : loopB 10000 wr wi one80 0 0 0 ≠ 0 := by decide +kernel
theorem tC : loopC 10000 (wr.toNat + 2^100) (wi.toNat + 2^100) (2^80 + 2^100) (2^100) (2^100) (2^100) ≠ 0 := by decide +kernel
