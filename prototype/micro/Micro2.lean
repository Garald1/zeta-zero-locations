/-! Micro-benchmarks: strict vs lazy loops in the kernel -/

-- lazy accumulator (structural recursion)
def lazyNat : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc => lazyNat k ((acc * 1234567891011 + k) >>> 40)

-- strict: force the accumulator by a test each step
def strictNat : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc =>
    let a := (acc * 1234567891011 + k) >>> 40
    if a == 0 then 0 else strictNat k a

def strictInt : Nat → Int → Int
  | 0, acc => acc
  | k+1, acc =>
    let a := (acc * (-1234567891011) + (k : Int)) >>> 40
    match a with
    | .ofNat 0 => 0
    | _ => strictInt k a

-- list fold (structural on List), strict
def foldStrict : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc =>
    let a := (acc * x + 7) >>> 40
    if a == 0 then 0 else foldStrict xs a

def mkList : Nat → List Nat → List Nat
  | 0, l => l
  | k+1, l => mkList k ((1234567891011 + k) :: l)

theorem tLazy : lazyNat 100000 5 ≠ 0 := by decide +kernel
theorem tStrictNat : strictNat 100000 5 ≠ 0 := by decide +kernel
theorem tStrictInt : strictInt 100000 5 ≠ 0 := by decide +kernel
theorem tFold : foldStrict (mkList 100000 []) 5 ≠ 0 := by decide +kernel
