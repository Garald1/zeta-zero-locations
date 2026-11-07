module

@[expose] public section

/-! Micro-benchmarks for kernel arithmetic cost -/

def loopNat : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc => loopNat k ((acc * 1234567891011 + k) >>> 40)

def loopInt : Nat → Int → Int
  | 0, acc => acc
  | k+1, acc => loopInt k ((acc * (-1234567891011) + (k : Int)) >>> 40)

def loopNatRaw : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc => loopNatRaw k (Nat.shiftRight (Nat.add (Nat.mul acc 1234567891011) k) 40)

-- 10^4 iterations each
theorem tNat : loopNat 10000 5 ≠ 0 := by decide +kernel
theorem tInt : loopInt 10000 5 ≠ 0 := by decide +kernel
theorem tNatRaw : loopNatRaw 10000 5 ≠ 0 := by decide +kernel
