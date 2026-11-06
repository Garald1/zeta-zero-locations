/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.PrimeDataCheck
import ZetaCert.BernTable

/-!
# The per-zero checker `zc`

`zc m G N K k fuel Dp` evaluates, in the kernel, the Euler–Maclaurin main term of order `2k+2`
and its derivative at `c = 1/2 + iγ`, `γ = G / 2^80`, with cut-off `N` (a prime `≤ 4000`),
and checks the hypotheses (B1), (B2) of `ZetaCert.zero_of_EM_bounds` with `κ = 1/2`,
`r = 2^-67`, together with `|γ - m/10^24| + r ≤ 10^-20`. The assembly after the Dirichlet sums is
done in exact rational arithmetic. Its soundness is `zc_spec` (`ZetaCert/CertSound.lean`).
-/

namespace ZetaCert

open ZetaCert.Eval ZetaCert.Data

/-- Prime data up to `N`. -/
def dataN (N : Nat) : List (Nat × Nat × Nat) := pdata.takeWhile (fun d => Nat.ble d.1 N)

/-- Value of an offset number, in `ℚ`. -/
def qO (X : Nat) : ℚ := ((X : ℤ) - 2 ^ 192 : ℚ) / 2 ^ 128

/-- Complex rationals. -/
abbrev CQ := ℚ × ℚ

def cqmul (a b : CQ) : CQ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def cqadd (a b : CQ) : CQ := (a.1 + b.1, a.2 + b.2)
def cqsub (a b : CQ) : CQ := (a.1 - b.1, a.2 - b.2)
def cqsmul (c : ℚ) (a : CQ) : CQ := (c * a.1, c * a.2)
def cqn1 (a : CQ) : ℚ := |a.1| + |a.2|
def cqn2 (a : CQ) : ℚ := a.1 * a.1 + a.2 * a.2

/-- `Π_{i < n} (c + i)`. -/
def prodShift (c : ℚ) : Nat → ℚ
  | 0 => 1
  | n + 1 => prodShift c n * (c + n)

/-! ## The rational quantities (functions of the kernel-computed values) -/

section Q
variable (G N K k Dp : Nat) (acc : Acc) (uN : Nat × Nat) (wN LN : Nat) (R R1 : GZ)

def qt : ℚ := (G : ℚ) / 2 ^ 80
def quu : ℚ := 1 / 2 ^ 128
def qδL : ℚ := 1 / 2 ^ 126
def qS : CQ := (qO acc.sr, qO acc.si)
def qD : CQ := (qO acc.dr, qO acc.di)
def qu : CQ := (qO uN.1, qO uN.2)
def qR : CQ := ((R.1 : ℚ) / 2 ^ 128, (R.2 : ℚ) / 2 ^ 128)
def qℓ : ℚ := (LN : ℚ) / 2 ^ 128
def qFv : CQ := cqadd (qS acc) (cqmul (qu uN) (qR R))
def qX : CQ := cqsub (qR R1) (cqsmul (qℓ LN) (qR R))
def qFd : CQ := cqadd (qD acc) (cqmul (qu uN) (qX LN R R1))
def qEp : ℚ := 2 ^ (K + 1) * (77 * quu) + 2 * (qt G * qδL) + 3 * quu
def qE' : ℚ := qEp G K + 4 * quu
def qerrS : ℚ := N * (Dp * qE' G K)
def qerrD : ℚ := N * ((Dp : ℚ) * (Dp * qE' G K) + Dp * qδL + 2 * quu)
def qeR : ℚ := 2 * (k + 2) * quu
def qeF : ℚ := qerrS G N K Dp + qEp G K * cqn1 (qR R) + qeR k
def qeX : ℚ := qeR k + qℓ LN * qeR k + qδL * (cqn1 (qR R) + qeR k)
def qeD : ℚ := qerrD G N K Dp + qEp G K * cqn1 (qX LN R R1) + qeX k LN R
def qbAbs : ℚ := |((bernAt bern (2 * k + 2)).1 : ℚ)| / (bernAt bern (2 * k + 2)).2
def qE0 : ℚ := prodShift (1 / 2 + qt G) (2 * k + 2) / (fact (2 * k + 2) : ℚ) * qbAbs k *
  (((wN + 1 : Nat) : ℚ) / 2 ^ 128 / (N : ℚ) ^ (2 * k + 1)) / (2 * k + 3 / 2)
def qE1 : ℚ := prodShift (1 + qt G) (2 * k + 2) / (fact (2 * k + 2) : ℚ) * qbAbs k /
  (N : ℚ) ^ (2 * k + 1) / (2 * k + 1)
def qr : ℚ := 1 / 2 ^ 67
def qlhs1 : ℚ := qr * (112 + 160 * (qt G + 1)) + 4 * qE1 G N k + qeD G N K k Dp LN R R1
def qlhs2 : ℚ := cqn1 (qFv acc uN R) + qeF G N K k Dp R + qE0 G N k wN

/-- The rational checks. -/
def zcQ (m : Nat) : Bool :=
  decide (qt G * qδL ≤ 1 / 2 ^ 42) && decide ((Dp : ℚ) * qE' G K * qEp G K ≤ quu) &&
  decide ((Dp : ℚ) * qE' G K ≤ 1) && decide ((Dp : ℚ) ≤ 2 ^ 20) &&
  decide (qlhs1 G N K k Dp LN R R1 * qlhs1 G N K k Dp LN R R1 ≤ 1 / 2 * (1 / 2) * cqn2 (qFd acc uN LN R R1)) &&
  decide (qlhs2 G N K k Dp acc uN wN R * qlhs2 G N K k Dp acc uN wN R ≤
    (1 - 1 / 2) * (1 - 1 / 2) * qr * qr * cqn2 (qFd acc uN LN R R1)) &&
  decide (|qt G - (m : ℚ) / 10 ^ 24| + qr ≤ 1 / 10 ^ 20)

end Q

/-- The checker. -/
def zc (m G N K k fuel Dp : Nat) : Bool :=
  let T := G * 2 ^ 48
  let data := dataN N
  match data.getLast? with
  | none => false
  | some (pN, wN, LN) =>
    let acc := sums N K T fuel data
    let uN := primeTerm K T wN LN
    let R := remR N G bern k
    let R1 := remR1 N G bern k
    Nat.beq pN N && Nat.ble 1 N && Nat.ble N (2 ^ 20) && Nat.blt N (2 ^ Dp) && Nat.ble K 40 &&
    Nat.ble (2 * k + 2) 123 && Nat.ble (2 ^ 81) G &&
    smallArgs K T data && enumOK N fuel (data.map Prod.fst) &&
    zcQ G N K k Dp acc uN wN LN R R1 m

end ZetaCert
