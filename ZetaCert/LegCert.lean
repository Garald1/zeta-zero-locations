/-
Copyright (c) 2026 Harald Helfgott. All rights reserved.
Released under Apache 2.0 license.
-/
import ZetaCert.Cert
import ZetaCert.RootDataCheck

/-!
# The checker for one point of a horizontal leg: `lc`

`lc j G N K k fuel Dp v d` evaluates the Euler–Maclaurin main term and its derivative at
`s = σ + iγ` with `σ = j/4096 ≥ 1/2`, `γ = G/2^80`, and checks
`v ≤ Re F(s) - eF - E0` and `‖F'(s)‖ + eD + 4 E1 ≤ d`. Soundness (`ZetaCert/LegCertSound.lean`):
`v ≤ Re ζ(s)` and `‖ζ'(s)‖ ≤ d`; `lcI` also gives `wlo ≤ Im ζ(s) ≤ whi`.
-/

namespace ZetaCert

open ZetaCert.Eval ZetaCert.Data

/-- Root data up to `N` at real part `j/4096`. -/
def rdataN (N : Nat) : List (Nat × Nat × Nat) := rdata.takeWhile (fun d => Nat.ble d.1 N)

section QG
variable (G N K k Dp j : Nat) (acc : Acc) (uN : Nat × Nat) (wN LN : Nat) (R R1 : GZ)

def qσ : ℚ := (j : ℚ) / 4096
def qew : ℚ := (2 * j - 1) * (2 * quu)
def qEpG : ℚ := 2 ^ (K + 1) * (77 * quu) + 2 * (qt G * qδL) + qew j + 2 * quu
def qE'G : ℚ := qEpG G K j + 4 * quu
def qerrSG : ℚ := N * (Dp * qE'G G K j)
def qerrDG : ℚ := N * ((Dp : ℚ) * (Dp * qE'G G K j) + Dp * qδL + 2 * quu)
def qeFG : ℚ := qerrSG G N K Dp j + qEpG G K j * cqn1 (qR R) + qeR k
def qeDG : ℚ := qerrDG G N K Dp j + qEpG G K j * cqn1 (qX LN R R1) + qeX k LN R
def qE0G : ℚ := prodShift (qσ j + qt G) (2 * k + 2) / (fact (2 * k + 2) : ℚ) * qbAbs k *
  (((wN + 1 : Nat) : ℚ) / 2 ^ 128 / (N : ℚ) ^ (2 * k + 1)) / (qσ j + 2 * k + 1)
def qE1G : ℚ := prodShift (qσ j + 1 / 2 + qt G) (2 * k + 2) / (fact (2 * k + 2) : ℚ) * qbAbs k /
  (N : ℚ) ^ (2 * k + 1) / (2 * k + 1)

/-- The rational checks at a leg point. -/
def lcQ (v d wlo whi : ℚ) : Bool :=
  decide (qt G * qδL ≤ 1 / 2 ^ 42) && decide ((Dp : ℚ) * qE'G G K j * qEpG G K j ≤ quu) &&
  decide ((Dp : ℚ) * qE'G G K j ≤ 1) && decide ((Dp : ℚ) ≤ 2 ^ 20) && decide (qew j ≤ 1 / 2 ^ 60) &&
  decide (v ≤ (qFv acc uN R).1 - qeFG G N K k Dp j R - qE0G G N k j wN) &&
  decide (cqn1 (qFd acc uN LN R R1) + qeDG G N K k Dp j LN R R1 + 4 * qE1G G N k j ≤ d) &&
  decide (wlo ≤ (qFv acc uN R).2 - qeFG G N K k Dp j R - qE0G G N k j wN) &&
  decide ((qFv acc uN R).2 + qeFG G N K k Dp j R + qE0G G N k j wN ≤ whi)

end QG

/-- The leg-point checker, also bounding `Im ζ(s)` between `wlo` and `whi`. -/
def lcI (j G N K k fuel Dp : Nat) (v d wlo whi : ℚ) : Bool :=
  let T := G * 2 ^ 48
  let S := j * 2 ^ 68
  let data := dataSigma j (rdataN N)
  match (dataN N).getLast?, (rdataN N).getLast? with
  | some (pN, wN, _), some (pN', xN, LN) =>
    let acc := sums N K T fuel data
    let uN := primeTerm K T (powPP xN 16 j) LN
    let R := remRS S N G bern k
    let R1 := remR1S S N G bern k
    Nat.beq pN N && Nat.beq pN' N && Nat.ble 1 N && Nat.ble N (2 ^ 20) && Nat.blt N (2 ^ Dp) &&
    Nat.ble K 40 && Nat.ble (2 * k + 2) 123 && Nat.ble (2 ^ 81) G && Nat.ble 2048 j && Nat.blt j 8193 &&
    smallArgs K T data && enumOK N fuel (data.map Prod.fst) &&
    lcQ G N K k Dp j acc uN wN LN R R1 v d wlo whi
  | _, _ => false

/-- The leg-point checker. -/
def lc (j G N K k fuel Dp : Nat) (v d : ℚ) : Bool := lcI j G N K k fuel Dp v d (-(2 ^ 30)) (2 ^ 30)

end ZetaCert
