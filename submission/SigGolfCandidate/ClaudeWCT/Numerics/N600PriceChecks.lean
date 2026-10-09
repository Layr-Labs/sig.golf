import SigGolfCandidate.ClaudeWCT.Numerics.N600Data
import SigGolfCandidate.ClaudeWCT.Numerics.Kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

section


namespace ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.Kernel (wpos wneg fact HB packPos packNeg)
def Nn : Nat := 563
def Kc : Nat := 128
def Q : Nat := 72064
def B1 : Nat := 71501
def B2 : Nat := 70938
def xNum (r : Nat) : Nat := wpos w1Data B1 r - wneg w1Data B1 r
def xfNum (t r : Nat) : Nat := wpos (wfData t) B1 r - wneg (wfData t) B1 r
def xfSum (r : Nat) : Nat := xfNum 0 r + xfNum 1 r + xfNum 2 r + xfNum 3 r + xfNum 4 r + xfNum 5 r
def yPos (r : Nat) : Nat := wpos w2Data B1 r + (Kc - 1) * wpos wwData B2 r
def yNeg (r : Nat) : Nat := wneg w2Data B1 r + (Kc - 1) * wneg wwData B2 r
def yNum (r : Nat) : Nat := yPos r - yNeg r
def poissonCheckQ (Qv un ud ln ld : Nat) (f : Nat → Nat) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Qv ^ (9 * (R - r)) + s) 0
  Md * sn * (S * ld * (R + 1) + ln ^ (R + 1) * ud * dbase * Qv ^ (9 * R)) ≤
    Mn * sd * ud * dbase * ld ^ (R + 1) * fact (R + 1) * Qv ^ (9 * R)
def A : Nat := 1353 * 2 ^ 24 * 563 ^ 9
def LN : Nat := 203317755
def LD : Nat := 100000000
def MN : Nat := 675
def MD : Nat := 1000
def DN : Nat := 3200
def DD : Nat := 1000000
def NN : Nat := 291
def ND : Nat := 1
def meanCheck : Bool := poissonCheckQ Q 13533529 100000000 LN LD (fun r => xNum r ^ 9) (Nn ^ 9) A 1 MN MD 80
def diagCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => yNum r ^ 9) ((Kc * Nn ^ 2) ^ 9) (A ^ 2) (2 ^ 31) DN DD 80
def nearCheck : Bool :=
  poissonCheckQ Q 13533529 100000000 LN LD (fun r => xNum r ^ 8 * xfSum r) (6 * Nn ^ 9) (54 * A) 1 NN ND 80
def convCheck : Bool :=
  Nat.beq (packPos w1Data ^ 2 + packNeg w1Data ^ 2 + packNeg wwData) (packPos wwData + 2 * packPos w1Data * packNeg w1Data)
end ClaudeWCT.Numerics.N600
end

section

namespace ClaudeWCT.Numerics.N600
theorem mean_ok : meanCheck = true := by decide +kernel
theorem near_ok : nearCheck = true := by decide +kernel
theorem diag_ok : diagCheck = true := by decide +kernel
theorem conv_ok : convCheck = true := by decide +kernel
end ClaudeWCT.Numerics.N600
end

