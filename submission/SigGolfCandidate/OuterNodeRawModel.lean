import SigGolfCandidate.OuterGroundCore
import SigGolfCandidate.FtsCode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeRawModel
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9 OuterGroundCore
open SphincsSecurity (bytesLE)

def high (coord heap : Nat) : Bool := if coord=8 ∧ heap=3 then false else true
def pre (coord index heap : Nat) (left : Digest) : List UInt8 := bytesLE 16 left++bytesLE 16 (wctNodeHeader coord index heap)
def rightBytes (right : Digest) : List UInt8 := bytesLE 16 right

theorem half_value (coord heap : Nat) (a : HashOutput) :
    SigGolfCandidate.FtsGrind.halfOf (high coord heap) a=value coord heap a := by
  unfold SigGolfCandidate.FtsGrind.halfOf high value offset
  by_cases h : coord=8 ∧ heap=3 <;> simp [h]

theorem zero_eq (coord heap : Nat) (a : HashOutput) :
    SigGolfCandidate.FtsGrind.zeroOkH (high coord heap) (OuterGroundCore.width coord) a=zeroOk coord (value coord heap a) := by
  apply Bool.eq_iff_iff.mpr
  simp [SigGolfCandidate.FtsGrind.zeroOkH,half_value,zeroOk,Nat.div_eq_zero_iff]

theorem trial_eq (coord index heap n : Nat) (left right : Digest) :
    publicHash (SigGolfCandidate.FtsGrind.trialInput (pre coord index heap left) n (rightBytes right))=
      publicQuery (trial coord index heap n left right) := by
  unfold publicHash publicQuery trial ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.fTrial
  unfold SigGolfCandidate.FtsGrind.trialInput pre rightBytes ftsNodeInputN
  simp only [List.append_assoc]

def raw (coord index heap : Nat) (left right : Digest) (fuel n : Nat) : M (Nat × HashOutput) :=
  SigGolfCandidate.FtsGrind.searchH (high coord heap) (OuterGroundCore.width coord)
    (pre coord index heap left) (rightBytes right) fuel n

def keep (coord heap : Nat) (p : Nat × HashOutput) : Nat × Digest := (p.1,value coord heap p.2)

theorem source_eq (coord index heap : Nat) (left right : Digest) : ∀ fuel n,
    search coord index heap left right fuel n=keep coord heap <$> raw coord index heap left right fuel n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n
    simp [raw,search,hashN,SigGolfCandidate.FtsGrind.searchH,trial_eq,keep,map_bind,bind_assoc]
  | succ fuel ih =>
    intro n
    simp only [raw,SigGolfCandidate.FtsGrind.searchH,map_bind,trial_eq,search,hashN,bind_assoc,pure_bind]
    congr 1
    funext a
    rw [zero_eq]
    split
    · simp [keep]
    · exact ih (n+1)

#print axioms source_eq
end OuterNodeRawModel
