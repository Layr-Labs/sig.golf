import SigGolfCandidate.OuterCopyChildB
import SigGolfCandidate.OuterCopyChildC
import SigGolfCandidate.FtsExpandRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterChildModel
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M W9Machine
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

def child (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (ends : List Digest)
    (padL padR : Digest) : M (Digest×Nat×Nat×Nat) :=
  if SharedV3.first k.val then
    (fun r=>(r.1,r.2.1,r.2.2,0)) <$> SharedV3.childNG w index k raw ends padL padR
  else do
    let j:=SharedV3.physical k.val raw.val
    let leaf←SharedV3.hashSel (SharedV3.hiOut j 0) (V3.leafInput k.val index raw.val padL ends)
    let acc←(List.range 5).foldlM (SharedV3.childStepG w index k.val j padR) (leaf,0,0)
    let left:=if j/32%2=0 then acc.1 else SharedV3.sibling w k.val j 5
    let right:=if j/32%2=0 then SharedV3.sibling w k.val j 5 else acc.1
    let outer←OuterGroundCore.nodeAt k.val index ((128+j)/64) left right
    pure (outer.2,acc.2.1,acc.2.2,outer.1)

def childProgram (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (ends : List Digest) : M (Digest×Nat×Nat×Nat) :=
  child w index k raw ends (SharedV3.leafPad w k.val)
    (SharedV3.nodePad w k.val (SharedV3.physical k.val raw.val) 4)

theorem widths : ∀ k : Fin 9,
    SigGolfCandidate.FtsGrind.widthOf (coordRegion k.val)=SigGolfCandidate.FtsGrind.ftsWidth k.val ∧
    decide (SigGolfCandidate.FtsGrind.SEL16≤coordRegion k.val)=decide (k.val<4) := by decide +kernel

#print axioms widths
end OuterChildModel
