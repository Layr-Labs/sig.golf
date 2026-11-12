import SigGolfCandidate.OuterResidualGroundChildren
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable section
namespace OuterResidualPadModel
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (wTrialDeps)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (ftsChild padCoord childWTrialDeps)

def padVals (v : Coord → Digest) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) : Digest×Digest :=
  (((padCoord index coord branch 0).map (selVals v)).getD 0,
    ((padCoord index coord branch 1).map (selVals v)).getD 0)
def ftsChildVal (v : Coord → Digest) (index : Fin (2^31)) (coord : Fin 9) (level physical : Nat) : Digest :=
  ((ftsChild index coord level physical).map (selVals v)).getD 0

def coordTrialDeps : Coord → List Coord
  | .inl (.node n)=>OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.trialDeps n
  | .inl (.wctNode n)=>wTrialDeps n
  | _=>[]
def msgDeps (L : EncLeaf) : List Coord :=
  (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.msgSlots L).map Prod.fst++
    (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.msgSlots L).flatMap (fun cs=>coordTrialDeps cs.1)

def padTrialDeps (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (side : Fin 2) : List Coord :=
  match padCoord index coord branch side with
  | some (.inl (.wctNode n))=>wTrialDeps n
  | _=>[]
def padDeps (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) : List Coord :=
  padTrialDeps index coord branch 0++padTrialDeps index coord branch 1

def cellDepsP : Node → List Coord
  | .node n=>OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.cellDeps (.node n)
  | .wctNode n=>(OuterResidualGroundChildren.childSlots (.wctNode n)).map Prod.fst++wTrialDeps n++
    childWTrialDeps n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)++
    childWTrialDeps n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)++
    padDeps n.1.index n.1.coord (n.1.idx.val/2)
  | .wctLeaf L=>(OuterResidualGroundChildren.childSlots (.wctLeaf L)).map Prod.fst++padDeps L.index L.coord (L.child.val%2)
  | N=>(OuterResidualGroundChildren.childSlots N).map Prod.fst
end OuterResidualPadModel
