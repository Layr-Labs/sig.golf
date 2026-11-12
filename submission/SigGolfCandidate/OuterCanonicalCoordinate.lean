import SigGolfCandidate.OuterChildModelB
import SigGolfCandidate.OuterChildModelC
import SigGolfCandidate.OuterRecover
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonicalCoordinate
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest

def canonical (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (prev : PairRoot) : M (PairRoot×Nat×Nat×Nat) := do
  let ends←(List.finRange 6).mapM fun i=>ClaudeWCT.WCT9.chain index coord.val raw.val i.val
    (4-wordDigit word i) (wordDigit word i) (values i)
  let j:=SharedV3.physical coord.val raw.val
  let leaf←leafHashH (128+j) index coord.val raw.val prev.1 ends
  let acc←(List.range 5).foldlM (canonicalStepG (SharedV3.first coord.val) index coord.val j path prev.2) (leaf,0,0)
  let lr:=if j/32%2=0 then (acc.1,path 5) else (path 5,acc.1)
  let outer←OuterGroundCore.nodeAt coord.val index ((128+j)/64) lr.1 lr.2
  pure (SharedV3.orderPair coord.val j outer.2 (path 6),acc.2.1,acc.2.2,outer.1)

def recover (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (prev : PairRoot) : M (PairRoot×Nat×Nat×Nat) :=
  OuterRecover.recover index coord.val ⟨SharedV3.physical coord.val raw.val,SharedV3.physical_lt _ _ raw.isLt⟩ word values path prev

theorem canonical_eq_recover (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (prev : PairRoot) (hf : SharedV3.first coord.val=false) :
    canonical index coord raw word values path prev=recover index coord raw word values path prev := by
  have hr : rawChild false (SharedV3.physical coord.val raw.val)=raw.val := by
    have h:=raw_physical_child (SharedV3.first coord.val) raw.val raw.isLt
    simpa only [SharedV3.physical,hf] using h
  unfold canonical recover OuterRecover.recover
  rw [recoverSharedInner_G]
  simp only [hf,hr,bind_assoc,pure_bind]
  have he : 2+SharedV3.physical coord.val raw.val/64=(128+SharedV3.physical coord.val raw.val)/64 := by omega
  rw [he]
  unfold SharedV3.orderPair SharedV3.direction SharedV3.lastLevel
  simp only [hf,Bool.false_eq_true,if_false,show 5+1=6 from rfl,show 2^6=64 from rfl]

#print axioms canonical_eq_recover
end OuterCanonicalCoordinate
