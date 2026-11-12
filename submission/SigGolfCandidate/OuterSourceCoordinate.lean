import SigGolfCandidate.OuterCoordinateModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSourceCoordinate
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest

def source (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) : M (PairRoot×Nat×Nat×Nat) :=
  if SharedV3.first coord.val then
    (fun r=>(r.1,r.2.1,r.2.2,0)) <$> sourceCoordinate index coord raw word values path prev
  else OuterCanonicalCoordinate.recover index coord raw word values path prev

theorem coordinate_eq_source (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) (p3 p2 : Digest)
    (hi : index<2^31) (hc : ChainReadout w coord word values) (hp : OuterReadout.Path w coord raw path p3 p2)
    (hp2 : 4≤coord.val → p2=0) :
    OuterCoordinateModel.coordinate w index coord raw word prev=source index coord raw word values path prev := by
  cases hf : SharedV3.first coord.val with
  | false=>
    simp only [source,hf,Bool.false_eq_true,if_false]
    exact (OuterCoordinateModel.canonical w index coord raw word values path prev p3 p2 hi hc hp hp2 hf).trans
      (OuterCanonicalCoordinate.canonical_eq_recover index coord raw word values path prev hf)
  | true=>
    rw [OuterCoordinateModel.coordinate_first w index coord raw word prev hf]
    simp only [source,hf,if_true]
    rw [coordinate_canonicalG w index coord raw word values path prev p3 p2 hi hc (OuterReadout.to_old_first hp hf) hp2,
      canonicalCoordinateG_eq_sourceCoordinate]

#print axioms coordinate_eq_source
end OuterSourceCoordinate
