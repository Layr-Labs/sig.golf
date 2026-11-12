import SigGolfCandidate.OuterFixedForest
import SigGolfCandidate.OuterVerifierHash
import SigGolfCandidate.Merge097
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterNotEncForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.Final.Credit ClaudeWCT.W9.T3M.Final.Credit.Paired
open SigGolfCandidate.T3M (allQ_bind allQ_pure allQ_foldlM)

theorem hashN (coord index heap n : Nat) (hc : coord<9) (left right : Digest) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord index heap n left right) NotEncS := by
  rw [OuterVerifierHash.hashN_eq]
  split
  · exact notEnc_topLow _ _ _ hc _ _ _
  · exact allQ_highHash_of_shortHash _ (notEnc_topLow _ _ _ hc _ _ _)

theorem recover (index coord : Nat) (hc : coord<9) (selected : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (n3 n2 n5 : Nat) (prev : PairRoot) :
    AllQueriesSatisfy (OuterFixedRecover.recover index coord selected word values path n3 n2 n5 prev) NotEncS := by
  unfold OuterFixedRecover.recover
  exact allQ_bind (notEnc_innerN _ _ _ hc _ _ _ _ _ _ _) fun _=>
    allQ_bind (hashN _ _ _ _ hc _ _) fun _=>allQ_pure _

theorem forest (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening)
    (ns3 ns2 ns5 : List Nat) :
    AllQueriesSatisfy (OuterFixedForest.forest index selected words opened ns3 ns2 ns5) NotEncS := by
  unfold OuterFixedForest.forest
  refine allQ_bind (allQ_foldlM _ _ (fun _ p=>?_) _) fun _=>?_
  · have hp:=p.isLt
    unfold OuterFixedForest.pair
    exact allQ_bind (notEnc_innerN _ _ _ (by omega) _ _ _ _ _ _ _) fun _=>
      recover _ _ (by omega) _ _ _ _ _ _ _ _
  · unfold OuterFixedForest.singleton
    exact recover _ _ (by decide) _ _ _ _ _ _ _ _
#print axioms forest
end OuterNotEncForest
