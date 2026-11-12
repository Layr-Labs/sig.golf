import SigGolfCandidate.OuterGroundFresh
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterGroundAvoid
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness SigGolfCandidate.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (Rank Child wctNodeHeader)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open SigGolfCandidate.T3M (allQ_pure allQ_bind allQ_foldlM)

def OP (coord index heap : Nat) : Prop := coord<9 ∧ index<2^31 ∧ 2≤heap ∧ heap<128
theorem OP.heap {coord index heap : Nat} (h : OP coord index heap) : 2≤heap ∧ heap<128 := h.2.2
def OuterSet (index : Nat) (S : Nat → Nat → Prop) : Prop := ∀ c x,S c x→OP c index x
section
variable {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop} (hS : OuterSet index S)
include hS
theorem ftsChainInputW_header (coord selected i step : Nat) (value : Digest) :
    queryHeader (pad64 (ClaudeWCT.WCT9.ftsChainInputW index coord selected i step value)) =
      bytesLE 16 (ClaudeWCT.WCT9.ftsChainHeader index coord selected i step) := by
  unfold ClaudeWCT.WCT9.ftsChainInputW
  split
  · simpa only [List.append_assoc] using
      queryHeader_padded (bytesLE 16 value) (zero16 ++ zero16) (bytesLE_length ..)
        (ClaudeWCT.WCT9.ftsChainHeader index coord selected i step)
  · simpa only [ClaudeWCT.WCT9.chainInput, List.append_assoc] using
      queryHeader_padded zero16 (_ : HashInput) (by simp [zero16])
        (ClaudeWCT.WCT9.ftsChainHeader index coord selected i step)

theorem notF_chain (coord selected i start count : Nat) (value : Digest) (hi : i < 6) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.chain index coord selected i start count value) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.chain
  exact allQ_foldlM _ _ (fun v step => notF_projHash _ (ftsChainInputW_header hS coord selected i step v)
    (fun c x _ he => ClaudeWCT.WCT9.wctNodeHeader_ne_ftsChainHeaderP c index x _ _ _ _ _ _ hi he.symm)) _

theorem notF_leafHashH (heap coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.leafHashH heap index coord selected pad ends) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.leafHashH
  refine notF_ftsHash heap (hdr := ClaudeWCT.WCT9.ftsLeafHeader index coord selected) ?_
    (fun c x hs he => ClaudeWCT.WCT9.ftsLeafHeader_ne_wctNodeHeader index coord selected (hS c x hs).1 index x
      (by have := (hS c x hs).heap; omega) he)
  unfold ClaudeWCT.WCT9.leafInputP
  simpa only [List.append_assoc] using
    queryHeader_padded (bytesLE 16 (ends.getD 0 0)) (bytesLE 16 pad ++ (ends.drop 1).flatMap (bytesLE 16))
      (bytesLE_length ..) (ClaudeWCT.WCT9.ftsLeafHeader index coord selected)

theorem notF_buildChildH (heap coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs pad) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.buildChildH
  refine allQ_bind (allQ_foldlM _ _ (fun st i => ?_) _) fun st => ?_
  · exact allQ_bind (notF_chain hS _ _ _ _ _ _ (by omega)) fun _ =>
      allQ_bind (notF_chain hS _ _ _ _ _ _ (by omega)) fun _ => allQ_pure _
  · exact allQ_bind (notF_leafHashH hS _ _ _ _ _) fun _ => allQ_pure _

theorem notF_ftsCoefs (coord : Nat) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.ftsCoefs index coord) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.ftsCoefs
  refine allQ_foldlM _ _ (fun acc j => ?_) _
  unfold ClaudeWCT.WCT9.ftsSeedPair privatePair privateHash
  exact allQ_bind ((allQueriesSatisfy_query_iff _ _).mpr
    (notF_private (fun c x h => (hS c x h).1) 8 coord index 0 j (by decide))) fun _ => allQ_pure _

/-- The children of a coordinate (coefficients and the 128 leaves) avoid every ground trial. -/
theorem notF_children (first : Bool) (coord : Nat) (word : Rank) (selected : Child) (pads : Nat → PairRoot)
    (coefs : List Digest) :
    AllQueriesSatisfy ((List.range 128).foldlM
      (fun (state : List Digest × List Digest) j => do
        let (root, values) ← ClaudeWCT.WCT9.buildChildH (128 + j) index coord (rawChild first j) word coefs
          (pads (j / 64)).1
        pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], []))
      (NotF secret index S) :=
  allQ_foldlM _ _ (fun _ _ => allQ_bind (notF_buildChildH hS _ _ _ _ _ _) fun _ => allQ_pure _) _


theorem node_ne_set (coord heap : Nat) (hc : coord<9) (hh : heap<128)
    (hn : ¬S coord heap) : ∀ c x,S c x→wctNodeHeader coord index heap≠wctNodeHeader c index x := by
  intro c x hs he
  have hp:=hS c x hs
  obtain ⟨e1,-,e3⟩:=ClaudeWCT.WCT9.wctNodeHeader_injective hc hp.2.1 (by omega) hp.1 hp.2.1
    (by have := hp.heap;omega) he
  exact hn (e1 ▸ e3 ▸ hs)

theorem notF_sharedNode_external (first : Bool) (coord heap : Nat) (pads : Nat → PairRoot) (l r : Digest)
    (hc : coord<9) (hh : heap<128) (hn : ¬S coord heap) :
    AllQueriesSatisfy (sharedNode first coord index heap pads l r) (NotF secret index S) := by
  have hne:=node_ne_set hS coord heap hc hh hn
  unfold sharedNode
  split
  · unfold sharedOuterHash
    split
    · exact notF_shortHash (wctTopInput_header ..) hne
    · exact notF_highHash (wctTopInput_header ..) hne
  · split
    · split
      · exact notF_highHash (wctTopInput_header ..) hne
      · exact notF_shortHash (wctTopInput_header ..) hne
    · refine ClaudeWCT.WCT9.allQ_ftsNodeG _ _ _ _ _ ?_ (fun n _ => ?_)
      · unfold ClaudeWCT.WCT9.wctNodeHashH
        exact notF_ftsHash heap (nodeH_header ..) hne
      · exact notF_shortHash (fTrial_header coord index heap n l r) hne


end
#print axioms notF_sharedNode_external
#print axioms notF_children
#print axioms notF_ftsCoefs
end OuterGroundAvoid
