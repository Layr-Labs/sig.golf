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
/-- C47 (C): a public query that is not 64 bytes long is no (64-byte) FTS node trial. -/
theorem notF_public_long {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop} {input : HashInput}
    (hl : input.length ≠ 64) : NotF secret index S (.inl (.inr input)) := by
  intro coord heap _ n l r
  show input ≠ _
  intro he
  have := fTrial_length coord index heap n l r
  rw [← he] at this
  exact hl this
/-- C47 (C): a leaf hash of at least three chain ends is longer than 64 bytes, hence no FTS node trial (coordinate 8's
heap-2 header `(0, base)` equals coordinate 6's child-0 leaf header). -/
theorem notF_leafHash_long {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop}
    (heap i coord selected : Nat) (pad : Digest) (ends : List Digest) (hlen : 3 ≤ ends.length) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.leafHashH heap i coord selected pad ends) (NotF secret index S) := by
  obtain ⟨e0, e1, e2, rest, rfl⟩ : ∃ e0 e1 e2 rest, ends = e0 :: e1 :: e2 :: rest := by
    match ends, hlen with
    | e0 :: e1 :: e2 :: rest, _ => exact ⟨e0, e1, e2, rest, rfl⟩
  have hl : (pad64 (ClaudeWCT.WCT9.leafInputP i coord selected pad (e0 :: e1 :: e2 :: rest))).length ≠ 64 := by
    have h1 : 80 ≤ (ClaudeWCT.WCT9.leafInputP i coord selected pad (e0 :: e1 :: e2 :: rest)).length := by
      simp [ClaudeWCT.WCT9.leafInputP, bytesLE_length] <;> omega
    have h3 : (ClaudeWCT.WCT9.leafInputP i coord selected pad (e0 :: e1 :: e2 :: rest)).length ≤
        (pad64 (ClaudeWCT.WCT9.leafInputP i coord selected pad (e0 :: e1 :: e2 :: rest))).length := by
      simp only [pad64, List.length_append, List.length_replicate]; omega
    omega
  have hp : AllQueriesSatisfy (publicHash (ClaudeWCT.WCT9.leafInputP i coord selected pad (e0 :: e1 :: e2 :: rest)))
      (NotF secret index S) := (allQueriesSatisfy_query_iff _ _).mpr (notF_public_long hl)
  unfold ClaudeWCT.WCT9.leafHashH ClaudeWCT.WCT9.ftsHash
  split
  · unfold ClaudeWCT.WCT9.highHash; exact allQ_bind hp fun _ => allQ_pure _
  · unfold shortHash; exact allQ_bind hp fun _ => allQ_pure _
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

/-- C47 (C): with at least three ends (the outer set may contain coordinate 8's heap 2, whose header equals coordinate
6's child-0 leaf header; the leaf query is longer). -/
theorem notF_leafHashH (heap coord selected : Nat) (pad : Digest) (ends : List Digest) (hlen : 3 ≤ ends.length) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.leafHashH heap index coord selected pad ends) (NotF secret index S) :=
  notF_leafHash_long heap index coord selected pad ends hlen

theorem notF_buildChildH (heap coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs pad) (NotF secret index S) := by
  -- C47 (C): unfold the six chain steps so that the leaf sees its six ends (`notF_leafHash_long`).
  unfold ClaudeWCT.WCT9.buildChildH
  rw [show List.finRange 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind]
  repeat (refine allQ_bind (notF_chain hS _ _ _ _ _ _ (Fin.isLt _)) fun _ => ?_)
  exact allQ_bind (notF_leafHash_long _ _ _ _ _ _ (by simp)) fun _ => allQ_pure _

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


/-- C46: pair-mates share the tag base, so the heap must be a fold heap (`2 ≤ heap`). -/
theorem node_ne_set (coord heap : Nat) (hc : coord<9) (hh : heap<128) (h2 : 2≤heap)
    (hn : ¬S coord heap) : ∀ c x,S c x→wctNodeHeader coord index heap≠wctNodeHeader c index x := by
  intro c x hs he
  have hp:=hS c x hs
  obtain ⟨e1,-,e3⟩:=ClaudeWCT.WCT9.wctNodeHeader_injective_of hc hp.2.1 (by omega) hp.1 hp.2.1
    (by have := hp.heap;omega)
    (Or.inl ⟨ClaudeWCT.WCT9.ftsTwoOk_of h2 hh,ClaudeWCT.WCT9.ftsTwoOk_of hp.heap.1 hp.heap.2⟩) he
  exact hn (e1 ▸ e3 ▸ hs)

theorem notF_sharedNode_external (first : Bool) (coord heap : Nat) (pads : Nat → PairRoot) (l r : Digest)
    (hc : coord<9) (hh : heap<128) (h2 : 2≤heap) (hn : ¬S coord heap) :
    AllQueriesSatisfy (sharedNode first coord index heap pads l r) (NotF secret index S) := by
  have hne:=node_ne_set hS coord heap hc hh h2 hn
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
