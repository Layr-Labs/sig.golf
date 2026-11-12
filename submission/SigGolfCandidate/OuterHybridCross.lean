import SigGolfCandidate.OuterHybridForestComplete
import SigGolfCandidate.OuterForestDomains
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option trace.profiler false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridCross
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.QuerySpace (queryHeader queryHeader_padded)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open SigGolfCandidate.T3M (allQ_pure allQ_bind allQ_foldlM)
open OuterHybridComplete OuterHybridForestComplete OuterForestBudget
section cross
variable {secret : BitVec 256} {i j : Nat} {S : Nat → Nat → Prop}

theorem nodeHdr_ne_cross (hS : HybridSet j S) (hi : i < 2 ^ 31) (hij : i ≠ j) {coord heap : Nat}
    (hc : coord < 9) (hh : heap < 2 ^ 64) : ∀ c x, S c x → wctNodeHeader coord i heap ≠ wctNodeHeader c j x := by
  intro c x hs he
  have hp := hS c x hs
  obtain ⟨-, e2, -⟩ := ClaudeWCT.WCT9.wctNodeHeader_injective hc hi hh hp.1 hp.2.1
    (by have := hp.heap; omega) he
  exact hij e2

theorem xF_chain (coord selected k start count : Nat) (value : Digest) (hi : k < 6) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.chain i coord selected k start count value) (NotF secret j S) := by
  unfold ClaudeWCT.WCT9.chain
  exact allQ_foldlM _ _ (fun v step => notF_projHash _
    (ftsChainInputW_header (S := fun _ _ => False) (fun _ _ h => h.elim) coord selected k step v)
    (fun c x _ he => ClaudeWCT.WCT9.wctNodeHeader_ne_ftsChainHeaderP c j x _ _ _ _ _ _ hi he.symm)) _

theorem xF_buildChildH (hS : HybridSet j S) (heap coord selected : Nat) (word : Rank) (coefs : List Digest)
    (pad : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap i coord selected word coefs pad) (NotF secret j S) := by
  unfold ClaudeWCT.WCT9.buildChildH
  refine allQ_bind (allQ_foldlM _ _ (fun st k => ?_) _) fun st => ?_
  · exact allQ_bind (xF_chain _ _ _ _ _ _ (by omega)) fun _ => allQ_bind (xF_chain _ _ _ _ _ _ (by omega)) fun _ => allQ_pure _
  · refine allQ_bind ?_ fun _ => allQ_pure _
    unfold ClaudeWCT.WCT9.leafHashH
    refine notF_ftsHash heap (hdr := ClaudeWCT.WCT9.ftsLeafHeader i coord selected) ?_
      (fun c x hs he => ClaudeWCT.WCT9.ftsLeafHeader_ne_wctNodeHeader i coord selected (hS c x hs).1 j x
        (by have := (hS c x hs).heap; omega) he)
    unfold ClaudeWCT.WCT9.leafInputP
    simpa only [List.append_assoc] using
      queryHeader_padded (bytesLE 16 (st.1.getD 0 0)) (bytesLE 16 pad ++ (st.1.drop 1).flatMap (bytesLE 16))
        (bytesLE_length ..) (ClaudeWCT.WCT9.ftsLeafHeader i coord selected)

theorem xF_ftsCoefs (hS : HybridSet j S) (coord : Nat) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.ftsCoefs i coord) (NotF secret j S) := by
  unfold ClaudeWCT.WCT9.ftsCoefs
  refine allQ_foldlM _ _ (fun acc k => ?_) _
  unfold ClaudeWCT.WCT9.ftsSeedPair privatePair privateHash
  exact allQ_bind ((allQueriesSatisfy_query_iff _ _).mpr
    (notF_private (fun c x h => (hS c x h).1) 8 coord i 0 k (by decide))) fun _ => allQ_pure _

theorem xF_sharedNode (hS : HybridSet j S) (hi : i < 2 ^ 31) (hij : i ≠ j) (first : Bool) (coord heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) (hc : coord < 9) (hh : heap < 128) :
    AllQueriesSatisfy (sharedNode first coord i heap pads left right) (NotF secret j S) := by
  have hne := nodeHdr_ne_cross hS hi hij hc (show heap < 2 ^ 64 by omega)
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
      · exact notF_shortHash (fTrial_header coord i heap n left right) hne

theorem allQ_foldlM_mem {α β : Type} {P : Spec.Domain → Prop} (f : α → β → M α) :
    ∀ (l : List β) (init : α), (∀ a, ∀ b ∈ l, AllQueriesSatisfy (f a b) P) →
      AllQueriesSatisfy (l.foldlM f init) P
  | [], init, _ => by rw [List.foldlM_nil]; exact allQ_pure _
  | b :: l, init, h => by
      rw [List.foldlM_cons]
      exact allQ_bind (h init b (List.mem_cons_self ..)) fun a =>
        allQ_foldlM_mem f l a (fun a' b' hb' => h a' b' (List.mem_cons_of_mem _ hb'))

theorem xF_buildSharedCoordinate (hS : HybridSet j S) (hi : i < 2 ^ 31) (hij : i ≠ j) (first : Bool)
    (coord : Nat) (hc : coord < 9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (buildSharedCoordinate first i coord selected word pads) (NotF secret j S) := by
  unfold buildSharedCoordinate sharedHeap
  refine allQ_bind (xF_ftsCoefs hS coord) fun coefs => allQ_bind
    (allQ_foldlM _ _ (fun _ _ => allQ_bind (xF_buildChildH hS _ _ _ _ _ _) fun _ => allQ_pure _) _) fun _ =>
    allQ_bind (allQ_foldlM_mem _ _ _ (fun nodes heap hm => ?_)) fun _ => allQ_pure _
  have hh : heap < 128 := by
    rw [List.mem_reverse, List.mem_range'_1] at hm
    cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;> omega
  exact allQ_bind (xF_sharedNode hS hi hij first coord heap pads _ _ hc hh) fun _ => allQ_pure _


theorem xF_hashN (hS : HybridSet j S) (hi : i<2^31) (hij : i≠j) (coord heap n : Nat)
    (hc : coord<9) (hh : heap<128) (l r : Digest) :
    AllQueriesSatisfy (OuterGroundCore.hashN coord i heap n l r) (NotF secret j S) := by
  have hne := nodeHdr_ne_cross hS hi hij hc (show heap<2^64 by omega)
  have hq : NotF secret j S (.inl (.inr (fTrial coord i heap n l r))) :=
    notF_public (fTrial_header coord i heap n l r) hne
  unfold OuterGroundCore.hashN publicQuery
  exact allQ_bind ((allQueriesSatisfy_query_iff _ _).mpr hq) (fun _=>allQ_pure _)
theorem xF_search (hS : HybridSet j S) (hi : i<2^31) (hij : i≠j) (coord heap : Nat)
    (hc : coord<9) (hh : heap<128) (l r : Digest) :
    ∀ fuel n,AllQueriesSatisfy (OuterGroundCore.search coord i heap l r fuel n) (NotF secret j S)
  | 0,n => by
    unfold OuterGroundCore.search
    exact allQ_bind (xF_hashN hS hi hij coord heap n hc hh l r) (fun _=>allQ_pure _)
  | fuel+1,n => by
    unfold OuterGroundCore.search
    apply allQ_bind (xF_hashN hS hi hij coord heap n hc hh l r)
    intro v
    split
    · exact allQ_pure _
    · exact xF_search hS hi hij coord heap hc hh l r fuel (n+1)

theorem xF_buildCoord (hS : HybridSet j S) (hi : i<2^31) (hij : i≠j) (first : Bool)
    (coord : Nat) (hc : coord<9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (buildCoord first i coord selected word pads) (NotF secret j S) := by
  cases first with
  | true =>
    rw [buildCoord,if_pos rfl,buildA_eq]
    exact xF_buildSharedCoordinate hS hi hij true coord hc selected word pads
  | false =>
    have hpre : AllQueriesSatisfy (OuterCoordinate.prelude false i coord selected word pads) (NotF secret j S) := by
      unfold OuterCoordinate.prelude OuterCoordinate.children
      refine allQ_bind (xF_ftsCoefs hS coord) (fun coefs=>?_)
      exact allQ_foldlM _ _ (fun (st : List Digest × List Digest) k=>
        allQ_bind (xF_buildChildH hS (128+k) coord (rawChild false k) word coefs (pads (k/64)).1)
          (fun _=>allQ_pure _)) ([],[])
    have hin : ∀ leaves,AllQueriesSatisfy (OuterInnerMoment.innerHeap false i coord pads leaves) (NotF secret j S) := by
      intro leaves
      unfold OuterInnerMoment.innerHeap
      apply allQ_foldlM_mem
      intro nodes heap hm
      have hh : heap<128 := by rw [List.mem_reverse,List.mem_range'_1] at hm;omega
      unfold heapStep
      exact allQ_bind (xF_sharedNode hS hi hij false coord heap pads _ _ hc hh) (fun _=>allQ_pure _)
    have hfin : ∀ nodes,AllQueriesSatisfy (OuterHeapMoment.finish coord i nodes) (NotF secret j S) := by
      intro nodes
      unfold OuterHeapMoment.finish OuterGroundCore.nodeAt
      exact allQ_bind (xF_search hS hi hij coord 3 hc (by decide) _ _ _ _) fun a=>
        allQ_bind (xF_search hS hi hij coord 2 hc (by decide) _ _ _ _) (fun _=>allQ_pure _)
    unfold buildCoord
    simp only [Bool.false_eq_true,↓reduceIte]
    unfold OuterCoordinate.build OuterHeapMoment.heap
    exact allQ_bind hpre (fun st=>allQ_bind (allQ_bind (hin st.1) hfin) (fun _=>allQ_pure _))

theorem xF_pairCheck (hi : i<2^31) (hj : j<2^31) (hij : i≠j) (p : Nat) (hp : p<4) (st : Bool × PairRoot) :
    AllQueriesSatisfy (pairCheck i p st) (NotF secret j (AllAbove 0)) := by
  unfold pairCheck
  exact allQ_bind (xF_buildCoord (hybridSet_above 0 j hj) hi hij true (2*p) (by omega) _ _ _) fun _=>
    allQ_bind (xF_buildCoord (hybridSet_above 0 j hj) hi hij false (2*p+1) (by omega) _ _ _) (fun _=>allQ_pure _)
theorem xF_forestCheck (hi : i<2^31) (hj : j<2^31) (hij : i≠j) :
    AllQueriesSatisfy (forestCheck i) (NotF secret j (AllAbove 0)) := by
  unfold forestCheck
  exact allQ_bind (xF_pairCheck hi hj hij 0 (by decide) _) fun _=>
    allQ_bind (xF_pairCheck hi hj hij 1 (by decide) _) fun _=>
    allQ_bind (xF_pairCheck hi hj hij 2 (by decide) _) fun _=>
    allQ_bind (xF_pairCheck hi hj hij 3 (by decide) _) fun st=>
    allQ_bind (xF_buildCoord (hybridSet_above 0 j hj) hi hij false 8 (by decide) _ _ _) (fun _=>allQ_pure _)
end cross
#print axioms xF_forestCheck
end OuterHybridCross
