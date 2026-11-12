import SigGolfCandidate.OuterPairedQueries
import SigGolfCandidate.OuterGroundDeterministic
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterPairedStructural
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance] Classical.propDecidable
variable (T : Answers) (index : Nat) (hidx : index<2^31)
 include hidx in
theorem sat_sharedNode (coord : Coord) (heap : Nat)
    (hcut:SharedForest.heapCut (Extract.Paired.first coord.val) ≤ heap) (hh:heap<128) :
    QueriesSat T (HonestQuery T)
      (OuterCanonicalNode.node (Extract.Paired.first coord.val) coord.val index heap
        (OuterExtractModel.pads T index coord.val)
        ((OuterExtractModel.nodes T index coord.val).getD (2*heap) 0)
        ((OuterExtractModel.nodes T index coord.val).getD (2*heap+1) 0)) := by
  by_cases ho : Extract.Paired.first coord.val=false ∧ heap<4
  · have h2 : 2≤heap := (SharedForest.heapCut_bounds _).1.trans hcut
    have hsn : OuterCanonicalNode.node (Extract.Paired.first coord.val) coord.val index heap
        (OuterExtractModel.pads T index coord.val) ((OuterExtractModel.nodes T index coord.val).getD (2*heap) 0)
        ((OuterExtractModel.nodes T index coord.val).getD (2*heap+1) 0) =
        Prod.snd <$> OuterGroundCore.nodeAt coord.val index heap ((OuterExtractModel.nodes T index coord.val).getD (2*heap) 0)
          ((OuterExtractModel.nodes T index coord.val).getD (2*heap+1) 0) := by
      unfold OuterCanonicalNode.node;rw [if_pos ho]
    rw [hsn]
    refine QueriesSat.map _ ?_
    unfold OuterGroundCore.nodeAt
    refine sat_outerSearch T coord.val index heap _ _ _ 0 (fun k _ hk => ?_)
    have hk' : k≤OuterExtractModel.honestFtsNonce T index coord.val heap := by
      simpa only [OuterExtractModel.honestFtsNonce,OuterExtractGround.nodeAt,if_pos ho.2,OuterGroundCore.nodeAt] using hk
    change HonestQuery T (.inl (.inr (pad64 (wctTopInput coord.val index heap
      ((OuterExtractModel.nodes T index coord.val).getD (2*heap) 0) (BitVec.ofNat 128 (k%2^64))
      ((OuterExtractModel.nodes T index coord.val).getD (2*heap+1) 0)))))
    rcases Nat.lt_or_ge k (OuterExtractModel.honestFtsNonce T index coord.val heap) with hlt|hge
    · exact Or.inr (Or.inr (Or.inr ⟨index,coord.val,heap,k,hidx,coord.isLt,Or.inr ⟨h2,ho.2,ho.1⟩,hlt,rfl⟩))
    · have heq:=le_antisymm hk' hge
      subst k
      obtain ⟨c,rfl⟩ : ∃c,heap=2+c := ⟨heap-2,by omega⟩
      refine Or.inr (Or.inl ⟨.wctNode index coord.val 5 c,⟨⟨hidx,coord.isLt,by decide,by norm_num;omega⟩,?_⟩,?_⟩)
      · intro hf;rw [ho.1] at hf;cases hf
      · have hn : OuterExtractGround.ftsNonceLevel coord.val 5:=Or.inr ⟨rfl,ho.1⟩
        simp only [OuterExtractModel.honestInput,if_neg (show (5:Nat)≠4 by decide),if_pos hn,
          show 2^(6-5)+c=2+c by norm_num]
  by_cases hg : WCT9.ftsGround coord.val heap
  · -- E8: the FTS ground trials are honest queries: the found one is the honest input, the earlier ones `FtsTrial`s.
    have h8 := WCT9.ftsGround_ge8 hg
    have h32 : heap < 32 := by unfold WCT9.ftsGround at hg; omega
    have hsn : OuterCanonicalNode.node (Extract.Paired.first coord.val) coord.val index heap
        (OuterExtractModel.pads T index coord.val) ((OuterExtractModel.nodes T index coord.val).getD (2*heap) 0)
        ((OuterExtractModel.nodes T index coord.val).getD (2*heap+1) 0) =
        ftsNodeG coord.val index heap ((OuterExtractModel.nodes T index coord.val).getD (2*heap) 0)
          ((OuterExtractModel.nodes T index coord.val).getD (2*heap+1) 0) := by
      unfold OuterCanonicalNode.node;rw [if_neg ho];unfold SharedForest.sharedNode;rw [if_neg (by omega),if_neg (by omega)]
    have hat : ∀ l r : Digest, WCT9.ftsNodeAt coord.val index heap l r =
        WCT9.ftsNonceSearch coord.val index heap l r (WCT9.ftsNonceCap coord.val heap - 1) 0 := fun l r => by
      unfold WCT9.ftsNodeAt; rw [if_neg (WCT9.ftsZeroBits_pos hg)]
    rw [hsn]
    unfold ftsNodeG
    refine QueriesSat.map _ ?_
    rw [hat]
    refine ClaudeWCT.W9.T3.Security.Wots.PairedStructural.sat_ftsNonceSearch T coord.val index heap _ _ _ 0 (fun k _ hk => ?_)
    rw [← hat] at hk
    have hk' : k ≤ OuterExtractModel.honestFtsNonce T index coord.val heap := by
      simpa only [OuterExtractModel.honestFtsNonce,OuterExtractGround.nodeAt,if_neg (show ¬heap<4 by omega)] using hk
    clear hk
    unfold ClaudeWCT.W9.T3.Security.Wots.PairedStructural.ftsQueryN
    rw [ftsNodeInputN_eq_top]
    rcases Nat.lt_or_ge k (OuterExtractModel.honestFtsNonce T index coord.val heap) with hlt | hge
    · exact Or.inr (Or.inr (Or.inr ⟨index, coord.val, heap, k, hidx, coord.isLt, Or.inl hg, hlt, rfl⟩))
    · have heq : k = OuterExtractModel.honestFtsNonce T index coord.val heap := le_antisymm hk' hge
      subst heq
      by_cases h16 : heap < 16
      · obtain ⟨c, rfl⟩ : ∃ c, heap = 8 + c := ⟨heap - 8, by omega⟩
        refine Or.inr (Or.inl ⟨.wctNode index coord.val 3 c, ⟨⟨hidx, coord.isLt, by decide, by norm_num; omega⟩,
          fun _ => by decide⟩, ?_⟩)
        have hnl : OuterExtractGround.ftsNonceLevel coord.val 3 := Or.inl (Or.inl rfl)
        simp only [OuterExtractModel.honestInput, if_neg (show (3:Nat) ≠ 4 by decide), hnl, if_true,
          show 2 ^ (6 - 3) + c = 8 + c by norm_num]
      · obtain ⟨c, rfl⟩ : ∃ c, heap = 16 + c := ⟨heap - 16, by omega⟩
        have hc4 : coord.val < 4 := by unfold WCT9.ftsGround at hg; omega
        refine Or.inr (Or.inl ⟨.wctNode index coord.val 2 c, ⟨⟨hidx, coord.isLt, by decide, by norm_num; omega⟩,
          fun _ => by decide⟩, ?_⟩)
        have hnl : OuterExtractGround.ftsNonceLevel coord.val 2 := Or.inl (Or.inr ⟨rfl, hc4⟩)
        simp only [OuterExtractModel.honestInput, if_neg (show (2:Nat) ≠ 4 by decide), hnl, if_true,
          show 2 ^ (6 - 2) + c = 16 + c by norm_num]
  have hq:=honest_sharedNode_input T index hidx coord heap hcut hh hg ho
  unfold OuterCanonicalNode.node
  rw [if_neg ho]
  unfold SharedForest.sharedNode
  split_ifs with h4 h8 hf
  · unfold SharedForest.sharedOuterHash
    rw [if_neg (by omega : ¬(4≤heap ∧ heap<8))] at hq
    split_ifs
    · exact SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash _ hq
    · exact ClaudeWCT.WCT9.Wots.Structural.sat_highHash T _ hq
  · rw [if_pos (show 4≤heap ∧ heap<8 by omega)] at hq
    exact ClaudeWCT.WCT9.Wots.Structural.sat_highHash T _ hq
  · rw [if_pos (show 4≤heap ∧ heap<8 by omega)] at hq
    exact SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash _ hq
  · rw [if_neg (by omega : ¬(4≤heap ∧ heap<8)),wctTopInput_zero] at hq
    rw [ftsNodeG_of_zero (ftsZeroBits_off hg), nodeHashH_eq]
    exact ClaudeWCT.WCT9.Wots.Structural.sat_ftsHash T _ _ hq

#print axioms sat_sharedNode
end OuterPairedStructural
