import SigGolfCandidate.OuterCanonHonest
import SigGolfCandidate.OuterCanonActualNodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots SphincsSecurity.Concrete
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OuterCanonicalModel.nodes OuterCanonicalModel.firstNodes OuterCanonicalModel.secondNodes
theorem honestInput_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    OuterExtractModel.honestInput answers node.toPos=cell (secretsOf answers) (node.sel labels) labels := by
  cases node with
  | chain p=>
      simp only [Node.sel,Node.toPos,OuterExtractModel.honestInput,Extract.honestInput]
      change pad64 (rowW p (Wots.honestChainValueW answers _ _ _ _ (WCT9.wotsSeed answers _ _ _ _) _)) =
        rowW p (priorW _ p _)
      rw [chainValue_eq h p.1 p.2.val (by have := p.2.isLt; omega), rowW_pad64, priorW_eq_valueW]
  | leaf L=>
      simp only [Node.sel,Node.toPos,OuterExtractModel.honestInput,Extract.honestInput,cell,OuterCanonBase.cell]
      rw [leafEnds_eq h L.1]
  | node n=>
      have hv1 : n.1.level.val < height n.1.lay := n.2.1
      have hv2 : n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) := n.2.2.1
      have hv3 : n.1.tree.val < 2 ^ treeBits n.1.lay := n.2.2.2.1
      have hpow : 2 ^ (height n.1.lay - n.1.level.val) = 2 * 2 ^ (height n.1.lay - n.1.level.val - 1) := by
        rw [← pow_succ']; congr 1; omega
      change Extract.honestInput answers (Node.node n).toPos =
        OuterCanonBase.cell (secretsOf answers) (.node (selNode labels n)) labels
      exact honestInput_node_sel (fun m => h (.node m)) n
        (builtTree_eq h _ _ _ _ (by omega) (by omega) hv3 (by omega))
        (builtTree_eq h _ _ _ _ (by omega) (by omega) hv3 (by omega))
  | wctChain p=>
      simp only [Node.sel,Node.toPos,OuterExtractModel.honestInput,Extract.honestInput,cell,OuterCanonBase.cell]
      rw [wctValue_eq h p.1 p.2.val (by have:=p.2.isLt;omega),WCT9.ftsChainInputW_padded]
  | wctLeaf L=>
      simp only [Node.sel,Node.toPos,OuterExtractModel.honestInput,cell]
      rw [wctEnds_eq h L,actual_leaf_pad answers labels h L.index L.coord L.child]
  | wctNode n=>
      have hl6:=n.1.level.isLt
      have hv':n.1.idx.val<2^(6-n.1.level.val) := by
        have := n.2
        unfold WctNodeRaw.Valid at this
        rwa [show 7-n.1.level.val-1=6-n.1.level.val by omega] at this
      have ht:n.1.level.val≤topLevel n.1.coord := by
        unfold topLevel
        split_ifs with hf
        · have hused:=hb.2 (by change decide (first n.1.coord.val)=true;exact decide_eq_true hf)
          omega
        · omega
      have hpow:2^(7-n.1.level.val)=2*2^(6-n.1.level.val) := by
        rw [←pow_succ'];congr 1;omega
      have hsub:7-n.1.level.val-1=6-n.1.level.val := by omega
      have hs := wSelNonce_lt labels n
      have hcl := wTrialCap_le n.1.coord.val n.1.level.val
      have ha := wActive_trial_of_le (labels := labels) (n := n) le_rfl
      change OuterExtractModel.honestInput answers (Node.wctNode n).toPos =
        cell (secretsOf answers) (.wctNode (wWithNonce n (wSelNonce labels n))) labels
      rw [cell_wctNode_active ha]
      simp only [Node.toPos, OuterExtractModel.honestInput, OuterExtractModel.honestFtsNonce, wWithNonce_index,
        wWithNonce_coord, wWithNonce_level, wWithNonce_idx, wWithNonce_nonce n (show wSelNonce labels n < 4096 by omega),
        hsub]
      change pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val (2^(6-n.1.level.val)+n.1.idx.val) _ _ _) = _
      rw [show 2*(2^(6-n.1.level.val)+n.1.idx.val)=2^(7-n.1.level.val)+2*n.1.idx.val by omega,
        show 2^(7-n.1.level.val)+2*n.1.idx.val+1=2^(7-n.1.level.val)+(2*n.1.idx.val+1) by omega,
        actual_nodes_label answers labels h n.1.index n.1.coord n.1.level.val (2*n.1.idx.val) ht (by omega),
        actual_nodes_label answers labels h n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1) ht (by omega)]
      by_cases h4:n.1.level.val=4
      · rw [if_pos h4,h4]
        have hi:n.1.idx.val<4 := by simpa [h4] using hv'
        rw [show (2^(6-4)+n.1.idx.val)/2-2=n.1.idx.val/2 by norm_num;omega,
          source_pads_label answers labels h n.1.index n.1.coord _ (by omega),if_pos rfl]
      · rw [if_neg h4,if_neg h4]
        by_cases h3:OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val
        · rw [if_pos h3,if_pos h3]
          have hfs := fts_step answers labels h n.1.index n.1.coord n.1.level.val n.1.idx.val h3 hv'
            (wWithNonce n 0) (ftsNodeAt_of_node n)
          rw [hfs]
          rfl
        · rw [if_neg h3,if_neg h3]
  | forest index=>exact hb.elim

theorem honest_answer (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (node : Node) (hb : Extract.Paired.Bounded node.toPos) :
    answers (.inl (.inr (OuterExtractModel.honestInput answers node.toPos)))=labels (node.sel labels) := by
  rw [honestInput_eq answers labels h node hb]
  exact h (node.sel labels)

#print axioms honestInput_eq
#print axioms honest_answer
end OuterCanonBase.Paired
