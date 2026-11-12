import SigGolfCandidate.OuterCanonSourceLeaves
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance] Classical.propDecidable

theorem node_ground (index : Fin (2^31)) (coord : Fin 9) (ps : Nat→Digest×Digest)
    (left right : Digest) (level c : Nat) (hc : c<2^(6-level))
    (hg : OuterExtractGround.ftsNonceLevel coord.val level) :
    OuterCanonicalNode.node (decide (first coord.val)) coord.val index.val (2^(6-level)+c) ps left right=
      Prod.snd <$> OuterExtractGround.nodeAt coord.val index.val (2^(6-level)+c) left right := by
  rcases hg with hi|⟨rfl,hf⟩
  · have hl:=Extract.Paired.ftsNonceLevel_le hi
    have hh:=(Extract.Paired.ftsNonceLevel_node (coord:=coord.val) (by omega) hc).mp hi
    have h8:=WCT9.ftsGround_ge8 hh
    rw [OuterCanonicalNodeGround.groundG _ _ _ _ _ hh]
    unfold OuterExtractGround.nodeAt
    rw [if_neg (by omega)]
    rfl
  · have hfirst : decide (first coord.val)=Extract.Paired.first coord.val:=rfl
    have hc2 : c<2:=by norm_num at hc;omega
    simp only [show (6:Nat)-5=1 by decide,show (2:Nat)^1=2 by decide]
    unfold OuterCanonicalNode.node OuterExtractGround.nodeAt
    rw [hfirst,hf,if_pos (by simp;omega),if_pos (by omega)]
theorem source_nodes_rec (answers : Answers) (labels : Labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b) :
    NodesRec answers labels index coord
      (OuterCanonicalModel.nodes answers (decide (first coord.val)) index.val coord.val ps) := by
  intro level hl c hc
  have hl6:level<6 := by unfold topLevel at hl;split_ifs at hl <;> omega
  have hr : Research.SharedForest.heapCut (decide (first coord.val))≤2^(6-level)+c ∧
      2^(6-level)+c<128 := by
    interval_cases level <;> norm_num at hc ⊢
    all_goals unfold Research.SharedForest.heapCut
    all_goals split_ifs with hf <;> try omega
    all_goals have hf':first coord.val := of_decide_eq_true hf
    all_goals simp only [topLevel,if_pos hf'] at hl
    all_goals omega
  have hg:=OuterCanonicalNode.graph answers (decide (first coord.val)) index.val coord.val ps
  have he:=hg.2.2 (2^(6-level)+c) hr.1 hr.2 (by have:=Research.SharedForest.heapCut_bounds (decide (first coord.val));omega)
  by_cases h3 : OuterExtractGround.ftsNonceLevel coord.val level
  · rw [if_pos h3,he,node_ground index coord ps _ _ level c hc h3,evalWithAnswerFn_map]
  rw [if_neg h3]
  have hpad : (if level=4 then (ps (c/2)).2 else (0:Digest))=
      (if level=4 then (pads labels index coord (c/2)).2 else 0) := by
    by_cases h4:level=4
    · subst level
      have hc4:c<4 := by simpa using hc
      rw [if_pos rfl,hps _ (by omega),if_pos rfl]
    · rw [if_neg h4,if_neg h4]
  exact he.trans ((sharedNode_eval answers index coord ps _ _ level c hl hc h3).trans
    (congrArg (fun pad:Digest=>Extract.Paired.proj (.wctNode index.val coord.val level c)
      (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level)+c)
        ((OuterCanonicalModel.nodes answers (decide (first coord.val)) index.val coord.val ps).getD (2*(2^(6-level)+c)) 0)
        pad
        ((OuterCanonicalModel.nodes answers (decide (first coord.val)) index.val coord.val ps).getD (2*(2^(6-level)+c)+1) 0))))))) hpad))

theorem source_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b)
    (level c : Nat) (hl : level≤topLevel coord) (hc : c<2^(7-level)) :
    (OuterCanonicalModel.nodes answers (decide (first coord.val)) index.val coord.val ps).getD
      (2^(7-level)+c) 0=ftsLabel labels index coord level c := by
  apply nodes_label answers labels h index coord _ _ (source_nodes_rec answers labels index coord ps hps) level c hl hc
  intro j hj
  have hg:=OuterCanonicalNode.graph answers (decide (first coord.val)) index.val coord.val ps
  rw [hg.2.1 (128+j) (by omega) (by omega),Nat.add_sub_cancel_left]
  exact source_leaves_label answers labels h index coord ps hps j hj

#print axioms source_nodes_rec
#print axioms source_nodes_label
end OuterCanonBase.Paired
