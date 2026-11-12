import SigGolfCandidate.OuterCanonNodes
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
theorem rawLeaf_lt (coord child : Nat) (hc : child<128) : rawLeaf coord child<128 := by
  unfold rawLeaf
  split_ifs <;> omega

theorem pads_raw_branch (labels : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (child : Nat) (hc : child<128) :
    pads labels index coord (child/64)=pads labels index coord (rawLeaf coord.val child%2) := by
  unfold pads
  split_ifs with hz ho
  · rfl
  · have hn:¬first coord.val := by unfold first;omega
    have he:rawLeaf coord.val child%2=child/64 := by unfold rawLeaf;rw [if_neg hn];omega
    rw [he]
  · rfl


 theorem sharedNode_eval (answers : Answers) (index : Fin (2^31)) (coord : Fin 9)
    (ps : Nat → Digest×Digest) (left right : Digest) (level c : Nat)
    (hl : level<topLevel coord) (hc : c<2^(6-level)) (h3 : ¬ OuterExtractGround.ftsNonceLevel coord.val level) :
    evalWithAnswerFn answers (OuterCanonicalNode.node (decide (first coord.val)) coord.val index.val
      (2^(6-level)+c) ps left right) =
      Extract.Paired.proj (.wctNode index.val coord.val level c)
        (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val
          (2^(6-level)+c) left (if level=4 then (ps (c/2)).2 else 0) right))))) := by
  have hl6:level<6 := by unfold topLevel at hl;split_ifs at hl <;> omega
  have hu : Extract.Paired.first coord.val = true → level < 5 := by
    intro hf
    have hf' : first coord.val := of_decide_eq_true hf
    simp only [topLevel, if_pos hf'] at hl
    exact hl
  have hd : decide (first coord.val) = Extract.Paired.first coord.val := rfl
  rw [hd, OuterExtractGround.sharedNode_eq_nodeProgramP index.val coord.val level c coord.isLt hl6 hc hu ps left right
    h3, Extract.Paired.eval_nodeProgram]
  have hpad : (if level=4 then (ps ((2^(6-level)+c)/2-2)).2 else (0:Digest)) =
      (if level=4 then (ps (c/2)).2 else 0) := by
    by_cases h4 : level=4
    · subst level
      rw [if_pos rfl, if_pos rfl, show (2^(6-4)+c)/2-2=c/2 by norm_num; omega]
    · rw [if_neg h4, if_neg h4]
  rw [hpad]
  rfl
theorem childRoot_eq (answers : Answers) (labels : Labels) (h : Agrees answers labels) (L : WctLeafPos) :
    WCT9.childRootH answers (128 + Extract.Paired.physical L.coord.val L.child.val)
      L.index.val L.coord.val L.child.val (pads labels L.index L.coord (L.child.val%2)).1 =
      Extract.Paired.proj (.wctLeaf L.index.val L.coord.val L.child.val) (labels (.wctLeaf L)) := by
  have hends : (List.ofFn fun i : Fin 6 => WCT9.chainEnd answers L.index.val L.coord.val L.child.val i) =
      Extract.wctEnds answers L.index.val L.coord.val L.child.val := rfl
  have hleaf : ∀ pad ends, WCT9.leafHashH (128 + Extract.Paired.physical L.coord.val L.child.val)
      L.index.val L.coord.val L.child.val pad ends =
      WCT9.ftsHash (128 + Extract.Paired.physical L.coord.val L.child.val)
        (Extract.wctLeafInputP L.index.val L.coord.val L.child.val pad ends) := by
    intro pad ends
    unfold WCT9.leafHashH WCT9.leafInputP Extract.wctLeafInputP Extract.listInput
    simp only [List.flatMap_cons, List.append_assoc]
  unfold WCT9.childRootH
  rw [hleaf,hends,wctEnds_eq h L,WCT9.eval_ftsHash,Extract.Paired.proj_wctLeaf]
  exact congrArg (WCT9.ftsHalf (128 + Extract.Paired.physical L.coord.val L.child.val)) (h (.wctLeaf L))

theorem physical_rawLeaf (coord : Fin 9) (c : Nat) (hc : c<128) :
    Extract.Paired.physical coord.val (rawLeaf coord.val c)=c := by
  unfold Extract.Paired.physical Research.SharedForest.physicalChild Extract.Paired.first rawLeaf
  by_cases hf : first coord.val
  · have hf' : decide (coord.val<8 ∧ coord.val%2=0)=true := decide_eq_true hf
    simp only [hf', if_pos hf, ↓reduceIte]
  · have hf' : decide (coord.val<8 ∧ coord.val%2=0)=false := decide_eq_false hf
    simp only [hf', if_neg hf, Bool.false_eq_true, ↓reduceIte]
    omega

theorem rawChild_eq (coord child : Nat) :
    Research.SharedForest.rawChild (decide (first coord)) child=rawLeaf coord child := by
  simp only [Research.SharedForest.rawChild,rawLeaf,decide_eq_true_eq]

theorem source_leaves_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (ps : Nat → Digest×Digest)
    (hps : ∀b,b<2 → ps b=pads labels index coord b) (c : Nat) (hc : c<128) :
    (Research.SharedForest.sharedLeaves answers (decide (first coord.val)) index.val coord.val ps).getD c 0 =
      ftsLabel labels index coord 0 c := by
  unfold Research.SharedForest.sharedLeaves
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact hc),List.getElem_ofFn]
  rw [rawChild_eq,hps _ (by omega),pads_raw_branch labels index coord c hc]
  have he:=childRoot_eq answers labels h ⟨index,coord,⟨rawLeaf coord.val c,rawLeaf_lt _ _ hc⟩⟩
  simp only [physical_rawLeaf coord c hc] at he
  unfold ftsLabel
  rw [if_pos rfl,dif_pos (rawLeaf_lt _ _ hc)]
  exact he


#print axioms source_leaves_label
#print axioms sharedNode_eval
end OuterCanonBase.Paired
