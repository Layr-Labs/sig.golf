import SigGolfCandidate.OuterCanonSourceNodes
import SigGolfCandidate.OuterCanonTreeSelection
import SigGolfCandidate.OuterExtractModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open ClaudeWCT
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OuterCanonicalModel.nodes OuterCanonicalModel.firstNodes OuterCanonicalModel.secondNodes
def pairLabel (labels : Labels) (index : Fin (2^31)) (pair : Fin 5) : Digest×Digest :=
  if h:pair.val=0 then WCT9.ftsStart else
    let coord:Fin 9:=⟨2*pair.val-1,by have:=pair.isLt;omega⟩
    (ftsLabel labels index coord 6 0,ftsLabel labels index coord 6 1)

theorem pads_even (labels : Labels) (index : Fin (2^31)) (pair : Fin 5) (branch : Nat) :
    pads labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ branch=pairLabel labels index pair := by
  fin_cases pair <;> rfl

theorem pads_odd (labels : Labels) (index : Fin (2^31)) (pair : Fin 4) (branch : Nat) :
    pads labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ branch=
      (ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ 5 (2*branch),
       ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ 5 (2*branch+1)) := by
  fin_cases pair <;> rfl

theorem firstNodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (pair : Fin 4) (prev : Digest×Digest)
    (hp : prev=pairLabel labels index ⟨pair.val,by have:=pair.isLt;omega⟩)
    (level c : Nat) (hl : level≤5) (hc : c<2^(7-level)) :
    (OuterCanonicalModel.firstNodes answers index.val pair.val prev).getD (2^(7-level)+c) 0=
      ftsLabel labels index ⟨2*pair.val,by have:=pair.isLt;omega⟩ level c := by
  let coord:Fin 9:=⟨2*pair.val,by have:=pair.isLt;omega⟩
  have hf:first coord.val := by dsimp[coord];unfold first;omega
  have hpads:∀b,b<2 → prev=pads labels index coord b := by
    intro b hb
    exact hp.trans (pads_even labels index ⟨pair.val,by have:=pair.isLt;omega⟩ b).symm
  have he:=source_nodes_label answers labels h index coord (fun _=>prev) hpads level c
    (by simpa only [topLevel,if_pos hf] using hl) hc
  simpa only [coord,OuterCanonicalModel.firstNodes,decide_eq_true hf] using he

theorem secondNodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (pair : Fin 4) (prev : Digest×Digest)
    (hp : prev=pairLabel labels index ⟨pair.val,by have:=pair.isLt;omega⟩)
    (level c : Nat) (hl : level≤6) (hc : c<2^(7-level)) :
    (OuterCanonicalModel.secondNodes answers index.val pair.val prev).getD (2^(7-level)+c) 0=
      ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ level c := by
  let coord:Fin 9:=⟨2*pair.val+1,by have:=pair.isLt;omega⟩
  have hf:¬first coord.val := by dsimp[coord];unfold first;omega
  have hpads:∀b,b<2 → Research.SharedForest.nodesPair
      (OuterCanonicalModel.firstNodes answers index.val pair.val prev) b=pads labels index coord b := by
    intro b hb
    rw [pads_odd labels index pair b]
    unfold Research.SharedForest.nodesPair
    apply Prod.ext
    · exact firstNodes_label answers labels h index pair prev hp 5 (2*b) (by decide) (by norm_num;omega)
    · simpa only [show 2^(7-5)+(2*b+1)=5+2*b by norm_num;omega] using firstNodes_label answers labels h index pair prev hp 5 (2*b+1) (by decide) (by norm_num;omega)
  have he:=source_nodes_label answers labels h index coord
    (Research.SharedForest.nodesPair (OuterCanonicalModel.firstNodes answers index.val pair.val prev))
    hpads level c (by simpa only [topLevel,if_neg hf] using hl) hc
  simpa only [coord,OuterCanonicalModel.secondNodes,decide_eq_false hf] using he
end OuterCanonBase.Paired

namespace OuterCanonBase.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OuterCanonBase
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OuterCanonicalModel.nodes OuterCanonicalModel.firstNodes OuterCanonicalModel.secondNodes

theorem pairLabel_succ (labels : Labels) (index : Fin (2^31)) (pair : Fin 4) :
    pairLabel labels index ⟨pair.val+1,by have:=pair.isLt;omega⟩ =
      (ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ 6 0,
       ftsLabel labels index ⟨2*pair.val+1,by have:=pair.isLt;omega⟩ 6 1) := by
  fin_cases pair <;> rfl

theorem pairPrev_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) : ∀n,(hn:n≤4) →
      OuterExtractModel.pairPrev answers index.val n=pairLabel labels index ⟨n,by omega⟩
  | 0,_=>rfl
  | n+1,hn=>by
    have ih:=pairPrev_label answers labels h index n (by omega)
    rw [OuterExtractModel.pairPrev,pairLabel_succ labels index ⟨n,by omega⟩]
    apply Prod.ext
    · exact secondNodes_label answers labels h index ⟨n,by omega⟩ _ ih 6 0 (by decide) (by decide)
    · exact secondNodes_label answers labels h index ⟨n,by omega⟩ _ ih 6 1 (by decide) (by decide)

theorem source_pads_even (answers : Answers) (index : Nat) (pair : Fin 5) (branch : Nat) :
    OuterExtractModel.pads answers index (2*pair.val) branch=OuterExtractModel.pairPrev answers index pair.val := by
  fin_cases pair <;> rfl

theorem source_pads_odd (answers : Answers) (index : Nat) (pair : Fin 4) (branch : Nat) :
    OuterExtractModel.pads answers index (2*pair.val+1) branch=
      Research.SharedForest.nodesPair
        (OuterCanonicalModel.firstNodes answers index pair.val (OuterExtractModel.pairPrev answers index pair.val)) branch := by
  fin_cases pair <;> rfl

theorem source_pads_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (hb:branch<2) :
    OuterExtractModel.pads answers index.val coord.val branch=pads labels index coord branch := by
  by_cases he:coord.val%2=0
  · let p:Fin 5:=⟨coord.val/2,by have:=coord.isLt;omega⟩
    have hc:coord=⟨2*p.val,by have:=p.isLt;omega⟩:=by apply Fin.ext;dsimp[p];omega
    rw [hc]
    rw [source_pads_even,pads_even,pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)]
  · let p:Fin 4:=⟨coord.val/2,by have:=coord.isLt;omega⟩
    have hc:coord=⟨2*p.val+1,by have:=p.isLt;omega⟩:=by apply Fin.ext;dsimp[p];omega
    rw [hc]
    rw [source_pads_odd,pads_odd]
    unfold Research.SharedForest.nodesPair
    apply Prod.ext
    · exact firstNodes_label answers labels h index p _
        (pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)) 5 (2*branch) (by decide) (by norm_num;omega)
    · simpa only [show 2^(7-5)+(2*branch+1)=5+2*branch by norm_num;omega] using firstNodes_label answers labels h index p _
        (pairPrev_label answers labels h index p.val (by have:=p.isLt;omega)) 5 (2*branch+1) (by decide) (by norm_num;omega)
end OuterCanonBase.Paired

namespace OuterCanonBase.Paired
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OuterCanonBase
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OuterCanonicalModel.nodes OuterCanonicalModel.firstNodes OuterCanonicalModel.secondNodes

theorem nodes_source (answers : Answers) (index : Nat) (coord : Fin 9) :
    OuterExtractModel.nodes answers index coord.val = OuterCanonicalModel.nodes (answers)
      (decide (first coord.val)) index coord.val (OuterExtractModel.pads answers index coord.val) := by
  fin_cases coord <;> simp only [OuterExtractModel.nodes,OuterExtractModel.first,first,OuterCanonicalModel.firstNodes,OuterCanonicalModel.secondNodes]
  all_goals norm_num
  all_goals first | rfl | (congr 1;funext b;simp only [OuterExtractModel.pads,OuterExtractModel.first,OuterCanonicalModel.firstNodes];rfl)

theorem actual_nodes_label (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat)
    (hl : level≤topLevel coord) (hc:c<2^(7-level)) :
    (OuterExtractModel.nodes answers index.val coord.val).getD (2^(7-level)+c) 0=
      ftsLabel labels index coord level c := by
  rw [nodes_source]
  exact source_nodes_label answers labels h index coord _ (source_pads_label answers labels h index coord) level c hl hc

theorem actual_leaf_pad (answers : Answers) (labels : Labels) (h : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (raw : Fin 128) :
    OuterExtractModel.pads answers index.val coord.val (OuterExtractModel.physical coord.val raw.val/64)=
      pads labels index coord (raw.val%2) := by
  have hp:OuterExtractModel.physical coord.val raw.val<128 :=
    Research.SharedForest.physicalChild_lt _ _ raw.isLt
  rw [source_pads_label answers labels h index coord _ (by omega),pads_raw_branch labels index coord _ hp]
  congr 1
  have he:rawLeaf coord.val (OuterExtractModel.physical coord.val raw.val)=raw.val := by
    rw [←rawChild_eq]
    exact Research.SharedForest.raw_physical_child _ _ raw.isLt
  rw [he]
end OuterCanonBase.Paired


#print axioms OuterCanonBase.Paired.actual_nodes_label
