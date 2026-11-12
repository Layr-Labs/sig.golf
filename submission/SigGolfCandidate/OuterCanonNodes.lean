import SigGolfCandidate.OuterCanonInnerStep
import SigGolfCandidate.OuterCanonOuterStep
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
def topLevel (coord : Fin 9) : Nat := if first coord.val then 5 else 6

/-- The source heap recurrence, expressed with the fixed projection of its address. -/
def NodesRec (answers : Answers) (labels : Labels) (index : Fin (2^31)) (coord : Fin 9)
    (nodes : Array Digest) : Prop :=
  ∀ level, level<topLevel coord → ∀ c,c<2^(6-level) →
    nodes.getD (2^(6-level)+c) 0 =
      if OuterExtractGround.ftsNonceLevel coord.val level then
        (evalWithAnswerFn answers (OuterExtractGround.nodeAt coord.val index.val (2^(6-level)+c)
          (nodes.getD (2*(2^(6-level)+c)) 0) (nodes.getD (2*(2^(6-level)+c)+1) 0))).2
      else Extract.Paired.proj (.wctNode index.val coord.val level c)
        (answers (.inl (.inr (pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val
          (2^(6-level)+c) (nodes.getD (2*(2^(6-level)+c)) 0)
          (if level=4 then (pads labels index coord (c/2)).2 else 0)
          (nodes.getD (2*(2^(6-level)+c)+1) 0))))))


theorem fts_step (answers : Answers) (labels : Labels) (ha : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hg : OuterExtractGround.ftsNonceLevel coord.val level)
    (hc : c<2^(6-level)) (n : WctNodePos) (hn : ftsNodeAt index coord level c=some n) :
    evalWithAnswerFn answers (OuterExtractGround.nodeAt coord.val index.val (2^(6-level)+c)
      (ftsLabel labels index coord level (2*c)) (ftsLabel labels index coord level (2*c+1)))=
      (wSelNonce labels n,Extract.Paired.proj (.wctNode index.val coord.val level c)
        (labels (.wctNode (wSelNode labels n)))) := by
  rcases hg with hi|⟨rfl,hf⟩
  · have hl:=Extract.Paired.ftsNonceLevel_le hi
    have hh:= (Extract.Paired.ftsNonceLevel_node (coord:=coord.val) (by omega) hc).mp hi
    have h8:=WCT9.ftsGround_ge8 hh
    unfold OuterExtractGround.nodeAt
    rw [if_neg (by omega)]
    exact inner_step answers labels ha index coord level c hi hc n hn
  · have hc2 : c<2:=by norm_num at hc;omega
    unfold OuterExtractGround.nodeAt
    simp only [show (6:Nat)-5=1 by decide,show (2:Nat)^1=2 by decide]
    rw [if_pos (by omega)]
    exact outer_step answers labels ha index coord c hf hc2 n hn
theorem nodes_label (answers : Answers) (labels : Labels) (ha : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (nodes : Array Digest)
    (hleaf : ∀c,c<128 → nodes.getD (128+c) 0=ftsLabel labels index coord 0 c)
    (hnode : NodesRec answers labels index coord nodes)
    (level c : Nat) (hl : level≤topLevel coord) (hc : c<2^(7-level)) :
    nodes.getD (2^(7-level)+c) 0=ftsLabel labels index coord level c := by
  have ht:topLevel coord≤6 := by unfold topLevel;split_ifs <;> omega
  induction level generalizing c with
  | zero=> exact hleaf c (by simpa using hc)
  | succ level ih=>
    have hl6:level<6 := by omega
    have hsub:7-(level+1)=6-level := by omega
    have hc':c<2^(6-level) := by simpa only [hsub] using hc
    have hpow:2^(7-level)=2*2^(6-level) := by rw [←pow_succ'];congr 1;omega
    have hleft : nodes.getD (2^(7-level)+2*c) 0=ftsLabel labels index coord level (2*c) := by
      apply ih <;> omega
    have hright : nodes.getD (2^(7-level)+(2*c+1)) 0=ftsLabel labels index coord level (2*c+1) := by
      apply ih <;> omega
    have hrec:=hnode level (by omega) c hc'
    have haddr:2*(2^(6-level)+c)=2^(7-level)+2*c := by rw [hpow];omega
    have haddr':2*(2^(6-level)+c)+1=2^(7-level)+(2*c+1) := by rw [hpow];omega
    rw [haddr,hleft] at hrec
    rw [show 2^(7-level)+2*c+1=2^(7-level)+(2*c+1) by omega,hright] at hrec
    obtain ⟨n,hn,hindex,hcoord,hlevel,hidx⟩:=OuterCanonBase.ftsNodeAt_some index coord level c hl6
      (by simpa only [show 7-level-1=6-level by omega] using hc')
    by_cases h3 : OuterExtractGround.ftsNonceLevel coord.val level
    · rw [if_pos h3, fts_step answers labels ha index coord level c h3 hc' n hn] at hrec
      rw [hsub, hrec]
      unfold ftsLabel
      rw [if_neg (by omega : level+1≠0),show level+1-1=level by omega,hn]
      all_goals rfl
    rw [if_neg h3] at hrec
    have hcell:cell (secretsOf answers) (.wctNode n) labels =
        pad64 (nodeInputP 3 (WCT9.nodeLayer coord.val) index.val (2^(6-level)+c)
          (ftsLabel labels index coord level (2*c))
          (if level=4 then (pads labels index coord (c/2)).2 else 0)
          (ftsLabel labels index coord level (2*c+1))) := by
      rw [cell_wctNode_active (wActive_zero labels n (OuterCanonBase.ftsNodeAt_nonce hn))]
      simp only [hindex,hcoord,hlevel,hidx,show 7-level-1=6-level by omega, if_neg h3]
    have he:=ha (.wctNode n)
    rw [hcell] at he
    rw [he] at hrec
    rw [hsub,hrec]
    unfold ftsLabel
    rw [if_neg (by omega : level+1≠0),show level+1-1=level by omega,hn]
    simp only [wSelNode_of_cap_one (labels := labels) (n := n) (by rw [hlevel, hcoord]; exact wTrialCap_off h3)
      (OuterCanonBase.ftsNodeAt_nonce hn)]


#print axioms fts_step
#print axioms nodes_label
end OuterCanonBase.Paired
