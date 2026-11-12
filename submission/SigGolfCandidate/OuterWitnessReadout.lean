import SigGolfCandidate.OuterWitnessWindows
import SigGolfCandidate.OuterForestModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterWitnessReadout
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired
open OuterWitnessOverlay

theorem chain (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (k : Fin 9) (word : Rank) (values : Fin 6 → Digest) (h : ChainReadout (witEncF16 output w) k word values) :
    ChainReadout (OuterExpand.witEncOuter output w nonces) k word values := by
  refine ⟨fun i=>Eq.trans ?_ (h.padA i),fun i=>Eq.trans ?_ (h.padB i),fun i=>Eq.trans ?_ (h.padC i),fun i=>Eq.trans ?_ (h.reveal i)⟩
  · unfold V3.chainPadA V3.chainOffset
    rw [Nat.add_assoc]
    exact wdig_region output w nonces k _ (OuterWitnessWindows.chain i).1
  · unfold V3.chainPadB V3.chainOffset
    rw [Nat.add_assoc]
    exact extract_region output w nonces k _ 8 (OuterWitnessWindows.chain i).2.1
  · unfold V3.chainPadC V3.chainOffset
    rw [Nat.add_assoc]
    exact wdig_region output w nonces k _ (OuterWitnessWindows.chain i).2.2.1
  · unfold V3.reveal V3.chainOffset
    split_ifs
    · exact wdig_region output w nonces k _ (OuterWitnessWindows.chain i).2.2.2.1
    · rw [Nat.add_assoc]
      exact wdig_region output w nonces k _ (OuterWitnessWindows.chain i).2.2.2.2

theorem path (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat) (k : Fin 9) :
    OuterReadout.Path (OuterExpand.witEncOuter output w nonces) k (rawChildFromOutput output k)
      (W9Drv.SharedCanonical.coordinatePath w.signature.forest k) (nDig (w.ftsNonces.getD k.val 0)) (pad16 k.val (w.ftsNonces16.getD k.val 0)) := by
  have hF:=pathReadout_witEncF16 output w k
  have hj:=SharedV3.physical_lt k.val (rawChildFromOutput output k).val (Fin.isLt _)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro l hl
    have h:=hF.headerPads l hl
    have hl6 : l<6 := by unfold SharedV3.lastLevel at hl;split at hl <;> omega
    unfold SharedV3.nodeHPad SharedV3.nodeTw at h ⊢
    split_ifs at h ⊢ with h4
    · rw [Nat.add_assoc,wdig_region output w nonces k _ ((OuterWitnessWindows.path ⟨_,hj⟩ ⟨l,hl6⟩).2.2 h4),←Nat.add_assoc]
      exact h
    · exact h
  · intro l hl hl5 hn4 hn3 hn2
    have h:=hF.nodePads l hl hn4 hn3 hn2
    have hl6 : l<6 := by omega
    unfold SharedV3.nodePad at h ⊢
    rw [Nat.add_assoc,wdig_region output w nonces k _ ((OuterWitnessWindows.path ⟨_,hj⟩ ⟨l,hl6⟩).2.1 hl5),←Nat.add_assoc]
    exact h
  · have h:=hF.nodePad3
    unfold SharedV3.nodePad at h ⊢
    rw [Nat.add_assoc,wdig_region output w nonces k _ ((OuterWitnessWindows.path ⟨_,hj⟩ ⟨3,by decide⟩).2.1 (by decide)),←Nat.add_assoc]
    exact h
  · have h:=hF.nodePad2
    unfold SharedV3.nodePad at h ⊢
    rw [Nat.add_assoc,wdig_region output w nonces k _ ((OuterWitnessWindows.path ⟨_,hj⟩ ⟨2,by decide⟩).2.1 (by decide)),←Nat.add_assoc]
    exact h
  · intro l hl
    have h:=hF.siblings l hl
    have hl6 : l<6 := by unfold SharedV3.lastLevel at hl;split at hl <;> omega
    unfold SharedV3.sibling at h ⊢
    rw [wdig_region output w nonces k _ (OuterWitnessWindows.path ⟨_,hj⟩ ⟨l,hl6⟩).1]
    exact h
  · have h:=hF.topOther
    simp only [SharedV3.topOther,W9Machine.wdig,ClaudeWCT.W9.T3M.wdig] at h ⊢
    have hf:=OuterWitnessWindows.topOther k ⟨_,hj⟩
    rw [extract_free output w nonces _ 16 hf.1 (fun c hc=>hf.2 ⟨c,hc⟩)]
    exact h

theorem initialPair (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat) :
    SharedV3.initialPair (OuterExpand.witEncOuter output w nonces)=ftsStart := by
  have h : SharedV3.initialPair (OuterExpand.witEncOuter output w nonces)=SharedV3.initialPair (witEncF16 output w) := by
    unfold SharedV3.initialPair SharedV3.leafPad V3.leafPad
    have h1:=wdig_region output w nonces 0 672 OuterWitnessWindows.hand.2
    have h2:=wdig_region output w nonces 0 160 OuterWitnessWindows.hand.1
    simp only [Fin.val_zero] at h1 h2
    rw [h1,h2]
  exact h.trans ((initialPair_witEncF16 output w).trans ((initialPair_witEncF output w).trans
    ((initialPair_witEncG output w).trans (PairedReadout.initialPair_witEnc output w))))

#print axioms chain
#print axioms path
#print axioms initialPair
end OuterWitnessReadout
