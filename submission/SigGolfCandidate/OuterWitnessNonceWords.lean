import SigGolfCandidate.OuterWitnessFreePadded
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterWitnessNonceWords
open RiscvZkvm.Rv64 SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
open OuterExpand OuterWitnessOverlay

theorem pos_bounds : ∀ k : Fin 5,outerNoncePos k.val+8≤21756 := by decide +kernel

theorem byte (ns : List Nat) (k : Fin 5) (j : Nat) (hj : j<8) (b : UInt8) :
    outerNonceByte ns (outerNoncePos k.val+j) b=(bytesLE 8 (BitVec.ofNat 64 (ns.getD k.val 0))).getD j 0 := by
  fin_cases k <;> interval_cases j <;> rfl

theorem window (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) (k : Fin 5) :
    ((list output w ns).drop (outerNoncePos k.val)).take 8=bytesLE 8 (BitVec.ofNat 64 (ns.getD k.val 0)) := by
  have hp:=pos_bounds k
  have hl : (witListF16 output w).length=21760 := by rw [ClaudeWCT.W9.T3M.PairedNonce16.witListF16_length,ClaudeWCT.W9.T3M.PairedNonce.witListG_length]
  apply List.ext_getElem
  · simp only [list,List.length_mapIdx,List.length_take,List.length_drop,hl,bytesLE_length]
    omega
  · intro i h1 h2
    have hi : i<8 := by simpa only [bytesLE_length] using h2
    simp only [list,List.getElem_take,List.getElem_drop,List.getElem_mapIdx]
    have H:=byte ns k i hi (witListF16 output w)[outerNoncePos k.val+i]
    simpa only [List.getD_eq_getElem _ _ h2] using H

theorem word (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) (k : Fin 5) :
    (witEncOuter output w ns).extractLsb' (8*outerNoncePos k.val) 64=BitVec.ofNat 64 (ns.getD k.val 0) := by
  unfold witEncOuter
  rw [ClaudeWCT.W9.T3M.PairedReadout.extract_readLE _ 21756 _ 8 (pos_bounds k)]
  change BitVec.ofNat 64 (readLE (((list output w ns).drop (outerNoncePos k.val)).take 8))=_
  rw [window,readLE_bytesLE]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

#print axioms window
#print axioms word
end OuterWitnessNonceWords
