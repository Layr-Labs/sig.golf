import SigGolfCandidate.OuterNodeSourceSim
import SigGolfCandidate.OuterNodeRecordHeader
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeInputHeader
open RiscvZkvm.Rv64 SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open OuterNodeSearchInvariant
open SphincsSecurity (bytesLE bytesLE_length)

/-- C46: the high word is the coordinate's heap label `ftsHeapLabelC coord heap`. -/
theorem split_header (coord index heap : Nat) (hc : coord<9) (hh : heap=2 ∨ heap=3) :
    wctNodeHeader coord index heap=BitVec.ofNat 64 (ftsHeapLabelC coord heap) ++ ftsNodeWord coord index := by
  rw [wctNodeHeader_eq hc index (by unfold FtsNew;rcases hh with rfl|rfl <;> omega)]
  rfl

/-- C46: on the outer-root nodes (odd coordinates and coordinate 8) heaps 2, 3 carry `ftsHeapLabel` (`0xf1b02`,
`3`). -/
theorem label_outer {coord heap : Nat} (hco : coord%2=1 ∨ coord=8) (hh : heap=2 ∨ heap=3) :
    ftsHeapLabelC coord heap=ftsHeapLabel heap := by
  rcases hco with ho|rfl
  · rw [ftsHeapLabelC_odd ho];rcases hh with rfl|rfl <;> decide
  · exact ftsHeapLabelC_eight heap

theorem input_header {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : coord<9) (hh : heap=2 ∨ heap=3) :
    s.getMem (BitVec.ofNat 64 (A+16))=ftsNodeWord coord index ∧
    s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 (ftsHeapLabelC coord heap) := by
  have hp:=F.pre_words
  unfold OuterNodeRawModel.pre at hp
  rw [wordsOf_append _ _ (by simp [bytesLE_length]),wordsOf_bytesLE16,wordsOf_bytesLE16,
    split_header coord index heap hc hh] at hp
  rw [show 4=2+2 from rfl,readWords_add,readWords_two,readWords_two] at hp
  simp only [List.cons_append,List.nil_append,BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_append_eq_left] at hp
  have hwords:=List.cons.inj (List.cons.inj (List.cons.inj hp).2).2
  have hlast:=List.cons.inj hwords.2
  constructor
  · simpa using hwords.1
  · simpa only [show A+8*2+8=A+24 by omega] using hlast.1

/-- C46: the outer-root nodes' heap-label word. -/
theorem input_label {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : coord<9) (hh : heap=2 ∨ heap=3) (hco : coord%2=1 ∨ coord=8) :
    s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 (ftsHeapLabel heap) := by
  rw [(input_header F hc hh).2,label_outer hco hh]

#print axioms input_header
#print axioms input_label
end OuterNodeInputHeader
