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

/-- C47: the input buffer's header words are the node header's halves. -/
theorem words {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s) :
    s.getMem (BitVec.ofNat 64 (A+16))=(wctNodeHeader coord index heap).extractLsb' 0 64 ∧
    s.getMem (BitVec.ofNat 64 (A+24))=(wctNodeHeader coord index heap).extractLsb' 64 64 := by
  have hp:=F.pre_words
  unfold OuterNodeRawModel.pre at hp
  rw [wordsOf_append _ _ (by simp [bytesLE_length]),wordsOf_bytesLE16,wordsOf_bytesLE16] at hp
  rw [show 4=2+2 from rfl,readWords_add,readWords_two,readWords_two] at hp
  simp only [List.cons_append,List.nil_append] at hp
  have hwords:=List.cons.inj (List.cons.inj (List.cons.inj hp).2).2
  have hlast:=List.cons.inj hwords.2
  exact ⟨by simpa using hwords.1,by simpa only [show A+8*2+8=A+24 by omega] using hlast.1⟩

theorem not_new {heap : Nat} (hh : heap=2 ∨ heap=3) : ¬ FtsNew heap := by
  unfold FtsNew;rcases hh with rfl|rfl <;> omega

/-- C46: the low word is the node word, the high word the coordinate's heap label `ftsHeapLabelC coord heap`. C47:
off coordinate 8's swapped heaps. -/
theorem input_header {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : coord<9) (hh : heap=2 ∨ heap=3) (hs : ¬ ftsSwap8 coord heap) :
    s.getMem (BitVec.ofNat 64 (A+16))=ftsNodeWord coord index ∧
    s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 (ftsHeapLabelC coord heap) := by
  obtain ⟨h1,h2⟩:=words F
  rw [wctNodeHeader_low hc,if_neg (not_new hh),if_neg hs] at h1
  rw [wctNodeHeader_high hc,if_neg (not_new hh),if_neg hs] at h2
  exact ⟨h1.trans (ftsNodeWord_eq_low2 hc index).symm,h2⟩

/-- C47: odd coordinates' outer roots: high word `0xf1b02` (heap 2) or `K = 0xe7404003` (heap 3). -/
theorem input_odd {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : coord<9) (hh : heap=2 ∨ heap=3) (ho : coord%2=1) :
    s.getMem (BitVec.ofNat 64 (A+16))=ftsNodeWord coord index ∧
    s.getMem (BitVec.ofNat 64 (A+24))=(if heap=2 then 989954#64 else 3879747587#64) := by
  obtain ⟨h1,h2⟩:=input_header F hc hh (fun h=>by have:=h.1;omega)
  refine ⟨h1,h2.trans ?_⟩
  rw [ftsHeapLabelC_odd ho]
  rcases hh with rfl|rfl <;> rfl

/-- C47: coordinate 8's outer roots: heap 2 `(a5', 0)`, heap 3 swapped `(929 * 2^50, a5')`. -/
theorem input_eight {A D index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre 8 index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hh : heap=2 ∨ heap=3) :
    s.getMem (BitVec.ofNat 64 (A+16))=(if heap=2 then ftsNodeWord 8 index else 1045961013456797696#64) ∧
    s.getMem (BitVec.ofNat 64 (A+24))=(if heap=2 then 0#64 else ftsNodeWord 8 index) := by
  obtain ⟨h1,h2⟩:=words F
  rw [wctNodeHeader_low (by decide),if_neg (not_new hh)] at h1
  rw [wctNodeHeader_high (by decide),if_neg (not_new hh)] at h2
  rcases hh with rfl|rfl
  · rw [if_neg (by decide)] at h1 h2
    exact ⟨h1.trans (ftsNodeWord_eq_low2 (by decide) index).symm,h2⟩
  · rw [if_pos (by decide)] at h1 h2
    exact ⟨h1,h2.trans (ftsNodeWord_eq_low2 (by decide) index).symm⟩

/-- C47: coordinate 8's outer-root high word is zero exactly on heap 2 (the `c` search's direction test). -/
theorem input_hi8 {A D index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre 8 index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hh : heap=2 ∨ heap=3) :
    s.getMem (BitVec.ofNat 64 (A+24))=0#64 ↔ heap=2 := by
  rw [(input_eight F hh).2]
  rcases hh with rfl|rfl
  · simp
  · simp only [show ¬ (3:Nat)=2 by decide,if_false,iff_false]
    intro he
    exact ftsNodeWord_ne_zero 8 index (by rw [he];rfl)

#print axioms input_header
#print axioms input_hi8
end OuterNodeInputHeader
