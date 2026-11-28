import SigGolfCandidate.OuterSignInput
import SigGolfCandidate.OuterSignFallback
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignHeader
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant
open SphincsSecurity (bytesLE bytesLE_length)

theorem fields {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
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

/-- C31: a packed FTS node word has nonzero low 11 bits (`2048 - heap` for heaps `8..127`). -/
theorem packed_low (coord index heap : Nat) (hh : FtsNew heap) (hc : coord<9) :
    ftsNodeWordH coord index heap <<< 53≠0#64 := by
  intro he
  have hn:=congrArg BitVec.toNat he
  have hw:=(ftsNodeWordH coord index heap).isLt
  simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq_mul_pow,BitVec.toNat_ofNat] at hn
  rw [show 2^64=2048*2^53 from by decide,Nat.mul_mod_mul_right] at hn
  have hm:=ftsNodeWordH_marker hh coord index
  obtain ⟨hlo,hhi⟩:=hh
  have h0 : (ftsNodeWordH coord index heap).toNat%2048=0 := by
    rcases Nat.eq_zero_or_pos ((ftsNodeWordH coord index heap).toNat%2048) with h|h
    · exact h
    · exfalso; have : 0<(ftsNodeWordH coord index heap).toNat%2048*2^53 := Nat.mul_pos h (by positivity); omega
  omega

/-- C46: heaps `4..127` fail the classifier's label test (a packed node has high word 0; the heaps `4..7` labels are
neither `3` nor `0xf1b02`). -/
theorem fallback {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : coord<9) (hh : 4≤heap) (hh128 : heap<128) : OuterSignFallback.Bad A s := by
  have hf:=fields F
  unfold OuterSignFallback.Bad
  refine Or.inr (Or.inl ?_)
  rw [hf.2,wctNodeHeader_high hc]
  have hv : (if FtsNew heap then 0 else ftsHeapLabelC coord heap)≠3 ∧
      (if FtsNew heap then 0 else ftsHeapLabelC coord heap)≠989954 ∧
      (if FtsNew heap then 0 else ftsHeapLabelC coord heap)<2^64 := by
    by_cases hn : FtsNew heap
    · rw [if_pos hn];decide
    · rw [if_neg hn]
      have h8 : heap<8 := by unfold FtsNew at hn;omega
      rcases Nat.mod_two_eq_zero_or_one coord with hc2|hc2
      · rw [ftsHeapLabelC_even hc2 hh (by omega)]
        interval_cases heap <;> decide
      · rw [ftsHeapLabelC_odd hc2]
        interval_cases heap <;> decide
  obtain ⟨h3,h9,hlt⟩:=hv
  exact ⟨fun he=>h3 ((ofNat_inj hlt (by decide)).mp he),fun he=>h9 ((ofNat_inj hlt (by decide)).mp he)⟩
#print axioms fields
#print axioms packed_low
#print axioms fallback
end OuterSignHeader
