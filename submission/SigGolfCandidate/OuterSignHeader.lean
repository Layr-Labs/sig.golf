import SigGolfCandidate.OuterSignInput
import SigGolfCandidate.OuterSignFallback
import SigGolfCandidate.OuterSignFields
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

/-- C47: the packed low word `ftsNodeLowN` has nonzero low 11 bits. -/
theorem packed_lowN (coord index heap : Nat) (hh : FtsNew heap) (hc : coord<9) :
    BitVec.ofNat 64 (ftsNodeLowN index coord heap) <<< 53≠0#64 := by
  intro he
  have hn:=congrArg BitVec.toNat he
  simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq_mul_pow,BitVec.toNat_ofNat] at hn
  rw [show 2^64=2048*2^53 from by decide,Nat.mul_mod_mul_right] at hn
  obtain ⟨hlo,hhi⟩:=hh
  have h0 : ftsNodeLowN index coord heap%2^64%2048=0 := by
    rcases Nat.eq_zero_or_pos (ftsNodeLowN index coord heap%2^64%2048) with h|h
    · exact h
    · exfalso; have : 0<ftsNodeLowN index coord heap%2^64%2048*2^53 := Nat.mul_pos h (by positivity); omega
  unfold ftsNodeLowN ftsBiasN at h0
  omega

/-- C47: an FTS node word is never the high-word labels `0`, `0xf1b02`, `K` of the classifier's `b` test... except
through its low half: its low 16 bits are `0xF800 - 2048 p`. -/
theorem node_ne (coord index : Nat) (hc : coord<9) :
    ftsNodeWord coord index≠989954#64 ∧ ftsNodeWord coord index≠3879747587#64 := by
  have h:=OuterHeaderFields.low16 coord index hc
  have hp : ftsPair coord ≤ 3 := by unfold ftsPair; split_ifs <;> omega
  constructor
  · intro he;rw [he] at h;change 989954%65536=_ at h;omega
  · intro he;rw [he] at h;change 3879747587%65536=_ at h;omega

/-- C46: heaps `4..127` fail the classifier. C47: a packed node (high word 0) has nonzero low 11 bits; a two-word node
of heaps `4..7` has a nonzero high word that is neither `0xf1b02` nor `K`, and a low word other than `929 * 2^50`. -/
theorem fallback {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : coord<9) (hh : 4≤heap) (hh128 : heap<128) : OuterSignFallback.Bad A s := by
  have hf:=fields F
  unfold OuterSignFallback.Bad
  by_cases hn : FtsNew heap
  · right;left
    rw [hf.2,hf.1,wctNodeHeader_high hc,wctNodeHeader_low hc,if_pos hn,if_pos hn]
    exact ⟨rfl,packed_lowN coord index heap hn hc⟩
  · right;right
    have hlt : heap<8 := by unfold FtsNew at hn;omega
    rw [hf.2,hf.1,wctNodeHeader_high hc,wctNodeHeader_low hc,if_neg hn,if_neg hn]
    by_cases hs : ftsSwap8 coord heap
    · rw [if_pos hs,if_pos hs]
      obtain ⟨rfl,h3,h6⟩:=hs
      rw [← ftsNodeWord_eq_low2 (by decide) index]
      have hne:=node_ne 8 index (by decide)
      refine ⟨fun he=>ftsNodeWord_ne_zero 8 index (by rw [he];rfl),?_,Or.inl hne⟩
      interval_cases heap <;> decide
    · rw [if_neg hs,if_neg hs,← ftsNodeWord_eq_low2 hc index]
      have hv : ftsHeapLabelC coord heap≠0 ∧ ftsHeapLabelC coord heap≠989954 ∧
          ftsHeapLabelC coord heap≠3879747587 ∧ ftsHeapLabelC coord heap<2^64 := by
        rcases Nat.mod_two_eq_zero_or_one coord with hc2|hc2
        · by_cases hc8 : coord<8
          · rw [ftsHeapLabelC_evenLow hc2 hc8]
            interval_cases heap <;> decide
          · obtain rfl : coord=8 := by omega
            rw [ftsHeapLabelC_eight]
            interval_cases heap <;> decide
        · rw [ftsHeapLabelC_odd hc2]
          interval_cases heap <;> decide
      obtain ⟨h0,h9,hK,hlt'⟩:=hv
      exact ⟨fun he=>h0 ((ofNat_inj hlt' (by decide)).mp he),OuterSignFields.ne_T4 coord index hc,
        Or.inl ⟨fun he=>h9 ((ofNat_inj hlt' (by decide)).mp he),fun he=>hK ((ofNat_inj hlt' (by decide)).mp he)⟩⟩
#print axioms fields
#print axioms packed_low
#print axioms fallback
end OuterSignHeader
