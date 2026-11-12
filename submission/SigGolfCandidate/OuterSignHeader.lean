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

theorem packed_tag (coord index heap : Nat) (hh : FtsNew heap) :
    ((ftsNodeWordH coord index heap <<< (48:Nat)) >>> (48:Nat))≠63488#64 := by
  intro he
  rw [OuterSignFields.low16] at he
  have hn:=congrArg BitVec.toNat he
  have hw:=(ftsNodeWordH coord index heap).isLt
  have hm:=ftsNodeWordH_marker hh coord index
  have ht : (BitVec.ofNat 64 63488).toNat=63488 := rfl
  change (BitVec.ofNat 64 ((ftsNodeWordH coord index heap).toNat%65536)).toNat=(BitVec.ofNat 64 63488).toNat at hn
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),ht] at hn
  obtain ⟨hlo,hhi⟩:=hh
  omega

theorem fallback {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : coord<9) (hh : 4≤heap) (hh128 : heap<128) : OuterSignFallback.Bad A s := by
  have hf:=fields F
  unfold OuterSignFallback.Bad
  by_cases hp : 8≤heap
  · refine Or.inr (Or.inl ?_)
    rw [hf.1]
    have hs : wctNodeHeader coord index heap=0#64++ftsNodeWordH coord index heap := by
      unfold wctNodeHeader
      rw [nodeTweak_ftsN (by unfold nodeLayer;omega) (by unfold nodeLayer;omega) index ⟨hp,hh128⟩]
      have he : nodeLayer coord-4=coord := by unfold nodeLayer;omega
      rw [he]
    rw [hs,BitVec.extractLsb'_append_eq_right]
    exact packed_tag coord index heap ⟨hp,hh128⟩
  · refine Or.inr (Or.inr ?_)
    rw [hf.2]
    have hs : wctNodeHeader coord index heap=BitVec.ofNat 64 (ftsHeapLabel heap)++ftsNodeWord coord index := by
      unfold wctNodeHeader
      rw [nodeTweak_fts (by unfold nodeLayer;omega) (by unfold nodeLayer;omega) index (by unfold FtsNew;omega)]
      have he : nodeLayer coord-4=coord := by unfold nodeLayer;omega
      rw [he]
    rw [hs,BitVec.extractLsb'_append_eq_left,BitVec.toNat_ofNat]
    interval_cases heap <;> decide
#print axioms fields
#print axioms packed_tag
#print axioms fallback
end OuterSignHeader
