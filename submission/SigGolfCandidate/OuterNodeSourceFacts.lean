import SigGolfCandidate.OuterNodeInputHeader
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeSourceFacts
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterGroundCore OuterNodeSourceSim

theorem runC {im : Image} {sk : BitVec 256} {b A D index heap : Nat} {left right : Digest}
    {s : MachineState} (hheap : heap=2 ∨ heap=3)
    (F : Input A D (OuterNodeRawModel.pre 8 index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hc : CodeAt im (pcOf b) OuterNodeHelper.cCode) (hp : s.pc=pcOf b) :
    TBSim im sk s 77838 (nodeAt 8 index heap left right)
      (SourceOut 8 heap s A D (pcOf b-4#64)) := by
  exact OuterNodeSourceSim.runC hheap (OuterNodeInputHeader.input_header F (by decide) hheap).2 F hc hp

theorem record {coord index heap A D : Nat} {left right : Digest} {s t : MachineState}
    {ret : Word} {res : Nat × Digest} (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31)
    (hh : heap=2 ∨ heap=3)
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hout : SourceOut coord heap s A D ret res t) :
    t.getMem (BitVec.ofNat 64 (8323072+(coord-1)*4096))=BitVec.ofNat 64 res.1 := by
  obtain ⟨raw,hkeep,ho⟩:=hout
  have hw:=OuterNodeInputHeader.input_header F hc9 hh
  have hrec:=OuterNodeRecordHeader.record_address s coord index hc hc9 hi (by
    rw [F.x10,ofNat_add_ofNat];exact hw.1)
  have hn : raw.1=res.1 := congrArg Prod.fst hkeep
  have hr:=ho.record
  rw [hrec,hn] at hr
  exact hr

theorem low_words {A D n : Nat} {a : HashOutput} {t : MachineState} (h : Answer A D n a t) :
    DigAt t D (a.extractLsb' 0 128) := by
  constructor
  · rw [BitVec.extractLsb'_extractLsb'_of_le (by decide)]
    exact h.output 0 (by decide)
  · rw [BitVec.extractLsb'_extractLsb'_of_le (by decide)]
    exact h.output 1 (by decide)

theorem high_words {A D n : Nat} {a : HashOutput} {t : MachineState} (h : Answer A D n a t) :
    DigAt t (D+16) (a.extractLsb' 128 128) := by
  constructor
  · rw [h.output 2 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
    omega
  · rw [show D+16+8=D+8*3 by omega,h.output 3 (by decide),OuterNodeHashZero.high_word]


theorem digest {coord heap A D : Nat} {s t : MachineState} {ret : Word} {res : Nat × Digest}
    (hout : SourceOut coord heap s A D ret res t) :
    DigAt t (D+offset coord heap/8) res.2 := by
  obtain ⟨raw,hkeep,ho⟩:=hout
  have hv : value coord heap raw.2=res.2 := congrArg Prod.snd hkeep
  rw [←hv]
  by_cases hz : coord=8 ∧ heap=3
  · simp only [value,offset,if_pos hz,Nat.zero_div,Nat.add_zero]
    exact low_words ho.answer
  · simp only [value,offset,if_neg hz,show 128/8=16 from rfl]
    exact high_words ho.answer

#print axioms digest

#print axioms runC
#print axioms record
#print axioms low_words
#print axioms high_words
end OuterNodeSourceFacts
