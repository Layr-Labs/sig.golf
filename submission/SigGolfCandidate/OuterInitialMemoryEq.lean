import SigGolfCandidate.OuterCompactInitial
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInitialMemoryEq
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.PrePass
open OuterSignatureCodec

theorem memory (im : Image) (m : Message) (pk : PublicKey) (sig : NewSig) (t : MachineState)
    (ht : SigMemC t.getMem (OuterSignatureCodec.expand sig))
    (hf : ∀ a,a∉(OuterCodecFrame.carrierWords++[33856])→t.getMem a=(w9init im m pk sig).getMem a) :
    t.getMem=(w9init im m pk (OuterSignatureCodec.expand sig)).getMem := by
  funext a
  let A:=a.toNat
  have hA : A<2^64 := a.isLt
  have ha : a=BitVec.ofNat 64 A := (BitVec.ofNat_toNat 64 a).symm
  rw [ha]
  by_cases hin : 28672≤A ∧ A<28672+5192 ∧ (A-28672)%8=0
  · let i:=(A-28672)/8
    have hi : i<649 := by dsimp only [i];omega
    have he : A=28672+8*i := by dsimp only [i];omega
    rw [he,ht.word i hi,w9_getMem im m pk (by decide : 5186≤5248) (OuterSignatureCodec.expand sig) _ (by omega),
      if_pos (by omega),show 28672+8*i-28672=8*i by omega]
    exact (SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_p (OuterSignatureCodec.expand sig) i (by omega)).symm
  · rw [hf]
    · rw [w9_getMem im m pk (by decide : 5183≤5248) sig A hA,
        w9_getMem im m pk (by decide : 5186≤5248) (OuterSignatureCodec.expand sig) A hA,
        if_neg hin,if_neg (by omega)]
    · simp only [OuterCodecFrame.carrierWords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      intro he
      rcases he with (he|he|he|he|he|he)|he
      all_goals
        have hh:=congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hA] at hh
        first
        | change A=29080 at hh
        | change A=29480 at hh
        | change A=29880 at hh
        | change A=30280 at hh
        | change A=30488 at hh
        | change A=33848 at hh
        | change A=33856 at hh
        apply hin
        rw [hh]
        exact ⟨by decide,by decide,by decide⟩
#print axioms memory
end OuterInitialMemoryEq
