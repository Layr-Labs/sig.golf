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
/-- E3: the published pk word at 160 is `dlo pk`. -/
theorem w9_pk0 (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (hn : n ≤ 5248) (σ : Bytes n) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 160)=SigGolfCandidate.T3M.Verify.dlo pk := by
  rw [w9_getMem im m pk hn σ 160 (by decide),if_neg (by omega)]
  unfold preSig
  rw [getMem_writeBytesAsWords _ _ 0xA0 160 (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]) (by decide),
    if_pos (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]),show 160-0xA0=8*0 from rfl,
    SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e pk 0 (by decide)]
  try rfl

/-- E3: `w9init` at pk and at `decD pk` differ only at key 160 (168 holds `dhi`, which decD keeps). -/
theorem w9_pk_eq (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (hn : n ≤ 5248) (σ : Bytes n) (A : Nat)
    (hA : A<2^64) (h160 : A≠160) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A)=(w9init im m (SigGolfCandidate.T3M.Verify.decD pk) σ).getMem (BitVec.ofNat 64 A) := by
  rw [w9_getMem im m pk hn σ A hA,w9_getMem im m _ hn σ A hA]
  split_ifs with hs
  -- the signature branch is `X = X` (split_ifs may already have closed it); only the preSig goal survives
  all_goals try with_reducible rfl
  unfold preSig
  rw [getMem_writeBytesAsWords _ _ 0xA0 A (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]) hA]
  simp only [SigGolfCandidate.T3M.Expand.bytes_length_e]
  split_ifs with hk
  all_goals try with_reducible rfl
  -- remaining: the pk window, where A = 168 (A ≠ 160)
  have h168 : A-0xA0=8*1 := by omega
  rw [h168,SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e pk 1 (by decide),
    SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e (n := 16) (SigGolfCandidate.T3M.Verify.decD pk) 1 (by decide)]
  exact (SigGolfCandidate.T3M.Verify.dhi_decD pk).symm

/-- E3 adapter: the unpack-entry frame (key 160 excluded) plus the decode fact give the old-shape frame
against `w9init .. (decD pk) ..`, so `memory`/`initialized`/`initialized_data` apply at `decD pk` verbatim. -/
theorem decoded (im : Image) (m : Message) (pk : PublicKey) (sig : NewSig) (t : MachineState)
    (hf : ∀ a,a∉(OuterCodecFrame.carrierWords++[33856,160])→t.getMem a=(w9init im m pk sig).getMem a)
    (hp : t.getMem (BitVec.ofNat 64 160)=1-(w9init im m pk sig).getMem (BitVec.ofNat 64 160)) :
    ∀ a,a∉(OuterCodecFrame.carrierWords++[33856])→
      t.getMem a=(w9init im m (SigGolfCandidate.T3M.Verify.decD pk) sig).getMem a := by
  intro a ha
  obtain ⟨A,hA,rfl⟩ : ∃ A,A<2^64 ∧ a=BitVec.ofNat 64 A := ⟨a.toNat,a.isLt,(BitVec.ofNat_toNat 64 a).symm⟩
  by_cases h160 : A=160
  · subst A
    rw [hp,w9_pk0 im m pk (by decide : 5183≤5248) sig,w9_pk0 im m _ (by decide : 5183≤5248) sig,
      SigGolfCandidate.T3M.Verify.dlo_decD]
  · rw [hf]
    · exact w9_pk_eq im m pk (by decide : 5183≤5248) sig A hA h160
    · intro he
      rcases List.mem_append.mp he with he|he
      · exact ha (List.mem_append_left _ he)
      · rcases List.mem_cons.mp he with he|he
        · exact ha (List.mem_append_right _ (List.mem_singleton.mpr he))
        · have hh:=congrArg BitVec.toNat (List.mem_singleton.mp he)
          rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hA] at hh
          exact h160 hh
#print axioms memory
#print axioms w9_pk0
#print axioms w9_pk_eq
#print axioms decoded
end OuterInitialMemoryEq
