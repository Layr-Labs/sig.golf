import SigGolfCandidate.OuterCodecInput
import SigGolfCandidate.OuterControlRun
import SigGolfCandidate.OuterDecode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterEntry
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Expand.PrePass
open OuterCodecMachine OuterSignatureCodec

theorem unpack_entry (sig : NewSig) (s : MachineState) (hp : s.pc=pcOf 0)
    (hw : ∀ i,i<648→s.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (hz : s.getMem 33856=0) :
    ∃ t,Steps OuterImages.expandImage s 40 40 t ∧ t.pc=pcOf 87500 ∧
      SigMemC t.getMem (OuterSignatureCodec.expand sig) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧
      (∀ r,r∈[Reg.x6,.x7,.x28,.x29]→t.getReg r=0) ∧
      (∀ a,a∉(OuterCodecFrame.carrierWords++[33856])→t.getMem a=s.getMem a) := by
  obtain ⟨u,su,up,ur,um⟩:=OuterControlRun.jump 0 88300 (by decide) (by decide) OuterImageControlTransfers.entry s hp
  let v:=unpackBlock.res.toState u
  have uv : Steps OuterImages.expandImage u 38 38 v := symRun_sound unpackBlock OuterImageHelpers.expand_unpack u up (unpack_obligs u)
  have vp : v.pc=pcOf 88338 := rfl
  obtain ⟨t,vt,tp,tr,tm⟩:=OuterControlRun.jump 88338 87500 (by decide) (by decide) OuterImageControlTransfers.unpack_return v vp
  refine ⟨t,su.trans (uv.trans vt),tp,⟨?_⟩,?_,?_,?_⟩
  · intro i hi
    rw [tm]
    exact OuterCodecInput.words sig u (by intro i hi;rw [um];exact hw i hi) (by rw [um];exact hz) i hi
  · intro r hr
    rw [tr,←ur r]
    cases r <;> simp at hr <;> rfl
  · intro r hr
    rw [tr]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> rfl
  · intro a ha
    rw [tm,OuterCodecFrame.unpack_frame u a ha,um]

theorem decode_entry (sig : NewSig) (s0 : MachineState) (hpc : s0.pc=pcOf 0)
    (hw : ∀ i,i<648→s0.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (hz : s0.getMem 33856=0) (hc : SharedCodec.nOfB (OuterSignatureCodec.expand sig)<nCanon) :
    ∃ u k c, Steps OuterImages.expandImage s0 k c u ∧ c ≤ 2405 ∧ u.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30, .x31], u.getReg r = 0) ∧
      RegsExcept s0 u [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC (OuterSignatureCodec.expand sig)) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC (OuterSignatureCodec.expand sig)).policyHints.toNat ∧
      Frame s0 u (fun A => A = 417792 ∨ (0x7000 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨v,sv,vp,vm,vr,vz,vf⟩:=unpack_entry sig s0 hpc hw hz
  obtain ⟨u,k,c,vu,hc',up,uz,ur,ui,uh,uf⟩:=OuterDecode.dec_gen v _ vp vm hc
  refine ⟨u,40+k,40+c,sv.trans vu,by omega,up,uz,?_,ui,uh,?_⟩
  · have hv : RegsExcept s0 v [.x6,.x7,.x18,.x19,.x20,.x28,.x29,.x30,.x31] := vr.mono (by decide)
    intro r hr
    exact (ur r hr).trans (hv r hr)
  · intro A hA hn
    rw [uf.get hA hn]
    apply vf
    simp only [OuterCodecFrame.carrierWords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro he
    rcases he with (he|he|he|he|he)|he
    all_goals
      have hh:=congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hA] at hh
      first
      | change A=29080 at hh
      | change A=29480 at hh
      | change A=29880 at hh
      | change A=30280 at hh
      | change A=30488 at hh
      | change A=33856 at hh
      subst A
      exact hn (Or.inr ⟨by decide,by decide⟩)

#print axioms decode_entry
#print axioms unpack_entry
end OuterEntry
