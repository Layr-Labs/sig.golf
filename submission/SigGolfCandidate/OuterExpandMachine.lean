import SigGolfCandidate.OuterInitialInfrastructure
import SigGolfCandidate.OuterEntryReject
import SigGolfCandidate.OuterExpandSource
import SigGolfCandidate.OuterSearched
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterExpandMachine
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OuterSignatureCodec

def work : Nat := 341+OuterSuffix.work+40+2365+37+((11*2^17)*200+12)+OuterSearched.work

theorem expand (sk : BitVec 256) (message : SigGolfCandidate.T3.Message) (pk : PublicKey) (sig : NewSig) :
    TBSim OuterImages.expandImage sk (w9init OuterImages.expandImage message pk sig) work
      (OuterExpand.expandN message pk (SharedCodec.sigDecC (OuterSignatureCodec.expand sig))) OuterForestHalt.Post := by
  let b:=OuterSignatureCodec.expand sig
  have hlen : OuterImages.expandImage.data.length=29936 := Images.expandData_length
  have hw:=OuterCompactInitial.input_words OuterImages.expandImage message pk sig
  have hz:=OuterCompactInitial.tail_zero OuterImages.expandImage hlen message pk sig
  rw [OuterExpandSource.expandN_source message pk _ (SharedCodec.fill_sigDecC _)]
  by_cases bad:12288≤(SharedCodec.sigDecC b).policyHints.toNat
  · rw [if_pos bad]
    have hc : ¬SharedCodec.nOfB b<PrePass.nCanon := by
      have h1:=(SharedCodec.policyHints_sigDecC_ge_iff b).mp bad
      rw [SharedCodec.R_mul_360] at h1
      unfold PrePass.nCanon
      omega
    obtain ⟨u,su,up⟩:=OuterEntryReject.reject sig _ (PrePass.w9_pc _ _ _ _) hw hz hc
    exact (TBSim.steps su (OuterForestHalt.finish (sk:=sk) (r:=none) (Or.inl up))).mono
      (by unfold work;omega) (fun _ _ h=>h)
  · rw [if_neg bad]
    have hh:(SharedCodec.sigDecC b).policyHints.toNat<12288:=by omega
    have hc:SharedCodec.nOfB b<PrePass.nCanon:=by
      have h1:=(SharedCodec.policyHints_sigDecC_ge_iff b).not.mp bad
      rw [SharedCodec.R_mul_360] at h1
      unfold PrePass.nCanon
      omega
    obtain ⟨v,sv,vp,vm,vr,vz,vf⟩:=OuterEntry.unpack_entry sig _ (PrePass.w9_pc _ _ _ _) hw hz
    have initial:=OuterInitialInfrastructure.initialized message pk sig v vm vf
    have hdata:=OuterInitialInfrastructure.initialized_data message pk sig v vm vf
    have vmem:=OuterInitialMemoryEq.memory OuterImages.expandImage message pk sig v vm vf
    rw [OuterInitialInfrastructure.initial_eq] at vmem
    obtain ⟨u,ku,cu,su,hcu,up,uz,ur,uin,uh,uf⟩:=OuterDecode.dec_gen v b vp vm hc
    have hmsg : ∀ k,k<4→u.getMem (BitVec.ofNat 64 (0x65A0+8*k))=message.extractLsb' (64*k) 64 := by
      intro k hk
      exact (uf.get (by omega) (by omega)).trans ((congrFun vmem _).trans
        (SharedInit.msgWord Images.expandData_length SharedInit.installed_dataBase message pk b k hk))
    have v5 : v.getReg .x5=0 := (vr .x5 (by decide)).trans (PrePass.w9_getReg_zero _ _ _ _ .x5 (by decide))
    have u5 : u.getReg .x5=0 := (ur .x5 (by decide)).trans v5
    obtain ⟨t,st,ready⟩:=SharedFront.prepare OuterDigestCodes.front_tail OuterDigestCodes.front_zero OuterDigestCodes.front_jump
      v u message b up u5 uin uh hmsg (hdata.frame uf (by intro A h1 h2;unfold SharedInit.DB at h1 h2;omega)) uf
    have search:=SharedFront.search_prepared (sk:=sk) OuterDigestCodes.look ready
    have continuation:=TBSim.bind (W₂:=OuterSearched.work) search
      (fun r s hs=>OuterSearched.continue_search initial hh hs)
    exact (TBSim.steps (sv.trans (su.trans st)) continuation).mono
      (by unfold work;omega) (fun _ _ h=>h)
#print axioms expand
end OuterExpandMachine
