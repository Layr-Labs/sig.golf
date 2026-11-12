import SigGolfCandidate.OuterTopRecovery
import SigGolfCandidate.OuterInstalledValidate
import SigGolfCandidate.OuterLayerFrame
import SigGolfCandidate.OuterHintFloor
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLayersRecovery
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M height chainCount route)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit)
open SigGolfCandidate.T3M.Expand.BC (LayerOut)
open ClaudeWCT ClaudeWCT.W9.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

theorem validate_step (s : MachineState) (hp : s.pc=pcOf 342) :
    Steps OuterImages.expandImage s 1 1 (s.setPC (pcOf 46929)) := by
  have hc:=OuterImageTransfers.code (b:=342) (by decide +kernel) SharedControl.validate_code
  obtain ⟨imm,hd,hoff⟩:=jalTo_sound (show jalTo (0x7ec2d06f#32) 342=some 46929 by decide)
  exact jal_x0_step hc hd hoff s hp

def recoverProgram (output : HashOutput) (sig : SharedForest.Signature) (counter : BitVec 32)
    (forest : Digest × Digest) (ftsN ftsN16 : List Nat) (pk : Digest) : M (Option (HashOutput × SharedForest.Witness)) :=
  SharedForest.recoverHintedLayers sig (WCT9.digestIndex output) (WCT9.topSib (SharedForest.mainSignature sig))
    4 (.pair forest.1 forest.2) >>= fun result=>
  match result with
  | none => pure none
  | some r => if OuterSigning.policyHintsValid (WCT9.digestIndex output) sig.policyHints r.digits r.lows then
      topProgram output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0,!(r.lows.getD 0 true),r.nonces,
        fun lay=>r.lowerNonces.getD lay.val [],ftsN,ftsN16⟩ r.foldedTop r.root pk
    else pure none

def SuffixDone (ns : List Nat) (r : Option (HashOutput×SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none=>ClaudeWCT.W9.Machine.Expand.SharedCompactMain.SuffixDone OuterImages.expandImage none s
  | some p=>OuterTopRecovery.Done ns (some p) s

theorem layers_good {sk : BitVec 256} {output : HashOutput} {sig : SharedForest.Signature}
    {b : SharedCodec.CBytes} {counter : BitVec 32} {forest : Digest × Digest} {ftsN ftsN16 : List Nat} {pk : Digest}
    {s : MachineState} (ns : List Nat) (houter : OuterForestCompactRecords.Inv 9 ns s) (h : LayersReady output sig b counter forest ftsN ftsN16 pk s) :
    TBSim OuterImages.expandImage sk s 3821600084 (recoverProgram output sig counter forest ftsN ftsN16 pk)
      (SuffixDone ns) := by
  have call:=OuterLayerRecovery.run (sk:=sk) (vin:=0) h.inv
  unfold recoverProgram
  refine TBSim.bind (W₂:=31600084) call (fun result t ht=>?_)
  cases result with
  | none => exact (TBSim.pure (Q:=SuffixDone ns) (a:=none) (Or.inr ht)).mono (by omega) (fun _ _ h=>h)
  | some r =>
    dsimp only
    obtain ⟨tp,t5,troot,clen,dlen,fields,credits,half,regs,frame,_,top,hints,floors,llen,flagP,_,nonces,_,recP⟩:=ht
    have trec : PadWit.RecTable t.getMem output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0,!(r.lows.getD 0 true),
        r.nonces,fun lay=>r.lowerNonces.getD lay.val [],ftsN,ftsN16⟩ := by
      intro lay hl
      obtain ⟨_,hm,hh,h4⟩:=recP lay hl lay.isLt
      exact ⟨fun m hm'=>hm m hm',hh,h4⟩
    have touter : OuterForestCompactRecords.Inv 9 ns t := OuterNoncePostRecords.frame houter frame (by
      intro m _
      apply OuterLayerFrame.not_outer
      · unfold OuterSharedPost.record;omega
      · unfold OuterSharedPost.record;have:=m.isLt;omega)
    have stable:=h.stable.frame frame (layer_keep _)
    have jump:=validate_step t tp
    let u:=t.setPC (pcOf 46929)
    obtain ⟨v,n,c,hn,hc,uv,vp,vr,vf⟩:=OuterValidate.validate_source_steps OuterInstalledValidate.code
      u rfl (WCT9.digestIndex output) h.inv.hidx (by simpa [u] using stable.index)
      sig.policyHints r.digits r.lows h.inv.hintsLt dlen (fun lay=>by
        simpa only [OuterHintFloor.eq,SigGolfCandidate.T3M.Search.CanonicalExpandHooks.hintFloor_source] using floors lay lay.isLt) hints
      (fun lay=>credits lay lay.isLt) SharedValidate.threshold1_lt SharedValidate.threshold2_lt
      stable.threshold1 stable.threshold2
    have tf : Frame t v (fun _=>False):=vf
    by_cases valid:OuterSigning.policyHintsValid (WCT9.digestIndex output) sig.policyHints r.digits r.lows=true
    · rw [if_pos valid] at vp ⊢
      have v5:v.getReg .x5=0 := (vr.get (by decide)).trans t5
      have ready:TopReady output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0,!(r.lows.getD 0 true),r.nonces,
          fun lay=>r.lowerNonces.getD lay.val [],ftsN,ftsN16⟩ b
          r.foldedTop r.root pk v :=
        ready_of_layers h.inv.hidx h.stable h.rho h.dc h.headerZero h.regionZero h.proj h.forestEq
          (fun lay=>fields lay lay.isLt) half frame troot (top (by decide)) tf vp v5
          (by rw [flagP (by decide)]; cases r.lows.getD 0 true <;> rfl) (nonces (by decide)) trec
          (FtsRecsN.frame h.fts (fun A h1 h2 => frame.get (by omega) (layer_not_fts _ A h1 h2)))
          (FtsRecs16.frame h.fts16 (fun A h1 h2 => frame.get (by omega) (layer_not_fts16 _ A h1 h2)))
      have vouter : OuterForestCompactRecords.Inv 9 ns v := OuterNoncePostRecords.frame touter tf (by simp)
      have result:=OuterTopRecovery.top_good (sk:=sk) OuterTopCodes.search OuterTopCodes.compact OuterTopCodes.zero
        OuterTopCodes.coordinates OuterTopCodes.afterCode OuterTopCodes.finishCode OuterTopCodes.endCode
        OuterTopCodes.scatterJump OuterTopCodes.compactJump ns vouter ready
      exact (TBSim.steps (jump.trans uv) result).mono (by omega) (by
        intro rv st hp
        cases rv with
        | none => exact Or.inl hp
        | some p => exact hp)
    · rw [if_neg valid] at vp ⊢
      exact (TBSim.steps (jump.trans uv) (TBSim.pure (Q:=SuffixDone ns) (a:=none) (Or.inl vp))).mono
        (by omega) (fun _ _ h=>h)

#print axioms layers_good
end OuterLayersRecovery
