import SigGolfCandidate.OuterFinishPreservation
import SigGolfCandidate.OuterNoncePostRecords
import SigGolfCandidate.OuterTopCodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterTopRecovery
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT OutAt)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame HalfAt ltable rlWit_range)
open ClaudeWCT ClaudeWCT.W9.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

def Done (ns : List Nat) (r : Option (HashOutput×SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none=>ClaudeWCT.W9.Machine.Expand.SharedCompactMain.Done none s
  | some p=>ClaudeWCT.W9.Machine.Expand.SharedCompactMain.Done (some p) s ∧ OuterForestCompactRecords.Inv 9 ns s

theorem top_good {im : Image} {sk : BitVec 256} (hsearch : SrchCoreAt im)
    (hcompact : CompactCodeAt im) (hz : SharedZero.ClearCode im)
    (hc : ∀k:Fin 9,SharedScatter.CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) SharedScatter.afterCode)
    (hf : CodeAt im (pcOf 47005) SharedScatter.finishCode)
    (he : CodeAt im (pcOf 43071) SharedScatter.endCode)
    (hj : CodeAt im (pcOf 43761) [0x24c0306f])
    (hentry : CodeAt im (pcOf 351) [0x4d52706f])
    {output : HashOutput} {w : SharedForest.Witness} {b : SharedCodec.CBytes} {folded root pk : Digest} {s : MachineState}
    (ns : List Nat) (houter : OuterForestCompactRecords.Inv 9 ns s)
    (h : TopReady output w b folded root pk s) :
    TBSim im sk s 31530000 (topProgram output w folded root pk) (Done ns) := by
  have hsib : WCT9.setTop (WCT9.topSib (SharedForest.mainSignature w.signature)) 0=
      WCT9.topSib (SharedForest.mainSignature w.signature) := by
    rw [←WCT9.topSib_fillTop,h.proj]
  have call:=search_entry_core (sk:=sk) hsearch (WCT9.digestIndex output) h.indexLt folded
    (WCT9.topSib (SharedForest.mainSignature w.signature)) root pk hsib s h.pc h.x5 h.root
    h.stable.pk.1 h.stable.pk.2 h.stable.index h.top
  unfold topProgram
  refine (TBSim.bind (W₂:=71150) call (fun result t ht=>?_)).mono (W':=31530000) (by norm_num) (fun _ _ h=>h)
  cases result with
  | none => exact (TBSim.pure (Q:=Done ns) (a:=none) ht).mono (by omega) (fun _ _ h=>h)
  | some c =>
    obtain ⟨tp,tzero,tnonzero⟩:=ht
    have frame : Frame s t (H2Writes (WCT9.digestIndex output)) := by
      by_cases hz:c=0
      · exact (tzero hz).mono (by simp)
      · exact (tnonzero hz).2.2
    have stable:=h.stable.frame frame (h2_keep (WCT9.digestIndex output))
    have touter : OuterForestCompactRecords.Inv 9 ns t := OuterNoncePostRecords.frame houter frame (by
      intro m _
      unfold H2Writes OuterSharedPost.record
      simp only [NODE,NOUT]
      have:=sOff_cases (WCT9.digestIndex output)
      omega)
    let w' : SharedForest.Witness:={w with signature:=SharedForest.fillTopSignature w.signature c}
    have regs : ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainSlotsV6 lay))=
        wordsOf (layerRegionV6 output (Paired.mainWitness w') lay) := by
      exact regions_fillTop output (Paired.mainWitness w) s t c h.proj h.regions h.layer h.zero
        tzero (fun hc=>(tnonzero hc).2.1) frame
    have head : t.readWords 2048 8=wordsOf (headerBytesV5 (Paired.mainWitness w')) := by
      change t.readWords (BitVec.ofNat 64 2048) 8=_
      rw [frame_readWords frame 2048 8 (by decide) (by
        intro i hi hw;unfold H2Writes at hw;simp only [NODE,NOUT] at hw
        have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.header
    have ctr : t.getMem 2080=(w'.counters 3).setWidth 64 := by
      change t.getMem (BitVec.ofNat 64 2080)=_
      rw [frame.get (A:=2080) (by decide) (by unfold H2Writes;simp only [NODE,NOUT];have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.ctr3
    have fields:=main_words_of_regions t output (Paired.mainWitness w') head regs
    obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0x4d52706f#32) 351=some 41108 by decide)
    have jump:=jal_x0_step hentry hd ho t tp
    have flag : t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if w'.topHigh then 128 else 0) := by
      rw [frame.get (by decide) (by unfold H2Writes;simp only [NODE,NOUT,Search.FLAG];have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.flag
    obtain ⟨v,tv,vp,v5,vph,vn⟩:=OuterFinishPreservation.Main.finish_steps hcompact hz hc ha hf he hj output w' b
      (t.setPC (pcOf 41108)) rfl stable.digest stable.plan stable.lplan stable.toptab fields ctr stable.forest
      h.forest stable.scatterPlan flag
    have tn := NoncesAt.frame h.nonces frame (by
      intro A h1 h2 hw; unfold H2Writes at hw; simp only [NODE,NOUT] at hw
      have:=sOff_cases (WCT9.digestIndex output);omega)
    have vnon : SigGolfCandidate.T3M.Expand.NoncesAt v w'.topNonces (route (WCT9.digestIndex output) 0).1 :=
      ⟨tn.1, fun k hk => (vn _ (Or.inl ⟨by omega, by omega⟩)).trans (tn.2.1 k hk),
        (vn _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans tn.2.2⟩
    have trec : PadWit.RecTable t.getMem output w := RecTable.frame h.recT (fun A h1 h2 => frame.get (by omega) (by
      intro hw; unfold H2Writes at hw; simp only [NODE,NOUT] at hw
      have:=sOff_cases (WCT9.digestIndex output);omega))
    have vrec : PadWit.RecTable v.getMem output w' := RecTable.frame trec (fun A h1 h2 => vn A (Or.inr (Or.inl ⟨h1, h2⟩)))
    have tfts : FtsRecsN output w.ftsNonces t := FtsRecsN.frame h.fts (fun A h1 h2 => frame.get (by omega) (by
      intro hw; unfold H2Writes at hw; simp only [NODE,NOUT] at hw
      have:=sOff_cases (WCT9.digestIndex output);omega))
    have vfts : FtsRecsN output w'.ftsNonces v := FtsRecsN.frame tfts (fun A h1 h2 => vn A (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
    have tfts16 : FtsRecs16 output w.ftsNonces16 t := FtsRecs16.frame h.fts16 (fun A h1 h2 => frame.get (by omega) (by
      intro hw; unfold H2Writes at hw; simp only [NODE,NOUT] at hw
      have:=sOff_cases (WCT9.digestIndex output);omega))
    have vfts16 : FtsRecs16 output w'.ftsNonces16 v := FtsRecs16.frame tfts16 (fun A h1 h2 => vn A (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))))
    have vouter : OuterForestCompactRecords.Inv 9 ns v := by
      refine ⟨houter.len,?_⟩
      intro m hm hfirst
      rw [vn _ (Or.inr (Or.inr (Or.inr (by
        unfold OuterSharedPost.record
        have:=m.isLt
        omega))))]
      exact touter.record m hm hfirst
    exact TBSim.steps (jump.trans tv) (TBSim.pure ⟨⟨vp,v5,vph,vnon,vrec,vfts,vfts16⟩,vouter⟩)

#print axioms top_good
end OuterTopRecovery
