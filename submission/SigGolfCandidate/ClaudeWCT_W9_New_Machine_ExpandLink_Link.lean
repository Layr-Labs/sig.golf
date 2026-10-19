import SigGolfCandidate.ClaudeWCT_W9_New_Machine_ExpandLink_Link_A

set_option Elab.async false
set_option maxRecDepth 100000


namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit lval lpath CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame HalfAt ltable rlWit_range)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layer_not_low (index A : Nat) (ha : A<0x2c48) (hc : A≠0x820) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hD|hD|hD|hD <;> omega
  · have:=rlWit_range h;have:=SigGolfCandidate.T3M.Expand.BC.ltable_lo lay;omega
  · rcases h with h|h
    · have:=h.2.1;omega
    · simp only [Search.FLAG] at h;omega

theorem layer_not_high (index A : Nat) (ha : 0xff0000 ≤ A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hD|hD|hD|hD <;> omega
  · have:=rlWit_range h;have:=ltable lay;omega
  · rcases h with h|h
    · have:=h.2.2;omega
    · simp only [Search.FLAG] at h;omega

theorem layer_header (N : HashOutput) (w : WCT9.Witness) (s t : MachineState)
    (hout : LayerOut t w.signature (WCT9.digestIndex N) 3 (w.counters 3))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex N) 4))
    (hr : DigAt s 2048 w.signature.rho)
    (hc : s.getMem 2064=BitVec.ofNat 64 w.digestCounter.toNat)
    (hz : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0) :
    t.readWords (BitVec.ofNat 64 2048) 8=wordsOf (headerBytesV5 w) ∧
      t.getMem 2080=BitVec.ofNat 64 (w.counters 3).toNat := by
  have ctr : t.getMem 2080=BitVec.ofNat 64 (w.counters 3).toNat := by
    have hlo:=hout.1
    change (t.getMem 2080).extractLsb' 0 32=w.counters 3 at hlo
    have hhi:=hhalf 2080 1 (by simp) (by decide) (by intro lay hl h;rw [lk_zero] at h;omega)
    rw [hz 4 (by decide) (by decide)] at hhi
    have hh : (t.getMem 2080).extractLsb' 32 32=0:=hhi
    rw [dword_of_halves (t.getMem 2080),hlo,hh]
    simp
  have r0:= (hframe.get (by decide) (layer_not_low _ 2048 (by decide) (by decide))).trans hr.1
  have r1:= (hframe.get (by decide) (layer_not_low _ 2056 (by decide) (by decide))).trans hr.2
  have dc:= (hframe.get (by decide) (layer_not_low _ 2064 (by decide) (by decide))).trans hc
  have zero (i:Nat) (hi:3 ≤ i) (hi':i<8) (hne:i≠4) : t.getMem (BitVec.ofNat 64 (2048+8*i))=0 := by
    rw [hframe.get (by omega) (layer_not_low _ _ (by omega) (by omega))]
    exact hz i hi hi'
  have ctr' : t.getMem (BitVec.ofNat 64 (2048+32))=BitVec.ofNat 64 (w.counters 3).toNat:=ctr
  refine ⟨?_,ctr⟩
  rw [headerW_words,readWords_eight,r0,r1,dc,zero 3 (by decide) (by decide) (by decide),
    ctr',
    zero 5 (by decide) (by decide) (by decide),zero 6 (by decide) (by decide) (by decide),
    zero 7 (by decide) (by decide) (by decide)]

#print axioms layer_header
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT OutAt)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (ltable rlWit_range)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

def Keep (A : Nat) : Prop := A<256 ∨ A=0x20550 ∨ (0x7000 ≤ A ∧ A<0x7760) ∨ 0xff0000 ≤ A

structure Stable (output : HashOutput) (b : SharedCodec48.CBytes) (pk : Digest) (s : MachineState) : Prop where
  digest : OutAt s 96 output
  forest : SharedCompact.ForestAt s b
  plan : PlanAt s
  lplan : Compact2.LPlanAt s
  toptab : Compact2.TopTabAt s
  scatterPlan : SharedScatter.PlanAt s
  pk : DigAt s 0xA0 pk
  index : s.getMem (0x20550#64)=BitVec.ofNat 64 (WCT9.digestIndex output)
  threshold1 : ∀r,r<56 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (WCT9.CanonicalPolicy.threshold 1 r)
  threshold2 : ∀r,r<41 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (WCT9.CanonicalPolicy.threshold 2 r)
  zt : SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 s

theorem Stable.frame {output : HashOutput} {b : SharedCodec48.CBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (h : Stable output b pk s) (hf : Frame s t W)
    (hn : ∀A,Keep A → ¬W A) : Stable output b pk t := by
  have word (A:Nat) (ha:A<2^64) (hk:Keep A) : t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := hf.get ha (hn A hk)
  have byte (A:Nat) (ha:A<2^64) (hk:0xff0000 ≤ A) : t.getByte (BitVec.ofNat 64 A)=s.getByte (BitVec.ofNat 64 A) :=
    hf.getByte ha (hn _ (Or.inr (Or.inr (Or.inr (by omega)))))
  constructor
  · intro k hk;rw [word _ (by omega) (Or.inl (by omega))];exact h.digest k hk
  · intro k hk
    have d:=h.forest k hk
    exact ⟨(word _ (by omega) (Or.inr (Or.inr (Or.inl (by omega))))).trans d.1,
      (word _ (by omega) (Or.inr (Or.inr (Or.inl (by omega))))).trans d.2⟩
  · intro k hk;rw [word _ (by unfold PLAN;omega) (Or.inr (Or.inr (Or.inr (by unfold PLAN;omega))))];exact h.plan k hk
  · intro k hk;rw [word _ (by unfold Compact2.LPLAN;omega) (Or.inr (Or.inr (Or.inr (by unfold Compact2.LPLAN;omega))))];exact h.lplan k hk
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [word _ (by unfold Compact2.TOPA;omega) (by unfold Keep Compact2.TOPA;omega)];exact h.toptab.1 k hk
    · rw [word _ (by unfold Compact2.TOPB;omega) (by unfold Keep Compact2.TOPB;omega)];exact h.toptab.2 k hk
  · intro child j hj;rw [byte _ (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by omega)];exact h.scatterPlan child j hj
  · exact ⟨(word _ (by decide) (Or.inl (by decide))).trans h.pk.1,(word _ (by decide) (Or.inl (by decide))).trans h.pk.2⟩
  · exact (word _ (by decide) (Or.inr (Or.inl rfl))).trans h.index
  · intro r hr;rw [byte _ (by omega) (by omega)];exact h.threshold1 r hr
  · intro r hr;rw [byte _ (by omega) (by omega)];exact h.threshold2 r hr
  · exact h.zt.frame hf (fun r hr => hn _ (Or.inr (Or.inr (Or.inr (by
      rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl]; omega)))))

theorem layer_keep (index A : Nat) (hk : Keep A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rcases hk with hk|rfl|hk|hk
  · exact layer_not_low index A (by omega) (by omega)
  · rintro (h|h|⟨lay,_,h|h|h⟩)
    · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
    · rcases lD_cases lay with hD|hD|hD|hD <;> omega
    · have:=rlWit_range h;have:=ltable lay;omega
    · rcases h with h|h
      · have:=h.2.1;omega
      · simp only [Search.FLAG] at h;omega
  · rintro (h|h|⟨lay,_,h|h|h⟩)
    · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
    · rcases lD_cases lay with hD|hD|hD|hD <;> omega
    · have:=rlWit_range h;have:=ltable lay;omega
    · rcases h with h|h
      · have:=h.2.1;omega
      · simp only [Search.FLAG] at h;omega
  · exact layer_not_high index A hk

def H2Writes (index A : Nat) : Prop := (NODE ≤ A ∧ A<NODE+64) ∨ (NOUT ≤ A ∧ A<NOUT+32) ∨ A=0x2c48+sOff index

theorem h2_keep (index A : Nat) (hk : Keep A) : ¬H2Writes index A := by
  have:=sOff_cases index
  unfold Keep at hk
  unfold H2Writes
  simp only [NODE,NOUT]
  omega
#print axioms Stable.frame
#print axioms layer_keep
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M height chainCount route)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit)
open SigGolfCandidate.T3M.Expand.BC (LayerOut)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def topProgram (output : HashOutput) (w : SharedForest.Witness) (folded root pk : Digest) :
    M (Option (HashOutput × SharedForest.Witness)) :=
  (if root=pk then pure (some 0) else WCT9.searchTop (WCT9.digestIndex output) folded (WCT9.topSib (SharedForest.mainSignature w.signature)) pk WCT9.searchFuel 1) >>= fun c=>
  pure (c.map fun c=>(output,{w with signature:=SharedForest.fillTopSignature w.signature c}))

/-- `some`: the expander reached the post-pass entry (pc 49400) with the phase-1 witness image and the top-node
nonces (`NoncesAt`, written by the img-v6 nonce routine) in place. -/
def Done (r : Option (HashOutput × SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none => s.pc=pcOf 354
  | some (output,w) => s.pc=pcOf 49400 ∧ s.getReg .x5=1 ∧ Phase1 output w s ∧
      SigGolfCandidate.T3M.Expand.NoncesAt s w.topNonces (route (WCT9.digestIndex output) 0).1

structure TopReady (output : HashOutput) (w : SharedForest.Witness) (b : SharedCodec48.CBytes)
    (folded root pk : Digest) (s : MachineState) : Prop where
  pc : s.pc=pcOf 42795
  x5 : s.getReg .x5=0
  root : DigAt s ENC root
  stable : Stable output b pk s
  indexLt : WCT9.digestIndex output<2^31
  top : ∀i,i<8 → s.getMem (BitVec.ofNat 64 (NODE+8*i))=
    (blkW (WCT9.digestIndex output) folded (WCT9.topSib (SharedForest.mainSignature w.signature))).getD i 0
  proj : WCT9.fillTop (SharedForest.mainSignature w.signature) 0=SharedForest.mainSignature w.signature
  header : s.readWords 2048 8=wordsOf (headerBytesV5 (Paired.mainWitness w))
  regions : ∀lay:Layer,s.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
    wordsOf (layerRegionV6 output (Paired.mainWitness w) lay)
  layer : LayerOut s (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) 0 (w.counters 0)
  zero : ∀A,0x2c48 ≤ A → A<0x2c48+64*66 →
    ¬RlWit 0 (route (WCT9.digestIndex output) 0).1 (lWC 0) (lWM 0) A → s.getMem (BitVec.ofNat 64 A)=0
  ctr3 : s.getMem 2080=(w.counters 3).setWidth 64
  forest : w.signature.forest=(SharedCodec48.sigDecC b).forest
  flag : s.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if w.topHigh then 128 else 0)
  nonces : SigGolfCandidate.T3M.Expand.NoncesAt s w.topNonces (route (WCT9.digestIndex output) 0).1

theorem top_good {im : Image} {sk : BitVec 256} (hsearch : SrchCoreAt im)
    (hcompact : CompactCodeAt im) (hz : SharedZero.ClearCode im)
    (hc : ∀k:Fin 9,SharedScatter.CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) SharedScatter.afterCode)
    (hf : CodeAt im (pcOf 47005) SharedScatter.finishCode)
    (he : CodeAt im (pcOf 43071) SharedScatter.endCode)
    (hj : CodeAt im (pcOf 43761) [0x24c0306f])
    (hentry : CodeAt im (pcOf 351) [0x4d52706f])
    {output : HashOutput} {w : SharedForest.Witness} {b : SharedCodec48.CBytes} {folded root pk : Digest} {s : MachineState}
    (h : TopReady output w b folded root pk s) :
    TBSim im sk s 15800000 (topProgram output w folded root pk) Done := by
  have hsib : WCT9.setTop (WCT9.topSib (SharedForest.mainSignature w.signature)) 0=
      WCT9.topSib (SharedForest.mainSignature w.signature) := by
    rw [←WCT9.topSib_fillTop,h.proj]
  have call:=search_entry_core (sk:=sk) hsearch (WCT9.digestIndex output) h.indexLt folded
    (WCT9.topSib (SharedForest.mainSignature w.signature)) root pk hsib s h.pc h.x5 h.root
    h.stable.pk.1 h.stable.pk.2 h.stable.index h.top
  unfold topProgram
  refine (TBSim.bind (W₂:=71150) call (fun result t ht=>?_)).mono (W':=15800000) (by norm_num) (fun _ _ h=>h)
  cases result with
  | none => exact (TBSim.pure (Q:=Done) (a:=none) ht).mono (by omega) (fun _ _ h=>h)
  | some c =>
    obtain ⟨tp,tzero,tnonzero⟩:=ht
    have frame : Frame s t (H2Writes (WCT9.digestIndex output)) := by
      by_cases hz:c=0
      · exact (tzero hz).mono (by simp)
      · exact (tnonzero hz).2.2
    have stable:=h.stable.frame frame (h2_keep (WCT9.digestIndex output))
    let w' : SharedForest.Witness:={w with signature:=SharedForest.fillTopSignature w.signature c}
    have regs : ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
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
    obtain ⟨v,tv,vp,v5,vph,vn⟩:=finish_steps hcompact hz hc ha hf he hj output w' b
      (t.setPC (pcOf 41108)) rfl stable.digest stable.plan stable.lplan stable.toptab fields ctr stable.forest
      h.forest stable.scatterPlan flag
    have tn := NoncesAt.frame h.nonces frame (by
      intro A h1 h2 hw; unfold H2Writes at hw; simp only [NODE,NOUT] at hw
      have:=sOff_cases (WCT9.digestIndex output);omega)
    have vnon : SigGolfCandidate.T3M.Expand.NoncesAt v w'.topNonces (route (WCT9.digestIndex output) 0).1 :=
      ⟨tn.1, fun k hk => (vn _ (by omega) (by omega)).trans (tn.2.1 k hk), (vn _ (by norm_num) (by norm_num)).trans tn.2.2⟩
    exact TBSim.steps (jump.trans tv) (TBSim.pure ⟨vp,v5,vph,vnon⟩)
#print axioms top_good
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (HashOutput)

def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage,Images.expandImage,Images.verifyImage⟩

def pairedExpandCost : Nat := 4210000000 + ClaudeWCT.W9.Machine.Expand.SharedCompactMain.suffixW

def PairedExpPost : Option (HashOutput × SigGolfCandidate.Research.SharedForest.Witness) → MachineState → Prop
  | none,t => (t.pc=pcOf 356 ∨ t.pc=pcOf 45231) ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧
      fetch Images.expandImage t=some (.base .ECALL)
  | some (output,w),t => t.pc=pcOf 45016 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t 4128 22012=ClaudeWCT.W9.T3M.Paired.witEncN output w ∧
      fetch Images.expandImage t=some (.base .ECALL)
end ClaudeWCT.W9.Machine.ExpandLink

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK TopBlkG)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame ltable rlWit_range)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem top_not_written (index A : Nat) (ha : 0x2c48 ≤ A) (hb : A<0x2c48+64*66)
    (hn : ¬RlWit 0 (route index 0).1 (lWC 0) (lWM 0) A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hd|hd|hd|hd <;> omega
  · by_cases he:lay=0
    · subst he;exact hn h
    · exact rlWit_region 0 lay _ A ha hb he h
  · rcases h with h|h
    · have:=h.2.1;omega
    · simp only [Search.FLAG] at h;omega

theorem ready_of_layers {output : HashOutput} {w : SharedForest.Witness} {b : SharedCodec48.CBytes}
    {pk folded root : Digest} {s t u : MachineState}
    (hi : WCT9.digestIndex output<2^31)
    (stable : Stable output b pk s)
    (hr : DigAt s 2048 w.signature.rho)
    (hdc : s.getMem 2064=BitVec.ofNat 64 w.digestCounter.toNat)
    (hzhead : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0)
    (hzregions : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hproj : WCT9.fillTop (SharedForest.mainSignature w.signature) 0=SharedForest.mainSignature w.signature)
    (hforest : w.signature.forest=(SharedCodec48.sigDecC b).forest)
    (hout : ∀lay:Layer,LayerOut t (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) lay (w.counters lay))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex output) 4))
    (hroot : DigAt t ENC root)
    (hblk : TopBlkG (WCT9.toT3Signature (SharedForest.mainSignature w.signature)) (WCT9.digestIndex output) 0 folded t)
    (hu : Frame t u (fun _=>False)) (up : u.pc=pcOf 42795) (u5 : u.getReg .x5=0)
    (hflag : t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if w.topHigh then 128 else 0))
    (hnon : SigGolfCandidate.T3M.Expand.NoncesAt t w.topNonces (route (WCT9.digestIndex output) 0).1) :
    TopReady output w b folded root pk u := by
  have mem (A:Nat) (ha:A<2^64) : u.getMem (BitVec.ofNat 64 A)=t.getMem (BitVec.ofNat 64 A):=hu.get ha (by simp)
  have rs:=layer_regions output (Paired.mainWitness w) s t hout hhalf hframe hzregions
  have hs:=layer_header output (Paired.mainWitness w) s t (hout 3) hhalf hframe hr hdc hzhead
  constructor
  · exact up
  · exact u5
  · exact ⟨(mem _ (by unfold ENC;omega)).trans hroot.1,(mem _ (by unfold ENC;omega)).trans hroot.2⟩
  · exact (stable.frame hframe (layer_keep _)).frame hu (by simp)
  · exact hi
  · intro i hi
    rw [mem _ (by unfold NODE;omega)]
    exact topBlk_get (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) folded t hblk i hi
  · exact hproj
  · change u.readWords (BitVec.ofNat 64 2048) 8=_
    rw [frame_readWords hu 2048 8 (by decide) (by simp)]
    exact hs.1
  · intro lay
    rw [frame_readWords hu _ _ (by have:=region_bounds lay;omega) (by simp)]
    exact rs lay
  · rcases hout 0 with ⟨ctr,values,paths⟩
    refine ⟨?_,?_,?_⟩
    · unfold SigGolfCandidate.T3M.Expand.BC.HalfAt at ctr ⊢
      rw [mem _ (by rw [show lD (0:Layer)=0x3ce8 by rfl];omega)]
      exact ctr
    · intro i hi
      exact ⟨(mem _ (by have:=ltable (0:Layer);omega)).trans (values i hi).1,
        (mem _ (by have:=ltable (0:Layer);omega)).trans (values i hi).2⟩
    · intro j hj
      have hh:SigGolfCandidate.T3M.Expand.sideOff (route (WCT9.digestIndex output) 0).1 j ≤ 48 := by
        unfold SigGolfCandidate.T3M.Expand.sideOff;split <;> omega
      exact ⟨(mem _ (by have:=ltable (0:Layer);omega)).trans (paths j hj).1,
        (mem _ (by have:=ltable (0:Layer);omega)).trans (paths j hj).2⟩
  · intro A ha hb hn
    rw [mem _ (by omega),hframe.get (by omega) (top_not_written _ A ha hb hn)]
    exact hzregions A ha (by omega)
  · change u.getMem (BitVec.ofNat 64 2080)=_
    rw [mem _ (by decide)]
    change t.getMem 2080=_
    exact hs.2.trans (BitVec.ofNat_toNat 64 (w.counters 3))
  · exact hforest
  · rw [mem _ (by decide)]; exact hflag
  · exact NoncesAt.frame hnon hu (by simp)
#print axioms ready_of_layers
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Expand (w9init)
open ClaudeWCT.W9.T3M.Final.Paired (ExpandRefines ExpandTerminates)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- img-v6: the expander reads the 5,239-byte signature (`SharedCodec.sigDecC`, 19-bit top field). -/
abbrev PairedExpandSimulation : Prop := ∀(sk : SecretKey)(message : Message)(pk : PublicKey)(b : Bytes 5239),
  TBSim Images.expandImage sk (w9init Images.expandImage message pk b) pairedExpandCost
    (ClaudeWCT.W9.T3M.Paired.expandN message pk (ClaudeWCT.W9.T3M.SharedCodec.sigDecC b)) PairedExpPost

theorem ppCycles_le : ClaudeWCT.W9.Machine.Expand.PostPass.ppCycles ≤ 1000000 := by
  unfold ClaudeWCT.W9.Machine.Expand.PostPass.ppCycles
  first
  | decide
  | (simp only [ClaudeWCT.W9.Machine.Expand.PostPass.RDA.res, ClaudeWCT.W9.Machine.Expand.PostPass.RDB.res,
      ClaudeWCT.W9.Machine.Expand.PostPass.RJ.res]; omega)
  | (norm_num [ClaudeWCT.W9.Machine.Expand.PostPass.RDA.res, ClaudeWCT.W9.Machine.Expand.PostPass.RDB.res,
      ClaudeWCT.W9.Machine.Expand.PostPass.RJ.res])
theorem pairedExpandCost_lt : pairedExpandCost+1<CYCLE_LIMIT := by
  have := ppCycles_le
  unfold pairedExpandCost ClaudeWCT.W9.Machine.Expand.SharedCompactMain.suffixW CYCLE_LIMIT
  omega

theorem paired_expand_initial (message : Message) (pk : PublicKey) (b : Bytes 5239) :
    initialState SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)=
      some (w9init Images.expandImage message pk b) := by
  unfold initialState
  rw [if_pos SigGolfCandidate.T3M.Paired.submission_expand_valid]
  simp only [inputBuffers,List.foldl_cons,List.foldl_nil]
  rfl

theorem paired_expPost_halt {o : Option (SigGolfCandidate.T3.HashOutput × SigGolfCandidate.Research.SharedForest.Witness)}
    {t : MachineState} (h : PairedExpPost o t) :
    fetch Images.expandImage t=some (.base .ECALL) ∧ t.getReg .x5=1 := by
  cases o with
  | none=>exact ⟨h.2.2.2,h.2.1⟩
  | some x=>exact ⟨h.2.2.2.2,h.2.1⟩

theorem paired_expPost_readout {o : Option (SigGolfCandidate.T3.HashOutput × SigGolfCandidate.Research.SharedForest.Witness)}
    {t : MachineState} (h : PairedExpPost o t) :
    o.map (fun x=>ClaudeWCT.W9.T3M.Paired.witEncN x.1 x.2)=
      if t.getReg .x10=0 then some (readOutput SigGolfCandidate.T3M.Paired.submission.sizes
        SigGolfCandidate.T3M.Paired.submission.layout .expand t) else none := by
  cases o with
  | none=>rw [if_neg (by rw [h.2.2.1];decide)];rfl
  | some x=>
    rw [if_pos h.2.2.1]
    exact congrArg some h.2.2.2.1.symm

theorem paired_expand_refines_of (H : PairedExpandSimulation) : ExpandRefines I0 := by
  intro message pk b
  apply Sim.run_eq SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)
    (paired_expand_initial message pk b) (H 0 message pk b) (Nat.lt_of_succ_lt pairedExpandCost_lt)
    (fun o=>o.map (fun x=>ClaudeWCT.W9.T3M.Paired.witEncN x.1 x.2))
  intro o t ht
  exact ⟨(paired_expPost_halt ht).1,(paired_expPost_halt ht).2,paired_expPost_readout ht⟩

theorem paired_expand_terminates_of (H : PairedExpandSimulation) : ExpandTerminates I0 := by
  intro hash message pk b
  obtain ⟨hf,hc⟩:=Sim.runWith SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)
    (paired_expand_initial message pk b) (H 0 message pk b) pairedExpandCost_lt
    (fun _ _ h=>paired_expPost_halt h) hash
  exact ⟨hf,lt_of_le_of_lt hc pairedExpandCost_lt⟩

theorem paired_expand_pending_of (H : PairedExpandSimulation) : ExpandRefines I0 ∧ ExpandTerminates I0 :=
  ⟨paired_expand_refines_of H,paired_expand_terminates_of H⟩
end ClaudeWCT.W9.Machine.ExpandLink

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M height chainCount route)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

structure LayersReady (output : HashOutput) (sig : SharedForest.Signature) (b : SharedCodec48.CBytes)
    (counter : BitVec 32) (forest : Digest × Digest) (pk : Digest) (s : MachineState) : Prop where
  inv : SigGolfCandidate.T3M.Expand.SharedLayers.LInv (SharedForest.mainSignature sig) sig.policyHints
    (WCT9.digestIndex output) 4 (.pair forest.1 forest.2) s
  stable : Stable output b pk s
  rho : DigAt s 2048 sig.rho
  dc : s.getMem 2064=BitVec.ofNat 64 counter.toNat
  headerZero : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0
  regionZero : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : WCT9.fillTop (SharedForest.mainSignature sig) 0=SharedForest.mainSignature sig
  forestEq : sig.forest=(SharedCodec48.sigDecC b).forest

def recoverProgram (output : HashOutput) (sig : SharedForest.Signature) (counter : BitVec 32)
    (forest : Digest × Digest) (pk : Digest) : M (Option (HashOutput × SharedForest.Witness)) :=
  SharedForest.recoverHintedLayers sig (WCT9.digestIndex output) (WCT9.topSib (SharedForest.mainSignature sig))
    4 (.pair forest.1 forest.2) >>= fun result=>
  match result with
  | none => pure none
  | some r => if SharedForest.policyHintsValid sig.policyHints r.digits r.lows then
      topProgram output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0,!(r.lows.getD 0 true),r.nonces⟩ r.foldedTop r.root pk
    else pure none

def SuffixDone (im : Image) (r : Option (HashOutput × SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none => s.pc=pcOf 354 ∨ (s.pc=pcOf 356 ∧ s.getReg .x5=1 ∧ s.getReg .x10=1 ∧ fetch im s=some (.base .ECALL))
  | some p => Done (some p) s

theorem layers_good {sk : BitVec 256} {output : HashOutput} {sig : SharedForest.Signature}
    {b : SharedCodec48.CBytes} {counter : BitVec 32} {forest : Digest × Digest} {pk : Digest} {s : MachineState}
    (h : LayersReady output sig b counter forest pk s) :
    TBSim Images.expandImage sk s 3782800060 (recoverProgram output sig counter forest pk) (SuffixDone Images.expandImage) := by
  have call:=SigGolfCandidate.T3M.Expand.SharedLayers.installed_recover_good (sk:=sk) (vin:=0) h.inv
  unfold recoverProgram
  refine TBSim.bind (W₂:=15800060) call (fun result t ht=>?_)
  cases result with
  | none => exact (TBSim.pure (Q:=SuffixDone Images.expandImage) (a:=none) (Or.inr ht)).mono (by omega) (fun _ _ h=>h)
  | some r =>
    dsimp only
    obtain ⟨tp,t5,troot,clen,dlen,fields,credits,half,regs,frame,_,top,hints,floors,llen,flagP,_,nonces⟩:=ht
    have stable:=h.stable.frame frame (layer_keep _)
    have jump:=SharedControl.validate_step t tp
    let u:=t.setPC (pcOf 46929)
    obtain ⟨v,n,c,hn,hc,uv,vp,vr,vf⟩:=SharedValidateV6.validate_source_steps SharedValidateV6.installed_code
      u rfl sig.policyHints r.digits r.lows h.inv.hintsLt dlen (fun lay=>floors lay lay.isLt) hints
      (fun lay=>credits lay lay.isLt) SharedValidate.threshold1_lt SharedValidate.threshold2_lt
      stable.threshold1 stable.threshold2
    have tf : Frame t v (fun _=>False):=vf
    by_cases valid:SharedForest.policyHintsValid sig.policyHints r.digits r.lows=true
    · rw [if_pos valid] at vp ⊢
      have v5:v.getReg .x5=0 := (vr.get (by decide)).trans t5
      have ready:TopReady output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0,!(r.lows.getD 0 true),r.nonces⟩ b
          r.foldedTop r.root pk v :=
        ready_of_layers h.inv.hidx h.stable h.rho h.dc h.headerZero h.regionZero h.proj h.forestEq
          (fun lay=>fields lay lay.isLt) half frame troot (top (by decide)) tf vp v5
          (by rw [flagP (by decide)]; cases r.lows.getD 0 true <;> rfl) (nonces (by decide))
      have result:=top_good (sk:=sk) SharedControl.installed_srchCore installed_compact SharedZero.installed_code
        SharedScatter.installed_coordinates SharedScatter.installed_after SharedScatter.installed_finish
        SharedScatter.installed_end
        SharedControl.scatter_code SharedControl.compact_code ready
      exact (TBSim.steps (jump.trans uv) result).mono (by omega) (by
        intro rv st hp
        cases rv with
        | none => exact Or.inl hp
        | some p => exact hp)
    · rw [if_neg valid] at vp ⊢
      exact (TBSim.steps (jump.trans uv) (TBSim.pure (Q:=SuffixDone Images.expandImage) (a:=none) (Or.inl vp))).mono
        (by omega) (fun _ _ h=>h)
#print axioms layers_good
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M)
open SigGolfCandidate.T3M.Search (ENC NODE TOP_DATA)
open SigGolfCandidate.T3M.Expand (CHAIN)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- Pairing stage 1: the signature with a zero top path, the witness of the initial FTS phase (the expander's
initial forest region and the cleared top path area agree with it; the forest only reads `.forest`). -/
def forestSig (sig : SharedForest.Signature) : SharedForest.Signature :=
  { sig with layers := fun lay => ⟨(sig.layers lay).values, fun j => if lay.val = 0 then 0 else (sig.layers lay).path j⟩ }
theorem forestSig_top (sig : SharedForest.Signature) : ∀ j, ((forestSig sig).layers 0).path j = 0 := fun _ => by simp [forestSig]

structure ForestMemory (output : HashOutput) (b : SharedCodec48.CBytes) (counter : BitVec 32) (pk : Digest) (s : MachineState) : Prop where
  stable : Stable output b pk s
  inflated : SharedCompact.InflatedAt s b
  hintsLt : (SharedCodec48.sigDecC b).policyHints.toNat<7744
  hints : s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec48.sigDecC b).policyHints.toNat
  dc : s.getMem 0x66008=BitVec.ofNat 64 counter.toNat
  c32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x
  zero : SigGolfCandidate.T3M.Expand.BC.LZero s
  table : Search.TableOK s
  cf : Search.CfTableOK 0 s
  reward : Search.Reward.RewardTablesOK s
  regionZero : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : WCT9.fillTop (SharedForest.mainSignature (SharedCodec48.sigDecC b)) 0=SharedForest.mainSignature (SharedCodec48.sigDecC b)

theorem ForestMemory.frame {output : HashOutput} {b : SharedCodec48.CBytes} {counter : BitVec 32} {pk : Digest}
    {s t : MachineState} (h : ForestMemory output b counter pk s)
    (hf : Frame s t (fun A=>1152 ≤ A ∧ A<11000)) : ForestMemory output b counter pk t := by
  have mem (A:Nat) (ha:A<2^64) (hn:¬(1152 ≤ A ∧ A<11000)) := hf.get ha hn
  constructor
  · exact h.stable.frame hf (by intro A hk;unfold Keep at hk;omega)
  · exact h.inflated.frame hf (by intro A ha hb;omega)
  · exact h.hintsLt
  · change t.getMem (BitVec.ofNat 64 0x66000)=_
    rw [mem _ (by decide) (by decide)]
    exact h.hints
  · change t.getMem (BitVec.ofNat 64 0x66008)=_
    rw [mem _ (by decide) (by decide)]
    exact h.dc
  · obtain ⟨x,hx,hm⟩:=h.c32
    exact ⟨x,hx,(mem _ (by unfold ENC;omega) (by unfold ENC;omega)).trans hm⟩
  · exact ⟨(mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c0,
      (mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c8,
      (mem _ (by unfold NODE;omega) (by unfold NODE;omega)).trans h.zero.n32,
      (mem _ (by unfold NODE;omega) (by unfold NODE;omega)).trans h.zero.n40,
      (mem _ (by unfold ENC;omega) (by unfold ENC;omega)).trans h.zero.e40⟩
  · exact h.table.frame hf (by intro i hi;unfold TOP_DATA;omega)
  · exact h.cf.frame hf (by intro i hi hj;unfold TOP_DATA;omega)
  · exact h.reward.frame hf (by intro i hi hj;unfold TOP_DATA;omega)
  · intro A ha hb;rw [mem _ (by omega) (by omega)];exact h.regionZero A ha hb
  · exact h.proj

theorem handoff_ready {output : HashOutput} {b : SharedCodec48.CBytes} {counter : BitVec 32} {pk : Digest}
    {pair : Digest × Digest} {s t : MachineState}
    (h : ForestMemory output b counter pk s) (hi:WCT9.digestIndex output<2^31)
    (hp:t.pc=pcOf 249) (h5:t.getReg .x5=0)
    (hL:DigAt s 2904 pair.1) (hR:DigAt s 2952 pair.2)
    (hroots:∀o,(o=0 ∨ o=8 ∨ o=48 ∨ o=56) → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (2904+o)))
    (hrho:∀i,i<2 → t.getMem (BitVec.ofNat 64 (2048+8*i))=s.getMem (BitVec.ofNat 64 (0x7000+8*i)))
    (hdc:t.getMem 2064=s.getMem 0x66008)
    (hzero:∀i,3 ≤ i → i<8 → t.getMem (BitVec.ofNat 64 (2048+8*i))=0)
    (hmove:∀i,i<428 → t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i)))
    (hf:Frame s t SharedHandoff.Writes) :
    LayersReady output (SharedCodec48.sigDecC b) b counter pair pk t := by
  constructor
  · exact SharedHandoff.layer_inv hp h5 hi h.stable.index h.inflated hL hR hroots hmove hf h.c32 h.zero h.table h.cf h.reward h.hintsLt h.hints h.stable.zt
  · exact h.stable.frame hf (by intro A hk;unfold Keep at hk;unfold SharedHandoff.Writes;omega)
  · have d:=h.inflated 0 (by decide)
    change DigAt s 0x7000 (SharedCodec48.sigDecC b).rho at d
    exact ⟨(hrho 0 (by decide)).trans d.1,(hrho 1 (by decide)).trans d.2⟩
  · exact hdc.trans h.dc
  · exact hzero
  · intro A ha hb
    rw [hf.get (by omega) (by unfold SharedHandoff.Writes;omega)]
    exact h.regionZero A ha hb
  · exact h.proj
  · rfl
#print axioms ForestMemory.frame
#print axioms handoff_ready
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

def forestProgram (output : HashOutput) (b : SharedCodec48.CBytes) (counter : BitVec 32) (pk : Digest) :
    M (Option (HashOutput × SharedForest.Witness)) :=
  SharedForest.recoverForest (WCT9.digestIndex output) (SharedForest.forestSelectionFromOutput output)
    (SharedForest.forestWordsFromOutput output) (SharedCodec48.sigDecC b).forest >>= fun pair=>
  recoverProgram output (SharedCodec48.sigDecC b) counter pair pk

theorem forest_suffix_good {sk : BitVec 256} {output : HashOutput} {b : SharedCodec48.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : SharedForestRun.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩)) s) :
    TBSim Images.expandImage sk s 3782804681 (forestProgram output b counter pk) (SuffixDone Images.expandImage) := by
  have call:=SharedForestRun.installed_forest_good sk output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩
    (WCT9.digestIndex output) hi s hI
  unfold forestProgram
  refine TBSim.bind (W₂:=3782802665) call (fun pair t ht=>?_)
  obtain ⟨tp,left,right,frame,fields,x8⟩:=ht
  have memory:=hm.frame frame
  obtain ⟨u,tu,up,u2,u5,roots,rho,dc,zeros,moved,regs,fr⟩:=SharedHandoff.steps SharedHandoff.installed_code t tp x8
  have ready:=handoff_ready memory hi up u5 left right roots rho dc zeros moved fr
  exact TBSim.steps tu (layers_good ready)
#print axioms forest_suffix_good
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

theorem expandN_source (message : Message) (pk : Digest) (b : SharedCodec48.CBytes)
    (hfill : SharedForest.fillTopSignature (SharedCodec48.sigDecC b) 0=SharedCodec48.sigDecC b) :
    Paired.expandN message pk (SharedCodec48.sigDecC b)=
      if (SharedCodec48.sigDecC b).policyHints.toNat ≥ 7744 then pure none else
        SharedForest.sharedDigestSearch (SharedCodec48.sigDecC b).rho message 0 (2^21) >>= fun result=>
          match result with
          | none => pure none
          | some (counter,output)=>forestProgram output b counter pk := by
  unfold Paired.expandN
  rw [hfill]
  by_cases bad:(SharedCodec48.sigDecC b).policyHints.toNat ≥ 7744
  · simp only [bad,ite_true]
  rw [if_neg bad,if_neg bad]
  apply congrArg (fun k=>SharedForest.sharedDigestSearch (SharedCodec48.sigDecC b).rho message 0 (2^21) >>= k)
  funext result
  cases result with
  | none => rfl
  | some pair =>
    rcases pair with ⟨counter,output⟩
    unfold forestProgram recoverProgram
    apply congrArg (fun k=>SharedForest.recoverForest (WCT9.digestIndex output)
      (SharedForest.forestSelectionFromOutput output) (SharedForest.forestWordsFromOutput output)
      (SharedCodec48.sigDecC b).forest >>= k)
    funext forest
    apply congrArg (fun k=>SharedForest.recoverHintedLayers (SharedCodec48.sigDecC b) (WCT9.digestIndex output)
      (WCT9.topSib (SharedForest.mainSignature (SharedCodec48.sigDecC b))) 4 (.pair forest.1 forest.2) >>= k)
    funext layers
    cases layers with
    | none => rfl
    | some layers =>
      dsimp only
      by_cases valid:SharedForest.policyHintsValid (SharedCodec48.sigDecC b).policyHints layers.digits layers.lows=true
      · simp only [valid,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
        unfold topProgram
        by_cases root:layers.root=pk
        · simp only [root,ite_true,pure_bind,Option.map_some,hfill]
        · simp only [root,ite_false]
          apply congrArg (fun k=>WCT9.searchTop (WCT9.digestIndex output) layers.foldedTop
            (WCT9.topSib (SharedForest.mainSignature (SharedCodec48.sigDecC b))) pk WCT9.searchFuel 1 >>= k)
          funext c
          cases c <;> rfl
      · have vf : SharedForest.policyHintsValid (SharedCodec48.sigDecC b).policyHints layers.digits layers.lows=false :=
          Bool.eq_false_iff.mpr valid
        simp only [vf,Bool.not_false,Bool.false_eq_true,ite_true,ite_false]
#print axioms expandN_source
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research

structure InitialMemory (b : SharedCodec48.CBytes) (pk : Digest) (s : MachineState) : Prop where
  plan : ClaudeWCT.W9.Machine.Expand.PlanAt s
  lplan : Compact2.LPlanAt s
  toptab : Compact2.TopTabAt s
  scatterPlan : SharedScatter.PlanAt s
  pk : DigAt s 0xA0 pk
  threshold1 : ∀r,r<56 → s.getByte (BitVec.ofNat 64 (16749456+r))=
    BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 r)
  threshold2 : ∀r,r<41 → s.getByte (BitVec.ofNat 64 (16749520+r))=
    BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 r)
  zt : SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 s
  c32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x
  zero : SigGolfCandidate.T3M.Expand.BC.LZero s
  table : Search.TableOK s
  cf : Search.CfTableOK 0 s
  reward : Search.Reward.RewardTablesOK s
  regionZero : ∀A,0x2c48≤A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : ClaudeWCT.WCT9.fillTop (SharedForest.mainSignature (SharedCodec48.sigDecC b)) 0=
    SharedForest.mainSignature (SharedCodec48.sigDecC b)

theorem initial_memory (m : Message) (pk : PublicKey) (b : SharedCodec48.CBytes)
    (hfill : SharedForest.fillTopSignature (SharedCodec48.sigDecC b) 0 = SharedCodec48.sigDecC b) :
    InitialMemory b pk (w9init Images.expandImage m pk b) := by
  have hp := SharedInit.initial_plans m pk b
  have ht := SharedInit.initial_tables m pk b
  have hf := SharedInit.initial_thresholds m pk b
  exact ⟨hp.1,hp.2,SharedInit.initial_toptab m pk b,(SharedInit.initial_data m pk b).plans,
    SharedInit.public_key_of_length Images.expandData_length m pk b,hf.1,hf.2,SharedInit.initial_zt m pk b,
    SharedInit.counter_of_length Images.expandData_length m pk b,
    SharedInit.layer_zero_of_length Images.expandData_length m pk b,
    ht.1,ht.2.1,ht.2.2,SharedInit.region_zero_of_length Images.expandData_length m pk b,
    SharedHandoff.main_projection b hfill⟩

#print axioms initial_memory
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem halt_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) :
    CodeAt im (pcOf 47012) [0x73] := by
  exact SharedCounterHooks.code_slice (off:=1956) hc (by decide +kernel) (by decide +kernel)

theorem installed_halt : CodeAt Images.expandImage (pcOf 47012) [0x73] :=
  halt_of_driver codeAt_expand_shared_driver

/-- img-v6: the pad writer's final `ecall` (45016). -/
theorem installed_halt_v6 : CodeAt Images.expandImage (pcOf 45016) [0x73] :=
  PadWriter.code_last (by decide) (by decide) (by decide +kernel)


theorem suffix_done {sk : BitVec 256} {r : Option (HashOutput × SharedForest.Witness)} {s : MachineState}
    (h : SuffixDone Images.expandImage r s) :
    TBSim Images.expandImage sk s suffixW (pure r) ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost := by
  cases r with
  | none =>
    rcases h with hp|⟨hp,h5,h10,hfetch⟩
    · obtain ⟨t,st,tp,t5,t10,tfetch⟩:=Search.cs0_spec SharedSearchCode.installed_searchKernel s hp
      exact (TBSim.steps st (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost) (a:=none)
        ⟨Or.inl tp,t5,t10,tfetch⟩)).mono (by unfold suffixW; omega) (fun _ _ h=>h)
    · exact (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost) (a:=none)
        ⟨Or.inl hp,h5,h10,hfetch⟩).mono (by unfold suffixW; omega) (fun _ _ h=>h)
  | some p =>
    rcases p with ⟨output,w⟩
    obtain ⟨hp,h5,ph,hn⟩:=h
    obtain ⟨t,st,tp,tr,tbuf,tm⟩:=PostEnc.pp_witEnc s hp output w ph.fts ph.old ph.choice ph.leaf
    have hscr (A:Nat) (h1:0x66700 ≤ A) (h2:A<0x66760) : t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
      rw [tm A (by omega)]; exact PostEnc.ppMem_scratch _ _ A h1 h2
    have hl : (SigGolfCandidate.T3.route (WCT9.digestIndex output) 0).1<4096 := by
      unfold SigGolfCandidate.T3.route; simp [SigGolfCandidate.T3.height]; omega
    have tleaf : (t.getMem (BitVec.ofNat 64 0x66758)).toNat % 4096=(SigGolfCandidate.T3.route (WCT9.digestIndex output) 0).1 % 4096 := by
      rw [hscr _ (by norm_num) (by norm_num),hn.2.2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show _ < 2^64 by omega)]
    have tnon : ∀ j, j < 11 → t.getMem (PadWriter.nonceAddr j)=BitVec.ofNat 64 (w.topNonces.getD j 0) := by
      intro j hj
      unfold PadWriter.nonceAddr
      rw [hscr _ (by omega) (by omega)]
      exact hn.2.1 j hj
    obtain ⟨u,su,up,u10,ur,ubuf,_⟩:=PadWit.pad_hook_witEncN t tp output w tleaf tnon tbuf
    have u5 : u.getReg .x5=1 := by rw [ur .x5 (by simp),tr .x5 (by simp)]; exact h5
    have fetch : fetch Images.expandImage u=some (.base .ECALL) := (installed_halt_v6.fetch u up).trans rfl
    have rb : readBuffer u 4128 22012=Paired.witEncN output w :=
      SharedWitnessOutput.readBuffer_words u 4128 22012 2752 _ (by decide) (by decide) (by decide) ubuf
    exact (TBSim.steps (st.trans su) (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost)
      (a:=some (output,w)) ⟨up,u5,u10,rb,fetch⟩)).mono (by unfold suffixW; omega) (fun _ _ h=>h)

theorem forest_suffix_halted {sk : BitVec 256} {output : HashOutput} {b : SharedCodec48.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : SharedForestRun.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩)) s) :
    TBSim Images.expandImage sk s (3782804681+suffixW) (forestProgram output b counter pk)
      ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost := by
  simpa only [bind_pure] using
    (TBSim.bind (W₂:=suffixW) (forest_suffix_good hi hm hI) (fun _ _ h=>suffix_done h))
#print axioms suffix_done
#print axioms forest_suffix_halted
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (ENC NODE TOP_DATA NBUF OutAt)
open SigGolfCandidate.T3M.Expand (CHAIN)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def ClearWrites (A:Nat) : Prop := A=0x66020 ∨ A=0x66008 ∨ A=0x66010 ∨ A=0x20550 ∨ (96≤A ∧ A<128) ∨ (1152≤A ∧ A<11064)

theorem memory_after_clear {s0 s t:MachineState} {output:HashOutput} {b:SharedCodec48.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec48.sigDecC b).policyHints.toNat<7744)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec48.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output)
    (hctr:t.getMem 0x66008=BitVec.ofNat 64 counter.toNat)
    (hindex:t.getMem 0x20550=s.getMem 0x20160 >>> 33)
    (hdigest:∀i,i<4 → t.getMem (BitVec.ofNat 64 (96+8*i))=s.getMem (BitVec.ofNat 64 (NBUF+8*i)))
    (hf:Frame s t ClearWrites) : ForestMemory output b counter pk t := by
  have word (A:Nat) (ha:A<2^64) (hS:¬SharedFront.SearchWrites A) (hC:¬ClearWrites A) :
      t.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A) :=
    (hf.get ha hC).trans (hs.get ha hS)
  have highWord (A:Nat) (ha:A<2^64) (hA:0xff0000≤A) :
      t.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A) := by
    apply word A ha
    · unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes
      simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF];omega
    · unfold ClearWrites;omega
  have highByte (A:Nat) (ha:A<2^64) (hA:0xff0000≤A) :
      t.getByte (BitVec.ofNat 64 A)=s0.getByte (BitVec.ofNat 64 A) := by
    apply (hs.trans hf).getByte ha
    rintro (h|h)
    · unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes at h
      simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF] at h;omega
    · unfold ClearWrites at h;omega
  have inflated:SharedCompact.InflatedAt t b:=hin.frame hf (by intro A ha hb;unfold ClearWrites;omega)
  constructor
  · constructor
    · intro i hi;exact (hdigest i hi).trans (hout i hi)
    · exact inflated.forest
    · intro i hi;rw[highWord _ (by unfold PLAN;omega) (by unfold PLAN;omega)];exact initial.plan i hi
    · intro i hi;rw[highWord _ (by unfold Compact2.LPLAN;omega) (by unfold Compact2.LPLAN;omega)];exact initial.lplan i hi
    · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [highWord _ (by unfold Compact2.TOPA;omega) (by unfold Compact2.TOPA;omega)];exact initial.toptab.1 k hk
      · rw [highWord _ (by unfold Compact2.TOPB;omega) (by unfold Compact2.TOPB;omega)];exact initial.toptab.2 k hk
    · intro child j hj
      rw[highByte _ (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by omega)]
      exact initial.scatterPlan child j hj
    · constructor
      · exact (word 160 (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.pk.1
      · exact (word 168 (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.pk.2
    · change t.getMem (0x20550:Word)=_
      rw[hindex]
      have ho:s.getMem (0x20160:Word)=output.extractLsb' 0 64:=hout 0 (by decide)
      rw[ho];exact Compact2.index_shr output
    · intro r hr;rw[highByte _ (by omega) (by omega)];exact initial.threshold1 r hr
    · intro r hr;rw[highByte _ (by omega) (by omega)];exact initial.threshold2 r hr
    · intro r hr;rw[highByte _ (by rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl];omega)
        (by rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl];omega)];exact initial.zt r hr
  · exact inflated
  · exact hh
  · exact (hf.get (A:=0x66000) (by decide) (by unfold ClearWrites;decide)).trans hhmem
  · exact hctr
  · obtain ⟨x,hx,hm⟩:=initial.c32
    exact ⟨x,hx,(word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans hm⟩
  · exact ⟨(word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c0,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c8,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.n32,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.n40,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.e40⟩
  · intro i hi;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.table i hi
  · intro i hi hj;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.cf i hi hj
  · intro i hi hj;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.reward i hi hj
  · intro A ha hb
    rw[hf.get (by omega) (by unfold ClearWrites;omega)]
    by_cases hz:A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8
    · exact hsetup A hz
    · rw[hs.get (by omega) (by
        unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes
        simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF];omega)]
      exact initial.regionZero A ha hb
  · exact initial.proj
#print axioms memory_after_clear
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem cleared_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec48.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec48.sigDecC b).policyHints.toNat<7744)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec48.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226) :
    ∃t,Steps Images.expandImage s 3740 3740 t ∧ t.pc=pcOf 45257 ∧
      (∀ (off:Nat),off+8≤8160 → off%8=0 → t.getMem (BitVec.ofNat 64 (2904+off))=0) ∧
      t.getMem 417824=0 ∧ t.getMem 0x66010=BitVec.ofNat 64 (WCT9.digestIndex output) ∧
      OutAt t NBUF output ∧ ForestMemory output b counter pk t := by
  have jump:=ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary.expand_steps ClaudeWCT.W9.Machine.Expand.SharedDigestCode.installed_success s hp
  let u:=s.setPC (pcOf 45232)
  obtain ⟨t,ut,tp,zeros,mode,ctr,index,idx,digest,regs,frame⟩:=
    SharedZero.accepted_clear SharedZero.installed_code u rfl h17
  have memory:ForestMemory output b counter pk t:=
    memory_after_clear initial hin hh hhmem hs hsetup hout (ctr.trans h19) idx digest frame
  refine ⟨t,jump.trans ut,tp,?_,mode,?_,?_,memory⟩
  · intro off hb ha;exact zeros (2904+off) (by omega) (by omega) (by omega)
  · rw[index]
    have ho:u.getMem (0x20160:Word)=output.extractLsb' 0 64:=hout 0 (by decide)
    rw[ho];exact Compact2.index_shr output
  · intro i hi
    exact (frame.get (by unfold NBUF;omega) (by simp only [ClearWrites,NBUF];omega)).trans (hout i hi)
#print axioms cleared_front
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem accepted_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec48.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec48.sigDecC b).policyHints.toNat<7744)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec48.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226)
    (hrank:∀k:Fin 9,SharedForest.rawForestRank output k.val<563) :
    ∃t,Steps Images.expandImage s 4996 5173 t ∧ ForestMemory output b counter pk t ∧
      SharedForestRun.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩)
        (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
        (fun k=>SharedForest.forestRank output k.val) t 0
        (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩)) t := by
  obtain ⟨u,su,up,uz,um,ui,uo,uf⟩:=cleared_front initial hin hh hhmem hs hsetup hout h19 h17 hp
  have fields:=SharedForestRun.fields_of_output u output (WCT9.digestIndex output) ui uo hrank
  obtain ⟨t,ut,ht,hframe⟩:=SharedScatter.scatter_forest_pre SharedScatter.installed_coordinates SharedScatter.installed_after
    output ⟨SharedCompactMain.forestSig (SharedCodec48.sigDecC b),counter,fun _=>0,false,[]⟩ b (WCT9.digestIndex output) u up uf.inflated rfl
    fields uf.stable.scatterPlan um uz rfl (forestSig_top _)
  exact ⟨t,su.trans ut,uf.frame hframe,ht⟩
#print axioms accepted_front
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.ExpandLink (PairedExpPost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem initial_pc (message : Message) (pk : PublicKey) (b : SharedCodec48.CBytes) :
    (w9init Images.expandImage message pk b).pc=pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg,MachineState.pc_writeBytesAsWords,MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords,MachineState.pc_writeBytesAsWords]
  rfl

theorem initial_x5 (message : Message) (pk : PublicKey) (b : SharedCodec48.CBytes) :
    (w9init Images.expandImage message pk b).getReg .x5=0 := by
  unfold w9init
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
  simp only [MachineState.getReg_writeBytesAsWords]
  rfl

/-- Cycle budget after the digest search (layers + top + compaction/scatter + img-v6 witness tail). -/
def searchedW : Nat := 3782809854 + suffixW

theorem searched_continue {sk : BitVec 256} {s0 s : MachineState} {pk : Digest} {b : SharedCodec48.CBytes}
    (initial : InitialMemory b pk s0) (hh:(SharedCodec48.sigDecC b).policyHints.toNat<7744)
    {r : Option (BitVec 32 × HashOutput)} (hs : SharedFront.Searched s0 b r s) :
    TBSim Images.expandImage sk s searchedW
      (match r with | none=>pure none | some (counter,output)=>forestProgram output b counter pk) PairedExpPost := by
  cases r with
  | none =>
    obtain ⟨t,st,tp,t5,t10,regs,frame⟩:=Sign.SharedDigestBoundary.failure_steps true
      SharedDigestCode.installed_failure s hs.result
    have pc:t.pc=pcOf 45231:=tp
    have hf:fetch Images.expandImage t=some (.base .ECALL):=
      (SharedDigestCode.installed_failure_ecall.fetch t pc).trans rfl
    exact (TBSim.steps st (TBSim.pure (Q:=PairedExpPost) (a:=none)
      ⟨Or.inr pc,t5,t10,hf⟩)).mono (by unfold searchedW; omega) (fun _ _ h=>h)
  | some result =>
    rcases result with ⟨counter,output⟩
    obtain ⟨hp,h19,hc,ha,hout⟩:=hs.result
    have hrank:=((SharedForest.accepted_conditions output ha).2.1)
    obtain ⟨t,st,memory,inv⟩:=accepted_front initial hs.inflated hh hs.hints hs.frame hs.setupZero hout h19
      hs.resultR17 hp hrank
    exact (TBSim.steps st (forest_suffix_halted (WCT9.digestIndex_lt output) memory inv)).mono
      (by unfold searchedW; omega) (fun _ _ h=>h)

end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem paired_expand_tbsim : PairedExpandSimulation := by
  intro sk message pk b
  -- img-v6: word 0 + the codec pre-pass rewrite the 5,239-byte signature into the 5,248-byte layout `b48`;
  -- the rest of the expander runs exactly as on the (virtual) initial state `w9init .. b48`.
  have hdec : SharedCodec48.sigDecC (SharedCodec48.sigBC (SharedCodec.sigDecC b))=SharedCodec.sigDecC b :=
    SharedCodec48.sigDecC_sigBC_v6 b
  have hfill : SharedForest.fillTopSignature (SharedCodec48.sigDecC (SharedCodec48.sigBC (SharedCodec.sigDecC b))) 0=
      SharedCodec48.sigDecC (SharedCodec48.sigBC (SharedCodec.sigDecC b)) := by
    rw [hdec]; exact SharedCodec48.fill_sigDecC b
  rw [← hdec, expandN_source message pk _ hfill]
  obtain ⟨u,c,su,hc,up,ureg,uf⟩:=PrePass.prepass_init message pk b
  have hsig : ∀ j, j<656 → u.getMem (BitVec.ofNat 64 (0x7000+8*j))=
      (SharedCodec48.sigBC (SharedCodec.sigDecC b)).extractLsb' (64*j) 64 := fun j hj =>
    (uf.get (by omega) (by simp)).trans
      (SharedInit.signatureWord Images.expandData_length SharedInit.installed_dataBase message pk _ j hj)
  have hmsg : ∀ k, k<4 → u.getMem (BitVec.ofNat 64 (0x6620+8*k))=message.extractLsb' (64*k) 64 := fun k hk =>
    (uf.get (by omega) (by simp)).trans
      (SharedInit.msgWord Images.expandData_length SharedInit.installed_dataBase message pk _ k hk)
  have u5 : u.getReg .x5=0 := (ureg .x5).trans (initial_x5 message pk _)
  by_cases bad:7744≤(SharedCodec48.sigDecC (SharedCodec48.sigBC (SharedCodec.sigDecC b))).policyHints.toNat
  · rw [if_pos bad]
    obtain ⟨t,st,tp,regs,frame⟩:=SharedCompact.invalid_front SharedCompact.installed_adapter_codeAt.tail
      SharedCompact.installed_adapter_codeAt.guard SharedFront.installed_invalid u up _ bad
      (BitVec.isLt (SharedCodec48.sigDecC _).policyHints) (SharedCompact.hints_of_signature u _ hsig)
    exact (TBSim.steps (su.trans st) (suffix_done (r:=none) (Or.inl tp))).mono
      (by unfold pairedExpandCost suffixW; omega) (fun _ _ h=>h)
  · rw [if_neg bad]
    have hh:(SharedCodec48.sigDecC (SharedCodec48.sigBC (SharedCodec.sigDecC b))).policyHints.toNat<7744:=by omega
    obtain ⟨t,st,ready⟩:=SharedFront.prepare SharedCompact.installed_adapter_codeAt SharedFront.installed_tail
      SharedFront.installed_zero SharedFront.installed_jump u message _ up u5 hsig hmsg
      ((SharedInit.initial_data message pk _).frame uf (by simp)) hh
    have search:=SharedFront.search_prepared (sk:=sk) SharedDigestCode.installed_look ready
    have continuation:=TBSim.bind (W₂:=searchedW) search
      (fun r s hs=>searched_continue (initial_memory message pk _ hfill) hh
        { hs with frame := (uf.trans hs.frame).mono (by intro A _ h; rcases h with h|h; exact h.elim; exact h) })
    exact (TBSim.steps (su.trans st) continuation).mono
      (by unfold pairedExpandCost SharedCompactMain.searchedW; omega) (fun _ _ h=>h)

theorem paired_expand_pending : Final.Paired.ExpandRefines I0 ∧ Final.Paired.ExpandTerminates I0 :=
  paired_expand_pending_of paired_expand_tbsim
#print axioms paired_expand_tbsim
#print axioms paired_expand_pending
end ClaudeWCT.W9.Machine.ExpandLink
