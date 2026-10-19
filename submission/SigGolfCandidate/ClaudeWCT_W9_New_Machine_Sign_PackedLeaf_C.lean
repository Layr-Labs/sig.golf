import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_PackedLeaf_B

set_option Elab.async false


namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest M)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (lower_n)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem chain_step_precise {im : Image} (hsub : Sign.SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Sign.Seed.sub61)
    (hc : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hnew : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) Sign.seedHookCode)
    (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
    (hlay : A.lay≠0) (hso : A.so=false) (hvS : A.valp+16*A.n≤0x50000)
    (hdS : A.digp+A.n≤0x50000) (hdestS : A.dest+16≤0x50000)
    (hvi : A.valp+16*A.n≤0x20550 ∨ 0x20558≤A.valp)
    {coefs : List Digest}
    {j : Nat} (hj : j<43) {prefixes : List (List Digest)} {u : MachineState}
    (hu0 : PSt s0 A coefs j prefixes u ∧ Frame s0 u (Writes A s0)) :
    TBSim im sk u chainC (prefixStep A coefs prefixes j) (fun ps x => PSt s0 A coefs (j+1) ps x ∧ Frame s0 x (Writes A s0)) := by
  obtain ⟨hu,huf⟩ := hu0
  have hcost : SharedSeed.lowerSeedC=lowerSeedC := rfl
  have plen := hu.len
  have hl := A.lay.isLt
  have hn : A.n = 43 := lower_n hlay
  have hlay' : A.lay.val < 256 := by have := A.lay.isLt; omega
  have hlay0 : A.lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨s, values, hs, hinv⟩ := hu.inv
  have g : ∀ r, r ∉ leafRegs → u.getReg r = s0.getReg r := fun r hr => by rw [hinv.regs.get hr, hs.regs]
  obtain ⟨v, c0, sv, hc0, vpc, vr, vf⟩ : ∃ v c0, Steps im u c0 c0 v ∧ c0 ≤ 5 ∧ v.pc = pcOf seedI ∧
      RegsExcept u v [] ∧ Frame u v (fun _ => False) := by
    by_cases hj0 : j = 0
    · exact ⟨u, 0, Steps.refl u, by norm_num, by rw [hu.pc, if_pos hj0], RegsExcept.refl _ _, Frame.refl _ _⟩
    · have hpc : u.pc = pcOf (1013 + 41) := by rw [hu.pc, if_neg hj0]
      obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.SharedLeaf.sub41_spec hsub u hpc j A.n (by omega) (by omega) hinv.x19
        (by rw [g _ (by simp [leafRegs]), hpre.x26])
      rw [if_pos (by omega)] at t1pc
      obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := hook_spec hhook t1 (by rw [t1pc])
      obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := SharedSeed.step_D1 hnew t2 t2pc (lay := A.lay.val) (j := j)
        (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [leafRegs]), hpre.x8]) hlay0 hlay'
        (by rw [t2r.get (by simp), t1r.get (by simp)]; exact hinv.x19) hj0 (by omega)
      exact ⟨t3, _, st1.trans (st2.trans st3), by norm_num, t3pc, ((t1r.trans t2r).trans t3r).mono (by simp),
        ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)⟩
  have hv19 : v.getReg .x19 = BitVec.ofNat 64 j := by rw [vr.get (by simp)]; exact hinv.x19
  have hv18 : v.getReg .x18 = BitVec.ofNat 64 A.leaf := by
    rw [vr.get (by simp), g _ (by simp [leafRegs]), hpre.x18]
  have hcv : SharedSeed.FamBuf v coefs := hu.coef.frame vf (fun _ _ _ h => h)
  obtain ⟨w, kw, cw, sw, hcw, wpc, w28, wseed, wr, wf⟩ :=
    SharedSeed.lower_seed hnew v vpc hv18 (by have := hpre.hleaf; omega) hv19 hj hcv
  rw [← PackedLeaf.lowerFamilySeed_eq hlay coefs A.leaf hj] at wseed
  have hs' : HybOf s0 (hyb s0 w) w := hyb_of s0 w
  have hinvw : LeafInv (hyb s0 w) A j (ends prefixes,values) w := LeafInv.rebase hinv hs hs' (vr.trans wr) (by
      intro r hr
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (vf.trans wf) (fun X h => by
      rcases h with h | h
      · exact h.elim
      · unfold SeedW BScr; simp only [COEF, CHAINW, PRIV, SEEDS] at *; omega)
    hpre.hvs hvS (by omega)
  have hpre' : LeafPreS sk (hyb s0 w) A := LeafPreS.transfer hpre hs'.regs hs'.base hdS
  have hcw' : DigAt w (SEEDS + 16) (Sign.Packed.memDig w (SEEDS + 16)) := Sign.Packed.memDig_digAt _ _
  have hcont := chain_cont_guarded hsub hcopy hc hpref sk hpre hlay hso hvS hdS hvi (by omega)
    w (WCT9.lowerFamilySeed coefs A.lay A.leaf j) _ (by rw [wpc]) hinvw hs' w28 wseed hcw'
  unfold prefixStep
  refine (TBSim.steps (sv.trans sw) (TBSim.bind (W₂:=0) hcont (fun vs x hx => TBSim.pure ?_))).mono
    (by unfold chainC; omega) (fun _ _ h => h)
  obtain ⟨vlen,xpc,base,vals,hsx,hinvx,-,xf,xsaved,xz⟩ := hx
  have hxcoef : SharedSeed.FamBuf x coefs := by
    have hslot := slot_lt A.lay (by omega : j<A.n)
    refine (hcv.frame wf ?_).frame xf ?_
    · intro X h1 h2 h; simp only [SharedSeed.FB, SharedSeed.FEND, COEF, CHAINW] at *; omega
    · intro X h1 h2 h
      simp only [SharedSeed.FB, SharedSeed.FEND, COEF, Sign.Seed.ChainWS, CHAIN, SharedPrefixes.buffer, LEAFPK] at *
      omega
  have hprecise : Frame s0 x (Writes A s0) := by
    apply ((huf.trans vf).trans (wf.trans xf)).mono
    intro X hX h
    rcases h with (h|h)|(h|h)
    · exact h
    · exact h.elim
    · left
      simp only [COEF,CHAINW] at h
      omega
    · rcases h with h|h|h
      · left; simp only [Sign.Seed.ChainWS,CHAIN] at h; omega
      · right
        refine ⟨h.1,?_,?_⟩ <;> simp only [SharedPrefixes.buffer] at * <;> omega
      · left
        have hs := slot_lt A.lay (by omega : j<A.n)
        simp only [LEAFPK] at hs
        omega
  refine ⟨?_,hprecise⟩
  refine ⟨by rw [if_neg (by omega)]; exact xpc,hxcoef,
    ⟨base,vals,hsx,by simpa only [ends,List.map_append,List.map_singleton] using hinvx⟩,
    by simp only [List.length_append,List.length_singleton,hu.len],?_,fun hj2 => xz (by omega)⟩
  intro hsel i hi k hk
  by_cases hij : i=j
  · subst i
    have hws : SharedPrefixes.selectionWord (w.getMem 0x20550) A.lay.val=w.getReg .x18 :=
      LeafInv.selected hpre hvi hinvw hs' hsel
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : prefixes.length≤j),
      hu.len,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] using xsaved hws k hk
  · have hij' : i<j := by omega
    have hi43 : i<43 := by omega
    have hb := SharedPrefixes.buffer_bounds (lay := A.lay.val) (by
      have hz : A.lay.val≠0 := fun h => hlay (Fin.ext h); omega)
      (by omega) hi43 (by omega : k<8)
    have saved := hu.saved hsel i hij' k hk
    have vSaved := saved.frame vf (by omega) (by simp) (by simp)
    have wSaved := vSaved.frame wf (by omega)
      (by simp only [COEF,CHAINW]; omega) (by simp only [COEF,CHAINW]; omega)
    have hslot := slot_lt A.lay (by omega : j<A.n)
    have xSaved := wSaved.frame xf (by omega)
      (by simp only [Sign.Seed.ChainWS,CHAIN,SharedPrefixes.buffer,LEAFPK] at *; omega)
      (by simp only [Sign.Seed.ChainWS,CHAIN,SharedPrefixes.buffer,LEAFPK] at *; omega)
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : i<prefixes.length)] using xSaved

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace ClaudeWCT.W9.Machine.Sign.SharedLeafMemory
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest M chainCount maxDigit)
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3M.Sign.Packed (lowLeafC)
open ClaudeWCT.W9.Machine.Sign.PackedLeaf (lower_n lower_height lower_blocks coefC CoefW)
open SigGolfCandidate.Research.SharedForest (chainPrefixes buildLeafPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem buildLeafPrefixes_precise {im : Image} (hsub : Sign.SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Sign.Seed.sub61)
    (hc : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hnew : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) Sign.seedHookCode)
    (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
    (hlay : A.lay ≠ 0) (hso : A.so = false) (hpc : s0.pc = pcOf (1013+27))
    (h15 : s0.getReg .x15 = BitVec.ofNat 64 (SigGolfCandidate.T3.height A.lay))
    (hvS : A.valp+16*A.n≤0x50000) (hdS : A.digp+A.n≤0x50000) (hdestS : A.dest+16≤0x50000)
    (hvi : A.valp+16*A.n≤0x20550 ∨ 0x20558≤A.valp)
    (carry : List Digest) (hcar : A.leaf % 7 ≠ 0 → SharedSeed.FamBuf s0 carry) :
    TBSim im sk s0 lowLeafC (buildLeafPrefixes A.lay A.tree A.leaf carry)
      (fun r t => t.pc=pcOf A.ret ∧ DigAt t A.dest r.1.1 ∧ r.1.2.length=43 ∧
        SharedSeed.FamBuf t r.2 ∧ RegsExcept s0 t leafRegs ∧
        Frame s0 t (fun X => LeafW A X ∨ BScr X) ∧
        Frame s0 t (Writes A s0) ∧
        (Selected A s0 → ∀ i, i<43 → ∀ k, k≤7 →
          DigAt t (SharedPrefixes.buffer A.lay.val i k) ((r.1.2.getD i []).getD k 0)) ∧
        Sign.Seed.Z32 t) := by
  have hn : A.n = 43 := lower_n hlay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLO : LOUT = 132032 := rfl
  obtain ⟨t1, st1, t1pc, t1x3, t1x19, t1l16, t1l24, t1r, t1f⟩ :=
    Sign.SharedLeaf.sub27_spec hsub s0 hpc A.lay A.tree A.leaf (by have := hpre.hroute; omega) hpre.x8 hpre.x9 hpre.x18
      (Or.inr h15) hlay
  have h0 : LeafInv s0 A 0 ([], []) t1 := by
    refine ⟨t1x19, ?_, by rw [t1x3, hpre.x1], t1r.mono (by decide), t1f.mono (fun X _ h => ?_), t1l16,
      t1l24, by simp, rfl, fun _ c hc => absurd hc (by omega), DigsAt.nil _ _⟩
    · rw [t1r.get (by simp), hpre.x23]; simp
    · unfold LeafW; rw [if_neg hlay]; omega
  have hs1 : HybOf s0 s0 t1 := HybOf.refl_of (t1f.mono (fun X _ h => by
    rcases h with h | h <;> (subst h; unfold BScr; omega)))
  have hc1 : A.leaf % 7 ≠ 0 → SharedSeed.FamBuf t1 carry := fun h =>
    (hcar h).frame t1f (fun X h1 h2 hx => by
      simp only [SharedSeed.FB, SharedSeed.FEND, COEF] at h1 h2; omega)
  unfold SigGolfCandidate.Research.SharedForest.buildLeafPrefixes
  refine TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 43 * chainC + 112)
    (coef_phase hsub hnew hhook sk hpre hlay h0 hs1 t1pc hc1) (fun cs u hu => ?_))) (by unfold lowLeafC coefC chainC lowerSeedC hornStepC; omega)
    (fun _ _ h => h)
  obtain ⟨upc, ucoef, ucarry, ur, uf⟩ := hu
  have hinvu : LeafInv (hyb s0 u) A 0 ([], []) u := LeafInv.rebase h0 hs1 (hyb_of s0 u) ur (by
      intro r hr
      simp only [PackedLeaf.coefRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    uf (fun X h => by
      unfold CoefW at h; unfold SeedW BScr
      rcases h with h | h | h | h
      · left; simp only [SharedSeed.FB, SharedSeed.FEND, COEF] at h; omega
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; exact h)
    hpre.hvs hvS (by omega)
  have hF00 : PSt s0 A cs.1 0 [] u :=
    ⟨by rw [if_pos rfl]; exact upc,ucoef,⟨_,[],hyb_of s0 u,hinvu⟩,rfl,by intros; omega,
      fun h => absurd h (by decide)⟩
  have hF0 : PSt s0 A cs.1 0 [] u ∧ Frame s0 u (Writes A s0) := by
    refine ⟨hF00,(t1f.trans uf).mono ?_⟩
    intro X hX h
    left
    simp only [CoefW,SharedSeed.FB,SharedSeed.FEND,COEF,PRIV,SEEDS,LEAFPK] at h
    omega
  have hfold := TBSim.foldlM_range' (image:=im) (sk:=sk) 0 43
    (prefixStep A cs.1) [] (fun j ps x => PSt s0 A cs.1 j ps x ∧ Frame s0 x (Writes A s0)) chainC
    (fun j hj st x hx => by
      simpa using (chain_step_precise hsub hcopy hc hpref hnew hhook sk hpre
        hlay hso hvS hdS hdestS hvi hj hx)) hF0
  rw [show List.range' 0 43 = List.range (chainCount A.lay) by rw [lower_n hlay]; exact List.range_eq_range'.symm]
    at hfold
  have heq : (List.range (chainCount A.lay)).foldlM (prefixStep A cs.1) [] =
      (List.range (chainCount A.lay)).mapM (fun i => chainPrefixes A.lay A.tree A.leaf i 0
        (maxDigit A.lay i) (WCT9.lowerFamilySeed cs.1 A.lay A.leaf i)) := by
    unfold prefixStep
    rw [foldlM_append_eq]
    simp only [List.nil_append,bind_pure]
    apply congrArg (fun f => (List.range (chainCount A.lay)).mapM f)
    funext i
    have hm : maxDigit A.lay i=7 := by unfold maxDigit; rw [if_neg hlay]
    rw [hm]
  rw [heq] at hfold
  refine TBSim.bind (W₁:=43*chainC) (W₂:=112) hfold (fun rows x hx => ?_)
  obtain ⟨⟨xpc,xcoef,⟨s3,values,hs3,hinv3⟩,xlen,xsaved,xz⟩,xprecise⟩ := hx
  have hpre3 := LeafPreS.transfer hpre hs3.regs hs3.base hdS
  rw [show (43 : Nat)=A.n from hn.symm] at hinv3
  have hex := Sign.SharedLeaf.leaf_exitS hsub sk hpre3 hinv3 (by rw [xpc,if_neg (by omega)])
  simp only [hso,Bool.false_eq_true,if_false] at hex
  have hds := hpre.hds
  rw [prefixEnds_eq A.lay hlay rows xlen]
  refine Sign.TBSim.of_eq' (TBSim.bind (W₂:=0) (f:=fun r => pure ((r.1,rows),cs.2))
    (hex.toTBSim (by rw [lower_blocks hlay]; norm_num)) (fun r y hy => TBSim.pure ?_))
    (by simp only [bind_assoc,pure_bind]) (by rw [lower_blocks hlay])
  obtain ⟨ypc,ydest,_,_,_,yregs,yframe,yf⟩ := hy
  refine ⟨ypc,ydest trivial,xlen,by
      rw [ucarry]
      exact xcoef.frame yf (fun X h1 h2 hx => by simp only [SharedSeed.FB, SharedSeed.FEND, COEF, LOUT] at *; omega),
    fun r hr => by rw [yregs.get hr,hs3.regs],?_,?_,?_,?_⟩
  · intro X hX hn'
    rw [yframe.get hX (fun h => hn' (Or.inl h)),hs3.base.get hX (fun h => hn' (Or.inr h))]
  · exact (xprecise.trans yf).mono (by
      intro X hX h
      rcases h with h|h
      · exact h
      · left; simp only [LOUT] at h; omega)
  · intro hsel i hi k hk
    have hlay1 : 1≤A.lay.val := by have hz : A.lay.val≠0 := fun h => hlay (Fin.ext h); omega
    have hb := SharedPrefixes.buffer_bounds (lay:=A.lay.val) hlay1 (by have := A.lay.isLt; omega) hi (by omega : k<8)
    exact (xsaved hsel i hi k hk).frame yf (by omega) (by unfold LOUT; omega) (by unfold LOUT; omega)
  · exact (xz (by decide)).frame yf (by unfold LOUT; omega) (by unfold LOUT; omega)

end ClaudeWCT.W9.Machine.Sign.SharedLeafMemory

namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
/-- Pairing stage 1: `Base.frame` when the only base cells in the write set are the F pads `CHAIN+32/40`, which are
zero again at the end (`Z32`). -/
theorem Base.frame_z32 {cfFlag : Nat} {sk : SecretKey} {cache : Bytes 131072} {t u : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : Base (cfFlag := cfFlag) sk cache t) (hf : Frame t u W) (hr : RegsExcept t u l)
    (h5 : .x5 ∉ l) (hW : ∀ A, A < 2 ^ 64 → BaseA A → W A → A = CHAIN + 32 ∨ A = CHAIN + 40) (hz : Z32 u) :
    Base (cfFlag := cfFlag) sk cache u := by
  have hf' : Frame t u (fun A => W A ∧ A ≠ CHAIN + 32 ∧ A ≠ CHAIN + 40) := by
    intro A hA hn
    by_cases h32 : A = CHAIN + 32
    · subst h32; rw [hz.1, h.zero _ (by decide) (by unfold NeverW; simp)]
    by_cases h40 : A = CHAIN + 40
    · subst h40; rw [hz.2, h.zero _ (by decide) (by unfold NeverW; simp)]
    exact hf A hA (fun hw => hn ⟨hw, h32, h40⟩)
  exact h.frame hf' hr h5 (fun A hA hb hw => by
    rcases hW A hA hb hw.1 with h' | h'
    · exact hw.2.1 h'
    · exact hw.2.2 h')
end SigGolfCandidate.T3M.Sign.Seed

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- The lower tree loop invariant (v6: for a leaf inside a family the coefficients sit in `FB`, `FamBuf`). -/
structure Inv (s1 : MachineState) (lay : Layer) (sb sel l : Nat)
    (st : List Digest × List (List Digest) × List Digest) (t : MachineState) : Prop where
  pc : t.pc=pcOf 1175
  x13 : t.getReg .x13=BitVec.ofNat 64 l
  regs : RegsExcept s1 t btRegs
  frame : Frame s1 t (BtW sb (height lay))
  precise : Frame s1 t (TreeWrites lay)
  len : st.1.length=l
  roots : DigsAt t (LOW+16*2^height lay) st.1
  saved : sel<l → st.2.1.length=43 ∧ ∀ i, i<43 → ∀ k,k≤7 →
    DigAt t (SharedPrefixes.buffer lay.val i k) ((st.2.1.getD i []).getD k 0)
  carry : l % 7 ≠ 0 → SharedSeed.FamBuf t st.2.2
  z : Seed.Z32 t

def body (lay : Layer) (tree sel : Nat) (st : List Digest × List (List Digest) × List Digest) (leaf : Nat) :
    T3.M (List Digest × List (List Digest) × List Digest) := do
  let ((root,prefixes),carry) ← SigGolfCandidate.Research.SharedForest.buildLeafPrefixes lay tree leaf st.2.2
  pure (st.1++[root],if leaf=sel then prefixes else st.2.1,carry)

variable {im : Image} (hc : SharedLowCode.Code im)
    (hsub : SharedLeafCode.Code im 1013)
    (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
variable {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat} {sb : Nat}
  {s1 : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1)
  (hselection : SharedPrefixes.selectionWord (s1.getMem 0x20550) lay.val=BitVec.ofNat 64 sel)
include hc hsub hcopy hchain hpref hseed hhook hs hselection
theorem body_step
    {l : Nat} (hl : l < 2 ^ height lay) {st : List Digest × List (List Digest) × List Digest} {t : MachineState}
    (htp : Inv s1 lay sb sel l st t) :
    TBSim im sk t (lowLeafC + 18)
      (body lay tree sel st l) (Inv s1 lay sb sel (l+1)) := by
  have ht := htp
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsb := hs.hsb
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1x6, t1r, t1f⟩ := blk1175_spec hc t ht.pc l (height lay) (by omega)
    (by rcases hH with h | h <;> omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_pos hl] at t1pc
  obtain ⟨t2, st2, t2pc, t2x18, t2x22, t2x23, t2r, t2f⟩ := blk1178_spec hc t1 t1pc l sel (by omega)
    (by have := hs.hsel; omega) (by rw [t1r.get (by simp)]; exact ht.x13)
    (by rw [t1r.get (by simp), g _ (by decide), hs.x14])
  obtain ⟨t3, k3, st3, hk3, t3pc, t3x22, t3x23, t3r, t3f⟩ : ∃ t3 k3, Steps im t2 k3 k3 t3 ∧
      k3 = (if l = sel then 3 else 0) ∧ t3.pc = pcOf 1187 ∧
      t3.getReg .x22 = BitVec.ofNat 64 (if l = sel then DIGITS else ZDIG) ∧
      t3.getReg .x23 = BitVec.ofNat 64 (if l = sel then sb else DUMMY) ∧
      RegsExcept t2 t3 [.x22, .x23] ∧ Frame t2 t3 (fun _ => False) := by
    by_cases hls : l = sel
    · rw [if_pos hls] at t2pc
      obtain ⟨u, stu, upc, u22, u23, ur, uf⟩ := blk1184_spec hc t2 t2pc
      refine ⟨u, 3, stu, by simp [hls], upc, by simp [hls, u22], ?_, ur, uf⟩
      rw [u23, t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x16]; simp [hls]
    · rw [if_neg hls] at t2pc
      exact ⟨t2, 0, Steps.refl _, by simp [hls], t2pc, by simp [hls, t2x22], by simp [hls, t2x23],
        RegsExcept.refl _ _, Frame.refl _ _⟩
  obtain ⟨t4, st4, t4pc, t4x1, t4x25, t4r, t4f⟩ := blk1187_spec hc t3 t3pc l (height lay) LOW hl
    (by rcases hH with h | h <;> omega) (by shared_tree_sgo)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp)]; exact ht.x13)
    (by rw [t3r.get (by simp), t2r.get (by simp)]; exact t1x6)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x2])
  have r14 : RegsExcept t t4 ([.x6] ++ [.x18, .x22, .x23] ++ [.x22, .x23] ++ [.x1, .x7, .x25]) :=
    ((t1r.trans t2r).trans t3r).trans t4r
  have f14 : Frame t t4 (fun _ => False) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun _ _ h => by simp_all)
  have hpre : LeafPreS sk t4 (btLeaf lay tree sel ds sb l) :=
    bt_leafPre hs hl ((ht.regs.trans r14).mono (by decide)) ((ht.frame.trans f14).mono
      (fun X _ h => by rcases h with h | h; exact h; exact h.elim)) t4x1
      (by rw [t4r.get (by simp), t3r.get (by simp)]; exact t2x18)
      (by rw [t4r.get (by simp)]; exact t3x22) (by rw [t4r.get (by simp)]; exact t3x23) t4x25
  have hcarry : l % 7 ≠ 0 → SharedSeed.FamBuf t4 st.2.2 := fun hp =>
    (htp.carry hp).frame f14 (fun _ _ _ h => h)
  have hvi : (btLeaf lay tree sel ds sb l).valp+16*(btLeaf lay tree sel ds sb l).n≤0x20550 ∨
      0x20558≤(btLeaf lay tree sel ds sb l).valp := by
    change (if l=sel then sb else DUMMY)+16*(btLeaf lay tree sel ds sb l).n≤0x20550 ∨ 0x20558≤(if l=sel then sb else DUMMY)
    rw [show (btLeaf lay tree sel ds sb l).n=43 from chainCount_low hlay]
    split_ifs <;> shared_tree_sgo
  have hleaf := SharedLeafMemory.buildLeafPrefixes_precise hsub hcopy hchain hpref hseed hhook sk hpre hlay rfl t4pc
    (by rw [(ht.regs.trans r14).get (by decide),hs.x15]; rfl)
    (by show (if l=sel then sb else DUMMY)+16*(btLeaf lay tree sel ds sb l).n≤0x50000
        rw [show (btLeaf lay tree sel ds sb l).n=43 from chainCount_low hlay]; split_ifs <;> shared_tree_sgo)
    (by show (if l=sel then DIGITS else ZDIG)+(btLeaf lay tree sel ds sb l).n≤0x50000
        rw [show (btLeaf lay tree sel ds sb l).n=43 from chainCount_low hlay]; split_ifs <;> shared_tree_sgo)
    (by show LOW+16*(2^height lay+l)+16≤0x50000; shared_tree_sgo) hvi st.2.2 hcarry
  have hselection4 : SharedLeafMemory.Selected (btLeaf lay tree sel ds sb l) t4 ↔ l=sel := by
    have idx : t4.getMem 0x20550=s1.getMem 0x20550 := by
      change t4.getMem (BitVec.ofNat 64 0x20550)=s1.getMem (BitVec.ofNat 64 0x20550)
      exact (ht.frame.trans f14).get (by decide) (by unfold BtW; shared_tree_sgo)
    unfold SharedLeafMemory.Selected
    change SharedPrefixes.selectionWord (t4.getMem 0x20550) lay.val=BitVec.ofNat 64 l ↔ _
    rw [idx,hselection]
    exact (ofNat_inj (by have := hs.hsel; omega) (by omega)).trans eq_comm
  unfold body
  refine TBSim.mono (TBSim.steps (st1.trans (st2.trans (st3.trans st4)))
    (TBSim.bind (W₂ := 2) hleaf (fun r u hu => ?_))) ?_ (fun _ _ h => h)
  rotate_left
  · rw [hk3]; unfold lowLeafC; split_ifs <;> omega
  obtain ⟨upc,uroot,ulen,ucarry,ur,uf,uprecise,usaved,uz⟩ := hu
  obtain ⟨⟨root, values⟩, carry⟩ := r
  obtain ⟨t5, st5, t5pc, t5x13, t5r, t5f⟩ := blk1191_spec hc u upc l
    (by rw [ur.get (by decide), r14.get (by simp)]; exact ht.x13)
  have hLW : ∀ X, (LeafW (btLeaf lay tree sel ds sb l) X ∨ SharedLeafMemory.BScr X) → BtW sb (height lay) X := by
    intro X h
    rcases h with h | h
    swap
    · unfold BtW BScr SharedLeafMemory.BScr at *; omega
    unfold LeafW at h
    rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
    change X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
      (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨ ((if (btLeaf lay tree sel ds sb l).lay = 0 then LEAFPK + 16 else LEAFPK) ≤ X ∧ X < LEAFPK + 16 * (43 + 2)) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
      ((if l = sel then sb else DUMMY) ≤ X ∧ X < (if l = sel then sb else DUMMY) + 16 * 43) ∨
      (LOW + 16 * (2 ^ height lay + l) ≤ X ∧ X < LOW + 16 * (2 ^ height lay + l) + 16) at h
    unfold BtW
    rw [show 2 ^ (height lay + 1) = 2 * 2 ^ height lay by rw [pow_succ]; ring]
    split_ifs at h <;> shared_tree_sgo
  have fU : Frame t t5 (BtW sb (height lay)) := ((f14.trans uf).trans t5f).mono (fun X _ h => by
    rcases h with (h | h) | h
    · exact h.elim
    · exact hLW X h
    · exact h.elim)
  have hc : SharedSeed.FamBuf t5 carry := ucarry.frame t5f (fun _ _ _ h => h)
  refine TBSim.pure_steps st5 ⟨t5pc,t5x13,?_,?_,?_,by simp [ht.len],?_,?_,fun _ => hc,
    uz.frame t5f (by simp) (by simp)⟩
  · exact (((ht.regs.trans r14).trans ur).trans t5r).mono (by decide)
  · exact (ht.frame.trans fU).mono (fun X _ h => by rcases h with h | h <;> exact h)
  · exact (((ht.precise.trans f14).trans uprecise).trans t5f).mono (by
      intro X hX h
      rcases h with ((h|h)|h)|h
      · exact h
      · exact h.elim
      · unfold SharedLeafMemory.Writes TreeWrites at *
        simp only [btLeaf] at h
        tauto
      · exact h.elim)
  ·
    have hd : DigAt u (LOW + 16 * 2 ^ height lay + 16 * st.1.length) root := by
      rw [ht.len, show LOW + 16 * 2 ^ height lay + 16 * l = LOW + 16 * (2 ^ height lay + l) by ring]
      exact uroot
    have hold : DigsAt u (LOW + 16 * 2 ^ height lay) st.1 := by
      refine ht.roots.frame ((f14.trans uf).mono (fun X _ h => h)) (by rw [ht.len]; shared_tree_sgo) ?_
      intro B h1 h2 h
      rw [ht.len] at h2
      rcases h with h | h | h
      · exact h
      swap
      · unfold SharedLeafMemory.BScr at h; shared_tree_sgo
      · unfold LeafW at h
        rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨ B = CHAIN + 24 ∨
          (CHAIN + 32 ≤ B ∧ B < CHAIN + 112) ∨ ((if (btLeaf lay tree sel ds sb l).lay = 0 then LEAFPK + 16 else LEAFPK) ≤ B ∧ B < LEAFPK + 16 * (43 + 2)) ∨ (LOUT ≤ B ∧ B < LOUT + 32) ∨
          ((if l = sel then sb else DUMMY) ≤ B ∧ B < (if l = sel then sb else DUMMY) + 16 * 43) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ B ∧ B < LOW + 16 * (2 ^ height lay + l) + 16) at h
        split_ifs at h <;> shared_tree_sgo
    exact (hold.snoc hd).frame t5f (by simp only [List.length_append, List.length_singleton, ht.len]; shared_tree_sgo)
      (fun _ _ _ h => h)
  · intro hsl
    by_cases hls : l=sel
    · simp only [hls,if_true]
      refine ⟨ulen,?_⟩
      intro i hi k hk
      have saved := usaved (hselection4.mpr hls) i hi k hk
      simp only [btLeaf] at saved
      have hb := SharedPrefixes.buffer_bounds (lay:=lay.val)
        (by have hz : lay.val≠0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hi (by omega : k<8)
      exact saved.frame t5f (by omega) (by simp) (by simp)
    · simp only [hls,if_false]
      obtain ⟨hlen,hsaved⟩ := ht.saved (by omega)
      refine ⟨hlen,?_⟩
      intro i hi k hk
      have hb := SharedPrefixes.buffer_bounds (lay:=lay.val)
        (by have hz : lay.val≠0 := fun h => hlay (Fin.ext h); omega) (by have := lay.isLt; omega) hi (by omega : k<8)
      refine (hsaved i hi k hk).frame ((f14.trans uprecise).trans t5f) (by omega) ?_ ?_
      all_goals
        have hnot : ¬ SharedLeafMemory.Selected (btLeaf lay tree sel ds sb l) t4 := fun h => hls (hselection4.mp h)
        simp only [SharedLeafMemory.Writes,hnot,false_and,or_false,false_or]
        omega

end SigGolfCandidate.T3M.Sign.SharedLowTree
