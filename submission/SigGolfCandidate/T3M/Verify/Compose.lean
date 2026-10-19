import SigGolfCandidate.T3M.Verify.Nonbinary.TopCost
import SigGolfCandidate.T3M.Verify.Nonbinary.TopRun
import SigGolfCandidate.T3M.Verify.Nonbinary.LayerContext
import SigGolfCandidate.T3M.Verify.MerkleSem
import SigGolfCandidate.T3M.Verify.AfterDefs
import SigGolfCandidate.T3M.Verify.TopSource

set_option Elab.async false

section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15,.x24]
/-- Campaign R6: the top chains write the 52 leaf slots from 25264 (the 32-byte gap [25232, 25264) after the tweak is
witness memory hashed as found) and the chain blocks. -/
def topChainWrites (A : Nat) : Prop := (25264 ≤ A ∧ A < 26112) ∨ (11768 ≤ A ∧ A < 15240)
/-- Campaign R6: the top leaf's known registers (`leafK 0` keeps `t0 = 0` but not main's `s2 = 0xFFF`: the R6
prologue loads `s2 = 856064`). -/
theorem topLeafK_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hr : RegsExcept s0 s topChainRegs) (h15 : s.getReg .x2 = 0x7fc00#64) : KnownOK (leafK 0) s := by
  intro p hp
  simp only [leafK, gkL, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals rw [hr.get (by simp [topChainRegs])]
  all_goals try exact he.mask
  all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
/-- Digit constants and leaf globals survive both the top entry and all chains. -/
theorem topLeafKeepK_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat)
    (t s0 s : MachineState) (a : BitVec 256) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hr : RegsExcept s0 s topChainRegs) : KnownOK (lfKeepK 0) s := by
  intro p hp
  simp [lfKeepK] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [hr.get (by simp [topChainRegs])]
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact he.table
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
/-- Campaign R6: at the final tail `ckTail d51` after the 52 top chains, the top leaf is ready: 52 ends at
`slotT j = 25264 + 16 j`, and the pad / gap / tweak high word are witness memory as found. -/
theorem topLeafReady_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s0 s : MachineState) (a : BitVec 256) (ends : List Digest) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hp : s.pc = pcOf (Nonbinary.ckTail
      ((nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).dig 51)))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites) (h15 : s.getReg .x2 = 0x7fc00#64)
    (hlen : ends.length = 52) (hend : ∀j<52, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk := topLeafK_of w pk index c t s0 s a ht he hr h15
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15224 ≤ topRowA c ∧ topRowA c ≤ 15480 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d,h12,hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have hg := Glob_writeHash ht.glob a d h12 (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))
  have hfr : Frame (writeHash t a) s (fun A => A = 25160 ∨ topChainWrites A) :=
    he.frame.trans hf
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h | h <;> omega) hk
  have hreg : ∀ r, r ∉ topChainRegs → r ∉ topEntryRegs → s.getReg r = t.getReg r := fun r h1 h2 => by
    rw [hr.get h1, he.regs.get h2, writeHash_getReg]
  have hy : (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).dig 51 < 8 := by
    rw [nctxOf_dig]
    unfold topDig
    rw [if_neg (by omega), if_pos rfl]
    omega
  -- witness words of the top leaf buffer that nothing writes before the leaf hash
  have hw : ∀ A, 25200 ≤ A → A < 25264 → A ≠ 25216 →
      s.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A h1 h2 _
    rw [hf.get (by omega) (by unfold topChainWrites; omega), he.frame.get (by omega) (by omega),
      writeHash_frame t a d A h12 (by omega) (by omega) (Or.inr (by omega))]
  have hlb0 : ClaudeWCT.W9.T3M.leafBufferBase 0 = 22296 := rfl
  refine ⟨⟨_,hy,hp⟩,hglob,?_,?_,?_,?_,hlen,hend,?_,?_,?_,?_⟩
  · exact topLeafKeepK_of w pk index c t s0 s a ht he hr
  · rw [hreg .x23 (by decide +kernel) (by decide +kernel)]
    exact ht.s7 0 rfl (by decide)
  · rw [hreg .x31 (by decide +kernel) (by decide +kernel)]
    exact (ht.t5 0 rfl).2 rfl
  · rw [hreg .x28 (by decide +kernel) (by decide +kernel), ht.word]
    exact hyperWord_top_prefix w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) |>.trans (by
      congr 1
      simp only [Nonbinary.NCtx.prefix, nctxOf, show T3.height 0 = 12 from rfl, Fin.val_zero]
      omega)
  · have ho := topEntry_orig w pk index c hc t s0 a ht he
    apply (ho.mono (fun o h => ⟨h.1, by
      norm_num [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, layerEnd] at *; omega⟩)).frame
    intro j hj hp
    exact hf.get (by unfold WIT WX at *;omega) (by
      norm_num [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots] at hp
      unfold topChainWrites WIT
      omega)
  · -- C3: the top leaf pad is witness memory
    have hpad := ht.bufferOrig.dig 22296 (by decide) (by unfold WX; decide) ⟨by decide, by decide⟩
      ⟨by decide, by decide⟩
    unfold ClaudeWCT.W9.T3M.wtopLeafPad; rw [hlb0]
    exact ⟨(hw 25200 (by omega) (by omega) (by omega)).trans hpad.1,
      (hw 25208 (by omega) (by omega) (by omega)).trans hpad.2⟩
  · -- Campaign R6: the 32-byte gap after the tweak is witness memory (hashed as found)
    have hg1 := ht.bufferOrig.dig 22328 (by decide) (by unfold WX; decide) ⟨by decide, by decide⟩
      ⟨by decide, by decide⟩
    have hg2 := ht.bufferOrig.dig 22344 (by decide) (by unfold WX; decide) ⟨by decide, by decide⟩
      ⟨by decide, by decide⟩
    unfold ClaudeWCT.W9.T3M.wtopLeafGap; rw [hlb0]
    exact ⟨⟨(hw 25232 (by omega) (by omega) (by omega)).trans hg1.1,
        (hw 25240 (by omega) (by omega) (by omega)).trans hg1.2⟩,
      ⟨(hw 25248 (by omega) (by omega) (by omega)).trans hg2.1,
        (hw 25256 (by omega) (by omega) (by omega)).trans hg2.2⟩⟩
  · -- C3: the top leaf tweak's high word is witness memory
    have hhi := ht.bufferOrig.hi 22312 (by decide) (by unfold WX; decide) ⟨by decide, by decide⟩
    unfold ClaudeWCT.W9.T3M.wleafHigh; rw [hlb0]
    exact (hw 25224 (by omega) (by omega) (by omega)).trans hhi
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem nctx_block (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - Verify.WIT = ClaudeWCT.W9.T3M.chainBlock 0 i := by
  change 13432 - 1664 + 64 * (53 - i) - Verify.WIT = 8096 + 16 * 48 + 64 * (54 - 1 - i)
  unfold Verify.WIT; omega
/-- Campaign R6: chain `i` of the top source program for the digit list `ds` (decoded: 51 data digits + checksum). -/
def srcChain (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ds : List Nat) (i : Nat) : T3.M Digest :=
  chainP 0 (route index 0).2 (route index 0).1 i (ds.getD i 0)
    (maxDigit 0 i - ds.getD i 0) (ClaudeWCT.W9.T3M.wchainPads w 0 i).1
    (ClaudeWCT.W9.T3M.wchainPads w 0 i).2 (ClaudeWCT.W9.T3M.wchainHeaderPad w 0 i) (ClaudeWCT.W9.T3M.wvalueFor w 0 ds i)
theorem topMax_maxDigit (i : Nat) : NCtx.topMax i = maxDigit 0 i := by
  simp only [NCtx.topMax, Nonbinary.mx, maxDigit, ite_true]
  split_ifs <;> omega
theorem nctx_chain_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (ds : List Nat)
    (i : Nat) (hds : ∀ j, j ≤ i → ds.getD j 0 = (nctxOf w index v p).dig j) :
    let c := nctxOf w index v p
    chainP 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.bufferVal i) =
      srcChain w index ds i := by
  have hbuf := (nctxOf w index v p).bufferVal_source ds i hds rfl
  dsimp only
  unfold srcChain
  rw [← hds i (le_refl _), topMax_maxDigit, hbuf]
  unfold NCtx.pad0 NCtx.pad1 NCtx.padHeader
  rw [nctx_block]
  rfl

theorem nctx_prefix_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (ds : List Nat)
    (m : Nat) (hds : ∀ j, j < m → ds.getD j 0 = (nctxOf w index v p).dig j) :
    (List.range' 0 m).foldlM (nctxOf w index v p).chainF [] =
      (List.range' 0 m).mapM (srcChain w index ds) := by
  unfold NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  apply mapM_congr'
  intro i hi
  have hi' := List.mem_range'_1.mp hi
  exact nctx_chain_eq w index v p ds i (fun j hj => hds j (by omega))
/-- Campaign R6: before a top rejection only data chains (i < 51) run. -/
theorem topRejectChains_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (m : Nat) (hm : m ≤ 51)
    (hL : ClaudeWCT.WCT9.topRejectLength v = m) :
    ClaudeWCT.WCT9.topRejectChains (ClaudeWCT.W9.T3M.topChainP w (route index 0).2 (route index 0).1 (dataDigits 0 v)) v =
      (List.range' 0 m).mapM (srcChain w index (dataDigits 0 v)) := by
  unfold ClaudeWCT.WCT9.topRejectChains
  rw [hL]
  refine (TopSource.take_mapM (fun n => chainP 0 (route index 0).2 (route index 0).1 n
    (ClaudeWCT.WCT9.topRunDigit v n) (maxDigit 0 n - ClaudeWCT.WCT9.topRunDigit v n)
    (ClaudeWCT.W9.T3M.wchainPads w 0 n).1 (ClaudeWCT.W9.T3M.wchainPads w 0 n).2
    (ClaudeWCT.W9.T3M.wchainHeaderPad w 0 n) (ClaudeWCT.W9.T3M.wvalueFor w 0 (dataDigits 0 v) n)) m (by omega)).trans ?_
  apply mapM_congr'
  intro n hn
  have hn' := List.mem_range'_1.mp hn
  unfold srcChain ClaudeWCT.WCT9.topRunDigit
  rw [if_pos (by omega)]
theorem chainsP_top_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ds : List Nat) :
    chainsP w 0 (route index 0).2 (route index 0).1 ds =
      (List.range' 0 52).mapM (srcChain w index ds) := by
  unfold chainsP
  simp only [ClaudeWCT.W9.T3M.chainPW_top]
  rw [← TopSource.take_mapM (srcChain w index ds) 52 (le_refl _)]
  rw [show (List.finRange (T3.chainCount 0)).take 52 = List.finRange (T3.chainCount 0) by
    rw [List.take_of_length_le]; simp [TopSource.chainCount0]]
  rfl

/-- Campaign R6: a valid g0 field takes the prologue's dispatch to group 0's cell. -/
theorem nctx_group0 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hv0 : Nonbinary.NCtx.gValid v 0) :
    (nctxOf w index v p).GroupIn s 0 [] s :=
  ⟨⟨fun _ _ => rfl, Frame.refl s _, by simp⟩, rfl,
    ((nctxOf w index v p).g0_group (nctx_fit6 w index v p) s he.pc).1 hv0⟩
/-- Campaign R6: an invalid g0 field faults at the prologue's dispatch. -/
theorem nctx_group0_bad (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hv0 : ¬ Nonbinary.NCtx.gValid v 0) : fetch vimage s = none :=
  ((nctxOf w index v p).g0_group (nctx_fit6 w index v p) s he.pc).2 hv0
/-- Campaign R6: chain 51's digit is the checksum (through `nctxOf_dig` with a symbolic index: a direct `show` makes
the unifier evaluate `min 7 (target 0 - sum)`). -/
theorem nctx_ck (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).CkOk := by
  intro ds hds h1 h2
  rw [nctx_dataSum] at hds
  have ht : T3.target 0 = 153 := rfl
  rw [nctxOf_dig]
  unfold topDig
  rw [if_neg (by omega), if_pos rfl, ht, hds]
  unfold Nonbinary.topT at h1 h2 ⊢
  omega
theorem top_chain_frame (c : NCtx) (hc : c.S3 = 13432) {s t : MachineState}
    (hf : Frame s t (c.Wr 52)) : Frame s t topChainWrites := by
  apply hf.mono
  intro A _ hA
  unfold NCtx.Wr NCtx.bufferEnd NCtx.blk Nonbinary.slot at hA
  rw [hc] at hA
  unfold topChainWrites
  split_ifs at hA <;> omega
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t
theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
set_option maxRecDepth 100000
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel
theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)
theorem cmp_good {P : Hash → Prop} (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQP P t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQP.halt (P := P) (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQP.stepsQ hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQP.stepsQ hu.steps (GoodQP.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height pad64 shortHash leafHash)
def kFin (pk : Digest) : Option Digest → OracleComp HashSpec Obs := fun x =>
  ccM (match x with
    | some r => pure (r == pk)
    | _ => pure false) Kb
theorem kFin_none (pk : Digest) : kFin pk none = pure (false, 0) := by simp [kFin, Kb]
theorem kFin_some (pk r : Digest) : kFin pk (some r) = pure (r == pk, 0) := by simp [kFin, Kb]
open ClaudeWCT.WCT9 (LayerMsg)
def RestIn (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index n : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  if n = 0 then match msg with
    | .forest root => CmpIn pk root s
    | .pair _ _ => False
  else LayerIn w pk index (n - 1) msg s
theorem mkEnd_top (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (u : MachineState) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk 0 (route index 0).1 u root t) : CmpIn pk root t := by
  have hl4 : (route index 0).1 < 4096 := by simpa [hL] using leaf_lt index 0
  have hpc : t.pc = pcOf (cmpPc (mkSh 0 1 (route index 0).1)) := by
    rw [ht.pc]
    congr 1
    simp [mkFin, cmpPc, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl,
      show mkOff 0 1 6 = 27 from rfl, BC.mkShp, mkShp]
    omega
  refine ⟨⟨mkSh 0 1 (route index 0).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
  · exact hpc
  · intro p hp
    simp only [cmpK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg, mkDst_cmp _ hl4]
  · rw [mkDst_cmp _ hl4]; exact ht.root
theorem mkStop_next (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index lay ends u)
    (v : Digest) (t : MachineState) (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    RestIn w pk index lay.val (mkMessage w index lay v) t := by
  by_cases h0 : lay.val = 0
  · have hz : lay = 0 := Fin.ext h0
    subst lay
    exact mkEnd_top w pk index u v t ht
  · simpa [RestIn, h0] using mkStop_next_lower w pk index hidx lay h0 ends u hu v t ht
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput route coreDigit dataDigits)
open Nonbinary (NCtx)
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem chainsCost_mono (c : NCtx) (m : Nat) (hm : m ≤ 52) : c.chainsCost 0 m ≤ c.chainsCost 0 52 := by
  have := Nonbinary.NCtx.chainsCost_add' c 0 m (52-m)
  rw [show m+(52-m)=52 by omega] at this
  omega
/-- Path-aware top accounting contract: the selector cost plus the verifier-side top path bonus is at most the
worst-case selector cost `selMax = 7`. e7b: hint clear (`verificationLow 0 high _ = !high`) costs 4 and earns the
top bonus 3; hint set costs 6 (LOW forced) or 7 (HIGH) and earns nothing. -/
theorem top_sel_bonus_le (high : Bool) (a : BitVec 256) :
    Verify.Nonbinary.selCost high a +
      ClaudeWCT.WCT9.CanonicalPolicy.pathBonus 0 (ClaudeWCT.WCT9.verificationLow 0 high a) ≤ 7 := by
  unfold Verify.Nonbinary.selCost
  cases high <;> simp [ClaudeWCT.WCT9.CanonicalPolicy.pathBonus, ClaudeWCT.WCT9.verificationLow] <;>
    split_ifs <;> omega
/-- Campaign R6: the verifier's group check is the spec's `topGroupValid`. -/
theorem topGroupValid_iff (v : Digest) (q : Nat) :
    ClaudeWCT.WCT9.topGroupValid v q = true ↔ Nonbinary.NCtx.gValid v q := by
  unfold ClaudeWCT.WCT9.topGroupValid Nonbinary.NCtx.gValid
  split_ifs <;> simp
/-- Campaign R6: the first invalid group (VER-A, S7). -/
theorem first_invalid (V : Digest) (h : ¬ ∀ q, q < 17 → Nonbinary.NCtx.gValid V q) :
    ∃ j, j < 17 ∧ (∀ q, q < j → Nonbinary.NCtx.gValid V q) ∧ ¬ Nonbinary.NCtx.gValid V j := by
  classical
  have hex : ∃ j, j < 17 ∧ ¬ Nonbinary.NCtx.gValid V j := by
    by_contra hn; push Not at hn; exact h (fun q hq => hn q hq)
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun q hq => ?_, (Nat.find_spec hex).2⟩
  have := Nat.find_min hex hq
  push Not at this
  exact this (by have := (Nat.find_spec hex).1; omega)
theorem topGroupBad_before (v : Digest) (j : Nat) (hval : ∀ q, q < j → Nonbinary.NCtx.gValid v q) (i : Nat)
    (hi : i < 3 * j) (hi51 : i < 51) : ClaudeWCT.WCT9.topGroupBad v i = false := by
  cases h : ClaudeWCT.WCT9.topGroupBad v i
  · rfl
  · rw [TopSource.topGroupBad_iff] at h
    rcases h with ⟨-, -, hg⟩ | ⟨h51, -⟩
    · have := (topGroupValid_iff v (i/3)).mpr (hval (i/3) (by omega))
      rw [hg] at this; cases this
    · omega
/-- Campaign R6: with the spare bit clear, the first invalid group `j` stops the verifier after `3 j` chains. -/
theorem topRejectLength_group (v : Digest) (hsp : v.toNat / 2 ^ 127 % 2 = 0) (j : Nat) (hj : j < 17)
    (hval : ∀ q, q < j → Nonbinary.NCtx.gValid v q) (hbad : ¬ Nonbinary.NCtx.gValid v j) :
    ClaudeWCT.WCT9.topRejectLength v = 3 * j := by
  apply TopSource.topRejectLength_bad v (3*j) (by omega) (by rw [Nonbinary.topSpare_eq]; exact hsp)
  · intro i hi
    exact topGroupBad_before v j hval i hi (by omega)
  · rw [TopSource.topGroupBad_iff]
    left
    refine ⟨by omega, by omega, ?_⟩
    rw [show 3 * j / 3 = j by omega]
    cases h : ClaudeWCT.WCT9.topGroupValid v j
    · rfl
    · exact absurd ((topGroupValid_iff v j).mp h) hbad
/-- Campaign R6: all 17 groups valid but the checksum out of range: the verifier runs the 51 data chains. -/
theorem topRejectLength_ck (v : Digest) (hsp : v.toNat / 2 ^ 127 % 2 = 0)
    (hval : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q)
    (hout : ¬ ((dataDigits 0 v).sum ≤ T3.target 0 ∧ T3.target 0 - (dataDigits 0 v).sum < 8)) :
    ClaudeWCT.WCT9.topRejectLength v = 51 := by
  apply TopSource.topRejectLength_bad v 51 (by omega) (by rw [Nonbinary.topSpare_eq]; exact hsp)
  · intro i hi
    exact topGroupBad_before v 17 hval i (by omega) hi
  · rw [TopSource.topGroupBad_iff]
    right
    refine ⟨rfl, ?_⟩
    unfold ClaudeWCT.WCT9.topChecksumOk
    simp only [decide_eq_false_iff_not]
    exact hout
/-- Campaign R6: the data digits agree with the chain context's digits. -/
theorem nctx_data_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    ∀ j, j < 51 → (dataDigits 0 v).getD j 0 = (nctxOf w index v p).dig j := by
  intro j hj
  rw [nctxOf_dig, ClaudeWCT.WCT9.dataDigits_top_getD v hj]
  unfold topDig
  rw [if_pos hj]
/-- Campaign R6: a decoded word's digits (data digits, then the checksum) are the chain context's digits. -/
theorem nctx_top_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat)
    (hs2 : T3.target 0 - (dataDigits 0 v).sum < 8) :
    ∀ j, j < 52 → (dataDigits 0 v ++ [T3.target 0 - (dataDigits 0 v).sum]).getD j 0 = (nctxOf w index v p).dig j := by
  intro j hj
  have hl := ClaudeWCT.WCT9.dataDigits_top_length v
  by_cases h51 : j < 51
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact h51)]
    exact nctx_data_digits w index v p j h51
  · have hj51 : j = 51 := by omega
    subst hj51
    rw [nctxOf_dig, List.getD_append_right _ _ _ _ (by rw [hl]), hl]
    unfold topDig
    rw [if_neg (by omega), if_pos rfl]
    simp only [Nat.sub_self, List.getD_cons_zero]
    omega
/-- Campaign R6: the verify data words (masks, gate) survive the top entry. -/
theorem topEntry_data (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s0 : MachineState) (a : BitVec 256) (hpre : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0) :
    DataOK s0 := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15224 ≤ topRowA c ∧ topRowA c ≤ 15480 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := hpre.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  exact (Glob_writeHash hpre.glob a d h12
    (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))).2.2.2.2.2.congr
    (fun A hlo hA => he.frame.get (by omega) (by unfold TAB at hlo; omega))
/-- Campaign R6: after the 52 top chains: the top leaf (7 cycles), the 12 folds and the root compare. -/
theorem top_leaf_tail (floors : T3.Layer → Nat) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat)
    (hc : c < nCopy 0) (hidx : index < 2 ^ 31) (t s0 : MachineState) (a : BitVec 256)
    (hpre : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (Q : Prop) (hQ : Q) (ends : List Digest) (z : MachineState)
    (hz : (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).TopOut
      (Nonbinary.NCtx.set24 s0 ((nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).s8v 16))
      ends z) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) z 78 271 Q 271
      (ccM (ClaudeWCT.WCT9.leafHashWG 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
        (ClaudeWCT.W9.T3M.wleafHigh w 0) (ClaudeWCT.W9.T3M.wtopLeafGap w) ends >>= merkleP w index 0)
        (fun r => kFin pk (some r))) := by
  obtain ⟨hr, hfz, hlen, hend, hpc, -⟩ := hz
  have hregs : RegsExcept s0 z topChainRegs := by
    intro r hrn
    have h24 : r ≠ .x24 := by intro hh; subst hh; exact hrn (by decide +kernel)
    rw [hr r (fun hh => hrn ((by decide +kernel : chainRegs ⊆ topChainRegs) hh)) h24,
      Nonbinary.NCtx.set24_regs s0 _ r h24]
  have hframe : Frame s0 z topChainWrites := top_chain_frame _ rfl hfz
  have h15 : z.getReg .x2 = 0x7fc00#64 := by
    rw [hregs.get (by decide +kernel)]; exact he.table
  have hready := topLeafReady_of w pk index c hc t s0 z a ends hpre he hpc hregs hframe h15 hlen
    (fun j hj => by have h := hend j (by omega); exact h)
  obtain ⟨u, st, hu⟩ := leafT_step w pk index c hc hidx ends z hready
  have hm := merkle_good (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) w pk index 0 ends u hidx hu
    (fun r => kFin pk (some r)) 9 8 8 Q
    (fun root t ht => by
      rw [kFin_some]
      exact cmp_good pk root t (mkEnd_top w pk index u root t (by simpa [MkStop] using ht)) Q hQ)
  have hmP : merkleP w index 0 = merklePrefix w index 0 := by
    funext x; rw [merkleP_eq]; rfl
  rw [hmP]
  have := GoodQP.steps st hm
  refine this.mono ?_ ?_ (fun h => ⟨h, ?_⟩) <;> simp [mkFuel_vals, mkCyc_vals]
/-- Campaign R6 top layer after its encoding hash: selector + prologue (`selCost + 8`, spare bit checked), the 17
groups and the checksum chain (`chainsCost 0 52 + 75`), leaf/folds/compare (271): accepted cost
`chainsCost 0 52 + 354 + selCost <= 1315 - floor` by the cost law (954 + penalty) and the policy's floor. -/
theorem top_after_hash (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (t : MachineState) (hpre : BC.EncPre w pk index 0 c t) (Q : Prop) (hQ : Q) (q : Query) (hq : EncQ 0 q)
    (a : BitVec 256) :
    GoodQP (fun hash => hash q = a ∧ HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w) hash) (writeHash t a) 2472 2800 Q
      (1315 - floors 0)
      (ccM (ClaudeWCT.W9.T3M.topLayerP w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a)) (kFin pk)) := by
  have hfloor := hbound 0
  obtain ⟨hT0, hT1⟩ := topTransition w pk index c hc t hpre a
  set v := T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a with hvdef
  have hsel := top_sel_bonus_le (ClaudeWCT.W9.T3M.wtopHigh w) a
  have hsel7 := Verify.Nonbinary.selCost_le (ClaudeWCT.W9.T3M.wtopHigh w) a
  unfold Verify.Nonbinary.selMax at hsel7
  have hv128 : v.toNat < 2 ^ 128 := v.isLt
  by_cases hsp : v.toNat / 2 ^ 127 % 2 = 0
  swap
  · -- spare bit set: decode fails before any chain; the prologue's `blt` lands on a zero word
    obtain ⟨n, z, st, hn, hfz⟩ := hT1 (by omega)
    have hdec : T3.decode 0 v = none := by
      cases hd : T3.decode 0 v with
      | none => rfl
      | some ds =>
        obtain ⟨-, hrv, -, -⟩ := ClaudeWCT.WCT9.decode_top_some hd
        exact absurd ((Nonbinary.NCtx.topRanksValid_iff v).mp hrv).1 hsp
    refine GoodQP.pre_mono (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) ?_ (fun _ h => h.2)
    refine Nonbinary.NCtx.goodQ_vacuous (A := 0) ?_ Q (1315 - floors 0)
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode_none w index hdec, ccM_map]
    simp only [kFin_none]
    rw [topRejectChains_eq w index v 0 (by omega)
      (TopSource.topRejectLength_spare v (by rw [Nonbinary.topSpare_eq]; exact hsp))]
    simp only [List.range'_zero, List.mapM_nil, ccM_pure]
    exact (GoodQP.steps st (Nonbinary.NCtx.goodQ_fault (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w))
      (Q := False) (A := 0) hfz)).mono (by omega) (by omega) (fun h => h.elim)
  obtain ⟨n0, s0, st0, hn0, hn0e, he⟩ := hT0 hsp
  set L := nctxOf w index v (trPc 0 c) with hLdef
  have hLok : L.ok := nctx_ok w index v c hidx
  have hkn : ∀ p ∈ L.known, s0.getReg p.1 = p.2 := nctx_known w pk index c t s0 a hpre he
  have hO := nctx_orig w index v (trPc 0 c) s0 (topEntry_orig w pk index c hc t s0 a hpre he)
    (topEntry_bufferOrig w pk index c hc t s0 a hpre he) (topEntry_data w pk index c hc t s0 a hpre he)
  have hf : L.Fit6 v := nctx_fit6 w index v (trPc 0 c)
  have hds : L.DigitsOk := nctx_digits w index v (trPc 0 c)
  have hEnc : Nonbinary.NCtx.Encoded6 v s0 := topEntry_encoded6 he
  have hck : L.CkOk := nctx_ck w index v (trPc 0 c)
  have hsumL : ((List.range 51).map L.dig).sum = (dataDigits 0 v).sum := nctx_dataSum w index v (trPc 0 c)
  have hcc : L.chainsCost 0 52 ≤ 2335 := L.chainsCost_any hds
  have hT : Nonbinary.topT = 153 := rfl
  have htg : T3.target 0 = 153 := rfl
  cases hdec : T3.decode 0 v with
  | some ds =>
    obtain ⟨-, hrv, ⟨hs1, hs2⟩, rfl⟩ := ClaudeWCT.WCT9.decode_top_some hdec
    have hval : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q := ((Nonbinary.NCtx.topRanksValid_iff v).mp hrv).2
    have hin : Nonbinary.topT - 7 ≤ ((List.range 51).map L.dig).sum ∧
        ((List.range 51).map L.dig).sum ≤ Nonbinary.topT := by
      rw [hsumL, hT]; rw [htg] at hs1 hs2; omega
    have hdsL := nctx_top_digits w index v (trPc 0 c) hs2
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode w index hdec, ccM_map, layerP_eq, ccM_bind, chainsP_top_eq,
      ← nctx_prefix_eq w index v (trPc 0 c) _ 52 hdsL]
    have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hval 0 (by omega))
    have body : GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) (writeHash t a) 2472 2800 Q
        (L.chainsCost 0 52 + 354 + Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a)
        (ccM ((List.range' 0 52).foldlM L.chainF [])
          (fun ends => ccM (ClaudeWCT.WCT9.leafHashWG 0 (route index 0).2 (route index 0).1
            (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w 0) (ClaudeWCT.W9.T3M.wtopLeafGap w) ends >>=
              merkleP w index 0)
            (fun r => kFin pk (some r)))) := by
      have H := L.top_full (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hck hkn hO hEnc hf hval hin
        (fun ends => ccM (ClaudeWCT.WCT9.leafHashWG 0 (route index 0).2 (route index 0).1
            (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w 0) (ClaudeWCT.W9.T3M.wtopLeafGap w) ends >>=
              merkleP w index 0)
          (fun r => kFin pk (some r))) 78 271 271 Q
        (fun ends z hz => top_leaf_tail floors w pk index c hc hidx t s0 a hpre he Q hQ ends z hz)
        s0 hg0
      have H2 := GoodQP.steps st0 H
      rw [Nonbinary.NCtx.ov_17] at H2
      exact H2.mono (by omega) (by omega) (fun h => ⟨h, by omega⟩)
    by_cases hcr : L.chainsCost 0 52 + Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a ≤ 961 - floors 0
    · exact (body.mono (le_refl _) (le_refl _) (fun h => ⟨h, by omega⟩)).pre_mono (fun _ h => h.2)
    · refine GoodQP.of_false_pre body ?_
      rintro hash ⟨hea, hok⟩
      have h7 := hok 0 q hq _ (by rw [hea]; exact hdec)
      simp only [ClaudeWCT.WCT9.CanonicalPolicy.pathReward, ClaudeWCT.WCT9.CanonicalPolicy.reward, hea] at h7
      rw [ClaudeWCT.WCT9.wordCredit_top hdec] at h7
      have hbalance := L.chainsCost_accepted hds v _ hdec hdsL
      exact hcr (by omega)
  | none =>
    refine GoodQP.pre_mono (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) ?_ (fun _ h => h.2)
    refine Nonbinary.NCtx.goodQ_vacuous (A := 0) ?_ Q (1315 - floors 0)
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode_none w index hdec, ccM_map]
    simp only [kFin_none]
    by_cases hall : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q
    · -- every group valid: the checksum is out of range
      have hout : ¬ ((dataDigits 0 v).sum ≤ T3.target 0 ∧ T3.target 0 - (dataDigits 0 v).sum < 8) := by
        rintro ⟨hs1, hs2⟩
        have hr : T3.topRanksValid v = true := (Nonbinary.NCtx.topRanksValid_iff v).mpr ⟨hsp, hall⟩
        rw [ClaudeWCT.WCT9.decode_top_of (by simpa [T3.encodedBits] using hv128) hr hs1 hs2] at hdec
        cases hdec
      have houtM : ¬ (Nonbinary.topT - 7 ≤ ((List.range 51).map L.dig).sum ∧
          ((List.range 51).map L.dig).sum ≤ Nonbinary.topT) := by
        rw [hsumL, hT]; rw [htg] at hout; omega
      rw [topRejectChains_eq w index v 51 (le_refl _) (topRejectLength_ck v hsp hall hout),
        ← nctx_prefix_eq w index v (trPc 0 c) _ 51 (nctx_data_digits w index v (trPc 0 c))]
      have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hall 0 (by omega))
      have H := L.top_bad_ck (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hkn hO hEnc hf hall houtM
        (fun _ => pure (false, 0)) (fun _ => rfl) False 0 s0 hg0
      have hm := chainsCost_mono L 51 (by omega)
      rw [Nonbinary.NCtx.ov_17, show (3 * 17 : Nat) = 51 from rfl] at H
      exact (GoodQP.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)
    · obtain ⟨j, hj17, hjmin, hjbad⟩ := first_invalid v hall
      have hL := topRejectLength_group v hsp j hj17 hjmin hjbad
      by_cases hj0 : j = 0
      · subst hj0
        rw [topRejectChains_eq w index v 0 (by omega) hL]
        simp only [List.range'_zero, List.mapM_nil, ccM_pure]
        have hfz := nctx_group0_bad w index v (trPc 0 c) _ s0 he hjbad
        exact (GoodQP.steps st0 (Nonbinary.NCtx.goodQ_fault (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w))
          (Q := False) (A := 0) hfz)).mono (by omega) (by omega) (fun h => h.elim)
      · rw [topRejectChains_eq w index v (3 * j) (by omega) hL,
          ← nctx_prefix_eq w index v (trPc 0 c) _ (3 * j)
            (fun i hi => nctx_data_digits w index v (trPc 0 c) i (by omega))]
        have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hjmin 0 (by omega))
        have H := L.top_bad_group (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hkn hO hEnc hf j
          (by omega) (by omega) hjmin hjbad (fun _ => pure (false, 0)) (fun _ => rfl) False 0 s0 hg0
        have hm := chainsCost_mono L (3 * j) (by omega)
        have hov := Nonbinary.NCtx.ov_le j (by omega)
        exact (GoodQP.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)

end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route leafHash)
open ClaudeWCT.WCT9 (LayerMsg)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
/-- Stage 2 (C2 + C3, as #866): top head 5 steps (row high-word pad), top leaf without the 16-byte pad stores and the
leaf tweak high-word store. Configuration (1)+(2): target 146 (accepted chains 936 -> 927) and the e7b
top-half selector (worst path 7 instead of 4, the honest LOW path's 3 cycles are credited by the top path bonus):
1292 -> 1286, fuel/cycles +3. -/
def topFuel : Nat := 5 + 1 + 2472
def topCyc : Nat := 5 + 8 + 2800
/-- Campaign R6: the top accepting constant is main's 1286 + 29 (= dK 92 - 9 (153 - 146)); with the RC pool 73 the
after-FTS bound is 5326 - 73 = 5253. -/
def topCycA (floors : T3.Layer → Nat) : Nat := 5 + 8 + (1315 - floors 0)
theorem top_layer_good (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q)
    (M : LayerMsg) (s : MachineState) (hs : LayerIn w pk index 0 M s) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) s topFuel topCyc Q (topCycA floors)
      (ccM (BC.layerLoop w index 1 M) (kFin pk)) := by
  rw [layerLoop_one]
  have hA := BC.encoding_setup w pk index 0 M s hs
  have hsA : stepsA (0 : Layer).val = 5 := rfl
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w index 0).toNat ≥ ClaudeWCT.WCT9.verifyWindow
  · exact absurd hctr (ClaudeWCT.WCT9.ctr_not_ge_verifyWindow _)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, hpre⟩ := hA.2 (by omega)
    set c := BC.cpIdx index (0 : Layer).val with hcdef
    have hc : c < nCopy 0 := by
      have h := BC.nCopy_eq
      have : c < 128 := by
        show (if (0 : Nat) = 3 then 0 else index / 2 ^ below (0 + 1) % 2 ^ hL (0 + 1)) < 128
        rw [if_neg (by decide +kernel)]
        exact lt_of_lt_of_le (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel)
      omega
    rw [hsA] at hst
    have hblk := BC.encoding_blocks w index 0 (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcHigh w index 0)
    have hq := encQ_layer 0 (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcCtr w index 0)
      (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w) (ClaudeWCT.W9.T3M.wbcHigh w index 0)
    have := GoodQP.verificationHash_bind_pre (lay := 0) (high := ClaudeWCT.W9.T3M.wtopHigh w)
      (f := ClaudeWCT.W9.T3M.topLayerP w index) hf h5 hv hin
      (fun a => by
        rw [show ClaudeWCT.WCT9.verificationAnswer 0 (ClaudeWCT.W9.T3M.wtopHigh w) a =
          T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a from rfl]
        exact top_after_hash floors hbound w pk index c hc hidx t hpre Q hQ _ hq a)
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by simp [topFuel]) (by simp [topCyc]) (by simp [topCycA]; omega))
def lCyc : Nat → Nat
  | 0 => 8
  | 1 => topCyc
  | n + 2 => layerCost (n + 1) 0 + mkCyc (n + 1) + lCyc (n + 1)
def lCycA (floors : T3.Layer → Nat) : Nat → Nat
  | 0 => 8
  | 1 => topCycA floors
  | n + 2 => layerCostA floors (n + 1) + mkCyc (n + 1) + lCycA floors (n + 1)
def lFuel : Nat → Nat
  | 0 => 9
  | 1 => topFuel
  | n + 2 => layerFuel (n + 1) + mkFuel (n + 1) + lFuel (n + 1)
theorem lCyc_4 : lCyc 4 = 6811 := by decide +kernel
/-- Stage 2: floor-free constant 5303 (stage 1: 5334; C2 −13, C3 −7). Configuration (1)+(2): 5297 (top −9 + 3). -/
theorem lCycA_4 (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) :
    lCycA floors 4 = 5326 - ((List.finRange 4).map floors).sum := by
  have h0 := hbound 0
  have h1 := hbound 1
  have h2 := hbound 2
  have h3 := hbound 3
  change (1181 - floors 3) + 153 + ((1173 - floors 2) + 153 +
    ((1173 - floors 1) + 165 + (5 + 8 + (1315 - floors 0)))) =
      5326 - (floors 0 + (floors 1 + (floors 2 + (floors 3 + 0))))
  omega
theorem lFuel_4 : lFuel 4 = 7855 := by decide +kernel
theorem layers_good (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ msg s, RestIn w pk index n msg s →
      GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) s (lFuel n) (lCyc n) Q (lCycA floors n)
        (ccM (BC.layerLoop w index n msg) (kFin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ msg s hs
    cases msg with
    | forest root =>
      simp only [BC.layerLoop, ccM_pure, kFin_some]
      exact cmp_good pk root s hs Q hQ
    | pair left right => exact False.elim hs
  | succ n ih =>
    intro hn msg s hs
    have hs' : LayerIn w pk index n msg s := by simpa [RestIn] using hs
    by_cases hn0 : n = 0
    · subst hn0
      exact top_layer_good floors hbound w pk index hidx Q hQ msg s hs'
    have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < 4 by omega)]
    have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h => hn0 (by rw [← hv, h]; rfl)
    rw [layerLoop_succ w index n (by omega) hn0 msg]
    have hg := layer_good_low floors hbound (ClaudeWCT.W9.T3M.wtopHigh w) w pk index (Fin.ofNat 4 n) hlay msg s (by rwa [hv])
      (fun ends => ClaudeWCT.WCT9.leafHashW (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w (Fin.ofNat 4 n)) ends >>=
        fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n)
      (kFin pk) (kFin_none pk) (lFuel n + mkFuel n) (lCyc n + mkCyc n) (lCycA floors n + mkCyc n) Q
      (fun ends u hu => by
        have hm := merkle_good_low (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) w pk index (Fin.ofNat 4 n) hlay ends u hidx hu
          (fun v => ccM (BC.layerLoop w index n (mkMessage w index (Fin.ofNat 4 n) v)) (kFin pk))
          (lFuel n) (lCyc n) (lCycA floors n) Q
          (fun v t ht => ih (by omega) _ t (by
            have h := mkStop_next w pk index hidx (Fin.ofNat 4 n) ends u hu v t ht
            rw [hv] at h
            exact h))
        simp only [ccM_bind, merkleMsg, ccM_pure, hv] at hm ⊢
        exact hm)
    rw [hv] at hg
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 + 1 = m + 2 from rfl]
    exact hg.mono (by simp only [lFuel]; omega) (by simp only [lCyc]; omega)
      (fun q => ⟨q, by simp only [lCycA]; omega⟩)
theorem after_good (floors : T3.Layer → Nat) (hcredit : CreditFloors floors) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (Q : Prop) (hQ : Q) (a : HashOutput)
    (top : Digest × Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ top u) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) u 8050 8050 Q 5253
      (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb) := by
  have hidx : ClaudeWCT.WCT9.digestIndex a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ top.1 top.2 u hidx h.glob h.idx h.pc h.left h.right h.wit h.base h.a1
    h.s10 h.heapOne h.heapTwo h.heapSeven h.heapThree h.heapFour h.heapFive h.coordStep h.topBase h.top h.top8 h.a2 h.d0
  have hg := layers_good floors hcredit.1 w pk _ hidx Q hQ 4 le_rfl (.pair top.1 top.2) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb =
      ccM (BC.layerLoop w (ClaudeWCT.WCT9.digestIndex a) 4 (.pair top.1 top.2)) (kFin pk) := by
    unfold afterFts
    rw [ccM_bind]
    rfl
  rw [e]
  rw [lFuel_4, lCyc_4, lCycA_4 floors hcredit.1] at hg
  have htotal := hcredit.2
  exact GoodQP.stepsQ hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
theorem after_good_budget : AfterGoodBudget 5253 :=
  fun floors hcredit pk w Q hQ a top u h => after_good floors hcredit pk w Q hQ a top u h
end SigGolfCandidate.T3M
end
