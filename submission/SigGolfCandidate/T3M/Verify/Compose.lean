import SigGolfCandidate.T3.Nonbinary.Cost
import SigGolfCandidate.T3M.Verify.Nonbinary.TopRun
import SigGolfCandidate.T3M.Verify.Nonbinary.LayerContext
import SigGolfCandidate.T3M.Verify.MerkleSem
import SigGolfCandidate.T3M.Verify.Init
import SigGolfCandidate.T3M.Verify.AfterDefs
import SigGolfCandidate.T3M.Verify.TopSource

section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfResearch.NonbinaryTop
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
def digitCredit (i d : Nat) : Nat := if last i≤d then 1 else 0
def digitSum (f : Nat → Nat) : Nat := ((List.range 54).map f).sum
def creditSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => digitCredit i (f i)).sum
def liveCredit (i d : Nat) : Nat := if d < topMax i then 1 else 0
def liveSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => liveCredit i (f i)).sum
def totalCost (f : Nat → Nat) : Nat := ((List.range 54).map fun i => chainCost i (f i)).sum
theorem chainCost_balance (i d : Nat) (hd : d≤topMax i) :
    chainCost i d+9*d+digitCredit i d+liveCredit i d=5+tableJump i+9*topMax i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost digitCredit liveCredit
  split_ifs <;> omega
theorem total_balance (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    totalCost f+9*digitSum f+creditSum f+liveSum f=2308 := by
  have H : ∀ l : List Nat,(∀i∈l,f i≤topMax i) →
      (l.map fun i => chainCost i (f i)).sum+9*(l.map f).sum+
        (l.map fun i => digitCredit i (f i)).sum+(l.map fun i => liveCredit i (f i)).sum=
        (l.map fun i => 5+tableJump i+9*topMax i).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := chainCost_balance i (f i) (h i (by simp))
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons]
      omega
  have hs := H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
  have he : ((List.range 54).map fun i => 5+tableJump i+9*topMax i).sum=2308 := by decide +kernel
  exact hs.trans he
theorem packed_credit_floor (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    54 ≤ creditSum f + liveSum f := by
  have H : ∀ l : List Nat, (∀ i ∈ l, f i ≤ topMax i) →
      l.length ≤ (l.map fun i => digitCredit i (f i)).sum +
        (l.map fun i => liveCredit i (f i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      have hcredit : 1 ≤ digitCredit i (f i) + liveCredit i (f i) := by
        unfold digitCredit liveCredit last
        split_ifs <;> omega
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  simpa only [creditSum, liveSum, List.length_range] using
    H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
def exactSum (f : Nat → Nat) : Nat := ((List.range 54).map fun i => if f i = last i then 1 else 0).sum
theorem credit_live_exact (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) :
    creditSum f + liveSum f = 54 + exactSum f := by
  have H : ∀ l : List Nat, (∀ i ∈ l, f i ≤ topMax i) →
      (l.map fun i => digitCredit i (f i)).sum + (l.map fun i => liveCredit i (f i)).sum =
        l.length + (l.map fun i => if f i = last i then 1 else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro h
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      have hm := topMax_bounds i
      have hcredit : digitCredit i (f i) + liveCredit i (f i) = 1 + (if f i = last i then 1 else 0) := by
        unfold digitCredit liveCredit last
        split_ifs <;> omega
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  simpa only [creditSum, liveSum, exactSum, List.length_range] using
    H (List.range 54) (fun i hi => hd i (List.mem_range.mp hi))
theorem topCredit_exact (v : Digest) : T3.topCredit v = exactSum (coreDigit 0 v) := by
  unfold T3.topCredit exactSum
  congr 1
theorem coreDigit_topMax (v : Digest) : ∀i,i<54 → coreDigit 0 v i≤topMax i := by
  intro i hi
  have hc := T3.Nonbinary.coreDigit_le (0:Layer) v i
  have he : maxDigit 0 i=topMax i := by
    unfold maxDigit topMax mx
    simp only [ite_true]
    split_ifs <;> omega
  rw [he] at hc
  exact hc
theorem total_any (f : Nat → Nat) (hd : ∀i,i<54 → f i≤topMax i) : totalCost f ≤ 2254 := by
  have hb := total_balance f hd
  have hc := packed_credit_floor f hd
  omega
theorem accepted_total_credit {v : Digest} {digits : List Nat}
    (h : T3.decode 0 v=some digits) : totalCost (coreDigit 0 v)+T3.topCredit v=958 := by
  have hd := coreDigit_topMax v
  have hs : digitSum (coreDigit 0 v)=144 := by
    obtain ⟨-, -, hsum, -⟩ := ClaudeWCT.WCT9.decode_top_some h
    have h144 : (T3.dataDigits 0 v).sum = 144 := hsum
    simpa [digitSum, T3.dataDigits, T3.dataCount] using h144
  have hb := total_balance (coreDigit 0 v) hd
  have hc := credit_live_exact (coreDigit 0 v) hd
  rw [topCredit_exact]
  omega
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15,.x24]
def topChainWrites (A : Nat) : Prop := (544 ≤ A ∧ A < 1488) ∨ (10240 ≤ A ∧ A < 13712)
theorem topLeafK_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s0)
    (hr : RegsExcept s0 s topChainRegs) (h15 : s.getReg .x2 = 0x3fe00#64) : KnownOK (leafK 0) s := by
  intro p hp
  simp [leafK,baseK] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals try exact h15
  all_goals rw [hr.get (by simp [topChainRegs])]
  all_goals try exact he.mask
  all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
theorem topLeafReady_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s0 s : MachineState) (a : BitVec 256) (ends : List Digest) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s0)
    (hp : ∃ y, y < 8 ∧ s.pc = pcOf (Nonbinary.finW y))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites) (h15 : s.getReg .x2 = 0x3fe00#64)
    (h24 : s.getReg .x24 = 0)
    (hlen : ends.length = 54) (hend : ∀j<54, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk := topLeafK_of w pk index c t s0 s a ht he hr h15
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 13696 ≤ topRowA c ∧ topRowA c ≤ 13952 ∧ topRowA c % 16 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d,h12,hd⟩ := ht.dst (by decide +kernel)
  change d = topRowA c ∨ d = topRowA c + 48 at hd
  have hg := Glob_writeHash ht.glob a d h12 (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))
  have hfr : Frame (writeHash t a) s topChainWrites :=
    (he.frame.trans hf).mono (by intro A h; simpa using h)
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h <;> omega) hk
  have hreg : ∀ r, r ∉ topChainRegs → r ∉ topEntryRegs → s.getReg r = t.getReg r := fun r h1 h2 => by
    rw [hr.get h1, he.regs.get h2, writeHash_getReg]
  refine ⟨hp,hglob,?_,?_,?_,?_,hlen,hend,?_,h24⟩
  · intro p hp
    simp [lfKeepK] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hr.get (by simp [topChainRegs])]
    all_goals try exact he.s3
    all_goals try exact he.ra
    all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
    all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
  · rw [hreg .x23 (by decide +kernel) (by decide +kernel)]
    exact ht.s7 0 rfl (by decide)
  · rw [hreg .x31 (by decide +kernel) (by decide +kernel)]
    exact (ht.t5 0 rfl).2 rfl
  · rw [hreg .x28 (by decide +kernel) (by decide +kernel), ht.word]
    exact hyperWord_top_prefix w index (a.extractLsb' 0 128) (trPc 0 c) |>.trans (by
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
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem nctx_block (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - 0x800 = ClaudeWCT.W9.T3M.chainBlock 0 i := by
  change 11904 - 1664 + 64 * (53 - i) - 2048 = 7424 + 16 * 48 + 64 * (54 - 1 - i)
  omega
def srcChain (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (i : Nat) : T3.M Digest :=
  chainP 0 (route index 0).2 (route index 0).1 i ((dataDigits 0 v).getD i 0)
    (maxDigit 0 i - (dataDigits 0 v).getD i 0) (ClaudeWCT.W9.T3M.wchainPads w 0 i).1
    (ClaudeWCT.W9.T3M.wchainPads w 0 i).2 (ClaudeWCT.W9.T3M.wchainHeaderPad w 0 i) (ClaudeWCT.W9.T3M.wvalue w 0 i)
theorem nctx_chain_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) (hi : i < 54) :
    let c := nctxOf w index v p
    chainP 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i) =
      srcChain w index v i := by
  have hm : NCtx.topMax i = maxDigit 0 i := by
    simp [NCtx.topMax, Nonbinary.mx, maxDigit, show (i / 3 < 17) ↔ i < 51 by omega]
  dsimp only
  unfold srcChain
  rw [T3.dataDigits_getD 0 v i hi, hm]
  unfold NCtx.pad0 NCtx.pad1 NCtx.padHeader NCtx.val
  rw [nctx_block]
  rfl
theorem nctx_prefix_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p m : Nat) (hm : m ≤ 54) :
    (List.range' 0 m).foldlM (nctxOf w index v p).chainF [] =
      (List.range' 0 m).mapM (srcChain w index v) := by
  unfold NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  apply mapM_congr'
  intro i hi
  exact nctx_chain_eq w index v p i (by have := List.mem_range'_1.mp hi; omega)
theorem topRejectChains_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (m : Nat) (hm : m ≤ 54)
    (hL : ClaudeWCT.WCT9.topRejectLength v = m) :
    ClaudeWCT.WCT9.topRejectChains (ClaudeWCT.W9.T3M.topChainP w (route index 0).2 (route index 0).1) v =
      (List.range' 0 m).mapM (srcChain w index v) := by
  unfold ClaudeWCT.WCT9.topRejectChains
  rw [hL]
  exact TopSource.take_mapM (srcChain w index v) m hm
theorem chainsP_top_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) :
    chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) =
      (List.range' 0 54).mapM (srcChain w index v) := by
  unfold chainsP
  rw [← TopSource.take_mapM (srcChain w index v) 54 (le_refl _)]
  rw [show (List.finRange (T3.chainCount 0)).take 54 = List.finRange (T3.chainCount 0) by
    rw [List.take_of_length_le]; simp [TopSource.chainCount0]]
  rfl
theorem nctx_fit (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).Fit (T3.topFlip v) := fun i _ => by
  show coreDigit 0 v i = _
  unfold coreDigit NCtx.rawDigit T3.topCode
  simp
theorem nctx_group0 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hv0 : Search.topRank (T3.topFlip v) 0 < 125) :
    (nctxOf w index v p).GroupIn s 0 [] s := by
  let c := nctxOf w index v p
  have hf : c.Fit (T3.topFlip v) := nctx_fit w index v p
  refine ⟨⟨fun r hr => rfl, Frame.refl s _, by simp⟩,rfl,?_⟩
  rw [he.pc, Nonbinary.prefixTarget_flip]
  unfold NCtx.entPc
  rw [c.fit_rank' hf 0 (by decide +kernel) hv0]
  have h0 : Search.topRank (T3.topFlip v) 0 = (T3.topFlip v).toNat % 128 := by unfold Search.topRank; simp
  rw [h0] at hv0 ⊢
  simp only [Nonbinary.entW, Nonbinary.cellW, Nonbinary.entOff, pcOf]
  simp
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem top_chain_frame (c : NCtx) (hc : c.S3 = 11904) {s t : MachineState}
    (hf : Frame s t (c.Wr 54)) : Frame s t topChainWrites := by
  apply hf.mono
  intro A _ hA
  simpa only [NCtx.Wr, NCtx.blk, hc, topChainWrites] using hA
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
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
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQ t 9 8 Q 8 (pure (root == pk, 0)) := by
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
    have hg := GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
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
    exact GoodQ.steps' hu.steps (GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
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
  have hpc : t.pc = pcOf (39970 + 128 * mkSh 0 1 (route index 0).1) := by
    rw [ht.pc]
    congr 1
    simp [mkFin, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl,
      show mkOff 0 1 6 = 33 from rfl, BC.mkShp, mkShp]
    omega
  refine ⟨⟨mkSh 0 1 (route index 0).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
  · rw [hpc]; rfl
  · intro p hp
    simp only [cmpK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg]
      congr 1
      exact (mkDst_chunk _).symm
  · change DigAt t (9472 + 48 * (mkSh 0 1 (route index 0).1 / 32 % 2)) root
    rw [mkDst_chunk]
    exact ht.root
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
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput route coreDigit dataDigits)
open Nonbinary (NCtx)
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem chainsCost_whole (c : NCtx) : c.chainsCost 0 54 = NCtx.totalCost c.dig := by
  unfold NCtx.chainsCost NCtx.totalCost
  rw [← List.range_eq_range']
theorem chainsCost_mono (c : NCtx) (m : Nat) (hm : m ≤ 54) : c.chainsCost 0 m ≤ c.chainsCost 0 54 := by
  have := Nonbinary.NCtx.chainsCost_add' c 0 m (54-m)
  rw [show m+(54-m)=54 by omega] at this
  omega
theorem s8v_top (c : NCtx) : c.s8v 17=BitVec.ofNat 64 (((List.range 54).map c.dig).sum)-144#64 := rfl
theorem s8v_zero_iff (c : NCtx) (hds : c.DigitsOk) :
    c.s8v 17=0 ↔ ((List.range 54).map c.dig).sum=144 := by
  have hb : ((List.range 54).map c.dig).sum ≤ 54*7 := by
    have : ∀ l : List Nat, (∀ i ∈ l, i<54) → (l.map c.dig).sum ≤ 7*l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons i l ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        have h1 := hds i (hl i (by simp))
        have h2 := NCtx.topMax_bounds i
        have h3 := ih (fun j hj => hl j (by simp [hj]))
        omega
    simpa using this (List.range 54) (fun i hi => List.mem_range.mp hi)
  rw [s8v_top]
  constructor
  · intro h
    have h' : BitVec.ofNat 64 (((List.range 54).map c.dig).sum)=144#64 := by
      have := congrArg (· + 144#64) h
      simpa using this
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]; rfl
theorem top_after_hash (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (t : MachineState) (hpre : BC.EncPre w pk index 0 c t) (Q : Prop) (hQ : Q) (q : Query) (hq : EncQ 0 q)
    (a : BitVec 256) :
    GoodQP (fun hash => hash q = a ∧ HashOk hash) (writeHash t a) 2373 2626 Q 1320
      (ccM (ClaudeWCT.W9.T3M.topLayerP w index (a.extractLsb' 0 128)) (kFin pk)) := by
  set v := a.extractLsb' 0 128 with hvdef
  obtain ⟨s0, st0, he⟩ := topTransition w pk index c hc t hpre a
  set L := nctxOf w index v (trPc 0 c) with hLdef
  have hLok : L.ok := nctx_ok w index v c hidx
  have hkn : ∀ p ∈ L.known, s0.getReg p.1 = p.2 := nctx_known w pk index c t s0 a hpre he
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have hDs0 : DataOK s0 := by
    have ha := topRowA_mem c hc'
    have hal : 13696 ≤ topRowA c ∧ topRowA c ≤ 13952 ∧ topRowA c % 16 = 0 := by
      simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
    obtain ⟨d, h12, hd⟩ := hpre.dst (by decide +kernel)
    change d = topRowA c ∨ d = topRowA c + 48 at hd
    exact (Glob_writeHash hpre.glob a d h12
      (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))).2.2.2.2.2.congr
      (fun A _ hA => he.frame.get (by omega) (by simp))
  have hO := nctx_orig w index v (trPc 0 c) s0 (topEntry_orig w pk index c hc t s0 a hpre he) hDs0
  have hf : L.Fit (T3.topFlip v) := nctx_fit w index v (trPc 0 c)
  have hds := L.fit_digits hf
  have hEnc : NCtx.Encoded (T3.topFlip v) s0 := topEntry_encoded he
  have hcc : L.chainsCost 0 54 ≤ 2254 := by rw [chainsCost_whole]; exact NCtx.total_any _ hds
  have hdig : ∀ i, L.dig i = coreDigit 0 v i := fun i => rfl
  have htail := Nonbinary.flip_tail v
  have hrank : ∀ j, Search.topRank (T3.topFlip v) j = T3.topCode v / 2 ^ (7 * j) % 128 := fun j => rfl
  cases hdec : T3.decode 0 v with
  | some ds =>
    obtain ⟨-, hrv, hsum, rfl⟩ := ClaudeWCT.WCT9.decode_top_some hdec
    have hval : ∀ j, j < 17 → Search.topRank (T3.topFlip v) j < 125 := by
      intro j hj
      unfold T3.topRanksValid at hrv
      have := List.all_eq_true.mp hrv j (List.mem_range.mpr hj)
      rw [hrank]
      simpa using this
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode w index hdec, ccM_map, layerP_eq, ccM_bind, chainsP_top_eq,
      ← nctx_prefix_eq w index v (trPc 0 c) 54 (le_refl _)]
    have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hval 0 (by decide +kernel))
    have hs8 : L.s8v 17 = 0 := by
      rw [s8v_zero_iff L hds, show L.dig = coreDigit 0 v from funext hdig]
      have : (dataDigits 0 v).sum = 144 := hsum
      simpa [dataDigits, T3.dataCount] using this
    have body : GoodQ (writeHash t a) 2373 2626 Q (1329 - T3.topCredit v)
        (ccM ((List.range' 0 54).foldlM L.chainF [])
          (fun ends => ccM (T3.leafHash 0 (route index 0).2 (route index 0).1 ends >>= merkleP w index 0)
            (fun r => kFin pk (some r)))) := by
      have H := L.top_full hLok hds hkn hO hEnc hf hval
        (fun ends => ccM (T3.leafHash 0 (route index 0).2 (route index 0).1 ends >>= merkleP w index 0)
          (fun r => kFin pk (some r))) 91 284 284 Q
        (fun ends z hz => by
          obtain ⟨hr, hfz, hlen, hend, hpc, h15, h24⟩ := hz
          have hregs : RegsExcept s0 z topChainRegs := by
            intro r hrn
            apply hr r
            · intro hh; exact hrn ((by decide +kernel : chainRegs ⊆ topChainRegs) hh)
            · intro hh; subst r; exact hrn (by decide +kernel)
            · intro hh; subst r; exact hrn (by decide +kernel)
          have hframe : Frame s0 z topChainWrites := top_chain_frame L rfl hfz
          have hready := topLeafReady_of w pk index c hc t s0 z a ends hpre he hpc hregs hframe h15
            (by rw [h24, hs8]) hlen (fun j hj => by have h := hend j (by omega); exact h)
          obtain ⟨u, st, hu⟩ := leafT_step w pk index c hc hidx ends z hready
          have hm := merkle_good w pk index 0 ends u hidx hu (fun r => kFin pk (some r)) 9 8 8 Q
            (fun root t ht => by
              rw [kFin_some]
              exact cmp_good pk root t (mkEnd_top w pk index u root t (by simpa [MkStop] using ht)) Q hQ)
          have hmP : merkleP w index 0 = merklePrefix w index 0 := by
            funext x; rw [merkleP_eq]; rfl
          rw [hmP]
          have := GoodQ.steps st hm
          refine this.mono ?_ ?_ (fun h => ⟨h, ?_⟩) <;> simp [mkFuel_vals, mkCyc_vals])
        s0 hg0
      have H2 := GoodQ.steps st0 H
      have hcr := NCtx.accepted_total_credit hdec
      rw [chainsCost_whole] at H2 hcc
      have hdigs : L.dig = coreDigit 0 v := funext hdig
      rw [hdigs] at H2 hcc
      refine H2.mono ?_ ?_ (fun h => ⟨h, ?_⟩) <;> omega
    by_cases hcr : 9 ≤ T3.topCredit v
    · exact (body.mono (le_refl _) (le_refl _) (fun h => ⟨h, by omega⟩)).toP.pre_mono (fun _ h => h.2)
    · refine GoodQP.of_false body ?_
      rintro hash ⟨hea, hok⟩
      have h7 := hok 0 q hq (dataDigits 0 v) (by rw [hea]; exact hdec)
      rw [ClaudeWCT.WCT9.wordCredit_top hdec] at h7
      exact hcr h7
  | none =>
    refine GoodQP.pre_mono (P := HashOk) ?_ (fun _ h => h.2)
    refine Nonbinary.NCtx.goodQ_vacuous (A := 0) ?_ Q 1320
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode_none w index hdec, ccM_map]
    simp only [kFin_none]
    have reject_from : ∀ z : MachineState, z.pc = pcOf 129638 → GoodQ z 4 4 False 0 (pure (false, 0)) := by
      intro z hz
      obtain ⟨z', st, fz, h5, h10⟩ := Verify.Nonbinary.reject_halt z hz
      exact (GoodQ.steps st (GoodQ.reject (Q := False) (A := 0) fz h5 h10)).mono (by omega) (by omega)
        (fun h => h.elim)
    have fault0 : 125 ≤ Search.topRank (T3.topFlip v) 0 → GoodQ s0 1 0 False 0 (pure (false, 0)) := by
      intro h0
      apply Nonbinary.NCtx.goodQ_fault
      apply Nonbinary.NCtx.fetch_fault
      rw [he.pc, Nonbinary.prefixTarget_flip, ← hvdef]
      have hr : Search.topRank (T3.topFlip v) 0 = (T3.topFlip v).toNat % 128 := by unfold Search.topRank; simp
      rw [hr] at h0
      simp only [BitVec.toNat_ofNat]
      have hm := Nat.mod_lt (T3.topFlip v).toNat (show 0 < 128 by decide +kernel)
      omega
    have hv' : v.toNat < 2 ^ 128 := v.isLt
    · by_cases hall : ∀ j, j < 17 → Search.topRank (T3.topFlip v) j < 125
      ·
        have hs : (dataDigits 0 v).sum ≠ 144 := by
          intro hs
          have hr : T3.topRanksValid v = true := by
            unfold T3.topRanksValid
            apply List.all_eq_true.mpr
            intro j hj
            have := hall j (List.mem_range.mp hj)
            rw [hrank] at this
            simpa using this
          rw [ClaudeWCT.WCT9.decode_top_of (by simpa [T3.encodedBits] using hv') hr hs] at hdec
          cases hdec
        rw [topRejectChains_eq w index v 54 (le_refl _) (TopSource.topRejectLength_sum v hall),
          ← nctx_prefix_eq w index v (trPc 0 c) 54 (le_refl _)]
        have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hall 0 (by decide +kernel))
        have H := L.top_full hLok hds hkn hO hEnc hf hall (fun _ => pure (false, 0)) 14 14 0 False
          (fun ends z hz => by
            obtain ⟨hr, -, -, -, hpc, h15, h24⟩ := hz
            have hne : z.getReg .x24 ≠ 0 := by
              rw [h24]; intro h0; apply hs
              have := (s8v_zero_iff L hds).mp h0
              rw [show L.dig = coreDigit 0 v from funext hdig] at this
              simpa [dataDigits, T3.dataCount] using this
            have hregs : RegsExcept s0 z topChainRegs := by
              intro r hrn
              apply hr r
              · intro hh; exact hrn ((by decide +kernel : chainRegs ⊆ topChainRegs) hh)
              · intro hh; subst r; exact hrn (by decide +kernel)
              · intro hh; subst r; exact hrn (by decide +kernel)
            obtain ⟨u, st, fu, h5, h10⟩ :=
              leafT_reject z hpc (topLeafK_of w pk index c t s0 z a hpre he hregs h15) hne
            exact (GoodQ.steps st (GoodQ.reject (Q := False) (A := 0) fu h5 h10)).mono (by omega) (by omega)
              (fun h => h.elim))
          s0 hg0
        exact (GoodQ.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)
      ·
        have hex : ∃ j, j < 17 ∧ 125 ≤ Search.topRank (T3.topFlip v) j := by
          by_contra hn
          apply hall
          intro j hj
          by_contra hb
          exact hn ⟨j, hj, by omega⟩
        classical
        let j := Nat.find hex
        have hjs : j < 17 ∧ 125 ≤ Search.topRank (T3.topFlip v) j := Nat.find_spec hex
        have hjmin : ∀ k, k < j → Search.topRank (T3.topFlip v) k < 125 := by
          intro k hk
          have := Nat.find_min hex hk
          by_contra hb
          exact this ⟨by omega, by omega⟩
        by_cases hj0 : j = 0
        · have h0 : 125 ≤ Search.topRank (T3.topFlip v) 0 := by rw [← hj0]; exact hjs.2
          rw [topRejectChains_eq w index v 0 (by decide +kernel)
            (by rw [TopSource.topRejectLength_bad v j (by omega) hjmin hjs.2, hj0])]
          simp only [List.range'_zero, List.mapM_nil, ccM_pure]
          exact (GoodQ.steps st0 (fault0 h0)).mono (by omega) (by omega) (fun h => h.elim)
        · rw [topRejectChains_eq w index v (3 * j) (by omega)
            (TopSource.topRejectLength_bad v j (by omega) hjmin hjs.2),
            ← nctx_prefix_eq w index v (trPc 0 c) (3 * j) (by omega)]
          have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hjmin 0 (by omega))
          have H := L.top_bad_group hLok hds hkn hO hEnc hf j (by omega) (by omega) hjmin hjs.2
            (fun _ => pure (false, 0)) (fun _ => rfl) False 0 s0 hg0
          have hm := chainsCost_mono L (3 * j) (by omega)
          have hov := Nonbinary.NCtx.ov_le j (by omega)
          exact (GoodQ.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route leafHash)
open ClaudeWCT.WCT9 (LayerMsg)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
def topFuel : Nat := 5 + 1 + 2373
def topCyc : Nat := 5 + 8 + 2626
def topCycA : Nat := 5 + 8 + 1320
theorem top_layer_good (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q)
    (M : LayerMsg) (s : MachineState) (hs : LayerIn w pk index 0 M s) :
    GoodQ s topFuel topCyc Q topCycA (ccM (BC.layerLoop w index 1 M) (kFin pk)) := by
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
    have hblk := BC.encoding_blocks w index 0 (route index 0).2 (route index 0).1 M
    have hq := encQ_layer 0 (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcCtr w index 0)
      (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w)
    have := GoodQP.shortHash_bind_pre (f := ClaudeWCT.W9.T3M.topLayerP w index) hf h5 hv hin
      (fun a => top_after_hash w pk index c hc hidx t hpre Q hQ _ hq a)
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by simp [topFuel]) (by simp [topCyc]) (by simp [topCycA])).toGoodQ
def lCyc : Nat → Nat
  | 0 => 8
  | 1 => topCyc
  | n + 2 => layerCost (n + 1) 0 + mkCyc (n + 1) + lCyc (n + 1)
def lCycA : Nat → Nat
  | 0 => 8
  | 1 => topCycA
  | n + 2 => layerCostA (n + 1) + mkCyc (n + 1) + lCycA (n + 1)
def lFuel : Nat → Nat
  | 0 => 9
  | 1 => topFuel
  | n + 2 => layerFuel (n + 1) + mkFuel (n + 1) + lFuel (n + 1)
theorem lCyc_4 : lCyc 4 = 6718 := by decide +kernel
theorem lCycA_4 : lCycA 4 = 5398 := by decide +kernel
theorem lFuel_4 : lFuel 4 = 7759 := by decide +kernel
theorem layers_good (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ msg s, RestIn w pk index n msg s →
      GoodQ s (lFuel n) (lCyc n) Q (lCycA n) (ccM (BC.layerLoop w index n msg) (kFin pk)) := by
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
      exact top_layer_good w pk index hidx Q hQ msg s hs'
    have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < 4 by omega)]
    have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h => hn0 (by rw [← hv, h]; rfl)
    rw [layerLoop_succ w index n (by omega) hn0 msg]
    have hg := layer_good_low w pk index (Fin.ofNat 4 n) hlay msg s (by rwa [hv])
      (fun ends => leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
        fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n)
      (kFin pk) (kFin_none pk) (lFuel n + mkFuel n) (lCyc n + mkCyc n) (lCycA n + mkCyc n) Q
      (fun ends u hu => by
        have hm := merkle_good w pk index (Fin.ofNat 4 n) ends u hidx hu
          (fun v => ccM (BC.layerLoop w index n (mkMessage w index (Fin.ofNat 4 n) v)) (kFin pk))
          (lFuel n) (lCyc n) (lCycA n) Q
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
theorem after_good (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (Q : Prop) (hQ : Q) (a : HashOutput) (root : Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ root u) :
    GoodQ u 8050 8050 Q 5398 (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some root)) Kb) := by
  have hidx : ClaudeWCT.WCT9.digestIndex a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ root u hidx h.glob h.idx h.pc h.root h.wit h.a2 h.s10 h.heapOne h.heapTwo h.heapSeven h.heapThree h.heapFour h.heapFive h.coordStep h.topBase h.top h.top8
  have hg := layers_good w pk _ hidx Q hQ 4 le_rfl (.forest root) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some root)) Kb =
      ccM (BC.layerLoop w (ClaudeWCT.WCT9.digestIndex a) 4 (.forest root)) (kFin pk) := by
    unfold afterFts
    rw [ccM_bind]
    rfl
  rw [e]
  rw [lFuel_4, lCyc_4, lCycA_4] at hg
  exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
theorem after_good_budget : AfterGoodBudget 5398 :=
  fun pk w Q hQ a root u h => after_good pk w Q hQ a root u h
end SigGolfCandidate.T3M
end
