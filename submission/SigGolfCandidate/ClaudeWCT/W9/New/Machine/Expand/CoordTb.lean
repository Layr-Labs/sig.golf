import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineCheck0
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineCheck1
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineCheck2
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck0
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.JTCheck1
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Drv
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.FtsSrc
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Region

section
namespace ClaudeWCT.W9.Machine.Expand
theorem routineOK_all (x : Nat) (hx : x < 563) : routineOK x = true := by
  have key : ∀ lo n, (List.range' lo n).all routineOK = true → lo ≤ x → x < lo + n → routineOK x = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h x (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : x < 64; · exact key 0 64 routineOK_0 (by omega) h0
  by_cases h64 : x < 128; · exact key 64 64 routineOK_64 (by omega) h64
  by_cases h128 : x < 192; · exact key 128 64 routineOK_128 (by omega) h128
  by_cases h192 : x < 256; · exact key 192 64 routineOK_192 (by omega) h192
  by_cases h256 : x < 320; · exact key 256 64 routineOK_256 (by omega) h256
  by_cases h320 : x < 384; · exact key 320 64 routineOK_320 (by omega) h320
  by_cases h384 : x < 448; · exact key 384 64 routineOK_384 (by omega) h384
  by_cases h448 : x < 512; · exact key 448 64 routineOK_448 (by omega) h448
  exact key 512 51 routineOK_512 (by omega) (by omega)
theorem jtOK_all (x : Nat) (hx : x < 563) : jtOK x = true := by
  have key : ∀ lo n, (List.range' lo n).all jtOK = true → lo ≤ x → x < lo + n → jtOK x = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h x (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : x < 64; · exact key 0 64 jtOK_0 (by omega) h0
  by_cases h64 : x < 128; · exact key 64 64 jtOK_64 (by omega) h64
  by_cases h128 : x < 192; · exact key 128 64 jtOK_128 (by omega) h128
  by_cases h192 : x < 256; · exact key 192 64 jtOK_192 (by omega) h192
  by_cases h256 : x < 320; · exact key 256 64 jtOK_256 (by omega) h256
  by_cases h320 : x < 384; · exact key 320 64 jtOK_320 (by omega) h320
  by_cases h384 : x < 448; · exact key 384 64 jtOK_384 (by omega) h384
  by_cases h448 : x < 512; · exact key 448 64 jtOK_448 (by omega) h448
  exact key 512 51 jtOK_512 (by omega) (by omega)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput M)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem jt_step {im : Image} (hc : NewCodeAt im) (f : Nat) (hf : f < 563) (s : MachineState)
    (hpc : s.pc = pcOf (jt0 + f)) :
    Steps im s 1 1 (s.setPC (pcOf (jtTarget f))) := by
  have h := jtOK_all f hf
  unfold jtOK at h
  split at h
  · rename_i w hw
    have hj : jalTo w (jt0 + f) = some (jtTarget f) := by simpa using h
    obtain ⟨imm, hd, hoff⟩ := jalTo_sound hj
    exact jal_x0_step (codeAt_one hc hw) hd hoff s hpc
  · cases h
structure FtsIn (sig : WCT9.Signature) (N : HashOutput) (sF : MachineState) : Prop where
  out : OutAt sF 0x60 N
  adm : WCT9.admissible N = true
  placed : Placed N sig sF
  bank : HdrBankOK sF
structure DrvInv (sig : WCT9.Signature) (N : HashOutput) (sF : MachineState) (k : Nat)
    (pairs : List (Digest × Digest)) (t : MachineState) : Prop where
  pc : t.pc = pcOf (base + dOff k)
  regs : DRegs (WCT9.digestIndex N) t
  x8 : t.getReg .x8 = BitVec.ofNat 64 (regBase (k - 1))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (k - 1))
  x15 : t.getReg .x15 = BitVec.ofNat 64 (WCT9.digestIndex N * 2 ^ 27 + 65536 * (k - 1))
  x16 : 0 < k → t.getReg .x16 = N.extractLsb' (64 * dWord (k - 1)) 64
  len : pairs.length = k
  pairs : ∀ k', k' < k → DigAt t (pslot k') (pairs.getD k' (0, 0)).1 ∧
    DigAt t (pslot k' + 16) (pairs.getD k' (0, 0)).2
  frame : Frame sF t (fun A => (0x840 ≤ A ∧ A < regBase k) ∨ (0x420 ≤ A ∧ A < 0x430 + 32 * k))
def coordCost : Nat := 420
theorem region_facts {sig : WCT9.Signature} {N : HashOutput} {sF t : MachineState} (hin : FtsIn sig N sF)
    (k : Nat) (hk : k < 9)
    (hfr : ∀ o, o < 1024 → t.getMem (BitVec.ofNat 64 (regBase k + o)) = sF.getMem (BitVec.ofNat 64 (regBase k + o))) :
    (∀ i (h : i < 6), DigAt t (regBase k + offC i + 48) ((sig.openings ⟨k, hk⟩).values ⟨i, h⟩)) ∧
    (∀ i (h : i < 6), DigAt t (regBase k + slotC i) ((sig.openings ⟨k, hk⟩).values ⟨i, h⟩)) ∧
    (∀ i, i < 6 → PadsZ (regBase k) i t) ∧
    DigAt t (regBase k + 848) 0 ∧
    (∀ l, l < 7 → DigAt t (regBase k + Merkle.padO l) 0) ∧
    (∀ l (h : l < 7), DigAt t (regBase k + Merkle.sibO l (WCT9.child N ⟨k, hk⟩).val)
      ((sig.openings ⟨k, hk⟩).path ⟨l, h⟩)) := by
  have tr : ∀ o d, o % 8 = 0 → o + 16 ≤ 1024 → DigAt sF (regBase k + o) d → DigAt t (regBase k + o) d :=
    fun o d h8 h16 hd => ⟨(hfr o (by omega)).trans hd.1, by
      rw [show regBase k + o + 8 = regBase k + (o + 8) by omega, hfr (o + 8) (by omega),
        ← show regBase k + o + 8 = regBase k + (o + 8) by omega]; exact hd.2⟩
  have pd := fun o (h8 : o % 8 = 0) (h16 : o + 16 ≤ 1024) d hw => placed_digAt hin.placed k hk o h8 h16 d hw
  refine ⟨fun i h => ?_, fun i h => ?_, fun i h => ?_,
    tr _ _ (by omega) (by omega) (pd 848 (by omega) (by omega) 0 (by rw [win_leafPad, zeros16])),
    fun l h => ?_, fun l h => ?_⟩
  · have hb := offC_bounds i h
    rw [Nat.add_assoc]
    exact tr _ _ (by omega) (by omega) (pd _ (by omega) (by omega) _ (win_chainVal _ _ ⟨i, h⟩))
  · have hb := slotC_bounds i h
    exact tr _ _ (by omega) (by omega) (pd _ (by omega) (by omega) _ (win_leafSlot _ _ ⟨i, h⟩))
  · have hb := offC_bounds i h
    have z0 := tr _ _ (by omega) (by omega) (pd (offC i + 0) (by omega) (by omega) 0
      (by rw [win_chainPad _ _ i h 0 (Or.inl rfl), zeros16]))
    have z16 := tr _ _ (by omega) (by omega) (pd (offC i + 16) (by omega) (by omega) 0
      (by rw [win_chainPad _ _ i h 16 (Or.inr (Or.inl rfl)), zeros16]))
    have z32 := tr _ _ (by omega) (by omega) (pd (offC i + 32) (by omega) (by omega) 0
      (by rw [win_chainPad _ _ i h 32 (Or.inr (Or.inr rfl)), zeros16]))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := z0.1; simp only [Nat.add_zero] at this; exact this.trans rfl
    · have := z0.2; simp only [Nat.add_zero] at this; exact this.trans rfl
    · have := z32.1; rw [← Nat.add_assoc] at this; exact this.trans rfl
    · have := z32.2; rw [show regBase k + (offC i + 32) + 8 = regBase k + offC i + 40 by omega] at this
      exact this.trans rfl
    · have := z16.2; rw [show regBase k + (offC i + 16) + 8 = regBase k + offC i + 24 by omega] at this
      exact this.trans rfl
  · have := tr _ _ (by unfold Merkle.padO Merkle.blkO; omega) (by unfold Merkle.padO Merkle.blkO; omega)
      (pd (Merkle.padO l) (by unfold Merkle.padO Merkle.blkO; omega) (by unfold Merkle.padO Merkle.blkO; omega) 0
        (by unfold Merkle.padO Merkle.blkO; rw [win_mpad _ _ ⟨l, h⟩, zeros16]))
    exact this
  · have hbit := bitAt_lt (WCT9.child N ⟨k, hk⟩).val l
    exact tr _ _ (by unfold Merkle.sibO Merkle.blkO; omega) (by unfold Merkle.sibO Merkle.blkO; omega)
      (pd _ (by unfold Merkle.sibO Merkle.blkO; omega) (by unfold Merkle.sibO Merkle.blkO; omega) _
        (by unfold Merkle.sibO Merkle.blkO Merkle.bitAt; exact win_sib _ _ ⟨l, h⟩))
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput M)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000
theorem field_lt_of_adm (N : HashOutput) (k : Nat) (hk : k < 9) (hadm : WCT9.admissible N = true) :
    WCT9.field N ⟨k, hk⟩ < 563 := by
  have := ((admissible_iff N).mp hadm).2 k (Nat.zero_le _) hk
  exact this
theorem codewordL_le4 (r : Nat) (hr : r < 563) (t : Nat) (ht : t < 6) : (codewordL r).getD t 0 ≤ 4 := by
  have := WCT9.wordDigit_le_four ⟨r, hr⟩ ⟨t, ht⟩
  rwa [codewordL_eq] at this
theorem regBase_bounds (k : Nat) (hk : k < 9) : regBase k % 64 = 0 ∧ 0x840 ≤ regBase k ∧ regBase k + 1024 ≤ 0x2c40 := by
  unfold regBase; omega
theorem chainsWr_range {B : Nat} {z : List Nat} {A : Nat} (h : chainsWr B z 6 A) : B + 464 ≤ A ∧ A < B + 1024 := by
  obtain ⟨t', ht', _, hw⟩ := h
  unfold chainWr offC slotC at hw
  split_ifs at hw <;> omega
theorem pslot_bounds (k : Nat) (hk : k < 9) : pslot k % 16 = 0 ∧ 0x420 ≤ pslot k ∧ pslot k + 48 = 0x430 + 32 * (k + 1) ∧
    pslot k + 48 ≤ 0x550 := by
  unfold pslot; omega
theorem hdr0_index (tag k index : Nat) (hidx : index < 2 ^ 31) : hdr0 tag k index 0 = hdr0 tag k 0 0 := by
  have h0 : index / 2 ^ 32 = 0 := Nat.div_eq_of_lt (by omega)
  simp only [hdr0, h0, Nat.zero_div]
theorem hdr0_node_lt (k : Nat) : hdr0 3 (4 + k) 0 0 < 2 ^ 32 := by
  unfold hdr0
  have := Nat.mod_lt (4 + k) (show 0 < 256 by decide)
  simp only [Nat.zero_div, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
  omega
theorem leafHdr_digAt {w : MachineState} {B k index j : Nat} (hk : k < 9) (hidx : index < 2 ^ 31) (hj : j < 128)
    (h0 : w.getMem (BitVec.ofNat 64 (B + 832)) = BitVec.ofNat 64 (qQ k index j + 1537))
    (h1 : w.getMem (BitVec.ofNat 64 (B + 840)) = 0) :
    DigAt w (B + 832) (ClaudeWCT.WCT9.ftsLeafHeader index k j) := by
  unfold ClaudeWCT.WCT9.ftsLeafHeader
  constructor
  · rw [h0, SigGolfCandidate.T3.append64_low]
    unfold ClaudeWCT.WCT9.ftsLeafLow qQ
    congr 1
    rw [Nat.mod_eq_of_lt (show k < 16 by omega), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hidx]
    ring
  · rw [show B + 832 + 8 = B + 840 by omega, h1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, SigGolfCandidate.T3.append64_toNat]
    have := (BitVec.ofNat 64 (ClaudeWCT.WCT9.ftsLeafLow index k j)).isLt
    have h0' : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0']
    omega
theorem pc_child (j : Nat) : (BitVec.ofNat 64 (17572 + 256 * j)) &&& 18446744073709551614#64 = pcOf (cbE j) := by
  have : BitVec.ofNat 64 (17572 + 256 * j) = pcOf (cbE j) := by
    unfold pcOf cbE cb0; congr 1; ring
  rw [this, not1_eq, pcOf_and_not1]
theorem jtTarget_field (N : HashOutput) (c : WCT9.Coord) (h : WCT9.field N c < 563) :
    jtTarget (WCT9.field N c) = routineEntry.getD (WCT9.rank N c).val 0 := by
  unfold jtTarget
  rw [WCT9.rank_val, Nat.mod_eq_of_lt h]
def coordRegs : List Reg :=
  [.x1, .x3, .x4, .x8, .x9, .x10, .x11, .x12, .x14, .x15, .x16, .x23, .x25, .x27, .x28, .x31]
theorem coord_tb {im : Image} (hc : NewCodeAt im) {sk : BitVec 256} {sig : WCT9.Signature} {N : HashOutput}
    {sF : MachineState} (hin : FtsIn sig N sF) (k : Nat) (hk : k < 9) (pairs : List (Digest × Digest))
    (t : MachineState) (hI : DrvInv sig N sF k pairs t) :
    TBSim im sk t coordCost (WCT9.recoverCoordinate sig (WCT9.digestIndex N) N ⟨k, hk⟩)
      (fun pr u => DrvInv sig N sF (k + 1) (pairs ++ [pr]) u) := by
  have hidx : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
  have hj : (WCT9.child N ⟨k, hk⟩).val < 128 := (WCT9.child N ⟨k, hk⟩).isLt
  have hf : WCT9.field N ⟨k, hk⟩ < 563 := field_lt_of_adm N k hk hin.adm
  have hr : (WCT9.rank N ⟨k, hk⟩).val < 563 := (WCT9.rank N ⟨k, hk⟩).isLt
  have hjt : jtTarget (WCT9.field N ⟨k, hk⟩) = routineEntry.getD (WCT9.rank N ⟨k, hk⟩).val 0 :=
    jtTarget_field N ⟨k, hk⟩ hf
  have hrb := regBase_bounds k hk
  have hps := pslot_bounds k hk
  set index := WCT9.digestIndex N with hindex
  set j := (WCT9.child N ⟨k, hk⟩).val with hjdef
  have hlow : ∀ A, A < 0x420 → t.getMem (BitVec.ofNat 64 A) = sF.getMem (BitVec.ofNat 64 A) :=
    fun A hA => hI.frame A (by omega) (by omega)
  have hregk : ∀ o, o < 1024 → t.getMem (BitVec.ofNat 64 (regBase k + o)) =
      sF.getMem (BitVec.ofNat 64 (regBase k + o)) :=
    fun o ho => hI.frame _ (by omega) (by omega)
  have hhigh : ∀ A, 0x3000 ≤ A → A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = sF.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2 => hI.frame A h2 (by unfold regBase at hrb ⊢; omega)
  have hout : OutAt t 0x60 N := fun i hi => (hlow _ (by omega)).trans (hin.out i hi)
  obtain ⟨t1, s1, p1, x1_1, x8_1, x28_1, x4_1, x23_1, x27_1, x15_1, x31_1, x16_1, x9_1, keep1, f1⟩ :=
    disp_spec hc k hk N index hidx t hI.pc hI.regs.x22 hI.regs.x29 hI.regs.x24 hI.regs.x2 hI.regs.x6 hI.x15
      hI.x16 hI.x8 hI.x28 hout
  have s2 := jt_step hc _ hf t1 p1
  rw [hjt] at s2
  set t2 := t1.setPC (pcOf (routineEntry.getD (WCT9.rank N ⟨k, hk⟩).val 0)) with ht2
  have m21 : ∀ A, t2.getMem A = t.getMem A := fun A => by
    rw [show t2.getMem A = t1.getMem A from rfl]
    have := f1 A.toNat A.isLt (fun h => h)
    simpa using this
  have r21 : ∀ r, t2.getReg r = t1.getReg r := fun r => rfl
  have k21 : ∀ r, r ∉ coordRegs → t2.getReg r = t.getReg r := by
    intro r hr
    simp only [coordRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h3, h4, h8, h9, _, _, _, h14, h15, h16, h23, _, h27, h28, h31⟩ := hr
    rw [r21, keep1 r h1 h3 h4 h8 h9 h14 h15 h16 h23 h27 h28 h31]
  have hro := routineOK_all _ hr
  unfold routineOK at hro
  obtain ⟨c, hw, hc300⟩ : ∃ c, walk (codewordL ((WCT9.rank N ⟨k, hk⟩).val)) 64 0
      (routineEntry.getD ((WCT9.rank N ⟨k, hk⟩).val) 0) = some c ∧ c ≤ routineCost := by
    revert hro
    cases walk (codewordL ((WCT9.rank N ⟨k, hk⟩).val)) 64 0 (routineEntry.getD ((WCT9.rank N ⟨k, hk⟩).val) 0) with
    | none => simp
    | some c => intro h; exact ⟨c, rfl, by simpa using h⟩
  have hreg2 : ∀ o, o < 1024 → t2.getMem (BitVec.ofNat 64 (regBase k + o)) =
      sF.getMem (BitVec.ofNat 64 (regBase k + o)) := fun o ho => (m21 _).trans (hregk o ho)
  obtain ⟨rv, rl, rp, rpad, rmp, rs⟩ := region_facts hin k hk hreg2
  have hpre : RPre (regBase k) (HB0 + 2048 + 512 * k) k index j (codewordL ((WCT9.rank N ⟨k, hk⟩).val))
      (fun t => if h : t < 6 then (sig.openings ⟨k, hk⟩).values ⟨t, h⟩ else 0) t2 := by
    refine ⟨⟨by omega, by omega, by unfold HB0; omega, by unfold HB0; omega, by unfold HB0; omega⟩,
      by unfold HB0; omega, hk, hidx, hj, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      fun t' ht => rp t' ht, fun t' ht => ?_, fun t' ht _ => ?_, fun t' ht => codewordL_le4 _ hr t' ht⟩
    · rw [r21, x8_1]
    · rw [r21, x28_1]
    · rw [r21, x4_1]
    · rw [r21, x31_1]; rfl
    · rw [k21 _ (by decide)]; exact hI.regs.x7
    · rw [k21 _ (by decide)]; exact hI.regs.heaps 2 (by decide) (by decide)
    · rw [k21 _ (by decide)]; exact hI.regs.heaps 3 (by decide) (by decide)
    · rw [k21 _ (by decide)]; exact hI.regs.x5
    · rw [r21, keep1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.regs.x11
    · simp only [dif_pos ht]; exact rv t' ht
    · simp only [dif_pos ht]; exact rl t' ht
  have hW := walk_tb (sk := sk) hc hpre 64 0 _ c [] t2 hw (by omega) rfl
    ⟨rfl, hpre.regs, keepC.refl _, Frame.refl _ _, fun t' ht' => absurd ht' (by omega)⟩
  rw [recoverCoordinate_split]
  refine (TBSim.steps (s1.trans s2) (TBSim.bind (W₂ := 99) hW (fun ends w hw' => ?_))).mono
    (by have := hc300; unfold routineCost at this; unfold coordCost dLen; split <;> omega) (fun _ _ h => h)
  simp only [List.nil_append] at hw'
  have hlen := hw'.len
  have hpath : ∀ l (h : l < 7), Merkle.finPath (sig.openings ⟨k, hk⟩).path l = (sig.openings ⟨k, hk⟩).path ⟨l, h⟩ :=
    fun l h => by simp [Merkle.finPath, h]
  rw [show (⟨k, hk⟩ : WCT9.Coord).val = k from rfl]
  have hprog : (WCT9.leafHash index k j ends >>=
        Merkle.sixLevels k index j (Merkle.finPath (sig.openings ⟨k, hk⟩).path)) >>=
        (fun top => pure (Merkle.pairOf j top ((sig.openings ⟨k, hk⟩).path 6))) =
      Merkle.childProgC k index j (Merkle.leafFields k index j ends) (Merkle.finPath (sig.openings ⟨k, hk⟩).path) := by
    rw [Merkle.childCanon k index j ends _ hlen]; rfl
  rw [hprog]
  have kw : ∀ r, r ∉ coordRegs → w.getReg r = t.getReg r := by
    intro r hr
    have hr' := hr
    simp only [coordRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨_, h3, _, _, _, h10, h11, h12, h14, _, _, _, h25, _, _, _⟩ := hr'
    rw [hw'.keep r h3 h10 h11 h12 h14 h25, k21 r hr]
  have wfr : ∀ o, o < 1024 → o + 8 ≤ 464 → w.getMem (BitVec.ofNat 64 (regBase k + o)) =
      t2.getMem (BitVec.ofNat 64 (regBase k + o)) := by
    intro o ho h464
    refine hw'.frame _ (by omega) ?_
    rintro (h | h | h)
    · have := chainsWr_range h; omega
    · omega
    · omega
  have hpreC : ChildPreE j (regBase k) k index (pslot k) (Merkle.leafFields k index j ends)
      (Merkle.finPath (sig.openings ⟨k, hk⟩).path) w := by
    refine ⟨?_, by omega, by unfold MEMORY_BYTES; omega, hps.1, by unfold pslot regBase; omega, by omega, by omega,
      ?_, ?_, hw'.a0, hw'.a1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hw'.pc, r21, x23_1, pc_child]
    · rw [kw _ (by decide)]; exact hI.regs.x5
    · rw [hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x8_1]
    · rw [hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x27_1]
    · intro h h2 h7
      have hh : Merkle.heapReg h = .x13 ∨ Merkle.heapReg h = .x19 ∨ Merkle.heapReg h = .x20 ∨
          Merkle.heapReg h = .x21 ∨ Merkle.heapReg h = .x26 ∨ Merkle.heapReg h = .x30 := by
        unfold Merkle.heapReg; split <;> simp
      rw [kw _ (by rcases hh with h | h | h | h | h | h <;> rw [h] <;> decide)]
      exact hI.regs.heaps h h2 h7
    · rw [hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x9_1]
    · intro i hi
      unfold Merkle.leafFields Merkle.leafO
      by_cases h0 : i = 0
      · subst h0; simp only [if_true, Nat.mul_zero, Nat.add_zero]
        have := hw'.ends 0 (by decide); rwa [show slotC 0 = 816 from rfl] at this
      · by_cases h1 : i = 1
        · subst h1; simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]
          exact leafHdr_digAt hk hidx hj hw'.h0 hw'.h1
        · by_cases h2 : i = 2
          · subst h2; simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false, if_true]
            have hnw : ∀ o, o < 16 → ¬ (chainsWr (regBase k) (codewordL (WCT9.rank N ⟨k, hk⟩).val) 6
                (regBase k + 848 + o) ∨ regBase k + 848 + o = regBase k + 832 ∨
                regBase k + 848 + o = regBase k + 840) := by
              rintro o ho (⟨t', ht', _, hc⟩ | h | h)
              · exact leafPad_free ht' o ho hc
              · omega
              · omega
            have e0 := hw'.frame (regBase k + 848) (by omega) (by simpa using hnw 0 (by omega))
            have e8 := hw'.frame (regBase k + 848 + 8) (by omega) (hnw 8 (by omega))
            rw [show regBase k + 816 + 16 * 2 = regBase k + 848 by omega]
            exact ⟨e0.trans rpad.1, e8.trans rpad.2⟩
          · simp only [h0, h1, h2, if_false]
            have := hw'.ends (i - 2) (by omega)
            rwa [show slotC (i - 2) = 816 + 16 * i by unfold slotC; split <;> omega, ← Nat.add_assoc] at this
    · intro l hl
      have hm := rmp l (by omega)
      have hb : Merkle.padO l + 16 ≤ 464 := by unfold Merkle.padO Merkle.blkO; omega
      exact ⟨(wfr _ (by omega) (by omega)).trans hm.1, by
        rw [Nat.add_assoc, wfr _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.2⟩
    · intro l hl
      have hm := rs l hl
      have hb : Merkle.sibO l j + 16 ≤ 464 := by
        unfold Merkle.sibO Merkle.blkO; have := bitAt_lt j l; omega
      rw [hpath l hl]
      exact ⟨(wfr _ (by omega) (by omega)).trans hm.1, by
        rw [Nat.add_assoc, wfr _ (by omega) (by omega), ← Nat.add_assoc]; exact hm.2⟩
  refine (child_tbE (sk := sk) hj hc hpreC).mono (le_refl _) (fun pr t3 hpost => ?_)
  have kall : ∀ r, r ∉ coordRegs → t3.getReg r = t.getReg r := by
    intro r hr
    have hr' := hr
    simp only [coordRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨_, h3, _, _, _, h10, h11, h12, h14, _, _, _, _, _, _, _⟩ := hr'
    rw [hpost.keep r h3 h10 h11 h12 h14, kw r hr]
  have kx : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → r ≠ .x25 →
      t3.getReg r = t1.getReg r := fun r a b c d e f => by
    rw [hpost.keep r a b c d e, hw'.keep r a b c d e f, r21]
  have F1 : Frame t t2 (fun _ => False) := fun A _ _ => m21 _
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun _ => ?_, by simp [hI.len], fun k' hk' => ?_, ?_⟩
  · rw [hpost.pc, hw'.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, x1_1,
      pcOf_and_not1, dOff_succ k hk, Nat.add_assoc]
  · rw [kall _ (by decide)]; exact hI.regs.x5
  · rw [kall _ (by decide)]; exact hI.regs.x22
  · rw [kall _ (by decide)]; exact hI.regs.x7
  · rw [kall _ (by decide)]; exact hI.regs.x6
  · intro h h2 h7
    have hh : Merkle.heapReg h = .x13 ∨ Merkle.heapReg h = .x19 ∨ Merkle.heapReg h = .x20 ∨
        Merkle.heapReg h = .x21 ∨ Merkle.heapReg h = .x26 ∨ Merkle.heapReg h = .x30 := by
      unfold Merkle.heapReg; split <;> simp
    rw [kall _ (by rcases hh with h | h | h | h | h | h <;> rw [h] <;> decide)]
    exact hI.regs.heaps h h2 h7
  · rw [kall _ (by decide)]; exact hI.regs.x17
  · rw [kall _ (by decide)]; exact hI.regs.x29
  · rw [kall _ (by decide)]; exact hI.regs.x24
  · rw [kall _ (by decide)]; exact hI.regs.x2
  · exact hpost.a1
  · rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x8_1, Nat.add_sub_cancel]
  · rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x28_1, Nat.add_sub_cancel]
  · rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x15_1, Nat.add_sub_cancel]
  · rw [kx _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x16_1, Nat.add_sub_cancel]
  ·
    have hfr3 : ∀ A, A + 8 ≤ pslot k → t3.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A hA
      rw [hpost.frame A (by omega) (by
          rintro (⟨off, _, he⟩ | h)
          · omega
          · omega),
        hw'.frame A (by omega) (by
          rintro (h | h | h)
          · have := chainsWr_range h; omega
          · omega
          · omega), m21]
    rcases Nat.lt_or_ge k' k with h | h
    · rw [getD_append_lt _ _ _ _ (by rw [hI.len]; exact h)]
      have hD := hI.pairs k' h
      have hlt : pslot k' + 32 ≤ pslot k := by unfold pslot; omega
      exact ⟨⟨(hfr3 _ (by omega)).trans hD.1.1, (hfr3 _ (by omega)).trans hD.1.2⟩,
        ⟨(hfr3 _ (by omega)).trans hD.2.1, (hfr3 _ (by omega)).trans hD.2.2⟩⟩
    · have : k' = k := by omega
      subst this
      have e := getD_append_len pairs pr (0, 0)
      rw [hI.len] at e
      rw [e]
      exact hpost.pair
  · refine (((hI.frame.trans F1).trans hw'.frame).trans hpost.frame).mono (fun A _ hA => ?_)
    rcases hA with ((h | h) | h) | h
    · rcases h with h | h
      · left; unfold regBase at h ⊢; omega
      · right; omega
    · exact h.elim
    · rcases h with h | h | h
      · have := chainsWr_range h; left; unfold regBase at this ⊢; omega
      · left; unfold regBase at h ⊢; omega
      · left; unfold regBase at h ⊢; omega
    · rcases h with ⟨off, hoff, he⟩ | h
      · have := (childWrites_bound hoff).2
        left; unfold regBase at he ⊢; omega
      · right; unfold pslot at h; omega
end ClaudeWCT.W9.Machine.Expand
end
