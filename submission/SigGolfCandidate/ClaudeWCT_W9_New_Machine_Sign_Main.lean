import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_TopLeafP
import SigGolfCandidate.T3M_Sign_PackedBoundaryEntry
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_PackedLeaf
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsLoop

macro "sign_slice_fast" : tactic => `(tactic|
  first
  | (apply SigGolfCandidate.T3M.codeAt_sign_last <;> decide +kernel)
  | (apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel))

section

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
structure GlobSt (sk : BitVec 256) (N : BitVec 256) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x22 : t.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex N)
  nbuf : OutAt t NBUF N
  table : TableAt t
  p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64
  zero : ∀ A, ScrZero A → t.getMem (BitVec.ofNat 64 A) = 0
def coordW (c : Nat) (A : Nat) : Prop :=
  loopW c A ∨ treeW A ∨ (FORW + forOff c ≤ A ∧ A < FORW + forOff c + 32) ∨ (slotP c 0 ≤ A ∧ A < slotP c 7) ∨
    (COEF ≤ A ∧ A < COEF + 864)
theorem GlobSt.frame {sk N : BitVec 256} {s t : MachineState} {c : Nat} {l : List Reg} (hc : c < 9)
    (h : GlobSt sk N s) (hr : RegsExcept s t l) (hl : .x5 ∉ l ∧ .x22 ∉ l) (hf : Frame s t (coordW c))
    (hz : DigAt t (NODEW + 32) 0) :
    GlobSt sk N t := by
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  have nw : ∀ A, (NBUF ≤ A ∧ A < NBUF + 32 ∨ TBL ≤ A ∧ A < TBL + 65536 ∨ A = PRIVW ∨ A = PRIVW + 8 ∨
      A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ (ScrZero A ∧ A ≠ NODEW + 32 ∧ A ≠ NODEW + 40)) → ¬ coordW c A := by
    intro A hA hw
    unfold coordW loopW bodyW treeW slotV slotP ScrZero at *
    simp only [COEF] at *
    aoh
  refine ⟨by rw [hr.get hl.1]; exact h.x5, by rw [hr.get hl.2]; exact h.x22, fun k hk => ?_, fun k hk => ?_,
    ?_, ?_, ?_, ?_, fun A hA => ?_⟩
  · rw [hf.get (by ao) (nw _ (Or.inl (by constructor <;> ao)))]; exact h.nbuf k hk
  · rw [hf.get (by ao) (nw _ (Or.inr (Or.inl (by constructor <;> ao))))]; exact h.table k hk
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p0
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p8
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p32
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p40
  · have hA' : A < 2 ^ 64 := by unfold ScrZero at hA; aoh
    by_cases h32 : A = NODEW + 32
    · subst h32; exact hz.1.trans (by decide)
    by_cases h40 : A = NODEW + 40
    · subst h40; exact hz.2.trans (by decide)
    rw [hf.get hA' (nw _ (by simp [hA, h32, h40]))]; exact h.zero A hA
theorem coordW_other {c c' A : Nat} (hc : c < 9) (hc' : c' < 9) (hne : c ≠ c')
    (hA : (SIG + 16 + 208 * c' ≤ A ∧ A < SIG + 16 + 208 * (c' + 1)) ∨
      (FORW + forOff c' ≤ A ∧ A < FORW + forOff c' + 32)) : ¬ coordW c A := by
  have h1 : forOff c ≤ 288 := by unfold forOff; omega
  have h2 : forOff c' ≤ 288 := by unfold forOff; omega
  have h3 : forOff c + 32 ≤ forOff c' ∨ forOff c' + 32 ≤ forOff c := by unfold forOff; omega
  intro hw
  unfold coordW loopW bodyW treeW slotV slotP at *
  simp only [COEF] at *
  aoh
def coefStepC : Nat := 8 + 10
def coordC (c : Nat) : Nat :=
  fk c + (1 + (14 + (27 * coefStepC + (128 * loopStepC + (126 * treeC + (12 + 7 * 13))))))
theorem coordC_le (c : Nat) :
    coordC c ≤ 13 + (1 + (14 + (27 * coefStepC + (128 * loopStepC + (126 * treeC + (12 + 7 * 13)))))) := by
  unfold coordC fk; split_ifs <;> omega
theorem field_lt563 {N : BitVec 256} (hadm : WCT9.admissible N = true) {c : Nat} (hc : c < 9) :
    N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10 < 563 :=
  ((WCT9.admissible_iff N).1 hadm).2 ⟨c, hc⟩
theorem pcI_seven (c : Nat) (hc : c < 9) : pcI c 7 = if c < 8 then cbase (c + 1) else 20715 := by
  interval_cases c <;> decide
def coefRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x29]
def coefW (A : Nat) : Prop := A = PRIVW + 16 ∨ A = PRIVW + 24 ∨ (COEF ≤ A ∧ A < COEF + 864)
structure CoefInv (im : Image) (c index : Nat) (s0 : MachineState) (j : Nat) (acc : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (if j < 27 then ecI c else leafI c)
  run : j < 27 → fetch im t = some (.base .ECALL) ∧ t.getReg .x7 = BitVec.ofNat 64 j ∧
    t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
    t.getReg .x12 = BitVec.ofNat 64 (COEF + 32 * j) ∧
    t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)
  done : 27 ≤ j → t.getReg .x18 = BitVec.ofNat 64 0
  p16 : t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c)
  len : acc.length = 2 * j
  coef : ∀ k < 2 * j, DigAt t (COEF + 16 * k) (acc.getD k 0)
  regs : RegsExcept s0 t coefRegs
  frame : Frame s0 t coefW
theorem paI_ecI : ∀ c, c < 9 → ecI c + 1 = paI c := by decide +kernel
theorem getD_append2 (acc : List Digest) (x y : Digest) (k : Nat) (hk : k < acc.length + 2) :
    (acc ++ [x, y]).getD k 0 = if k < acc.length then acc.getD k 0 else if k = acc.length then x else y := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : k - acc.length = 1 := by omega
    simp [this]
section coefs
variable {im : Image} {sk : BitVec 256}
theorem coef_step (hcode : NewCodeAt im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    (h5 : s0.getReg .x5 = 0) (h22 : s0.getReg .x22 = BitVec.ofNat 64 index)
    (p0 : s0.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64)
    (p8 : s0.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64)
    (p32 : s0.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64)
    (p40 : s0.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64)
    (p48 : s0.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0) (p56 : s0.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0)
    (j : Nat) (hj : j < 27) (acc : List Digest) (t : MachineState) (h : CoefInv im c index s0 j acc t) :
    TBSim im sk t coefStepC (coefStep index c acc (0 + j)) (CoefInv im c index s0 (j + 1)) := by
  obtain ⟨ec, x7, x10, x11, x12, m24⟩ := h.run hj
  have gm : ∀ A, A < 2 ^ 64 → ¬ coefW A → t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => h.frame.get hA hn
  have nw : ∀ A, (A = PRIVW ∨ A = PRIVW + 8 ∨ A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ A = PRIVW + 48 ∨
      A = PRIVW + 56) → ¬ coefW A := by
    intro A hA hw; unfold coefW at hw; simp only [PRIVW, COEF] at *; omega
  have hq := hashInput_priv t sk hc (by omega : index < 2 ^ 32) (by omega : j < 2 ^ 32) x10 x11
    (by rw [gm _ (by ao) (nw _ (by simp))]; exact p0) (by rw [gm _ (by ao) (nw _ (by simp))]; exact p8) h.p16 m24
    (by rw [gm _ (by ao) (nw _ (by simp))]; exact p32) (by rw [gm _ (by ao) (nw _ (by simp))]; exact p40)
    (by rw [gm _ (by ao) (nw _ (by simp))]; exact p48) (by rw [gm _ (by ao) (nw _ (by simp))]; exact p56)
  have t5 : t.getReg .x5 = 0 := by rw [h.regs.get (by simp [coefRegs])]; exact h5
  have t22 : t.getReg .x22 = BitVec.ofNat 64 index := by rw [h.regs.get (by simp [coefRegs])]; exact h22
  unfold coefStep WCT9.ftsSeedPair
  simp only [Nat.zero_add]
  refine (TBSim.privatePair_bind' (W := 10) ec t5
    (hashArgs_const t PRIVW 64 (COEF + 32 * j) x10 x11 x12 (by ao) (by norm_num) (by ao)
      (by simp only [COEF]; omega) (by simp only [COEF]; omega)) hq (fun a => ?_)).mono
    (by unfold coefStepC; omega) (fun _ _ h => h)
  set u := writeHash t a with hu
  have fu := Frame.writeHash t a (COEF + 32 * j) x12 (by simp only [COEF]; omega)
  have dlo := DigAt.writeHash_lo t a (COEF + 32 * j) x12 (by simp only [COEF]; omega)
  have dhi := DigAt.writeHash_hi t a (COEF + 32 * j) x12 (by simp only [COEF]; omega)
  have upc : u.pc = pcOf (paI c) := by
    rw [hu, pc_writeHash, h.pc, if_pos hj, pcOf_add4, paI_ecI c hc]
  have hlen : (acc ++ [a.extractLsb' 0 128, a.extractLsb' 128 128]).length = 2 * (j + 1) := by
    simp [h.len]; omega
  -- facts common to both exits, at `u`
  have ucoef : ∀ k < 2 * (j + 1), DigAt u (COEF + 16 * k)
      ((acc ++ [a.extractLsb' 0 128, a.extractLsb' 128 128]).getD k 0) := by
    intro k hk
    rw [getD_append2 _ _ _ k (by rw [h.len]; omega), h.len]
    split_ifs with h1 h2
    · exact (h.coef k h1).frame fu (by simp only [COEF]; omega) (by simp only [COEF]; omega)
        (by simp only [COEF]; omega)
    · subst h2; rw [show COEF + 16 * (2 * j) = COEF + 32 * j by omega]; exact dlo
    · rw [show k = 2 * j + 1 by omega, show COEF + 16 * (2 * j + 1) = COEF + 32 * j + 16 by omega]; exact dhi
  have up16 : u.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c) := by
    rw [fu.get (by ao) (by simp only [PRIVW, COEF]; omega)]; exact h.p16
  have uregs : RegsExcept s0 u coefRegs :=
    (h.regs.trans (fun x _ => getReg_writeHash t a x : RegsExcept t u [])).mono (by simp)
  have uframe : Frame s0 u coefW := (h.frame.trans fu).mono (fun A _ hA => by
    rcases hA with hA | hA
    · exact hA
    · unfold coefW; right; right; simp only [COEF] at *; omega)
  by_cases hj1 : j + 1 < 27
  · obtain ⟨v, sv, ev, vpc, v7, v10, v11, v12, v24, vregs, vframe⟩ := step_CLc hcode hc u upc
      (by rw [hu, getReg_writeHash]; exact x7) hj1 (by rw [hu, getReg_writeHash]; exact x12)
      (by rw [hu, getReg_writeHash]; exact t22) (by omega)
    refine TBSim.pure_steps' sv ⟨by rw [if_pos hj1]; exact vpc, fun _ => ⟨ev, v7, v10, v11, ?_, v24⟩,
      fun h' => absurd h' (by omega), ?_, hlen, fun k hk => (ucoef k hk).frame vframe (by simp only [COEF]; omega)
        (by simp only [PRIVW, COEF]; omega) (by simp only [PRIVW, COEF]; omega),
      (uregs.trans vregs).mono (by simp [coefRegs]), (uframe.trans vframe).mono (fun A _ hA => by
        rcases hA with hA | hA
        · exact hA
        · unfold coefW; right; left; exact hA)⟩
    · rw [v12, show COEF + 32 * j + 32 = COEF + 32 * (j + 1) by omega]
    · rw [vframe.get (by ao) (by simp only [PRIVW]; omega)]; exact up16
  · obtain ⟨v, sv, vpc, v18, vregs, vframe⟩ := step_CLx hcode hc u upc
      (by rw [hu, getReg_writeHash]; exact x7) (by omega)
    refine (TBSim.pure_steps' sv ⟨by rw [if_neg hj1]; exact vpc, fun h' => absurd h' hj1, fun _ => v18, ?_, hlen,
      fun k hk => (ucoef k hk).frame vframe (by simp only [COEF]; omega) id id,
      (uregs.trans vregs).mono (by simp [coefRegs]), (uframe.trans vframe).mono (fun A _ hA => by
        rcases hA with hA | hA
        · exact hA
        · exact hA.elim)⟩).mono (by norm_num) (fun _ _ h => h)
    rw [vframe.get (by ao) id]; exact up16
end coefs
section coord
variable {im : Image} {sk : BitVec 256}
theorem path_copies (hcode : NewCodeAt im) {c sel : Nat} (hc : c < 9) (hsel : sel < 128) {heap : Array Digest} :
    ∀ n, n ≤ 7 → ∀ t : MachineState, t.pc = pcOf (pcI c (7 - n)) → t.getReg .x24 = BitVec.ofNat 64 sel →
      (∀ m, 2 ≤ m → m < 256 → DigAt t (HEAPW + 16 * m) (heap.getD m 0)) →
      ∃ u, Steps im t (13 * n) (13 * n) u ∧ u.pc = pcOf (pcI c 7) ∧
        (∀ l, 7 - n ≤ l → l < 7 → DigAt u (slotP c l) (heap.getD (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) 0)) ∧
        RegsExcept t u [.x6, .x7, .x28, .x29] ∧ Frame t u (fun A => slotP c (7 - n) ≤ A ∧ A < slotP c 7) := by
  intro n
  induction n with
  | zero =>
    intro _ t hpc _ _
    exact ⟨t, Steps.refl t, hpc, fun l h1 h2 => absurd h2 (by omega), RegsExcept.refl _ _, fun A _ _ => rfl⟩
  | succ n ih =>
    intro hn t hpc h24 hheap
    have hl : 7 - (n + 1) < 7 := by omega
    obtain ⟨t1, s1, p1, m0, m8, r1, f1⟩ := step_PC hcode hc hl hsel t hpc h24
    have hph := pathHeap_lt sel (7 - (n + 1)) hsel hl
    have hm := hheap (2 ^ (7 - (7 - (n + 1))) + (sel / 2 ^ (7 - (n + 1)) ^^^ 1)) (by
      have : 2 ≤ 2 ^ (7 - (7 - (n + 1))) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (7 - (7 - (n + 1))) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) hph
    have h24' : t1.getReg .x24 = BitVec.ofNat 64 sel := by rw [r1.get (by simp)]; exact h24
    have hheap' : ∀ m, 2 ≤ m → m < 256 → DigAt t1 (HEAPW + 16 * m) (heap.getD m 0) := fun m h1 h2 =>
      (hheap m h1 h2).frame f1 (by ao) (by unfold slotP; intro h; rcases h with h | h <;> aoh)
        (by unfold slotP; intro h; rcases h with h | h <;> aoh)
    obtain ⟨u, su, pu, hu, ru, fu⟩ := ih (by omega) t1 (by rw [p1, show 7 - (n + 1) + 1 = 7 - n by omega]) h24' hheap'
    refine ⟨u, (s1.trans su).of_eq (by ring) (by ring), pu, fun l h1 h2 => ?_, (r1.trans ru).mono (by simp), ?_⟩
    · by_cases hle : 7 - n ≤ l
      · exact hu l hle h2
      · have : l = 7 - (n + 1) := by omega
        subst this
        have hd : DigAt t1 (slotP c (7 - (n + 1))) (heap.getD (2 ^ (7 - (7 - (n + 1))) + (sel / 2 ^ (7 - (n + 1)) ^^^ 1)) 0) :=
          ⟨by rw [m0]; exact hm.1, by rw [m8]; exact hm.2⟩
        exact DigAt.frame hd fu (by unfold slotP; ao) (by unfold slotP; intro h; aoh) (by unfold slotP; intro h; aoh)
    · refine (f1.trans fu).mono (fun A _ hA => ?_)
      unfold slotP at *
      rcases hA with (h | h) | h <;> aoh
theorem getD_map_range7 (f : Nat → Digest) {l : Nat} (hl : l < 7) : ((List.range 7).map f).getD l 0 = f l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
theorem toArray_getD_high (leaves : List Digest) (m : Nat) (hm : 128 ≤ m) :
    ((List.replicate 128 (0 : Digest) ++ leaves).toArray).getD m 0 = leaves.getD (m - 128) 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append_right (by simp; omega)]
  simp [List.getD_eq_getElem?_getD]
-- (witness stack) removed: reference-image (NewCodeAt) FTS proof; the old FTS code has no G chains.
end coord
end ClaudeWCT.W9.Machine.Sign
end
section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
def coordCmax : Nat := 13 + (1 + (14 + (27 * coefStepC + (128 * loopStepC + (126 * treeC + (12 + 7 * 13))))))
def ftsW' (A : Nat) : Prop := (PRIVW ≤ A ∧ A < SCREND) ∨ (SIG + 16 ≤ A ∧ A < SIG + 1888)
structure FtsInv (sk N : BitVec 256) (s0 : MachineState) (k : Nat)
    (st : List WCT9.Opening × List (Digest × Digest)) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 9 then cbase k else 20715)
  glob : GlobSt sk N t
  len1 : st.1.length = k
  len2 : st.2.length = k
  outs : ∀ c < k, OpeningAt t c (st.1.getD c ⟨fun _ => 0, fun _ => 0⟩) ∧
    DigAt t (FORW + forOff c) (st.2.getD c (0, 0)).1 ∧ DigAt t (FORW + forOff c + 16) (st.2.getD c (0, 0)).2
  regs : RegsExcept s0 t ftsRegs
  frame : Frame s0 t ftsW'
theorem foldlM_finRange9 {α : Type} (f : α → Fin 9 → M α) (init : α) :
    (List.finRange 9).foldlM f init =
      (List.range' 0 9).foldlM (fun st k => if h : k < 9 then f st ⟨k, h⟩ else pure st) init := by
  rw [show List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl,
    show List.range' 0 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
  simp only [List.foldlM_cons, List.foldlM_nil]
  rfl
theorem OpeningAt.frame {s t : MachineState} {W : Nat → Prop} {c : Nat} {op : WCT9.Opening} (hc : c < 9)
    (h : OpeningAt s c op) (hf : Frame s t W)
    (hW : ∀ A, SIG + 16 + 208 * c ≤ A → A < SIG + 16 + 208 * (c + 1) → ¬ W A) : OpeningAt t c op := by
  refine ⟨fun i => (h.1 i).frame hf (by ao) (hW _ (by omega) (by have := i.isLt; omega))
    (hW _ (by omega) (by have := i.isLt; omega)), fun l => (h.2 l).frame hf (by ao)
      (hW _ (by omega) (by have := l.isLt; omega)) (hW _ (by omega) (by have := l.isLt; omega))⟩
theorem getD_snoc {α : Type} (l : List α) (x d : α) (n : Nat) :
    (l ++ [x]).getD n d = if n < l.length then l.getD n d else if n = l.length then x else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp
theorem prevPair_last (start : Digest × Digest) (l : List (Digest × Digest)) (d : Digest × Digest) (k : Nat)
    (hl : l.length = k)
    (hk : 1 ≤ k) : WCT9.prevPair start l = l.getD (k - 1) d := by
  unfold WCT9.prevPair
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hl, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
theorem FtsInv.pads {sk N : BitVec 256} {s0 : MachineState} {k : Nat} {st : List WCT9.Opening × List (Digest × Digest)}
    {t : MachineState} (hk : k < 9) (h : FtsInv sk N s0 k st t) :
    PadAt k 0 (WCT9.prevPair WCT9.ftsStart st.2).1 t ∧ PadAt k 16 (WCT9.prevPair WCT9.ftsStart st.2).2 t := by
  unfold PadAt
  by_cases k0 : k = 0
  · subst k0
    rw [List.length_eq_zero_iff.mp h.len2]
    exact ⟨by rw [if_pos rfl]; rfl, by rw [if_pos rfl]; rfl⟩
  · rw [if_neg k0, if_neg k0, prevPair_last _ _ (0, 0) k h.len2 (by omega)]
    obtain ⟨-, o2, o3⟩ := h.outs (k - 1) (by omega)
    exact ⟨by rw [Nat.add_zero]; exact o2, o3⟩
section fts
variable {im : Image} {sk : BitVec 256}
-- (witness stack) removed: reference-image (NewCodeAt) FTS proof; the old FTS code has no G chains.
end fts
theorem getD_flatMap_pairWords : ∀ (ps : List (Digest × Digest)) (c r : Nat), c < ps.length → r < 4 →
    (ps.flatMap pairWords).getD (4 * c + r) 0 = (pairWords (ps.getD c (0, 0))).getD r 0
  | [], c, r, h, _ => absurd h (by simp)
  | p :: ps, 0, r, _, hr => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [pairWords]; omega),
      List.getD_cons_zero, List.getD_eq_getElem?_getD, Nat.mul_zero, Nat.zero_add]
  | p :: ps, c + 1, r, h, hr => by
    have ih := getD_flatMap_pairWords ps c r (by simp at h; omega) hr
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [pairWords]; omega),
      List.getD_cons_succ, ← ih, List.getD_eq_getElem?_getD]
    simp only [pairWords, List.length_cons, List.length_nil]
    congr 2
    omega
theorem pairWords_getD (p : Digest × Digest) (r : Nat) (hr : r < 4) :
    (pairWords p).getD r 0 = (if r < 2 then p.1 else p.2).extractLsb' (64 * (r % 2)) 64 := by
  interval_cases r <;> rfl
theorem hashInput_forest (t : MachineState) {index : Nat} (pairs : List (Digest × Digest)) (hlen : pairs.length = 9)
    (hidx : index < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 FORW) (h11 : t.getReg .x11 = BitVec.ofNat 64 320)
    (hr : ∀ c < 9, DigAt t (FORW + forOff c) (pairs.getD c (0, 0)).1 ∧
      DigAt t (FORW + forOff c + 16) (pairs.getD c (0, 0)).2)
    (m0 : t.getMem (BitVec.ofNat 64 FORW) = 0) (m8 : t.getMem (BitVec.ofNat 64 (FORW + 8)) = 0)
    (m16 : t.getMem (BitVec.ofNat 64 (FORW + 16)) = BitVec.ofNat 64 3841)
    (m24 : t.getMem (BitVec.ofNat 64 (FORW + 24)) = BitVec.ofNat 64 index) :
    hashInput t = toQ (pad64 (WCT9.forestInput index pairs)) := by
  refine hashInput_of_words t _ 4 FORW (by rw [pad64_of_aligned _ (by rw [forestIn_len _ _ hlen]),
    forestIn_len _ _ hlen]) h10 (by ao) (by ao) h11 ?_
  rw [wordsOf_forest index pairs hlen hidx]
  intro k hk
  by_cases hk4 : k < 4
  · interval_cases k
    · exact m0
    · exact m8
    · exact m16
    · exact m24
  · obtain ⟨c, r, hr4, rfl⟩ : ∃ c r, r < 4 ∧ k = 4 + (4 * c + r) := ⟨(k - 4) / 4, (k - 4) % 4, Nat.mod_lt _ (by norm_num),
      by omega⟩
    have hc : c < 9 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), show 4 + (4 * c + r) - [(0 : Word), 0,
      BitVec.ofNat 64 3841, BitVec.ofNat 64 index].length = 4 * c + r by simp, ← List.getD_eq_getElem?_getD,
      getD_flatMap_pairWords pairs c r (by omega) hr4, pairWords_getD _ r hr4]
    obtain ⟨d1, d2⟩ := hr c hc
    have ha : FORW + 8 * (4 + (4 * c + r)) = (if r < 2 then FORW + forOff c else FORW + forOff c + 16) + 8 * (r % 2) := by
      unfold forOff; split_ifs <;> omega
    rw [ha]
    interval_cases r
    · simp only [show (0 : Nat) < 2 from by norm_num, if_true, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]; exact d1.1
    · simp only [show (1 : Nat) < 2 from by norm_num, if_true, Nat.one_mod, Nat.mul_one]; exact d1.2
    · simp only [show ¬ (2 : Nat) < 2 from by norm_num, if_false, show 2 % 2 = 0 from rfl, Nat.mul_zero, Nat.add_zero]
      exact d2.1
    · simp only [show ¬ (3 : Nat) < 2 from by norm_num, if_false, show 3 % 2 = 1 from rfl, Nat.mul_one]; exact d2.2
theorem ftsC_bound : 11 + (9 * coordCmax + (12 + 0)) ≤ ftsC := by
  unfold coordCmax loopStepC childC stepC hornC hornStepC coefStepC treeC ftsC; norm_num
section fts2
variable {im : Image}
-- (witness stack) removed: reference-image (NewCodeAt) FTS proof; the old FTS code has no G chains.
end fts2
end ClaudeWCT.W9.Machine.Sign
end
end

section

section
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest Pieces Layer chainCount height piecesSignature)
open SphincsSecurity (bytesLE bytesLE_length)
local macro "so" : tactic => `(tactic| ((try simp only [SIG] at *) <;> omega))
theorem readBuffer_split (t : MachineState) (A n k : Nat) :
    ∃ R, ((List.range (n + k)).foldl
      (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0) =
      ((List.range n).foldl
      (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0) + 2 ^ (8 * n) * R := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R + (t.getByte (BitVec.ofNat 64 (A + (n + k)))).toNat * 2 ^ (8 * k), ?_⟩
    rw [show n + (k + 1) = (n + k) + 1 by ring, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, hR, show 8 * (n + k) = 8 * n + 8 * k by ring, pow_add]
    ring
theorem readBuffer_trunc (t : MachineState) (A n k : Nat) :
    readBuffer t A n = BitVec.ofNat (8 * n) (readBuffer t A (n + k)).toNat := by
  obtain ⟨R, hR⟩ := readBuffer_split t A n k
  unfold readBuffer
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [hR, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)), Nat.add_mul_mod_self_left]
theorem readOutput_sig (imgs : Phase → Image) (t : MachineState) (sig : WCT9.Signature)
    (h : ∀ k < 332, DigAt t (SIG + 16 * k) ((W9.T3M.sigDigests sig).getD (W9.T3M.cIdx k) 0)) :
    readOutput (wsub imgs).sizes (wsub imgs).layout .sign t = W9.T3M.sigBC sig := by
  have hd : DigsAt t SIG (W9.T3M.compactList sig) := fun k hk => by
    have hk' : k < 332 := by simpa [W9.T3M.compactList] using hk
    have := h k hk'
    simpa [W9.T3M.compactList, List.getD_eq_getElem?_getD, hk'] using this
  have hw := hd.words
  have hlen : (W9.T3M.compactList sig).length = 332 := by simp [W9.T3M.compactList]
  rw [hlen] at hw
  have hl : ((W9.T3M.compactList sig).flatMap (bytesLE 16)).length = 8 * 664 := by
    have : ∀ ds : List Digest, (ds.flatMap (bytesLE 16)).length = 16 * ds.length := fun ds => by
      induction ds with
      | nil => rfl
      | cons d ds ih => rw [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
    rw [this, hlen]
  have e := readBuffer_of_words t SIG 664 ((W9.T3M.compactList sig).flatMap (bytesLE 16)) (by decide) (by decide)
    hl hw
  show readBuffer t SIG 5310 = W9.T3M.sigBC sig
  rw [readBuffer_trunc t SIG 5310 2, show 5310 + 2 = 8 * 664 from rfl, e]
  apply BitVec.eq_of_toNat_eq
  rw [W9.T3M.sigBC_toNat_compact, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num))]
  rfl
theorem DigAt.of_mem {X Y : MachineState} {a b : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 b) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (b + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y b d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
theorem t3LayIdx_eq (lay : Layer) : t3LayIdx lay = W9.T3M.layIdx lay + 19 := by
  fin_cases lay <;> rfl
theorem piece_digest {w : MachineState} {sig : WCT9.Signature} {lay : Layer} {p : Pieces}
    (hp : PieceAt w lay p) (hl : sig.layers lay = piecesSignature lay p) (i : Nat)
    (hi : i < chainCount lay + height lay) :
    DigAt w (SIG + 16 * (t3LayIdx lay + i)) ((W9.T3M.sigDigests sig).getD (W9.T3M.layIdx lay + i) 0) := by
  by_cases hc : i < chainCount lay
  · rw [W9.T3M.sigDigests_layValue sig lay i hc, hl]
    exact hp.1 i hc
  · have e := W9.T3M.sigDigests_layPath sig lay (i - chainCount lay) (by omega)
    rw [show chainCount lay + (i - chainCount lay) = i by omega] at e
    rw [e, hl]
    have := hp.2 (i - chainCount lay) (by omega)
    rwa [show t3LayIdx lay + chainCount lay + (i - chainCount lay) = t3LayIdx lay + i by omega] at this
theorem final_digests {v w x : MachineState} {rho : Digest} {ops : List WCT9.Opening} {ps : List Pieces}
    (hrho : DigAt v SIG rho) (hops : ∀ k < 9, OpeningAt v k (ops.getD k ⟨fun _ => 0, fun _ => 0⟩))
    (hfw : Frame v w (fun A => ¬ (SIG ≤ A ∧ A < SIG + 2192)))
    (hpieces : ∀ lay : Layer, PieceAt w lay (ps.getD lay.val ([], []))) (hc : CompactPost w x) :
    ∀ k < 332, DigAt x (SIG + 16 * k)
      ((W9.T3M.sigDigests (WCT9.assembledSignature rho ops ps)).getD (W9.T3M.cIdx k) 0) := by
  intro k hk
  obtain ⟨-, -, -, hmove, hfx⟩ := hc
  set sig := WCT9.assembledSignature rho ops ps with hsig
  by_cases hlow : k < 118
  · rw [show W9.T3M.cIdx k = k by unfold W9.T3M.cIdx; rw [if_pos (by omega)]]
    have keep : ∀ A, SIG ≤ A → A < SIG + 1888 → x.getMem (BitVec.ofNat 64 A) = v.getMem (BitVec.ofNat 64 A) := by
      intro A hS hA
      rw [hfx.get (by so) (by so), hfw.get (by so) (by so)]
    have keepD : ∀ d, DigAt v (SIG + 16 * k) d → DigAt x (SIG + 16 * k) d := fun d hd =>
      DigAt.of_mem hd (keep _ (by so) (by so)) (keep _ (by so) (by so))
    apply keepD
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [W9.T3M.sigDigests_rho, hsig, WCT9.assembledSignature_rho]; simpa using hrho
    · obtain ⟨c, i, hc9, hi13, rfl⟩ : ∃ c i, c < 9 ∧ i < 13 ∧ k = 1 + 13 * c + i :=
        ⟨(k - 1) / 13, (k - 1) % 13, by omega, by omega, by omega⟩
      have ho := hops c hc9
      by_cases hi6 : i < 6
      · have e := W9.T3M.sigDigests_value sig ⟨c, hc9⟩ ⟨i, hi6⟩
        simp only at e
        rw [e, hsig, WCT9.assembledSignature_openings]
        have := ho.1 ⟨i, hi6⟩
        simp only at this
        rwa [show SIG + 16 * (1 + 13 * c + i) = SIG + 16 + 208 * c + 16 * i by ring]
      · have e := W9.T3M.sigDigests_path sig ⟨c, hc9⟩ ⟨i - 6, by omega⟩
        simp only at e
        rw [show 1 + 13 * c + 6 + (i - 6) = 1 + 13 * c + i by omega] at e
        rw [e, hsig, WCT9.assembledSignature_openings]
        have := ho.2 ⟨i - 6, by omega⟩
        simp only at this
        rwa [show SIG + 16 * (1 + 13 * c + i) = SIG + 112 + 208 * c + 16 * (i - 6) by omega]
  ·
    have hpk : 118 + cpIdx (k - 118) = W9.T3M.cIdx k := by
      unfold cpIdx W9.T3M.cIdx; split_ifs <;> omega
    have moveD : ∀ d, DigAt w (SIG + 16 * (W9.T3M.cIdx k + 19)) d → DigAt x (SIG + 16 * k) d := fun d hd => by
      refine DigAt.of_mem hd ?_ ?_
      · have := hmove (2 * (k - 118)) (by omega)
        rw [show 2 * (k - 118) / 2 = k - 118 by omega, show 2 * (k - 118) % 2 = 0 by omega,
          show SIG + 1888 + 8 * (2 * (k - 118)) = SIG + 16 * k by so,
          show SIG + 2192 + 16 * cpIdx (k - 118) + 8 * 0 = SIG + 16 * (W9.T3M.cIdx k + 19) by rw [← hpk]; so] at this
        exact this
      · have := hmove (2 * (k - 118) + 1) (by omega)
        rw [show (2 * (k - 118) + 1) / 2 = k - 118 by omega, show (2 * (k - 118) + 1) % 2 = 1 by omega,
          show SIG + 1888 + 8 * (2 * (k - 118) + 1) = SIG + 16 * k + 8 by so,
          show SIG + 2192 + 16 * cpIdx (k - 118) + 8 * 1 = SIG + 16 * (W9.T3M.cIdx k + 19) + 8 by rw [← hpk]; so] at this
        exact this
    apply moveD
    have hc1 : 118 ≤ W9.T3M.cIdx k := by unfold W9.T3M.cIdx; split_ifs <;> omega
    have hc2 : W9.T3M.cIdx k < 332 := by unfold W9.T3M.cIdx; split_ifs <;> omega
    generalize W9.T3M.cIdx k = j at hc1 hc2 ⊢
    have key : ∀ lay : Layer, ∀ i, i < chainCount lay + height lay → j = W9.T3M.layIdx lay + i →
        DigAt w (SIG + 16 * (j + 19)) ((W9.T3M.sigDigests sig).getD j 0) := by
      intro lay i hi hk'
      have := piece_digest (hpieces lay) (sig := sig) rfl i hi
      rw [t3LayIdx_eq] at this
      rw [hk', show W9.T3M.layIdx lay + i + 19 = W9.T3M.layIdx lay + 19 + i by omega]
      exact this
    by_cases h1 : j < 184
    · exact key 0 (j - 118) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    by_cases h2 : j < 234
    · exact key 1 (j - 184) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    by_cases h3 : j < 283
    · exact key 2 (j - 234) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    · exact key 3 (j - 283) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
end ClaudeWCT.W9.Machine.Sign
end
section
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M Pieces Layer privateMac privateNonce)
local macro "so" : tactic =>
  `(tactic| ((try simp only [SIG, SK, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, CHAINW, NODEW, FORW, SCREND,
    SearchW, FtsW, ScrZero, NewW] at *) <;> omega))
def Kw (cache : Bytes 131072) (m : Message) (rho : Digest) : M (Option WCT9.Signature) := do
  let some (_, output) ← WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit | pure none
  let forest ← WCT9.signForest (WCT9.digestIndex output) output
  let some pieces ← WCT9.signLayersBC (cacheDec cache) (WCT9.digestIndex output) 4 (.pair forest.2.1 forest.2.2)
    | pure none
  pure (some (WCT9.assembledSignature rho forest.1 pieces))
theorem rev3_sign_eq (cache : Bytes 131072) (m : Message) :
    WCT9.Rev3.sign (cacheDec cache) m = (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= Kw cache m) := by
  rw [WCT9.Rev3.sign_eq, WCT9.Rev3.signPayload_eq]
  rfl
def FinalQ : Option WCT9.Signature → MachineState → Prop
  | none, t => FailedT t ∨ FailedS t
  | some sig, t => t.pc = pcOf 20745 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      ∀ k < 332, DigAt t (SIG + 16 * k) ((W9.T3M.sigDigests sig).getD (W9.T3M.cIdx k) 0)
def restC : Nat := searchC + (ftsC + (layC + compactK))
def signCW : Nat := frontC + restC
theorem signCW_eq : signCW = 4110967262 := by
  norm_num [signCW, restC, frontC, searchC, trialC, WCT9.digestAttemptLimit, ftsC, layC, compactK]
theorem signCW_lt : signCW + 1 < CYCLE_LIMIT := by
  rw [signCW_eq]; norm_num [CYCLE_LIMIT]
section rest
variable {im : Image} {sk : BitVec 256} {cache : Bytes 131072} {m : Message}
theorem rest_tbsim (hcode : SignCodeAt im) (hS : SearchGood im) (hF : FtsGood im) (hC : CompactGood im)
    {Inv : MachineState → Prop} (hstab : InvStable Inv) (hlay : LayersSpec im sk cache Inv)
    (rho : Digest) (t : MachineState) (hp : HookPre sk m rho t) (hinv : Inv t) :
    TBSim im sk t restC (Kw cache m rho) FinalQ := by
  obtain ⟨hnew, hhooks⟩ := hcode
  unfold Kw restC
  refine TBSim.bind (hS hnew hhooks sk rho m t hp.search) (fun r u hu => ?_)
  rcases r with _ | ⟨c, N⟩
  · exact TBSim.mono (TBSim.pure (Or.inr hu)) (Nat.zero_le _) (fun _ _ h => h)
  obtain ⟨upc, u5, uadm, unb, u22, uidx, -, ur, uf⟩ := hu
  have gu : ∀ A, A < 2 ^ 64 → ¬ SearchW A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => uf.get hA hn
  have hpre : FtsPre sk N u :=
    { pc := upc
      x5 := u5
      x22 := u22
      adm := WCT9.admissible_of_producer uadm
      nbuf := unb
      sk := fun k hk => by rw [gu _ (by so) (by so)]; exact hp.sk k hk
      zero := fun A hA => by
        rw [gu _ (by unfold ScrZero at hA; so) (by unfold ScrZero at hA; so)]; exact hp.zero A hA
      table := fun k hk => by rw [gu _ (by so) (by so)]; exact hp.table k hk }
  refine TBSim.bind (hF hnew sk N u hpre) (fun fr v hv => ?_)
  obtain ⟨ops, top⟩ := fr
  obtain ⟨vpc, v5, vroot, vright, -, vops, vr, vf⟩ := hv
  have hlp : LayPre (WCT9.digestIndex N) top v :=
    ⟨vpc, v5, Nat.mod_lt _ (by norm_num), by rw [vf.get (by so) (by so)]; exact uidx, vroot, vright⟩
  have hinv' : Inv v := hstab t v hinv ((uf.trans vf).mono (fun A _ h => h))
    ((ur.trans vr).mono (by decide))
  refine TBSim.bind (hlay _ top v hlp hinv') (fun r w hw => ?_)
  rcases r with _ | ps
  · exact TBSim.mono (TBSim.pure (Or.inl hw)) (Nat.zero_le _) (fun _ _ h => h)
  obtain ⟨wpc, -, wpieces, wf⟩ := hw
  obtain ⟨x, st, hx⟩ := hC hnew hhooks w wpc
  have hrho : DigAt v SIG rho :=
    (hp.sigRho.frame uf (by so) (by so) (by so)).frame vf (by so) (by so) (by so)
  exact TBSim.pure_steps' st ⟨hx.1, hx.2.1, hx.2.2.1, final_digests hrho vops wf wpieces hx⟩
end rest
theorem sign_tbsim_w (hS : ∀ im, SearchGood im) (hF : ∀ im, FtsGood im) (hC : ∀ im, CompactGood im)
    {imgs : Phase → Image} {Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop}
    (hcode : SignCodeAt (imgs .sign)) (hU : Unchanged imgs Inv) (sk : BitVec 256) (cache : Bytes 131072)
    (m : Message) :
    ∃ s0, initialState (wsub imgs) .sign (sk, cache, m) = some s0 ∧
      TBSim (imgs .sign) sk s0 signCW (WCT9.Rev3.sign (cacheDec cache) m) FinalQ := by
  obtain ⟨s0, hinit, hfs⟩ := hU.front sk cache m
  refine ⟨s0, hinit, ?_⟩
  rw [rev3_sign_eq]
  exact hfs restC FinalQ (Kw cache m) (fun t ht => Or.inl ht)
    (fun rho t hp hi => rest_tbsim hcode (hS _) (hF _) (hC _) (hU.stable sk cache m) (hU.layers sk cache m) rho t hp hi)
theorem fetch_ecall {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) (n : Nat)
    (hn : look n = some 0x00000073) (hn' : n < 2 ^ 32) (t : MachineState) (ht : t.pc = pcOf n) :
    fetch im t = some (.base .ECALL) := by
  have e : (pcOf n).toNat = 0x1000 + 4 * n := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  rw [fetch_of_look hl (pc := pcOf n) (by rw [e]; simp) (by rw [e]; simpa using hn) t ht]
  rfl
theorem finalQ_fetch {imgs : Phase → Image} (hcode : SignCodeAt (imgs .sign)) :
    ∀ o t, FinalQ o t → fetch (imgs .sign) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 := by
  obtain ⟨hnew, hhooks⟩ := hcode
  intro o t ht
  rcases o with _ | sig
  · rcases ht with h | h
    · exact ⟨fetch_ecall (hookLook_ok hhooks) 545 (by decide) (by decide) t h.pc, h.x5⟩
    · exact ⟨fetch_ecall (headLook_ok hnew) 11174 (by decide +kernel) (by decide) t h.pc, h.x5⟩
  · exact ⟨fetch_ecall (tailLook_ok hnew) 20745 (by decide +kernel) (by decide) t ht.1, ht.2.1⟩
theorem signMain_of (hS : ∀ im, SearchGood im) (hF : ∀ im, FtsGood im) (hC : ∀ im, CompactGood im) :
    SignMain := by
  intro imgs Inv hcode hU
  refine ⟨fun sk cache m => ?_, fun hash sk cache m => ?_⟩
  · obtain ⟨s0, hinit, hsim⟩ := sign_tbsim_w hS hF hC hcode hU sk cache m
    refine Sim.run_eq (wsub imgs) .sign (sk, cache, m) hinit hsim (by have := signCW_lt; omega)
      (fun o => o.map W9.T3M.sigBC) (fun o t ht => ?_)
    obtain ⟨hf, h5⟩ := finalQ_fetch hcode o t ht
    refine ⟨hf, h5, ?_⟩
    rcases o with _ | sig
    · rcases ht with h | h
      · rw [if_neg (by rw [h.x10]; decide)]; rfl
      · rw [if_neg (by rw [h.x10]; decide)]; rfl
    · rw [if_pos ht.2.2.1, readOutput_sig imgs t sig ht.2.2.2]; rfl
  · obtain ⟨s0, hinit, hsim⟩ := sign_tbsim_w hS hF hC hcode hU sk cache m
    obtain ⟨h1, h2⟩ := Sim.runWith (wsub imgs) .sign (sk, cache, m) hinit hsim signCW_lt
      (finalQ_fetch hcode) hash
    exact ⟨h1, by have := signCW_lt; omega⟩
end ClaudeWCT.W9.Machine.Sign
end
end

section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))
def cHook : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 20730, false, 1, 1, [], none⟩
def cLoopRegs : RegFile :=
  (((RegFile.init.set .x6 (.ld (.reg .x28))).set .x7 (.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8))))).set .x28
    (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16)))).set .x29 (.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16)))
def cLoopMem : SymMem :=
  [(⟨some (.reg .x29), BitVec.ofNat 64 8⟩, .ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))), (⟨some (.reg .x29), BitVec.ofNat 64 0⟩, .ld (.reg .x28))]
def cLoopObl : List Oblig :=
  [.valid ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ 8, .valid ⟨some (.reg .x28), BitVec.ofNat 64 8⟩ 8,
    .valid ⟨some (.reg .x28), BitVec.ofNat 64 0⟩ 8]
def cBr (d : Bool) : Br := ⟨.ltu, .bin .add (.reg .x28) (.c (BitVec.ofNat 64 16)), .reg .x30, d⟩
def cBack : PRes := ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20736, false, 7, 7, [cBr true], none⟩
def cExit : PRes :=
  ⟨⟨(cLoopRegs.set .x5 (.c (BitVec.ofNat 64 1))).set .x10 (.c (BitVec.ofNat 64 0)), cLoopMem, cLoopObl⟩, pcOf 20745, true, 9, 9, [cBr false], none⟩
theorem run_cHook : run hookLook [20730] 540 [] = some cHook := optBeq_eq (by decide +kernel)
theorem run_cBack : run tailLook [20736] 20736 [.br true] = some cBack := optBeq_eq (by decide +kernel)
theorem run_cExit : run tailLook [20736] 20736 [.br false] = some cExit := optBeq_eq (by decide +kernel)
theorem cLoopMem_get (s : MachineState) (S D A : Nat) (hD : D + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s cLoopMem (BitVec.ofNat 64 A) =
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold cLoopMem
  rw [memEval_cons, memEval_cons, memEval_nil]
  have e1 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ = BitVec.ofNat 64 (D + 8) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 8
  have e0 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ = BitVec.ofNat 64 D := by
    simp only [Addr.eval, E.eval, h29, ofNat_add_ofNat, Nat.add_zero]
  have v1 : (E.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))).eval s = s.getMem (BitVec.ofNat 64 (S + 8)) := by
    simp only [E.eval, BinOp.eval, h28]; rw [ofNat_add_ofNat S 8]
  have v0 : (E.ld (.reg .x28)).eval s = s.getMem (BitVec.ofNat 64 S) := by
    simp only [E.eval, h28]
  rw [e1, e0, v1, v0]
  simp only [ofNat_inj hA (show D + 8 < 2 ^ 64 by so), ofNat_inj hA (show D < 2 ^ 64 by so)]
theorem cLoopObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 16 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ cLoopObl, o.holds s := by
  unfold MEMORY_BYTES at hS hD
  intro o ho
  simp only [cLoopObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp only [Oblig.holds, Addr.eval, E.eval, h28, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
theorem cBr_holds (s : MachineState) (S : Nat) (d : Bool) (hS : S + 16 < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h30 : s.getReg .x30 = BitVec.ofNat 64 (SIG + 5616))
    (hd : (decide (S + 16 < SIG + 5616)) = d) : (cBr d).holds s := by
  simp only [Br.holds, cBr, CmpOp.eval, E.eval, BinOp.eval, h28, h30]
  rw [ofNat_add_ofNat]
  rw [← hd]
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS, Nat.mod_eq_of_lt (show SIG + 5616 < 2 ^ 64 by
    decide)]
structure CInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 20736
  x28 : t.getReg .x28 = BitVec.ofNat 64 (SIG + 2192 + 16 * k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (SIG + 1888 + 16 * k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)
  done : ∀ j < 2 * k, t.getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * j))
  frame : Frame s0 t (fun A => SIG + 1888 ≤ A ∧ A < SIG + 1888 + 16 * k)
theorem cIter_mem {s0 t : MachineState} {k : Nat} (hk : k < 214) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (A : Nat) (hA : A < 2 ^ 64) :
    (r.toState t).getMem (BitVec.ofNat 64 A) =
      if A = SIG + 1888 + 16 * k + 8 then s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * k + 8))
      else if A = SIG + 1888 + 16 * k then s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * k))
      else t.getMem (BitVec.ofNat 64 A) := by
  rw [PRes.toState_getMem', hmem, cLoopMem_get t _ _ A (by so) hA h.x28 h.x29]
  rw [h.frame.get (by so) (by so), h.frame.get (by so) (by so)]
theorem cIter_inv {s0 t : MachineState} {k : Nat} (hk : k < 214) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (u : MachineState) (hu : u = r.toState t)
    (hpc : u.pc = pcOf 20736) (h28 : u.getReg .x28 = BitVec.ofNat 64 (SIG + 2192 + 16 * (k + 1)))
    (h29 : u.getReg .x29 = BitVec.ofNat 64 (SIG + 1888 + 16 * (k + 1)))
    (h30 : u.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)) : CInv s0 (k + 1) u := by
  subst hu
  refine ⟨hpc, h28, h29, h30, fun j hj => ?_, fun A hA hn => ?_⟩
  · rw [cIter_mem hk h r hmem _ (by so)]
    by_cases hj2 : j < 2 * k
    · rw [if_neg (by so), if_neg (by so)]; exact h.done j hj2
    · by_cases hje : j = 2 * k
      · subst hje; rw [if_neg (by so), if_pos (by so)]; congr 2; omega
      · have : j = 2 * k + 1 := by so
        subst this; rw [if_pos (by so)]; congr 2; omega
  · rw [cIter_mem hk h r hmem A hA, if_neg (by so), if_neg (by so)]
    exact h.frame.get hA (by so)
theorem cLoop {im : Image} (hl : LookOK im tailLook) {s0 u : MachineState} (h0 : CInv s0 0 u) :
    ∀ k, k ≤ 213 → ∃ t, Steps im u (7 * k) (7 * k) t ∧ CInv s0 k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨t, st, ht⟩ := ih (by so)
    obtain ⟨st1, -⟩ := run_sound hl run_cBack t ht.pc
      (cLoopObl_holds t _ _ (by so) (by so) (by so)
        (by so) ht.x28 ht.x29)
      (by
        intro b hb
        simp only [cBack, List.mem_singleton] at hb
        subst hb
        exact cBr_holds t _ true (by so) ht.x28 ht.x30 (by simp; omega))
    refine ⟨_, (st.trans st1).of_eq (by simp [cBack]; ring) (by simp [cBack]; ring),
      cIter_inv (by so) ht cBack rfl _ rfl (PRes.toState_pc' _ _ rfl) ?_ ?_ ?_⟩
    · rw [PRes.toState_getReg']
      show (E.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16))).eval t = _
      simp only [E.eval, BinOp.eval, ht.x28]; rw [ofNat_add_ofNat]; congr 1
    · rw [PRes.toState_getReg']
      show (E.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16))).eval t = _
      simp only [E.eval, BinOp.eval, ht.x29]; rw [ofNat_add_ofNat]; congr 1
    · rw [PRes.toState_getReg']; exact ht.x30
/-- [h2 lane] the sign prepass (words 20813..20831, entered from the copy hook at 20730). -/
def pSetupRegs : RegFile :=
  ((((RegFile.init.set .x14 (.ld (.c (BitVec.ofNat 64 0x7ca0)))).set .x15 (.ld (.c (BitVec.ofNat 64 0x7ca8)))).set .x28
    (.c (BitVec.ofNat 64 0x7cb0))).set .x29 (.c (BitVec.ofNat 64 0x7ca0))).set .x30 (.c (BitVec.ofNat 64 0x85f0))
def pSetup : PRes := ⟨⟨pSetupRegs, [], []⟩, pcOf 20821, false, 9, 9, [], none⟩
def pBack : PRes := ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20821, false, 7, 7, [cBr true], none⟩
def pExitRegs : RegFile :=
  ((cLoopRegs.set .x28 (.c (BitVec.ofNat 64 0x7890))).set .x29 (.c (BitVec.ofNat 64 0x7760))).set .x30
    (.c (BitVec.ofNat 64 0x85f0))
def pExitMem : SymMem :=
  (⟨some (.reg .x29), BitVec.ofNat 64 24⟩, .reg .x15) :: (⟨some (.reg .x29), BitVec.ofNat 64 16⟩, .reg .x14) :: cLoopMem
def pExitObl : List Oblig :=
  .valid ⟨some (.reg .x29), BitVec.ofNat 64 24⟩ 8 :: .valid ⟨some (.reg .x29), BitVec.ofNat 64 16⟩ 8 :: cLoopObl
def pExit : PRes := ⟨⟨pExitRegs, pExitMem, pExitObl⟩, pcOf 20736, false, 16, 16, [cBr false], none⟩
theorem run_pSetup : run cLook [20821] 20730 [] = some pSetup := optBeq_eq (by decide +kernel)
theorem run_pBack : run cLook [20821] 20821 [.br true] = some pBack := optBeq_eq (by decide +kernel)
theorem run_pExit : run cLook [20736] 20821 [.br false] = some pExit := optBeq_eq (by decide +kernel)
theorem pExitMem_get (s : MachineState) (S D A : Nat) (hD : D + 32 < 2 ^ 64) (hA : A < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s pExitMem (BitVec.ofNat 64 A) =
      if A = D + 24 then s.getReg .x15 else if A = D + 16 then s.getReg .x14 else
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold pExitMem
  rw [memEval_cons, memEval_cons]
  have e24 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 24⟩ = BitVec.ofNat 64 (D + 24) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 24
  have e16 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 16⟩ = BitVec.ofNat 64 (D + 16) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 16
  have v15 : (E.reg .x15).eval s = s.getReg .x15 := rfl
  have v14 : (E.reg .x14).eval s = s.getReg .x14 := rfl
  rw [e24, e16, v15, v14, cLoopMem_get s S D A (by so) hA h28 h29]
  simp only [ofNat_inj hA (show D + 24 < 2 ^ 64 by so), ofNat_inj hA (show D + 16 < 2 ^ 64 by so)]
theorem pExitObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 32 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ pExitObl, o.holds s := by
  intro o ho
  simp only [pExitObl, List.mem_cons] at ho
  rcases ho with rfl | rfl | ho
  · unfold MEMORY_BYTES at hD
    simp only [Oblig.holds, Addr.eval, E.eval, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
  · unfold MEMORY_BYTES at hD
    simp only [Oblig.holds, Addr.eval, E.eval, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
  · exact cLoopObl_holds s S D hS (by so) hS8 hD8 h28 h29 o ho
structure PInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 20821
  x28 : t.getReg .x28 = BitVec.ofNat 64 (SIG + 3248 + 16 * k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (SIG + 3232 + 16 * k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)
  x14 : t.getReg .x14 = s0.getMem (BitVec.ofNat 64 (SIG + 3232))
  x15 : t.getReg .x15 = s0.getMem (BitVec.ofNat 64 (SIG + 3240))
  done : ∀ j < 2 * k, t.getMem (BitVec.ofNat 64 (SIG + 3232 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 8 * j))
  frame : Frame s0 t (fun A => SIG + 3232 ≤ A ∧ A < SIG + 3232 + 16 * k)
theorem pIter_mem {s0 t : MachineState} {k : Nat} (hk : k < 148) (h : PInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (A : Nat) (hA : A < 2 ^ 64) :
    (r.toState t).getMem (BitVec.ofNat 64 A) =
      if A = SIG + 3232 + 16 * k + 8 then s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 16 * k + 8))
      else if A = SIG + 3232 + 16 * k then s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 16 * k))
      else t.getMem (BitVec.ofNat 64 A) := by
  rw [PRes.toState_getMem', hmem, cLoopMem_get t _ _ A (by so) hA h.x28 h.x29]
  rw [h.frame.get (by so) (by so), h.frame.get (by so) (by so)]
theorem pIter_inv {s0 t : MachineState} {k : Nat} (hk : k < 148) (h : PInv s0 k t) (u : MachineState)
    (hu : u = pBack.toState t) : PInv s0 (k + 1) u := by
  subst hu
  refine ⟨PRes.toState_pc' _ _ rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun A hA hn => ?_⟩
  · rw [PRes.toState_getReg']
    show (E.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16))).eval t = _
    simp only [E.eval, BinOp.eval, h.x28]; rw [ofNat_add_ofNat]; congr 1
  · rw [PRes.toState_getReg']
    show (E.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16))).eval t = _
    simp only [E.eval, BinOp.eval, h.x29]; rw [ofNat_add_ofNat]; congr 1
  · rw [PRes.toState_getReg']; exact h.x30
  · rw [PRes.toState_getReg']; exact h.x14
  · rw [PRes.toState_getReg']; exact h.x15
  · rw [pIter_mem hk h pBack rfl _ (by so)]
    by_cases hj2 : j < 2 * k
    · rw [if_neg (by so), if_neg (by so)]; exact h.done j hj2
    · by_cases hje : j = 2 * k
      · subst hje; rw [if_neg (by so), if_pos (by so)]; congr 2; omega
      · have : j = 2 * k + 1 := by so
        subst this; rw [if_pos (by so)]; congr 2; omega
  · rw [pIter_mem hk h pBack rfl A hA, if_neg (by so), if_neg (by so)]
    exact h.frame.get hA (by so)
theorem pLoop {im : Image} (hl : LookOK im cLook) {s0 u : MachineState} (h0 : PInv s0 0 u) :
    ∀ k, k ≤ 147 → ∃ t, Steps im u (7 * k) (7 * k) t ∧ PInv s0 k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨t, st, ht⟩ := ih (by so)
    obtain ⟨st1, -⟩ := run_sound hl run_pBack t ht.pc
      (cLoopObl_holds t _ _ (by so) (by so) (by so) (by so) ht.x28 ht.x29)
      (by
        intro b hb
        simp only [pBack, List.mem_singleton] at hb
        subst hb
        exact cBr_holds t _ true (by so) ht.x28 ht.x30 (by simp; omega))
    exact ⟨_, (st.trans st1).of_eq (by simp [pBack]; ring) (by simp [pBack]; ring),
      pIter_inv (by so) ht _ rfl⟩
theorem compactGood (im : Image) : CompactGood im := by
  intro hnew hhooks s hpc
  have hlt := tailLook_ok hnew
  have hlh := hookLook_ok hhooks
  have hlc := cLook_ok hnew hhooks
  obtain ⟨s1, -⟩ := run_sound hlh run_cHook s hpc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u1 := cHook.toState s with hu1
  have u1pc : u1.pc = pcOf 20730 := PRes.toState_pc' _ _ rfl
  obtain ⟨s2, -⟩ := run_sound hlc run_pSetup u1 u1pc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u2 := pSetup.toState u1 with hu2
  have h0 : PInv s 0 u2 := by
    refine ⟨PRes.toState_pc' _ _ rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => by so, fun A _ _ => rfl⟩
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
  obtain ⟨t, st, ht⟩ := pLoop hlc h0 147 le_rfl
  obtain ⟨s3, -⟩ := run_sound hlc run_pExit t ht.pc
    (pExitObl_holds t _ _ (by so) (by so) (by so) (by so) ht.x28 ht.x29)
    (by
      intro b hb
      simp only [pExit, List.mem_singleton] at hb
      subst hb
      exact cBr_holds t _ false (by so) ht.x28 ht.x30 (by simp))
  set u3 := pExit.toState t with hu3
  have u3pc : u3.pc = pcOf 20736 := PRes.toState_pc' _ _ rfl
  have u3get : ∀ A, A < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 A) =
      if A = SIG + 5608 then s.getMem (BitVec.ofNat 64 (SIG + 3240))
      else if A = SIG + 5600 then s.getMem (BitVec.ofNat 64 (SIG + 3232))
      else if A = SIG + 5592 then s.getMem (BitVec.ofNat 64 (SIG + 5608))
      else if A = SIG + 5584 then s.getMem (BitVec.ofNat 64 (SIG + 5600))
      else t.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu3, PRes.toState_getMem']
    show memEval t pExitMem (BitVec.ofNat 64 A) = _
    rw [pExitMem_get t (SIG + 3248 + 16 * 147) (SIG + 3232 + 16 * 147) A (by so) hA ht.x28 ht.x29, ht.x15, ht.x14,
      ht.frame.get (A := SIG + 3248 + 16 * 147 + 8) (by so) (by so),
      ht.frame.get (A := SIG + 3248 + 16 * 147) (by so) (by so)]
    try rfl
  have u3frame : Frame s u3 (fun A => SIG + 3232 ≤ A ∧ A < SIG + 5616) := fun A hA hn => by
    rw [u3get A hA, if_neg (by so), if_neg (by so), if_neg (by so), if_neg (by so)]
    exact ht.frame.get hA (by so)
  have u3mem : ∀ k < 428, u3.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * cpIdx (k / 2) + 8 * (k % 2))) := by
    intro k hk
    rw [u3get _ (by so)]
    unfold cpIdx
    by_cases k1 : k = 427
    · subst k1; rw [if_pos (by so)]; rfl
    by_cases k2 : k = 426
    · subst k2; rw [if_neg (by so), if_pos (by so)]; rfl
    by_cases k3 : k = 425
    · subst k3; rw [if_neg (by so), if_neg (by so), if_pos (by so)]; rfl
    by_cases k4 : k = 424
    · subst k4; rw [if_neg (by so), if_neg (by so), if_neg (by so), if_pos (by so)]; rfl
    rw [if_neg (by so), if_neg (by so), if_neg (by so), if_neg (by so)]
    by_cases hlo : k < 130
    · rw [ht.frame.get (by so) (by so), if_pos (show k / 2 < 65 by omega)]
      congr 2; omega
    · have hd := ht.done (k - 130) (by omega)
      rw [show SIG + 3232 + 8 * (k - 130) = SIG + 2192 + 8 * k by so] at hd
      rw [hd, if_neg (show ¬ k / 2 < 65 by omega), if_pos (show k / 2 < 213 by omega)]
      rw [show SIG + 3248 + 8 * (k - 130) = SIG + 2192 + 16 * (k / 2 + 1) + 8 * (k % 2) by so]
  have h0' : CInv u3 0 u3 := by
    refine ⟨u3pc, ?_, ?_, ?_, fun j hj => by so, Frame.refl _ _⟩
    · rw [hu3, PRes.toState_getReg']; rfl
    · rw [hu3, PRes.toState_getReg']; rfl
    · rw [hu3, PRes.toState_getReg']; rfl
  obtain ⟨t', st', ht'⟩ := cLoop hlt h0' 213 le_rfl
  obtain ⟨s4, -⟩ := run_sound hlt run_cExit t' ht'.pc
    (cLoopObl_holds t' _ _ (by so) (by so) (by so)
      (by so) ht'.x28 ht'.x29)
    (by
      intro b hb
      simp only [cExit, List.mem_singleton] at hb
      subst hb
      exact cBr_holds t' _ false (by so) ht'.x28 ht'.x30 (by simp))
  have hfin : ∀ k < 428, (cExit.toState t').getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * k)) =
      u3.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * k)) := by
    intro k hk
    rw [cIter_mem (by so) ht' cExit rfl _ (by so)]
    by_cases hk2 : k < 2 * 213
    · rw [if_neg (by so), if_neg (by so)]; exact ht'.done k hk2
    · by_cases hke : k = 2 * 213
      · subst hke; rw [if_neg (by so), if_pos (by so)]
      · have : k = 2 * 213 + 1 := by so
        subst this; rw [if_pos (by so)]
  refine ⟨cExit.toState t', ((s1.trans s2).trans ((st.trans s3).trans (st'.trans s4))).of_eq
    (by simp [cHook, pSetup, pExit, cExit, compactK]) (by simp [cHook, pSetup, pExit, cExit, compactK]),
    PRes.toState_pc' _ _ rfl, ?_, ?_, fun k hk => (hfin k hk).trans (u3mem k hk), fun A hA hn => ?_⟩
  · rw [PRes.toState_getReg']; rfl
  · rw [PRes.toState_getReg']; rfl
  · rw [cIter_mem (by so) ht' cExit rfl A hA, if_neg (by so), if_neg (by so),
      ht'.frame.get hA (by so), u3frame.get hA (by so)]
end ClaudeWCT.W9.Machine.Sign
end

section




namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
-- (witness stack) removed: signMain / sign_refines_w / sign_terminates_w (legacy SignMain over the reference FTS).
theorem newCodeAt_of_drop {im : Image} (h : im.code.drop 11003 = signNew)
    (h2 : signTramp <+: im.code.drop 21450) (ha : arenaCode <+: im.code.drop 1700) : NewCodeAt im := by
  rw [NewCodeAt, h]; exact ⟨List.prefix_refl _, h2, ha⟩
end ClaudeWCT.W9.Machine.Sign
end

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def code22128 : List (BitVec 32) := bv_list% 32 [0x21137,0x10113,0xf93,0x2b00d13,0xd93,0x8837,0xcb080813,0x700793,0xfff40313,0x2030063]
sym_block blk22128 := symRun { noAlias := true } code22128 (pcOf 22128) 100
def code22138 : List (BitVec 32) := bv_list% 32 [0x600793,0x8837,0xfd080813,0xffe40313,0x30663]
sym_block blk22138 := symRun { noAlias := true } code22138 (pcOf 22138) 100
def code22143 : List (BitVec 32) := bv_list% 32 [0x8837,0x2e080813]
sym_block blk22143 := symRun { noAlias := true } code22143 (pcOf 22143) 100
def code22145 : List (BitVec 32) := bv_list% 32 [0x20e37,0x550e0e13,0xe3303,0xfff40393,0x38c63]
sym_block blk22145 := symRun { noAlias := true } code22145 (pcOf 22145) 100
def code22150 : List (BitVec 32) := bv_list% 32 [0xffe40393,0x2038063]
sym_block blk22150 := symRun { noAlias := true } code22150 (pcOf 22150) 100
def code22152 : List (BitVec 32) := bv_list% 32 [0x3f37913,0x635493,0x200006f]
sym_block blk22152 := symRun { noAlias := true } code22152 (pcOf 22152) 100
def code22155 : List (BitVec 32) := bv_list% 32 [0xc35913,0x7f97913,0x1335493,0x100006f]
sym_block blk22155 := symRun { noAlias := true } code22155 (pcOf 22155) 100
def code22159 : List (BitVec 32) := bv_list% 32 [0x635913,0x3f97913,0xc35493]
sym_block blk22159 := symRun { noAlias := true } code22159 (pcOf 22159) 100
def code22162 : List (BitVec 32) := bv_list% 32 [0x90713,0x809eb0ef]
sym_block blk22162 := symRun { noAlias := true } code22162 (pcOf 22162) 100
structure Code (im : Image) : Prop where
  at22128 : CodeAt im (pcOf 22128) code22128
  at22138 : CodeAt im (pcOf 22138) code22138
  at22143 : CodeAt im (pcOf 22143) code22143
  at22145 : CodeAt im (pcOf 22145) code22145
  at22150 : CodeAt im (pcOf 22150) code22150
  at22152 : CodeAt im (pcOf 22152) code22152
  at22155 : CodeAt im (pcOf 22155) code22155
  at22159 : CodeAt im (pcOf 22159) code22159
  at22162 : CodeAt im (pcOf 22162) code22162
def sigBase (lay : Nat) : Nat := if lay=1 then 0x7cb0 else if lay=2 then 0x7fd0 else 0x82e0
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 1173
  ret : t.getReg .x1=pcOf 22164
  rootBase : t.getReg .x2=BitVec.ofNat 64 LOW
  so : t.getReg .x31=0
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  sigBase : t.getReg .x16=BitVec.ofNat 64 (SharedRootControl.sigBase lay)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  regs : RegsExcept s t [.x1,.x2,.x6,.x7,.x9,.x14,.x15,.x16,.x18,.x26,.x27,.x28,.x31]
  frame : Frame s t (fun _ => False)
theorem setup1 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=1)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 21 21 t ∧ Post 1 index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  let s1 := blk22128.res.toState s
  have st1 : Steps im s 10 10 s1 := symRun_sound blk22128 hc.at22128 s hp (by simp [blk22128.res,rv_simp])
  let s2 := blk22145.res.toState s1
  have st2 : Steps im s1 5 5 s2 := symRun_sound blk22145 hc.at22145 s1 (by simp [s1,s2,blk22128.res,blk22145.res,rv_simp,h8]) (by simp [blk22145.res,rv_simp])
  let s3 := blk22155.res.toState s2
  have st3 : Steps im s2 4 4 s3 := symRun_sound blk22155 hc.at22155 s2 (by simp [s1,s2,s3,blk22128.res,blk22145.res,blk22155.res,rv_simp,h8]) (by simp [blk22155.res,rv_simp])
  let s4 := blk22162.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22162 hc.at22162 s3 (by simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8]) (by simp [blk22162.res,rv_simp])
  refine ⟨s4, st1.trans (st2.trans (st3.trans (st4))), ?_⟩
  constructor
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change (BitVec.ofNat 64 index >>> (12 : Nat) &&& 127) = BitVec.ofNat 64 (index/2^12%2^7)
    rw [ofNat_shr index 12 (by omega)]
    exact ofNat_and_mask (index/2^12) 7 (by decide)
  · simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change BitVec.ofNat 64 index >>> (19 : Nat) = BitVec.ofNat 64 (index/2^19)
    exact ofNat_shr index 19 (by omega)
  · intro r hr; cases r <;> simp_all [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW] <;> rfl
  · intro A hA hn; simp [s1,s2,s3,s4,blk22128.res,blk22145.res,blk22155.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
theorem setup2 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=2)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 27 27 t ∧ Post 2 index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  let s1 := blk22128.res.toState s
  have st1 : Steps im s 10 10 s1 := symRun_sound blk22128 hc.at22128 s hp (by simp [blk22128.res,rv_simp])
  let s2 := blk22138.res.toState s1
  have st2 : Steps im s1 5 5 s2 := symRun_sound blk22138 hc.at22138 s1 (by simp [s1,s2,blk22128.res,blk22138.res,rv_simp,h8]) (by simp [blk22138.res,rv_simp])
  let s3 := blk22145.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22145 hc.at22145 s2 (by simp [s1,s2,s3,blk22128.res,blk22138.res,blk22145.res,rv_simp,h8]) (by simp [blk22145.res,rv_simp])
  let s4 := blk22150.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22150 hc.at22150 s3 (by simp [s1,s2,s3,s4,blk22128.res,blk22138.res,blk22145.res,blk22150.res,rv_simp,h8]) (by simp [blk22150.res,rv_simp])
  let s5 := blk22159.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22159 hc.at22159 s4 (by simp [s1,s2,s3,s4,s5,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,rv_simp,h8]) (by simp [blk22159.res,rv_simp])
  let s6 := blk22162.res.toState s5
  have st6 : Steps im s5 2 2 s6 := symRun_sound blk22162 hc.at22162 s5 (by simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8]) (by simp [blk22162.res,rv_simp])
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change (BitVec.ofNat 64 index >>> (6 : Nat) &&& 63) = BitVec.ofNat 64 (index/2^6%2^6)
    rw [ofNat_shr index 6 (by omega)]
    exact ofNat_and_mask (index/2^6) 6 (by decide)
  · simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change BitVec.ofNat 64 index >>> (12 : Nat) = BitVec.ofNat 64 (index/2^12)
    exact ofNat_shr index 12 (by omega)
  · intro r hr; cases r <;> simp_all [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW] <;> rfl
  · intro A hA hn; simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22145.res,blk22150.res,blk22159.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
theorem setup3 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=3)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 29 29 t ∧ Post 3 index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  let s1 := blk22128.res.toState s
  have st1 : Steps im s 10 10 s1 := symRun_sound blk22128 hc.at22128 s hp (by simp [blk22128.res,rv_simp])
  let s2 := blk22138.res.toState s1
  have st2 : Steps im s1 5 5 s2 := symRun_sound blk22138 hc.at22138 s1 (by simp [s1,s2,blk22128.res,blk22138.res,rv_simp,h8]) (by simp [blk22138.res,rv_simp])
  let s3 := blk22143.res.toState s2
  have st3 : Steps im s2 2 2 s3 := symRun_sound blk22143 hc.at22143 s2 (by simp [s1,s2,s3,blk22128.res,blk22138.res,blk22143.res,rv_simp,h8]) (by simp [blk22143.res,rv_simp])
  let s4 := blk22145.res.toState s3
  have st4 : Steps im s3 5 5 s4 := symRun_sound blk22145 hc.at22145 s3 (by simp [s1,s2,s3,s4,blk22128.res,blk22138.res,blk22143.res,blk22145.res,rv_simp,h8]) (by simp [blk22145.res,rv_simp])
  let s5 := blk22150.res.toState s4
  have st5 : Steps im s4 2 2 s5 := symRun_sound blk22150 hc.at22150 s4 (by simp [s1,s2,s3,s4,s5,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,rv_simp,h8]) (by simp [blk22150.res,rv_simp])
  let s6 := blk22152.res.toState s5
  have st6 : Steps im s5 3 3 s6 := symRun_sound blk22152 hc.at22152 s5 (by simp [s1,s2,s3,s4,s5,s6,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,rv_simp,h8]) (by simp [blk22152.res,rv_simp])
  let s7 := blk22162.res.toState s6
  have st7 : Steps im s6 2 2 s7 := symRun_sound blk22162 hc.at22162 s6 (by simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8]) (by simp [blk22162.res,rv_simp])
  refine ⟨s7, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6.trans (st7)))))), ?_⟩
  constructor
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change (BitVec.ofNat 64 index &&& 63) = BitVec.ofNat 64 (index%2^6)
    exact ofNat_and_mask index 6 (by decide)
  · simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
  · simp only [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
    change BitVec.ofNat 64 index >>> (6 : Nat) = BitVec.ofNat 64 (index/2^6)
    exact ofNat_shr index 6 (by omega)
  · intro r hr; cases r <;> simp_all [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW] <;> rfl
  · intro A hA hn; simp [s1,s2,s3,s4,s5,s6,s7,blk22128.res,blk22138.res,blk22143.res,blk22145.res,blk22150.res,blk22152.res,blk22162.res,rv_simp,h8,hidx,sigBase,LOW]
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open Packed
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem setup {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22128)
    (lay : Layer) (hlay : lay≠0) (index : Nat) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t k, Steps im s k k t ∧ k≤29 ∧ Post lay.val index s t := by
  fin_cases lay
  · exact (hlay rfl).elim
  · obtain ⟨t,hs,hp⟩ := setup1 hc s hp index hi h8 hidx
    exact ⟨t,21,hs,by decide,hp⟩
  · obtain ⟨t,hs,hp⟩ := setup2 hc s hp index hi h8 hidx
    exact ⟨t,27,hs,by decide,hp⟩
  · obtain ⟨t,hs,hp⟩ := setup3 hc s hp index hi h8 hidx
    exact ⟨t,29,hs,by decide,hp⟩

theorem Post.btPre {sk : SecretKey} {cache : Bytes 131072} {s t : MachineState}
    {lay : Layer} (hlay : lay≠0) {index : Nat} (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0)
    (h : Post lay.val index s t) :
    BtPre (cfFlag := cfFlag) sk cache lay (route index lay).2 (route index lay).1 [] (SharedRootControl.sigBase lay.val) t := by
  have leafEq : (if lay.val=1 then index/4096%128 else if lay.val=2 then index/64%64 else index%64)=(route index lay).1 := by
    fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height]
  have treeEq : (if lay.val=1 then index/524288 else if lay.val=2 then index/4096 else index/64)=(route index lay).2 := by
    fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height]
  have heightEq : (if lay.val=1 then 7 else 6)=SigGolfCandidate.T3.height lay := by
    fin_cases lay <;> simp_all [SigGolfCandidate.T3.height]
  refine
    { x2 := h.rootBase
      x8 := (h.regs.get (by decide)).trans h8
      x9 := by rw [h.tree,treeEq]
      x14 := by rw [h.selected,h.leaf,leafEq]
      x15 := by rw [h.height,heightEq]
      x16 := h.sigBase
      x26 := h.chains
      x27 := h.n4
      x31 := h.so
      base := hb.frame h.frame h.regs (by decide) (fun _ _ _ he => he)
      hlay := hlay
      htree := by fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height] <;> omega
      hroute := by intro l hl; fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height] <;> omega
      hsel := by fin_cases lay <;> simp_all [route,SigGolfCandidate.T3.height] <;> omega
      hdb := by simp
      digits := by intro i hi; rw [h.frame.getByte (by unfold DIGITS; omega) (fun he => he)]; simpa using hz i hi
      hsb := by fin_cases lay <;> simp_all [SharedRootControl.sigBase,SigGolfCandidate.T3.height,SIG] <;> decide
      hsb8 := by fin_cases lay <;> decide }
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def frontCode : List (BitVec 32) := bv_list% 32 [0x300413,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block front := symRun { noAlias := true } frontCode (pcOf 22100) 100
def zeroCode : List (BitVec 32) := bv_list% 32 [0x20e37,0x420e0e13,0xe3023,0xe3423,0xe3823,0xe3c23,0x20e3023,0x20e3423,0x20e3823]
sym_block zero := symRun { noAlias := true } zeroCode (pcOf 22115) 100
def hintCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xe3023,0x100413]
sym_block hint := symRun { noAlias := true } hintCode (pcOf 22124) 100
def donePrepCode : List (BitVec 32) := bv_list% 32 [0xfff40f13,0x66eb7,0x40e8e93,0x5f1393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block donePrep := symRun { noAlias := true } donePrepCode (pcOf 22164) 100
def doneExitCode : List (BitVec 32) := bv_list% 32 [0x140413,0x400313,0xf26466e3]
sym_block doneExit := symRun { noAlias := true } doneExitCode (pcOf 22179) 100
theorem front_steps {im : Image} (hc : CodeAt im (pcOf 22100) frontCode)
    (s : MachineState) (hp : s.pc=pcOf 22100) :
    ∃ t, Steps im s 7 7 t ∧ t.pc=pcOf 22107 ∧ t.getReg .x8=3 ∧
      t.getReg .x28=BitVec.ofNat 64 ENC ∧ t.getReg .x29=BitVec.ofNat 64 (0x66000+160) ∧
      RegsExcept s t [.x7,.x8,.x28,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound front hc s hp (by simp [front.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [front.res,rv_simp]
  · simp [front.res,rv_simp]
  · simp [front.res,rv_simp,ENC]
  · simp [front.res,rv_simp]
  · intro r hr; cases r <;> simp_all [front.res,rv_simp] <;> rfl
  · intro A hA hn; simp [front.res,rv_simp]

theorem zero_steps {im : Image} (hc : CodeAt im (pcOf 22115) zeroCode)
    (s : MachineState) (hp : s.pc=pcOf 22115) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 22124 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=0) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56) := by
  refine ⟨_,symRun_sound zero hc s hp (by simp [zero.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero.res,rv_simp]
  · intro i hi; interval_cases i <;> simp [zero.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp_all [zero.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,zero.res]
    t3n [DIGITS]
    repeat rw [if_neg (by unfold DIGITS at hn; omega)]

theorem hint_steps {im : Image} (hc : CodeAt im (pcOf 22124) hintCode)
    (s : MachineState) (hp : s.pc=pcOf 22124) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf 22128 ∧ t.getReg .x8=1 ∧ t.getMem (0x66000#64)=0 ∧
      RegsExcept s t [.x8,.x28] ∧ Frame s t (fun A => A=0x66000) := by
  refine ⟨_,symRun_sound hint hc s hp (by simp [hint.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [hint.res,rv_simp]
  · simp [hint.res,rv_simp]
  · simp [hint.res,rv_simp]
  · intro r hr; cases r <;> simp_all [hint.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,hint.res]
    t3n []
    rw [if_neg (by omega)]

theorem donePrep_steps {im : Image} (hc : CodeAt im (pcOf 22164) donePrepCode)
    (s : MachineState) (hp : s.pc=pcOf 22164) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 7 7 t ∧ t.pc=pcOf 22171 ∧ t.getReg .x28=BitVec.ofNat 64 ENC ∧
      t.getReg .x29=BitVec.ofNat 64 (0x66000+64+32*(lay-1)) ∧
      RegsExcept s t [.x7,.x28,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound donePrep hc s hp (by simp [donePrep.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [donePrep.res,rv_simp]
  · simp [donePrep.res,rv_simp,ENC]
  · interval_cases lay <;> simp_all [donePrep.res,rv_simp]
  · intro r hr; cases r <;> simp_all [donePrep.res,rv_simp] <;> rfl
  · intro A hA hn; simp [donePrep.res,rv_simp]

theorem doneExit_steps {im : Image} (hc : CodeAt im (pcOf 22179) doneExitCode)
    (s : MachineState) (hp : s.pc=pcOf 22179) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22128 else pcOf 22182) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧
      RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound doneExit hc s hp (by simp [doneExit.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [doneExit.res,rv_simp,pcOf]
  · interval_cases lay <;> simp_all [doneExit.res,rv_simp]
  · intro r hr; cases r <;> simp_all [doneExit.res,rv_simp] <;> rfl
  · intro A hA hn; simp [doneExit.res,rv_simp]
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def copy22107Code : List (BitVec 32) := bv_list% 32 [0xe3303,0x8e3383,0x6eb023,0x7eb423,0x30e3303,0x38e3383,0x6eb823,0x7ebc23]
sym_block copy22107 := symRun { noAlias := true } copy22107Code (pcOf 22107) 100
theorem copy22107_steps {im : Image} (hc : CodeAt im (pcOf 22107) copy22107Code)
    (s : MachineState) (hp : s.pc=pcOf 22107) (dest : Nat) (ha : 0x66000≤dest) (hb : dest+32≤0x66200) (ha8 : dest%8=0)
    (hd : dest=0x66040 ∨ dest=0x66060 ∨ dest=0x66080 ∨ dest=0x660a0)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC) (h29 : s.getReg .x29=BitVec.ofNat 64 dest)
    (left right : Digest) (hl : DigAt s ENC left) (hr : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 8 8 t ∧ t.pc=pcOf 22115 ∧ DigAt t dest left ∧ DigAt t (dest+16) right ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => dest≤A ∧ A<dest+32) := by
  rcases hd with rfl|rfl|rfl|rfl
  all_goals
    have ho : Oblig.all s copy22107.res.st.obl := by
      simp [copy22107.res,rv_simp,h28,h29,ENC]
      decide
    refine ⟨_,symRun_sound copy22107 hc s hp ho,?_,?_,?_,?_,?_⟩
    · simp [copy22107.res,rv_simp]
    · constructor
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.1
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.2
    · constructor
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.1
      · simp only [Result.toState_getMem,copy22107.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.2
    · intro r hr; cases r <;> simp at hr <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem,copy22107.res]
      t3n [h28,h29,ENC]
      repeat rw [if_neg (by omega)]
def copy22171Code : List (BitVec 32) := bv_list% 32 [0xe3303,0x8e3383,0x6eb023,0x7eb423,0x30e3303,0x38e3383,0x6eb823,0x7ebc23]
sym_block copy22171 := symRun { noAlias := true } copy22171Code (pcOf 22171) 100
theorem copy22171_steps {im : Image} (hc : CodeAt im (pcOf 22171) copy22171Code)
    (s : MachineState) (hp : s.pc=pcOf 22171) (dest : Nat) (ha : 0x66000≤dest) (hb : dest+32≤0x66200) (ha8 : dest%8=0)
    (hd : dest=0x66040 ∨ dest=0x66060 ∨ dest=0x66080 ∨ dest=0x660a0)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC) (h29 : s.getReg .x29=BitVec.ofNat 64 dest)
    (left right : Digest) (hl : DigAt s ENC left) (hr : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 8 8 t ∧ t.pc=pcOf 22179 ∧ DigAt t dest left ∧ DigAt t (dest+16) right ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => dest≤A ∧ A<dest+32) := by
  rcases hd with rfl|rfl|rfl|rfl
  all_goals
    have ho : Oblig.all s copy22171.res.st.obl := by
      simp [copy22171.res,rv_simp,h28,h29,ENC]
      decide
    refine ⟨_,symRun_sound copy22171 hc s hp ho,?_,?_,?_,?_,?_⟩
    · simp [copy22171.res,rv_simp]
    · constructor
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.1
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hl
        exact hl.2
    · constructor
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.1
      · simp only [Result.toState_getMem,copy22171.res]
        t3n [h28,h29,ENC]
        repeat first | rw [if_neg (by omega)] | rw [if_pos (by omega)]
        simp only [DigAt,ENC] at hr
        exact hr.2
    · intro r hr; cases r <;> simp at hr <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem,copy22171.res]
      t3n [h28,h29,ENC]
      repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure ExtraCode (im : Image) : Prop where
  front : CodeAt im (pcOf 22100) frontCode
  copyA : CodeAt im (pcOf 22107) copy22107Code
  zero : CodeAt im (pcOf 22115) zeroCode
  hint : CodeAt im (pcOf 22124) hintCode
  donePrep : CodeAt im (pcOf 22164) donePrepCode
  copyB : CodeAt im (pcOf 22171) copy22171Code
  doneExit : CodeAt im (pcOf 22179) doneExitCode

theorem entry_steps {im : Image} (hc : ExtraCode im)
    (s : MachineState) (hp : s.pc=pcOf 22100) (left right : Digest)
    (hl : DigAt s ENC left) (hr : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 28 28 t ∧ t.pc=pcOf 22128 ∧ t.getReg .x8=1 ∧
      DigAt t (0x66000+160) left ∧ DigAt t (0x66000+176) right ∧
      t.getMem (0x66000#64)=0 ∧
      (∀ i,i<43 → t.getByte (BitVec.ofNat 64 (DIGITS+i))=0) ∧
      RegsExcept s t [.x6,.x7,.x8,.x28,.x29] ∧
      Frame s t (fun A => A=0x66000 ∨ 0x66000+160≤A ∧ A<0x66000+192 ∨ DIGITS≤A ∧ A<DIGITS+56) := by
  obtain ⟨a,sa,pa,a8,a28,a29,ar,af⟩ := front_steps hc.front s hp
  obtain ⟨b,ab,pb,bl,br,brs,bf⟩ := copy22107_steps hc.copyA a pa (0x66000+160)
    (by decide) (by decide) (by decide) (by decide) a28 a29 left right
    (hl.frame af (by decide) (fun h => h) (fun h => h))
    (hr.frame af (by decide) (fun h => h) (fun h => h))
  obtain ⟨c,bc,pc,cz,cr,cf⟩ := zero_steps hc.zero b pb
  obtain ⟨t,ct,pt,t8,th,tr,tf⟩ := hint_steps hc.hint c pc
  have ft : Frame b t (fun A => DIGITS≤A ∧ A<DIGITS+56 ∨ A=0x66000) := (cf.trans tf).mono (by tauto)
  refine ⟨t,sa.trans (ab.trans (bc.trans ct)),pt,t8,?_,?_,th,?_,?_,?_⟩
  · exact bl.frame ft (by decide) (by unfold DIGITS; omega) (by unfold DIGITS; omega)
  · exact br.frame ft (by decide) (by unfold DIGITS; omega) (by unfold DIGITS; omega)
  · intro i hi
    rw [tf.getByte (by unfold DIGITS; omega) (by unfold DIGITS; omega)]
    rw [getByte_eq_word c (DIGITS+i) (by unfold DIGITS; omega)]
    rw [show (DIGITS+i)/8*8=DIGITS+8*(i/8) by unfold DIGITS; omega,cz _ (by omega)]
    simp [extractByte]
  · exact (((ar.trans brs).trans cr).trans tr).mono (by simp)
  · exact (((af.trans bf).trans cf).trans tf).mono (by intros A hA hw; rcases hw with ((hw|hw)|hw)|hw <;> tauto)

theorem done_steps {im : Image} (hc : ExtraCode im)
    (s : MachineState) (hp : s.pc=pcOf 22164) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (left right : Digest)
    (hleft : DigAt s ENC left) (hright : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=(if lay<3 then pcOf 22128 else pcOf 22182) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧
      DigAt t (0x66000+64+32*(lay-1)) left ∧ DigAt t (0x66000+80+32*(lay-1)) right ∧
      RegsExcept s t [.x6,.x7,.x8,.x28,.x29,.x30] ∧
      Frame s t (fun A => 0x66000+64+32*(lay-1)≤A ∧ A<0x66000+96+32*(lay-1)) := by
  obtain ⟨a,sa,pa,a28,a29,ar,af⟩ := donePrep_steps hc.donePrep s hp lay hl hh h8
  obtain ⟨b,ab,pb,bl,br,brs,bf⟩ := copy22171_steps hc.copyB a pa (0x66000+64+32*(lay-1))
    (by omega) (by omega) (by omega) (by interval_cases lay <;> decide) a28 a29 left right
    (hleft.frame af (by decide) (fun h => h) (fun h => h))
    (hright.frame af (by decide) (fun h => h) (fun h => h))
  have b8 : b.getReg .x8=BitVec.ofNat 64 lay := (brs.get (by decide)).trans ((ar.get (by decide)).trans h8)
  obtain ⟨t,bt,pt,t8,tr,tf⟩ := doneExit_steps hc.doneExit b pb lay hl hh b8
  refine ⟨t,sa.trans (ab.trans bt),pt,t8,bl.frame tf (by omega) (fun h => h) (fun h => h),?_,?_,?_⟩
  · have h := br.frame tf (by omega) (fun h => h) (fun h => h)
    convert h using 1 <;> omega
  · exact ((ar.trans brs).trans tr).mono (by simp)
  · exact ((af.trans bf).trans tf).mono (by
      intros A hA hw
      rcases hw with (hw|hw)|hw
      · exact hw.elim
      · omega
      · exact hw.elim)
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_extraCode : ExtraCode Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
abbrev buffer (lay i d : Nat) : Nat := 0x6e000+8192*lay+128*i+16*d
def stepCode : List (BitVec 32) := bv_list% 32 [0x431313,0x6c0e33,0xe3303,0x8e3383,0x6bb023,0x7bb423,0x1b0b13,0x10b8b93,0x80c0c13,0x1a8a93,0x2b00313,0xfc6ae8e3]
sym_block step := symRun { noAlias := true } stepCode (pcOf 22436) 100

theorem step_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (s : MachineState) (hp : s.pc=pcOf 22436) (lay i d sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hi : i<43) (hd : d<8)
    (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (h6 : s.getReg .x6=BitVec.ofNat 64 d) (h21 : s.getReg .x21=BitVec.ofNat 64 i)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (h23 : s.getReg .x23=BitVec.ofNat 64 (sb+16*i))
    (h24 : s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0)) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=(if i+1<43 then pcOf 22435 else pcOf 22448) ∧
      t.getReg .x21=BitVec.ofNat 64 (i+1) ∧ t.getReg .x22=BitVec.ofNat 64 (DIGITS+i+1) ∧
      t.getReg .x23=BitVec.ofNat 64 (sb+16*(i+1)) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay (i+1) 0) ∧
      t.getMem (BitVec.ofNat 64 (sb+16*i))=s.getMem (BitVec.ofNat 64 (buffer lay i d)) ∧
      t.getMem (BitVec.ofNat 64 (sb+16*i+8))=s.getMem (BitVec.ofNat 64 (buffer lay i d+8)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => A=sb+16*i ∨ A=sb+16*i+8) := by
  have ho : Oblig.all s step.res.st.obl := by
    simp only [step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    omega
  refine ⟨_,symRun_sound step hc s hp ho,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS,pcOf]
    simp [BitVec.ult,toNat_ofNat_lt (show i+1<2^64 by omega)]
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    omega
  · simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    rw [if_neg (by omega),if_pos (by omega)]
    simp [Nat.mul_comm]
  · simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    simp [Nat.mul_comm]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    rw [if_neg (by omega),if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem byte_steps {im : Image} (hc : CodeAt im (pcOf 22435) [0xb4303])
    (s : MachineState) (hp : s.pc=pcOf 22435) (i d : Nat) (hi : i<43) (hd : d<8)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 d) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22436 ∧ t.getReg .x6=BitVec.ofNat 64 d ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hoff : s.getReg .x22+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 (DIGITS+i) := by
    rw [h22]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have st := steps_lbu (rd := .x6) (rs := .x22) (off := 0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by unfold DIGITS; omega)]; simp [MEMORY_BYTES,DIGITS]; omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 22436; rw [hp]; rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn; simp

theorem iteration_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303])
    (s : MachineState) (hp : s.pc=pcOf 22435) (lay i d sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hi : i<43) (hd : d<8)
    (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (h21 : s.getReg .x21=BitVec.ofNat 64 i)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (h23 : s.getReg .x23=BitVec.ofNat 64 (sb+16*i))
    (h24 : s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 d)
    (v : Digest) (hv : DigAt s (buffer lay i d) v) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=(if i+1<43 then pcOf 22435 else pcOf 22448) ∧
      t.getReg .x21=BitVec.ofNat 64 (i+1) ∧ t.getReg .x22=BitVec.ofNat 64 (DIGITS+i+1) ∧
      t.getReg .x23=BitVec.ofNat 64 (sb+16*(i+1)) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay (i+1) 0) ∧
      DigAt t (sb+16*i) v ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => A=sb+16*i ∨ A=sb+16*i+8) := by
  obtain ⟨a,sa,ap,a6,ar,af⟩ := byte_steps hbcode s hp i d hi hd h22 hb
  obtain ⟨t,aToT,tp,t21,t22,t23,t24,tl,tr,ts,tf⟩ := step_steps hc a ap lay i d sb hl hh hi hd hsb hsb' hsb8
    a6 ((ar.get (by decide)).trans h21) ((ar.get (by decide)).trans h22)
    ((ar.get (by decide)).trans h23) ((ar.get (by decide)).trans h24)
  have va := hv.frame af (by unfold buffer; omega) (fun h => h) (fun h => h)
  exact ⟨t,sa.trans aToT,tp,t21,t22,t23,t24,⟨tl.trans va.1,tr.trans va.2⟩,
    (ar.trans ts).mono (by simp),(af.trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem loop_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (lay sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (digits : Nat→Nat) (prefixes : Nat→Nat→Digest) (hd : ∀ j,j<43 → digits j<8) :
    ∀ count i, i+count=43 → ∀ s : MachineState,
      s.pc=(if i<43 then pcOf 22435 else pcOf 22448) →
      s.getReg .x21=BitVec.ofNat 64 i → s.getReg .x22=BitVec.ofNat 64 (DIGITS+i) →
      s.getReg .x23=BitVec.ofNat 64 (sb+16*i) →
      s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0) →
      (∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits j)) →
      (∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay j d) (prefixes j d)) →
      ∃ t, Steps im s (13*count) (13*count) t ∧ t.pc=pcOf 22448 ∧
        (∀ j,i≤j → j<43 → DigAt t (sb+16*j) (prefixes j (digits j))) ∧
        RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
        Frame s t (fun A => sb+16*i≤A ∧ A<sb+16*43) := by
  intro count
  induction count with
  | zero =>
      intro i hi s hp h21 h22 h23 h24 hb hv
      have hi' : i=43 := by omega
      refine ⟨s,Steps.refl _,by simpa [hi'] using hp,?_,?_,?_⟩
      · intro j hj hj'; omega
      · intro r hr; rfl
      · intro A hA hn; rfl
  | succ count ih =>
      intro i hcount s hp h21 h22 h23 h24 hb hv
      have hi : i<43 := by omega
      obtain ⟨a,sa,ap,a21,a22,a23,a24,av,ar,af⟩ := iteration_steps hc hbcode s
        (by simpa [hi] using hp) lay i (digits i) sb hl hh hi (hd i hi) hsb hsb' hsb8
        h21 h22 h23 h24 (hb i hi) (prefixes i (digits i)) (hv i hi _ (hd i hi))
      obtain ⟨t,aToT,tp,tv,tr,tf⟩ := ih (i+1) (by omega) a ap a21
        (by simpa [Nat.add_assoc] using a22) a23 a24
        (by
          intro j hj
          rw [af.getByte (by unfold DIGITS; omega) (by unfold DIGITS; omega)]
          exact hb j hj)
        (by
          intro j hj d hd
          exact (hv j hj d hd).frame af (by unfold buffer; omega)
            (by unfold buffer; omega) (by unfold buffer; omega))
      refine ⟨t,?_,tp,?_,(ar.trans tr).mono (by simp),?_⟩
      · convert sa.trans aToT using 1 <;> omega
      · intro j hij hj
        by_cases he : j=i
        · subst j
          exact av.frame tf (by omega) (by omega) (by omega)
        · exact tv j (by omega) hj
      · exact (af.trans tf).mono (by intro A hA h; rcases h with h|h <;> omega)
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def metaAddr (lay : Layer) : Nat := 0x66000+64+32*(lay.val-1)
def metaW (lay : Layer) (A : Nat) : Prop := metaAddr lay≤A ∧ A < metaAddr lay+32
structure Stored (lay : Layer) (index : Nat) (p : PreparedLower) (t : MachineState) : Prop where
  plen : p.prefixes.length=43
  saved : ∀ i,i<43 → ∀ k,k≤7 → DigAt t (SharedPrefixes.buffer lay.val i k) ((p.prefixes.getD i []).getD k 0)
  path : DigsAt t (sigBase lay.val+16*43) ((List.range (height lay)).map fun j => (p.levels.getD j []).getD ((route index lay).1/2^j ^^^ 1) 0)
  left : DigAt t (metaAddr lay) (topPair lay p.levels).1
  right : DigAt t (metaAddr lay+16) (topPair lay p.levels).2
structure OnePost (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (index : Nat)
    (s : MachineState) (p : PreparedLower) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=(if lay.val<3 then pcOf 22128 else pcOf 22182)
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  zero : ∀ i,i<43 → t.getByte (BitVec.ofNat 64 (DIGITS+i))=0
  stored : Stored lay index p t
  frame : Frame s t (fun A => SharedLowTree.AllW lay (route index lay).2 (sigBase lay.val) A ∨ metaW lay A)
  precise : Frame s t (fun A => SharedLowTree.TreeWrites lay A ∨ metaW lay A)

theorem one_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hlay : lay≠0) {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (btCost+47) (buildTreePrefixes lay (route index lay).2 (route index lay).1)
      (OnePost (cfFlag := cfFlag) sk cache lay index s) := by
  have h0 : lay.val≠0 := fun h => hlay (Fin.ext h)
  have hl := lay.isLt
  obtain ⟨a,k,sa,hk,ha⟩ := setup hc s hpc lay hlay index hi h8 hidx
  have hpre := ha.btPre hlay hi h8 hb hz
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (ha.frame.get (by decide) (fun h => h)).trans hidx
  have hsel : SharedPrefixes.selectionWord (a.getMem 0x20550) lay.val=BitVec.ofNat 64 (route index lay).1 := by
    rw [aidx]; exact SharedPrefixes.selection_route index hi lay hlay
  have ht := SharedLowTree.buildTreePrefixes_tbsim hlow hlevels hsub hcopy hchain hpref hseed hhook
    hpre ha.pc ha.ret hsel
  refine TBSim.mono (TBSim.steps sa (TBSim.post_steps (k := 18) (c := 18) ht (fun p u hu => ?_))) (by omega) (fun _ _ h => h)
  have u8 : u.getReg .x8=BitVec.ofNat 64 lay.val := (hu.regs.get (by decide)).trans hpre.x8
  obtain ⟨t,ut,pt,t8,tl,tr,trs,tf⟩ := done_steps he u hu.pc lay.val (by omega) (by omega) u8
    (topPair lay p.levels).1 (topPair lay p.levels).2 hu.left hu.right
  have tf' : Frame u t (metaW lay) := tf.mono (by unfold metaW metaAddr; intros A hA h; omega)
  have fm : Frame s t (fun A => SharedLowTree.AllW lay (route index lay).2 (sigBase lay.val) A ∨ metaW lay A) :=
    ((ha.frame.trans hu.frame).trans tf').mono (by intros A hA h; rcases h with (h|h)|h <;> tauto)
  refine ⟨t,ut,pt,t8,?_,?_,?_,?_,fm,?_⟩
  · exact hu.base.frame tf' trs (by decide) (by
      intro A hA hb hw
      unfold BaseA NeverW at hb
      unfold metaW metaAddr at hw
      simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA] at hb
      omega)
  · change t.getMem (BitVec.ofNat 64 0x20550)=BitVec.ofNat 64 index
    rw [fm.get (A := 0x20550) (by decide) ?_]; exact hidx
    unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
    fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT]
  · intro i hI
    rw [fm.getByte (by unfold DIGITS; omega) ?_]; exact hz i hI
    unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
    fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT,DIGITS] <;> omega
  · refine ⟨hu.plen,?_,?_,?_,?_⟩
    · intro i hI j hj
      have hbound := SharedPrefixes.buffer_bounds (by omega : 1≤lay.val) (by omega : lay.val≤3) hI (by omega : j<8)
      exact (hu.saved i hI j hj).frame tf' (by omega) (by unfold metaW metaAddr; omega) (by unfold metaW metaAddr; omega)
    · refine hu.path.frame tf' ?_ ?_
      · simp only [List.length_map,List.length_range]; fin_cases lay <;> decide
      · intro A hA hA'
        simp only [List.length_map,List.length_range] at hA'
        unfold metaW metaAddr
        fin_cases lay <;> simp_all [sigBase,height] <;> omega
    · exact tl
    · convert tr using 1 <;> unfold metaAddr <;> omega
  · exact ((ha.frame.trans hu.precise).trans tf').mono (by intros A hA h; rcases h with (h|h)|h <;> tauto)
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def setupACode : List (BitVec 32) := bv_list% 32 [0xa93,0x20b37,0x420b0b13,0x8bb7,0xcb0b8b93,0xfff40313,0x30e63]
sym_block setupA := symRun { noAlias := true } setupACode (pcOf 22418) 100
def setupBCode : List (BitVec 32) := bv_list% 32 [0x8bb7,0xfd0b8b93,0xffe40313,0x30663]
sym_block setupB := symRun { noAlias := true } setupBCode (pcOf 22425) 100
def setupCCode : List (BitVec 32) := bv_list% 32 [0x8bb7,0x2e0b8b93]
sym_block setupC := symRun { noAlias := true } setupCCode (pcOf 22429) 100
def setupDCode : List (BitVec 32) := bv_list% 32 [0x6ec37,0xc0c13,0xd41313,0x6c0c33]
sym_block setupD := symRun { noAlias := true } setupDCode (pcOf 22431) 100
def sigBase (lay : Nat) : Nat := if lay=1 then 0x7cb0 else if lay=2 then 0x7fd0 else 0x82e0
structure SetupCode (im : Image) : Prop where
  a : CodeAt im (pcOf 22418) setupACode
  b : CodeAt im (pcOf 22425) setupBCode
  c : CodeAt im (pcOf 22429) setupCCode
  d : CodeAt im (pcOf 22431) setupDCode
theorem setupA_steps {im : Image} (hc : CodeAt im (pcOf 22418) setupACode)
    (s : MachineState) (hp : s.pc=pcOf 22418) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 7 7 t ∧ t.pc=(if lay=1 then pcOf 22431 else pcOf 22425) ∧ t.getReg .x21=0 ∧ t.getReg .x22=BitVec.ofNat 64 DIGITS ∧ t.getReg .x23=BitVec.ofNat 64 0x7cb0 ∧ RegsExcept s t [.x6,.x21,.x22,.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupA hc s hp (by simp [setupA.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupA.res,rv_simp]
theorem setupB_steps {im : Image} (hc : CodeAt im (pcOf 22425) setupBCode)
    (s : MachineState) (hp : s.pc=pcOf 22425) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=(if lay=2 then pcOf 22431 else pcOf 22429) ∧ t.getReg .x23=BitVec.ofNat 64 0x7fd0 ∧ RegsExcept s t [.x6,.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupB hc s hp (by simp [setupB.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupB.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupB.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupB.res,rv_simp]
theorem setupC_steps {im : Image} (hc : CodeAt im (pcOf 22429) setupCCode)
    (s : MachineState) (hp : s.pc=pcOf 22429)  :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22431 ∧ t.getReg .x23=BitVec.ofNat 64 0x82e0 ∧ RegsExcept s t [.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupC hc s hp (by simp [setupC.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [setupC.res,rv_simp]
  · simp [setupC.res,rv_simp]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupC.res,rv_simp]
theorem setupD_steps {im : Image} (hc : CodeAt im (pcOf 22431) setupDCode)
    (s : MachineState) (hp : s.pc=pcOf 22431) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf 22435 ∧ t.getReg .x24=BitVec.ofNat 64 (buffer lay 0 0) ∧ RegsExcept s t [.x6,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupD hc s hp (by simp [setupD.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupD.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupD.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupD.res,rv_simp]
theorem setup_steps {im : Image} (hc : SetupCode im)
    (s : MachineState) (hp : s.pc=pcOf 22418) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t k, Steps im s k k t ∧ k≤17 ∧ t.pc=pcOf 22435 ∧ t.getReg .x21=0 ∧
      t.getReg .x22=BitVec.ofNat 64 DIGITS ∧ t.getReg .x23=BitVec.ofNat 64 (sigBase lay) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay 0 0) ∧
      RegsExcept s t [.x6,.x21,.x22,.x23,.x24] ∧ Frame s t (fun _ => False) := by
  obtain ⟨a,sa,ap,a21,a22,a23,ar,af⟩ := setupA_steps hc.a s hp lay hl hh h8
  have a8 := (ar.get (by decide)).trans h8
  interval_cases lay
  · obtain ⟨t,at',tp,t24,tr,tf⟩ := setupD_steps hc.d a (by simpa using ap) 1 (by decide) (by decide) a8
    exact ⟨t,11,sa.trans at',by decide,tp,(tr.get (by decide)).trans a21,(tr.get (by decide)).trans a22,
      (tr.get (by decide)).trans a23,t24,(ar.trans tr).mono (by simp),(af.trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b23,br,bf⟩ := setupB_steps hc.b a (by simpa using ap) 2 (by decide) (by decide) a8
    obtain ⟨t,bt,tp,t24,tr,tf⟩ := setupD_steps hc.d b (by simpa using bp) 2 (by decide) (by decide) ((br.get (by decide)).trans a8)
    exact ⟨t,15,sa.trans (ab.trans bt),by decide,tp,
      (tr.get (by decide)).trans ((br.get (by decide)).trans a21),
      (tr.get (by decide)).trans ((br.get (by decide)).trans a22),
      (tr.get (by decide)).trans b23,t24,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b23,br,bf⟩ := setupB_steps hc.b a (by simpa using ap) 3 (by decide) (by decide) a8
    obtain ⟨c,bc,cp,c23,cr,cf⟩ := setupC_steps hc.c b (by simpa using bp)
    obtain ⟨t,ct,tp,t24,tr,tf⟩ := setupD_steps hc.d c cp 3 (by decide) (by decide)
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a8))
    exact ⟨t,17,sa.trans (ab.trans (bc.trans ct)),by decide,tp,
      (tr.get (by decide)).trans ((cr.get (by decide)).trans ((br.get (by decide)).trans a21)),
      (tr.get (by decide)).trans ((cr.get (by decide)).trans ((br.get (by decide)).trans a22)),
      (tr.get (by decide)).trans c23,t24,(((ar.trans br).trans cr).trans tr).mono (by simp),
      (((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem reveal_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (hsetup : SetupCode im)
    (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (digits : Nat→Nat) (prefixes : Nat→Nat→Digest) (hd : ∀ j,j<43 → digits j<8)
    (s : MachineState) (hp : s.pc=pcOf 22418) (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits j))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay j d) (prefixes j d)) :
    ∃ t k, Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (sigBase lay) ((List.range 43).map fun i => prefixes i (digits i)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => sigBase lay≤A ∧ A<sigBase lay+688) := by
  obtain ⟨a,k,sa,hk,ap,a21,a22,a23,a24,ar,af⟩ := setup_steps hsetup s hp lay hl hh h8
  obtain ⟨t,aToT,tp,tv,tr,tf⟩ := loop_steps hc hbcode lay (sigBase lay) hl hh
    (by interval_cases lay <;> decide) (by interval_cases lay <;> decide) (by interval_cases lay <;> decide)
    digits prefixes hd 43 0 (by decide) a (by simpa using ap) a21
    (by simpa using a22) (by simpa using a23) a24
    (by intro j hj; rw [af.getByte (by unfold DIGITS; omega) (fun h => h)]; exact hb j hj)
    (by intro j hj d hd; exact (hv j hj d hd).frame af (by unfold buffer; omega) (fun h => h) (fun h => h))
  refine ⟨t,k+559,sa.trans aToT,by omega,tp,?_,(ar.trans tr).mono (by simp),?_⟩
  · intro i hi
    have hi' : i<43 := by simpa using hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,List.getElem_range]
    exact tv i (by omega) hi'
  · exact (af.trans tf).mono (by intro A hA h; rcases h with h|h; exact h.elim; simpa using h)
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_setupCode : SetupCode Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
theorem installed_byteCode : CodeAt Images.signImage (pcOf 22435) [0xb4303] := by
  sign_slice_fast
theorem installed_stepCode : CodeAt Images.signImage (pcOf 22436) stepCode := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem Stored.after {sk : SecretKey} {cache : Bytes 131072} {index : Nat} {lay other : Layer}
    (hl : lay≠0) (ho : other≠0) (hne : lay≠other) {s t : MachineState} {p q : PreparedLower}
    (h : Stored other index p s) (ht : OnePost (cfFlag := cfFlag) sk cache lay index s q t) : Stored other index p t := by
  have hl0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have ho0 : other.val≠0 := fun h => ho (Fin.ext h)
  have hlb := lay.isLt
  have hob := other.isLt
  refine ⟨h.plen,?_,?_,?_,?_⟩
  · intro i hi k hk
    have b := SharedPrefixes.buffer_bounds (by omega : 1≤other.val) (by omega : other.val≤3) hi (by omega : k<8)
    refine (h.saved i hi k hk).frame ht.precise (by omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_other_prefix lay other hne ho (i := i) (k := k) hi (by omega) 0 (by decide) (by simpa using ha)
      · unfold metaW metaAddr at ha; omega
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_other_prefix lay other hne ho (i := i) (k := k) hi (by omega) 1 (by decide) (by simpa using ha)
      · unfold metaW metaAddr at ha; omega
  · refine h.path.frame ht.frame ?_ ?_
    · simp only [List.length_map,List.length_range]; fin_cases other <;> decide
    · intro A ha hw
      simp only [List.length_map,List.length_range] at hw
      unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
      fin_cases lay <;> fin_cases other <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT] <;> omega
  · refine h.left.frame ht.precise (by unfold metaAddr; omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
  · refine h.right.frame ht.precise (by unfold metaAddr; omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def RootsWrites (A : Nat) : Prop := A < 0x66000 ∨ (0x66040≤A ∧ A<0x660a0) ∨ (0x70000≤A ∧ A<0x76000)
structure RootsPost (sk : SecretKey) (cache : Bytes 131072) (index : Nat)
    (s : MachineState) (p : PreparedRoots) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=pcOf 22182
  layer : t.getReg .x8=4
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  one : Stored 1 index p.one t
  two : Stored 2 index p.two t
  three : Stored 3 index p.three t
  frame : Frame s t RootsWrites
  counterMem : t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32))

theorem OnePost.counterMem {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower}
    (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) :
    t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32)) := by
  apply h.frame.get (by unfold ENC; decide)
  unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
  fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT] <;> omega

theorem OnePost.rootsFrame {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower} (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) :
    Frame s t RootsWrites := by
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have hbound := lay.isLt
  exact h.precise.mono (by unfold SharedLowTree.TreeWrites metaW metaAddr RootsWrites; intros A hA h; omega)

theorem prepareRoots_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=1) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (3*(btCost+47)) (prepareRoots index) (RootsPost (cfFlag := cfFlag) sk cache index s) := by
  have r1 := one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    (lay := 1) (by decide) hi s hpc h8 hidx hb hz
  unfold prepareRoots
  refine TBSim.mono (TBSim.bind r1 (fun p1 t1 h1 =>
    TBSim.bind (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
      (lay := 2) (by decide) hi t1 (by simpa using h1.pc) h1.layer h1.indexMem h1.base h1.zero)
      (fun p2 t2 h2 => TBSim.bind
        (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
          (lay := 3) (by decide) hi t2 (by simpa using h2.pc) h2.layer h2.indexMem h2.base h2.zero)
        (fun p3 t3 h3 => TBSim.pure ?_)))) (by omega) (fun _ _ h => h)
  refine ⟨by simpa using h3.pc,by simpa using h3.layer,h3.base,h3.indexMem,?_,?_,h3.stored,?_,?_⟩
  · exact (h1.stored.after (by decide) (by decide) (by decide) h2).after
      (by decide) (by decide) (by decide) h3
  · exact h2.stored.after (by decide) (by decide) (by decide) h3
  · exact (((h1.rootsFrame (by decide)).trans (h2.rootsFrame (by decide))).trans
      (h3.rootsFrame (by decide))).mono (by intro A hA h; rcases h with (h|h)|h <;> exact h)
  · exact (h3.counterMem (by decide)).trans ((h2.counterMem (by decide)).trans (h1.counterMem (by decide)))
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def introCode : List (BitVec 32) := bv_list% 32 [0x413,0x493,0xc00793,0x3600d13,0x3300d93,0x9200893,0x20e37,0x550e0e13,0xe3903,0x1395913,0x90713,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block introBlock := symRun { noAlias := true } introCode (pcOf 22182) 100
def copyCode : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xf1dea0ef]
sym_block copyBlock := symRun { noAlias := true } copyCode (pcOf 22199) 100
structure IntroPost (index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22199
  x8 : t.getReg .x8=0
  x9 : t.getReg .x9=0
  x14 : t.getReg .x14=BitVec.ofNat 64 (index/2^19)
  x15 : t.getReg .x15=12
  x17 : t.getReg .x17=146
  x18 : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  x26 : t.getReg .x26=54
  x27 : t.getReg .x27=51
  x28 : t.getReg .x28=BitVec.ofNat 64 ENC
  x29 : t.getReg .x29=BitVec.ofNat 64 0x66040
  regs : RegsExcept s t [.x7,.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun _ => False)
theorem intro_steps {im : Image} (hc : CodeAt im (pcOf 22182) introCode)
    (s : MachineState) (hp : s.pc=pcOf 22182) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 17 17 t ∧ IntroPost index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  refine ⟨_,symRun_sound introBlock hc s hp (by simp [introBlock.res,rv_simp]),?_⟩
  constructor
  all_goals first
    | solve | (simp only [Result.toState_getReg,introBlock.res]; t3n [hidx,ENC])
    | solve | (simp [introBlock.res,rv_simp])
    | solve | (intro r hr; cases r <;> simp at hr <;> rfl)
    | solve | (intro A hA hn; simp [introBlock.res,rv_simp])
    | (simp only [Result.toState_getReg,introBlock.res]; t3n [hidx,ENC];
       apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight,toNat_ofNat_lt (show index<2^64 by omega),Nat.shiftRight_eq_div_pow]; omega)

theorem copy_steps {im : Image} (hc : CodeAt im (pcOf 22199) copyCode)
    (s : MachineState) (hp : s.pc=pcOf 22199)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC) (h29 : s.getReg .x29=BitVec.ofNat 64 0x66040)
    (left right : Digest) (hl : DigAt s 0x66040 left) (hr : DigAt s 0x66050 right) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 646 ∧ t.getReg .x1=pcOf 22208 ∧
      DigAt t ENC left ∧ DigAt t (ENC+48) right ∧
      RegsExcept s t [.x1,.x6,.x7] ∧
      Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) := by
  have ho : Oblig.all s copyBlock.res.st.obl := by
    simp [copyBlock.res,rv_simp,h28,h29,ENC]
    decide
  refine ⟨_,symRun_sound copyBlock hc s hp ho,?_,?_,?_,?_,?_,?_⟩
  · simp [copyBlock.res,rv_simp]
  · simp [copyBlock.res,rv_simp,pcOf]
  · constructor
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hl.1
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hl.2
  · constructor
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hr.1
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hr.2
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,copyBlock.res]
    t3n [h28,h29,ENC]
    unfold ENC at hn
    repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Code (im : Image) : Prop where
  intro : CodeAt im (pcOf 22182) introCode
  copy : CodeAt im (pcOf 22199) copyCode
structure Post (index : Nat) (left right : Digest) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22208
  x8 : t.getReg .x8=0
  x9 : t.getReg .x9=0
  x14 : t.getReg .x14=BitVec.ofNat 64 (index/2^19)
  x15 : t.getReg .x15=12
  x17 : t.getReg .x17=146
  x18 : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  x26 : t.getReg .x26=54
  x27 : t.getReg .x27=51
  left : DigAt t ENC left
  right : DigAt t (ENC+48) right
  regs : RegsExcept s t [.x1,.x6,.x7,.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)
theorem steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 22182) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (left right : Digest)
    (hl : DigAt s 0x66040 left) (hr : DigAt s 0x66050 right) :
    ∃ t, Steps im s 26 26 t ∧ Post index left right s t := by
  obtain ⟨a,sa,ha⟩ := intro_steps hc.intro s hp index hi hidx
  obtain ⟨t,at',tp,tret,tl,tr,trs,tf⟩ := copy_steps hc.copy a ha.pc ha.x28 ha.x29 left right
    (hl.frame ha.frame (by decide) (fun h => h) (fun h => h))
    (hr.frame ha.frame (by decide) (fun h => h) (fun h => h))
  refine ⟨t,sa.trans at',tp,tret,?_,?_,?_,?_,?_,?_,?_,?_,tl,tr,?_,?_⟩
  · exact (trs.get (by decide)).trans ha.x8
  · exact (trs.get (by decide)).trans ha.x9
  · exact (trs.get (by decide)).trans ha.x14
  · exact (trs.get (by decide)).trans ha.x15
  · exact (trs.get (by decide)).trans ha.x17
  · exact (trs.get (by decide)).trans ha.x18
  · exact (trs.get (by decide)).trans ha.x26
  · exact (trs.get (by decide)).trans ha.x27
  · exact (ha.regs.trans trs).mono (by simp)
  · exact (ha.frame.trans tf).mono (by tauto)
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor
  · sign_slice_fast
  · sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedResidual
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def read22230Code : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3303,0x18e3383,0x63e663]
sym_block read22230 := symRun { noAlias := true } read22230Code (pcOf 22230) 100
def zero22230Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22230 := symRun { noAlias := true } zero22230Code (pcOf 22235) 100
def sub22230Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22230 := symRun { noAlias := true } sub22230Code (pcOf 22237) 100
def store22230Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22230 := symRun { noAlias := true } store22230Code (pcOf 22238) 100
structure Code22230 (im : Image) : Prop where
  read : CodeAt im (pcOf 22230) read22230Code
  zero : CodeAt im (pcOf 22235) zero22230Code
  sub : CodeAt im (pcOf 22237) sub22230Code
  store : CodeAt im (pcOf 22238) store22230Code

theorem read22230_steps {im : Image} (hc : CodeAt im (pcOf 22230) read22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22230) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 5 5 t ∧ t.pc=(if c<r then pcOf 22237 else pcOf 22235) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧ t.getReg .x7=BitVec.ofNat 64 c ∧ t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound read22230 hc s hp (by simp [read22230.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [read22230.res,rv_simp,hrm,hcm,pcOf,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),toNat_ofNat_lt (show c<2^64 by omega)]
  · simp [read22230.res,rv_simp,hrm]
  · simp [read22230.res,rv_simp,hcm]
  · simp [read22230.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [read22230.res,rv_simp]

theorem zero22230_steps {im : Image} (hc : CodeAt im (pcOf 22235) zero22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22235) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22230 hc s hp (by simp [zero22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22230.res,rv_simp]
  · simp [zero22230.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22230.res,rv_simp]

theorem sub22230_steps {im : Image} (hc : CodeAt im (pcOf 22237) sub22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22237) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22230 hc s hp (by simp [sub22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22230.res,rv_simp]
  · simp only [Result.toState_getReg,sub22230.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22230.res,rv_simp]

theorem store22230_steps {im : Image} (hc : CodeAt im (pcOf 22238) store22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22238) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22239 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22230 hc s hp (by simp [store22230.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22230.res,rv_simp]
  · simp [store22230.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22230.res]; t3n [h28]
    rw [if_neg (by omega)]

theorem residual22230_steps {im : Image} (hc : Code22230 im)
    (s : MachineState) (hp : s.pc=pcOf 22230) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t k, Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22239 ∧ t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  obtain ⟨a,sa,ap,a6,a7,a28,ar,af⟩ := read22230_steps hc.read s hp r c hr hc' hrm hcm
  by_cases hcr : c<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := sub22230_steps hc.sub a (by simpa [hcr] using ap) r c hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,7,sa.trans (ab.trans bt),by decide,tp,tv,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := zero22230_steps hc.zero a (by simpa [hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,8,sa.trans (ab.trans bt),by decide,tp,by simpa [Nat.sub_eq_zero_of_le (by omega : r≤c)] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
def read22448Code : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3303,0x18e3383,0x63e663]
sym_block read22448 := symRun { noAlias := true } read22448Code (pcOf 22448) 100
def zero22448Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22448 := symRun { noAlias := true } zero22448Code (pcOf 22453) 100
def sub22448Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22448 := symRun { noAlias := true } sub22448Code (pcOf 22455) 100
def store22448Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22448 := symRun { noAlias := true } store22448Code (pcOf 22456) 100
structure Code22448 (im : Image) : Prop where
  read : CodeAt im (pcOf 22448) read22448Code
  zero : CodeAt im (pcOf 22453) zero22448Code
  sub : CodeAt im (pcOf 22455) sub22448Code
  store : CodeAt im (pcOf 22456) store22448Code

theorem read22448_steps {im : Image} (hc : CodeAt im (pcOf 22448) read22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22448) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 5 5 t ∧ t.pc=(if c<r then pcOf 22455 else pcOf 22453) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧ t.getReg .x7=BitVec.ofNat 64 c ∧ t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound read22448 hc s hp (by simp [read22448.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [read22448.res,rv_simp,hrm,hcm,pcOf,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),toNat_ofNat_lt (show c<2^64 by omega)]
  · simp [read22448.res,rv_simp,hrm]
  · simp [read22448.res,rv_simp,hcm]
  · simp [read22448.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [read22448.res,rv_simp]

theorem zero22448_steps {im : Image} (hc : CodeAt im (pcOf 22453) zero22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22453) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22448 hc s hp (by simp [zero22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22448.res,rv_simp]
  · simp [zero22448.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22448.res,rv_simp]

theorem sub22448_steps {im : Image} (hc : CodeAt im (pcOf 22455) sub22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22455) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22448 hc s hp (by simp [sub22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22448.res,rv_simp]
  · simp only [Result.toState_getReg,sub22448.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22448.res,rv_simp]

theorem store22448_steps {im : Image} (hc : CodeAt im (pcOf 22456) store22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22456) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22457 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22448 hc s hp (by simp [store22448.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22448.res,rv_simp]
  · simp [store22448.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22448.res]; t3n [h28]
    rw [if_neg (by omega)]

theorem residual22448_steps {im : Image} (hc : Code22448 im)
    (s : MachineState) (hp : s.pc=pcOf 22448) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t k, Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22457 ∧ t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  obtain ⟨a,sa,ap,a6,a7,a28,ar,af⟩ := read22448_steps hc.read s hp r c hr hc' hrm hcm
  by_cases hcr : c<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := sub22448_steps hc.sub a (by simpa [hcr] using ap) r c hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,7,sa.trans (ab.trans bt),by decide,tp,tv,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := zero22448_steps hc.zero a (by simpa [hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,8,sa.trans (ab.trans bt),by decide,tp,by simpa [Nat.sub_eq_zero_of_le (by omega : r≤c)] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedResidual

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def EntryWrites (A : Nat) : Prop := A=0x66000 ∨ 0x660a0≤A ∧ A<0x660c0 ∨ DIGITS≤A ∧ A<DIGITS+56
structure BuiltPost (sk : SecretKey) (cache : Bytes 131072) (index : Nat) (forest : Digest×Digest)
    (s : MachineState) (p : PreparedRoots) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=pcOf 22182
  layer : t.getReg .x8=4
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  one : Stored 1 index p.one t
  two : Stored 2 index p.two t
  three : Stored 3 index p.three t
  hintZero : t.getMem (0x66000#64)=0
  forestL : DigAt t 0x660a0 forest.1
  forestR : DigAt t 0x660b0 forest.2
  frame : Frame s t (fun A => EntryWrites A ∨ RootsWrites A)
  counterMem : t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32))

theorem entry_roots_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat} (hi : index<2^31)
    (forest : Digest×Digest) (s : MachineState) (hpc : s.pc=pcOf 22100)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hl : DigAt s ENC forest.1) (hr : DigAt s (ENC+48) forest.2) :
    TBSim im sk s (28+3*(btCost+47)) (prepareRoots index) (BuiltPost (cfFlag := cfFlag) sk cache index forest s) := by
  obtain ⟨a,sa,ap,a8,al,ar,az,ad,ars,af⟩ := entry_steps he s hpc forest.1 forest.2 hl hr
  have af' : Frame s a EntryWrites := af.mono (by unfold EntryWrites; intros A hA h; exact h)
  have abase : Base (cfFlag := cfFlag) sk cache a := hb.frame af' ars (by decide) (by
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold EntryWrites at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA,DIGITS] at hbase hw
    omega)
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (af'.get (A := 0x20550) (by decide) (by unfold EntryWrites DIGITS; omega)).trans hidx
  refine (TBSim.steps sa (prepareRoots_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    hi a ap a8 aidx abase ad)).mono (le_refl _) ?_
  intro p t ht
  refine ⟨ht.pc,ht.layer,ht.base,ht.indexMem,ht.one,ht.two,ht.three,?_,?_,?_,af'.trans ht.frame,?_⟩
  · exact (ht.frame.get (A := 0x66000) (by decide) (by unfold RootsWrites; decide)).trans az
  · exact al.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
  · exact ar.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
  · exact ht.counterMem.trans (af'.get (A := ENC+32) (by unfold ENC; decide) (by unfold EntryWrites ENC DIGITS; decide))
#print axioms entry_roots_tbsim
end SigGolfCandidate.T3M.Sign.SharedRootControl


namespace SigGolfCandidate.T3M.Sign.SharedTopDigits
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def saveCode : List (BitVec 32) := bv_list% 32 [0x20e37,0x420e0e13,0x66eb7,0x100e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x20e3303,0x26eb023,0x28e3303,0x26eb423,0x30e3303,0x26eb823]
sym_block save := symRun { noAlias := true } saveCode (pcOf 22208) 100
theorem save_steps {im : Image} (hc : CodeAt im (pcOf 22208) saveCode)
    (s : MachineState) (hp : s.pc=pcOf 22208) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22226 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => 0x66100≤A ∧ A<0x66100+56) := by
  refine ⟨_,symRun_sound save hc s hp (by simp [save.res,rv_simp]; try decide),?_,?_,?_,?_⟩
  · simp [save.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [save.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,save.res]
    t3n [DIGITS]
    try unfold DIGITS at hn
    repeat rw [if_neg (by omega)]
#print axioms save_steps
def restoreCode : List (BitVec 32) := bv_list% 32 [0x66e37,0x100e0e13,0x20eb7,0x420e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x20e3303,0x26eb023,0x28e3303,0x26eb423,0x30e3303,0x26eb823]
sym_block restore := symRun { noAlias := true } restoreCode (pcOf 22460) 100
theorem restore_steps {im : Image} (hc : CodeAt im (pcOf 22460) restoreCode)
    (s : MachineState) (hp : s.pc=pcOf 22460) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22478 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56) := by
  refine ⟨_,symRun_sound restore hc s hp (by simp [restore.res,rv_simp]; try decide),?_,?_,?_,?_⟩
  · simp [restore.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [restore.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,restore.res]
    t3n [DIGITS]
    try unfold DIGITS at hn
    repeat rw [if_neg (by omega)]
#print axioms restore_steps
end SigGolfCandidate.T3M.Sign.SharedTopDigits


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def cst (n : Nat) : E := .c (BitVec.ofNat 64 n)
def rfs (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def thCode : List (BitVec 32) := bv_list% 32 [0xfff40313,0x30e63,0xffe40313,0xc030c63,0x1600313,0x1c6a7263,0xa0e93,0x1c00006f,0x3800313,0x1a6a7a63,0xe93,0x2600313,0x1a6a6663,0x100e93,0x2700313,0x1a6a6063,0x200e93,0x2800313,0x186a6a63,0x300e93,0x2900313,0x186a6463,0x400e93,0x2a00313,0x166a6e63,0x500e93,0x2b00313,0x166a6863,0x600e93,0x2c00313,0x166a6263,0x700e93,0x2d00313,0x146a6c63,0x800e93,0x2f00313,0x146a6663,0x900e93,0x3000313,0x146a6063,0xa00e93,0x3100313,0x126a6a63,0xb00e93,0x3300313,0x126a6463,0xc00e93,0x3400313,0x106a6e63,0xd00e93,0x3600313,0x106a6863,0xe00e93,0x3700313,0x106a6263,0xf00e93,0xfc0006f,0x2900313,0xe6a7863,0xe93,0x1400313,0xe6a6463,0x100e93,0x1500313,0xc6a6e63,0x200e93,0x1600313,0xc6a6863,0x300e93,0x1700313,0xc6a6263,0x400e93,0x1800313,0xa6a6c63,0x500e93,0x1900313,0xa6a6663,0x600e93,0x1a00313,0xa6a6063,0x700e93,0x1b00313,0x86a6a63,0x800e93,0x1c00313,0x86a6463,0x900e93,0x1d00313,0x66a6e63,0xa00e93,0x1e00313,0x66a6863,0xb00e93,0x1f00313,0x66a6263,0xc00e93,0x2100313,0x46a6c63,0xd00e93,0x2200313,0x46a6663,0xe00e93,0x2300313,0x46a6063,0xf00e93,0x2500313,0x26a6a63,0x1000e93,0x2600313,0x26a6463,0x1100e93,0x2700313,0x6a6e63,0x1200e93,0x2800313,0x6a6863,0x1300e93,0x80006f,0x945fd06f,0xf44fd06f]
/-- The img-v6 threshold routine `th` (appended, 24851..24970): `t4 := threshold(s0, s4)`; L1 cascade at 24859
(residual < 56), L2 at 24908 (residual < 41), L3 at 24855 (floor = residual < 22), failure 24969 (`jal 22490`),
result 24970 (`jal 22363`). -/
def lookT (n : Nat) : Option (BitVec 32) := if 24851 ≤ n then thCode[n-24851]? else none
def ends1 : List Nat := [38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 51, 52, 54, 55]
def ends2 : List Nat := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 39, 40]
def dirs (m v : Nat) : List Dir := [.br false] ++ List.replicate v (.br false) ++ (if v < m then [.br true] else [])
def resL (ends : List Nat) (m bound v : Nat) : PRes :=
  ⟨⟨rfs [(.x6,cst (ends.getD (if v < m then v else m-1) 0)),(.x29,cst v)],[],[]⟩,pcOf 22363,false,
    (if v < m then 6+3*v else 5+3*m),(if v < m then 6+3*v else 5+3*m),
    (if v < m then [⟨.ltu,.reg .x20,cst (ends.getD v 0),true⟩] else []) ++
    ((List.range v).reverse.map (fun i => ⟨.ltu,.reg .x20,cst (ends.getD i 0),false⟩)) ++
    [⟨.geu,.reg .x20,cst bound,false⟩],none⟩
theorem checked1 : (List.range 16).all (fun v =>
    optBeq (run lookT [22363] 24859 (dirs 15 v)) (resL ends1 15 56 v)) = true := by decide +kernel
theorem checked2 : (List.range 20).all (fun v =>
    optBeq (run lookT [22363] 24908 (dirs 19 v)) (resL ends2 19 41 v)) = true := by decide +kernel
theorem code_lookT {im : Image} (hc : CodeAt im (pcOf 24851) thCode) : LookOK im lookT := by
  intro n w hw
  unfold lookT at hw
  split at hw
  · rename_i hn
    have hlen := (List.getElem?_eq_some_iff.mp hw).1
    obtain ⟨rest,hrest⟩ := hc.2.2.2
    have hpref : thCode ++ rest = im.code.drop 24851 := by simpa [pcOf] using hrest
    have hget : (im.code.drop 24851)[n-24851]? = some w := by
      rw [← hpref,List.getElem?_append_left hlen]; exact hw
    simpa [List.getElem?_drop,Nat.add_sub_cancel' hn] using hget
  · cases hw
theorem floorL_steps {im : Image} (hc : CodeAt im (pcOf 24851) thCode) (ends : List Nat) (m bound start : Nat)
    (hchk : (List.range (m+1)).all (fun v =>
      optBeq (run lookT [22363] start (dirs m v)) (resL ends m bound v)) = true)
    (hm : 0 < m) (hlen : ends.length=m) (hlt : ∀ i, i < m → ends.getD i 0<2^64) (hb : bound<2^64)
    (s : MachineState) (hp : s.pc=pcOf start) (r v : Nat)
    (hv : v ≤ m) (hr : r<bound)
    (hupper : v < m → r<ends.getD v 0)
    (hlower : ∀ i,i < v → ends.getD i 0≤r)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t k, Steps im s k k t ∧ k≤5+3*m ∧ t.pc=pcOf 22363 ∧
      t.getReg .x29=BitVec.ofNat 64 v ∧ RegsExcept s t [.x6,.x29] ∧ Frame s t (fun _ => False) := by
  have hh := optBeq_eq (List.all_eq_true.mp hchk v (List.mem_range.mpr (by omega)))
  have hob : ∀ o∈(resL ends m bound v).st.obl,o.holds s := by simp [resL]
  have hbr : ∀ b∈(resL ends m bound v).brs,b.holds s := by
    intro b hb
    simp only [resL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with (hb|hb)|rfl
    · split at hb
      · rename_i hvm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        subst hb
        simp only [Br.holds,E.eval,cst,CmpOp.eval,h20]
        have he := hlt v hvm
        simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show r<2^64 by omega),Nat.mod_eq_of_lt he,decide_eq_true_eq]
        exact hupper hvm
      · simp at hb
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
      have hi : i < v := List.mem_range.mp (List.mem_reverse.mp hi)
      have he := hlt i (by omega)
      simp only [Br.holds,E.eval,cst,CmpOp.eval,h20]
      simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show r<2^64 by omega),Nat.mod_eq_of_lt he,decide_eq_false_iff_not]
      exact Nat.not_lt.mpr (hlower i hi)
    · simp [Br.holds,E.eval,cst,CmpOp.eval,h20,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega)]
      omega
  refine ⟨(resL ends m bound v).toState s,_,(run_sound (code_lookT hc) hh s hp hob hbr).1,?_,rfl,rfl,?_,?_⟩
  · simp only [resL]; split <;> omega
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; rfl
end SigGolfCandidate.T3M.Sign.SharedFloor


namespace SigGolfCandidate.T3M.Sign.SharedResidual
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed22230 : Code22230 Images.signImage := by
  constructor <;> sign_slice_fast
theorem installed22448 : Code22448 Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedResidual
namespace SigGolfCandidate.T3M.Sign.SharedTopDigits
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_save : CodeAt Images.signImage (pcOf 22208) saveCode := by
  sign_slice_fast
theorem installed_restore : CodeAt Images.signImage (pcOf 22460) restoreCode := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedTopDigits


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def selectACode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3a03,0x0c10206f]
sym_block selectA := symRun { noAlias := true } selectACode (pcOf 22240) 100
def dispACode : List (BitVec 32) := bv_list% 32 [0xfff40313,0x30e63]
sym_block dispA := symRun { noAlias := true } dispACode (pcOf 24851) 100
def selectBCode : List (BitVec 32) := bv_list% 32 [0xffe40313,0xc030c63]
sym_block selectB := symRun { noAlias := true } selectBCode (pcOf 24853) 100
def guard3Code : List (BitVec 32) := bv_list% 32 [0x1600313,0x1c6a7263]
sym_block guard3 := symRun { noAlias := true } guard3Code (pcOf 24855) 100
def return3Code : List (BitVec 32) := bv_list% 32 [0xa0e93,0x1c00006f]
sym_block return3 := symRun { noAlias := true } return3Code (pcOf 24857) 100
def finCode : List (BitVec 32) := bv_list% 32 [0xf44fd06f]
sym_block fin := symRun { noAlias := true } finCode (pcOf 24970) 100

theorem selectA_steps {im : Image} (hc : CodeAt im (pcOf 22240) selectACode)
    (s : MachineState) (hp : s.pc=pcOf 22240) (r : Nat)
    (hr : s.getMem (0x66008#64)=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 24851 ∧
      t.getReg .x20=BitVec.ofNat 64 r ∧ RegsExcept s t [.x20,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound selectA hc s hp (by simp [selectA.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [selectA.res,rv_simp]
  · simp [selectA.res,rv_simp,hr]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem dispA_steps {im : Image} (hc : CodeAt im (pcOf 24851) dispACode)
    (s : MachineState) (hp : s.pc=pcOf 24851) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=(if lay=1 then pcOf 24859 else pcOf 24853) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound dispA hc s hp (by simp [dispA.res,rv_simp]),?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩
    interval_cases lay <;> simp [dispA.res,rv_simp,h8]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem selectB_steps {im : Image} (hc : CodeAt im (pcOf 24853) selectBCode)
    (s : MachineState) (hp : s.pc=pcOf 24853) (lay : Nat) (hl : lay=2 ∨ lay=3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=(if lay=2 then pcOf 24908 else pcOf 24855) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound selectB hc s hp (by simp [selectB.res,rv_simp]),?_,?_,?_⟩
  · rcases hl with rfl|rfl <;> simp [selectB.res,rv_simp,h8]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem guard3_steps {im : Image} (hc : CodeAt im (pcOf 24855) guard3Code)
    (s : MachineState) (hp : s.pc=pcOf 24855) (r : Nat) (hr : r<22)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 24857 ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound guard3 hc s hp (by simp [guard3.res,rv_simp]),?_,?_,?_⟩
  · simp [guard3.res,rv_simp,h20,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),hr]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem return3_steps {im : Image} (hc : CodeAt im (pcOf 24857) return3Code)
    (s : MachineState) (hp : s.pc=pcOf 24857) (r : Nat)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 24970 ∧ t.getReg .x29=BitVec.ofNat 64 r ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound return3 hc s hp (by simp [return3.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [return3.res,rv_simp]
  · simp [return3.res,rv_simp,h20]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem fin_steps {im : Image} (hc : CodeAt im (pcOf 24970) finCode)
    (s : MachineState) (hp : s.pc=pcOf 24970) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22363 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound fin hc s hp (by simp [fin.res,rv_simp]),?_,?_,?_⟩
  · simp [fin.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
end SigGolfCandidate.T3M.Sign.SharedFloor

namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.WCT9
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem threshold1_range : ∀ r,r<56 →
    CanonicalPolicy.threshold 1 r≤15 ∧ (CanonicalPolicy.threshold 1 r<15 → r<ends1.getD (CanonicalPolicy.threshold 1 r) 0) ∧
      ∀ i,i<CanonicalPolicy.threshold 1 r → ends1.getD i 0≤r := by decide +kernel
theorem threshold2_range : ∀ r,r<41 →
    CanonicalPolicy.threshold 2 r≤19 ∧ (CanonicalPolicy.threshold 2 r<19 → r<ends2.getD (CanonicalPolicy.threshold 2 r) 0) ∧
      ∀ i,i<CanonicalPolicy.threshold 2 r → ends2.getD i 0≤r := by decide +kernel
theorem ends1_lt : ∀ i, i<15 → ends1.getD i 0<2^64 := by decide +kernel
theorem ends2_lt : ∀ i, i<19 → ends2.getD i 0<2^64 := by decide +kernel

structure DispatchCode (im : Image) : Prop where
  selectA : CodeAt im (pcOf 22240) selectACode
  dispA : CodeAt im (pcOf 24851) dispACode
  selectB : CodeAt im (pcOf 24853) selectBCode
  guard3 : CodeAt im (pcOf 24855) guard3Code
  return3 : CodeAt im (pcOf 24857) return3Code
  fin : CodeAt im (pcOf 24970) finCode
  th : CodeAt im (pcOf 24851) thCode

theorem threshold_steps {im : Image} (hc : DispatchCode im)
    (s : MachineState) (hp : s.pc=pcOf 22240) (lay r : Nat) (hl : 1≤lay ∧ lay≤3)
    (hr : r < if lay=1 then 56 else if lay=2 then 41 else 22)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) :
    ∃ t k,Steps im s k k t ∧ k≤70 ∧ t.pc=pcOf 22363 ∧
      t.getReg .x29=BitVec.ofNat 64 (CanonicalPolicy.threshold lay r) ∧
      RegsExcept s t [.x6,.x20,.x28,.x29] ∧ Frame s t (fun _ => False) := by
  obtain ⟨a,sa,ap,a20,ar,af⟩ := selectA_steps hc.selectA s hp r hrm
  have a8 := (ar.get (by decide : RiscvZkvm.Rv64.Reg.x8 ∉ [.x20,.x28])).trans h8
  obtain ⟨b,ab,bp,br,bf⟩ := dispA_steps hc.dispA a ap lay hl a8
  have b20 := (br.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans a20
  have b8 := (br.get (by decide : RiscvZkvm.Rv64.Reg.x8 ∉ [.x6])).trans a8
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · have ht := threshold1_range r (by simpa using hr)
    obtain ⟨t,k,bt,hk,tp,t29,tr,tf⟩ := floorL_steps hc.th ends1 15 56 24859 checked1 (by decide) rfl ends1_lt
      (by decide) b (by simpa using bp) r _ ht.1 (by simpa using hr) ht.2.1 ht.2.2 b20
    exact ⟨t,4+2+k,(sa.trans ab).trans bt,by omega,tp,t29,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨c,bc,cp,cr,cf⟩ := selectB_steps hc.selectB b (by simpa using bp) 2 (by simp) b8
    have c20 := (cr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans b20
    have ht := threshold2_range r (by simpa using hr)
    obtain ⟨t,k,ct,hk,tp,t29,tr,tf⟩ := floorL_steps hc.th ends2 19 41 24908 checked2 (by decide) rfl ends2_lt
      (by decide) c (by simpa using cp) r _ ht.1 (by simpa using hr) ht.2.1 ht.2.2 c20
    exact ⟨t,4+2+2+k,((sa.trans ab).trans bc).trans ct,by omega,tp,t29,
      (((ar.trans br).trans cr).trans tr).mono (by simp),(((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
  · obtain ⟨c,bc,cp,cr,cf⟩ := selectB_steps hc.selectB b (by simpa using bp) 3 (by simp) b8
    have c20 := (cr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans b20
    obtain ⟨d,cd,dp,dr,df⟩ := guard3_steps hc.guard3 c (by simpa using cp) r (by simpa using hr) c20
    have d20 := (dr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans c20
    obtain ⟨e,de,ep,e29,er,ef⟩ := return3_steps hc.return3 d dp r d20
    obtain ⟨t,et,tp,tr,tf⟩ := fin_steps hc.fin e ep
    refine ⟨t,13,((((sa.trans ab).trans bc).trans cd).trans de).trans et,by decide,tp,?_,
      (((((ar.trans br).trans cr).trans dr).trans er).trans tr).mono (by simp),
      (((((af.trans bf).trans cf).trans df).trans ef).trans tf).mono (by tauto)⟩
    rw [tr.get (by decide),e29]
    simp [CanonicalPolicy.threshold,show r≤21 by simp at hr;omega]
#print axioms threshold_steps
end SigGolfCandidate.T3M.Sign.SharedFloor

namespace SigGolfCandidate.T3M.Sign.SharedHints
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def firstCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x1de3823,0xe3303,0x1e400393,0xfff40f13,0xf0a63]
sym_block first := symRun { noAlias := true } firstCode (pcOf 22363) 100
def secondCode : List (BitVec 32) := bv_list% 32 [0x1600393,0xffe40f13,0xf0463]
sym_block second := symRun { noAlias := true } secondCode (pcOf 22370) 100
def thirdCode : List (BitVec 32) := bv_list% 32 [0x100393]
sym_block third := symRun { noAlias := true } thirdCode (pcOf 22373) 100
def addHintCode : List (BitVec 32) := bv_list% 32 [0x3d383b3,0x730333,0x6e3023]
sym_block addHint := symRun { noAlias := true } addHintCode (pcOf 22374) 100

theorem first_steps {im : Image} (hc : CodeAt im (pcOf 22363) firstCode)
    (s : MachineState) (hp : s.pc=pcOf 22363) (lay h f : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h29 : s.getReg .x29=BitVec.ofNat 64 f)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 h) :
    ∃ t,Steps im s 7 7 t ∧ t.pc=(if lay=1 then pcOf 22374 else pcOf 22370) ∧
      t.getReg .x6=BitVec.ofNat 64 h ∧ t.getReg .x7=484 ∧ t.getReg .x28=0x66000 ∧
      t.getMem (0x66010#64)=BitVec.ofNat 64 f ∧
      RegsExcept s t [.x6,.x7,.x28,.x30] ∧ Frame s t (fun A => A=0x66010) := by
  refine ⟨_,symRun_sound first hc s hp (by simp [first.res,rv_simp];try decide),?_,?_,?_,?_,?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩;interval_cases lay <;> simp [first.res,rv_simp,h8]
  · simp [first.res,rv_simp,hm]
  · simp [first.res,rv_simp]
  · simp [first.res,rv_simp]
  · simp [first.res,rv_simp,h29]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,first.res]; t3n []
    rw [if_neg (by omega)]

theorem second_steps {im : Image} (hc : CodeAt im (pcOf 22370) secondCode)
    (s : MachineState) (hp : s.pc=pcOf 22370) (lay : Nat) (hl : lay=2 ∨ lay=3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay=2 then pcOf 22374 else pcOf 22373) ∧
      t.getReg .x7=22 ∧ RegsExcept s t [.x7,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound second hc s hp (by simp [second.res,rv_simp]),?_,?_,?_,?_⟩
  · rcases hl with rfl|rfl <;> simp [second.res,rv_simp,h8]
  · simp [second.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem third_steps {im : Image} (hc : CodeAt im (pcOf 22373) thirdCode)
    (s : MachineState) (hp : s.pc=pcOf 22373) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22374 ∧ t.getReg .x7=1 ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound third hc s hp (by simp [third.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [third.res,rv_simp]
  · simp [third.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem add_steps {im : Image} (hc : CodeAt im (pcOf 22374) addHintCode)
    (s : MachineState) (hp : s.pc=pcOf 22374) (h f mul : Nat)
    (h6 : s.getReg .x6=BitVec.ofNat 64 h) (h7 : s.getReg .x7=BitVec.ofNat 64 mul)
    (h29 : s.getReg .x29=BitVec.ofNat 64 f) (h28 : s.getReg .x28=0x66000) :
    ∃ t,Steps im s 3 6 t ∧ t.pc=pcOf 22377 ∧
      t.getMem (0x66000#64)=BitVec.ofNat 64 (h+mul*f) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=0x66000) := by
  refine ⟨_,symRun_sound addHint hc s hp (by simp [addHint.res,rv_simp,h28];try decide),?_,?_,?_,?_⟩
  · simp [addHint.res,rv_simp]
  · simp only [Result.toState_getMem,addHint.res];t3n [h6,h7,h29,h28]
    simp [← BitVec.ofNat_mul,← BitVec.ofNat_add]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,addHint.res];t3n [h28]
    rw [if_neg (by omega)]
#print axioms add_steps
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedHints
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Code (im : Image) : Prop where
  first : CodeAt im (pcOf 22363) firstCode
  second : CodeAt im (pcOf 22370) secondCode
  third : CodeAt im (pcOf 22373) thirdCode
  add : CodeAt im (pcOf 22374) addHintCode

/-- Hint weight of layer `lay` (img-v4/v6 radix 484 / 22 / 1). -/
def hintWeight (lay : Nat) : Nat := if lay = 1 then 484 else if lay = 2 then 22 else 1
theorem steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22363)
    (lay h f : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h29 : s.getReg .x29=BitVec.ofNat 64 f)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 h) :
    ∃ t k,Steps im s k (k+3) t ∧ k≤14 ∧ t.pc=pcOf 22377 ∧
      t.getMem (0x66000#64)=BitVec.ofNat 64 (h+hintWeight lay*f) ∧
      t.getMem (0x66010#64)=BitVec.ofNat 64 f ∧
      RegsExcept s t [.x6,.x7,.x28,.x30] ∧ Frame s t (fun A => A=0x66000 ∨ A=0x66010) := by
  obtain ⟨a,sa,ap,a6,a7,a28,am,ar,af⟩ := first_steps hc.first s hp lay h f hl h8 h29 hm
  have a8 := (ar.get (by decide : Reg.x8 ∉ [.x6,.x7,.x28,.x30])).trans h8
  have a29 := (ar.get (by decide : Reg.x29 ∉ [.x6,.x7,.x28,.x30])).trans h29
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · obtain ⟨t,aToT,tp,tm,tr,tf⟩ := add_steps hc.add a (by simpa using ap) h f 484 a6 a7 a29 a28
    exact ⟨t,10,sa.trans aToT,by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans am,
      (ar.trans tr).mono (by simp),(af.trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b7,br,bf⟩ := second_steps hc.second a (by simpa using ap) 2 (by simp) a8
    obtain ⟨t,bt,tp,tm,tr,tf⟩ := add_steps hc.add b (by simpa using bp) h f 22
      ((br.get (by decide)).trans a6) b7 ((br.get (by decide)).trans a29) ((br.get (by decide)).trans a28)
    exact ⟨t,13,sa.trans (ab.trans bt),by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans ((bf.get (by decide) (by simp)).trans am),
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b7,br,bf⟩ := second_steps hc.second a (by simpa using ap) 3 (by simp) a8
    obtain ⟨c,bc,cp,c7,cr,cf⟩ := third_steps hc.third b (by simpa using bp)
    obtain ⟨t,ct,tp,tm,tr,tf⟩ := add_steps hc.add c cp h f 1
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a6)) c7
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a29))
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a28))
    exact ⟨t,14,sa.trans (ab.trans (bc.trans ct)),by decide,tp,by simpa [hintWeight] using tm,
      (tf.get (A:=0x66010) (by decide) (by decide)).trans ((cf.get (by decide) (by simp)).trans ((bf.get (by decide) (by simp)).trans am)),
      (((ar.trans br).trans cr).trans tr).mono (by simp),(((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
#print axioms steps
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_dispatch : DispatchCode Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedFloor
namespace SigGolfCandidate.T3M.Sign.SharedHints
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedHints


namespace SigGolfCandidate.T3M.Sign.SharedControlTail
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def initResidualCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x4d00313,0x6e3423]
sym_block initResidual := symRun { noAlias := true } initResidualCode (pcOf 22226) 100
def firstLayerCode : List (BitVec 32) := bv_list% 32 [0x100413]
sym_block firstLayer := symRun { noAlias := true } firstLayerCode (pcOf 22239) 100
def nextLayerCode : List (BitVec 32) := bv_list% 32 [0x140413,0x400313,0xc8646ae3]
sym_block nextLayer := symRun { noAlias := true } nextLayerCode (pcOf 22457) 100
def topProduceCode : List (BitVec 32) := bv_list% 32 [0x413,0x493,0xc00793,0x3600d13,0x3300d93,0x9200893,0x20e37,0x550e0e13,0xe3903,0x1395913,0x90713,0xf80ea06f]
sym_block topProduce := symRun { noAlias := true } topProduceCode (pcOf 22478) 100

theorem initResidual_steps {im : Image} (hc : CodeAt im (pcOf 22226) initResidualCode)
    (s : MachineState) (hp : s.pc=pcOf 22226) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22230 ∧ t.getMem (0x66008#64)=77 ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound initResidual hc s hp (by simp [initResidual.res,rv_simp];try decide),?_,?_,?_,?_⟩
  · simp [initResidual.res,rv_simp]
  · simp [initResidual.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,initResidual.res];t3n []
    rw [if_neg (by omega)]

theorem firstLayer_steps {im : Image} (hc : CodeAt im (pcOf 22239) firstLayerCode)
    (s : MachineState) (hp : s.pc=pcOf 22239) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22240 ∧ t.getReg .x8=1 ∧
      RegsExcept s t [.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound firstLayer hc s hp (by simp [firstLayer.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [firstLayer.res,rv_simp]
  · simp [firstLayer.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem nextLayer_steps {im : Image} (hc : CodeAt im (pcOf 22457) nextLayerCode)
    (s : MachineState) (hp : s.pc=pcOf 22457) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22240 else pcOf 22460) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧ RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound nextLayer hc s hp (by simp [nextLayer.res,rv_simp]),?_,?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩;interval_cases lay <;> simp [nextLayer.res,rv_simp,h8]
  · simp [nextLayer.res,rv_simp,h8,BitVec.ofNat_add]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

structure TopPost (index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=54
  n4 : t.getReg .x27=51
  target : t.getReg .x17=146
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  regs : RegsExcept s t [.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28]
  frame : Frame s t (fun _ => False)
theorem topProduce_steps {im : Image} (hc : CodeAt im (pcOf 22478) topProduceCode)
    (s : MachineState) (hp : s.pc=pcOf 22478) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 12 12 t ∧ TopPost index s t := by
  refine ⟨_,symRun_sound topProduce hc s hp (by simp [topProduce.res,rv_simp]),?_⟩
  constructor
  all_goals first
    | solve | simp [topProduce.res,rv_simp,hidx]
    | skip
  · simp only [topProduce.res,rv_simp,hidx]
    exact ofNat_shr index 19 (by omega)
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms topProduce_steps
end SigGolfCandidate.T3M.Sign.SharedControlTail


namespace SigGolfCandidate.T3M.Sign.SharedLowerRegisters
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
def code22377 : List (BitVec 32) := bv_list% 32 [0x2b00d13,0xd93,0xc900893,0x600793,0xfff40313,0x30463]
sym_block blk22377 := symRun { noAlias := true } code22377 (pcOf 22377) 100
def code22383 : List (BitVec 32) := bv_list% 32 [0x80006f]
sym_block blk22383 := symRun { noAlias := true } code22383 (pcOf 22383) 100
def code22384 : List (BitVec 32) := bv_list% 32 [0x700793]
sym_block blk22384 := symRun { noAlias := true } code22384 (pcOf 22384) 100
def code22385 : List (BitVec 32) := bv_list% 32 [0x20e37,0x550e0e13,0xe3303,0xfff40393,0x38c63]
sym_block blk22385 := symRun { noAlias := true } code22385 (pcOf 22385) 100
def code22390 : List (BitVec 32) := bv_list% 32 [0xffe40393,0x2038063]
sym_block blk22390 := symRun { noAlias := true } code22390 (pcOf 22390) 100
def code22392 : List (BitVec 32) := bv_list% 32 [0x3f37913,0x635493,0x200006f]
sym_block blk22392 := symRun { noAlias := true } code22392 (pcOf 22392) 100
def code22395 : List (BitVec 32) := bv_list% 32 [0xc35913,0x7f97913,0x1335493,0x100006f]
sym_block blk22395 := symRun { noAlias := true } code22395 (pcOf 22395) 100
def code22399 : List (BitVec 32) := bv_list% 32 [0x635913,0x3f97913,0xc35493]
sym_block blk22399 := symRun { noAlias := true } code22399 (pcOf 22399) 100
def code22402 : List (BitVec 32) := bv_list% 32 [0x90713,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block blk22402 := symRun { noAlias := true } code22402 (pcOf 22402) 100
def code22409 : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xbd5ea0ef]
sym_block blk22409 := symRun { noAlias := true } code22409 (pcOf 22409) 100
structure Code (im : Image) : Prop where
  at22377 : CodeAt im (pcOf 22377) code22377
  at22383 : CodeAt im (pcOf 22383) code22383
  at22384 : CodeAt im (pcOf 22384) code22384
  at22385 : CodeAt im (pcOf 22385) code22385
  at22390 : CodeAt im (pcOf 22390) code22390
  at22392 : CodeAt im (pcOf 22392) code22392
  at22395 : CodeAt im (pcOf 22395) code22395
  at22399 : CodeAt im (pcOf 22399) code22399
  at22402 : CodeAt im (pcOf 22402) code22402
  at22409 : CodeAt im (pcOf 22409) code22409
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22409
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  dst : t.getReg .x28=BitVec.ofNat 64 ENC
  src : t.getReg .x29=BitVec.ofNat 64 (0x66040+32*lay)
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun _ => False)
theorem setup1 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=1)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 23 23 t ∧ Post 1 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22384.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22384 hc.at22384 s1 (by simp [s1,blk22377.res,s2,blk22384.res,rv_simp,h8]) (by simp [blk22384.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22395.res.toState s3
  have st4 : Steps im s3 4 4 s4 := symRun_sound blk22395 hc.at22395 s3 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,rv_simp,h8]) (by simp [blk22395.res,rv_simp];try decide)
  let s5 := blk22402.res.toState s4
  have st5 : Steps im s4 7 7 s5 := symRun_sound blk22402 hc.at22402 s4 (by simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s5, st1.trans (st2.trans (st3.trans (st4.trans (st5)))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index >>> (12:Nat) &&& 127)=BitVec.ofNat 64 (index/2^12%2^7)
    rw [ofNat_shr index 12 (by omega)]
    exact ofNat_and_mask (index/2^12) 7 (by decide)
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (19:Nat)=BitVec.ofNat 64 (index/2^19)
    exact ofNat_shr index 19 (by omega)
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22384.res,s3,blk22385.res,s4,blk22395.res,s5,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms setup1
theorem setup2 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=2)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 24 24 t ∧ Post 2 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22383.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22383 hc.at22383 s1 (by simp [s1,blk22377.res,s2,blk22383.res,rv_simp,h8]) (by simp [blk22383.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22390.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22390 hc.at22390 s3 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,rv_simp,h8]) (by simp [blk22390.res,rv_simp];try decide)
  let s5 := blk22399.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22399 hc.at22399 s4 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,rv_simp,h8]) (by simp [blk22399.res,rv_simp];try decide)
  let s6 := blk22402.res.toState s5
  have st6 : Steps im s5 7 7 s6 := symRun_sound blk22402 hc.at22402 s5 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index >>> (6:Nat) &&& 63)=BitVec.ofNat 64 (index/2^6%2^6)
    rw [ofNat_shr index 6 (by omega)]
    exact ofNat_and_mask (index/2^6) 6 (by decide)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (12:Nat)=BitVec.ofNat 64 (index/2^12)
    exact ofNat_shr index 12 (by omega)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22399.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms setup2
theorem setup3 {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 22377)
    (index : Nat) (hi : index<2^31) (h8 : s.getReg .x8=3)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t,Steps im s 24 24 t ∧ Post 3 index s t := by
  let s1 := blk22377.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound blk22377 hc.at22377 s hp (by simp [blk22377.res,rv_simp];try decide)
  let s2 := blk22383.res.toState s1
  have st2 : Steps im s1 1 1 s2 := symRun_sound blk22383 hc.at22383 s1 (by simp [s1,blk22377.res,s2,blk22383.res,rv_simp,h8]) (by simp [blk22383.res,rv_simp];try decide)
  let s3 := blk22385.res.toState s2
  have st3 : Steps im s2 5 5 s3 := symRun_sound blk22385 hc.at22385 s2 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,rv_simp,h8]) (by simp [blk22385.res,rv_simp];try decide)
  let s4 := blk22390.res.toState s3
  have st4 : Steps im s3 2 2 s4 := symRun_sound blk22390 hc.at22390 s3 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,rv_simp,h8]) (by simp [blk22390.res,rv_simp];try decide)
  let s5 := blk22392.res.toState s4
  have st5 : Steps im s4 3 3 s5 := symRun_sound blk22392 hc.at22392 s4 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,rv_simp,h8]) (by simp [blk22392.res,rv_simp];try decide)
  let s6 := blk22402.res.toState s5
  have st6 : Steps im s5 7 7 s6 := symRun_sound blk22402 hc.at22402 s5 (by simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8]) (by simp [blk22402.res,rv_simp];try decide)
  refine ⟨s6, st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6))))), ?_⟩
  constructor
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change (BitVec.ofNat 64 index &&& 63)=BitVec.ofNat 64 (index%2^6)
    exact ofNat_and_mask index 6 (by decide)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp only [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
    change BitVec.ofNat 64 index >>> (6:Nat)=BitVec.ofNat 64 (index/2^6)
    exact ofNat_shr index 6 (by omega)
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · simp [s1,blk22377.res,s2,blk22383.res,s3,blk22385.res,s4,blk22390.res,s5,blk22392.res,s6,blk22402.res,rv_simp,h8,hidx,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
#print axioms setup3
end SigGolfCandidate.T3M.Sign.SharedLowerRegisters


namespace SigGolfCandidate.T3M.Sign.SharedLowerCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def code : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xbd5ea0ef]
sym_block block := symRun { noAlias := true } code (pcOf 22409) 100

structure Post (lay : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  regs : RegsExcept s t [.x1,.x6,.x7]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)
theorem steps {im : Image} (hc : CodeAt im (pcOf 22409) code)
    (s : MachineState) (hp : s.pc=pcOf 22409) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC)
    (h29 : s.getReg .x29=BitVec.ofNat 64 (0x66040+32*lay)) :
    ∃ t,Steps im s 9 9 t ∧ Post lay s t := by
  rcases hl with ⟨hlo,hhi⟩
  have hob : block.res.obligs s := by
    interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC] <;> decide
  refine ⟨_,symRun_sound block hc s hp hob,?_⟩
  constructor
  · simp [block.res,rv_simp]
  · simp [block.res,rv_simp]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · interval_cases lay <;> simp [block.res,rv_simp,h28,h29,ENC]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res];t3n [h28,ENC]
    unfold ENC at hn
    repeat rw [if_neg (by omega)]
#print axioms steps
end SigGolfCandidate.T3M.Sign.SharedLowerCopy


namespace SigGolfCandidate.T3M.Sign.SharedLowerSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Post (lay index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)

theorem registers {im : Image} (hc : SharedLowerRegisters.Code im) (s : MachineState)
    (hp : s.pc=pcOf 22377) (lay index : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k,Steps im s k k t ∧ k≤24 ∧ SharedLowerRegisters.Post lay index s t := by
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup1 hc s hp index hi h8 hidx
    exact ⟨t,23,ht,by decide,hp⟩
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup2 hc s hp index hi h8 hidx
    exact ⟨t,24,ht,by decide,hp⟩
  · obtain ⟨t,ht,hp⟩ := SharedLowerRegisters.setup3 hc s hp index hi h8 hidx
    exact ⟨t,24,ht,by decide,hp⟩

theorem setup {im : Image} (hc : SharedLowerRegisters.Code im) (s : MachineState)
    (hp : s.pc=pcOf 22377) (lay index : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index) :
    ∃ t k,Steps im s k k t ∧ k≤33 ∧ Post lay index s t := by
  obtain ⟨a,k,sa,hk,ha⟩ := registers hc s hp lay index hl hi h8 hidx
  obtain ⟨t,aToT,ht⟩ := SharedLowerCopy.steps hc.at22409 a ha.pc lay hl ha.dst ha.src
  refine ⟨t,k+9,sa.trans aToT,by omega,?_⟩
  refine ⟨ht.pc,ht.ret,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (ht.regs.get (by decide)).trans ha.chains
  · exact (ht.regs.get (by decide)).trans ha.n4
  · exact (ht.regs.get (by decide)).trans ha.target
  · exact (ht.regs.get (by decide)).trans ha.height
  · exact (ht.regs.get (by decide)).trans ha.leaf
  · rw [ht.regs.get (by decide),ht.regs.get (by decide)];exact ha.selected
  · exact (ht.regs.get (by decide)).trans ha.tree
  · exact ht.leftLo.trans (ha.frame.get (by omega) (by simp))
  · exact ht.leftHi.trans (ha.frame.get (by omega) (by simp))
  · exact ht.rightLo.trans (ha.frame.get (by omega) (by simp))
  · exact ht.rightHi.trans (ha.frame.get (by omega) (by simp))
  · exact (ha.regs.trans ht.regs).mono (by simp)
  · exact (ha.frame.trans ht.frame).mono (by tauto)
#print axioms setup
end SigGolfCandidate.T3M.Sign.SharedLowerSetup


namespace SigGolfCandidate.T3M.Sign.SharedLowerSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.WCT9
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure CallPost (lay index residual hints : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22418
  chains : t.getReg .x26=43
  n4 : t.getReg .x27=0
  target : t.getReg .x17=201
  height : t.getReg .x15=BitVec.ofNat 64 (if lay=1 then 7 else 6)
  leaf : t.getReg .x18=BitVec.ofNat 64 (if lay=1 then index/4096%128 else if lay=2 then index/64%64 else index%64)
  selected : t.getReg .x14=t.getReg .x18
  tree : t.getReg .x9=BitVec.ofNat 64 (if lay=1 then index/524288 else if lay=2 then index/4096 else index/64)
  leftLo : t.getMem (BitVec.ofNat 64 ENC)=s.getMem (BitVec.ofNat 64 (0x66040+32*lay))
  leftHi : t.getMem (BitVec.ofNat 64 (ENC+8))=s.getMem (BitVec.ofNat 64 (0x66048+32*lay))
  rightLo : t.getMem (BitVec.ofNat 64 (ENC+48))=s.getMem (BitVec.ofNat 64 (0x66050+32*lay))
  rightHi : t.getMem (BitVec.ofNat 64 (ENC+56))=s.getMem (BitVec.ofNat 64 (0x66058+32*lay))
  floor : t.getMem (0x66010#64)=BitVec.ofNat 64 (ClaudeWCT.WCT9.CanonicalPolicy.threshold lay residual)
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (hints+SharedHints.hintWeight lay*ClaudeWCT.WCT9.CanonicalPolicy.threshold lay residual)
  layer : t.getReg .x8=BitVec.ofNat 64 lay
  regs : RegsExcept s t [.x1,.x6,.x7,.x9,.x14,.x15,.x17,.x18,.x20,.x26,.x27,.x28,.x29,.x30]
  frame : Frame s t (fun A => A=0x66000 ∨ A=0x66010 ∨ A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)


theorem call_steps {im : Image} (hf : SharedFloor.DispatchCode im) (hh : SharedHints.Code im)
    (hc : SharedLowerRegisters.Code im) (s : MachineState) (hp : s.pc=pcOf 22240)
    (lay index residual hints : Nat) (hl : 1≤lay ∧ lay≤3) (hi : index<2^31)
    (hr : residual < if lay=1 then 56 else if lay=2 then 41 else 22)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hidx : s.getMem (0x20550#64)=BitVec.ofNat 64 index)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual)
    (hhm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t k c,Steps im s k c t ∧ c≤120 ∧ CallPost lay index residual hints s t := by
  obtain ⟨a,ka,sa,hka,ap,a29,ar,af⟩ := SharedFloor.threshold_steps hf s hp lay residual hl hr h8 hrm
  have a8 := (ar.get (by decide : Reg.x8 ∉ [.x6,.x20,.x28,.x29])).trans h8
  obtain ⟨b,kb,ab,hkb,bp,bhints,bfloor,br,bf⟩ := SharedHints.steps hh a ap lay hints _ hl a8 a29
    ((af.get (A:=0x66000) (by decide) (by simp)).trans hhm)
  have b8 := (br.get (by decide : Reg.x8 ∉ [.x6,.x7,.x28,.x30])).trans a8
  have bidx : b.getMem (0x20550#64)=BitVec.ofNat 64 index :=
    (bf.get (A:=0x20550) (by decide) (by decide)).trans ((af.get (by decide) (by simp)).trans hidx)
  obtain ⟨t,kc,bt,hkc,ht⟩ := setup hc b bp lay index hl hi b8 bidx
  refine ⟨t,ka+kb+kc,ka+(kb+3)+kc,(sa.trans ab).trans bt,by omega,?_⟩
  refine ⟨ht.pc,ht.ret,ht.chains,ht.n4,ht.target,ht.height,ht.leaf,ht.selected,ht.tree,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ht.leftLo.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.leftHi.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.rightLo.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact ht.rightHi.trans ((bf.get (by omega) (by omega)).trans (af.get (by omega) (by simp)))
  · exact (ht.frame.get (A:=0x66010) (by decide) (by unfold ENC;decide)).trans bfloor
  · exact (ht.frame.get (A:=0x66000) (by decide) (by unfold ENC;decide)).trans bhints
  · exact (ht.regs.get (by decide)).trans b8
  · exact ((ar.trans br).trans ht.regs).mono (by simp)
  · exact ((af.trans bf).trans ht.frame).mono (by tauto)
#print axioms call_steps
end SigGolfCandidate.T3M.Sign.SharedLowerSetup


namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest Pieces chainCount height)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem prepared_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (hsetup : SetupCode im)
    (lay : Layer) (hl : lay≠0) (leaf : Nat) (p : PreparedLower) (digits : List Nat)
    (hd : ∀ j,j<43 → digits.getD j 0<8)
    (s : MachineState) (hp : s.pc=pcOf 22418) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits.getD j 0))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay.val j d) ((p.prefixes.getD j []).getD d 0))
    (ha : DigsAt s (sigBase lay.val+688) (preparedPieces lay leaf p digits).2) :
    ∃ t k,Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (sigBase lay.val) (preparedPieces lay leaf p digits).1 ∧
      DigsAt t (sigBase lay.val+688) (preparedPieces lay leaf p digits).2 ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => sigBase lay.val≤A ∧ A<sigBase lay.val+688) := by
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have hbound := lay.isLt
  obtain ⟨t,k,hs,hk,tp,tv,tr,tf⟩ := reveal_steps hc hbcode hsetup lay.val (by omega) (by omega)
    (fun j => digits.getD j 0) (fun j d => (p.prefixes.getD j []).getD d 0) hd s hp h8 hb hv
  refine ⟨t,k,hs,hk,tp,?_,?_,tr,tf⟩
  · have hcc : chainCount lay=43 := by fin_cases lay <;> simp_all [chainCount]
    simpa [preparedPieces,hcc] using tv
  · intro j hj
    have hj' : j<height lay := by simpa [preparedPieces] using hj
    have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
    exact (ha j hj).frame tf
      (by unfold sigBase;split_ifs <;> omega)
      (by intro h;omega)
      (by intro h;omega)
#print axioms prepared_steps
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_hooks : CanonicalHooks.Code Images.signImage := by
  constructor
  · constructor <;> sign_slice_fast
  all_goals sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedSearchCode

namespace SigGolfCandidate.T3M.Sign.SharedControlTail
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_initResidual : CodeAt Images.signImage (pcOf 22226) initResidualCode := by
  sign_slice_fast
theorem installed_firstLayer : CodeAt Images.signImage (pcOf 22239) firstLayerCode := by
  sign_slice_fast
theorem installed_nextLayer : CodeAt Images.signImage (pcOf 22457) nextLayerCode := by
  sign_slice_fast
theorem installed_topProduce : CodeAt Images.signImage (pcOf 22478) topProduceCode := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedControlTail
namespace SigGolfCandidate.T3M.Sign.SharedLowerRegisters
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor <;> sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedLowerRegisters
namespace SigGolfCandidate.T3M.Sign.SharedLowerCopy
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : CodeAt Images.signImage (pcOf 22409) code := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedLowerCopy

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def code : List (BitVec 32) := bv_list% 32 [0xfffe37,0xe0e13,0x260e0ba3,0xff0fd06f]
sym_block block := symRun {noAlias:=true} code (pcOf 24661) 6

theorem steps {im : Image} (hc : CodeAt im (pcOf 24661) code)
    (s : MachineState) (hp : s.pc=pcOf 24661) (flag : Nat) (hf : CfTableOK flag s) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22100 ∧ CfTableOK 0 t ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=TOP_DATA+624) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [block.res,rv_simp]
  · intro i hi hj
    have old:=hf i hi hj
    rw [getByte_eq_word _ _ (by unfold TOP_DATA;omega)]
    rw [getByte_eq_word _ _ (by unfold TOP_DATA;omega)] at old
    interval_cases i <;> simp only [cfByte] at old ⊢ <;>
      simp [block.res,rv_simp,TOP_DATA] at old ⊢ <;> try exact old
    all_goals first
      | exact extractByte_replaceByte_same _ _ (by decide) _
      | rw [extractByte_replaceByte_diff _ _ _ (by decide) (by decide) (by decide)];exact old
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res];t3n []
    rw [if_neg (by unfold TOP_DATA at hn;omega)]
#print axioms steps
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : CodeAt Images.signImage (pcOf 24661) code := by
  sign_slice_fast
theorem installed_jump : CodeAt Images.signImage (pcOf 378) [0x36d1706f] := by
  sign_slice_fast
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem byte_result (s : MachineState) (A : Nat) (ha : A<2^64) :
    (block.res.toState s).getByte (BitVec.ofNat 64 A) =
      if A=TOP_DATA+631 then 0 else s.getByte (BitVec.ofNat 64 A) := by
  rw [getByte_eq_word _ _ ha,getByte_eq_word _ _ ha]
  simp only [Result.toState_getMem,block.res];t3n []
  rw [Nat.mod_eq_of_lt (show A/8*8<18446744073709551616 by omega)]
  by_cases he : A/8*8=16773744
  · rw [if_pos he]
    by_cases hf : A=TOP_DATA+631
    · rw [if_pos hf]
      subst A
      exact extractByte_replaceByte_same _ _ (by decide) _
    · rw [if_neg hf]
      have hm : A%8≠7 := by unfold TOP_DATA at hf;omega
      rw [extractByte_replaceByte_diff _ _ _ (Nat.mod_lt _ (by decide)) (by decide) hm]
      rw [show BitVec.ofNat 64 (A/8*8)=16773744#64 by rw [he]]
  · rw [if_neg he,if_neg (by unfold TOP_DATA;omega)]
#print axioms byte_result
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem tables_result (s : MachineState) (flag : Nat) (ht : TableOK s)
    (hf : CfTableOK flag s) (hr : Reward.RewardTablesOK s) :
    TableOK (block.res.toState s) ∧ CfTableOK 0 (block.res.toState s) ∧
      Reward.RewardTablesOK (block.res.toState s) := by
  constructor
  · intro i hi
    rw [byte_result _ _ (by unfold TOP_DATA;omega),if_neg (by omega)]
    exact ht i hi
  constructor
  · intro i hi hj
    rw [byte_result _ _ (by unfold TOP_DATA;omega)]
    by_cases h : i=631
    · subst i;simp [cfByte]
    · rw [if_neg (by omega),hf i hi hj]
      simp [cfByte,h]
  · intro i hi hj
    rw [byte_result _ _ (by unfold TOP_DATA;omega),if_neg (by omega)]
    exact hr i hi hj
#print axioms tables_result
end SigGolfCandidate.T3M.Sign.SharedFlagInit

namespace SigGolfCandidate.T3M.Sign.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_kernel (P : Prop) (hP : P) : KernAt Images.signImage 543 P := by
  refine ⟨⟨?_,?_⟩,Or.inr rfl,?_,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  all_goals sign_slice_fast
theorem installed_searchKernel : KernAt Images.signImage 543 (CanonicalHooks.Code Images.signImage) :=
  installed_kernel _ installed_hooks
end SigGolfCandidate.T3M.Sign.SharedSearchCode

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

structure Tables (s : MachineState) : Prop where
  x5 : s.getReg .x5=0
  z40 : s.getMem (BitVec.ofNat 64 (ENC+40))=0
  table : TableOK s
  cf : CfTableOK 0 s
  reward : Reward.RewardTablesOK s
  zt : ZeroCap.ZtOK 543 s

def TableCells (A : Nat) : Prop := A=ENC+40 ∨ TOP_DATA≤A ∧ A<TOP_DATA+2944 ∨ 16691072≤A ∧ A<16691200

theorem Tables.frame {s t : MachineState} {W : Nat→Prop} {regs : List Reg}
    (h : Tables s) (hf : Frame s t W) (hr : RegsExcept s t regs) (h5 : .x5∉regs)
    (hw : ∀ A, TableCells A → ¬W A) : Tables t := by
  refine ⟨(hr.get h5).trans h.x5,?_,?_,?_,?_,?_⟩
  · exact (hf.get (by unfold ENC;decide) (hw _ (Or.inl rfl))).trans h.z40
  · exact h.table.frame hf (fun i hi => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.cf.frame hf (fun i hi hj => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.reward.frame hf (fun i hi hj => hw _ (Or.inr (Or.inl (by unfold TOP_DATA;omega))))
  · exact h.zt.frame hf (fun r hr => hw _ (Or.inr (Or.inr (by
      simp only [ZeroCap.ZT, if_neg (show (543:Nat) ≠ 354 by decide)]; omega))))

def topArgs (index : Nat) (pair : Digest×Digest) : Canonical.CsArgs :=
  ⟨0,(route index 0).2,(route index 0).1,.pair pair.1 pair.2,22208,22⟩

theorem top_pre (index : Nat) (hi : index<2^31) (pair : Digest×Digest)
    (s t : MachineState) (h : SharedTopSetup.Post index pair.1 pair.2 s t)
    (ht : Tables t) (hc : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    Canonical.CsPre 543 (topArgs index pair) t := by
  have hr : (route index 0).2=0 := T3.route_top_tree index hi
  have hl : (route index 0).1=index/2^19 := by
    change index/2^19%2^12=index/2^19
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨h.pc,h.ret,ht.x5,h.x8,?_,?_,h.x17,h.x26,h.x27,?_,?_,?_,Or.inl hr,
    h.left.1,h.left.2,hc,ht.z40,h.right.1,h.right.2,ht.table,ht.cf,ht.reward,ht.zt,
    by intro h; exact (h rfl).elim,by intro; rfl,?_⟩
  · simpa [topArgs,hr] using h.x9
  · simpa only [topArgs,hl] using h.x18
  · change (route index 0).2<2^32;rw [hr];decide
  · change (route index 0).1<2^32;rw [hl];omega
  · change (route index 0).2*2^12+(route index 0).1<2^32;rw [hr,hl];omega
  · intro hn;exact (hn rfl).elim

def lowerArgs (lay : Layer) (index floor : Nat) (pair : Digest×Digest) : Canonical.CsArgs :=
  ⟨lay,(route index lay).2,(route index lay).1,.pair pair.1 pair.2,22418,floor⟩

theorem lower_pre (lay : Layer) (hl : lay≠0) (index residual hints : Nat) (hi : index<2^31)
    (pair : Digest×Digest) (s t : MachineState) (h : SharedLowerSetup.CallPost lay.val index residual hints s t)
    (ht : Tables t) (hc : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hp0 : DigAt s (0x66040+32*lay.val) pair.1)
    (hp1 : DigAt s (0x66050+32*lay.val) pair.2)
    (hf : CanonicalPolicy.threshold lay.val residual<22) :
    Canonical.CsPre 543 (lowerArgs lay index (CanonicalPolicy.threshold lay.val residual) pair) t := by
  have htree : (route index lay).2<2^32 := by fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  have hleaf : (route index lay).1<2^32 := by fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  have hroute : (route index lay).2*2^height lay+(route index lay).1<2^32 := by
    fin_cases lay <;> simp_all [T3.route,T3.height] <;> omega
  refine ⟨h.pc,h.ret,ht.x5,h.layer,?_,?_,?_,?_,?_,htree,hleaf,hroute,Or.inr ?_,
    h.leftLo.trans hp0.1,?_,hc,ht.z40,h.rightLo.trans hp1.1,?_,ht.table,ht.cf,ht.reward,ht.zt,(by intro _; exact hf),?_,?_⟩
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.tree
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.leaf
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.target
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.chains
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.n4
  · fin_cases lay <;> (try exact (hl rfl).elim) <;> simpa [lowerArgs,T3.route,T3.height,T3.chainCount,T3.target,CanonicalPolicy.normalLayer,Search.csN4] using h.height
  · change t.getMem (BitVec.ofNat 64 (ENC+8))=pair.1.extractLsb' 64 64
    have he : 0x66048+32*lay.val=(0x66040+32*lay.val)+8 := by omega
    exact h.leftHi.trans (he ▸ hp0.2)
  · change t.getMem (BitVec.ofNat 64 (ENC+56))=pair.2.extractLsb' 64 64
    have he : 0x66058+32*lay.val=(0x66050+32*lay.val)+8 := by omega
    exact h.rightHi.trans (he ▸ hp1.2)
  · intro he;exact (hl he).elim
  · intro _;exact h.floor

theorem credit_small (lay : Layer) (low : Bool) (ds : List Nat) : CanonicalPolicy.credit lay low ds<2^32 := by
  have hword : wordCredit lay ds≤T3.chainCount lay := by
    simpa only [wordCredit,List.length_range] using List.length_filter_le (fun i => decide (ds.getD i 0+1=T3.maxDigit lay i)) (List.range (T3.chainCount lay))
  have hcopy : savedCopies lay ds≤T3.chainCount lay := by
    simpa only [savedCopies,List.length_range] using List.length_filter_le (fun i => decide (safeZeroCopy lay ds i)) (List.range (T3.chainCount lay))
  have hc : T3.chainCount lay≤54 := by fin_cases lay <;> decide
  have hb := CanonicalPolicy.pathBonus_le lay low
  unfold CanonicalPolicy.credit CanonicalPolicy.pathReward CanonicalPolicy.reward
  omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def ValueWrites (A : Nat) : Prop :=
  ∃ lay : Nat, 1≤lay ∧ lay≤3 ∧ SharedRootControl.sigBase lay≤A ∧ A<SharedRootControl.sigBase lay+688

def WorkWrites (A : Nat) : Prop :=
  (ENC≤A ∧ A<ENC+40) ∨ (ENC+48≤A ∧ A<ENC+64) ∨
  (EOUT≤A ∧ A<EOUT+32) ∨ (DIGITS≤A ∧ A<DIGITS+64) ∨
  (0x66000≤A ∧ A<0x66020 ∨ A=0x667F8) ∨ (0x66100≤A ∧ A<0x66138) ∨ ValueWrites A

theorem work_bound {A : Nat} (h : WorkWrites A) : A<0x66800 := by
  rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_table {A : Nat} (h : TableCells A) : ¬WorkWrites A := by
  rcases h with rfl|h
  · intro h
    rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
    all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
    unfold SharedRootControl.sigBase at hb he
    split_ifs at hb he <;> unfold ENC at * <;> omega
  · intro hw
    have := work_bound hw
    unfold TOP_DATA at h
    omega

theorem work_not_meta {A : Nat} (hl : 0x66040≤A) (hu : A<0x660c0) : ¬WorkWrites A := by
  intro h
  rcases h with h|h|h|h|h|h|⟨lay,hlay,ulay,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_index : ¬WorkWrites 0x20550 := by
  intro h
  rcases h with h|h|h|h|h|h|⟨lay,hl,hu,hb,he⟩
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at hb he
  split_ifs at hb he <;> omega

theorem work_not_path (lay : Layer) (hl : lay≠0) (j half : Nat)
    (hj : j<height lay) (hh : half<2) :
    ¬WorkWrites (SharedRootControl.sigBase lay.val+688+16*j+8*half) := by
  intro h
  rcases h with h|h|h|h|h|h|⟨other,ho1,ho3,hlo,hhi⟩
  all_goals first
    | (fin_cases lay <;> simp_all [SharedRootControl.sigBase,height,ENC,EOUT,DIGITS] <;> omega)
    | skip
  interval_cases other <;> fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega

theorem stored_frame {s t : MachineState} (hf : Frame s t WorkWrites)
    (lay : Layer) (hl : lay≠0) (index : Nat) (p : PreparedLower)
    (h : SharedRootControl.Stored lay index p s) : SharedRootControl.Stored lay index p t := by
  have hln : 1≤lay.val := by have := lay.isLt;by_contra hh;apply hl;exact Fin.ext (by omega)
  have hlu : lay.val<4 := lay.isLt
  refine ⟨h.plen,?_,?_,?_,?_⟩
  · intro i hi k hk
    apply (h.saved i hi k hk).frame hf
    · unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer;omega
    · intro hw;have := work_bound hw
      unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer at this;omega
    · intro hw;have := work_bound hw
      unfold ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer at this;omega
  · intro j hj
    have hj' : j<height lay := by simpa only [List.length_map,List.length_range] using hj
    apply (h.path j hj).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega
    · simpa only [Nat.mul_zero,Nat.add_zero] using work_not_path lay hl j 0 hj' (by decide)
    · simpa only [Nat.mul_one] using work_not_path lay hl j 1 hj' (by decide)
  · apply h.left.frame hf
    · unfold SharedRootControl.metaAddr;omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
  · apply h.right.frame hf
    · unfold SharedRootControl.metaAddr;omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega
    · apply work_not_meta <;> unfold SharedRootControl.metaAddr <;> omega

structure Stable (index : Nat) (prepared : PreparedRoots) (forest : Digest×Digest) (s : MachineState) : Prop where
  tables : Tables s
  indexMem : s.getMem (0x20550#64)=BitVec.ofNat 64 index
  one : SharedRootControl.Stored 1 index prepared.one s
  two : SharedRootControl.Stored 2 index prepared.two s
  three : SharedRootControl.Stored 3 index prepared.three s
  forestL : DigAt s 0x660a0 forest.1
  forestR : DigAt s 0x660b0 forest.2

theorem Stable.frame {s t : MachineState} {index : Nat} {prepared : PreparedRoots} {forest : Digest×Digest}
    {regs : List Reg} (h : Stable index prepared forest s) (hf : Frame s t WorkWrites)
    (hr : RegsExcept s t regs) (h5 : .x5∉regs) : Stable index prepared forest t := by
  refine ⟨h.tables.frame hf hr h5 (fun _ => work_not_table),
    (hf.get (by decide) work_not_index).trans h.indexMem,
    stored_frame hf 1 (by decide) _ _ h.one,stored_frame hf 2 (by decide) _ _ h.two,
    stored_frame hf 3 (by decide) _ _ h.three,?_,?_⟩
  · exact h.forestL.frame hf (by decide) (work_not_meta (by decide) (by decide)) (work_not_meta (by decide) (by decide))
  · exact h.forestR.frame hf (by decide) (work_not_meta (by decide) (by decide)) (work_not_meta (by decide) (by decide))

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure TopTailSteps (im : Image) : Prop where
  save : ∀ s : MachineState, s.pc=pcOf 22208 →
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22226 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => 0x66100≤A ∧ A<0x66100+56)
  init : ∀ s : MachineState, s.pc=pcOf 22226 →
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 22230 ∧ t.getMem (0x66008#64)=77 ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008)
  residual : ∀ s : MachineState, s.pc=pcOf 22230 → ∀ r c : Nat, r<2^32 → c<2^32 →
    s.getMem (0x66008#64)=BitVec.ofNat 64 r → s.getMem (0x66018#64)=BitVec.ofNat 64 c →
    ∃ t k,Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22239 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008)
  first : ∀ s : MachineState, s.pc=pcOf 22239 →
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22240 ∧ t.getReg .x8=1 ∧
      RegsExcept s t [.x8] ∧ Frame s t (fun _ => False)

def TopTailWrites (A : Nat) : Prop := (0x66100≤A ∧ A<0x66138) ∨ A=0x66008

theorem topTail_subset {A : Nat} (h : TopTailWrites A) : WorkWrites A := by
  rcases h with h|rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

structure TopTailPost (low : Bool) (ds : List Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual 77 0 low ds)
  saved : ∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))
  regs : RegsExcept s t [.x6,.x7,.x8,.x28,.x29]
  frame : Frame s t TopTailWrites

theorem top_tail {im : Image} (hc : TopTailSteps im)
    (s : MachineState) (hp : s.pc=pcOf 22208) (low : Bool) (ds : List Nat)
    (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds)) :
    ∃ t k,Steps im s k k t ∧ k≤31 ∧ TopTailPost low ds s t := by
  obtain ⟨a,sa,ap,asaved,ar,af⟩ := hc.save s hp
  obtain ⟨b,ab,bp,brm,br,bf⟩ := hc.init a ap
  have bcm : b.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit 0 low ds) :=
    (bf.get (by decide) (by decide)).trans ((af.get (by decide) (by omega)).trans hcm)
  obtain ⟨c,k,bc,hk,cp,crm,cr,cf⟩ := hc.residual b bp 77 (CanonicalPolicy.credit 0 low ds) (by decide) (credit_small _ _ _) brm bcm
  obtain ⟨t,ct,tp,t8,tr,tf⟩ := hc.first c cp
  refine ⟨t,18+4+k+1,((sa.trans ab).trans bc).trans ct,by omega,?_,t8,?_,?_,?_,?_⟩
  · exact tp
  · exact (tf.get (by decide) (by simp)).trans crm
  · intro i hi
    exact (tf.get (by omega) (by simp)).trans ((cf.get (by omega) (by omega)).trans
      ((bf.get (by omega) (by omega)).trans (asaved i hi)))
  · exact (((ar.trans br).trans cr).trans tr).mono (by simp)
  · exact (((af.trans bf).trans cf).trans tf).mono (by
      intro A hA h;rcases h with ((h|h)|h)|h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
      · exact h.elim)

theorem top_residual_small {low : Bool} {ds : List Nat} (h : 22≤CanonicalPolicy.credit 0 low ds) :
    CanonicalPolicy.nextResidual 77 0 low ds<56 := by
  unfold CanonicalPolicy.nextResidual;omega

theorem words_bytes {s t : MachineState} (A B n : Nat) (hA : A%8=0) (hB : B%8=0)
    (hs : A+8*n<2^64) (ht : B+8*n<2^64)
    (hw : ∀ i,i<n → t.getMem (BitVec.ofNat 64 (B+8*i))=s.getMem (BitVec.ofNat 64 (A+8*i)))
    (j : Nat) (hj : j<8*n) :
    t.getByte (BitVec.ofNat 64 (B+j))=s.getByte (BitVec.ofNat 64 (A+j)) := by
  rw [getByte_eq_word t (B+j) (by omega),getByte_eq_word s (A+j) (by omega)]
  have ha : (A+j)/8*8=A+8*(j/8) := by omega
  have hb : (B+j)/8*8=B+8*(j/8) := by omega
  rw [ha,hb,hw _ (by omega)]
  congr 1
  omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure LowerTailSteps (im : Image) : Prop where
  reveal : ∀ (lay : Layer), lay≠0 → ∀ (leaf : Nat) (p : PreparedLower) (ds : List Nat),
    (∀ j,j<43 → ds.getD j 0<8) → ∀ s : MachineState, s.pc=pcOf 22418 →
    s.getReg .x8=BitVec.ofNat 64 lay.val →
    (∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)) →
    (∀ j,j<43 → ∀ d,d<8 → DigAt s (ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer lay.val j d) ((p.prefixes.getD j []).getD d 0)) →
    DigsAt s (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2 →
    ∃ t k,Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay leaf p ds).1 ∧
      DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2 ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688)
  residual : ∀ s : MachineState, s.pc=pcOf 22448 → ∀ r c : Nat, r<2^32 → c<2^32 →
    s.getMem (0x66008#64)=BitVec.ofNat 64 r → s.getMem (0x66018#64)=BitVec.ofNat 64 c →
    ∃ t k,Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22457 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008)
  next : ∀ s : MachineState, s.pc=pcOf 22457 → ∀ lay : Nat, (1≤lay ∧ lay≤3) →
    s.getReg .x8=BitVec.ofNat 64 lay →
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if lay<3 then pcOf 22240 else pcOf 22460) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧ RegsExcept s t [.x6,.x8] ∧ Frame s t (fun _ => False)

def LowerTailWrites (lay : Layer) (A : Nat) : Prop :=
  (SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688) ∨ A=0x66008

theorem lowerTail_subset (lay : Layer) (hl : lay≠0) {A : Nat} (h : LowerTailWrites lay A) : WorkWrites A := by
  have hh := lay.isLt
  have hz : lay.val≠0 := fun h=>hl (Fin.ext h)
  rcases h with h|rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lay.val,by omega,by omega,h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

structure LowerTailPost (lay : Layer) (leaf residual : Nat) (p : PreparedLower) (low : Bool) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=(if lay.val<3 then pcOf 22240 else pcOf 22460)
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual residual lay low ds)
  values : DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay leaf p ds).1
  path : DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2
  regs : RegsExcept s t [.x6,.x7,.x8,.x21,.x22,.x23,.x24,.x28]
  frame : Frame s t (LowerTailWrites lay)

theorem lower_tail {im : Image} (hc : LowerTailSteps im)
    (lay : Layer) (hl : lay≠0) (leaf residual : Nat) (p : PreparedLower) (low : Bool) (ds : List Nat)
    (hd : ∀ j,j<43 → ds.getD j 0<8) (s : MachineState) (hp : s.pc=pcOf 22418)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (ClaudeWCT.W9.Machine.Sign.SharedPrefixes.buffer lay.val j d) ((p.prefixes.getD j []).getD d 0))
    (ha : DigsAt s (SharedRootControl.sigBase lay.val+688) (preparedPieces lay leaf p ds).2)
    (hr : residual<2^32) (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual)
    (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 (CanonicalPolicy.credit lay low ds)) :
    ∃ t k,Steps im s k k t ∧ k≤587 ∧ LowerTailPost lay leaf residual p low ds s t := by
  have hln : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt;have : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  have hsbase : SharedRootControl.sigBase lay.val+1024<0x66000 := by unfold SharedRootControl.sigBase;split_ifs <;> omega
  obtain ⟨a,ka,sa,hka,ap,av,aa,ar,af⟩ := hc.reveal lay hl leaf p ds hd s hp h8 hb hv ha
  obtain ⟨b,kb,ab,hkb,bp,brm,br,bf⟩ := hc.residual a ap residual (CanonicalPolicy.credit lay low ds) hr (credit_small _ _ _)
    ((af.get (by decide) (by omega)).trans hrm) ((af.get (by decide) (by omega)).trans hcm)
  have b8 := (br.get (by decide : Reg.x8∉[.x6,.x7,.x28])).trans ((ar.get (by decide)).trans h8)
  obtain ⟨t,bt,tp,t8,tr,tf⟩ := hc.next b bp lay.val hln b8
  refine ⟨t,ka+kb+3,(sa.trans ab).trans bt,by omega,tp,t8,?_,?_,?_,?_,?_⟩
  · exact (tf.get (by decide) (by simp)).trans brm
  · intro j hj
    have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
    have hj' : j<43 := by simpa [preparedPieces,hcc] using hj
    apply (av j hj).frame (bf.trans tf)
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro h;rcases h with h|h;omega;exact h.elim
    · intro h;rcases h with h|h;omega;exact h.elim
  · intro j hj
    have hj' : j<height lay := by simpa [preparedPieces] using hj
    have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
    apply (aa j hj).frame (bf.trans tf)
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro h;rcases h with h|h;omega;exact h.elim
    · intro h;rcases h with h|h;omega;exact h.elim
  · exact ((ar.trans br).trans tr).mono (by simp)
  · exact ((af.trans bf).trans tf).mono (by
      intro A hA h;rcases h with (h|h)|h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def LowerWrites (lay : Layer) (A : Nat) : Prop :=
  (ENC≤A ∧ A<ENC+40) ∨ (ENC+48≤A ∧ A<ENC+64) ∨
  (EOUT≤A ∧ A<EOUT+32) ∨ (DIGITS≤A ∧ A<DIGITS+64) ∨
  (0x66000≤A ∧ A<0x66020 ∨ A=0x667F8) ∨ (SharedRootControl.sigBase lay.val≤A ∧ A<SharedRootControl.sigBase lay.val+688)

theorem lowerWrites_subset (lay : Layer) (hl : lay≠0) {A : Nat} (h : LowerWrites lay A) : WorkWrites A := by
  have hh := lay.isLt
  have hz : lay.val≠0 := fun h=>hl (Fin.ext h)
  rcases h with h|h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lay.val,by omega,by omega,h⟩)))))

theorem lowerWrites_saved (lay : Layer) (i : Nat) (hi : i<7) : ¬LowerWrites lay (0x66100+8*i) := by
  intro h
  rcases h with h|h|h|h|h|h
  all_goals first | omega | (simp only [ENC,EOUT,DIGITS] at *;omega) | skip
  unfold SharedRootControl.sigBase at h;split_ifs at h <;> omega

theorem csWrites_subset {A : Nat} (h : Canonical.CsW A) : WorkWrites A := by
  unfold Canonical.CsW DigW CanonicalHooks.CreditW at h
  unfold WorkWrites
  simp only [Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG,ENC,EOUT,DIGITS] at *
  omega

theorem csWrites_lower (lay : Layer) {A : Nat} (h : Canonical.CsW A) : LowerWrites lay A := by
  unfold Canonical.CsW DigW CanonicalHooks.CreditW at h
  unfold LowerWrites
  simp only [Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG,ENC,EOUT,DIGITS] at *
  omega

theorem topSetupWrites_subset {A : Nat} (h : A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) : WorkWrites A := by
  unfold WorkWrites;omega

theorem lowerSetupWrites_subset (lay : Layer) {A : Nat}
    (h : A=0x66000 ∨ A=0x66010 ∨ A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) : LowerWrites lay A := by
  unfold LowerWrites;omega

def SavedTop (ds : List Nat) (t : MachineState) : Prop :=
  ∃ s : MachineState,
    (∀ j,j<54 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)) ∧
    (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i)))

theorem SavedTop.frame {ds : List Nat} {s t : MachineState} {W : Nat→Prop}
    (h : SavedTop ds s) (hf : Frame s t W) (hw : ∀ i,i<7 → ¬W (0x66100+8*i)) : SavedTop ds t := by
  obtain ⟨u,hu,hmem⟩ := h
  exact ⟨u,hu,fun i hi=>(hf.get (by omega) (hw i hi)).trans (hmem i hi)⟩

theorem SavedTop.restore {ds : List Nat} {s t : MachineState} (h : SavedTop ds s)
    (hw : ∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) :
    ∀ j,j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0) := by
  obtain ⟨u,hu,hmem⟩ := h
  intro j hj
  exact (words_bytes DIGITS DIGITS 7 (by unfold DIGITS;decide) (by unfold DIGITS;decide)
    (by unfold DIGITS;decide) (by unfold DIGITS;decide) (fun i hi=>(hw i hi).trans (hmem i hi)) j (by omega)).trans (hu j hj)

theorem lower_decode_digits (lay : Layer) (hl : lay≠0) {ds : List Nat}
    (hd : ∃ v,CanonicalPolicy.decode lay v=some ds) : ∀ j,j<43 → ds.getD j 0<8 := by
  obtain ⟨v,hv⟩ := hd
  have he : CanonicalPolicy.normalLayer lay=1 := by simp [CanonicalPolicy.normalLayer,hl]
  change T3.decode (CanonicalPolicy.normalLayer lay) v=some ds at hv
  rw [he] at hv
  intro j hj
  have hb := T3.decode_digit_max hv j (by simpa [T3.chainCount] using hj)
  simpa [T3.maxDigit] using Nat.lt_succ_of_le hb

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure FinishSteps (im : Image) : Prop where
  restore : ∀ s : MachineState,s.pc=pcOf 22460 →
    ∃ t,Steps im s 18 18 t ∧ t.pc=pcOf 22478 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56)
  produce : ∀ s : MachineState,s.pc=pcOf 22478 → ∀ index : Nat,index<2^31 →
    s.getMem (0x20550#64)=BitVec.ofNat 64 index →
    ∃ t,Steps im s 12 12 t ∧ SharedControlTail.TopPost index s t

structure Finished (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=54
  n4 : t.getReg .x27=51
  target : t.getReg .x17=146
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  stable : Stable index p forest t
  digits : ∀ j,j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56)

theorem finish_steps {im : Image} (hc : FinishSteps im) (index : Nat) (hi : index<2^31)
    (p : PreparedRoots) (forest : Digest×Digest) (ds : List Nat) (s : MachineState)
    (hp : s.pc=pcOf 22460) (hstable : Stable index p forest s) (hsaved : SavedTop ds s)
    (hsum : (s.getReg .x25).toNat≤201) :
    ∃ t,Steps im s 30 30 t ∧ Finished index p forest ds s t := by
  obtain ⟨a,sa,ap,acopy,ar,af⟩ := hc.restore s hp
  have haf : Frame s a WorkWrites := af.mono (by intro A hA h;unfold WorkWrites;omega)
  have hsta : Stable index p forest a := hstable.frame haf ar (by decide)
  obtain ⟨t,at',ht⟩ := hc.produce a ap index hi hsta.indexMem
  have hstt : Stable index p forest t := hsta.frame (ht.frame.mono (by simp)) ht.regs (by decide)
  refine ⟨t,sa.trans at',ht.pc,ht.layer,ht.tree,ht.height,ht.chains,ht.n4,ht.target,ht.leaf,ht.selected,hstt,?_,?_,?_⟩
  · intro j hj
    rw [ht.frame.getByte (by unfold DIGITS;omega) (by simp)]
    exact hsaved.restore acopy j hj
  · rw [ht.regs.get (by decide),ar.get (by decide)];exact hsum
  · exact (af.trans ht.frame).mono (by tauto)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure SearchCalls (im : Image) (sk : BitVec 256) : Prop where
  call : ∀ (A : Canonical.CsArgs) (s : MachineState), Canonical.CsPre 543 A s →
    TBSim im sk s (Canonical.csCost A.lay)
      (CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (searchLimit A.lay))
      (Canonical.CsPost im 543 A s)

structure TopSetupSteps (im : Image) : Prop where
  setup : ∀ s : MachineState, s.pc=pcOf 22182 → ∀ index : Nat,index<2^31 →
    s.getMem 0x20550=BitVec.ofNat 64 index → ∀ left right : Digest,
    DigAt s 0x66040 left → DigAt s 0x66050 right →
    ∃ t,Steps im s 26 26 t ∧ SharedTopSetup.Post index left right s t

structure TopReady (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (low : Bool) (ds : List Nat)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22240
  layer : t.getReg .x8=1
  residual : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual 77 0 low ds)
  small : CanonicalPolicy.nextResidual 77 0 low ds<56
  hints : t.getMem (0x66000#64)=0
  c32 : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some ds
  length : ds.length=54
  saved : SavedTop ds t
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t WorkWrites

def SearchError (im : Image) (t : MachineState) : Prop :=
  t.pc=pcOf 545 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)

def TopStagePost (im : Image) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option (BitVec 32×List Nat×Bool)→MachineState→Prop
  | none,t => SearchError im t
  | some (_,ds,low),t => TopReady index p forest low ds s t

theorem top_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : TopSetupSteps im) (htailSteps : TopTailSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost 0+57)
      (CanonicalPolicy.layerCounterSearchAt 0 22 (route index 0).2 (route index 0).1
        (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im index p forest s) := by
  obtain ⟨a,sa,ha⟩ := ht.setup s hp index hi hstable.indexMem _ _ hstable.one.left hstable.one.right
  have haf : Frame s a WorkWrites := ha.frame.mono (fun _ _=>topSetupWrites_subset)
  have hsta : Stable index p forest a := hstable.frame haf ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold ENC;omega) (by unfold ENC;omega)).trans hcv⟩
  have H := hs.call (topArgs index (topPair 1 p.one.levels)) a (top_pre index hi _ s a ha hsta.tables hac)
  have Htail : TBSim im sk a (Canonical.csCost 0+31)
      (CanonicalPolicy.layerCounterSearchAt 0 22 (route index 0).2 (route index 0).1
        (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0))
      (TopStagePost im index p forest s) := by
    have hb := TBSim.bind H (f:=fun r=>pure r) (W₂:=31) (Q₂:=TopStagePost im index p forest s) (by
      intro r u hu
      cases r with
      | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=TopStagePost im index p forest s) hu).mono (by omega) (fun _ _ h=>h)
      | some pair =>
        obtain ⟨c,ds,low⟩ := pair
        rcases hu with ⟨up,hc,uc19,uc32,hdec,hlen,hdigs,ur,uf,usum,ucredit,hfloor⟩
        have huf : Frame a u WorkWrites := uf.mono (fun _ _=>csWrites_subset)
        have hstu : Stable index p forest u := hsta.frame huf ur (by decide)
        obtain ⟨t,k,ut,hk,htail⟩ := top_tail htailSteps u up low ds ucredit
        have htf : Frame u t WorkWrites := htail.frame.mono (fun _ _=>topTail_subset)
        have hstt : Stable index p forest t := hstu.frame htf htail.regs (by decide)
        refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
        refine ⟨htail.pc,htail.layer,htail.residual,top_residual_small hfloor,?_,?_,hstt,hdec,hlen,⟨u,hdigs,htail.saved⟩,?_,?_⟩
        · exact (htail.frame.get (by decide) (by unfold TopTailWrites;omega)).trans
            ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans
              ((ha.frame.get (by decide) (by unfold ENC;omega)).trans hh))
        · exact ⟨c.toNat,by omega,
            (htail.frame.get (by unfold ENC;omega) (by unfold TopTailWrites ENC;omega)).trans uc32⟩
        · rw [htail.regs.get (by decide)]
          change (u.getReg .x25).toNat≤201
          change (u.getReg .x25).toNat≤146 at usum
          omega
        · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
    simpa only [bind_pure,topArgs,lowerArgs] using hb
  exact (TBSim.steps sa Htail).mono (by omega) (fun _ _ h=>h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def stageBound (lay : Layer) : Nat := if lay.val=1 then 56 else if lay.val=2 then 41 else 22

def preparedAt (p : PreparedRoots) (lay : Layer) : PreparedLower :=
  if lay.val=1 then p.one else if lay.val=2 then p.two else p.three

def messageAt (p : PreparedRoots) (forest : Digest×Digest) (lay : Layer) : Digest×Digest :=
  if lay.val=1 then topPair 2 p.two.levels else if lay.val=2 then topPair 3 p.three.levels else forest

theorem Stable.prepared {index : Nat} {p : PreparedRoots} {forest : Digest×Digest} {s : MachineState}
    (h : Stable index p forest s) (lay : Layer) (hl : lay≠0) :
    SharedRootControl.Stored lay index (preparedAt p lay) s := by
  fin_cases lay <;> first | exact (hl rfl).elim | exact h.one | exact h.two | exact h.three

theorem Stable.message {index : Nat} {p : PreparedRoots} {forest : Digest×Digest} {s : MachineState}
    (h : Stable index p forest s) (lay : Layer) (hl : lay≠0) :
    DigAt s (0x66040+32*lay.val) (messageAt p forest lay).1 ∧
    DigAt s (0x66050+32*lay.val) (messageAt p forest lay).2 := by
  fin_cases lay
  · exact (hl rfl).elim
  · exact ⟨h.two.left,h.two.right⟩
  · exact ⟨h.three.left,h.three.right⟩
  · exact ⟨h.forestL,h.forestR⟩

theorem floor_small (lay : Layer) (hl : lay≠0) (r : Nat) (hr : r<stageBound lay) :
    CanonicalPolicy.threshold lay.val r<22 ∧ (lay.val=1 → CanonicalPolicy.threshold lay.val r<16) := by
  fin_cases lay
  · exact (hl rfl).elim
  · change CanonicalPolicy.threshold 1 r<22 ∧ (1=1 → CanonicalPolicy.threshold 1 r<16)
    have : CanonicalPolicy.threshold 1 r<16 := CanonicalPolicy.lower_one_floor_lt ⟨r,hr⟩
    exact ⟨by omega, fun _ => this⟩
  · change CanonicalPolicy.threshold 2 r<22 ∧ (2=1 → _)
    have : CanonicalPolicy.threshold 2 r≤19 := (CanonicalPolicy.lower_two_progress ⟨r,hr⟩).1
    exact ⟨by omega, fun h => absurd h (by decide)⟩
  · change CanonicalPolicy.threshold 3 r<22 ∧ (3=1 → _)
    rw [CanonicalPolicy.lower_three_progress r hr];exact ⟨hr, fun h => absurd h (by decide)⟩

theorem next_stage_bound (lay : Layer) (hl : lay≠0) (r : Nat) (hr : r<stageBound lay)
    (low : Bool) (ds : List Nat) (hd : CanonicalPolicy.threshold lay.val r≤CanonicalPolicy.credit lay low ds) :
    (∀ hnext : lay.val<3, CanonicalPolicy.nextResidual r lay low ds<stageBound ⟨lay.val+1,by omega⟩) ∧
    (lay.val=3 → CanonicalPolicy.nextResidual r lay low ds=0) := by
  fin_cases lay
  · exact (hl rfl).elim
  · change CanonicalPolicy.threshold 1 r≤CanonicalPolicy.credit 1 low ds at hd
    change (∀ hnext : 1<3, r-CanonicalPolicy.credit 1 low ds<41) ∧ (1=3 → r-CanonicalPolicy.credit 1 low ds=0)
    have h : r-CanonicalPolicy.threshold 1 r<41 := (CanonicalPolicy.lower_one_progress ⟨r,hr⟩).2
    constructor <;> intro hnext <;> omega
  · change CanonicalPolicy.threshold 2 r≤CanonicalPolicy.credit 2 low ds at hd
    change (∀ hnext : 2<3, r-CanonicalPolicy.credit 2 low ds<22) ∧ (2=3 → r-CanonicalPolicy.credit 2 low ds=0)
    have h : r-CanonicalPolicy.threshold 2 r<22 := (CanonicalPolicy.lower_two_progress ⟨r,hr⟩).2
    constructor <;> intro hnext <;> omega
  · change CanonicalPolicy.threshold 3 r≤CanonicalPolicy.credit 3 low ds at hd
    rw [CanonicalPolicy.lower_three_progress r hr] at hd
    change (∀ hnext : 3<3, _) ∧ (3=3 → r-CanonicalPolicy.credit 3 low ds=0)
    constructor
    · intro hh;omega
    · intro _;exact Nat.sub_eq_zero_of_le hd

structure LowerSetupSteps (im : Image) : Prop where
  setup : ∀ s : MachineState,s.pc=pcOf 22240 → ∀ lay index residual hints : Nat,
    (1≤lay ∧ lay≤3) → index<2^31 → (residual<(if lay=1 then 56 else if lay=2 then 41 else 22)) →
    s.getReg .x8=BitVec.ofNat 64 lay → s.getMem (0x20550#64)=BitVec.ofNat 64 index →
    s.getMem (0x66008#64)=BitVec.ofNat 64 residual → s.getMem (0x66000#64)=BitVec.ofNat 64 hints →
    ∃ t k c,Steps im s k c t ∧ c≤120 ∧ SharedLowerSetup.CallPost lay index residual hints s t

structure LowerReady (lay : Layer) (index residual hints : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (low : Bool) (ds : List Nat) (s t : MachineState) : Prop where
  pc : t.pc=if lay.val<3 then pcOf 22240 else pcOf 22460
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  residualMem : t.getMem (0x66008#64)=BitVec.ofNat 64 (CanonicalPolicy.nextResidual residual lay low ds)
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 (hints+SharedHints.hintWeight lay.val*CanonicalPolicy.threshold lay.val residual)
  c32 : ∃ c<2^32,t.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  stable : Stable index p forest t
  values : DigsAt t (SharedRootControl.sigBase lay.val) (preparedPieces lay (route index lay).1 (preparedAt p lay) ds).1
  path : DigsAt t (SharedRootControl.sigBase lay.val+688) (preparedPieces lay (route index lay).1 (preparedAt p lay) ds).2
  floor : CanonicalPolicy.threshold lay.val residual≤CanonicalPolicy.credit lay low ds
  sum : (t.getReg .x25).toNat≤201
  frame : Frame s t (LowerWrites lay)

def LowerStagePost (im : Image) (lay : Layer) (index residual hints : Nat) (p : PreparedRoots)
    (forest : Digest×Digest) (s : MachineState) : Option (BitVec 32×List Nat×Bool)→MachineState→Prop
  | none,t => SearchError im t
  | some (_,ds,low),t => LowerReady lay index residual hints p forest low ds s t

theorem lower_stage {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (ht : LowerSetupSteps im) (htail : LowerTailSteps im)
    (lay : Layer) (hl : lay≠0) (index residual hints : Nat) (hi : index<2^31) (hr : residual<stageBound lay)
    (p : PreparedRoots) (forest : Digest×Digest) (s : MachineState) (hp : s.pc=pcOf 22240)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hstable : Stable index p forest s)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 residual) (hhm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (Canonical.csCost lay+707)
      (CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val residual)
        (route index lay).2 (route index lay).1 (.pair (messageAt p forest lay).1 (messageAt p forest lay).2) 0 (searchLimit lay))
      (LowerStagePost im lay index residual hints p forest s) := by
  have hln : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt;have : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  obtain ⟨a,ka,ca,sa,hca,ha⟩ := ht.setup s hp lay.val index residual hints hln hi hr h8 hstable.indexMem hrm hhm
  have haf : Frame s a (LowerWrites lay) := ha.frame.mono (fun _ _=>lowerSetupWrites_subset lay)
  have hsta : Stable index p forest a := hstable.frame (haf.mono (fun _ _=>lowerWrites_subset lay hl)) ha.regs (by decide)
  have hac : ∃ c<2^32,a.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c := by
    obtain ⟨c,hc,hcv⟩ := hc32
    exact ⟨c,hc,(ha.frame.get (by unfold ENC;omega) (by unfold ENC;omega)).trans hcv⟩
  obtain ⟨hp0,hp1⟩ := hstable.message lay hl
  have H := hs.call (lowerArgs lay index (CanonicalPolicy.threshold lay.val residual) (messageAt p forest lay)) a
    (lower_pre lay hl index residual hints hi _ s a ha hsta.tables hac hp0 hp1 (floor_small lay hl residual hr).1)
  have HB := TBSim.bind H (f:=fun r=>pure r) (W₂:=587) (Q₂:=LowerStagePost im lay index residual hints p forest s) (by
    intro r u hu
    cases r with
    | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=LowerStagePost im lay index residual hints p forest s) hu).mono (by omega) (fun _ _ h=>h)
    | some pair =>
      obtain ⟨c,ds,low⟩ := pair
      rcases hu with ⟨up,hc,uc19,uc32,hdec,hlen,hdigs,ur,uf,usum,ucredit,hfloor⟩
      have huf : Frame a u (LowerWrites lay) := uf.mono (fun _ _=>csWrites_lower lay)
      have hstu : Stable index p forest u := hsta.frame (huf.mono (fun _ _=>lowerWrites_subset lay hl)) ur (by decide)
      have hsp := hstu.prepared lay hl
      have uh8 : u.getReg .x8=BitVec.ofNat 64 lay.val := (ur.get (by decide)).trans ha.layer
      have uhrm : u.getMem (0x66008#64)=BitVec.ofNat 64 residual :=
        (uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans
          ((ha.frame.get (by decide) (by unfold ENC;omega)).trans hrm)
      have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
      obtain ⟨t,k,ut,hk,ht⟩ := lower_tail htail lay hl (route index lay).1 residual (preparedAt p lay) low ds
        (lower_decode_digits lay hl hdec) u up uh8 (by simpa only [lowerArgs,hcc,Search.DIGITS,DIGITS] using hdigs)
        (fun j hj d hd=>hsp.saved j hj d (by omega)) hsp.path (by unfold stageBound at hr;split_ifs at hr <;> omega) uhrm ucredit
      have htf : Frame u t (LowerWrites lay) := ht.frame.mono (by intro A hA h;unfold LowerWrites;rcases h with h|rfl;tauto;omega)
      have hstt : Stable index p forest t := hstu.frame (htf.mono (fun _ _=>lowerWrites_subset lay hl)) ht.regs (by decide)
      refine (TBSim.steps ut (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
      refine ⟨ht.pc,ht.layer,ht.residual,?_,?_,hstt,ht.values,ht.path,hfloor,?_,?_⟩
      · exact (ht.frame.get (by decide) (by unfold LowerTailWrites SharedRootControl.sigBase;split_ifs <;> omega)).trans
          ((uf.get (by decide) (by simp only [Canonical.CsW,CanonicalHooks.CreditW,DigW,Search.ENC,Search.EOUT,Search.DIGITS,Search.FLAG];omega)).trans ha.hints)
      · exact ⟨c.toNat,by omega,(ht.frame.get (by unfold ENC;omega)
          (by unfold LowerTailWrites SharedRootControl.sigBase ENC;split_ifs <;> omega)).trans uc32⟩
      · rw [ht.regs.get (by decide)]
        simpa [lowerArgs,CanonicalPolicy.normalLayer,hl,T3.target] using usum
      · exact ((haf.trans huf).trans htf).mono (fun _ _ h=>by rcases h with (h|h)|h <;> exact h))
  have HC := TBSim.steps sa HB
  simpa only [bind_pure,topArgs,lowerArgs] using HC.mono (by change ca+(Canonical.csCost lay+587)≤Canonical.csCost lay+707;omega) (fun _ _ h=>h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def PiecesStored (lay : Layer) (pieces : T3.Pieces) (s : MachineState) : Prop :=
  DigsAt s (SharedRootControl.sigBase lay.val) pieces.1 ∧
  DigsAt s (SharedRootControl.sigBase lay.val+688) pieces.2

theorem lowerWrites_other_values (old current : Layer) (ho : old≠0) (hc : current≠0)
    (hne : old≠current) (j half : Nat) (hj : j<43) (hh : half<2) :
    ¬LowerWrites current (SharedRootControl.sigBase old.val+16*j+8*half) := by
  intro h
  rcases h with h|h|h|h|h|h
  all_goals fin_cases old <;> fin_cases current <;>
    simp_all [SharedRootControl.sigBase,ENC,EOUT,DIGITS] <;> omega

theorem PiecesStored.frame_lower {s t : MachineState} {old current : Layer} {pieces : T3.Pieces}
    (ho : old≠0) (hc : current≠0) (hne : old≠current)
    (hlen : pieces.1.length=43) (hpath : pieces.2.length=height old)
    (h : PiecesStored old pieces s) (hf : Frame s t (LowerWrites current)) : PiecesStored old pieces t := by
  constructor
  · intro j hj
    have hj' : j<43 := by simpa only [hlen] using hj
    apply (h.1 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · simpa using lowerWrites_other_values old current ho hc hne j 0 hj' (by decide)
    · simpa using lowerWrites_other_values old current ho hc hne j 1 hj' (by decide)
  · intro j hj
    have hj' : j<height old := by simpa only [hpath] using hj
    have hheight : height old≤12 := by fin_cases old <;> decide
    apply (h.2 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw
      exact work_not_path old ho j 0 hj' (by decide) (by simpa using lowerWrites_subset current hc hw)
    · intro hw
      exact work_not_path old ho j 1 hj' (by decide) (by simpa using lowerWrites_subset current hc hw)

theorem PiecesStored.frame_finish {s t : MachineState} {lay : Layer} {pieces : T3.Pieces}
    (hl : lay≠0) (hlen : pieces.1.length=43) (hpath : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) (hf : Frame s t (fun A=>DIGITS≤A ∧ A<DIGITS+56)) : PiecesStored lay pieces t := by
  have hsbase : SharedRootControl.sigBase lay.val+1024<DIGITS := by
    unfold SharedRootControl.sigBase DIGITS;split_ifs <;> omega
  have hheight : height lay≤7 := by fin_cases lay <;> simp_all [height]
  constructor
  · intro j hj
    have hj' : j<43 := by simpa only [hlen] using hj
    apply (h.1 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw;omega
    · intro hw;omega
  · intro j hj
    have hj' : j<height lay := by simpa only [hpath] using hj
    apply (h.2 j hj).frame hf
    · unfold SharedRootControl.sigBase;split_ifs <;> omega
    · intro hw;omega
    · intro hw;omega

theorem prepared_length (lay : Layer) (hl : lay≠0) (leaf : Nat) (p : PreparedLower) (ds : List Nat) :
    (preparedPieces lay leaf p ds).1.length=43 ∧ (preparedPieces lay leaf p ds).2.length=height lay := by
  have hcc : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
  simp [preparedPieces,hcc]

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000

theorem work_not_base {A : Nat} (hb : BaseA A) : ¬WorkWrites A := by
  intro hw
  rcases hw with hw|hw|hw|hw|hw|hw|⟨lay,hlo,hhi,ha,hb'⟩
  all_goals unfold BaseA NeverW at hb
  all_goals simp only [PRIV,REGION,FLEAF,Keygen.NODE,CHAIN,ZDIG,ENC,EOUT,DIGITS,NBUF,TOP_DATA] at *
  all_goals first | omega | skip
  all_goals unfold SharedRootControl.sigBase at *
  all_goals split_ifs at * <;> omega

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000

theorem stateBase_frame {sk : SecretKey} {cache : Bytes 131072} {s t : MachineState}
    (h : SharedTopPath.StateBase sk cache s) (hf : Frame s t WorkWrites)
    (hx5 : t.getReg .x5=0) : SharedTopPath.StateBase sk cache t := by
  have g : ∀ A,A<2^64→BaseA A→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hb => hf.get hA (work_not_base hb)
  refine ⟨hx5,?_,?_,?_,?_,?_,?_,fun k hk=>?_,fun A hA hn h32 h40=>?_⟩
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p0
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p8
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p32
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p40
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p48
  · exact (g _ (by decide) (by unfold BaseA;simp)).trans h.p56
  · exact (g _ (by unfold REGION;omega) (by unfold BaseA;right;right;right;right;right;right;left;omega)).trans (h.region k hk)
  · exact (g _ hA (by unfold BaseA;right;right;right;right;right;right;right;left;exact hn)).trans (h.zero A hA hn h32 h40)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

structure Choices where
  c0 : BitVec 32
  c1 : BitVec 32
  c2 : BitVec 32
  c3 : BitVec 32
  d0 : List Nat
  d1 : List Nat
  d2 : List Nat
  d3 : List Nat
  l0 : Bool
  l1 : Bool
  l2 : Bool
  l3 : Bool

def Choices.r1 (a : Choices) := CanonicalPolicy.nextResidual 77 0 a.l0 a.d0
def Choices.r2 (a : Choices) := CanonicalPolicy.nextResidual a.r1 1 a.l1 a.d1
def Choices.r3 (a : Choices) := CanonicalPolicy.nextResidual a.r2 2 a.l2 a.d2
def Choices.hints (a : Choices) := 484*CanonicalPolicy.threshold 1 a.r1 +
  22*CanonicalPolicy.threshold 2 a.r2 + CanonicalPolicy.threshold 3 a.r3

def prefixSearch (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) : T3.M (Option Choices) := do
  let some (c0,d0,l0) ← CanonicalPolicy.layerCounterSearchAt 0 22 (route index 0).2 (route index 0).1
    (.pair (topPair 1 p.one.levels).1 (topPair 1 p.one.levels).2) 0 (searchLimit 0) | pure none
  let r1 := CanonicalPolicy.nextResidual 77 0 l0 d0
  let f1 := CanonicalPolicy.threshold 1 r1
  if f1≥16 then return none
  let some (c1,d1,l1) ← CanonicalPolicy.layerCounterSearchAt 1 f1 (route index 1).2 (route index 1).1
    (.pair (topPair 2 p.two.levels).1 (topPair 2 p.two.levels).2) 0 (searchLimit 1) | pure none
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  let f2 := CanonicalPolicy.threshold 2 r2
  if f2≥22 then return none
  let some (c2,d2,l2) ← CanonicalPolicy.layerCounterSearchAt 2 f2 (route index 2).2 (route index 2).1
    (.pair (topPair 3 p.three.levels).1 (topPair 3 p.three.levels).2) 0 (searchLimit 2) | pure none
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  let f3 := CanonicalPolicy.threshold 3 r3
  if f3≥22 then return none
  let some (c3,d3,l3) ← CanonicalPolicy.layerCounterSearchAt 3 f3 (route index 3).2 (route index 3).1
    (.pair forest.1 forest.2) 0 (searchLimit 3) | pure none
  pure (some ⟨c0,c1,c2,c3,d0,d1,d2,d3,l0,l1,l2,l3⟩)

structure PrefixReady (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) (a : Choices)
    (s t : MachineState) : Prop where
  pc : t.pc=pcOf 441
  layer : t.getReg .x8=0
  tree : t.getReg .x9=0
  height : t.getReg .x15=12
  chains : t.getReg .x26=54
  n4 : t.getReg .x27=51
  target : t.getReg .x17=146
  leaf : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  selected : t.getReg .x14=t.getReg .x18
  stable : Stable index p forest t
  decoded : ∃ v,CanonicalPolicy.decode 0 v=some a.d0
  digits : ∀ j,j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (a.d0.getD j 0)
  sum : (t.getReg .x25).toNat≤201
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 a.hints
  residual : t.getMem (0x66008#64)=0
  credit : CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3=0
  frame : Frame s t WorkWrites

def PrefixPost (im : Image) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) : Option Choices→MachineState→Prop
  | none,t => SearchError im t
  | some a,t => PrefixReady index p forest a s t

def prefixCost : Nat := Canonical.csCost 0+57+((Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)))

theorem prefix_good {im : Image} {sk : BitVec 256} (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s prefixCost (prefixSearch index p forest) (PrefixPost im index p forest s) := by
  unfold prefixSearch
  have H0 := top_stage hs htop htail index hi p forest s hp hstable hh hc32
  refine (TBSim.bind H0 (W₂:=(Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30))) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=prefixCost) (by unfold prefixCost;omega) (fun _ _ h=>h)
  intro r0 t0 h0
  cases r0 with
  | none => exact (TBSim.pure (a:=none) (s:=t0) (Q:=PrefixPost im index p forest s) h0).mono (by omega) (fun _ _ h=>h)
  | some a0 =>
    obtain ⟨c0,d0,l0⟩ := a0
    change TopReady index p forest l0 d0 s t0 at h0
    let r1 := CanonicalPolicy.nextResidual 77 0 l0 d0
    let f1 := CanonicalPolicy.threshold 1 r1
    have hf1 : f1<16 := (floor_small 1 (by decide) r1 h0.small).2 rfl
    dsimp only [f1,r1] at hf1
    simp only [if_neg (Nat.not_le.mpr hf1)]
    have H1 := lower_stage hs hlower hltail 1 (by decide) index r1 0 hi h0.small p forest t0
      h0.pc h0.layer h0.stable h0.residual h0.hints h0.c32
    refine (TBSim.bind H1 (W₂:=(Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 1+707)+((Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30))) (by omega) (fun _ _ h=>h)
    intro r1out t1 h1
    cases r1out with
    | none => exact (TBSim.pure (a:=none) (s:=t1) (Q:=PrefixPost im index p forest s) h1).mono (by omega) (fun _ _ h=>h)
    | some a1 =>
      obtain ⟨c1,d1,l1⟩ := a1
      change LowerReady 1 index r1 0 p forest l1 d1 t0 t1 at h1
      let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
      let f2 := CanonicalPolicy.threshold 2 r2
      have hr2 : r2<41 := (next_stage_bound 1 (by decide) r1 h0.small l1 d1 h1.floor).1 (by decide)
      have hf2 : f2<22 := (floor_small 2 (by decide) r2 hr2).1
      have hints1 : t1.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1) := by simpa [SharedHints.hintWeight] using h1.hints
      have saved1 : SavedTop d0 t1 := h0.saved.frame h1.frame (lowerWrites_saved 1)
      dsimp only [f2,r2,r1] at hf2
      simp only [if_neg (Nat.not_le.mpr hf2)]
      have H2 := lower_stage hs hlower hltail 2 (by decide) index r2 (484*f1) hi hr2 p forest t1
        h1.pc h1.layer h1.stable h1.residualMem hints1 h1.c32
      refine (TBSim.bind H2 (W₂:=(Canonical.csCost 3+707)+30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 2+707)+((Canonical.csCost 3+707)+30)) (by omega) (fun _ _ h=>h)
      intro r2out t2 h2
      cases r2out with
      | none => exact (TBSim.pure (a:=none) (s:=t2) (Q:=PrefixPost im index p forest s) h2).mono (by omega) (fun _ _ h=>h)
      | some a2 =>
        obtain ⟨c2,d2,l2⟩ := a2
        change LowerReady 2 index r2 (484*f1) p forest l2 d2 t1 t2 at h2
        let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
        let f3 := CanonicalPolicy.threshold 3 r3
        have hr3 : r3<22 := (next_stage_bound 2 (by decide) r2 hr2 l2 d2 h2.floor).1 (by decide)
        have hf3 : f3<22 := (floor_small 3 (by decide) r3 hr3).1
        have hints2 : t2.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1+22*f2) := by simpa [SharedHints.hintWeight] using h2.hints
        have saved2 : SavedTop d0 t2 := saved1.frame h2.frame (lowerWrites_saved 2)
        have one1 : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one d1) t1 := ⟨h1.values,h1.path⟩
        have one2 := one1.frame_lower (current:=2) (by decide) (by decide) (by decide)
          (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 h2.frame
        dsimp only [f3,r3,r2,r1] at hf3
        simp only [if_neg (Nat.not_le.mpr hf3)]
        have H3 := lower_stage hs hlower hltail 3 (by decide) index r3 (484*f1+22*f2) hi hr3 p forest t2
          h2.pc h2.layer h2.stable h2.residualMem hints2 h2.c32
        refine (TBSim.bind H3 (W₂:=30) (Q₂:=PrefixPost im index p forest s) ?_).mono (W':=(Canonical.csCost 3+707)+30) (by omega) (fun _ _ h=>h)
        intro r3out t3 h3
        cases r3out with
        | none => exact (TBSim.pure (a:=none) (s:=t3) (Q:=PrefixPost im index p forest s) h3).mono (by omega) (fun _ _ h=>h)
        | some a3 =>
          obtain ⟨c3,d3,l3⟩ := a3
          change LowerReady 3 index r3 (484*f1+22*f2) p forest l3 d3 t2 t3 at h3
          have hz : CanonicalPolicy.nextResidual r3 3 l3 d3=0 :=
            (next_stage_bound 3 (by decide) r3 hr3 l3 d3 h3.floor).2 rfl
          have saved3 : SavedTop d0 t3 := saved2.frame h3.frame (lowerWrites_saved 3)
          have one3 := one2.frame_lower (current:=3) (by decide) (by decide) (by decide)
            (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 h3.frame
          have two2 : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two d2) t2 := ⟨h2.values,h2.path⟩
          have two3 := two2.frame_lower (current:=3) (by decide) (by decide) (by decide)
            (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 h3.frame
          have three3 : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three d3) t3 := ⟨h3.values,h3.path⟩
          obtain ⟨t,st,ht⟩ := finish_steps hfinish index hi p forest d0 t3 h3.pc h3.stable saved3 h3.sum
          refine (TBSim.steps st (TBSim.pure (s:=t) (a:=some ⟨c0,c1,c2,c3,d0,d1,d2,d3,l0,l1,l2,l3⟩) (Q:=PrefixPost im index p forest s) ?_)).mono (W':=30) (by omega) (fun _ _ h=>h)
          refine ⟨ht.pc,ht.layer,ht.tree,ht.height,ht.chains,ht.n4,ht.target,ht.leaf,ht.selected,ht.stable,
            h0.decoded,ht.digits,ht.sum,?_,?_,?_,?_,?_,hz,?_⟩
          · exact one3.frame_finish (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 ht.frame
          · exact two3.frame_finish (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 ht.frame
          · exact three3.frame_finish (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 ht.frame
          · have hm := (ht.frame.get (A:=0x66000) (by decide) (by unfold DIGITS;omega)).trans h3.hints
            change t.getMem (0x66000#64)=BitVec.ofNat 64 (484*f1+22*f2+f3)
            simpa [SharedHints.hintWeight] using hm
          · have hm := (ht.frame.get (A:=0x66008) (by decide) (by unfold DIGITS;omega)).trans h3.residualMem
            change t.getMem (0x66008#64)=BitVec.ofNat 64 0
            simpa only [hz] using hm
          · have F1 := h1.frame.mono (fun _ _=>lowerWrites_subset 1 (by decide))
            have F2 := h2.frame.mono (fun _ _=>lowerWrites_subset 2 (by decide))
            have F3 := h3.frame.mono (fun _ _=>lowerWrites_subset 3 (by decide))
            have F4 : Frame t3 t WorkWrites := ht.frame.mono (by intro A hA h;unfold WorkWrites;omega)
            exact ((((h0.frame.trans F1).trans F2).trans F3).trans F4).mono (by
              intro A hA h;rcases h with (((h|h)|h)|h)|h <;> exact h)

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open OracleComp
set_option maxHeartbeats 500000
set_option maxRecDepth 32768

def finishSource (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots)
    (a : Choices) : M (Option CanonicalLayers) := do
  let top ← signTop cache (route index 0).1 a.d0
  pure (some ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3,
    BitVec.ofNat 16 a.hints⟩)

theorem searchPreparedLayers_prefix (cache : SigGolfCandidate.T3.Cache) (index : Nat) (p : PreparedRoots) (forest : Digest×Digest) :
    searchPreparedLayers cache index p forest =
      prefixSearch index p forest >>= fun
        | none => pure none
        | some a => finishSource cache index p a := by
  unfold searchPreparedLayers prefixSearch
  simp only [CanonicalPolicy.totalCredit,CanonicalPolicy.threshold_top]
  simp only [bind_assoc]
  congr 1
  funext o0
  cases o0 with
  | none => simp only [pure_bind]
  | some o0 =>
    obtain ⟨c0,d0,l0⟩ := o0
    dsimp only
    split
    · simp_all only [pure_bind, ite_true, ite_false]
    · simp_all only [bind_assoc, ite_true, ite_false]
      congr 1
      funext o1
      cases o1 with
      | none => simp only [pure_bind]
      | some o1 =>
        obtain ⟨c1,d1,l1⟩ := o1
        dsimp only
        split
        · simp_all only [pure_bind, ite_true, ite_false]
        · simp_all only [bind_assoc, ite_true, ite_false]
          congr 1
          funext o2
          cases o2 with
          | none => simp only [pure_bind]
          | some o2 =>
            obtain ⟨c2,d2,l2⟩ := o2
            dsimp only
            split
            · simp_all only [pure_bind, ite_true, ite_false]
            · simp_all only [bind_assoc, ite_true, ite_false]
              congr 1
              funext o3
              cases o3 with
              | none => simp only [pure_bind]
              | some o3 =>
                obtain ⟨c3,d3,l3⟩ := o3
                simp only [pure_bind,finishSource,Choices.r1,Choices.r2,Choices.r3,Choices.hints]

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open Packed.Boundary
open Packed (L0W)
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def TopFinishPost (s : MachineState) (top : T3.Pieces) (t : MachineState) : Prop :=
  t.pc=pcOf 540 ∧ (∀ i<54,DigAt t (SIG+2192+16*i) (top.1.getD i 0)) ∧
    (∀ j<12,DigAt t (SIG+3056+16*j) (top.2.getD j 0)) ∧ Frame s t L0W ∧
    t.getMem (0x66000#64)=s.getMem (0x66000#64) ∧
    t.getMem (0x66008#64)=s.getMem (0x66008#64)

structure TopCalls (im : Image) (sk : SecretKey) (cache : Bytes 131072) : Prop where
  call : ∀ (leaf : Nat),leaf<4096 → ∀ (ds : List Nat) (u : MachineState),u.pc=pcOf 441 →
    SharedTopPath.StateBase sk cache u → TopRegs leaf u →
    u.getReg .x18=BitVec.ofNat 64 leaf → (u.getReg .x25).toNat≤201 →
    (∀ i<54,ds.getD i 0≤T3.maxDigit 0 i) →
    (∀ i<54,u.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 (ds.getD i 0)) →
    TBSim im sk u 335006 (T3.signTop (cacheDec cache) leaf ds) (TopFinishPost u)

theorem PiecesStored.frame_top {s t : MachineState} {lay : Layer} {pieces : T3.Pieces}
    (hl : lay≠0) (hlen : pieces.1.length=43) (hpath : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) (hf : Frame s t L0W) : PiecesStored lay pieces t := by
  constructor
  · intro i hi
    have hi' : i<43 := by simpa only [hlen] using hi
    apply (h.1 i hi).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG] <;> omega
  · intro j hj
    have hj' : j<height lay := by simpa only [hpath] using hj
    apply (h.2 j hj).frame hf
    · fin_cases lay <;> simp_all [SharedRootControl.sigBase,height] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG,height] <;> omega
    · intro hw
      fin_cases lay <;> simp_all [SharedRootControl.sigBase,L0W,SIG,height] <;> omega

def layersValue (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces) : CanonicalLayers :=
  ⟨[top,preparedPieces 1 (route index 1).1 p.one a.d1,
      preparedPieces 2 (route index 2).1 p.two a.d2,preparedPieces 3 (route index 3).1 p.three a.d3],
    [a.c0,a.c1,a.c2,a.c3],[a.d0,a.d1,a.d2,a.d3],[a.l0,a.l1,a.l2,a.l3],CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3,
    BitVec.ofNat 16 a.hints⟩

structure Completed (index : Nat) (p : PreparedRoots) (a : Choices) (top : T3.Pieces)
    (t : MachineState) : Prop where
  pc : t.pc=pcOf 540
  topValues : ∀ i<54,DigAt t (SIG+2192+16*i) (top.1.getD i 0)
  topPath : ∀ j<12,DigAt t (SIG+3056+16*j) (top.2.getD j 0)
  one : PiecesStored 1 (preparedPieces 1 (route index 1).1 p.one a.d1) t
  two : PiecesStored 2 (preparedPieces 2 (route index 2).1 p.two a.d2) t
  three : PiecesStored 3 (preparedPieces 3 (route index 3).1 p.three a.d3) t
  hints : t.getMem (0x66000#64)=BitVec.ofNat 64 a.hints
  residual : t.getMem (0x66008#64)=0
  credit : CanonicalPolicy.nextResidual a.r3 3 a.l3 a.d3=0

def LayersPost (im : Image) (index : Nat) (p : PreparedRoots) : Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => ∃ a top,layers=layersValue index p a top ∧ Completed index p a top t

theorem searchPreparedLayers_good {im : Image} {sk : SecretKey} {cache : Bytes 131072}
    (hc : TopCalls im sk cache) (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (LayersPost im index p) := by
  rw [searchPreparedLayers_prefix]
  refine TBSim.bind (prefix_good hs htop htail hlower hltail hfinish index hi p forest s hp hstable hh hc32)
    (W₂:=335006) (Q₂:=LayersPost im index p) ?_
  intro a u hu
  cases a with
  | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=LayersPost im index p) hu).mono (by omega) (fun _ _ h=>h)
  | some a =>
    change PrefixReady index p forest a s u at hu
    have hb := stateBase_frame hbase hu.frame hu.stable.tables.x5
    have hleaf : index/2^19<4096 := by omega
    have hregs : TopRegs (index/2^19) u :=
      ⟨hu.layer,hu.tree,hu.selected.trans hu.leaf,hu.chains,hu.n4⟩
    have hd7 : ∀ i<54,a.d0.getD i 0≤T3.maxDigit 0 i := by
      obtain ⟨v,hv⟩ := hu.decoded
      change T3.decode 0 v=some a.d0 at hv
      intro i hi
      exact T3.decode_digit_max hv i hi
    have H := hc.call (index/2^19) hleaf a.d0 u hu.pc hb hregs hu.leaf hu.sum hd7 hu.digits
    unfold finishSource
    have hr : (route index 0).1=index/2^19 := by
      change index/2^19%2^12=index/2^19
      exact Nat.mod_eq_of_lt hleaf
    rw [hr]
    refine (TBSim.bind H (W₂:=0) (Q₂:=LayersPost im index p) ?_).mono (by omega) (fun _ _ h=>h)
    intro top t ht
    rcases ht with ⟨htpc,htv,htp,htf,hth,htr⟩
    refine TBSim.pure (a:=some (layersValue index p a top)) (s:=t) (Q:=LayersPost im index p) ?_
    refine ⟨a,top,rfl,htpc,htv,htp,?_,?_,?_,hth.trans hu.hints,htr.trans hu.residual,hu.credit⟩
    · exact hu.one.frame_top (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 htf
    · exact hu.two.frame_top (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 htf
    · exact hu.three.frame_top (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 htf

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem installed_searchCalls (sk : BitVec 256) : SearchCalls Images.signImage sk :=
  ⟨fun _ _ hp => Canonical.counterSearch_good SharedSearchCode.installed_searchKernel hp⟩

theorem installed_topSetup : TopSetupSteps Images.signImage :=
  ⟨SharedTopSetup.steps SharedTopSetup.installed_code⟩

theorem installed_topTail : TopTailSteps Images.signImage :=
  ⟨SharedTopDigits.save_steps SharedTopDigits.installed_save,
   SharedControlTail.initResidual_steps SharedControlTail.installed_initResidual,
   SharedResidual.residual22230_steps SharedResidual.installed22230,
   SharedControlTail.firstLayer_steps SharedControlTail.installed_firstLayer⟩

theorem installed_lowerSetup : LowerSetupSteps Images.signImage :=
  ⟨SharedLowerSetup.call_steps SharedFloor.installed_dispatch SharedHints.installed_code SharedLowerRegisters.installed_code⟩

theorem installed_lowerTail : LowerTailSteps Images.signImage :=
  ⟨SharedReveal.prepared_steps SharedReveal.installed_stepCode SharedReveal.installed_byteCode SharedReveal.installed_setupCode,
   SharedResidual.residual22448_steps SharedResidual.installed22448,
   SharedControlTail.nextLayer_steps SharedControlTail.installed_nextLayer⟩

theorem installed_finish : FinishSteps Images.signImage :=
  ⟨SharedTopDigits.restore_steps SharedTopDigits.installed_restore,
   SharedControlTail.topProduce_steps SharedControlTail.installed_topProduce⟩

theorem installed_prefix_good {sk : BitVec 256}
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s prefixCost (prefixSearch index p forest) (PrefixPost Images.signImage index p forest s) :=
  prefix_good (installed_searchCalls sk) installed_topSetup installed_topTail installed_lowerSetup
    installed_lowerTail installed_finish index hi p forest s hp hstable hh hc32

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem installed_topCalls (sk : SecretKey) (cache : Bytes 131072) :
    TopCalls Images.signImage sk cache := by
  constructor
  intro leaf hl ds u up hb hr h18 h25 hd ud
  have H := SharedTopContinuation.top_only SharedTopBlocks.installed_code
    ClaudeWCT.W9.Machine.Sign.SharedTopLeafP.installed_continuation_leaf leaf hl ds u up hb hr h18 h25 hd ud
  exact H.mono (le_refl _) (by
    intro top t ht
    rcases ht with ⟨tp,tv,ta,tf,tm⟩
    exact ⟨tp,tv,ta,tf,tm _ (Or.inl rfl),tm _ (Or.inr rfl)⟩)

theorem installed_searchPreparedLayers_good {sk : SecretKey} {cache : Bytes 131072}
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (LayersPost Images.signImage index p) :=
  searchPreparedLayers_good (installed_topCalls sk cache) (installed_searchCalls sk)
    installed_topSetup installed_topTail installed_lowerSetup installed_lowerTail installed_finish
    index hi p forest s hp hstable hbase hh hc32

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9

theorem base_stateBase {sk : SecretKey} {cache : Bytes 131072} {s : MachineState} {flag : Nat}
    (h : Base (cfFlag:=flag) sk cache s) : SharedTopPath.StateBase sk cache s :=
  ⟨h.x5,h.p0,h.p8,h.p32,h.p40,h.p48,h.p56,h.region,fun A hA hn _ _ => h.zero A hA hn⟩

theorem base_tables {sk : SecretKey} {cache : Bytes 131072} {s : MachineState}
    (h : Base (cfFlag:=0) sk cache s) : Tables s :=
  ⟨h.x5,h.zero _ (by decide) (by unfold NeverW;tauto),h.table,h.cf,h.reward,h.zt⟩

theorem built_stable {sk : SecretKey} {cache : Bytes 131072} {index : Nat} {forest : Digest×Digest}
    {s t : MachineState} {p : PreparedRoots}
    (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t) : Stable index p forest t :=
  ⟨base_tables h.base,h.indexMem,h.one,h.two,h.three,h.forestL,h.forestR⟩

theorem from_built_good {sk : SecretKey} {cache : Bytes 131072}
    {index : Nat} (hi : index<2^31) {p : PreparedRoots} {forest : Digest×Digest}
    {s t : MachineState} (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk t (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (LayersPost Images.signImage index p) := by
  apply installed_searchPreparedLayers_good index hi p forest t h.pc (built_stable h)
    (base_stateBase h.base) h.hintZero
  obtain ⟨c,hc,hv⟩ := hc32
  exact ⟨c,hc,h.counterMem.trans hv⟩

end SigGolfCandidate.T3M.Sign.SharedSearches

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def innerCode (c : Nat) : List (BitVec 32) := ((coordCodesW.getD c []).drop 1).take (lI c-cbase c-1)
theorem inner_bounds (c : Fin 9) : cbase c.val+1≤lI c.val ∧ lI c.val-cbase c.val≤(coordCodesW.getD c.val []).length ∧ cbase c.val<2^20 := by
  fin_cases c <;> decide +kernel

theorem codeAt_get_word {im : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : b<2^30) (hc : CodeAt im (pcOf b) code) {i : Nat} {w : BitVec 32}
    (hi : code[i]?=some w) : im.code[b+i]?=some w := by
  have hpc : (pcOf b).toNat=4096+4*b := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest,hrest⟩ := hc.2.2.2
  rw [hpc,show (4096+4*b-4096)/4=b by omega] at hrest
  have hlen:= (List.getElem?_eq_some_iff.mp hi).1
  have hh : (code++rest)[i]?=some w := by rwa [List.getElem?_append_left hlen]
  rw [hrest,List.getElem?_drop] at hh
  simpa [Nat.add_comm] using hh

theorem fetch_of_code {im : Image}
    (hh : CodeAt im (pcOf 11003) headCode)
    (hi : ∀c : Fin 9,CodeAt im (pcOf (cbase c.val+1)) (innerCode c.val))
    (ha : CodeAt im (pcOf 1700) arenaCode) (hs : CodeAt im (pcOf 21200) ftsStub) : Fetch im := by
  constructor
  · intro n w hw
    unfold headLook at hw
    split at hw
    · rename_i hle
      have he:=codeAt_get_word (by decide : 11003<2^30) hh hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
  · intro c hc n w hw
    have hb:=inner_bounds ⟨c,hc⟩
    dsimp only at hb
    unfold coordLook at hw
    split at hw
    · rename_i hn
      unfold coordLookW at hw
      have hw' : (innerCode c)[n-(cbase c+1)]?=some w := by
        unfold innerCode
        rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop]
        rwa [show 1+(n-(cbase c+1))=n-cbase c by omega]
      have hf:=codeAt_get_word (by omega : cbase c+1<2^30) (hi ⟨c,hc⟩) hw'
      simpa [show cbase c+1+(n-(cbase c+1))=n by omega] using hf
    · split at hw
      · rename_i hn2
        have he := codeAt_get_word (by decide : 21200 < 2^30) hs hw
        simpa [show 21200 + (n - 21200) = n by omega] using he
      · unfold arenaLook at hw
        split at hw
        · rename_i hle
          have he := codeAt_get_word (by decide : 1700 < 2^30) ha hw
          simpa [Nat.add_sub_cancel' hle] using he
        · cases hw
#print axioms fetch_of_code
end ClaudeWCT.W9.Machine.Sign.SharedReuse


namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_fetch : Fetch Images.signImage := by
  apply fetch_of_code
  · sign_slice_fast
  · intro c
    fin_cases c <;> sign_slice_fast
  · sign_slice_fast
  · sign_slice_fast
#print axioms installed_fetch
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_c4Stub : CodeAt Images.signImage (pcOf c4StubPc) c4Stub := by
  sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hstub
      have he := SharedReuse.codeAt_get_word (by decide : c4StubPc < 2^30) installed_c4Stub hw
      simpa [Nat.add_sub_cancel' hstub.2] using he
    · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_c4Stub : CodeAt Images.signImage (pcOf c4StubPc) c4Stub := by
  sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hstub
      have he := SharedReuse.codeAt_get_word (by decide : c4StubPc < 2^30) installed_c4Stub hw
      simpa [Nat.add_sub_cancel' hstub.2] using he
    · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
/-- C1: the stub words in the former nop gaps of `signCode_85`. -/
theorem installed_stub (c : Fin 9) : CodeAt Images.signImage (pcOf (stubPc c.val)) (stubWords c.val) := by
  fin_cases c <;> apply codeAt_sign_last <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hle
      have hb : stubPc c<2^30 := by
        have h : ∀ c : Fin 9,stubPc c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he := SharedReuse.codeAt_get_word hb (installed_stub ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
#print axioms installed_code
#print axioms installed_stub
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
/-- C1: the stub words in the former nop gaps of `signCode_85`. -/
theorem installed_stub (c : Fin 9) : CodeAt Images.signImage (pcOf (stubPc c.val)) (stubWords c.val) := by
  fin_cases c <;> apply codeAt_sign_last <;> decide +kernel
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · split at hw
    · rename_i hle
      have hb : stubPc c<2^30 := by
        have h : ∀ c : Fin 9,stubPc c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he := SharedReuse.codeAt_get_word hb (installed_stub ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
#print axioms installed_code
#print axioms installed_stub
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_hookCode (c : Fin 9) : CodeAt Images.signImage (pcOf (lI c.val)) [hookWords.getD c.val 0] := by
  fin_cases c <;> sign_slice_fast
theorem installed_hookLook (c : Nat) (hc : c<9) : LookOK Images.signImage (hookLook c) := by
  intro n w hw
  unfold hookLook at hw
  split at hw
  · rename_i he
    have hh : hookWords.getD c 0=w := Option.some.inj hw
    have hb : lI c<2^30 := by
      have h : ∀ c : Fin 9,lI c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have hx := SharedReuse.codeAt_get_word (i:=0) hb (installed_hookCode ⟨c,hc⟩) (by simpa [hh])
    simpa [he] using hx
  · cases hw
#print axioms installed_hookCode
#print axioms installed_hookLook
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (basePc c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : basePc c<2^30 := by
      have h : ∀ c : Fin 9,basePc c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hle
    have hb : entry c<2^30 := by
      have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have he := SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
    simpa [Nat.add_sub_cancel' hle] using he
  · cases hw
#print axioms installed_code
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_code (c : Fin 9) : CodeAt Images.signImage (pcOf (entry c.val)) (words c.val) := by
  fin_cases c <;> sign_slice_fast
theorem installed_hookCode (c : Fin 9) : CodeAt Images.signImage (pcOf (cbase c.val)) [hookWord c.val] := by
  fin_cases c <;> sign_slice_fast
theorem installed_look (c : Nat) (hc : c<9) : LookOK Images.signImage (look c) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i he
    have hh : hookWord c=w := Option.some.inj hw
    have hb : cbase c<2^30 := by
      have h : ∀ c : Fin 9,cbase c.val<2^30 := by decide +kernel
      exact h ⟨c,hc⟩
    have hx:=SharedReuse.codeAt_get_word (i:=0) (w:=w) hb (installed_hookCode ⟨c,hc⟩) (by simpa [hh])
    simpa [he] using hx
  · split at hw
    · rename_i hle
      have hb : entry c<2^30 := by
        have h : ∀ c : Fin 9,entry c.val<2^30 := by decide +kernel
        exact h ⟨c,hc⟩
      have he:=SharedReuse.codeAt_get_word hb (installed_code ⟨c,hc⟩) hw
      simpa [Nat.add_sub_cancel' hle] using he
    · cases hw
#print axioms installed_code
#print axioms installed_hookCode
#print axioms installed_look
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open SigGolfCandidate.T3M
theorem installed_Code (c : Nat) (hc : c<9) : Code Images.signImage c :=
  ⟨SharedField.installed_look c hc, SharedLeaf.installed_look c hc,
   SharedLeaf.installed_hookLook c hc, SharedNext.installed_look c hc,
   SharedNode.installed_look c hc, SharedTail.installed_look c hc,
   SharedFinish.installed_look c hc, SharedPath.installed_look c hc,
   SharedEnd.installed_look c hc⟩
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate

namespace ClaudeWCT.W9.Machine.Sign.SharedBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_forTail : CodeAt Images.signImage (pcOf 20715) (tailCode.take 28) := by
  sign_slice_fast
theorem installed_forTramp : CodeAt Images.signImage (pcOf 21450) signTramp := by
  sign_slice_fast
theorem installed_forLook : LookOK Images.signImage forLook := by
  intro n w hw
  unfold forLook at hw
  split at hw
  · rename_i hn
    have he:(tailCode.take 28)[n-20715]?=some w := by
      rw [List.getElem?_take,if_pos (by omega)];exact hw
    have hh:=SharedReuse.codeAt_get_word (by decide:20715<2^30) installed_forTail he
    simpa only[Nat.add_sub_cancel' hn.1]using hh
  · unfold trampLook at hw
    split at hw
    · rename_i hn
      have hh:=SharedReuse.codeAt_get_word (by decide:21450<2^30) installed_forTramp hw
      simpa only[Nat.add_sub_cancel' hn]using hh
    · cases hw
#print axioms installed_forLook
end ClaudeWCT.W9.Machine.Sign.SharedBoundary

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_sign_code : CodeAt Images.signImage (pcOf (base false)) (words false) := by
  sign_slice_fast
theorem installed_sign_look : LookOK Images.signImage (look false) := look_of_code false installed_sign_code
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_sign_success : CodeAt Images.signImage (pcOf 22754) signCode := by
  sign_slice_fast
theorem installed_sign_failure_jump : CodeAt Images.signImage (pcOf 22764) [0xcccea06f] := by
  sign_slice_fast
theorem installed_sign_failure : CodeAt Images.signImage (failPC false) failureCode := by
  sign_slice_fast
theorem installed_sign_failure_ecall : CodeAt Images.signImage (pcOf 545) [0x73] := by
  sign_slice_fast
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open Packed.Boundary
open Packed (L0W)
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

def FramedLayersPost (im : Image) (index : Nat) (p : PreparedRoots) (s : MachineState) :
    Option CanonicalLayers→MachineState→Prop
  | none,t => SearchError im t
  | some layers,t => LayersPost im index p (some layers) t ∧ Frame s t (fun A=>WorkWrites A ∨ L0W A)

theorem searchPreparedLayers_framed {im : Image} {sk : SecretKey} {cache : Bytes 131072}
    (hc : TopCalls im sk cache) (hs : SearchCalls im sk)
    (htop : TopSetupSteps im) (htail : TopTailSteps im) (hlower : LowerSetupSteps im)
    (hltail : LowerTailSteps im) (hfinish : FinishSteps im)
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim im sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (FramedLayersPost im index p s) := by
  rw [searchPreparedLayers_prefix]
  refine TBSim.bind (prefix_good hs htop htail hlower hltail hfinish index hi p forest s hp hstable hh hc32)
    (W₂:=335006) (Q₂:=FramedLayersPost im index p s) ?_
  intro a u hu
  cases a with
  | none => exact (TBSim.pure (a:=none) (s:=u) (Q:=FramedLayersPost im index p s) hu).mono (by omega) (fun _ _ h=>h)
  | some a =>
    change PrefixReady index p forest a s u at hu
    have hb := stateBase_frame hbase hu.frame hu.stable.tables.x5
    have hleaf : index/2^19<4096 := by omega
    have hregs : TopRegs (index/2^19) u :=
      ⟨hu.layer,hu.tree,hu.selected.trans hu.leaf,hu.chains,hu.n4⟩
    have hd7 : ∀ i<54,a.d0.getD i 0≤T3.maxDigit 0 i := by
      obtain ⟨v,hv⟩ := hu.decoded
      change T3.decode 0 v=some a.d0 at hv
      intro i hi
      exact T3.decode_digit_max hv i hi
    have H := hc.call (index/2^19) hleaf a.d0 u hu.pc hb hregs hu.leaf hu.sum hd7 hu.digits
    unfold finishSource
    have hr : (route index 0).1=index/2^19 := by
      change index/2^19%2^12=index/2^19
      exact Nat.mod_eq_of_lt hleaf
    rw [hr]
    refine (TBSim.bind H (W₂:=0) (Q₂:=FramedLayersPost im index p s) ?_).mono (by omega) (fun _ _ h=>h)
    intro top t ht
    rcases ht with ⟨htpc,htv,htp,htf,hth,htr⟩
    refine TBSim.pure (a:=some (layersValue index p a top)) (s:=t) (Q:=FramedLayersPost im index p s) ?_
    refine ⟨⟨a,top,rfl,htpc,htv,htp,?_,?_,?_,hth.trans hu.hints,htr.trans hu.residual,hu.credit⟩,hu.frame.trans htf⟩
    · exact hu.one.frame_top (by decide) (prepared_length 1 (by decide) _ _ _).1 (prepared_length 1 (by decide) _ _ _).2 htf
    · exact hu.two.frame_top (by decide) (prepared_length 2 (by decide) _ _ _).1 (prepared_length 2 (by decide) _ _ _).2 htf
    · exact hu.three.frame_top (by decide) (prepared_length 3 (by decide) _ _ _).1 (prepared_length 3 (by decide) _ _ _).2 htf

#print axioms searchPreparedLayers_framed
end SigGolfCandidate.T3M.Sign.SharedSearches
namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def LowFrame (s t : MachineState) : Prop := Frame s t (fun A => ¬(SIG≤A ∧ A<SIG+2192))

theorem LowFrame.trans {s t u : MachineState} (h : LowFrame s t) (h' : LowFrame t u) : LowFrame s u :=
  (Frame.trans h h').mono (by intro A hA h;exact h.elim id id)

theorem OnePost.lowFrame {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower}
    (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) : LowFrame s t := by
  apply h.frame.mono
  intro A hA hw hsig
  unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr at hw
  fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT,SIG] <;> omega

theorem prepareRoots_framed {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=1) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (3*(btCost+47)) (prepareRoots index) (fun p t => RootsPost (cfFlag := cfFlag) sk cache index s p t ∧ LowFrame s t) := by
  have r1 := one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    (lay := 1) (by decide) hi s hpc h8 hidx hb hz
  unfold prepareRoots
  refine TBSim.mono (TBSim.bind r1 (fun p1 t1 h1 =>
    TBSim.bind (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
      (lay := 2) (by decide) hi t1 (by simpa using h1.pc) h1.layer h1.indexMem h1.base h1.zero)
      (fun p2 t2 h2 => TBSim.bind
        (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
          (lay := 3) (by decide) hi t2 (by simpa using h2.pc) h2.layer h2.indexMem h2.base h2.zero)
        (fun p3 t3 h3 => TBSim.pure ?_)))) (by omega) (fun _ _ h => h)
  refine ⟨?_, ((h1.lowFrame (by decide)).trans (h2.lowFrame (by decide))).trans (h3.lowFrame (by decide))⟩
  refine ⟨by simpa using h3.pc,by simpa using h3.layer,h3.base,h3.indexMem,?_,?_,h3.stored,?_,?_⟩
  · exact (h1.stored.after (by decide) (by decide) (by decide) h2).after
      (by decide) (by decide) (by decide) h3
  · exact h2.stored.after (by decide) (by decide) (by decide) h3
  · exact (((h1.rootsFrame (by decide)).trans (h2.rootsFrame (by decide))).trans
      (h3.rootsFrame (by decide))).mono (by intro A hA h; rcases h with (h|h)|h <;> exact h)
  · exact (h3.counterMem (by decide)).trans ((h2.counterMem (by decide)).trans (h1.counterMem (by decide)))

theorem entry_roots_framed {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat} (hi : index<2^31)
    (forest : Digest×Digest) (s : MachineState) (hpc : s.pc=pcOf 22100)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hl : DigAt s ENC forest.1) (hr : DigAt s (ENC+48) forest.2) :
    TBSim im sk s (28+3*(btCost+47)) (prepareRoots index) (fun p t => BuiltPost (cfFlag := cfFlag) sk cache index forest s p t ∧ LowFrame s t) := by
  obtain ⟨a,sa,ap,a8,al,ar,az,ad,ars,af⟩ := entry_steps he s hpc forest.1 forest.2 hl hr
  have af' : Frame s a EntryWrites := af.mono (by unfold EntryWrites; intros A hA h; exact h)
  have abase : Base (cfFlag := cfFlag) sk cache a := hb.frame af' ars (by decide) (by
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold EntryWrites at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA,DIGITS] at hbase hw
    omega)
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (af'.get (A := 0x20550) (by decide) (by unfold EntryWrites DIGITS; omega)).trans hidx
  refine (TBSim.steps sa (prepareRoots_framed hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    hi a ap a8 aidx abase ad)).mono (le_refl _) ?_
  intro p t hpair
  rcases hpair with ⟨ht,hlo⟩
  refine ⟨?_, ?_⟩
  · refine ⟨ht.pc,ht.layer,ht.base,ht.indexMem,ht.one,ht.two,ht.three,?_,?_,?_,af'.trans ht.frame,?_⟩
    · exact (ht.frame.get (A := 0x66000) (by decide) (by unfold RootsWrites; decide)).trans az
    · exact al.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
    · exact ar.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
    · exact ht.counterMem.trans (af'.get (A := ENC+32) (by unfold ENC; decide) (by unfold EntryWrites ENC DIGITS; decide))
  · exact (show LowFrame s a from af'.mono (by unfold EntryWrites SIG DIGITS; intros A hA hw hsig; omega)).trans hlo

#print axioms entry_roots_framed
end SigGolfCandidate.T3M.Sign.SharedRootControl
namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
theorem installed_searchPreparedLayers_framed {sk : SecretKey} {cache : Bytes 131072}
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : Digest×Digest)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk s (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (FramedLayersPost Images.signImage index p s) :=
  searchPreparedLayers_framed (installed_topCalls sk cache) (installed_searchCalls sk)
    installed_topSetup installed_topTail installed_lowerSetup installed_lowerTail installed_finish
    index hi p forest s hp hstable hbase hh hc32


theorem from_built_framed {sk : SecretKey} {cache : Bytes 131072}
    {index : Nat} (hi : index<2^31) {p : PreparedRoots} {forest : Digest×Digest}
    {s t : MachineState} (h : SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t)
    (hc32 : ∃ c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) :
    TBSim Images.signImage sk t (prefixCost+335006) (searchPreparedLayers (cacheDec cache) index p forest)
      (FramedLayersPost Images.signImage index p t) := by
  apply installed_searchPreparedLayers_framed index hi p forest t h.pc (built_stable h)
    (base_stateBase h.base) h.hintZero
  obtain ⟨c,hc,hv⟩ := hc32
  exact ⟨c,hc,h.counterMem.trans hv⟩

end SigGolfCandidate.T3M.Sign.SharedSearches
namespace SigGolfCandidate.T3M.Sign.SharedSearches
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open Packed.Boundary
open Packed (L0W)

theorem layers_lowFrame {s t : MachineState} (h : Frame s t (fun A=>WorkWrites A ∨ L0W A)) :
    Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)) := by
  apply h.mono
  intro A hA hw hlo
  rcases hw with hw|hw
  · rcases hw with hw|hw|hw|hw|hw|hw|⟨lay,hl,hu,ha,hb⟩
    all_goals first | (simp only [ENC,EOUT,DIGITS,SIG] at *;omega) | skip
    unfold SharedRootControl.sigBase at ha hb
    simp only [SIG] at hlo
    split_ifs at ha hb <;>omega
  · exact hw.1 hlo

#print axioms layers_lowFrame
end SigGolfCandidate.T3M.Sign.SharedSearches
