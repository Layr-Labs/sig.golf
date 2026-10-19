import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_TopLeafP
import SigGolfCandidate.T3M_Sign_PackedBoundaryEntry
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_PackedLeaf
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsLoop

set_option Elab.async false

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
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
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
