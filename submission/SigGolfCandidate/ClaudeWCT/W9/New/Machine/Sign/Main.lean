import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsLoop

section

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
structure GlobSt (sk : BitVec 256) (N : BitVec 256) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x22 : t.getReg .x22 = BitVec.ofNat 64 (N.toNat % 2 ^ 31)
  nbuf : OutAt t NBUF N
  table : TableAt t
  p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64
  zero : ∀ A, ScrZero A → t.getMem (BitVec.ofNat 64 A) = 0
def coordW (c : Nat) (A : Nat) : Prop :=
  loopW c A ∨ treeW A ∨ (FORW + forOff c ≤ A ∧ A < FORW + forOff c + 32) ∨ (slotP c 0 ≤ A ∧ A < slotP c 7)
theorem GlobSt.frame {sk N : BitVec 256} {s t : MachineState} {c : Nat} {l : List Reg} (hc : c < 9)
    (h : GlobSt sk N s) (hr : RegsExcept s t l) (hl : .x5 ∉ l ∧ .x22 ∉ l) (hf : Frame s t (coordW c)) :
    GlobSt sk N t := by
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  have nw : ∀ A, (NBUF ≤ A ∧ A < NBUF + 32 ∨ TBL ≤ A ∧ A < TBL + 65536 ∨ A = PRIVW ∨ A = PRIVW + 8 ∨
      A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ ScrZero A) → ¬ coordW c A := by
    intro A hA hw
    unfold coordW loopW bodyW treeW slotV slotP ScrZero at *
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
    rw [hf.get hA' (nw _ (by simp [hA]))]; exact h.zero A hA
theorem coordW_other {c c' A : Nat} (hc : c < 9) (hc' : c' < 9) (hne : c ≠ c')
    (hA : (SIG + 16 + 224 * c' ≤ A ∧ A < SIG + 16 + 224 * (c' + 1)) ∨
      (FORW + forOff c' ≤ A ∧ A < FORW + forOff c' + 32)) : ¬ coordW c A := by
  have h1 : forOff c ≤ 288 := by unfold forOff; omega
  have h2 : forOff c' ≤ 288 := by unfold forOff; omega
  have h3 : forOff c + 32 ≤ forOff c' ∨ forOff c' + 32 ≤ forOff c := by unfold forOff; omega
  intro hw
  unfold coordW loopW bodyW treeW slotV slotP at *
  aoh
def coordC (c : Nat) : Nat := fk c + (1 + (1 + (128 * loopStepC + (126 * treeC + (12 + 7 * 13)))))
theorem coordC_le (c : Nat) : coordC c ≤ 13 + (1 + (1 + (128 * loopStepC + (126 * treeC + (12 + 7 * 13))))) := by
  unfold coordC fk; split_ifs <;> omega
theorem field_lt16200 {N : BitVec 256} (hadm : WCT9.admissible N = true) {c : Nat} (hc : c < 9) :
    N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14 < 16200 :=
  ((WCT9.admissible_iff N).1 hadm).2 ⟨c, hc⟩
theorem pcI_seven (c : Nat) (hc : c < 9) : pcI c 7 = if c < 8 then cbase (c + 1) else 20715 := by
  interval_cases c <;> decide
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
theorem coord_unit (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) {N : BitVec 256}
    (hadm : WCT9.admissible N = true) {s : MachineState} (hpc : s.pc = pcOf (cbase c)) (hg : GlobSt sk N s)
    (state : List WCT9.Opening × List (Digest × Digest)) :
    TBSim im sk s (coordC c) (WCT9.openingStep (N.toNat % 2 ^ 31) N state ⟨c, hc⟩) (fun st t =>
      t.pc = pcOf (pcI c 7) ∧ GlobSt sk N t ∧
        (∃ op pr, st = (state.1 ++ [op], state.2 ++ [pr]) ∧ OpeningAt t c op ∧ DigAt t (FORW + forOff c) pr.1 ∧
          DigAt t (FORW + forOff c + 16) pr.2) ∧
        RegsExcept s t ftsRegs ∧ Frame s t (coordW c)) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hf16 := field_lt16200 hadm hc
  have hsel128 : N.toNat / 2 ^ WCT9.coordBase c % 128 < 128 := Nat.mod_lt _ (by norm_num)
  obtain ⟨t1, s1, p1, x24, x28, r1, f1⟩ := step_F hcode hc s hpc hg.nbuf
  have ht1 : TableAt t1 := fun k hk => by rw [f1.get (by ao) id]; exact hg.table k hk
  obtain ⟨t2, s2, p2, x25, r2, f2⟩ := step_lwu hcode hc t1 p1 (by omega) x28 ht1
  obtain ⟨t3, s3, p3, x18, r3, f3⟩ := step_Z hcode hc t2 p2
  have g3 : ∀ A, A < 2 ^ 64 → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [f3.get hA id, f2.get hA id, f1.get hA id]
  have hz : ∀ A, ScrZero A → t3.getMem (BitVec.ofNat 64 A) = 0 := fun A hA => by
    rw [g3 A (by unfold ScrZero at hA; aoh)]; exact hg.zero A hA
  have r13 : RegsExcept s t3 [.x6, .x18, .x24, .x25, .x28] := ((r1.trans r2).trans r3).mono (by simp)
  have hb3 : BodySt sk 0 (N.toNat % 2 ^ 31) (N.toNat / 2 ^ WCT9.coordBase c % 128)
      (pkAt (N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14)) t3 :=
    ⟨by rw [r13.get (by simp)]; exact hg.x5, x18, by rw [r13.get (by simp)]; exact hg.x22,
      by rw [r3.get (by simp), r2.get (by simp)]; exact x24, by rw [r3.get (by simp)]; exact x25,
      by rw [g3 _ (by ao)]; exact hg.p0, by rw [g3 _ (by ao)]; exact hg.p8, by rw [g3 _ (by ao)]; exact hg.p32,
      by rw [g3 _ (by ao)]; exact hg.p40, hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]),
      hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero])⟩
  have hword : ∀ i : Fin 7, pkAt (N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14) / 4 ^ i.val % 4 =
      WCT9.wordDigit (WCT9.rank N ⟨c, hc⟩) i := fun i => pkAt_digit _ hf16 i
  unfold WCT9.openingStep
  dsimp only
  simp only [WCT9.buildCoordinate_factor, bind_assoc, pure_bind]
  refine (TBSim.steps ((s1.trans s2).trans s3) (TBSim.bind (W₂ := 126 * treeC + (12 + 7 * 13))
    (child_loop (word := WCT9.rank N ⟨c, hc⟩) hcode hc hsel128 hidx (by have := pkAt_lt (N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14); omega)
      hword (LoopInv.init p3 hb3)) (fun rows t4 h4 => ?_))).mono (by unfold coordC; omega) (fun _ _ h => h)
  have h4pc : t4.pc = pcOf (nodeI c) := by have := h4.pc; rwa [if_neg (by norm_num)] at this
  have h4b := h4.body
  rw [if_neg (by norm_num)] at h4b
  have g4 : ∀ A, A < 2 ^ 64 → ¬ loopW c A → t4.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => h4.frame.get hA hn
  have h0 : TreeInv c (N.toNat % 2 ^ 31) t4 0 ((List.replicate 128 (0 : Digest) ++ rows.1).toArray) t4 :=
    ⟨by rw [if_pos (by norm_num)]; exact h4pc, h4b.x5, h4b.x18, h4b.x22, by simp [h4.len],
      fun m hm1 hm2 => by
        rw [toArray_getD_high _ _ (by omega)]
        have := h4.leaves (m - 128) (by omega)
        rwa [show 128 + (m - 128) = m by omega] at this,
      by rw [g4 _ (by ao) (by unfold loopW bodyW slotV; intro h; aoh)]; exact hz _ (by simp [ScrZero]),
      by rw [g4 _ (by ao) (by unfold loopW bodyW slotV; intro h; aoh)]; exact hz _ (by simp [ScrZero]),
      RegsExcept.refl _ _, Frame.refl _ _⟩
  refine TBSim.bind (W₂ := 12 + 7 * 13) (tree_loop hcode hc hidx h0) (fun heap t5 h5 => ?_)
  have h5pc : t5.pc = pcOf (rI c) := by have := h5.pc; rwa [if_neg (by norm_num)] at this
  obtain ⟨t6, s6, p6, q0, q8, q16, q24, r6, f6⟩ := step_R0 hcode hc t5 h5pc
  have h24 : t6.getReg .x24 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.coordBase c % 128) := by
    rw [r6.get (by simp), h5.regs.get (by simp [treeRegs])]; exact h4b.x24
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  have hheap6 : ∀ m, 2 ≤ m → m < 256 → DigAt t6 (HEAPW + 16 * m) (heap.getD m 0) := fun m h1 h2 =>
    (h5.heap m (by omega) h2).frame f6 (by ao) (by intro h; rcases h with h | h | h | h <;> aoh)
      (by intro h; rcases h with h | h | h | h <;> aoh)
  obtain ⟨t7, s7, p7, hpath, r7, f7⟩ := path_copies hcode hc hsel128 7 le_rfl t6 (by rw [p6]) h24 hheap6
  have hregs : RegsExcept s t7 ftsRegs :=
    ((((r13.trans h4.regs).trans h5.regs).trans r6).trans r7).mono (by simp [ftsRegs, bodyRegs, treeRegs])
  have hframe : Frame s t7 (coordW c) := by
    refine (((((f1.trans f2).trans f3).trans h4.frame).trans h5.frame).trans f6 |>.trans f7).mono (fun A _ hA => ?_)
    unfold coordW
    rcases hA with (((((hA | hA) | hA) | hA) | hA) | hA) | hA
    · exact hA.elim
    · exact hA.elim
    · exact hA.elim
    · left; exact hA
    · right; left; exact hA
    · right; right; left; rcases hA with h | h | h | h <;> (subst h; constructor <;> omega)
    · right; right; right; exact hA
  have hval : ∀ i : Fin 7, DigAt t7 (SIG + 16 + 224 * c + 16 * i.val) (rows.2.1.getD i.val 0) := fun i => by
    obtain ⟨-, hd⟩ := h4.vals hsel128
    have h1 := hd i.val i.isLt
    unfold slotV at h1
    refine ((h1.frame h5.frame (by ao) ?_ ?_).frame f6 (by ao) ?_ ?_).frame f7 (by ao) ?_ ?_ <;>
      (intro h; (try simp only [treeW, slotP] at h); have := i.isLt; aoh)
  refine TBSim.pure_steps' (s6.trans s7) ⟨p7, GlobSt.frame hc hg hregs (by simp [ftsRegs]) hframe,
    ⟨_, _, rfl, ⟨fun i => hval i, fun l => ?_⟩, ?_, ?_⟩, hregs, hframe⟩
  · have hx : N.toNat / 2 ^ WCT9.coordBase c % 128 / 2 ^ l.val ^^^ 1 < 2 ^ (7 - l.val) := by
      have := pathHeap_lt _ l.val hsel128 l.isLt
      have h2 := pathIdx_eq _ hsel128 l.val l.isLt
      have : (N.toNat / 2 ^ WCT9.coordBase c % 128 + 128) / 2 ^ l.val ^^^ 1 < 2 ^ (7 - l.val + 1) := by
        apply Nat.xor_lt_two_pow
        · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 7 - l.val + 1 + l.val = 8 by omega]; omega
        · exact Nat.one_lt_two_pow (by omega)
      rw [pow_succ] at this; omega
    have := hpath l.val (by omega) l.isLt
    unfold slotP at this
    show DigAt t7 (SIG + 128 + 224 * c + 16 * l.val) (((List.range 7).map fun level =>
      ((WCT9.heapLevels heap).getD level []).getD ((WCT9.child N ⟨c, hc⟩).val / 2 ^ level ^^^ 1) 0).getD l.val 0)
    have hcv : (WCT9.child N ⟨c, hc⟩).val = N.toNat / 2 ^ WCT9.coordBase c % 128 := rfl
    rw [getD_map_range7 _ l.isLt, hcv, show ((WCT9.heapLevels heap).getD l.val []).getD _ 0 =
      SigGolfCandidate.T3.Correctness.treeValue (WCT9.heapLevels heap) l.val _ from rfl,
      WCT9.heapLevels_value heap l.val _ l.isLt hx]
    exact this
  · have h1 : DigAt t6 (FORW + forOff c) (heap.getD 2 0) := by
      have := h5.heap 2 (by norm_num) (by norm_num)
      exact ⟨by rw [q0]; exact this.1, by rw [q8]; exact this.2⟩
    show DigAt t7 (FORW + forOff c) (((WCT9.heapLevels heap).getD 6 []).getD 0 0)
    rw [show ((WCT9.heapLevels heap).getD 6 []).getD 0 0 = heap.getD 2 0 from
      WCT9.heapLevels_value heap 6 0 (by norm_num) (by norm_num)]
    exact h1.frame f7 (by ao) (by unfold slotP; intro h; aoh) (by unfold slotP; intro h; aoh)
  · have h1 : DigAt t6 (FORW + forOff c + 16) (heap.getD 3 0) := by
      have := h5.heap 3 (by norm_num) (by norm_num)
      refine ⟨?_, ?_⟩
      · rw [q16]; exact this.1
      · rw [show FORW + forOff c + 16 + 8 = FORW + forOff c + 24 by omega, q24]; exact this.2
    show DigAt t7 (FORW + forOff c + 16) (((WCT9.heapLevels heap).getD 6 []).getD 1 0)
    rw [show ((WCT9.heapLevels heap).getD 6 []).getD 1 0 = heap.getD 3 0 from
      WCT9.heapLevels_value heap 6 1 (by norm_num) (by norm_num)]
    exact h1.frame f7 (by ao) (by unfold slotP; intro h; aoh) (by unfold slotP; intro h; aoh)
end coord
end ClaudeWCT.W9.Machine.Sign
end
section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
def coordCmax : Nat := 13 + (1 + (1 + (128 * loopStepC + (126 * treeC + (12 + 7 * 13)))))
def ftsW' (A : Nat) : Prop := (PRIVW ≤ A ∧ A < SCREND) ∨ (SIG + 16 ≤ A ∧ A < SIG + 2032)
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
    (hW : ∀ A, SIG + 16 + 224 * c ≤ A → A < SIG + 16 + 224 * (c + 1) → ¬ W A) : OpeningAt t c op := by
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
section fts
variable {im : Image} {sk : BitVec 256}
theorem fts_step (hcode : NewCodeAt im) {N : BitVec 256} (hadm : WCT9.admissible N = true) {s0 : MachineState}
    (k : Nat) (hk : k < 9) (st : List WCT9.Opening × List (Digest × Digest)) (t : MachineState)
    (h : FtsInv sk N s0 k st t) :
    TBSim im sk t coordCmax
      ((fun st k => if h : k < 9 then WCT9.openingStep (N.toNat % 2 ^ 31) N st ⟨k, h⟩ else pure st) st (0 + k))
      (FtsInv sk N s0 (k + 1)) := by
  simp only [Nat.zero_add, dif_pos hk]
  have hpc : t.pc = pcOf (cbase k) := by rw [h.pc, if_pos hk]
  refine (coord_unit hcode hk hadm hpc h.glob st).mono (coordC_le k) (fun st' u hu => ?_)
  obtain ⟨upc, ug, ⟨op, pr, rfl, hop, hpr1, hpr2⟩, uregs, uframe⟩ := hu
  have hfo : forOff k ≤ 288 := by unfold forOff; omega
  refine ⟨?_, ug, by simp [h.len1], by simp [h.len2], fun c hc => ?_, (h.regs.trans uregs).mono (by simp),
    (h.frame.trans uframe).mono (fun A _ hA => ?_)⟩
  · rw [upc, pcI_seven k hk]
    by_cases h8 : k < 8
    · rw [if_pos h8, if_pos (by omega)]
    · rw [if_neg h8, if_neg (by omega)]
  · rw [getD_snoc, getD_snoc, h.len1, h.len2]
    by_cases hck : c < k
    · rw [if_pos hck, if_pos hck]
      obtain ⟨o1, o2, o3⟩ := h.outs c hck
      have hfo' : forOff c ≤ 288 := by unfold forOff; omega
      have hdis : forOff k + 32 ≤ forOff c ∨ forOff c + 32 ≤ forOff k := by unfold forOff; omega
      exact ⟨o1.frame (by omega) uframe (fun A h1 h2 => coordW_other hk (by omega) (by omega) (Or.inl ⟨h1, h2⟩)),
        o2.frame uframe (by ao) (coordW_other (c' := c) hk (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩))
          (coordW_other (c' := c) hk (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩)),
        o3.frame uframe (by ao) (coordW_other (c' := c) hk (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩))
          (coordW_other (c' := c) hk (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩))⟩
    · have : c = k := by omega
      subst this
      rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_pos rfl, if_pos rfl]
      exact ⟨hop, hpr1, hpr2⟩
  · rcases hA with hA | hA
    · exact hA
    · unfold ftsW'
      unfold coordW loopW bodyW treeW slotV slotP at hA
      aoh
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
theorem ftsC_bound : 11 + (9 * coordCmax + (13 + (8 * 5 + (1 + 0)))) ≤ ftsC := by
  unfold coordCmax loopStepC childC stepC chainC treeC ftsC; norm_num
section fts2
variable {im : Image}
theorem ftsGood (im : Image) : FtsGood im := by
  intro hcode sk N s hpre
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  obtain ⟨t0, s0', p0, k1, k2, r0, f0⟩ := step_SK hcode s hpre.pc
  have g0 : ∀ A, A < 2 ^ 64 → A ≠ PRIVW + 40 → A ≠ PRIVW + 32 → A ≠ PRIVW + 8 → A ≠ PRIVW →
      t0.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 h3 h4 =>
    f0.get hA (by simp [h1, h2, h3, h4])
  have hg0 : GlobSt sk N t0 :=
    { x5 := by rw [r0.get (by simp)]; exact hpre.x5
      x22 := by rw [r0.get (by simp)]; exact hpre.x22
      nbuf := fun k hk => by rw [g0 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hpre.nbuf k hk
      table := fun k hk => by rw [g0 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hpre.table k hk
      p0 := by have := k1 0 (by norm_num); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this]
               exact hpre.sk 0 (by norm_num)
      p8 := by have := k1 1 (by norm_num); simp only [Nat.mul_one] at this; rw [this]; exact hpre.sk 1 (by norm_num)
      p32 := by have := k2 0 (by norm_num); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this]
                exact hpre.sk 2 (by norm_num)
      p40 := by have := k2 1 (by norm_num); simp only [Nat.mul_one] at this; rw [this]
                rw [show SK + 16 + 8 = SK + 8 * 3 from rfl]; exact hpre.sk 3 (by norm_num)
      zero := fun A hA => by
        rw [g0 _ (by unfold ScrZero at hA; aoh) (by unfold ScrZero at hA; aoh) (by unfold ScrZero at hA; aoh)
          (by unfold ScrZero at hA; aoh) (by unfold ScrZero at hA; aoh)]
        exact hpre.zero A hA }
  have hinv0 : FtsInv sk N s 0 ([], []) t0 :=
    ⟨by rw [if_pos (by norm_num)]; exact p0, hg0, rfl, rfl, fun c hc => absurd hc (by omega),
      r0.mono (by simp [ftsRegs]), f0.mono (fun A _ hA => by unfold ftsW'; left; rcases hA with h | h | h | h <;> aoh)⟩
  unfold WCT9.signForest WCT9.forestRows
  rw [foldlM_finRange9]
  refine (TBSim.steps s0' (TBSim.bind (W₂ := 13 + (8 * 5 + (1 + 0)))
    (TBSim.foldlM_range' 0 9 _ _ (FtsInv sk N s) coordCmax (fun k hk st t ht => fts_step hcode hpre.adm k hk st t ht)
      hinv0) (fun st t9 h9 => ?_))).mono ftsC_bound (fun _ _ h => h)
  have h9pc : t9.pc = pcOf 20715 := by have := h9.pc; rwa [if_neg (by norm_num)] at this
  obtain ⟨t1, s1, e1, p1, x10, x11, x12, m0, m8, m16, m24, r1, f1⟩ := step_For hcode t9 h9pc h9.glob.x22
  have hq : hashInput t1 = toQ (pad64 (WCT9.forestInput (N.toNat % 2 ^ 31) st.2)) := by
    refine hashInput_forest t1 st.2 h9.len2 (by omega) x10 x11 (fun c hc => ?_) m0 m8 m16 m24
    have hfo : forOff c ≤ 288 := by unfold forOff; omega
    have hfo' : 32 ≤ forOff c := by unfold forOff; omega
    obtain ⟨-, o2, o3⟩ := h9.outs c hc
    exact ⟨o2.frame f1 (by ao) (by intro h; rcases h with h | h | h | h <;> omega)
        (by intro h; rcases h with h | h | h | h <;> omega),
      o3.frame f1 (by ao) (by intro h; rcases h with h | h | h | h <;> omega)
        (by intro h; rcases h with h | h | h | h <;> omega)⟩
  have hx5 : t1.getReg .x5 = 0 := by rw [r1.get (by simp)]; exact h9.glob.x5
  have hbl : (toQ (pad64 (WCT9.forestInput (N.toNat % 2 ^ 31) st.2))).blocks = 5 := by
    rw [pad64_of_aligned _ (by rw [forestIn_len _ _ h9.len2]), blocks_toQ ⟨by rw [forestIn_len _ _ h9.len2]; norm_num,
      by rw [forestIn_len _ _ h9.len2]⟩, forestIn_len _ _ h9.len2]
  rw [forestPk_eq]
  refine (TBSim.steps s1 (TBSim.shortHash_bind' (W := 1 + 0) (f := fun root => pure (st.1, root)) e1 hx5
    (hashArgs_const t1 FORW 320 FOUT x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
    (fun a => ?_))).mono (by rw [hbl]) (fun _ _ h => h)
  have fh := Frame.writeHash t1 a FOUT x12 (by ao)
  obtain ⟨t2, s2, p2, r2, f2⟩ := step_J hcode (writeHash t1 a) (by rw [pc_writeHash, p1, pcOf_add4])
  have hroot := DigAt.writeHash_lo t1 a FOUT x12 (by ao)
  refine TBSim.pure_steps' s2 ⟨p2, ?_, ?_, h9.len1, fun k hk => ?_, ?_, ?_⟩
  · rw [r2.get (by simp), getReg_writeHash]; exact hx5
  · exact hroot.frame f2 (by ao) id id
  · refine (((h9.outs k hk).1.frame hk f1 (fun A h1 h2 => ?_)).frame hk fh (fun A h1 h2 => ?_)).frame hk f2
      (fun A _ _ h => h)
    · intro h; rcases h with h | h | h | h <;> aoh
    · intro h; aoh
  · exact (h9.regs.trans ((r1.trans (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 (writeHash t1 a) [])).trans
      r2)).mono (by simp [ftsRegs])
  · refine (((h9.frame.trans f1).trans fh).trans f2).mono (fun A _ hA => ?_)
    unfold FtsW
    unfold ftsW' at hA
    rcases hA with ((hA | hA) | hA) | hA
    · rcases hA with hA | hA
      · left; exact hA
      · right; left; exact hA
    · left; rcases hA with h | h | h | h <;> constructor <;> aoh
    · right; right; exact hA
    · exact hA.elim
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
theorem readOutput_sig (imgs : Phase → Image) (t : MachineState) (sig : WCT9.Signature)
    (h : ∀ k < 341, DigAt t (SIG + 16 * k) ((W9.T3M.sigDigests sig).getD k 0)) :
    readOutput (wsub imgs).sizes (wsub imgs).layout .sign t = W9.T3M.sigB sig := by
  have hd : DigsAt t SIG (W9.T3M.sigDigests sig) := fun k hk =>
    h k (by rw [W9.T3M.length_sigDigests] at hk; exact hk)
  have hw := hd.words
  rw [W9.T3M.length_sigDigests] at hw
  have hl : ((W9.T3M.sigDigests sig).flatMap (bytesLE 16)).length = 8 * 682 := by
    have : ∀ ds : List Digest, (ds.flatMap (bytesLE 16)).length = 16 * ds.length := fun ds => by
      induction ds with
      | nil => rfl
      | cons d ds ih => rw [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
    rw [this, W9.T3M.length_sigDigests]
  have e := readBuffer_of_words t SIG 682 ((W9.T3M.sigDigests sig).flatMap (bytesLE 16)) (by decide) (by decide)
    hl hw
  show readBuffer t SIG (8 * 682) = W9.T3M.sigB sig
  rw [e, W9.T3M.sigB, W9.T3M.serialize_eq]
theorem DigAt.of_mem {X Y : MachineState} {a b : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 b) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (b + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y b d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
theorem t3LayIdx_eq (lay : Layer) : t3LayIdx lay = W9.T3M.layIdx lay + 10 := by
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
    ∀ k < 341, DigAt x (SIG + 16 * k)
      ((W9.T3M.sigDigests (WCT9.assembledSignature rho ops ps)).getD k 0) := by
  intro k hk
  obtain ⟨-, -, -, hmove, hfx⟩ := hc
  set sig := WCT9.assembledSignature rho ops ps with hsig
  by_cases hlow : k < 127
  ·
    have keep : ∀ A, SIG ≤ A → A < SIG + 2032 → x.getMem (BitVec.ofNat 64 A) = v.getMem (BitVec.ofNat 64 A) := by
      intro A hS hA
      rw [hfx.get (by so) (by so), hfw.get (by so) (by so)]
    have keepD : ∀ d, DigAt v (SIG + 16 * k) d → DigAt x (SIG + 16 * k) d := fun d hd =>
      DigAt.of_mem hd (keep _ (by so) (by so)) (keep _ (by so) (by so))
    apply keepD
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [W9.T3M.sigDigests_rho, hsig, WCT9.assembledSignature_rho]; simpa using hrho
    · obtain ⟨c, i, hc9, hi14, rfl⟩ : ∃ c i, c < 9 ∧ i < 14 ∧ k = 1 + 14 * c + i :=
        ⟨(k - 1) / 14, (k - 1) % 14, by omega, by omega, by omega⟩
      have ho := hops c hc9
      by_cases hi7 : i < 7
      · have e := W9.T3M.sigDigests_value sig ⟨c, hc9⟩ ⟨i, hi7⟩
        simp only at e
        rw [e, hsig, WCT9.assembledSignature_openings]
        have := ho.1 ⟨i, hi7⟩
        simp only at this
        rwa [show SIG + 16 * (1 + 14 * c + i) = SIG + 16 + 224 * c + 16 * i by ring]
      · have e := W9.T3M.sigDigests_path sig ⟨c, hc9⟩ ⟨i - 7, by omega⟩
        simp only at e
        rw [show 1 + 14 * c + 7 + (i - 7) = 1 + 14 * c + i by omega] at e
        rw [e, hsig, WCT9.assembledSignature_openings]
        have := ho.2 ⟨i - 7, by omega⟩
        simp only at this
        rwa [show SIG + 16 * (1 + 14 * c + i) = SIG + 128 + 224 * c + 16 * (i - 7) by omega]
  ·
    have moveD : ∀ d, DigAt w (SIG + 16 * (k + 10)) d → DigAt x (SIG + 16 * k) d := fun d hd => by
      refine DigAt.of_mem hd ?_ ?_
      · have := hmove (2 * (k - 127)) (by omega)
        rw [show SIG + 2032 + 8 * (2 * (k - 127)) = SIG + 16 * k by so,
          show SIG + 2192 + 8 * (2 * (k - 127)) = SIG + 16 * (k + 10) by so] at this
        exact this
      · have := hmove (2 * (k - 127) + 1) (by omega)
        rw [show SIG + 2032 + 8 * (2 * (k - 127) + 1) = SIG + 16 * k + 8 by so,
          show SIG + 2192 + 8 * (2 * (k - 127) + 1) = SIG + 16 * (k + 10) + 8 by so] at this
        exact this
    apply moveD
    have key : ∀ lay : Layer, ∀ i, i < chainCount lay + height lay → k = W9.T3M.layIdx lay + i →
        DigAt w (SIG + 16 * (k + 10)) ((W9.T3M.sigDigests sig).getD k 0) := by
      intro lay i hi hk'
      have := piece_digest (hpieces lay) (sig := sig) rfl i hi
      rw [t3LayIdx_eq] at this
      rw [hk', show W9.T3M.layIdx lay + i + 10 = W9.T3M.layIdx lay + 10 + i by omega]
      exact this
    by_cases h1 : k < 193
    · exact key 0 (k - 127) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    by_cases h2 : k < 243
    · exact key 1 (k - 193) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    by_cases h3 : k < 292
    · exact key 2 (k - 243) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
    · exact key 3 (k - 292) (by simp [chainCount, height]; omega) (by simp [W9.T3M.layIdx]; omega)
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
  let forest ← WCT9.signForest (output.toNat % 2 ^ 31) output
  let some pieces ← WCT9.signLayersBC (cacheDec cache) (output.toNat % 2 ^ 31) 4 (.forest forest.2) | pure none
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
      ∀ k < 341, DigAt t (SIG + 16 * k) ((W9.T3M.sigDigests sig).getD k 0)
def restC : Nat := searchC + (ftsC + (layC + compactK))
def signCW : Nat := frontC + restC
theorem signCW_eq : signCW = 3433634170 := by
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
  obtain ⟨ops, root⟩ := fr
  obtain ⟨vpc, v5, vroot, -, vops, vr, vf⟩ := hv
  have hlp : LayPre (N.toNat % 2 ^ 31) root v :=
    ⟨vpc, v5, Nat.mod_lt _ (by norm_num), by rw [vf.get (by so) (by so)]; exact uidx, vroot⟩
  have hinv' : Inv v := hstab t v hinv ((uf.trans vf).mono (fun A _ h => h))
    ((ur.trans vr).mono (by decide))
  refine TBSim.bind (hlay _ root v hlp hinv') (fun r w hw => ?_)
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
      (fun o => o.map W9.T3M.sigB) (fun o t ht => ?_)
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
def cSetupRegs : RegFile :=
  ((RegFile.init.set .x28 (.c (BitVec.ofNat 64 (SIG + 2192)))).set .x29 (.c (BitVec.ofNat 64 (SIG + 2032)))).set
    .x30 (.c (BitVec.ofNat 64 (SIG + 5616)))
def cSetup : PRes := ⟨⟨cSetupRegs, [], []⟩, pcOf 20736, false, 6, 6, [], none⟩
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
theorem run_cSetup : run tailLook [20736] 20730 [] = some cSetup := optBeq_eq (by decide +kernel)
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
  x29 : t.getReg .x29 = BitVec.ofNat 64 (SIG + 2032 + 16 * k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)
  done : ∀ j < 2 * k, t.getMem (BitVec.ofNat 64 (SIG + 2032 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * j))
  frame : Frame s0 t (fun A => SIG + 2032 ≤ A ∧ A < SIG + 2032 + 16 * k)
theorem cIter_mem {s0 t : MachineState} {k : Nat} (hk : k < 214) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (A : Nat) (hA : A < 2 ^ 64) :
    (r.toState t).getMem (BitVec.ofNat 64 A) =
      if A = SIG + 2032 + 16 * k + 8 then s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * k + 8))
      else if A = SIG + 2032 + 16 * k then s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * k))
      else t.getMem (BitVec.ofNat 64 A) := by
  rw [PRes.toState_getMem', hmem, cLoopMem_get t _ _ A (by so) hA h.x28 h.x29]
  rw [h.frame.get (by so) (by so), h.frame.get (by so) (by so)]
theorem cIter_inv {s0 t : MachineState} {k : Nat} (hk : k < 214) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (u : MachineState) (hu : u = r.toState t)
    (hpc : u.pc = pcOf 20736) (h28 : u.getReg .x28 = BitVec.ofNat 64 (SIG + 2192 + 16 * (k + 1)))
    (h29 : u.getReg .x29 = BitVec.ofNat 64 (SIG + 2032 + 16 * (k + 1)))
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
theorem compactGood (im : Image) : CompactGood im := by
  intro hnew hhooks s hpc
  have hlt := tailLook_ok hnew
  have hlh := hookLook_ok hhooks
  obtain ⟨s1, -⟩ := run_sound hlh run_cHook s hpc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u1 := cHook.toState s with hu1
  have u1pc : u1.pc = pcOf 20730 := PRes.toState_pc' _ _ rfl
  have u1mem : ∀ a, u1.getMem a = s.getMem a := fun a => rfl
  obtain ⟨s2, -⟩ := run_sound hlt run_cSetup u1 u1pc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u2 := cSetup.toState u1 with hu2
  have h0 : CInv s 0 u2 := by
    refine ⟨PRes.toState_pc' _ _ rfl, ?_, ?_, ?_, fun j hj => by so, fun A _ _ => rfl⟩
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
  obtain ⟨t, st, ht⟩ := cLoop hlt h0 213 le_rfl
  obtain ⟨s3, -⟩ := run_sound hlt run_cExit t ht.pc
    (cLoopObl_holds t _ _ (by so) (by so) (by so)
      (by so) ht.x28 ht.x29)
    (by
      intro b hb
      simp only [cExit, List.mem_singleton] at hb
      subst hb
      exact cBr_holds t _ false (by so) ht.x28 ht.x30 (by simp))
  refine ⟨cExit.toState t, ((s1.trans s2).trans (st.trans s3)).of_eq (by simp [cHook, cSetup, cExit, compactK])
    (by simp [cHook, cSetup, cExit, compactK]), PRes.toState_pc' _ _ rfl, ?_, ?_, fun k hk => ?_, fun A hA hn => ?_⟩
  · rw [PRes.toState_getReg']; rfl
  · rw [PRes.toState_getReg']; rfl
  · rw [cIter_mem (by so) ht cExit rfl _ (by so)]
    by_cases hk2 : k < 2 * 213
    · rw [if_neg (by so), if_neg (by so)]; exact ht.done k hk2
    · by_cases hke : k = 2 * 213
      · subst hke; rw [if_neg (by so), if_pos (by so)]
      · have : k = 2 * 213 + 1 := by so
        subst this; rw [if_pos (by so)]
  · rw [cIter_mem (by so) ht cExit rfl A hA, if_neg (by so), if_neg (by so),
      ht.frame.get hA (by so)]
end ClaudeWCT.W9.Machine.Sign
end

section




namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
theorem signMain : SignMain := signMain_of searchGood ftsGood compactGood
theorem sign_refines_w (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop)
    (hcode : SignCodeAt (imgs .sign)) (hU : Unchanged imgs Inv) : SignRefinesW imgs :=
  (signMain imgs Inv hcode hU).1
theorem sign_terminates_w (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop)
    (hcode : SignCodeAt (imgs .sign)) (hU : Unchanged imgs Inv) : SignTerminatesW imgs :=
  (signMain imgs Inv hcode hU).2
theorem newCodeAt_of_drop {im : Image} (h : im.code.drop 11003 = signNew) : NewCodeAt im := by
  rw [NewCodeAt, h]
end ClaudeWCT.W9.Machine.Sign
end
