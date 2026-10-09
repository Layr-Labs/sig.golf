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
    (COEF ≤ A ∧ A < COEF + 1632)
theorem GlobSt.frame {sk N : BitVec 256} {s t : MachineState} {c : Nat} {l : List Reg} (hc : c < 9)
    (h : GlobSt sk N s) (hr : RegsExcept s t l) (hl : .x5 ∉ l ∧ .x22 ∉ l) (hf : Frame s t (coordW c)) :
    GlobSt sk N t := by
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  have nw : ∀ A, (NBUF ≤ A ∧ A < NBUF + 32 ∨ TBL ≤ A ∧ A < TBL + 65536 ∨ A = PRIVW ∨ A = PRIVW + 8 ∨
      A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ ScrZero A) → ¬ coordW c A := by
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
    rw [hf.get hA' (nw _ (by simp [hA]))]; exact h.zero A hA
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
  fk c + (1 + (14 + (51 * coefStepC + (128 * loopStepC + (126 * treeC + (12 + 7 * 13))))))
theorem coordC_le (c : Nat) :
    coordC c ≤ 13 + (1 + (14 + (51 * coefStepC + (128 * loopStepC + (126 * treeC + (12 + 7 * 13)))))) := by
  unfold coordC fk; split_ifs <;> omega
theorem field_lt563 {N : BitVec 256} (hadm : WCT9.admissible N = true) {c : Nat} (hc : c < 9) :
    N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10 < 563 :=
  ((WCT9.admissible_iff N).1 hadm).2 ⟨c, hc⟩
theorem pcI_seven (c : Nat) (hc : c < 9) : pcI c 7 = if c < 8 then cbase (c + 1) else 20715 := by
  interval_cases c <;> decide
def coefRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x18, .x29]
def coefW (A : Nat) : Prop := A = PRIVW + 16 ∨ A = PRIVW + 24 ∨ (COEF ≤ A ∧ A < COEF + 1632)
structure CoefInv (im : Image) (c index : Nat) (s0 : MachineState) (j : Nat) (acc : List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (if j < 51 then ecI c else leafI c)
  run : j < 51 → fetch im t = some (.base .ECALL) ∧ t.getReg .x7 = BitVec.ofNat 64 j ∧
    t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
    t.getReg .x12 = BitVec.ofNat 64 (COEF + 32 * j) ∧
    t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)
  done : 51 ≤ j → t.getReg .x18 = BitVec.ofNat 64 0
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
    (j : Nat) (hj : j < 51) (acc : List Digest) (t : MachineState) (h : CoefInv im c index s0 j acc t) :
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
  by_cases hj1 : j + 1 < 51
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
theorem coord_unit (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) {N : BitVec 256}
    (hadm : WCT9.admissible N = true) {s : MachineState} (hpc : s.pc = pcOf (cbase c)) (hg : GlobSt sk N s)
    (state : List WCT9.Opening × List (Digest × Digest)) :
    TBSim im sk s (coordC c) (WCT9.openingStep (WCT9.digestIndex N) N state ⟨c, hc⟩) (fun st t =>
      t.pc = pcOf (pcI c 7) ∧ GlobSt sk N t ∧
        (∃ op pr, st = (state.1 ++ [op], state.2 ++ [pr]) ∧ OpeningAt t c op ∧ DigAt t (FORW + forOff c) pr.1 ∧
          DigAt t (FORW + forOff c + 16) pr.2) ∧
        RegsExcept s t ftsRegs ∧ Frame s t (coordW c)) := by
  have hidx : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
  have hf := field_lt563 hadm hc
  have hsel128 : N.toNat / 2 ^ WCT9.childBase c % 128 < 128 := Nat.mod_lt _ (by norm_num)
  obtain ⟨t1, s1, p1, x24, x28, r1, f1⟩ := step_F hcode hc s hpc hg.nbuf
  have ht1 : TableAt t1 := fun k hk => by rw [f1.get (by ao) id]; exact hg.table k hk
  obtain ⟨t2, s2, p2, x25, r2, f2⟩ := step_lwu hcode hc t1 p1 (by omega) x28 ht1
  have r12 : RegsExcept s t2 [.x6, .x24, .x25, .x28] := (r1.trans r2).mono (by simp)
  have g2 : ∀ A, A < 2 ^ 64 → t2.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [f2.get hA id, f1.get hA id]
  have hz2 : ∀ A, ScrZero A → t2.getMem (BitVec.ofNat 64 A) = 0 := fun A hA => by
    rw [g2 A (by unfold ScrZero at hA; aoh)]; exact hg.zero A hA
  have h22 : t2.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex N) := by rw [r12.get (by simp)]; exact hg.x22
  obtain ⟨t3, s3, e3, p3, x7, x10, x11, x12, m16, m24, r3, f3⟩ := step_Z hcode hc t2 p2 h22
  have hc0 : CoefInv im c (WCT9.digestIndex N) t2 0 [] t3 :=
    ⟨by rw [if_pos (by norm_num)]; exact p3, fun _ => ⟨e3, x7, x10, x11, x12, m24⟩, fun h => absurd h (by omega),
      m16, rfl, fun k hk => absurd hk (by omega), r3.mono (by simp [coefRegs]),
      f3.mono (fun A _ hA => by unfold coefW; rcases hA with h | h <;> simp [h])⟩
  have hrank : WCT9.rank N ⟨c, hc⟩ = ⟨N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10, hf⟩ :=
    Fin.ext (show WCT9.field N ⟨c, hc⟩ % 563 = _ from Nat.mod_eq_of_lt hf)
  have hword : ∀ i : Fin 6, pkAt (N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10) / 8 ^ i.val % 8 =
      WCT9.wordDigit (WCT9.rank N ⟨c, hc⟩) i := fun i => by rw [hrank]; exact pkAt_digit _ hf i
  have hw64 : pkAt (N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10) < 2 ^ 64 := by
    have := pkAt_lt (N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10); omega
  unfold WCT9.openingStep
  dsimp only
  simp only [buildCoordinateF_factor, ftsCoefs_eq, bind_assoc, pure_bind]
  refine (TBSim.steps ((s1.trans s2).trans s3)
    (TBSim.bind (W₂ := 128 * loopStepC + (126 * treeC + (12 + 7 * 13)))
      (TBSim.foldlM_range' 0 51 (coefStep (WCT9.digestIndex N) c) [] (CoefInv im c (WCT9.digestIndex N) t2)
        coefStepC (fun j hj acc t ht => coef_step hcode hc hidx (by rw [r12.get (by simp)]; exact hg.x5) h22
          (by rw [g2 _ (by ao)]; exact hg.p0) (by rw [g2 _ (by ao)]; exact hg.p8)
          (by rw [g2 _ (by ao)]; exact hg.p32) (by rw [g2 _ (by ao)]; exact hg.p40)
          (hz2 _ (by simp [ScrZero])) (hz2 _ (by simp [ScrZero])) j hj acc t ht) hc0)
      (fun coefs t3' h3 => ?_))).mono (by unfold coordC; omega) (fun _ _ h => h)
  have g3 : ∀ A, A < 2 ^ 64 → ¬ coefW A → t3'.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => by rw [h3.frame.get hA hn, g2 A hA]
  have nwz : ∀ A, ScrZero A → ¬ coefW A := by
    intro A hA hw; unfold ScrZero at hA; unfold coefW at hw; simp only [PRIVW, CHAINW, NODEW, COEF] at *; omega
  have hz : ∀ A, ScrZero A → t3'.getMem (BitVec.ofNat 64 A) = 0 := fun A hA => by
    rw [g3 A (by unfold ScrZero at hA; aoh) (nwz A hA)]
    exact hg.zero A hA
  have r13 : RegsExcept s t3' ([.x6, .x24, .x25, .x28] ++ coefRegs) := r12.trans h3.regs
  have nwp : ∀ A, (A = PRIVW ∨ A = PRIVW + 8 ∨ A = PRIVW + 32 ∨ A = PRIVW + 40) → ¬ coefW A := by
    intro A hA hw; unfold coefW at hw; simp only [PRIVW, COEF] at *; omega
  have hb3 : BodySt sk 0 (WCT9.digestIndex N) (N.toNat / 2 ^ WCT9.childBase c % 128)
      (pkAt (N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10)) t3' :=
    ⟨by rw [r13.get (by simp [coefRegs])]; exact hg.x5, h3.done (le_refl _),
      by rw [r13.get (by simp [coefRegs])]; exact hg.x22,
      by rw [h3.regs.get (by simp [coefRegs]), r2.get (by simp)]; exact x24,
      by rw [h3.regs.get (by simp [coefRegs])]; exact x25,
      by rw [g3 _ (by ao) (nwp _ (by simp))]; exact hg.p0, by rw [g3 _ (by ao) (nwp _ (by simp))]; exact hg.p8,
      by rw [g3 _ (by ao) (nwp _ (by simp))]; exact hg.p32, by rw [g3 _ (by ao) (nwp _ (by simp))]; exact hg.p40,
      hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]),
      hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero])⟩
  have hp3 : t3'.pc = pcOf (leafI c) := by have := h3.pc; rwa [if_neg (by norm_num)] at this
  have hcf : CoefAt t3' coefs := fun k hk => h3.coef k (by omega)
  have hlen : coefs.length = 102 := h3.len
  refine TBSim.bind (W₂ := 126 * treeC + (12 + 7 * 13))
    (child_loop (word := WCT9.rank N ⟨c, hc⟩) hcode hc hsel128 hidx hw64 hword hlen hcf
      (LoopInv.init hp3 hb3)) (fun rows t4 h4 => ?_)
  have h4pc : t4.pc = pcOf (nodeI c) := by have := h4.pc; rwa [if_neg (by norm_num)] at this
  have h4b := h4.body
  rw [if_neg (by norm_num)] at h4b
  have g4 : ∀ A, A < 2 ^ 64 → ¬ loopW c A → t4.getMem (BitVec.ofNat 64 A) = t3'.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => h4.frame.get hA hn
  have h0 : TreeInv c (WCT9.digestIndex N) t4 0 ((List.replicate 128 (0 : Digest) ++ rows.1).toArray) t4 :=
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
  have h24 : t6.getReg .x24 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase c % 128) := by
    rw [r6.get (by simp), h5.regs.get (by simp [treeRegs])]; exact h4b.x24
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  have hheap6 : ∀ m, 2 ≤ m → m < 256 → DigAt t6 (HEAPW + 16 * m) (heap.getD m 0) := fun m h1 h2 =>
    (h5.heap m (by omega) h2).frame f6 (by ao) (by intro h; rcases h with h | h | h | h <;> aoh)
      (by intro h; rcases h with h | h | h | h <;> aoh)
  obtain ⟨t7, s7, p7, hpath, r7, f7⟩ := path_copies hcode hc hsel128 7 le_rfl t6 (by rw [p6]) h24 hheap6
  have hregs : RegsExcept s t7 ftsRegs :=
    ((((r13.trans h4.regs).trans h5.regs).trans r6).trans r7).mono (by simp [ftsRegs, bodyRegs, treeRegs, coefRegs])
  have hframe : Frame s t7 (coordW c) := by
    refine (((((f1.trans f2).trans h3.frame).trans h4.frame).trans h5.frame).trans f6 |>.trans f7).mono
      (fun A _ hA => ?_)
    unfold coordW
    rcases hA with (((((hA | hA) | hA) | hA) | hA) | hA) | hA
    · exact hA.elim
    · exact hA.elim
    · unfold coefW at hA
      rcases hA with h | h | h
      · left; left; unfold bodyW; left; subst h; constructor <;> ao
      · left; left; unfold bodyW; left; subst h; constructor <;> ao
      · right; right; right; right; exact h
    · left; exact hA
    · right; left; exact hA
    · right; right; left; rcases hA with h | h | h | h <;> (subst h; constructor <;> omega)
    · right; right; right; left; exact hA
  have hval : ∀ i : Fin 6, DigAt t7 (SIG + 16 + 208 * c + 16 * i.val) (rows.2.getD i.val 0) := fun i => by
    obtain ⟨-, hd⟩ := h4.vals hsel128
    have h1 := hd i.val i.isLt
    unfold slotV at h1
    refine ((h1.frame h5.frame (by ao) ?_ ?_).frame f6 (by ao) ?_ ?_).frame f7 (by ao) ?_ ?_ <;>
      (intro h; (try simp only [treeW, slotP] at h); have := i.isLt; aoh)
  refine TBSim.pure_steps' (s6.trans s7) ⟨p7, GlobSt.frame hc hg hregs (by simp [ftsRegs]) hframe,
    ⟨_, _, rfl, ⟨fun i => hval i, fun l => ?_⟩, ?_, ?_⟩, hregs, hframe⟩
  · have hx : N.toNat / 2 ^ WCT9.childBase c % 128 / 2 ^ l.val ^^^ 1 < 2 ^ (7 - l.val) := by
      have := pathHeap_lt _ l.val hsel128 l.isLt
      have h2 := pathIdx_eq _ hsel128 l.val l.isLt
      have : (N.toNat / 2 ^ WCT9.childBase c % 128 + 128) / 2 ^ l.val ^^^ 1 < 2 ^ (7 - l.val + 1) := by
        apply Nat.xor_lt_two_pow
        · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 7 - l.val + 1 + l.val = 8 by omega]; omega
        · exact Nat.one_lt_two_pow (by omega)
      rw [pow_succ] at this; omega
    have := hpath l.val (by omega) l.isLt
    unfold slotP at this
    show DigAt t7 (SIG + 112 + 208 * c + 16 * l.val) (((List.range 7).map fun level =>
      ((WCT9.heapLevels heap).getD level []).getD ((WCT9.child N ⟨c, hc⟩).val / 2 ^ level ^^^ 1) 0).getD l.val 0)
    have hcv : (WCT9.child N ⟨c, hc⟩).val = N.toNat / 2 ^ WCT9.childBase c % 128 := rfl
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
def coordCmax : Nat := 13 + (1 + (14 + (51 * coefStepC + (128 * loopStepC + (126 * treeC + (12 + 7 * 13))))))
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
section fts
variable {im : Image} {sk : BitVec 256}
theorem fts_step (hcode : NewCodeAt im) {N : BitVec 256} (hadm : WCT9.admissible N = true) {s0 : MachineState}
    (k : Nat) (hk : k < 9) (st : List WCT9.Opening × List (Digest × Digest)) (t : MachineState)
    (h : FtsInv sk N s0 k st t) :
    TBSim im sk t coordCmax
      ((fun st k => if h : k < 9 then WCT9.openingStep (WCT9.digestIndex N) N st ⟨k, h⟩ else pure st) st (0 + k))
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
      simp only [COEF] at hA
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
  unfold coordCmax loopStepC childC stepC hornC hornStepC coefStepC treeC ftsC; norm_num
section fts2
variable {im : Image}
theorem ftsGood (im : Image) : FtsGood im := by
  intro hcode sk N s hpre
  have hidx : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
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
  have hq : hashInput t1 = toQ (pad64 (WCT9.forestInput (WCT9.digestIndex N) st.2)) := by
    refine hashInput_forest t1 st.2 h9.len2 (by omega) x10 x11 (fun c hc => ?_) m0 m8 m16 m24
    have hfo : forOff c ≤ 288 := by unfold forOff; omega
    have hfo' : 32 ≤ forOff c := by unfold forOff; omega
    obtain ⟨-, o2, o3⟩ := h9.outs c hc
    exact ⟨o2.frame f1 (by ao) (by intro h; rcases h with h | h | h | h <;> omega)
        (by intro h; rcases h with h | h | h | h <;> omega),
      o3.frame f1 (by ao) (by intro h; rcases h with h | h | h | h <;> omega)
        (by intro h; rcases h with h | h | h | h <;> omega)⟩
  have hx5 : t1.getReg .x5 = 0 := by rw [r1.get (by simp)]; exact h9.glob.x5
  have hbl : (toQ (pad64 (WCT9.forestInput (WCT9.digestIndex N) st.2))).blocks = 5 := by
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
  let some pieces ← WCT9.signLayersBC (cacheDec cache) (WCT9.digestIndex output) 4 (.forest forest.2) | pure none
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
theorem signCW_eq : signCW = 3549928522 := by
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
  have hlp : LayPre (WCT9.digestIndex N) root v :=
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
