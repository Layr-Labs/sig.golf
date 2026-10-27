import SigGolfCandidate.Merge076
import SigGolfCandidate.Merge078

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutBlock ====
section

/-! # Pairing stage 1: the leaf / digest layout block (expand words 48100 .. 49225)

Entered by `43953: jal 48100` (after `43472..43476`), it copies the staged rho / digest counter (32 bytes at 23008) to
the witness tail at 26112, clears `[23008, 26112)` (388 words), then fills the four leaf buffers: 180 chunks (T51; #938 had 183)
`lui a0; addi a0,S; ld t1,0(a0); sd t1,X(a1); ld t1,8(a0); sd t1,X+8(a1)`, each group preceded by `li a1,D`
(D = 23008 / 23744 / 24480 / 25232), and returns through the straight tail `cRet` (49207 .. 49225: #938's
items 180..182 without their stores, then `jal 43500`). Sources `S` (chain values in the final paired
layout) lie below 23008. -/

namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
def chunkRes (S X p : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x6 (E.ld (.c (BitVec.ofNat 64 (S + 8))))).set .x10 (.c (BitVec.ofNat 64 S)),
    [(⟨some (.reg .x11), BitVec.ofNat 64 (X + 8)⟩, E.ld (.c (BitVec.ofNat 64 (S + 8)))),
     (⟨some (.reg .x11), BitVec.ofNat 64 X⟩, E.ld (.c (BitVec.ofNat 64 S)))],
    [.valid ⟨some (.reg .x11), BitVec.ofNat 64 (X + 8)⟩ 8, .ne ⟨none, BitVec.ofNat 64 (S + 8)⟩
      ⟨some (.reg .x11), BitVec.ofNat 64 X⟩, .valid ⟨some (.reg .x11), BitVec.ofNat 64 X⟩ 8]⟩,
    .c (pcOf (p + 6)), .endOfCode, 6, 6⟩
theorem run_chunk (k : Nat) (hk : k < 180) :
    symRun cfgC (lbCodes.getD k []) (pcOf (pcK k)) 40 = some (chunkRes (sK k) (xK k) (pcK k)) := by
  interval_cases k <;> kernel_rfl
def headRes (D p : Nat) : Result := ⟨⟨RegFile.init.set .x11 (.c (BitVec.ofNat 64 D)), [], []⟩, .c (pcOf (p + 2)),
  .endOfCode, 2, 2⟩
theorem run_head (g : Nat) (hg : g < 4) :
    symRun cfgC (lbHeadCodes.getD g []) (pcOf (lbHeadPc.getD g 0)) 40 =
      some (headRes ([23008, 23744, 24480, 25232].getD g 0) (lbHeadPc.getD g 0)) := by
  interval_cases g <;> kernel_rfl
sym_block RTop := symRun cfgC cTop (pcOf 48100) 40
sym_block RClr0 := symRun cfgC cClr0 (pcOf 48112) 40
sym_block RClrL := symRun cfgC cClrL (pcOf 48116) 40
sym_block RRet := symRun cfgC cRet (pcOf 49207) 40

theorem slot_mono : ∀ k j, k < j → j < 180 → slotK k + 16 ≤ slotK j := by
  intro k j hkj hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hadj := tab_facts.2.2.2.2.2.1 j (by omega)
    by_cases h : k = j
    · subst h; exact hadj
    · have := ih (by omega) (by omega); omega
def hitVal (M : Nat → Word) (j A : Nat) : Word :=
  match (List.range j).find? (fun k => decide (slotK k ≤ A ∧ A < slotK k + 16)) with
  | some k => M (sK k + (A - slotK k))
  | none => 0
/-- Memory after the tail copy, the clear and the first `j` leaf-slot items. -/
def itMem (M : Nat → Word) (j A : Nat) : Word :=
  if 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0 then M (A - 3104)
  else if 23008 ≤ A ∧ A < 26112 ∧ A % 8 = 0 then hitVal M j A
  else M A
/-- The memory after the whole layout block. -/
def lbMem (M : Nat → Word) (A : Nat) : Word := itMem M 180 A
theorem hitVal_succ (M : Nat → Word) (j A : Nat) (hj : j < 180) :
    hitVal M (j + 1) A = if slotK j ≤ A ∧ A < slotK j + 16 then M (sK j + (A - slotK j)) else hitVal M j A := by
  unfold hitVal
  rw [List.range_succ, List.find?_append]
  by_cases hA : slotK j ≤ A ∧ A < slotK j + 16
  · have hnone : (List.range j).find? (fun k => decide (slotK k ≤ A ∧ A < slotK k + 16)) = none := by
      rw [List.find?_eq_none]
      intro k hk
      have := slot_mono k j (List.mem_range.mp hk) hj
      simp only [decide_eq_true_eq]; omega
    rw [hnone, if_pos hA]
    simp [hA]
  · rw [if_neg hA]
    cases h : (List.range j).find? (fun k => decide (slotK k ≤ A ∧ A < slotK k + 16)) with
    | some k => rfl
    | none => simp [hA]
theorem chunk_regs (S X p : Nat) (u : MachineState) : RegsExcept u ((chunkRes S X p).toState u) [.x6, .x10] := by
  intro r hr; simp at hr; cases r <;> simp_all [chunkRes, rv_simp] <;> rfl
def topM (M : Nat → Word) (A : Nat) : Word :=
  if 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0 then M (A - 3104) else M A
def clrM (M : Nat → Word) (i A : Nat) : Word :=
  if 23008 ≤ A ∧ A < 23008 + 8 * i ∧ A % 8 = 0 then 0 else topM M A
theorem itMem_zero (M : Nat → Word) (A : Nat) : clrM M 388 A = itMem M 0 A := by
  unfold clrM itMem topM hitVal
  simp only [List.range_zero, List.find?_nil]
  split_ifs <;> first | rfl | omega
def itemsLen (j : Nat) : Nat := ((List.range j).map itemLen).sum
theorem itemsLen_succ (j : Nat) : itemsLen (j + 1) = itemsLen j + itemLen j := by
  unfold itemsLen; rw [List.range_succ, List.map_append, List.sum_append]; simp
theorem itemsLen_all : itemsLen 180 = 1088 := by decide
section
variable {im : Image} (hc : Code im)
include hc
theorem item_spec (k : Nat) (hk : k < 180) (M : Nat → Word) (s : MachineState) (hpc : s.pc = pcOf (itemPc k))
    (h11 : hdK k = false → s.getReg .x11 = BitVec.ofNat 64 (dK k))
    (hm : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = itMem M k A) :
    ∃ t, Steps im s (itemLen k) (itemLen k) t ∧ t.pc = pcOf (pcK k + 6) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dK k) ∧ RegsExcept s t [.x6, .x10, .x11] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = itMem M (k + 1) A := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨hS8, hS, hX8, hX, hD8, hD⟩ := tab_facts.2.2.2.2.2.2.2.2 k hk
  have hsl := slot_mono 0 k
  have hsl0 := tab_facts.2.2.2.2.2.2.1
  have hslE : slotK k + 16 ≤ 26112 := by
    by_cases h : k = 179
    · subst h; exact tab_facts.2.2.2.2.2.2.2.1
    · have := slot_mono k 179 (by omega) (by omega); have := tab_facts.2.2.2.2.2.2.2.1; omega
  -- reach the chunk with x11 = dK k
  obtain ⟨u, su, pu, u11, ru, fu, hlen⟩ : ∃ u, Steps im s (itemLen k - 6) (itemLen k - 6) u ∧ u.pc = pcOf (pcK k) ∧
      u.getReg .x11 = BitVec.ofNat 64 (dK k) ∧ RegsExcept s u [.x11] ∧ Frame s u (fun _ => False) ∧
      itemLen k = (itemLen k - 6) + 6 := by
    cases hh : hdK k
    · refine ⟨s, by simpa [itemLen, hh] using Steps.refl s, by rw [hpc]; simp [itemPc, hh], h11 hh,
        RegsExcept.refl _ _, Frame.refl _ _, by simp [itemLen, hh]⟩
    · have hg : grpK k < 4 := by unfold grpK; split_ifs <;> omega
      have hpcg := tab_facts.2.2.2.1 k hk hh
      have hD : [23008, 23744, 24480, 25232].getD (grpK k) 0 = dK k := by
        unfold hdK at hh; simp only [Bool.or_eq_true, beq_iff_eq] at hh
        rcases hh with ((h | h) | h) | h <;> subst h <;> decide
      have hrun := run_head (grpK k) hg
      have h2 : 2 ≤ pcK k := by
        unfold hdK at hh; simp only [Bool.or_eq_true, beq_iff_eq] at hh
        rcases hh with ((h | h) | h) | h <;> subst h <;> decide
      refine ⟨_, (symRun_sound hrun (hc.head _ hg) s (by rw [hpc, hpcg]; simp [itemPc, hh])
        (by simp [headRes, rv_simp])).of_eq (by simp [itemLen, hh, headRes]) (by simp [itemLen, hh, headRes]),
        ?_, ?_, ?_, ?_, by simp [itemLen, hh]⟩
      · simp only [Result.toState_pc, headRes, E.eval, hpcg]
        rw [show pcK k - 2 + 2 = pcK k by omega]
      · simp only [Result.toState_getReg, headRes, rv_simp, hD]; rfl
      · intro r hr; simp at hr; cases r <;> simp_all [headRes, rv_simp] <;> rfl
      · intro A _ _; rfl
  have hdk0 : 23008 ≤ slotK k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact hsl0
    · have := slot_mono 0 k h hk; omega
  have hmu : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = itMem M k A := fun A hA => by
    rw [fu.get hA (by simp), hm A hA]
  have srcM : ∀ x, x < 16 → u.getMem (BitVec.ofNat 64 (sK k + x)) = M (sK k + x) := fun x hx => by
    rw [hmu _ (by omega)]; unfold itMem; rw [if_neg (by omega), if_neg (by omega)]
  have hobl : Oblig.all u (chunkRes (sK k) (xK k) (pcK k)).st.obl := by
    simp [chunkRes, rv_simp, accessValid_iff, u11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; unfold slotK at *; omega
  have sc := symRun_sound (run_chunk k hk) (hc.chunk k hk) u pu hobl
  refine ⟨_, (su.trans sc).of_eq (by show (itemLen k - 6) + 6 = itemLen k; omega)
    (by show (itemLen k - 6) + 6 = itemLen k; omega), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, chunkRes, E.eval]
  · simp only [Result.toState_getReg, chunkRes, rv_simp]; rw [← u11]; rfl
  · exact (ru.trans (chunk_regs _ _ _ u)).mono (by simp)
  · intro A hA
    have k0 := ofNat_inj hA (show slotK k < 2 ^ 64 by omega)
    have k8 := ofNat_inj hA (show slotK k + 8 < 2 ^ 64 by omega)
    have e8 : BitVec.ofNat 64 (dK k + (xK k + 8)) = BitVec.ofNat 64 (slotK k + 8) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; unfold slotK at *; omega
    have e0 : BitVec.ofNat 64 (dK k + xK k) = BitVec.ofNat 64 (slotK k) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; unfold slotK at *; omega
    simp only [Result.toState_getMem, chunkRes, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, u11,
      ofNat_add_ofNat, e8, e0, k0, k8]
    rw [srcM 8 (by omega), show sK k = sK k + 0 from rfl, srcM 0 (by omega), hmu A hA]
    unfold itMem
    rw [hitVal_succ M k A hk]
    by_cases a8 : A = slotK k + 8
    · subst a8; rw [if_pos rfl, if_neg (by omega), if_pos ⟨by omega, by omega, by unfold slotK; omega⟩,
        if_pos ⟨by omega, by omega⟩]
      simp
    rw [if_neg a8]
    by_cases a0 : A = slotK k
    · subst a0; rw [if_pos rfl, if_neg (by omega), if_pos ⟨by omega, by omega, by unfold slotK; omega⟩,
        if_pos ⟨le_rfl, by omega⟩]
      simp
    rw [if_neg a0]
    by_cases ht : 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0
    · rw [if_pos ht, if_pos ht]
    rw [if_neg ht, if_neg ht]
    by_cases hb : 23008 ≤ A ∧ A < 26112 ∧ A % 8 = 0
    · rw [if_pos hb, if_pos hb, if_neg (by unfold slotK at *; omega)]
    · rw [if_neg hb, if_neg hb]

set_option maxRecDepth 200000 in
theorem top_spec (s : MachineState) (hpc : s.pc = pcOf 48100) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 48112 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = topM (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  refine ⟨_, symRun_sound RTop hc.top s hpc (by simp [RTop.res, rv_simp]), ?_, ?_⟩
  · simp only [Result.toState_pc, RTop.res, E.eval]
  · intro A hA
    have key : ∀ c : Nat, c < 2 ^ 64 → (BitVec.ofNat 64 A = BitVec.ofNat 64 c ↔ A = c) := fun c hc => ofNat_inj hA hc
    simp only [Result.toState_getMem, RTop.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval,
      key 26136 (by norm_num), key 26128 (by norm_num), key 26120 (by norm_num), key 26112 (by norm_num)]
    unfold topM
    by_cases h : 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0
    · rw [if_pos h]
      rcases (show A = 26112 ∨ A = 26120 ∨ A = 26128 ∨ A = 26136 by omega) with rfl | rfl | rfl | rfl <;> rfl
    · rw [if_neg h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem clr_iter (s : MachineState) (hpc : s.pc = pcOf 48116) (i : Nat) (hi : i < 388)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * i)) (h11 : s.getReg .x11 = BitVec.ofNat 64 26112) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i + 1 < 388 then pcOf 48116 else pcOf 48119) ∧
      t.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * (i + 1)) ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
      RegsExcept s t [.x10] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = 23008 + 8 * i then 0 else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RClrL hc.clrL s hpc (by
    simp [RClrL.res, rv_simp, accessValid_iff, h10, BitVec.toNat_ofNat]; omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RClrL.res, E.eval, CmpOp.eval, BinOp.eval, h10, h11, ofNat_add_ofNat]
    have he : BitVec.ult (BitVec.ofNat 64 (23008 + 8 * i + 8)) (BitVec.ofNat 64 26112) = decide (i + 1 < 388) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [decide_eq_decide]; omega
    rw [he]
    by_cases h : i + 1 < 388 <;> simp [h]
  · rw [show 23008 + 8 * (i + 1) = 23008 + 8 * i + 8 by ring]; simp [RClrL.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RClrL.res, rv_simp, h11]
  · intro r hr; simp at hr; cases r <;> simp_all [RClrL.res, rv_simp] <;> rfl
  · intro A hA
    have key := ofNat_inj hA (show 23008 + 8 * i < 2 ^ 64 by omega)
    simp only [Result.toState_getMem, RClrL.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h10,
      BitVec.add_zero, key]
    rfl
theorem clr_loop (s : MachineState) (hpc : s.pc = pcOf 48116) (M : Nat → Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 23008) (h11 : s.getReg .x11 = BitVec.ofNat 64 26112)
    (hm : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = topM M A) :
    ∀ i, 0 < i → i ≤ 388 → ∃ t, Steps im s (3 * i) (3 * i) t ∧
      t.pc = (if i < 388 then pcOf 48116 else pcOf 48119) ∧
      t.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * i) ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
      RegsExcept s t [.x10] ∧ ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = clrM M i A := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hi
    obtain ⟨t, st, pt, t10, t11, rt, mt⟩ : ∃ t, Steps im s (3 * i) (3 * i) t ∧ t.pc = pcOf 48116 ∧
        t.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * i) ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
        RegsExcept s t [.x10] ∧ ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = clrM M i A := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        exact ⟨s, Steps.refl s, hpc, by simpa using h10, h11, RegsExcept.refl _ _, fun A hA => by
          rw [hm A hA]; unfold clrM; rw [if_neg (by omega)]⟩
      · obtain ⟨t, st, pt, t10, t11, rt, mt⟩ := ih h0 (by omega)
        exact ⟨t, st, by rw [pt, if_pos (by omega)], t10, t11, rt, mt⟩
    obtain ⟨u, su, pu, u10, u11, ru, mu⟩ := clr_iter hc t pt i (by omega) t10 t11
    refine ⟨u, (st.trans su).of_eq (by omega) (by omega), pu,
      u10, u11, (rt.trans ru).mono (by simp), fun A hA => ?_⟩
    rw [mu A hA, mt A hA]
    unfold clrM
    by_cases ha : A = 23008 + 8 * i
    · subst ha; rw [if_pos rfl, if_pos (by omega)]
    · rw [if_neg ha]
      by_cases h1 : 23008 ≤ A ∧ A < 23008 + 8 * i ∧ A % 8 = 0
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
theorem items_loop (M : Nat → Word) (s : MachineState) (hpc : s.pc = pcOf 48119)
    (hm : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = itMem M 0 A) :
    ∀ j, j ≤ 180 → ∃ t, Steps im s (itemsLen j) (itemsLen j) t ∧
      t.pc = pcOf (if j < 180 then itemPc j else 49207) ∧
      (0 < j → j < 180 → hdK j = false → t.getReg .x11 = BitVec.ofNat 64 (dK j)) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = itMem M j A := by
  intro j
  induction j with
  | zero => intro _; exact ⟨s, Steps.refl s, by rw [hpc, if_pos (by omega)]; rfl,
      fun h => absurd h (by omega), hm⟩
  | succ j ih =>
    intro hj
    obtain ⟨t, st, pt, t11, mt⟩ := ih (by omega)
    rw [if_pos (by omega)] at pt
    obtain ⟨u, su, pu, u11, ru, mu⟩ := item_spec hc j (by omega) M t pt
      (fun hh => t11 (tab_facts.2.2.2.2.1 j (by omega) hh).1 (by omega) hh) mt
    refine ⟨u, (st.trans su).of_eq (itemsLen_succ j).symm (itemsLen_succ j).symm, ?_, ?_, mu⟩
    · by_cases hj' : j + 1 < 180
      · rcases (tab_facts.1 j (by omega)) with h | h
        · rw [pu, h, if_pos hj']
        · omega
      · have : j = 179 := by omega
        subst this; rw [pu, if_neg (by omega), tab_facts.2.1]
    · intro _ hj' hh
      rw [u11, (tab_facts.2.2.2.2.1 (j + 1) hj' hh).2, Nat.add_sub_cancel]
/-- Pairing stage 1: the whole layout block, 48100 -> 43500 in 2287 steps. -/
theorem layout_spec (s : MachineState) (hpc : s.pc = pcOf 48100) :
    ∃ t, Steps im s 2287 2287 t ∧ t.pc = pcOf 43500 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = lbMem (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨t1, s1, p1, m1⟩ := top_spec hc s hpc
  obtain ⟨t2, s2, p2, x10, x11, f2⟩ : ∃ t, Steps im t1 4 4 t ∧ t.pc = pcOf 48116 ∧
      t.getReg .x10 = BitVec.ofNat 64 23008 ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = t1.getMem (BitVec.ofNat 64 A) := by
    refine ⟨_, symRun_sound RClr0 hc.clr0 t1 p1 (by simp [RClr0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, RClr0.res, E.eval]
    · simp [RClr0.res, rv_simp]
    · simp [RClr0.res, rv_simp]
    · intro A _; simp [RClr0.res, rv_simp]
  obtain ⟨t3, s3, p3, _, _, _, m3⟩ := clr_loop hc t2 p2 _ x10 x11 (fun A hA => by rw [f2 A hA, m1 A hA]) 388
    (by omega) le_rfl
  rw [if_neg (by omega)] at p3
  obtain ⟨t4, s4, p4, _, m4⟩ := items_loop hc _ t3 p3 (fun A hA => by rw [m3 A hA, itMem_zero]) 180 le_rfl
  rw [if_neg (by omega)] at p4
  refine ⟨_, ((((s1.trans s2).trans s3).trans s4).trans (symRun_sound RRet hc.ret t4 p4
    (by simp [RRet.res, rv_simp]))).of_eq (by rw [itemsLen_all]; simp [RRet.res]) (by rw [itemsLen_all]; simp [RRet.res]),
    ?_, fun A hA => ?_⟩
  · simp [Result.toState_pc, RRet.res, E.eval]
  · rw [show ((RRet.res).toState t4).getMem (BitVec.ofNat 64 A) = t4.getMem (BitVec.ofNat 64 A) by
      simp [RRet.res, rv_simp], m4 A hA]
    rfl
end
end ClaudeWCT.W9.Machine.Expand.Layout
end
