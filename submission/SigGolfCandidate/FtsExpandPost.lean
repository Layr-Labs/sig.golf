import SigGolfCandidate.SimCore
import SigGolfCandidate.Merge048
import SigGolfCandidate.FtsCode
import SigGolfCandidate.FtsTramp
set_option debug.skipKernelTC true
set_option linter.all false

/-! # FTS carrier grind: the expand witness post-pass (`POST`, 61050..61088)

Entered from the final HALT word (a `jal zero, POST`). For `k = 0..8` it reads the record of the coordinate with
frame base `sB k = 9768 - 848 k` (`slotA (sB k)`: witness pad address, nonce) and stores the nonce at the address,
then (S5185 FTS16) jumps at `POST + 38` to `copy2` (57168), which writes the level-2 nonce records and halts. -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M

/-- Frame base of coordinate `k` in the expand FTS pass. -/
def sB (k : Nat) : Nat := 9768 - 848 * k
def cfgP : Config := { noAlias := true }
def postBody : List (BitVec 32) := postWords.take 38

sym_block ePost := symRun cfgP postWords (pcOf POST) 40

/-- `t3n` without the (not yet imported) `rv_simp` set: the Merge047 `rv_simp` lemmas listed explicitly. -/
macro "pn" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [Result.toState_getReg, Result.toState_getMem, Result.toState_pc, Result.toState_code,
      SymState.toState_getReg, SymState.toState_getMem, SymState.toState_pc, RegFile.get, E.eval, BinOp.eval,
      UnOp.eval, CmpOp.eval, LoadKind.fromWord, StoreKind.merge, Addr.eval, memEval_cons, memEval_nil,
      BitVec.add_zero, Oblig.all, Oblig.holds, Result.obligs, Result.pc, Result.st, Result.steps, Result.cycles,
      Result.stop, SymState.regs, SymState.mem, SymState.obl, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat,
      ofNat_eq_iff, BitVec.toNat_ofNat, memAccessValid_iff, MEMORY_BYTES, ne_eq, bne_iff_ne,
      decide_eq_true_eq, ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, $ts',*])

/-- One dword store. -/
def upd (M : Word → Word) (a : Word) (v : Word) : Word → Word := fun A => if A = a then v else M A
/-- Memory after the post-pass: the nine recorded nonces stored at the recorded addresses, `k = 0` first. -/
def postMem (M : Word → Word) : Word → Word :=
  (List.range 9).foldl (fun N k => upd N (M (BitVec.ofNat 64 (slotA (sB k))))
    (M (BitVec.ofNat 64 (slotA (sB k) + 8)))) M

/-- The recorded pad addresses: 8-aligned and below the record area. -/
def AddrsOK (M : Word → Word) : Prop :=
  ∀ k < 9, (M (BitVec.ofNat 64 (slotA (sB k)))).toNat % 8 = 0 ∧
    (M (BitVec.ofNat 64 (slotA (sB k)))).toNat + 8 ≤ SCR

theorem postBody_code {im : Image} (h : CodeAt im (pcOf POST) postWords) : CodeAt im (pcOf POST) postBody := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · have : postBody.length ≤ postWords.length := by decide
    omega
  · exact (List.take_prefix _ _).trans h4

/-! ## `post_run`: windows, the straight-line iteration, and assembly -/

/-- Window of `postWords`. -/
def pw (a b : Nat) : List (BitVec 32) := (postWords.drop (a - POST)).take (b - a)

theorem code_pw {im : Image} (hc : CodeAt im (pcOf POST) postWords) (a b : Nat) (ha : POST ≤ a)
    (hb : b ≤ POST + 39) (hab : a ≤ b) : CodeAt im (pcOf a) (pw a b) := by
  have hlen : postWords.length = 39 := postWords_length
  have := codeAt_sub (a - POST) hc (seg := pw a b) (by simp [pw, hlen]; omega) (by simp [pw])
  rwa [show POST + (a - POST) = a by omega] at this

theorem postIter_words (k : Nat) (hk : k < 9) :
    pw (POST + 2 + 4 * k) (POST + 2 + 4 * k + 4) = [0xfbe83, 0x8fbf03, 0x1eeb023, 0x960f8f93] := by
  interval_cases k <;> decide +kernel

theorem postIter_code {im : Image} (hc : CodeAt im (pcOf POST) postWords) (k : Nat) (hk : k < 9) :
    CodeAt im (pcOf (POST + 2 + 4 * k)) [0xfbe83] ∧
    CodeAt im (pcOf (POST + 2 + 4 * k + 1)) [0x8fbf03] ∧
    CodeAt im (pcOf (POST + 2 + 4 * k + 2)) [0x1eeb023] ∧
    CodeAt im (pcOf (POST + 2 + 4 * k + 3)) [0x960f8f93] := by
  have h4 := code_pw hc (POST + 2 + 4 * k) (POST + 2 + 4 * k + 4) (by omega) (by omega) (by omega)
  rw [postIter_words k hk] at h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using codeAt_sub 0 h4 (seg := [0xfbe83]) (by simp) rfl
  · have := codeAt_sub 1 h4 (seg := [0x8fbf03]) (by simp) rfl
    simpa using this
  · have := codeAt_sub 2 h4 (seg := [0x1eeb023]) (by simp) rfl
    simpa using this
  · have := codeAt_sub 3 h4 (seg := [0x960f8f93]) (by simp) rfl
    simpa using this

theorem postTail_code {im : Image} (hc : CodeAt im (pcOf POST) postWords) :
    CodeAt im (pcOf (POST + 38)) [0xac0fc06f] := by
  have hd : postWords.drop 38 = [0xac0fc06f] := by decide +kernel
  have hlen : postWords.length = 39 := postWords_length
  have h := codeAt_sub 38 hc (seg := [0xac0fc06f]) (by simp [hlen]) (by rw [hd]; rfl)
  simpa using h

theorem postSext12_zero : signExtend12 (0 : BitVec 12) = 0 := by decide

theorem postSext12_decr (a : Nat) (ha : 1696 ≤ a) (ha2 : a < 2 ^ 64) :
    BitVec.ofNat 64 a + signExtend12 (0x960 : BitVec 12) = BitVec.ofNat 64 (a - 1696) := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (0x960 : BitVec 12)).toNat = 2 ^ 64 - 1696 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha2, hs, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a - 1696 < 2 ^ 64 by omega)]
  omega

theorem postHead_code {im : Image} (hc : CodeAt im (pcOf POST) postWords) :
    CodeAt im (pcOf POST) [0x7e5fb7] ∧ CodeAt im (pcOf (POST + 1)) [0xc50f8f93] := by
  have h2 := code_pw hc POST (POST + 2) (by omega) (by omega) (by omega)
  have hd : pw POST (POST + 2) = [0x7e5fb7, 0xc50f8f93] := by decide +kernel
  rw [hd] at h2
  exact ⟨by simpa using codeAt_sub 0 h2 (seg := [0x7e5fb7]) (by simp) rfl,
    by simpa using codeAt_sub 1 h2 (seg := [0xc50f8f93]) (by simp) rfl⟩

/-- `POST`'s first two words: `lui t6,0x7e5; addi t6,t6,-944`, giving `t6 = slotA (sB 0)`. -/
theorem postHead_step {im : Image} (hc : CodeAt im (pcOf POST) postWords) (s : MachineState)
    (hpc : s.pc = pcOf POST) :
    ∃ u, Steps im s 2 2 u ∧ u.pc = pcOf (POST + 2) ∧ u.getReg .x31 = BitVec.ofNat 64 (slotA (sB 0)) ∧
      RegsExcept s u [.x31] ∧ (∀ A, u.getMem A = s.getMem A) := by
  obtain ⟨c0, c1⟩ := postHead_code hc
  have step1 : Steps im s 1 1 ((s.setReg .x31 (luiVal (0x7e5 : BitVec 20))).setPC (pcOf (POST + 1))) :=
    micro_step (i := .base (.LUI .x31 (0x7e5 : BitVec 20)))
      (m := .alu .x31 .add (.imm (luiVal (0x7e5 : BitVec 20))) (.imm 0)) c0 rfl rfl hpc
      (by simp only [Micro.exec, BinOp.eval, Src.eval, hpc, pcOf_add4, add_zero])
  set s1 := (s.setReg .x31 (luiVal (0x7e5 : BitVec 20))).setPC (pcOf (POST + 1)) with hs1def
  have hx31_s1 : s1.getReg .x31 = luiVal (0x7e5 : BitVec 20) := by
    rw [hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x31 : Reg) ≠ .x0)]
  have hpc_s1 : s1.pc = pcOf (POST + 1) := rfl
  have hmem_s1 : ∀ A, s1.getMem A = s.getMem A := by
    intro A; rw [hs1def, MachineState.getMem_setPC, MachineState.getMem_setReg]
  have hlui : luiVal (0x7e5 : BitVec 20) = BitVec.ofNat 64 8278016 := by decide
  have e : s1.getReg .x31 + signExtend12 (0xC50 : BitVec 12) = BitVec.ofNat 64 (slotA (sB 0)) := by
    rw [hx31_s1, hlui, show slotA (sB 0) = 8277072 from by unfold slotA SCR sB; norm_num]
    decide
  have step2 : Steps im s1 1 1
      ((s1.setReg .x31 (s1.getReg .x31 + signExtend12 (0xC50 : BitVec 12))).setPC (pcOf (POST + 2))) :=
    micro_step (i := .base (.ADDI .x31 .x31 (0xC50 : BitVec 12)))
      (m := .alu .x31 .add (.reg .x31) (.imm (signExtend12 (0xC50 : BitVec 12)))) c1 rfl rfl hpc_s1
      (by simp only [Micro.exec, BinOp.eval, Src.eval, hpc_s1, pcOf_add4])
  refine ⟨_, step1.trans step2, rfl, by rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq
    (by decide : (Reg.x31 : Reg) ≠ .x0)]; exact e, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr), hs1def,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A
    rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hmem_s1 A

/-- One `POST` loop iteration (unconditional, unlike `copy2`'s skip-if-zero): `ld t4,0(t6); ld t5,8(t6);
sd t5,0(t4); addi t6,t6,-1696`. -/
theorem post_iter {im : Image} (hc : CodeAt im (pcOf POST) postWords) (k : Nat) (hk : k < 9)
    (s : MachineState) (hpc : s.pc = pcOf (POST + 2 + 4 * k))
    (ht6 : s.getReg .x31 = BitVec.ofNat 64 (slotA (sB k)))
    (hbnd : (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).toNat % 8 = 0 ∧
      (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).toNat + 8 ≤ SCR) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf (POST + 2 + 4 * (k + 1)) ∧
      t.getReg .x31 = BitVec.ofNat 64 (slotA (sB k) - 1696) ∧
      RegsExcept s t [.x29, .x30, .x31] ∧
      (∀ A, t.getMem A = upd s.getMem (s.getMem (BitVec.ofNat 64 (slotA (sB k))))
        (s.getMem (BitVec.ofNat 64 (slotA (sB k) + 8))) A) := by
  have getMemSetMem : ∀ (u : MachineState) (a v A : Word),
      (u.setMem a v).getMem A = if A = a then v else u.getMem A := by
    intro u a v A; simp [MachineState.setMem, MachineState.getMem]
  obtain ⟨c0, c1, c2, c3⟩ := postIter_code hc k hk
  have hslt : slotA (sB k) < 2 ^ 64 := by unfold slotA SCR sB; omega
  have hmod8 : slotA (sB k) % 8 = 0 := by unfold slotA SCR sB; omega
  have hav0 : accessValid (BitVec.ofNat 64 (slotA (sB k))) 8 = true := by
    rw [memAccessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslt]
    exact ⟨by unfold slotA SCR MEMORY_BYTES sB; omega, hmod8⟩
  have e0 : s.getReg .x31 + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (slotA (sB k)) := by
    rw [postSext12_zero, add_zero, ht6]
  have step1 : Steps im s 1 1
      ((s.setReg .x29 (s.getMem (BitVec.ofNat 64 (slotA (sB k))))).setPC (pcOf (POST + 2 + 4 * k + 1))) :=
    micro_step (i := .base (.LD .x29 .x31 0)) (m := .load .d .x29 .x31 (signExtend12 0)) c0 rfl rfl hpc
      (by simp only [Micro.exec, e0, hav0, LoadKind.width, if_true, LoadKind.read, hpc, pcOf_add4])
  set s1 := (s.setReg .x29 (s.getMem (BitVec.ofNat 64 (slotA (sB k))))).setPC (pcOf (POST + 2 + 4 * k + 1))
    with hs1def
  have hx29_s1 : s1.getReg .x29 = s.getMem (BitVec.ofNat 64 (slotA (sB k))) := by
    rw [hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x29 : Reg) ≠ .x0)]
  have hx31_s1 : s1.getReg .x31 = BitVec.ofNat 64 (slotA (sB k)) := by
    rw [hs1def, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x31)]
    exact ht6
  have hmem_s1 : ∀ A, s1.getMem A = s.getMem A := by
    intro A; rw [hs1def, MachineState.getMem_setPC, MachineState.getMem_setReg]
  have hpc_s1 : s1.pc = pcOf (POST + 2 + 4 * k + 1) := rfl
  have htgtlt : (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).toNat < 2 ^ 64 :=
    (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).isLt
  have e8 : s1.getReg .x31 + signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 (slotA (sB k) + 8) := by
    rw [hx31_s1, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show (8 : Word) = BitVec.ofNat 64 8 from by decide, ofNat_add_ofNat]
  have hslt8 : slotA (sB k) + 8 < 2 ^ 64 := by unfold slotA SCR sB; omega
  have hmod8_8 : (slotA (sB k) + 8) % 8 = 0 := by unfold slotA SCR sB; omega
  have hav8 : accessValid (BitVec.ofNat 64 (slotA (sB k) + 8)) 8 = true := by
    rw [memAccessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslt8]
    exact ⟨by unfold slotA SCR MEMORY_BYTES sB; omega, hmod8_8⟩
  have step2 : Steps im s1 1 1
      ((s1.setReg .x30 (s1.getMem (BitVec.ofNat 64 (slotA (sB k) + 8)))).setPC (pcOf (POST + 2 + 4 * k + 2))) :=
    micro_step (i := .base (.LD .x30 .x31 8)) (m := .load .d .x30 .x31 (signExtend12 8)) c1 rfl rfl hpc_s1
      (by simp only [Micro.exec, e8, hav8, LoadKind.width, if_true, LoadKind.read, hpc_s1, pcOf_add4])
  set s2 := (s1.setReg .x30 (s1.getMem (BitVec.ofNat 64 (slotA (sB k) + 8)))).setPC (pcOf (POST + 2 + 4 * k + 2))
    with hs2def
  have hx29_s2 : s2.getReg .x29 = s.getMem (BitVec.ofNat 64 (slotA (sB k))) := by
    rw [hs2def, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x30 : Reg) ≠ .x29)]
    exact hx29_s1
  have hx30_s2 : s2.getReg .x30 = s.getMem (BitVec.ofNat 64 (slotA (sB k) + 8)) := by
    rw [hs2def, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x30 : Reg) ≠ .x0)]
    exact hmem_s1 _
  have hx31_s2 : s2.getReg .x31 = BitVec.ofNat 64 (slotA (sB k)) := by
    rw [hs2def, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : (Reg.x30 : Reg) ≠ .x31)]
    exact hx31_s1
  have hpc_s2 : s2.pc = pcOf (POST + 2 + 4 * k + 2) := rfl
  have hmem_s2 : ∀ A, s2.getMem A = s.getMem A := by
    intro A; rw [hs2def, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hmem_s1 A
  have e0' : s2.getReg .x29 + signExtend12 (0 : BitVec 12) = s.getMem (BitVec.ofNat 64 (slotA (sB k))) := by
    rw [postSext12_zero, add_zero, hx29_s2]
  have hav0' : accessValid (s.getMem (BitVec.ofNat 64 (slotA (sB k)))) 8 = true := by
    have hSM : SCR ≤ MEMORY_BYTES := by unfold SCR MEMORY_BYTES; omega
    rw [memAccessValid_iff]
    exact ⟨by omega, hbnd.1⟩
  have step3 : Steps im s2 1 1
      ((s2.setMem (s.getMem (BitVec.ofNat 64 (slotA (sB k)))) (s2.getReg .x30)).setPC
        (pcOf (POST + 2 + 4 * k + 3))) :=
    micro_step (i := .base (.SD .x29 .x30 0)) (m := .store .d .x29 .x30 (signExtend12 0)) c2 rfl rfl hpc_s2
      (by simp only [Micro.exec, e0', hav0', StoreKind.width, if_true, StoreKind.write, hpc_s2, pcOf_add4])
  set s3 := (s2.setMem (s.getMem (BitVec.ofNat 64 (slotA (sB k)))) (s2.getReg .x30)).setPC
    (pcOf (POST + 2 + 4 * k + 3)) with hs3def
  have hx31_s3 : s3.getReg .x31 = BitVec.ofNat 64 (slotA (sB k)) := by
    rw [hs3def, MachineState.getReg_setPC, getReg_setMem']
    exact hx31_s2
  have hpc_s3 : s3.pc = pcOf (POST + 2 + 4 * k + 3) := rfl
  have hmem_s3 : ∀ A, s3.getMem A = upd s.getMem (s.getMem (BitVec.ofNat 64 (slotA (sB k))))
      (s.getMem (BitVec.ofNat 64 (slotA (sB k) + 8))) A := by
    intro A
    rw [hs3def, MachineState.getMem_setPC, getMemSetMem]
    unfold upd
    by_cases hA : A = s.getMem (BitVec.ofNat 64 (slotA (sB k)))
    · rw [if_pos hA, if_pos hA]; exact hx30_s2
    · rw [if_neg hA, if_neg hA]; exact hmem_s2 A
  have e : s3.getReg .x31 + signExtend12 (0x960 : BitVec 12) = BitVec.ofNat 64 (slotA (sB k) - 1696) := by
    rw [hx31_s3]; exact postSext12_decr (slotA (sB k)) (by unfold slotA SCR sB; omega) hslt
  have step4 : Steps im s3 1 1
      ((s3.setReg .x31 (s3.getReg .x31 + signExtend12 (0x960 : BitVec 12))).setPC
        (pcOf (POST + 2 + 4 * k + 4))) :=
    micro_step (i := .base (.ADDI .x31 .x31 (0x960 : BitVec 12)))
      (m := .alu .x31 .add (.reg .x31) (.imm (signExtend12 (0x960 : BitVec 12)))) c3 rfl rfl hpc_s3
      (by simp only [Micro.exec, BinOp.eval, Src.eval, hpc_s3, pcOf_add4])
  refine ⟨(s3.setReg .x31 (s3.getReg .x31 + signExtend12 (0x960 : BitVec 12))).setPC
    (pcOf (POST + 2 + 4 * k + 4)), ?_, ?_, ?_, ?_, ?_⟩
  · have := step1.trans (step2.trans (step3.trans step4))
    simpa using this
  · show pcOf (POST + 2 + 4 * k + 4) = pcOf (POST + 2 + 4 * (k + 1))
    rw [show POST + 2 + 4 * k + 4 = POST + 2 + 4 * (k + 1) from by ring]
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (Reg.x31 : Reg) ≠ .x0)]
    exact e
  · intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨hr29, hr30, hr31⟩ := hr
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr31),
      hs3def, MachineState.getReg_setPC, getReg_setMem',
      hs2def, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr30),
      hs1def, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr29)]
  · intro A
    rw [MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hmem_s3 A

/-- `postMem`'s fold, after only the first `j` iterations. -/
def postMemPartial (M : Word → Word) (j : Nat) : Word → Word :=
  (List.range j).foldl (fun N k => upd N (M (BitVec.ofNat 64 (slotA (sB k))))
    (M (BitVec.ofNat 64 (slotA (sB k) + 8)))) M

theorem postMemPartial_zero (M : Word → Word) : postMemPartial M 0 = M := rfl
theorem postMemPartial_nine (M : Word → Word) : postMemPartial M 9 = postMem M := rfl

theorem postMemPartial_succ (M : Word → Word) (j : Nat) :
    postMemPartial M (j + 1) =
      upd (postMemPartial M j) (M (BitVec.ofNat 64 (slotA (sB j)))) (M (BitVec.ofNat 64 (slotA (sB j) + 8))) := by
  unfold postMemPartial
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem slotA_ge_SCR (k : Nat) (hk : k < 9) : SCR ≤ slotA (sB k) := by unfold slotA SCR sB; omega

theorem postMemPartial_ge (M : Word → Word)
    (hb : ∀ k < 9, (M (BitVec.ofNat 64 (slotA (sB k)))).toNat % 8 = 0 ∧
      (M (BitVec.ofNat 64 (slotA (sB k)))).toNat + 8 ≤ SCR)
    (A : Word) (hA : SCR ≤ A.toNat) : ∀ j ≤ 9, postMemPartial M j A = M A := by
  intro j
  induction j with
  | zero => intro _; exact congrFun (postMemPartial_zero M) A
  | succ j ih =>
    intro hj
    rw [postMemPartial_succ]
    unfold upd
    rw [if_neg]
    · exact ih (by omega)
    · intro heq
      have hbound := (hb j (by omega)).2
      have := congrArg BitVec.toNat heq
      omega

theorem postMemPartial_slotA (M : Word → Word)
    (hb : ∀ k < 9, (M (BitVec.ofNat 64 (slotA (sB k)))).toNat % 8 = 0 ∧
      (M (BitVec.ofNat 64 (slotA (sB k)))).toNat + 8 ≤ SCR)
    (j k : Nat) (hj : j ≤ 9) (hk : k < 9) :
    postMemPartial M j (BitVec.ofNat 64 (slotA (sB k))) = M (BitVec.ofNat 64 (slotA (sB k))) ∧
    postMemPartial M j (BitVec.ofNat 64 (slotA (sB k) + 8)) = M (BitVec.ofNat 64 (slotA (sB k) + 8)) := by
  have hge := slotA_ge_SCR k hk
  have hlt : slotA (sB k) < 2 ^ 64 := by unfold slotA SCR sB; omega
  have hlt8 : slotA (sB k) + 8 < 2 ^ 64 := by unfold slotA SCR sB; omega
  refine ⟨postMemPartial_ge M hb _ ?_ j hj, postMemPartial_ge M hb _ ?_ j hj⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hge
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt8]; omega

/-- The 9-iteration loop (fixed `4 * rem` steps, unlike `copy2`'s data-dependent count). -/
theorem post_run_aux {im : Image} (hc : CodeAt im (pcOf POST) postWords) (s : MachineState)
    (hb : ∀ k < 9, (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).toNat % 8 = 0 ∧
      (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).toNat + 8 ≤ SCR) :
    ∀ rem n, n + rem = 9 → ∀ u : MachineState, RegsExcept s u [.x29, .x30, .x31] →
      u.pc = pcOf (POST + 2 + 4 * n) → (∀ A, u.getMem A = postMemPartial s.getMem n A) →
      (rem > 0 → u.getReg .x31 = BitVec.ofNat 64 (slotA (sB n))) →
      ∃ t : MachineState, Steps im u (4 * rem) (4 * rem) t ∧
        t.pc = pcOf (POST + 2 + 4 * 9) ∧ RegsExcept u t [.x29, .x30, .x31] ∧
        (∀ A, t.getMem A = postMem s.getMem A) := by
  intro rem
  induction rem with
  | zero =>
    intro n hn u hreg hpc hmem _
    have hn9 : n = 9 := by omega
    subst hn9
    exact ⟨u, Steps.refl u, hpc, RegsExcept.refl u _, fun A => by rw [hmem A, postMemPartial_nine]⟩
  | succ r ih =>
    intro n hn u hreg hpc hmem hx31
    have hn9 : n < 9 := by omega
    have hx31' := hx31 (by omega)
    have hmem_k : u.getMem (BitVec.ofNat 64 (slotA (sB n))) = s.getMem (BitVec.ofNat 64 (slotA (sB n))) := by
      rw [hmem]; exact (postMemPartial_slotA s.getMem hb n n (by omega) hn9).1
    have hmem_k8 : u.getMem (BitVec.ofNat 64 (slotA (sB n) + 8)) = s.getMem (BitVec.ofNat 64 (slotA (sB n) + 8)) := by
      rw [hmem]; exact (postMemPartial_slotA s.getMem hb n n (by omega) hn9).2
    have hbnd' : (u.getMem (BitVec.ofNat 64 (slotA (sB n)))).toNat % 8 = 0 ∧
        (u.getMem (BitVec.ofNat 64 (slotA (sB n)))).toNat + 8 ≤ SCR := by
      rw [hmem_k]; exact hb n hn9
    obtain ⟨t', step', hpt', hxt', hrt', hmt'⟩ := post_iter hc n hn9 u hpc hx31' hbnd'
    have hmem_t' : ∀ A, t'.getMem A = postMemPartial s.getMem (n + 1) A := by
      intro A
      rw [hmt' A, postMemPartial_succ]
      unfold upd
      simp only [hmem_k, hmem_k8]
      by_cases hA : A = s.getMem (BitVec.ofNat 64 (slotA (sB n)))
      · rw [if_pos hA, if_pos hA]
      · rw [if_neg hA, if_neg hA, hmem A]
    have hreg' : RegsExcept s t' [.x29, .x30, .x31] := by
      have htr : RegsExcept s t' ([.x29, .x30, .x31] ++ [.x29, .x30, .x31]) := hreg.trans hrt'
      exact htr.mono (fun r hr => (List.mem_append.mp hr).elim id id)
    have hxt'' : t'.getReg .x31 = BitVec.ofNat 64 (slotA (sB (n + 1))) := by
      have heq : slotA (sB n) - 1696 = slotA (sB (n + 1)) := by unfold slotA sB; omega
      rw [hxt', heq]
    obtain ⟨t, step, hptf, hrtf, hmtf⟩ := ih (n + 1) (by omega) t' hreg' hpt' hmem_t' (fun _ => hxt'')
    refine ⟨t, ?_, hptf, ?_, hmtf⟩
    · have hcomb : Steps im u (4 + 4 * r) (4 + 4 * r) t := step'.trans step
      have heq4 : 4 * (r + 1) = 4 + 4 * r := by ring
      rw [heq4]; exact hcomb
    · have htr2 : RegsExcept u t ([.x29, .x30, .x31] ++ [.x29, .x30, .x31]) := hrt'.trans hrtf
      exact htr2.mono (fun r hr => (List.mem_append.mp hr).elim id id)

/-- The `jal zero, 57168` at `POST + 38` (into `copy2`). -/
theorem postTail_step {im : Image} (hc : CodeAt im (pcOf POST) postWords) (s : MachineState)
    (hpc : s.pc = pcOf (POST + 38)) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 57168 ∧ RegsExcept s t [] ∧ (∀ A, t.getMem A = s.getMem A) := by
  have hc38 := postTail_code hc
  have heqenc : encJal 0 (jOff (POST + 38) 57168) = 0xac0fc06f := by decide
  have hcode : CodeAt im (pcOf (POST + 38)) [encJal 0 (jOff (POST + 38) 57168)] := by
    rw [heqenc]; exact hc38
  have step := jal_step (a := POST + 38) (t := 57168) (rd := 0) (r := Reg.x0) (by decide) (by decide) hcode
    (by unfold POST; omega) (by omega) s hpc
  refine ⟨_, step, rfl, ?_, ?_⟩
  · intro r _; simp [MachineState.setReg, MachineState.getReg_setPC]
  · intro A; simp [MachineState.setReg, MachineState.getMem_setPC]

/-- The post-pass: 38 steps to `POST + 38`, which is (S5185 FTS16) `jal zero, 57168` into the level-2 nonce record
pass `copy2` (in `expandFts16Code`), so 39 steps reach `copy2`'s entry; memory is `postMem`. -/
theorem post_run {im : Image} (hc : CodeAt im (pcOf POST) postWords) (s : MachineState)
    (hpc : s.pc = pcOf POST) (addr : Nat → Nat)
    (hm : ∀ k < 9, s.getMem (BitVec.ofNat 64 (slotA (sB k))) = BitVec.ofNat 64 (addr k))
    (hb : ∀ k < 9, addr k % 8 = 0 ∧ addr k + 8 ≤ SCR) :
    ∃ t, Steps im s 39 39 t ∧ t.pc = pcOf 57168 ∧
      RegsExcept s t [.x29, .x30, .x31] ∧ (∀ A, t.getMem A = postMem s.getMem A) := by
  have hb' : ∀ k < 9, (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).toNat % 8 = 0 ∧
      (s.getMem (BitVec.ofNat 64 (slotA (sB k)))).toNat + 8 ≤ SCR := by
    intro k hk
    have haddrlt : addr k < 2 ^ 64 := by have := (hb k hk).2; unfold SCR at this; omega
    rw [hm k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddrlt]
    exact hb k hk
  obtain ⟨u, step0, hpu, hxu, hru, hmu⟩ := postHead_step hc s hpc
  obtain ⟨t, step, hpt, hrt, hmt⟩ := post_run_aux hc s hb' 9 0 rfl u (hru.mono (by decide))
    hpu (fun A => by rw [hmu A, postMemPartial_zero]) (fun _ => hxu)
  obtain ⟨t2, step2, hpt2, hrt2, hmt2⟩ := postTail_step hc t hpt
  have hcombined : RegsExcept s t2 ([.x31] ++ ([.x29, .x30, .x31] ++ [])) := hru.trans (hrt.trans hrt2)
  refine ⟨t2, ?_, hpt2, ?_, ?_⟩
  · have hcomb := (step0.trans step).trans step2
    have heq : 2 + 4 * 9 + 1 = 39 := by norm_num
    rw [← heq]; exact hcomb
  · exact hcombined.mono (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h <;> simp [h])
  · intro A; rw [hmt2 A, hmt A]

end SigGolfCandidate.FtsGrind

