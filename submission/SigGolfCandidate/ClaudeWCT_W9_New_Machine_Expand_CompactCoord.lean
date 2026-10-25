import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_CompactLoop
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_DrvBits

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt planBytes)
open ClaudeWCT.W9.T3M (authBase authRoot)
set_option linter.unusedSimpArgs false
/-- r3w: the staging slot of sibling level `l` (levels `0..4` from the plan table, level 5 the fixed staging block
`+832`, as the compaction code writes it; the witness layer's own `authSibOff 5` moved to `784`). -/
def authSibOff (c l : Nat) : Nat :=
  if l < 5 then ClaudeWCT.W9.T3M.authSibOff c l else 832 + 48 * (1 - c / 2 ^ 5 % 2)
def bitE (l : Nat) : E :=
  if l < 6 then .bin .and (.bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))) (.c 1#64)
  else .bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))
def nbE (l : Nat) : E := .bin .xor (bitE l) (.c 1#64)
def t6E (l : Nat) : E := .bin .add (.bin .sll (nbE l) (.c 4#64)) (.bin .sll (nbE l) (.c 5#64))
def hwE (l : Nat) : E :=
  .un (.ld .hu (2 * (l % 4))) (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld)
/-- Nested FTS (r1-1): level 5 targets the fixed staging block `+832` (`addi t3,zero,832`, no plan load). -/
def dstE (l : Nat) : E :=
  if l < 5 then .bin .add (.bin .add (.reg .x9) (hwE l)) (t6E l)
  else if l = 5 then .bin .add (.bin .add (.reg .x9) (.c 832#64)) (t6E l) else .bin .add (.reg .x9) (hwE l)
def a3E (l : Nat) : E := .bin .add (.reg .x8) (t6E l)
def srcE (l o : Nat) : E :=
  if 64 * (6 - l) + o = 0 then a3E l else .bin .add (a3E l) (.c (BitVec.ofNat 64 (64 * (6 - l) + o)))
def sibRegs (l : Nat) : RegFile :=
  ((((RegFile.init.set .x13 (a3E l)).set .x28 (dstE l)).set .x29 (srcE l 0).ld).set .x30 (srcE l 8).ld).set .x31
    (t6E l)
/-- r3w (witness stack): store shift of sibling level `l` of coordinate `k` (`sd t4,-sh(t3)`; level 5 one block
further down). The FTS content of the staging is dead (rebuilt by the finish pass), only the frame matters. -/
def sh (k l : Nat) : Nat := if k = 0 then 0 else if l < 5 then 48 * (k - 1) else 48 * k
def shOff (k l o : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - sh k l + o)
theorem sh_le (k l : Nat) : sh k l ≤ 48 * k ∧ sh k l % 16 = 0 := by
  unfold sh; split_ifs <;> omega
theorem ofNat_shOff (X k l o : Nat) (hk : k < 9) (h : sh k l ≤ X) :
    BitVec.ofNat 64 X + shOff k l o = BitVec.ofNat 64 (X - sh k l + o) := by
  have := sh_le k l
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  unfold shOff
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64]
  omega
/-- r3w: destination of sibling level `l` of coordinate `k` (region base `D`). -/
def sdst (c D k l : Nat) : Nat := D - sh k l + authSibOff c l
def sibMem (k l : Nat) : SymMem :=
  [(⟨some (dstE l), shOff k l 8⟩, (srcE l 8).ld), (⟨some (dstE l), shOff k l 0⟩, (srcE l 0).ld)]
def sibObl4 (k l : Nat) : List Oblig :=
  [.valid ⟨some (dstE l), shOff k l 8⟩ 8, .valid ⟨some (dstE l), shOff k l 0⟩ 8,
    .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l) + 8)⟩ 8, .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l))⟩ 8]
def sibOblP (l : Nat) : List Oblig := [.align8 (.reg .x20), .valid ⟨some (.reg .x20), BitVec.ofNat 64 (2 * l)⟩ 2]
def sibObl (k l : Nat) : List Oblig := sibObl4 k l ++ (if l = 5 then [] else sibOblP l)
set_option maxRecDepth 20000 in
theorem run_sib (k l : Nat) (hk : k < 9) (hl : l < 6) : symRun cfgC (cSib k l) (pcOf (sibAt k l)) 40 =
    some ⟨⟨sibRegs l, sibMem k l, sibObl k l⟩, .c (pcOf (sibAt k l + sibLen l)), .endOfCode, sibLen l, sibLen l⟩ := by
  interval_cases k <;> interval_cases l <;> kernel_rfl
def srcOff (c l : Nat) : Nat := 64 * (6 - l) + 48 * (1 - c / 2 ^ l % 2)
def planHW (c l : Nat) : Nat := if l < 6 then authBase c l else authRoot c
set_option maxRecDepth 100000 in
theorem planHW_ok : ∀ r < 64, ∀ l < 5,
    LoadKind.hu.fromWord (bytesToWordLE ((planBytes.drop (8 * (2 * r + l / 4))).take 8)) (2 * (l % 4)) =
      BitVec.ofNat 64 (planHW r l) := by
  decide +kernel
theorem authSibOff_ok : ∀ c < 128, ∀ l < 5, authSibOff c l % 16 = 0 ∧ authSibOff c l + 16 ≤ 320 := by
  decide +kernel
theorem authSibOff_five (c : Nat) : authSibOff c 5 = 832 + 48 * (1 - c / 2 ^ 5 % 2) := by
  unfold authSibOff; rw [if_neg (by norm_num)]
theorem auth6_ok (c : Nat) (hc : c < 128) (l : Nat) (hl : l < 6) :
    authSibOff c l % 16 = 0 ∧ authSibOff c l + 16 ≤ 896 ∧ (l < 5 → authSibOff c l + 16 ≤ 320) ∧
      (l = 5 → 832 ≤ authSibOff c l) := by
  by_cases h : l < 5
  · have := authSibOff_ok c hc l h
    exact ⟨this.1, by omega, fun _ => this.2, fun h5 => by omega⟩
  · obtain rfl : l = 5 := by omega
    rw [authSibOff_five]
    have : c / 2 ^ 5 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    refine ⟨by omega, by omega, fun h => by omega, fun _ => by omega⟩
theorem planHW_mod (c l : Nat) : planHW (c % 64) l = planHW c l := by
  unfold planHW authBase authRoot; rw [Nat.mod_mod]
section eval
variable {s : MachineState} {c : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (hc : c < 128)
include h19 hc
theorem bitE_eval (l : Nat) (hl : l < 7) : (bitE l).eval s = BitVec.ofNat 64 (c / 2 ^ l % 2) := by
  apply BitVec.eq_of_toNat_eq
  unfold bitE
  split
  · simp only [E.eval, BinOp.eval, h19, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show l < 64 by omega), show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod,
      Nat.mod_eq_of_lt (show c / 2 ^ l % 2 < 2 ^ 64 from lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))]
  · have hl6 : l = 6 := by omega
    subst hl6
    simp only [E.eval, BinOp.eval, h19, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
    norm_num
    omega
theorem nbE_eval (l : Nat) (hl : l < 7) : (nbE l).eval s = BitVec.ofNat 64 (1 - c / 2 ^ l % 2) := by
  have hb := bitE_eval h19 hc l hl
  simp only [nbE, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem t6E_eval (l : Nat) (hl : l < 7) : (t6E l).eval s = BitVec.ofNat 64 (48 * (1 - c / 2 ^ l % 2)) := by
  have hb := nbE_eval h19 hc l hl
  simp only [t6E, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem a3E_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) :
    (a3E l).eval s = BitVec.ofNat 64 (S + 48 * (1 - c / 2 ^ l % 2)) := by
  simp only [a3E, E.eval, BinOp.eval, h8, t6E_eval h19 hc l hl, ofNat_add_ofNat]
theorem srcE_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (o : Nat) :
    (srcE l o).eval s = BitVec.ofNat 64 (S + srcOff c l + o) := by
  unfold srcE srcOff
  split
  · rw [a3E_eval h19 hc l hl h8]; congr 1; omega
  · simp only [E.eval, BinOp.eval, a3E_eval h19 hc l hl h8, ofNat_add_ofNat]; congr 1; omega
end eval
theorem hwE_eval {s : MachineState} {c : Nat} (hc : c < 128)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s) (l : Nat) (hl : l < 5) :
    (hwE l).eval s = BitVec.ofNat 64 (planHW c l) := by
  have hr : c % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hw : (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld).eval s =
      bytesToWordLE ((planBytes.drop (8 * (2 * (c % 64) + l / 4))).take 8) := by
    split
    · simp only [E.eval, h20]
      rw [show l / 4 = 0 by omega, show PLAN + 16 * (c % 64) = PLAN + 8 * (2 * (c % 64) + 0) by ring]
      exact hp _ (by omega)
    · simp only [E.eval, BinOp.eval, h20, ofNat_add_ofNat]
      rw [show l / 4 = 1 by omega, show PLAN + 16 * (c % 64) + 8 = PLAN + 8 * (2 * (c % 64) + 1) by ring]
      exact hp _ (by omega)
  simp only [hwE, E.eval, UnOp.eval]
  rw [hw, planHW_ok (c % 64) hr l hl, planHW_mod]
theorem authSibOff_eq (c l : Nat) (hl : l < 5) :
    authSibOff c l = if l < 6 then planHW c l + 48 * (1 - c / 2 ^ l % 2) else planHW c l := by
  unfold authSibOff ClaudeWCT.W9.T3M.authSibOff planHW SigGolfCandidate.T3M.sibOff
  rw [if_pos hl]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  split_ifs <;> omega
theorem dstE_eval {s : MachineState} {c D : Nat} (hc : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (l : Nat) (hl : l < 6) :
    (dstE l).eval s = BitVec.ofNat 64 (D + authSibOff c l) := by
  by_cases hl5 : l < 5
  · rw [authSibOff_eq c l (by omega), if_pos (show l < 6 by omega)]
    simp only [dstE, if_pos hl5, E.eval, BinOp.eval, h9, hwE_eval hc h20 hp l hl5, t6E_eval h19 hc l (by omega),
      ofNat_add_ofNat]
    rw [Nat.add_assoc]
  · obtain rfl : l = 5 := by omega
    rw [authSibOff_five]
    simp only [dstE, show ¬ (5 : Nat) < 5 by decide, if_false, if_true, E.eval, BinOp.eval, h9,
      t6E_eval h19 hc 5 (by omega), ofNat_add_ofNat]
    rw [Nat.add_assoc]
theorem srcOff_bound (c l : Nat) : srcOff c l + 16 ≤ 448 ∧ srcOff c l % 16 = 0 := by
  unfold srcOff
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  constructor <;> omega
theorem sibRegs_get (l : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x13, .x28, .x29, .x30, .x31]) :
    ((sibRegs l).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h13, h28, h29, h30, h31⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
/-! Nested FTS (r1-1): level 6. The word at `sibAt k 6` jumps to the trampoline `P6(k)` (words
`33000 + 13 k`), which loads coordinate `k`'s top sibling from the scratch region (`x8 + 48 (1 - bit6)`) and
stores it with the flag `1 - bit6` to the hold slot `0x380000 + 32 k`; the final assembly places it. -/
def cJ6s : List (BitVec 32) := [4187975791,3776933999,3365892207,2954850415,2543808623,4279201903,3868160111,3457118319,3046076527]
def cP6s : List (List (BitVec 32)) := [[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,31338531,32388131,33437731,109084783],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,64892963,65942563,66992163,520126575],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,98447395,99496995,100546595,931168367],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,132001827,133051427,134101027,1342210159],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,165556259,166605859,167655459,1753251951],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,199110691,200160291,201209891,17858671],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,232665123,233714723,234764323,428900463],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,266219555,267269155,268318755,839942255],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,299773987,300823587,301873187,1250984047]]
def cJ6 (k : Nat) : List (BitVec 32) := [cJ6s.getD k 0]
def cP6 (k : Nat) : List (BitVec 32) := cP6s.getD k []
def p6At (k : Nat) : Nat := 33000 + 13 * k
def p6tE : E := .bin .add (.bin .sll (nbE 6) (.c 5#64)) (.bin .sll (nbE 6) (.c 4#64))
def a6E : E := .bin .add p6tE (.reg .x8)
def p6Regs : RegFile :=
  ((((RegFile.init.set .x13 a6E).set .x28 (.c 0x380000#64)).set .x29 (E.ld a6E)).set .x30
    (E.ld (.bin .add a6E (.c 8#64)))).set .x31 (nbE 6)
def p6Mem (k : Nat) : SymMem :=
  [(⟨none, BitVec.ofNat 64 (holdAt k + 16)⟩, nbE 6), (⟨none, BitVec.ofNat 64 (holdAt k + 8)⟩, E.ld (.bin .add a6E (.c 8#64))),
    (⟨none, BitVec.ofNat 64 (holdAt k)⟩, E.ld a6E)]
def p6Obl : List Oblig := [.valid ⟨some a6E, 8#64⟩ 8, .valid ⟨some a6E, 0#64⟩ 8]
theorem run_j6 (k : Nat) (hk : k < 9) : symRun cfgC (cJ6 k) (pcOf (sibAt k 6)) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf (p6At k)), .jump, 1, 1⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_p6 (k : Nat) (hk : k < 9) : symRun cfgC (cP6 k) (pcOf (p6At k)) 40 =
    some ⟨⟨p6Regs, p6Mem k, p6Obl⟩, .c (pcOf (coordAt k + 109)), .jump, 13, 13⟩ := by
  interval_cases k <;> kernel_rfl
theorem p6Regs_get (s : MachineState) (r : Reg) (hr : r ∉ [.x13, .x28, .x29, .x30, .x31]) :
    (p6Regs.get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h13, h28, h29, h30, h31⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sib_spec (k l : Nat) (hk : k < 9) (hl : l < 6) (s : MachineState) (hpc : s.pc = pcOf (sibAt k l))
    (c S D : Nat) (hcl : c < 128) (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)))
    (hp : PlanAt s) (hS : S % 16 = 0) (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0)
    (hD' : D + 896 ≤ MEMORY_BYTES) (hsh : 48 * k ≤ D) :
    ∃ t, Steps im s (sibLen l) (sibLen l) t ∧ t.pc = pcOf (sibAt k l + sibLen l) ∧
      RegsExcept s t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = sdst c D k l + 8 then s.getMem (BitVec.ofNat 64 (S + srcOff c l + 8))
        else if A = sdst c D k l then s.getMem (BitVec.ofNat 64 (S + srcOff c l))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have ha := auth6_ok c hcl l hl
  have hso := srcOff_bound c l
  have hd := dstE_eval hcl h19 h20 hp h9 l hl
  have hs0 := srcE_eval h19 hcl l (by omega) h8 0
  have hs8 := srcE_eval h19 hcl l (by omega) h8 8
  have ha3 := a3E_eval h19 hcl l (by omega) h8
  have hrun := run_sib k l hk hl
  have hshl := sh_le k l
  have e8 := ofNat_shOff (D + authSibOff c l) k l 8 hk (by omega)
  have e0 := ofNat_shOff (D + authSibOff c l) k l 0 hk (by omega)
  have hobl : Oblig.all s (sibObl k l) := by
    rw [Oblig.all_iff]
    intro o ho
    unfold sibObl at ho
    rw [List.mem_append] at ho
    rcases ho with ho | ho
    swap
    · split at ho
      · simp at ho
      · simp only [sibOblP, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold PLAN; omega
        · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
          unfold PLAN; omega
    simp only [sibObl4, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hd, e8, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, hd, e0, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + (64 * (6 - l) + 8) = S + srcOff c l + 8 by unfold srcOff; omega]
      omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + 64 * (6 - l) = S + srcOff c l by unfold srcOff; omega]
      omega
  refine ⟨_, symRun_sound hrun (code_cSib hc k l hk hl) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    rw [Result.toState_getReg]
    exact sibRegs_get l s r hr
  · intro A hA
    unfold sdst
    simp only [Result.toState_getMem, sibMem, memEval_cons, memEval_nil, Addr.eval, E.eval, hd, hs0, hs8, e8, e0,
      Nat.add_zero]
    have hbig : D - sh k l + authSibOff c l + 8 < 2 ^ 64 := by omega
    have q8 : D + authSibOff c l - sh k l + 8 = D - sh k l + authSibOff c l + 8 := by omega
    have q0 : D + authSibOff c l - sh k l = D - sh k l + authSibOff c l := by omega
    rw [q8, q0]
    by_cases h1 : A = D - sh k l + authSibOff c l + 8
    · subst h1; simp
    · rw [if_neg (fun h => h1 ((ofNat_inj hA hbig).mp h)), if_neg h1]
      by_cases h2 : A = D - sh k l + authSibOff c l
      · subst h2; simp
      · rw [if_neg (fun h => h2 ((ofNat_inj hA (by omega)).mp h)), if_neg h2]
theorem code_cJ6 (k : Nat) (hk : k < 9) : CodeAt im (pcOf (sibAt k 6)) (cJ6 k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cP6 (k : Nat) (hk : k < 9) : CodeAt im (pcOf (p6At k)) (cP6 k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sib6_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (sibAt k 6)) (c S : Nat)
    (hcl : c < 128) (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h19 : s.getReg .x19 = BitVec.ofNat 64 c)
    (hS : S % 16 = 0) (hS' : S + 448 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf (coordAt k + 109) ∧ RegsExcept s t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = holdAt k + 16 then BitVec.ofNat 64 (1 - c / 2 ^ 6 % 2)
        else if A = holdAt k + 8 then s.getMem (BitVec.ofNat 64 (S + srcOff c 6 + 8))
        else if A = holdAt k then s.getMem (BitVec.ofNat 64 (S + srcOff c 6))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨t1, hj, r1, m1, p1⟩ : ∃ t1, Steps im s 1 1 t1 ∧ (∀ r, t1.getReg r = s.getReg r) ∧
      (∀ A, t1.getMem A = s.getMem A) ∧ t1.pc = pcOf (p6At k) := by
    refine ⟨_, symRun_sound (run_j6 k hk) (code_cJ6 hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_⟩
    · intro r; rw [Result.toState_getReg]; cases r <;> rfl
    · intro A; simp [rv_simp]
    · simp [Result.toState_pc, E.eval]
  have hnb := nbE_eval (s := t1) (by rw [r1]; exact h19) hcl 6 (by omega)
  have h48 : p6tE.eval t1 = BitVec.ofNat 64 (48 * (1 - c / 2 ^ 6 % 2)) := by
    simp only [p6tE, E.eval, BinOp.eval, hnb]
    have : c / 2 ^ 6 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases (show c / 2 ^ 6 % 2 = 0 ∨ c / 2 ^ 6 % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
  have hso := srcOff_bound c 6
  have ha6 : a6E.eval t1 = BitVec.ofNat 64 (S + srcOff c 6) := by
    simp only [a6E, E.eval, BinOp.eval, h48, r1, h8, ofNat_add_ofNat]
    congr 1; unfold srcOff; omega
  have ha8 : (E.bin .add a6E (.c 8#64)).eval t1 = BitVec.ofNat 64 (S + srcOff c 6 + 8) := by
    simp only [E.eval, BinOp.eval, ha6, ofNat_add_ofNat]
  have hobl : Oblig.all t1 p6Obl := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [p6Obl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, ha6, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, ha6, BitVec.add_zero, accessValid_iff, BitVec.toNat_ofNat]; omega
  have hp := symRun_sound (run_p6 k hk) (code_cP6 hc k hk) t1 p1 hobl
  refine ⟨_, (hj.trans hp).of_eq rfl rfl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    rw [Result.toState_getReg, p6Regs_get t1 r hr, r1]
  · intro A hA
    simp only [Result.toState_getMem, p6Mem, memEval_cons, memEval_nil, Addr.eval, hnb, ha6, ha8, E.eval, BinOp.eval,
      ofNat_add_ofNat, m1]
    have hH : holdAt k + 16 < 2 ^ 64 := by unfold holdAt; omega
    by_cases e1 : A = holdAt k + 16
    · subst e1; simp
    · rw [if_neg (fun h => e1 ((ofNat_inj hA hH).mp h)), if_neg e1]
      by_cases e2 : A = holdAt k + 8
      · subst e2; simp
      · rw [if_neg (fun h => e2 ((ofNat_inj hA (by omega)).mp h)), if_neg e2]
        by_cases e3 : A = holdAt k
        · subst e3; simp
        · rw [if_neg (fun h => e3 ((ofNat_inj hA (by omega)).mp h)), if_neg e3]
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt child_bits)
set_option linter.unusedSimpArgs false
def SNAP : Nat := 0x200000
def rHead (k : Nat) : Result :=
  [RHead0.res, RHead1.res, RHead2.res, RHead3.res, RHead4.res, RHead5.res, RHead6.res, RHead7.res, RHead8.res].getD k
    RHead0.res
def rMid (k : Nat) : Result :=
  [RMid0.res, RMid1.res, RMid2.res, RMid3.res, RMid4.res, RMid5.res, RMid6.res, RMid7.res, RMid8.res].getD k RMid0.res
theorem run_head (k : Nat) (hk : k < 9) : symRun cfgC (cHead k) (pcOf (coordAt k)) 40 = some (rHead k) := by
  interval_cases k
  exacts [RHead0, RHead1, RHead2, RHead3, RHead4, RHead5, RHead6, RHead7, RHead8]
theorem run_mid (k : Nat) (hk : k < 9) : symRun cfgC (cMid k) (pcOf (coordAt k + 6)) 40 = some (rMid k) := by
  interval_cases k
  exacts [RMid0, RMid1, RMid2, RMid3, RMid4, RMid5, RMid6, RMid7, RMid8]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem start_spec (s : MachineState) (hpc : s.pc = pcOf 41108) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 0x840 ∧
      t.getReg .x11 = BitVec.ofNat 64 SNAP ∧ t.getReg .x12 = BitVec.ofNat 64 1152 ∧ t.getReg .x1 = pcOf 41115 ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RStart (code_cStart hc) s hpc (by simp [RStart.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RStart.res, E.eval]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]; rfl
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · c_regs RStart.res
  · intro A _ _; rfl
theorem regs_spec (s : MachineState) (hpc : s.pc = pcOf 41115) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (coordAt 0) ∧ t.getReg .x8 = BitVec.ofNat 64 SNAP ∧
      t.getReg .x9 = BitVec.ofNat 64 0x840 ∧ t.getReg .x18 = BitVec.ofNat 64 PLAN ∧
      RegsExcept s t [.x8, .x9, .x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RRegs (code_cRegs hc) s hpc (by simp [RRegs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RRegs.res, E.eval, coordAt]
  · simp [RRegs.res, rv_simp]; rfl
  · simp [RRegs.res, rv_simp]
  · simp [RRegs.res, rv_simp]; rfl
  · c_regs RRegs.res
  · intro A _ _; rfl
theorem final_spec (s : MachineState) (hpc : s.pc = pcOf 42120) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (0x800 + 9280) ∧
      t.getReg .x11 = BitVec.ofNat 64 (0x800 + 8128) ∧ t.getReg .x12 = BitVec.ofNat 64 1713 ∧
      t.getReg .x1 = pcOf 42127 ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RFinal (code_cFinal hc) s hpc (by simp [RFinal.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RFinal.res, E.eval]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · c_regs RFinal.res
  · intro A _ _; rfl
theorem halt_spec (s : MachineState) (hpc : s.pc = pcOf 42127) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42142 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RHalt (code_cHalt hc) s hpc (by simp [RHalt.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RHalt.res, E.eval]
  · c_regs RHalt.res
  · intro A _ _; rfl
end
def headX6 (k : Nat) : E :=
  .bin .srl (E.c (BitVec.ofNat 64 (0x60 + 8 * (WCT9.childBase k / 64)))).ld (.c (BitVec.ofNat 64 (WCT9.childBase k % 64)))
def headRegs (k : Nat) : RegFile :=
  ((((RegFile.init.set .x6 (headX6 k)).set .x19 (.bin .and (headX6 k) (.c 127#64))).set .x11 (.reg .x9)).set .x12
    (.c 40#64)).set .x1 (.c (pcOf (coordAt k + 6)))
def midRegs (k : Nat) : RegFile :=
  (((RegFile.init.set .x10 (.bin .add (.reg .x8) (.c 448#64))).set .x11 (.bin .add (.reg .x9) (.c 320#64))).set .x12
    (.c 72#64)).set .x1 (.c (pcOf (coordAt k + 10)))
theorem rHead_eq (k : Nat) (hk : k < 9) : rHead k = ⟨⟨headRegs k, [], []⟩, .c (pcOf 42137), .jump, 6, 6⟩ := by
  interval_cases k <;> kernel_rfl
theorem rMid_eq (k : Nat) (hk : k < 9) : rMid k = ⟨⟨midRegs k, [], []⟩, .c (pcOf 42130), .jump, 4, 4⟩ := by
  interval_cases k <;> kernel_rfl
theorem headRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x6, .x11, .x12, .x19]) :
    ((headRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h6, h11, h12, h19⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem midRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x10, .x11, .x12]) :
    ((midRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h10, h11, h12⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem childBase_shift (k : Nat) (hk : k < 9) : WCT9.childBase k % 64 + 7 ≤ 64 ∧ WCT9.childBase k / 64 < 4 := by
  interval_cases k <;> decide
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem head_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (D : Nat) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42137 ∧
      t.getReg .x19 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase k % 128) ∧
      t.getReg .x11 = BitVec.ofNat 64 D ∧ t.getReg .x12 = BitVec.ofNat 64 40 ∧ t.getReg .x1 = pcOf (coordAt k + 6) ∧
      RegsExcept s t [.x1, .x6, .x11, .x12, .x19] ∧ Frame s t (fun _ => False) := by
  have hrun := run_head k hk
  rw [rHead_eq k hk] at hrun
  obtain ⟨hsh, hw⟩ := childBase_shift k hk
  refine ⟨_, symRun_sound hrun (code_cHead hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, headRegs, headX6, RegFile.set, RegFile.get, E.eval, BinOp.eval]
    have hm := hN (WCT9.childBase k / 64) hw
    rw [hm]
    apply BitVec.eq_of_toNat_eq
    have := child_bits N (WCT9.childBase k / 64) (WCT9.childBase k % 64) hsh
    rw [Nat.div_add_mod] at this
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 64 by omega)]
    rw [this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num) : N.toNat / 2 ^ WCT9.childBase k % 128 < 2 ^ 64)]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval, h9]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact headRegs_get k s r hr
  · intro A _ _; rfl
theorem mid_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 6)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (S + 448) ∧
      t.getReg .x11 = BitVec.ofNat 64 (D + 320) ∧ t.getReg .x12 = BitVec.ofNat 64 72 ∧
      t.getReg .x1 = pcOf (coordAt k + 10) ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  have hrun := run_mid k hk
  rw [rMid_eq k hk] at hrun
  refine ⟨_, symRun_sound hrun (code_cMid hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact midRegs_get k s r hr
  · intro A _ _; rfl
theorem row_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 10)) (c : Nat)
    (hcl : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (coordAt k + 13) ∧ t.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)) ∧
      RegsExcept s t [.x7, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_row k hk) (code_cRow hc k hk) s hpc (by simp [RRow.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RRow.res, RegFile.get, E.eval, BinOp.eval, h19, h18]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl, SigGolfCandidate.T3M.Search.ofNat_and_mask c 6 (by norm_num)]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; ring
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h20⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem step_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 109)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (coordAt k + 111) ∧ t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧
      t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧ RegsExcept s t [.x8, .x9] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_step k hk) (code_cStep hc k hk) s hpc (by simp [RStep.res, rv_simp]), ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8', h9'⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
def sibLev (c j : Nat) : Option Nat :=
  (List.range 6).find? fun l => authSibOff c l = 8 * j ∨ authSibOff c l + 8 = 8 * j
def sibSrc (c j : Nat) : Option Nat :=
  (sibLev c j).map fun l => if authSibOff c l = 8 * j then srcOff c l else srcOff c l + 8
/-- The hold slot of coordinate `k`: its top sibling and the flag `1 - bit6`. -/
def holdMem (M : Nat → Word) (c S k : Nat) (A : Nat) (rest : Word) : Word :=
  if A = holdAt k + 16 then BitVec.ofNat 64 (1 - c / 2 ^ 6 % 2)
  else if A = holdAt k + 8 then M (S + srcOff c 6 + 8)
  else if A = holdAt k then M (S + srcOff c 6) else rest
def sibsMem (M : Nat → Word) (c S D k L : Nat) (A : Nat) : Word :=
  match (List.range L).find? (fun l => A = sdst c D k l ∨ A = sdst c D k l + 8) with
  | some l => if A = sdst c D k l then M (S + srcOff c l) else M (S + srcOff c l + 8)
  | none => M A
theorem find_range_succ (p : Nat → Bool) (L : Nat) :
    (List.range (L + 1)).find? p = match (List.range L).find? p with
      | some l => some l
      | none => if p L then some L else none := by
  rw [List.range_succ, List.find?_append]
  cases h : (List.range L).find? p with
  | some l => rfl
  | none => simp only [List.find?_cons, List.find?_nil, Option.none_or]; cases hp : p L <;> simp [hp]
theorem find_some {p : Nat → Bool} {L l : Nat} (h : (List.range L).find? p = some l) : l < L ∧ p l = true :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), List.find?_some h⟩
theorem find_none {p : Nat → Bool} {L : Nat} (h : (List.range L).find? p = none) (l : Nat) (hl : l < L) :
    p l = false := by
  have := List.find?_eq_none.mp h l (List.mem_range.mpr hl)
  simpa using this
theorem auth_disj (c : Nat) (hc : c < 128) (l l' : Nat) (hl : l < 6) (hl' : l' < 6) (hne : l ≠ l') :
    authSibOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authSibOff c l := by
  by_cases h : l < 5 ∧ l' < 5
  · have e1 : authSibOff c l = ClaudeWCT.W9.T3M.authSibOff c l := if_pos h.1
    have e2 : authSibOff c l' = ClaudeWCT.W9.T3M.authSibOff c l' := if_pos h.2
    rw [e1, e2]
    exact ClaudeWCT.W9.T3M.auth_sib_disjoint c hc l h.1 l' h.2 hne
  · have a := auth6_ok c hc l hl
    have b := auth6_ok c hc l' hl'
    rcases (show l = 5 ∨ l' = 5 by omega) with e | e
    · have := a.2.2.2 e; have := b.2.2.1 (by omega); omega
    · have := b.2.2.2 e; have := a.2.2.1 (by omega); omega
theorem sdst_disj (c D k : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (l l' : Nat) (hl : l < 6) (hl' : l' < 6)
    (hne : l ≠ l') : sdst c D k l + 16 ≤ sdst c D k l' ∨ sdst c D k l' + 16 ≤ sdst c D k l := by
  have a := auth6_ok c hc l hl
  have b := auth6_ok c hc l' hl'
  have hd := auth_disj c hc l l' hl hl' hne
  have A1 : (l < 5 ∧ authSibOff c l + 16 ≤ 320) ∨ (l = 5 ∧ 832 ≤ authSibOff c l) := by
    by_cases h : l < 5
    · exact Or.inl ⟨h, a.2.2.1 h⟩
    · exact Or.inr ⟨by omega, a.2.2.2 (by omega)⟩
  have B1 : (l' < 5 ∧ authSibOff c l' + 16 ≤ 320) ∨ (l' = 5 ∧ 832 ≤ authSibOff c l') := by
    by_cases h : l' < 5
    · exact Or.inl ⟨h, b.2.2.1 h⟩
    · exact Or.inr ⟨by omega, b.2.2.2 (by omega)⟩
  unfold sdst sh
  rcases A1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases B1 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> split_ifs <;> omega
theorem sdst_bound (c D k l : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hl : l < 6) :
    D - 48 * k ≤ sdst c D k l ∧ sdst c D k l + 16 ≤ D + 896 ∧ sdst c D k l % 16 = (D - sh k l) % 16 := by
  obtain ⟨a1, a2, -, -⟩ := auth6_ok c hc l hl
  have := sh_le k l
  unfold sdst
  omega
theorem sibsMem_succ (M : Nat → Word) (c S D k L : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hL : L < 6) (A : Nat) :
    sibsMem M c S D k (L + 1) A =
      if A = sdst c D k L + 8 then M (S + srcOff c L + 8)
      else if A = sdst c D k L then M (S + srcOff c L) else sibsMem M c S D k L A := by
  unfold sibsMem
  rw [find_range_succ]
  cases h : (List.range L).find? (fun l => decide (A = sdst c D k l ∨ A = sdst c D k l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have hd := sdst_disj c D k hc hk l L (by omega) hL (by omega)
    simp only
    rw [if_neg (show ¬ A = sdst c D k L + 8 by omega), if_neg (show ¬ A = sdst c D k L by omega)]
  | none =>
    simp only
    by_cases h1 : A = sdst c D k L + 8
    · have h2 : ¬ A = sdst c D k L := by omega
      rw [if_pos (show decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h1]),
        if_pos h1]
      simp only
      rw [if_neg h2]
    · by_cases h2 : A = sdst c D k L
      · rw [if_pos (show decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h2]),
          if_neg h1, if_pos h2]
        simp only
        rw [if_pos h2]
      · rw [if_neg (show ¬ decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h1, h2]),
          if_neg h1, if_neg h2]
def zcMem (M : Nat → Word) (S D : Nat) (A : Nat) : Word :=
  if D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0 then M (S + 448 + (A - D - 320))
  else if D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0 then 0 else M A
/-- Staging region of coordinate `k` after its zero/copy calls and its six sibling stores (r3w: the sibling
stores of coordinate `k ≥ 2` land below `D`, in the previous region). -/
def coordMem (M : Nat → Word) (c S D k : Nat) (A : Nat) : Word := sibsMem (zcMem M S D) c S D k 6 A
theorem sibsMem_out (M : Nat → Word) (c S D k L : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hL : L ≤ 6) (A : Nat)
    (hA : A < D - 48 * k ∨ D + 896 ≤ A) : sibsMem M c S D k L A = M A := by
  unfold sibsMem
  cases h : (List.range L).find? (fun l => decide (A = sdst c D k l ∨ A = sdst c D k l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have := sdst_bound c D k l hc hk (by omega)
    omega
  | none => rfl
def sibsCyc (L : Nat) : Nat := 14 * L
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem sibs_spec (k : Nat) (hk : k < 9) (c S D : Nat) (hcl : c < 128) (hS : S % 16 = 0)
    (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0) (hDS : D + 896 ≤ S) (hDP : D + 896 ≤ PLAN)
    (hsh : 48 * k ≤ D) (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (coordAt k + 13)) (h8 : u.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : u.getReg .x9 = BitVec.ofNat 64 D) (h19 : u.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : u.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt u) :
    ∀ L ≤ 6, ∃ t, Steps im u (sibsCyc L) (sibsCyc L) t ∧ t.pc = pcOf (coordAt k + 13 + sibsCyc L) ∧
      RegsExcept u t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = sibsMem M0 c S D k L A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  intro L hL
  induction L with
  | zero => exact ⟨u, Steps.refl u, by simpa [sibsCyc] using hpc, RegsExcept.refl u _, fun A hA => hM A hA⟩
  | succ L ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hpL : t.pc = pcOf (sibAt k L) := by
      rw [pt, show coordAt k + 13 + sibsCyc L = sibAt k L by unfold sibAt sibsCyc; omega]
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega), sibsMem_out M0 c S D k L hcl hsh (by omega) _ (by omega), ← hM _ (by omega)]
      exact hp j hj
    obtain ⟨t', st', pt', rt', mt'⟩ := sib_spec hc k L hk (by omega) t hpL c S D hcl
      (by rw [rt.get (by decide), h8]) (by rw [rt.get (by decide), h9]) (by rw [rt.get (by decide), h19])
      (by rw [rt.get (by decide), h20]) hpt hS hS' hD (by omega) hsh
    have hcyc : sibsCyc L + sibLen L = sibsCyc (L + 1) := by unfold sibsCyc sibLen; split <;> omega
    refine ⟨t', (st.trans st').of_eq hcyc hcyc, ?_, (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    · rw [pt', show sibAt k L + sibLen L = coordAt k + 13 + sibsCyc (L + 1) by
        unfold sibAt; rw [← hcyc]; unfold sibsCyc; omega]
    · have hso := srcOff_bound c L
      rw [mt' A hA, sibsMem_succ M0 c S D k L hcl hsh (by omega) A, mt (S + srcOff c L + 8) (by omega),
        mt (S + srcOff c L) (by omega), mt A hA,
        sibsMem_out M0 c S D k L hcl hsh (by omega) (S + srcOff c L + 8) (Or.inr (by omega)),
        sibsMem_out M0 c S D k L hcl hsh (by omega) (S + srcOff c L) (Or.inr (by omega))]
set_option maxRecDepth 20000 in
theorem coord_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (hp : PlanAt s) (S D : Nat) (h8 : s.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN)
    (hS : S % 16 = 0) (hD : D % 16 = 0) (hDS : D + 896 ≤ S) (hS' : S + 1024 ≤ MEMORY_BYTES)
    (hDP : D + 896 ≤ PLAN) (hsh : 48 * k ≤ D) :
    ∃ t, Steps im s 707 707 t ∧ t.pc = pcOf (coordAt k + 111) ∧
      t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧ t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        holdMem (fun B => s.getMem (BitVec.ofNat 64 B)) (N.toNat / 2 ^ WCT9.childBase k % 128) S k A
          (coordMem (fun B => s.getMem (BitVec.ofNat 64 B)) (N.toNat / 2 ^ WCT9.childBase k % 128) S D k A) := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  obtain ⟨c, hcdef⟩ : ∃ c, c = N.toNat / 2 ^ WCT9.childBase k % 128 := ⟨_, rfl⟩
  rw [← hcdef]
  have hcl : c < 128 := by rw [hcdef]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨t1, s1, p1, r19, r11, r12, r1, g1, f1⟩ := head_spec hc k hk s hpc N hN D h9
  rw [← hcdef] at r19
  obtain ⟨t2, s2, p2, g2, m2⟩ := zero_spec hc t1 p1 D 40 (coordAt k + 6) r11 r12 r1 (by norm_num) (by norm_num)
    (by omega) (by omega)
  obtain ⟨t3, s3, p3, q10, q11, q12, q1, g3, f3⟩ := mid_spec hc k hk t2 p2 S D
    (by rw [g2.get (by decide), g1.get (by decide), h8]) (by rw [g2.get (by decide), g1.get (by decide), h9])
  obtain ⟨t4, s4, p4, g4, m4⟩ := copy_spec hc t3 p3 (S + 448) (D + 320) 72 (coordAt k + 10) q10 q11 q12 q1
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨t5, s5, p5, w20, g5, f5⟩ := row_spec hc k hk t4 p4 c hcl
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), r19])
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h18])
  have hz : ∀ X < 2 ^ 64, t3.getMem (BitVec.ofNat 64 X) = zeroed t1 D 40 X := fun X hX => by
    rw [f3 X hX (fun h => h), m2 X hX]
  have hM5 : ∀ A < 2 ^ 64, t5.getMem (BitVec.ofNat 64 A) =
      zcMem (fun B => s.getMem (BitVec.ofNat 64 B)) S D A := by
    intro A hA
    rw [f5 A hA (fun h => h), m4 A hA]
    unfold copied zcMem
    by_cases h1 : D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0
    · rw [if_pos (show D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0 by omega), if_pos h1,
        hz _ (by omega)]
      unfold zeroed
      rw [if_neg (by omega), f1 _ (by omega) (fun h => h),
        show S + 448 + (A - (D + 320)) = S + 448 + (A - D - 320) by omega]
    · rw [if_neg (show ¬ (D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0) by omega), if_neg h1,
        hz A hA]
      unfold zeroed
      by_cases h2 : D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0
      · rw [if_pos (show D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0 by omega), if_pos h2]
      · rw [if_neg (show ¬ (D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0) by omega), if_neg h2,
          f1 A hA (fun h => h)]
  have hp5 : PlanAt t5 := fun j hj => by
    rw [hM5 _ (by omega)]
    unfold zcMem
    rw [if_neg (show ¬ (D + 320 ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 896 ∧ (PLAN + 8 * j - D - 320) % 8 = 0) by omega),
      if_neg (show ¬ (D ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 320 ∧ (PLAN + 8 * j - D) % 8 = 0) by omega)]
    exact hp j hj
  have e8 : t5.getReg .x8 = BitVec.ofNat 64 S := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h8]
  have e9 : t5.getReg .x9 = BitVec.ofNat 64 D := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h9]
  have e19 : t5.getReg .x19 = BitVec.ofNat 64 c := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), r19]
  obtain ⟨t6, s6, p6, g6, m6⟩ := sibs_spec hc k hk c S D hcl hS (by omega) hD (by omega) (by omega) hsh t5 _ hM5
    p5 e8 e9 e19 w20 hp5 6 le_rfl
  obtain ⟨t6', s6', p6', g6', m6'⟩ := sib6_spec hc k hk t6
    (by rw [p6, show coordAt k + 13 + sibsCyc 6 = sibAt k 6 by unfold sibsCyc sibAt; omega]) c S hcl
    (by rw [g6.get (by decide), e8]) (by rw [g6.get (by decide), e19]) hS (by omega)
  obtain ⟨t7, s7, p7, w8, w9, g7, f7⟩ := step_spec hc k hk t6' p6' S D
    (by rw [g6'.get (by decide), g6.get (by decide), e8]) (by rw [g6'.get (by decide), g6.get (by decide), e9])
  have hzS : ∀ o, o < 448 → t6.getMem (BitVec.ofNat 64 (S + o)) = s.getMem (BitVec.ofNat 64 (S + o)) := by
    intro o ho
    rw [m6 _ (by omega), sibsMem_out _ c S D k 6 hcl hsh le_rfl _ (Or.inr (by omega))]
    unfold zcMem; rw [if_neg (by omega), if_neg (by omega)]
  have hso := srcOff_bound c 6
  refine ⟨t7, (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s6').trans s7).of_eq
    (by unfold sibsCyc; omega) (by unfold sibsCyc; omega), p7, w8, w9,
    (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g6').trans g7).mono (by decide),
    fun A hA => ?_⟩
  rw [f7 A hA (fun h => h), m6' A hA]
  unfold holdMem
  split_ifs
  · rfl
  · rw [show S + srcOff c 6 + 8 = S + (srcOff c 6 + 8) by omega, hzS _ (by omega)]
  · rw [hzS _ (by omega)]
  · rw [m6 A hA]; rfl
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
