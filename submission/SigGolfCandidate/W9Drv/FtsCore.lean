import SigGolfCandidate.W9Machine.WctN600Contract
import SigGolfCandidate.W9Machine.WctSourceWords
import SigGolfCandidate.W9Machine.WctPackedHeader
import SigGolfCandidate.W9Machine.WctTraceProgram
import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.W9Drv.Gate
import SigGolfCandidate.T3M.Verify.AfterDefs
import SigGolfCandidate.T3M.Verify.Common
import SigGolfCandidate.T3M.Images.Sizes

variable {choiceHint : BitVec 64}


set_option Elab.async false

section


namespace W9Machine.N600
def C1RanksEq : Prop := originalRanks = ClaudeWCT.WCT9.codeRanks
def C1CostsEq : Prop := rankCosts = ClaudeWCT.WCT9.routineCosts
def C1EmbedEq : Prop := embed = ClaudeWCT.WCT9.embed
def C1RankCostEq : Prop := rankCost = ClaudeWCT.WCT9.routineCost
def C1WordsEq : Prop :=
  originalRanks.map (fun r => (ClaudeWCT.WCT9.compositions 5 6 7).getD r []) =
    ClaudeWCT.WCT9.codeWords
def C1JointCostEq : Prop :=
  ∀ a : SigGolfCandidate.T3.HashOutput,
    JointCost (ClaudeWCT.WCT9.rank a) (ClaudeWCT.WCT9.child a) = ClaudeWCT.WCT9.jointCost a
def C1ProducerCapEq : Prop :=
  ∀ a : SigGolfCandidate.T3.HashOutput,
    ProducerCostOK (ClaudeWCT.WCT9.rank a) (ClaudeWCT.WCT9.child a) ↔ ClaudeWCT.WCT9.capOk a = true
end W9Machine.N600
end

section

namespace W9Machine.N600
set_option maxRecDepth 100000
theorem originalRanks_eq_c1 : C1RanksEq := rfl
theorem rankCosts_eq_c1 : C1CostsEq := rfl
theorem embed_eq_c1 : C1EmbedEq := by
  funext rank
  apply Fin.ext
  change originalRanks.getD rank.val 0 = _
  rw [show originalRanks = ClaudeWCT.WCT9.codeRanks from originalRanks_eq_c1,
    List.getD_eq_getElem _ _ (by rw [ClaudeWCT.WCT9.codeRanks_length]; exact rank.isLt)]
  rfl
theorem rankCost_eq_c1 : C1RankCostEq := by
  funext rank
  change rankCosts.getD rank.val 0 = _
  rw [show rankCosts = ClaudeWCT.WCT9.routineCosts from rankCosts_eq_c1,
    List.getD_eq_getElem _ _ (by rw [ClaudeWCT.WCT9.routineCosts_length]; exact rank.isLt)]
  rfl
theorem codeWords_eq_c1 : C1WordsEq := by
  change originalRanks.map _ = _
  rw [show originalRanks = ClaudeWCT.WCT9.codeRanks from originalRanks_eq_c1]
  exact ClaudeWCT.WCT9.codeRanks_map
end W9Machine.N600
namespace W9Machine.N600
theorem jointCost_eq_c1 : C1JointCostEq := by
  intro a
  unfold JointCost NineCost ClaudeWCT.WCT9.jointCost ClaudeWCT.WCT9.coordCost
  rw [rankCost_eq_c1, ← List.sum_map_add]
theorem producerCostOK_iff_c1 : C1ProducerCapEq := by
  intro a
  unfold ProducerCostOK ClaudeWCT.WCT9.capOk
  rw [jointCost_eq_c1 a, decide_eq_true_iff]
  rfl
end W9Machine.N600
end

section








section
namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
theorem digAt_of_eq {X Y : MachineState} {a : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 a) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (a + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y a d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
end W9Drv
end
end

section


namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def slotStart : Nat := 195584
def chainEntries : List Nat := Frozen.chainEntries
theorem slot_entries_all : (List.finRange 563).all (fun r =>
    decide (Frozen.layout.chainWord (N600.embed r) = slotStart + 64 * r.val)) = true := by
  decide +kernel
theorem slot_entry (r : Fin 563) : Frozen.layout.chainWord (N600.embed r) = slotStart + 64 * r.val :=
  of_decide_eq_true (List.all_eq_true.mp slot_entries_all r (List.mem_finRange r))
end W9Drv
end

section







section
set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def coordDispatch (p ld cpos fsh coord : Nat) (advance : Bool) : Result :=
  let raw : E := if coord ≥ 7 then .reg .x17 else if ld ≠ 0 then .ld (.c (BitVec.ofNat 64 ld)) else .reg .x16
  let dig := if ld ≠ 0 ∨ coord = 7 then mkBin .or raw (.reg .x24) else raw
  let cmask : E := if coord = 2 then .c (BitVec.ofNat 64 0x7f00000) else .reg .x27
  let child : E := if cpos = 0 then mkBin .and dig (.c 127)
    else if cpos = 57 then mkBin .srl dig (.c (BitVec.ofNat 64 57))
    else mkBin .and (mkBin .srl dig (.c (BitVec.ofNat 64 cpos))) (.c 127)
  let childSh20 : E := mkBin .and (mkBin .srl dig (.c 1)) cmask
  let pre := if advance then mkAdd (.reg .x15) (.reg .x6) else .reg .x15
  let packed := if coord = 2 ∨ coord = 8 then mkBin .or childSh20 pre else mkBin .or (mkBin .sll child (.c 20)) pre
  let childPc := if coord = 2 ∨ coord = 8 then mkAdd (mkBin .srl childSh20 (.c 12)) (.reg .x29)
    else mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let sh : E := if fsh = 5 then mkBin .sll dig (.c 1)
    else mkBin .srl dig (.c (BitVec.ofNat 64 (fsh - 6)))
  let field := mkBin .and sh (.reg .x2)
  let n := (if ld ≠ 0 then 1 else 0) + (if coord = 2 ∨ coord = 5 then 2 else 1) + (if advance then 9 else 7) + (if ld ≠ 0 ∨ coord = 7 then 1 else 0)
  let regs := if ld ≠ 0 then RegFile.init.set .x16 dig else RegFile.init
  let regs := if coord = 7 then regs.set .x17 dig else regs
  let regs := if coord = 2 then regs.set .x27 cmask else regs
  let regs := regs.set .x4 (if coord = 2 ∨ coord = 8 then childSh20 else child)
  let regs := if advance then regs.set .x15 pre else regs
  let regs := (regs.set .x31 packed).set .x23 childPc
  let regs := if advance then regs.set .x8 (addC (.reg .x8) (BitVec.ofNat 64 (2 ^ 64 - 896))) else regs
  let regs := (regs.set .x14 field).set .x1 (.c (pcOf (p + n)))
  ⟨⟨regs, [], []⟩, mkBin .and field (.c (~~~1#64)), .jump, n, n⟩
end W9Machine
end
section
namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWordsN (k : Nat) : List (BitVec 32) := [[0x7f87213,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0x181713,0x277733,0x700e7],[0x803803,0x1886833,0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xc8040413,0x181713,0x277733,0x700e7],[0x7f00db7,0x185213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xc8040413,0x1485713,0x277733,0x700e7],[0x3985213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xc8040413,0x2385713,0x277733,0x700e7],[0x1003803,0x1886833,0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xc8040413,0x181713,0x277733,0x700e7],[0x1585213,0x7f27213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xc8040413,0x1485713,0x277733,0x700e7],[0x3985213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xc8040413,0x2385713,0x277733,0x700e7],[0x188e8b3,0x7f8f213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xc8040413,0x189713,0x277733,0x700e7],[0x18d213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xc8040413,0x148d713,0x277733,0x700e7]].getD k []
def digWord (k : Nat) : Nat := [0,1,1,1,2,2,2,3,3].getD k 0
def ldOf (k : Nat) : Nat := [0,8,0,0,16,0,0,0,0].getD k 0
def cposOf (k : Nat) : Nat := [0,0,21,57,0,21,57,0,21].getD k 0
def fshOf (k : Nat) : Nat := [5,5,26,41,5,26,41,5,26].getD k 0
def dispatchLenN (k : Nat) : Nat := [8, 12, 11, 10, 12, 11, 10, 11, 10].getD k 0
def dispatchResultN (k : Nat) : Result :=
  coordDispatch (dispatchPc k) (ldOf k) (cposOf k) (fshOf k) k (decide (k ≠ 0))
theorem dispatch_all_checked : (List.range 9).all (fun k =>
    rOK (symRun {} (dispatchWordsN k) (pcOf (dispatchPc k)) (dispatchLenN k)) (dispatchResultN k)) = true := by
  decide +kernel
theorem dispatch_all_linked : (List.range 9).all (fun k => sliceChecked (dispatchPc k) (dispatchWordsN k)) = true := by
  decide +kernel
end W9Drv
end
section
namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchCode (k : Fin 9) : List (BitVec 32) := dispatchWordsN k.val
def dispatchLen (k : Fin 9) : Nat := dispatchLenN k.val
def dispatchResult (k : Fin 9) : Result := dispatchResultN k.val
theorem dispatch_checked (k : Fin 9) :
    rOK (symRun {} (dispatchCode k) (pcOf (dispatchPc k.val)) (dispatchLen k))
      (dispatchResult k) = true :=
  List.all_eq_true.mp dispatch_all_checked k.val (List.mem_range.mpr k.isLt)
theorem dispatch_linked (k : Fin 9) :
    sliceChecked (dispatchPc k.val) (dispatchCode k) = true :=
  List.all_eq_true.mp dispatch_all_linked k.val (List.mem_range.mpr k.isLt)
theorem dispatch_mem (k : Fin 9) (u : MachineState) (A : Word) :
    ((dispatchResult k).toState u).getMem A = u.getMem A := by
  fin_cases k <;> rfl
theorem dispatch_steps (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    Steps Frozen.image u (dispatchLen k) (dispatchLen k) ((dispatchResult k).toState u) := by
  have hs := symRun_sound (rOK_eq (dispatch_checked k))
    (slice_at _ _ (dispatch_linked k)) u hu.pc
  have hcost : (dispatchResult k).steps = dispatchLen k ∧
      (dispatchResult k).cycles = dispatchLen k := by
    fin_cases k <;> exact ⟨rfl, rfl⟩
  rw [hcost.1, hcost.2] at hs
  apply hs
  change Oblig.all u (dispatchResult k).st.obl
  rw [Oblig.all_iff]
  intro o ho
  have hobl : (dispatchResult k).st.obl = [] := by
    fin_cases k <;> rfl
  rw [hobl] at ho
  simp at ho
end W9Drv
end
section
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def chainEntryState (a : HashOutput) (k : Fin 9) (u : MachineState) : MachineState :=
  { (dispatchResult k).toState u with
    pc := pcOf (Frozen.layout.chainWord (N600.embed (ClaudeWCT.WCT9.rank a k))) }
theorem nat_and127 (n : Nat) : n &&& 127 = n % 128 := by
  have h := Nat.and_two_pow_sub_one_eq_mod n 7
  simpa using h
def childOfWord (k : Fin 9) (x : Word) : Word :=
  if cposOf k.val = 0 then x &&& 127#64 else if cposOf k.val = 57 then x >>> 57
  else (x >>> cposOf k.val) &&& 127#64
theorem dispatch_child (a : HashOutput) (k : Fin 9) :
    childOfWord k (a.extractLsb' (64 * digWord k.val) 64) =
      BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> simp [childOfWord, cposOf, digWord, ClaudeWCT.WCT9.child, ClaudeWCT.WCT9.childBase,
    BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    nat_and127, BitVec.toNat_ofNat] <;> omega
theorem childOfWord_pad (k : Fin 9) (x : Word) :
    childOfWord k (x ||| rankPad) = childOfWord k x := by
  fin_cases k <;> simp only [childOfWord, cposOf, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;> simp [rankPad]
def dispatchDig (k : Fin 9) : E :=
  let raw : E := if k.val ≥ 7 then .reg .x17 else
    if ldOf k.val ≠ 0 then .ld (.c (BitVec.ofNat 64 (ldOf k.val))) else .reg .x16
  if ldOf k.val ≠ 0 ∨ k.val = 7 then mkBin .or raw (.reg .x24) else raw
theorem dispatchDig_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchDig k).eval u = a.extractLsb' (64 * digWord k.val) 64 ||| rankPad := by
  have hd := hu.digest (digWord k.val) (by fin_cases k <;> decide)
  have hc := hu.cached
  have h3 := hu.cached3
  have hp := hu.jt
  fin_cases k <;> simp_all [dispatchDig, ldOf, digWord, cachedWord, mkBin_eval, E.eval, BinOp.eval]
def dispatchChild (k : Fin 9) : E :=
  if cposOf k.val = 0 then mkBin .and (dispatchDig k) (.c 127)
  else if cposOf k.val = 57 then mkBin .srl (dispatchDig k) (.c (BitVec.ofNat 64 57))
  else mkBin .and (mkBin .srl (dispatchDig k) (.c (BitVec.ofNat 64 (cposOf k.val)))) (.c 127)
theorem dispatchChild_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchChild k).eval u = BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  have hd := dispatchDig_eval pk w a k pairs u hu
  rw [← dispatch_child a k, ← childOfWord_pad, ← hd]
  fin_cases k <;> rfl
theorem dispatch_keep (k : Fin 9) (u : MachineState) (r : Reg)
    (hr : r ∉ [.x1,.x4,.x8,.x9,.x14,.x15,.x16,.x17,.x23,.x27,.x31]) :
    ((dispatchResult k).toState u).getReg r = u.getReg r := by
  rw [Result.toState_getReg]
  fin_cases k <;> cases r <;> first | exact False.elim (hr (by decide)) | rfl
theorem childSh20_eq (x : Word) :
    (x >>> 1) &&& 0x7f00000#64 = ((x >>> 21) &&& 127#64) <<< 20 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp
theorem childSh8_eq (x : Word) :
    ((x >>> 1) &&& 0x7f00000#64) >>> 12 = ((x >>> 21) &&& 127#64) <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp
theorem dispatch_childPC (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    ((dispatchResult k).toState u).getReg .x23 =
      ((dispatchChild k).eval u <<< 8) + u.getReg .x29 := by
  have hm := hu.childMask
  fin_cases k
  · rfl
  · rfl
  · change ((((dispatchDig 2).eval u >>> 1) &&& 0x7f00000#64) >>> 12) + u.getReg .x29 =
      (((dispatchDig 2).eval u >>> 21 &&& 127#64) <<< 8) + u.getReg .x29
    rw [childSh8_eq]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change ((((dispatchDig 8).eval u >>> 1) &&& u.getReg .x27) >>> 12) + u.getReg .x29 =
      (((dispatchDig 8).eval u >>> 21 &&& 127#64) <<< 8) + u.getReg .x29
    rw [hm (by decide), show BitVec.ofNat 64 0x7f00000 = 0x7f00000#64 from rfl, childSh8_eq]
theorem dispatch_x4 (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    ((dispatchResult k).toState u).getReg .x4 =
      if k.val = 2 ∨ k.val = 8 then (dispatchChild k).eval u <<< 20 else (dispatchChild k).eval u := by
  have hm := hu.childMask
  fin_cases k
  · rfl
  · rfl
  · change ((dispatchDig 2).eval u >>> 1) &&& 0x7f00000#64 =
      ((dispatchDig 2).eval u >>> 21 &&& 127#64) <<< 20
    rw [childSh20_eq]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change ((dispatchDig 8).eval u >>> 1) &&& u.getReg .x27 =
      ((dispatchDig 8).eval u >>> 21 &&& 127#64) <<< 20
    rw [hm (by decide), show BitVec.ofNat 64 0x7f00000 = 0x7f00000#64 from rfl, childSh20_eq]
theorem dispatch_node (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x15 =
      (if k.val = 0 then u.getReg .x15 else u.getReg .x15 + u.getReg .x6) := by
  fin_cases k <;> rfl
theorem dispatch_leaf (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    ((dispatchResult k).toState u).getReg .x31 =
      ((dispatchChild k).eval u <<< 20) ||| ((dispatchResult k).toState u).getReg .x15 := by
  have hm := hu.childMask
  fin_cases k
  · rfl
  · rfl
  · change (((dispatchDig 2).eval u >>> 1) &&& 0x7f00000#64) ||| ((dispatchResult 2).toState u).getReg .x15 =
      (((dispatchDig 2).eval u >>> 21 &&& 127#64) <<< 20) ||| ((dispatchResult 2).toState u).getReg .x15
    rw [childSh20_eq]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change (((dispatchDig 8).eval u >>> 1) &&& u.getReg .x27) ||| ((dispatchResult 8).toState u).getReg .x15 =
      (((dispatchDig 8).eval u >>> 21 &&& 127#64) <<< 20) ||| ((dispatchResult 8).toState u).getReg .x15
    rw [hm (by decide), show BitVec.ofNat 64 0x7f00000 = 0x7f00000#64 from rfl, childSh20_eq]
theorem nodeLow_value (k index : Nat) (hk : k < 9) (hi : index < 2 ^ 31) :
    V3.nodeLow k index = index * 2 ^ 27 + 1537 + 65536 * (k + 1) := by
  unfold V3.nodeLow ClaudeWCT.WCT9.ftsLeafLow
  rw [Nat.mod_eq_of_lt (by omega : k + 1 < 16), Nat.mod_eq_of_lt hi]
  omega
theorem dispatch_nodeWord (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    ((dispatchResult k).toState u).getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val (idxOf a)) := by
  have hi : idxOf a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  rw [dispatch_node, nodeLow_value _ _ k.isLt hi]
  by_cases hk0 : k.val = 0
  · rw [if_pos hk0, hu.nodeReg]
    apply congrArg (BitVec.ofNat 64)
    omega
  · rw [if_neg hk0, hu.nodeReg, hu.coordStep, show (65536 : BitVec 64) = BitVec.ofNat 64 65536 from rfl,
      ofNat_add_ofNat]
    apply congrArg (BitVec.ofNat 64)
    generalize idxOf a = x
    have := k.isLt
    omega
theorem shl_ofNat (x n : Nat) : BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x <<< n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]
theorem orAux (index j L : Nat) (hj : j < 2 ^ 7) (hL : L < 2 ^ 20) :
    j <<< 20 ||| (index * 2 ^ 27 + L) = index * 2 ^ 27 + j * 2 ^ 20 + L := by
  have e1 : index * 2 ^ 27 + L = (index <<< 7) <<< 20 ||| L := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hL, Nat.shiftLeft_eq, Nat.shiftLeft_eq]; ring
  have e3 : (index <<< 7) ||| j = index * 2 ^ 7 + j := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hj, Nat.shiftLeft_eq]
  rw [e1, ← Nat.or_assoc, Nat.or_comm (j <<< 20), ← Nat.shiftLeft_or_distrib, e3,
    ← Nat.shiftLeft_add_eq_or_of_lt hL, Nat.shiftLeft_eq]
  ring
theorem leafLow_or (index k j : Nat) (hk : k < 9) (hj : j < 128) (hi : index < 2 ^ 31) :
    (BitVec.ofNat 64 j <<< 20) ||| BitVec.ofNat 64 (V3.nodeLow k index) =
      BitVec.ofNat 64 (V3.leafLow index k j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    nodeLow_value k index hk hi, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega : j <<< 20 < 2 ^ 64),
    Nat.add_assoc, Nat.mod_eq_of_lt (by omega : index * 2 ^ 27 + (1537 + 65536 * (k + 1)) < 2 ^ 64),
    orAux index j _ (by omega) (by omega)]
  unfold V3.leafLow ClaudeWCT.WCT9.ftsLeafLow
  rw [Nat.mod_eq_of_lt (by omega : k + 1 < 16), Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  have : index * 2 ^ 27 + j * 2 ^ 20 + (1537 + 65536 * (k + 1)) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
theorem dispatch_x9 (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x9 = u.getReg .x9 := by
  fin_cases k <;> rfl
theorem dispatch_chain_pre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    N600.Pre Frozen.layout (V3.viewW w k.val u) (idxOf a) k (ClaudeWCT.WCT9.child a k) (ClaudeWCT.WCT9.rank a k)
      (chainEntryState a k u) := by
  have hm (A : Word) : (chainEntryState a k u).getMem A = u.getMem A := rfl
  have hr (r : Reg) (h : r ∉ [.x1,.x4,.x8,.x9,.x14,.x15,.x16,.x17,.x23,.x27,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hc := dispatchChild_eval pk w a k pairs u hu
  have hi : idxOf a < 2^31 := ClaudeWCT.WCT9.digestIndex_lt a
  have hj := (ClaudeWCT.WCT9.child a k).isLt
  have hnode := dispatch_nodeWord pk w a k pairs u hu
  refine {
    indexBound := hi
    pc := rfl
    baseReg := ?_
    leafWord := ?_
    nodeWord := hnode
    childIdx := by
      change ((dispatchResult k).toState u).getReg .x4 = _
      rw [dispatch_x4 pk w a k pairs u hu, hc]
      fin_cases k
      · rfl
      · rfl
      · exact shl_ofNat _ 20
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact shl_ofNat _ 20
    hashMode := (hr .x5 (by decide)).trans (hu.glob.1 (.x5, 0) (by simp))
    stepOne := (hr .x7 (by decide)).trans hu.stepOne
    stepTwo := (hr .x13 (by decide)).trans hu.stepTwo
    hashLen := (hr .x11 (by decide)).trans hu.hashLen
    childPC := ?_
    returnPC := ?_
    heaps := ?_
    witness := by
      intro off ho h8
      rw [hm]
      have hk := k.isLt
      have hr8 := V3.regionOffset_mod k.val
      have hrl := V3.regionOffset_le k.val
      rw [V3.view_word w k.val u _ (by omega) (by unfold V3.regionOffset; omega)]
      by_cases hh : V3.isHand off
      · rw [if_pos ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hh⟩]
        congr 2
        unfold Chain.base coordinateBase V3.regionOffset
        omega
      · rw [if_neg (fun h => hh (by rw [Nat.add_sub_cancel_left] at h; exact h.2))]
        have hw := hu.coords k.val (Nat.le_refl _) (by omega) off ho h8 (by omega) (fun _ => hh)
        have he : regionAddr k.val + off - 0x4c0 = V3.regionOffset k.val + off := by
          unfold regionAddr V3.regionOffset; omega
        have hb : Chain.base k + off = regionAddr k.val + off := by
          unfold Chain.base coordinateBase regionAddr; omega
        rw [hb]
        simpa only [W9Machine.OrigW, he] using hw }
  · change ((dispatchResult k).toState u).getReg .x8 = _
    have hb := hu.baseReg
    fin_cases k <;> simp [dispatchResult, dispatchResultN, coordDispatch, ldOf, cposOf, fshOf, dispatchPc,
      Result.toState_getReg, RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hb, Chain.base,
      coordinateBase]
  · change ((dispatchResult k).toState u).getReg .x31 = _
    rw [dispatch_leaf pk w a k pairs u hu, hc, hnode]
    exact leafLow_or _ _ _ k.isLt hj hi
  · change ((dispatchResult k).toState u).getReg .x23 = _
    rw [dispatch_childPC pk w a k pairs u hu, hc, hu.childBlock]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Frozen.layout, pcOf]
    omega
  · change ((dispatchResult k).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h2 h7)
end W9Drv
end
section
namespace W9Drv
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem aligned_clear_low (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0
    simp
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]
    simp [h]
  · simp [h0, hj]
theorem field_mask8 (x : BitVec 64) :
    x &&& 261888#64 = ((x >>> 8) &&& 1023#64) <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp
theorem nat_and1023 (n : Nat) : n &&& 1023 = n % 1024 := by
  have h := Nat.and_two_pow_sub_one_eq_mod n 10
  simpa using h
def shiftW (k : Fin 9) (x : Word) : Word :=
  if fshOf k.val = 5 then x <<< 1 else x >>> (fshOf k.val - 6)
def shiftE (k : Fin 9) (d : E) : E :=
  if fshOf k.val = 5 then mkBin .sll d (.c 1)
  else mkBin .srl d (.c (BitVec.ofNat 64 (fshOf k.val - 6)))
theorem shiftE_eval (k : Fin 9) (d : E) (u : MachineState) :
    (shiftE k d).eval u = shiftW k (d.eval u) := by
  fin_cases k <;> simp [shiftE, shiftW, fshOf, mkBin_eval, BinOp.eval] <;> rfl
theorem dispatch_field (a : HashOutput) (k : Fin 9) :
    shiftW k (a.extractLsb' (64 * digWord k.val) 64) &&& 261888#64 =
      BitVec.ofNat 64 (256 * ClaudeWCT.WCT9.field a k) := by
  rw [field_mask8]
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> simp [shiftW, fshOf, digWord, ClaudeWCT.WCT9.field, ClaudeWCT.WCT9.fieldBase,
    BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat, nat_and1023] <;> omega
theorem shiftW_pad (k : Fin 9) (x : Word) :
    shiftW k (x ||| rankPad) &&& 1048320#64 =
      (shiftW k x &&& 261888#64) ||| 786432#64 := by
  fin_cases k <;> simp only [shiftW, fshOf, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;> simp [rankPad]
theorem dispatch_pc (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    ((dispatchResult k).toState u).pc = pcOf (slotStart + 64 * ClaudeWCT.WCT9.field a k) := by
  have he : ((dispatchResult k).toState u).pc =
      (mkBin .and (mkBin .and (shiftE k (dispatchDig k)) (.reg .x2))
      (.c (~~~1#64))).eval u := by
    fin_cases k <;> rfl
  rw [he]
  simp only [mkBin_eval, E.eval, BinOp.eval, hu.mask]
  rw [shiftE_eval, dispatchDig_eval pk w a k roots u hu]
  rw [shiftW_pad, dispatch_field]
  have hf : ClaudeWCT.WCT9.field a k < 1024 := by unfold ClaudeWCT.WCT9.field; omega
  rw [ofNat_or_disjoint' (256 * ClaudeWCT.WCT9.field a k) 786432 18 (by omega) (by decide),
    aligned_clear_low _ (by omega)]
  unfold slotStart pcOf
  congr 1
  omega
theorem codeAt_single (pc : Nat) (words : List (BitVec 32))
    (hb : pc + words.length < 257214)
    (hc : CodeAt Frozen.image (pcOf pc) words) (i : Nat) (hi : i < words.length) :
    CodeAt Frozen.image (pcOf (pc + i)) [words[i]] := by
  have hp : (pcOf pc).toNat = 4096 + 4 * pc := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  have hpi : (pcOf (pc + i)).toNat = 4096 + 4 * (pc + i) := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [hpi]; omega, by rw [hpi]; omega, by rw [hpi]; simp; omega, ?_⟩
  have hpre := hc.2.2.2.drop i
  have hs : [words[i]] <+: words.drop i := by
    rw [List.singleton_prefix_iff_head?_eq_some]
    simp [List.head?_drop, hi]
  have ht := hs.trans hpre
  simpa [hp, hpi, List.drop_drop, Nat.add_comm] using ht
theorem fetch_past (s : MachineState) (p : Nat) (hp : s.pc = pcOf p) (hL : 257258 ≤ p)
    (hb : p < 2 ^ 40) : fetch Frozen.image s = none := by
  have hlen : Frozen.image.code.length = 257258 := by
    rw [Frozen.image_code_eq]; exact SigGolfCandidate.T3M.Images.verifyCode_length
  have ht : s.pc.toNat = 0x1000 + 4 * p := by
    rw [hp]; simp only [pcOf, BitVec.toNat_ofNat]; omega
  have hn : Frozen.image.code[p]? = none := List.getElem?_eq_none (by omega)
  unfold fetch
  simp [ht, hn]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem invalid_slot_checked :
    ((List.range' 563 400).all fun r => sliceChecked (slotStart + 64*r) [0]) = true := by
  decide +kernel
theorem fetch_invalid_last (s : MachineState) (hp : s.pc = pcOf 257216) :
    fetch Frozen.image s = none := by
  have hz : Frozen.image.code[257216]? = some (0 : BitVec 32) := by
    rw [Frozen.image_code_eq]
    exact SigGolfCandidate.T3M.Verify.vlook_ok 257216 0 (by decide +kernel)
  unfold fetch
  rw [hp]
  change (Frozen.image.code[257216]? >>= decodeInstruction) = none
  rw [hz]
  rfl
theorem fetch_invalid_slot (s : MachineState) (r : Nat)
    (hp : s.pc = pcOf (slotStart + 64*r)) (hlo : 563 ≤ r) (hhi : r < 1024) :
    fetch Frozen.image s = none := by
  by_cases h : r < 963
  · have hc : sliceChecked (slotStart + 64*r) [0] = true :=
      List.all_eq_true.mp invalid_slot_checked r (List.mem_range'_1.mpr ⟨hlo, by omega⟩)
    exact (slice_at _ _ hc).fetch s hp
  · by_cases he : r = 963
    · subst r
      exact fetch_invalid_last s hp
    · exact fetch_past s _ hp (by unfold slotStart; omega) (by unfold slotStart; omega)
theorem goodQFor_fault {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch Frozen.image s = none) :
    GoodQFor (choiceHint := choiceHint) Frozen.image s 1 0 Q A (pure (false, 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_fetch_none (F - 1) hf, map_pure]; rfl
  · have he : evalWithAnswerFn hash (Riscv.execute (F - 1 + 1) Frozen.image s) = ⟨.failure, s, 0, 0, 0⟩ := by
      rw [execute_fetch_none (F - 1) hf]; rfl
    rw [hF', he]
    exact ⟨by simp, Nat.zero_le _, fun h _ => by simp at h⟩
end W9Drv
end
section
set_option maxHeartbeats 400000
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open W9Machine
set_option maxHeartbeats 1600000 in
theorem coord_core_good (chains : N600.AllGood (choiceHint := choiceHint) Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good (choiceHint := choiceHint) Frozen.layout ⟨38, 95, 95 - ClaudeWCT.WCT9.childSave j.val⟩ j)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 563)
    (v u : MachineState) (padL padZ : Digest) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs)
    (hu : N600.Pre Frozen.layout (V3.viewW w k.val v) index k j rank u)
    (hL : DigAt v (0x4c0 + V3.regionOffset k.val + 720) padL)
    (hZ : DigAt v (0x4c0 + V3.regionOffset k.val + 864) padZ)
    (hnext : ∀ ends entry, Chain.Post Frozen.layout (V3.viewW w k.val v) index k j u ends entry →
      ∀ computed t, Child.Post Frozen.layout k j entry computed t →
        GoodQFor (choiceHint := choiceHint) Frozen.image t N C Q A (K computed)) :
    GoodQFor (choiceHint := choiceHint) Frozen.image u (N + 127) (C + 184) Q
      (A + (N600.rankCost rank + (95 - ClaudeWCT.WCT9.childSave j.val)))
      (ccM (N600.program w index k j rank >>= fun ends => V3.childN w index k j ends padL padZ) K) := by
  have hspec : (N600.program w index k j rank >>= fun ends => V3.childN w index k j ends padL padZ) =
      (N600.program (V3.viewW w k.val v) index k j rank >>= fun ends =>
        V3.childProgram (V3.viewW w k.val v) index k j ends) := by
    unfold N600.program
    rw [V3.chainProgram_view]
    simp only [V3.childProgram_view w index k v j _ padL padZ hL hZ]
  rw [hspec, ccM_bind]
  have hc := chains rank (V3.viewW w k.val v) index k j u (N+38) (C+95) (A+(95 - ClaudeWCT.WCT9.childSave j.val)) Q
    (fun ends => ccM (V3.childProgram (V3.viewW w k.val v) index k j ends) K) hu
    (fun ends entry hp => childs j (V3.viewW w k.val v) index k ends entry N C A Q K hp.child
      (hnext ends entry hp))
  convert hc using 1 <;> first | rfl | omega
end W9Drv
end
section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
/-- Nested FTS: one coordinate of the machine-level FTS (chains, nested child, top pair ordered by bit 6). -/
def coordN (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 563)
    (prev : Digest × Digest) : M (Digest × Digest) := do
  let ends ← N600.program w index k j rank
  let top ← V3.childN w index k j ends prev.1 prev.2
  let other := V3.topOther w k.val j.val
  pure (if j.val / 64 % 2 = 0 then (top, other) else (other, top))
def stepN (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (state : Option (List (Digest × Digest)))
    (k : Fin 9) : M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if !ClaudeWCT.W9.T3M.fieldOk a k then return none
  let pair ← coordN w (idxOf a) k (ClaudeWCT.WCT9.child a k) (ClaudeWCT.WCT9.rank a k) (prevOf w pairs)
  pure (some (pairs ++ [pair]))
/-- The machine-level nested FTS: the last coordinate's top pair. -/
def ftsN (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) : M (Option (Digest × Digest)) := do
  let some pairs ← (List.finRange 9).foldlM (stepN w a) (some []) | pure none
  pure (some (prevOf w pairs))
/-- Writes of coordinate `n`: its region (and the 16 bytes above, the level-5 right-output spill) and one of the
two hand-off slots of region `n + 1`. -/
def coordW (n j : Nat) (A : Nat) : Prop :=
  (regionAddr n ≤ A ∧ A < regionAddr n + 912) ∨
    (if j / 64 % 2 = 0 then regionAddr n - 192 ≤ A ∧ A < regionAddr n - 160
      else regionAddr n - 48 ≤ A ∧ A < regionAddr n - 16)
theorem coord_frame (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9) (v u entry t : MachineState)
    (ends : List Digest) (computed : Digest)
    (hp : Chain.Post Frozen.layout (V3.viewW w k.val v) (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k (ClaudeWCT.WCT9.child a k) entry computed t) :
    Frame u t (coordW k.val (ClaudeWCT.WCT9.child a k).val) := by
  have hk := k.isLt
  intro A hA hn
  unfold coordW regionAddr at hn
  rw [ht.frame A hA (by
    unfold Child.writes Child.handAddr coordinateBase
    split_ifs at hn ⊢ <;> omega)]
  exact hp.frame A hA (by unfold Chain.writes Chain.base coordinateBase; omega)
theorem prevOf_snoc (w : ClaudeWCT.W9.T3M.WBytes) (pairs : List (Digest × Digest)) (p : Digest × Digest) :
    prevOf w (pairs ++ [p]) = p := by
  unfold prevOf; simp
theorem regionAddr_succ (n : Nat) (hn : n < 9) : regionAddr n = regionAddr (n + 1) + 896 := by
  unfold regionAddr; omega
theorem coordW_bounds {n j A : Nat} (hn : n < 9) (h : coordW n j A) : 1200 ≤ A ∧ A < 9472 := by
  unfold coordW regionAddr at h; split_ifs at h <;> omega
set_option maxRecDepth 100000 in
/-- The witness top sibling of coordinate `k` survives in region `k + 1` (only the other hand-off slot is written). -/
theorem next_other (w : ClaudeWCT.W9.T3M.WBytes) (k : Fin 9) (j : Nat) (u t : MachineState)
    (hf : Frame u t (coordW k.val j)) (off : Nat) (hoff : off = 720 ∨ off = 864)
    (hsel : if j / 64 % 2 = 0 then off = 864 else off = 720)
    (h0 : W9Machine.OrigW w u (regionAddr (k.val + 1) + off))
    (h1 : W9Machine.OrigW w u (regionAddr (k.val + 1) + (off + 8))) :
    DigAt t (regionAddr (k.val + 1) + off) (V3.topOther w k.val j) := by
  have hk := k.isLt
  have h1' : W9Machine.OrigW w u (regionAddr (k.val + 1) + off + 8) := by rw [Nat.add_assoc]; exact h1
  have hlo : 0x4c0 ≤ regionAddr (k.val + 1) + off := by unfold regionAddr; omega
  have hdig := W9Machine.DigAt_origW h0 h1' hlo
  have he : regionAddr (k.val + 1) + off - 0x4c0 = V3.topOtherOff k.val j := by
    unfold V3.topOtherOff V3.regionOffset regionAddr
    split_ifs at hsel ⊢ <;> omega
  rw [he] at hdig
  refine hdig.frame hf (by unfold regionAddr; omega) ?_ ?_
  · intro hw; unfold coordW regionAddr at hw; split_ifs at hsel hw <;> omega
  · intro hw; unfold coordW regionAddr at hw; split_ifs at hsel hw <;> omega
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
/-- The previous-pair slots after coordinate `n`: the computed node at its hand-off slot, the other one is the
witness top sibling. -/
theorem coord_next (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hu : CoordPre pk w a k.val pairs u)
    (hp : Chain.Post Frozen.layout (V3.viewW w k.val u) (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k (ClaudeWCT.WCT9.child a k) entry computed t) :
    CoordPre pk w a (k.val+1) (pairs ++ [if (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 0
      then (computed, V3.topOther w k.val (ClaudeWCT.WCT9.child a k).val)
      else (V3.topOther w k.val (ClaudeWCT.WCT9.child a k).val, computed)]) t := by
  have hk := k.isLt
  have hc := dispatch_chain_pre pk w a k pairs u hu
  have hf := coord_frame w a k u u entry t ends computed hp ht
  have hm (A : Nat) (hA : A < 2^64) (hs : A < 1200 ∨ 9472 ≤ A) :
      t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    intro hw
    have := coordW_bounds hk hw
    omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      t.getReg r = (chainEntryState a k u).getReg r := by
    rw [ht.keep r (by
      simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x4,.x8,.x9,.x14,.x15,.x16,.x17,.x23,.x27,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hdr : ∀ i, 4 ≤ i → (i < 6 ∨ i = 13) → ¬ coordW k.val (ClaudeWCT.WCT9.child a k).val (WIT + 8 * i) := by
    intro i h4 h6 hw
    unfold coordW regionAddr WIT at hw
    split_ifs at hw <;> omega
  have hg : Glob [(.x5, 0)] w pk t := by
    obtain ⟨hreg, hh, hpk, hz, hhalf, hdata⟩ := hu.glob
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact (hr .x5 (by decide)).trans ((hd .x5 (by decide)).trans (hreg (.x5, 0) (by simp)))
    · intro j hj4 hj
      rw [hf _ (by unfold WIT; omega) (hdr j hj4 hj)]
      exact hh j hj4 hj
    · exact ⟨(hm 160 (by decide) (Or.inl (by omega))).trans hpk.1,
        (hm 168 (by decide) (Or.inl (by omega))).trans hpk.2⟩
    · intro A hA
      have hb : A < 1200 := by simp [pSlots] at hA; omega
      exact (hm A (by omega) (Or.inl hb)).trans (hz A hA)
    · change (t.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hm CTRW (by decide) (Or.inl (by decide))]
      exact hhalf
    · refine ⟨?_, fun lay hl => ?_, ?_⟩
      · rw [hm (TOPBASE-8) (by unfold TOPBASE; omega) (Or.inr (by unfold TOPBASE; omega))]
        exact hdata.mask
      · have hb := hdrAddr_bounds lay
        rw [hm (hdrAddr lay) (by unfold TOPBASE at *; omega) (Or.inr (by unfold TOPBASE at *; omega))]
        exact hdata.header lay hl
      · rw [hm (TOPB9+56) (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))]
        exact hdata.buffer3
  have hb6 : (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 0 ∨ (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 1 := by omega
  have hra := regionAddr_succ k.val hk
  have hbase : coordinateBase k = regionAddr k.val := by unfold coordinateBase regionAddr; omega
  have hR9 : regionAddr (k.val + 1) ≥ 496 := by unfold regionAddr; omega
  -- the other top sibling, from the witness (region k+1 is untouched outside one hand-off slot)
  have hother : ∀ off, (off = 720 ∨ off = 864) →
      (if (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 0 then off = 864 else off = 720) →
      DigAt t (regionAddr (k.val + 1) + off) (V3.topOther w k.val (ClaudeWCT.WCT9.child a k).val) := by
    intro off hoff hsel
    exact next_other w k _ u t hf off hoff hsel
      (hu.coords (k.val + 1) (by omega) (by omega) off (by omega) (by omega) (fun _ => by omega)
        (fun h => by omega))
      (hu.coords (k.val + 1) (by omega) (by omega) (off + 8) (by omega) (by omega) (fun _ => by omega)
        (fun h => by omega))
  have htop : DigAt t (Child.handAddr k (ClaudeWCT.WCT9.child a k)) computed := ht.top
  refine {
    le := by omega
    length := by simp [hu.length]
    pc := ?_
    glob := hg
    digest := fun i hi => (hm _ (by omega) (Or.inl (by omega))).trans (hu.digest i hi)
    bank := ?_
    forest := ?_
    index := (hr .x22 (by decide)).trans ((hd .x22 (by decide)).trans hu.index)
    heaps := ?_
    stepOne := (hr .x7 (by decide)).trans hc.stepOne
    stepTwo := (hr .x13 (by decide)).trans hc.stepTwo
    hashLen := ht.hashLen
    coordStep := (hr .x6 (by decide)).trans ((hd .x6 (by decide)).trans hu.coordStep)
    nodeReg := ?_
    d0 := (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.d0
    cached3 := ?_
    cached := ?_
    mask := (hr .x2 (by decide)).trans ((hd .x2 (by decide)).trans hu.mask)
    childMask := ?_
    jt := (hr .x24 (by decide)).trans ((hd .x24 (by decide)).trans hu.jt)
    childBlock := (hr .x29 (by decide)).trans ((hd .x29 (by decide)).trans hu.childBlock)
    baseReg := ?_
    pairPtr := ?_
    prevL := ?_
    prevR := ?_
    a2 := ?_
    coords := ?_
    layer := ?_ }
  · rw [ht.pc]
    fin_cases k <;> rfl
  · refine ⟨?_, ?_⟩
    · intro i hi
      exact (hm _ (by unfold TOPLOAD; omega) (Or.inr (by unfold TOPLOAD; omega))).trans (hu.bank.top i hi)
    · exact (hm _ (by unfold TOPLOAD; omega) (Or.inr (by unfold TOPLOAD; omega))).trans hu.bank.top8
  · refine ⟨?_, ?_, ?_⟩
    · exact (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.forest.zero0
    · exact (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.forest.zero1
    · exact (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.forest.header
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hc.heaps h h2 h7)
  · rw [hr .x15 (by decide), show k.val + 1 - 1 = k.val by omega]
    change ((dispatchResult k).toState u).getReg .x15 = _
    rw [dispatch_nodeWord pk w a k pairs u hu,
      nodeLow_value _ _ k.isLt (ClaudeWCT.WCT9.digestIndex_lt a)]
    apply congrArg (BitVec.ofNat 64)
    change ClaudeWCT.WCT9.digestIndex a * 2 ^ 27 + 1537 + 65536 * (k.val + 1) =
      ClaudeWCT.WCT9.digestIndex a * 2 ^ 27 + 67073 + 65536 * k.val
    omega
  · rw [hr .x17 (by decide)]
    have h3 := hu.cached3
    have hj := hu.jt
    fin_cases k <;> first | exact h3 | exact congrArg₂ (fun x y : Word => x ||| y) h3 hj
  · rw [hr .x16 (by decide)]
    have hd1 := hu.digest 1 (by decide)
    have hd2 := hu.digest 2 (by decide)
    have hcache := hu.cached
    have hj := hu.jt
    fin_cases k <;> first | exact hcache | exact congrArg₂ (fun x y : Word => x ||| y) hd1 hj | exact congrArg₂ (fun x y : Word => x ||| y) hd2 hj
  · intro hk3
    rw [hr .x27 (by decide)]
    have hcm := hu.childMask
    fin_cases k <;> first | exact absurd hk3 (by decide) | rfl | exact hcm (by decide)
  · rw [hr .x8 (by decide), show k.val + 1 - 1 = k.val by omega]
    have hb := hc.baseReg
    simp only [Chain.base, coordinateBase] at hb
    rw [hb]
    congr 1
    try omega
  · rw [hr .x9 (by decide)]
    exact (dispatch_x9 k u).trans hu.pairPtr
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      have e : Child.handAddr k (ClaudeWCT.WCT9.child a k) = regionAddr (k.val + 1) + 720 := by
        unfold Child.handAddr; rw [if_pos h0, hbase]; omega
      rw [← e]; exact htop
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      exact hother 720 (Or.inl rfl) (by rw [if_neg (by omega)])
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      exact hother 864 (Or.inr rfl) (by rw [if_pos h0])
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      have e : Child.handAddr k (ClaudeWCT.WCT9.child a k) = regionAddr (k.val + 1) + 864 := by
        unfold Child.handAddr; rw [if_neg (by omega), hbase]; omega
      rw [← e]; exact htop
  · intro _
    have h12 := ht.a2
    unfold Child.handAddr at h12
    rw [hbase] at h12
    split_ifs at h12
    · left; rw [h12]; congr 1; unfold regionAddr; omega
    · right; rw [h12]; congr 1; unfold regionAddr; omega
  · intro m hm1 hm9 off hoff h8 hv hh
    have h0 := hu.coords m (by omega) hm9 off hoff h8 hv (fun h => by omega)
    unfold W9Machine.OrigW at h0 ⊢
    rw [← h0]
    apply hf _ (by unfold regionAddr; omega)
    intro hw
    unfold coordW at hw
    have hmk : regionAddr m + 896 ≤ regionAddr k.val := by unfold regionAddr; omega
    rcases Nat.lt_or_ge (k.val + 1) m with hgt | hle
    · have : regionAddr m + 896 ≤ regionAddr (k.val + 1) := by unfold regionAddr; omega
      split_ifs at hw <;> omega
    · have hm' : m = k.val + 1 := by omega
      subst hm'
      have hn := hh rfl
      unfold V3.isHand at hn
      split_ifs at hw <;> omega
  · exact hu.layer.frame (fun j hj h => hf _ (by unfold WIT WX at *; omega)
      (by intro hw; unfold coordW regionAddr WIT at *; split_ifs at hw <;> omega))
set_option maxHeartbeats 1600000 in
theorem coord_good (chains : N600.AllGood (choiceHint := choiceHint) Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good (choiceHint := choiceHint) Frozen.layout ⟨38, 95, 95 - ClaudeWCT.WCT9.childSave j.val⟩ j)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Option (List (Digest × Digest)) → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a k.val pairs u) (hnone : K none = pure (false, 0))
    (hnext : ∀ pair t, CoordPre pk w a (k.val + 1) (pairs ++ [pair]) t →
      GoodQFor (choiceHint := choiceHint) Frozen.image t N C Q A (K (some (pairs ++ [pair])))) :
    GoodQFor (choiceHint := choiceHint) Frozen.image u (N + (dispatchLen k + 184))
      (C + (dispatchLen k + 184)) Q (A + ((dispatchLen k + 89) + (N600.rankCost (ClaudeWCT.WCT9.rank a k) +
        ClaudeWCT.WCT9.childExtra (ClaudeWCT.WCT9.child a k))))
      (ccM (stepN w a (some pairs) k) K) := by
  have ds := dispatch_steps pk w a k pairs u hu
  have hpc := dispatch_pc pk w a k pairs u hu
  have hfb : ClaudeWCT.WCT9.field a k < 1024 := by
    unfold ClaudeWCT.WCT9.field; omega
  by_cases hok : ClaudeWCT.W9.T3M.fieldOk a k = true
  · have hfield : ClaudeWCT.WCT9.field a k < 563 := by
      exact of_decide_eq_true hok
    have hrank : (ClaudeWCT.WCT9.rank a k).val = ClaudeWCT.WCT9.field a k := by
      simp only [ClaudeWCT.WCT9.rank]; exact Nat.mod_eq_of_lt hfield
    have hst : chainEntryState a k u = (dispatchResult k).toState u := by
      unfold chainEntryState
      rw [slot_entry, hrank, ← hpc]
    have hk := k.isLt
    have hreg : 0x4c0 + V3.regionOffset k.val = regionAddr k.val := by
      unfold V3.regionOffset regionAddr; omega
    have core := coord_core_good chains childs w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (ClaudeWCT.WCT9.rank a k) u (chainEntryState a k u) (prevOf w pairs).1 (prevOf w pairs).2 N C A Q
      (fun top => K (some (pairs ++ [if (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 0
        then (top, V3.topOther w k.val (ClaudeWCT.WCT9.child a k).val)
        else (V3.topOther w k.val (ClaudeWCT.WCT9.child a k).val, top)])))
      (dispatch_chain_pre pk w a k pairs u hu) (by rw [hreg]; exact hu.prevL) (by rw [hreg]; exact hu.prevR)
      (fun ends entry hp computed t ht => hnext _ _ (coord_next pk w a k pairs u entry t ends computed hu hp ht))
    rw [hst] at core
    have full := core.steps ds
    have hce := ClaudeWCT.WCT9.childExtra_add (ClaudeWCT.WCT9.child a k)
    have hmx : ClaudeWCT.WCT9.maxChildSave = 6 := rfl
    simp only [stepN, coordN, hok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, ccM_bind, ccM_pure, bind_assoc, pure_bind]
    simp only [ccM_bind, ccM_pure] at full
    convert full.mono (N' := N + (dispatchLen k + 184)) (C' := C + (dispatchLen k + 184))
      (A' := A + ((dispatchLen k + 89) + (N600.rankCost (ClaudeWCT.WCT9.rank a k) +
        ClaudeWCT.WCT9.childExtra (ClaudeWCT.WCT9.child a k)))) (by omega) (by omega)
      (fun hq => ⟨hq, by omega⟩) using 3
    all_goals (funext top; split_ifs <;> rfl)
  · have hfield : ¬ ClaudeWCT.WCT9.field a k < 563 := by
      intro hh
      exact hok (show decide (ClaudeWCT.WCT9.field a k < 563) = true from decide_eq_true hh)
    have hpast := fetch_invalid_slot _ _ hpc (by omega) hfb
    have rr : GoodQFor (choiceHint := choiceHint) Frozen.image ((dispatchResult k).toState u) 1 0 Q 0 (pure (false, 0)) :=
      goodQFor_fault hpast
    have full := rr.steps ds
    have hfalse : ClaudeWCT.W9.T3M.fieldOk a k = false := Bool.eq_false_iff.mpr hok
    simp only [stepN, hfalse, Bool.not_false, ↓reduceIte, ccM_pure, hnone]
    exact full.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
/-- The end of the nested FTS: coordinate 8 has handed its top pair to the virtual region below it. -/
theorem fts_final (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a 9 pairs u) :
    FtsOut ⟨pk, w, a⟩ (prevOf w pairs) u := by
  refine ⟨hu.glob, hu.index, ?_, ?_, ?_, ?_, ?_, hu.hashLen, hu.heaps 6 (by decide) (by decide), hu.stepOne,
    hu.stepTwo, hu.heaps 7 (by decide) (by decide), hu.heaps 3 (by decide) (by decide),
    hu.heaps 4 (by decide) (by decide), hu.heaps 5 (by decide) (by decide), hu.coordStep, hu.pairPtr,
    hu.bank.top, hu.bank.top8, ?_, hu.d0⟩
  · exact hu.pc
  · have h := hu.prevL
    rwa [show regionAddr 9 + 720 = WIT by unfold regionAddr WIT; rfl] at h
  · have h := hu.prevR
    rwa [show regionAddr 9 + 864 = WIT + 144 by unfold regionAddr WIT; rfl] at h
  · exact hu.layer
  · rw [hu.baseReg]; rfl
  · have h := hu.a2 (by decide)
    rwa [show regionAddr 9 + 704 = 1200 by unfold regionAddr; rfl,
      show regionAddr 9 + 848 = 1344 by unfold regionAddr; rfl] at h
def finishN (w : ClaudeWCT.W9.T3M.WBytes) (state : Option (List (Digest × Digest))) :
    M (Option (Digest × Digest)) :=
  match state with
  | none => pure none
  | some pairs => pure (some (prevOf w pairs))
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => dispatchLen k + 184)).sum
def coordsAccept (a : HashOutput) (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => (dispatchLen k + 89) + (N600.rankCost (ClaudeWCT.WCT9.rank a k) +
    ClaudeWCT.WCT9.childExtra (ClaudeWCT.WCT9.child a k)))).sum
theorem fold_none (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (stepN w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, stepN, pure_bind] using ih
theorem coordinates_good (chains : N600.AllGood (choiceHint := choiceHint) Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good (choiceHint := choiceHint) Frozen.layout ⟨38, 95, 95 - ClaudeWCT.WCT9.childSave j.val⟩ j)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (ks : List (Fin 9)) (n : Nat) (pairs : List (Digest × Digest)) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs)
    (horder : ks.map Fin.val = List.range' n ks.length) (hend : n + ks.length = 9)
    (hu : CoordPre pk w a n pairs u) (hnone : K none = pure (false, 0))
    (hnext : ∀ top t, FtsOut ⟨pk,w,a⟩ top t →
      GoodQFor (choiceHint := choiceHint) Frozen.image t N C Q A (K (some top))) :
    GoodQFor (choiceHint := choiceHint) Frozen.image u (N + coordsCost ks) (C + coordsCost ks) Q (A + coordsAccept a ks)
      (ccM (ks.foldlM (stepN w a) (some pairs) >>= finishN w) K) := by
  induction ks generalizing n pairs u with
  | nil =>
    have hn : n = 9 := by simpa using hend
    subst n
    simp only [List.foldlM_nil, pure_bind, finishN, ccM_pure]
    simpa [coordsCost, coordsAccept] using hnext _ u (fts_final pk w a pairs u hu)
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at horder
    obtain ⟨hn, ht⟩ := horder
    subst n
    let K' : Option (List (Digest × Digest)) → OracleComp HashSpec Obs := fun state =>
      ccM (ks.foldlM (stepN w a) state >>= finishN w) K
    have hkNone : K' none = pure (false, 0) := by
      simp only [K', fold_none, pure_bind, finishN, ccM_pure, hnone]
    have hstep := coord_good chains childs pk w a k pairs u (N + coordsCost ks)
      (C + coordsCost ks) (A + coordsAccept a ks) Q K' hu hkNone
      (fun pair t hh => ih (k.val + 1) (pairs ++ [pair]) t ht
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend) hh)
    simp only [List.foldlM_cons, bind_assoc, ccM_bind]
    convert hstep using 1 <;> simp [coordsCost, coordsAccept, Nat.add_left_comm, Nat.add_comm,
      K', ccM_bind] <;> omega
theorem coordsAccept_all (a : HashOutput) :
    coordsAccept a (List.finRange 9) = 896 + ClaudeWCT.WCT9.jointCost a := by
  unfold coordsAccept
  rw [List.sum_map_add]
  have hfixed : ((List.finRange 9).map (fun k => dispatchLen k + 89)).sum = 896 := by decide
  rw [hfixed]
  congr 1
  simp only [ClaudeWCT.WCT9.jointCost, ClaudeWCT.WCT9.coordCost,
    (show N600.rankCost = ClaudeWCT.WCT9.routineCost from N600.rankCost_eq_c1)]
end W9Drv
end
end

section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
/-- The FTS phase of the verifier refines the machine-level nested FTS `ftsN` (bridged to track A's `wctP`
in `W9Drv.SpecBridge`). -/
def FtsGoodByCost (acceptCost : HashOutput → Nat) : Prop :=
  ∀ (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs),
    GatePre pk w a u → K none = pure (false, 0) →
    (∀ top t, FtsOut ⟨pk,w,a⟩ top t →
      GoodQFor (choiceHint := choiceHint) Frozen.image t N C Q A (K (some top))) →
    GoodQFor (choiceHint := choiceHint) Frozen.image u (N+2023) (C+2023) Q (A+acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ftsN w a else pure none) K)
def ftsAcceptCost (a : HashOutput) : Nat := 918 + ClaudeWCT.WCT9.jointCost a
theorem fts_good_of (chains : N600.AllGood (choiceHint := choiceHint) Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good (choiceHint := choiceHint) Frozen.layout ⟨38, 95, 95 - ClaudeWCT.WCT9.childSave j.val⟩ j) :
    FtsGoodByCost (choiceHint := choiceHint) ftsAcceptCost := by
  intro pk w a u N C A Q K hu hnone hnext
  let KG : Bool → OracleComp HashSpec Obs := fun b =>
    if b then ccM (ftsN w a) K else K none
  have hg := gate_good pk w a u (N + 1751) (C + 1751) (A + (896 + ClaudeWCT.WCT9.jointCost a)) Q KG hu
    (by simpa only [KG, Bool.false_eq_true, ↓reduceIte] using hnone)
    (fun t ht => by
      have hc := coordinates_good chains childs pk w a (List.finRange 9) 0 [] t N C A Q K
        (by decide)
        (by simp) ht hnone hnext
      rw [show coordsCost (List.finRange 9) = 1751 by decide,
        show coordsAccept a (List.finRange 9) = 896 + ClaudeWCT.WCT9.jointCost a by
          rw [coordsAccept_all]] at hc
      apply hc.congr
      change ccM (_ >>= finishN w) K = ccM (ftsN w a) K
      apply congrArg (fun p : M (Option (Digest × Digest)) => ccM p K)
      unfold ftsN
      apply congrArg (fun f : Option (List (Digest × Digest)) → M (Option (Digest × Digest)) =>
        (List.finRange 9).foldlM (stepN w a) (some []) >>= f)
      funext state
      cases state <;> rfl)
  change GoodQFor (choiceHint := choiceHint) Frozen.image u (N + 1773) (C + 1773) Q (A + (896 + ClaudeWCT.WCT9.jointCost a) + 22)
    (KG (ClaudeWCT.W9.T3M.gateOk a)) at hg
  apply (hg.mono (by omega) (by omega) (fun hq => ⟨hq, by simp only [ftsAcceptCost]; omega⟩)).congr
  cases ClaudeWCT.W9.T3M.gateOk a <;> simp [KG, ccM_pure]
end W9Drv
end

/-! Nested FTS (r1-1): the machine-level FTS phase `W9Drv.ftsN` is track A's padded verifier FTS phase
`ClaudeWCT.W9.T3M.wctP`. The chain part reuses the frontier bridge; the tree part matches `V3.childN` (explicit
nested pads, high-half top node) against `wctCoordP`. -/

section
set_option autoImplicit false
namespace W9Machine
open OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT
theorem chainLow_canonical (index coord child chain step : Nat)
    (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128) (ht : chain < 6) (hs : step < 4) :
    V3.chainLow index coord child chain step = WCT9.ftsChainLow index coord child chain step := by
  rw [chainLow_add _ _ _ _ _ ht hs, chainPrefix_value _ _ _ hk hj]
  unfold WCT9.ftsChainLow
  rw [Nat.mod_eq_of_lt (by omega : chain < 8), Nat.mod_eq_of_lt (by omega : step < 4),
    Nat.mod_eq_of_lt (by omega : coord + 1 < 16), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi]
  omega
theorem chainInput_canonical (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 6) (hs : step < 4) :
    V3.chainInput index coord child chain step a b c value =
      ClaudeWCT.W9.T3M.wctChainInputP index coord child chain step a b c value := by
  change _ = blk4 a (WCT9.ftsChainHeaderP index coord child chain step b) c value
  rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
      (chainInput_length _ _ _ _ _ _ _ _ _),
    ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _),
    wordsOf_chainInput, wordsOf_blk4]
  simp only [dlo, dhi, WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high,
    chainLow_canonical _ _ _ _ _ hi hk hj ht hs]
theorem chainP_canonical (index coord child chain start count : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 6) (hbound : start + count ≤ 4) :
    V3.chainP index coord child chain start count a b c value =
      ClaudeWCT.W9.T3M.wctChainP index coord child chain start count a b c value := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
    simp only [V3.chainP, ClaudeWCT.W9.T3M.wctChainP, List.range'_succ, List.foldlM_cons]
    rw [chainInput_canonical _ _ _ _ _ _ _ _ _ hi hk hj ht (by omega)]
    congr 1
    funext v
    exact ih (start + 1) v (by omega)
def canonicalChains (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 666) :
    M (List Digest) :=
  (List.finRange 6).mapM fun t =>
    let d := WCT9.digit rank t
    ClaudeWCT.W9.T3M.wctChainP index k.val j.val t.val (4 - d) d
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).1
      (ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val)
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).2
      (ClaudeWCT.W9.T3M.wreveal w k.val t.val d)
theorem chainProgram_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 666) (hi : index < 2 ^ 31) :
    V3.chainProgram w index k j rank = canonicalChains w index k j rank := by
  unfold V3.chainProgram canonicalChains
  congr 1
  funext t
  have hd := WCT9.digit_le_four rank t
  rw [chainP_canonical _ _ _ _ _ _ _ _ _ _ hi k.isLt j.isLt t.isLt (by omega)]
  have hb : V3.chainPadB w k.val t.val = ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val := by
    simp only [V3.chainPadB, ClaudeWCT.W9.T3M.wcHeaderPad,
      V3.chainOffset, V3.regionOffset, ClaudeWCT.W9.T3M.wctChainBlock,
      ClaudeWCT.W9.T3M.regionBase, Nat.add_assoc]
    rw [show ClaudeWCT.W9.T3M.wdig w = W9Machine.wdig w from rfl, W9Machine.wdig_hi]
    congr 2 <;> omega
  rw [hb]
  rfl
end W9Machine
end
section
set_option autoImplicit false
namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open OracleComp
open SigGolfCandidate.T3 (Digest HashOutput M shortHash header)
open SphincsSecurity (bytesLE bytesLE_length)
theorem nodeHdr_canonical (k : Fin 9) (index heap : Nat) (hp : BitVec 64) :
    V3.nodeHdr k.val index heap hp =
      SigGolfCandidate.T3M.SecurityInputs.withHigh
        (SigGolfCandidate.T3.nodeTweak 3 (ClaudeWCT.WCT9.nodeLayer k.val) index heap) hp := by
  have hk := k.isLt
  have hlow : V3.nodeLow k.val index = 1537 + 65536 * (k.val + 1) + 2 ^ 27 * (index % 2 ^ 31) := by
    unfold V3.nodeLow ClaudeWCT.WCT9.ftsLeafLow
    rw [Nat.mod_eq_of_lt (show k.val + 1 < 16 by omega)]
    simp only [Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
    ring
  rw [show ClaudeWCT.WCT9.nodeLayer k.val = 4 + k.val from rfl]
  unfold V3.nodeHdr SigGolfCandidate.T3M.SecurityInputs.withHigh
  by_cases hn : SigGolfCandidate.T3.FtsNew heap
  · have hm := SigGolfCandidate.T3.ftsNodeWordH_marker hn (4 + k.val - 4) index
    rw [if_pos (show 8 ≤ heap ∧ heap < 128 from hn), SigGolfCandidate.T3.nodeTweak_ftsN (by omega) (by omega) _ hn,
      if_pos (by rw [SigGolfCandidate.T3.append64_toNat]
                 obtain ⟨h8, h128⟩ := hn
                 have h0 : (0#64).toNat = 0 := rfl
                 omega),
      SigGolfCandidate.T3.append64_low]
    congr 1
    unfold SigGolfCandidate.T3.ftsNodeWordH
    rw [hlow, show 4 + k.val - 4 = k.val by omega, Nat.mod_eq_of_lt (show k.val + 1 < 16 by omega)]
    obtain ⟨h8, h128⟩ := hn
    congr 1
    omega
  · rw [if_neg (show ¬ (8 ≤ heap ∧ heap < 128) from hn), SigGolfCandidate.T3.nodeTweak_fts (by omega) (by omega) _ hn,
      if_neg (by rw [SigGolfCandidate.T3.append64_toNat, SigGolfCandidate.T3.ftsNodeWord_toNat]; omega),
      show 4 + k.val - 4 = k.val by omega]
    have hw : BitVec.ofNat 64 (V3.nodeLow k.val index) = SigGolfCandidate.T3.ftsNodeWord k.val index := by
      apply BitVec.eq_of_toNat_eq
      rw [SigGolfCandidate.T3.ftsNodeWord_toNat, BitVec.toNat_ofNat, hlow, Nat.mod_eq_of_lt (show k.val + 1 < 16 by omega)]
      have := Nat.mod_lt index (show 0 < 2 ^ 31 by decide)
      omega
    rw [hw]
/-- C1: the machine's half selection is the spec's `ftsHash` on the heap of the computed value. -/
theorem hashSel_ftsHash (heap : Nat) (input : SigGolfCandidate.T3.HashInput) :
    V3.hashSel (ClaudeWCT.WCT9.ftsHighHeap heap) input = ClaudeWCT.WCT9.ftsHash heap input := by
  unfold V3.hashSel V3.hashHi ClaudeWCT.WCT9.ftsHash
  rfl
set_option maxRecDepth 100000 in
theorem hiOut_heap (j m : Nat) (hj : j < 128) (hm : m < 6) :
    V3.hiOut j m = ClaudeWCT.WCT9.ftsHighHeap ((128 + j) / 2 ^ m) := by
  have h : ∀ j < 128, ∀ m < 6, V3.hiOut j m = ClaudeWCT.WCT9.ftsHighHeap ((128 + j) / 2 ^ m) := by
    decide +kernel
  exact h j hj m hm
theorem hiOut_leaf (j : Nat) (hj : j < 128) : V3.hiOut j 0 = ClaudeWCT.WCT9.ftsHighHeap (128 + j) := by
  have h := hiOut_heap j 0 hj (by decide)
  simpa using h
/-- C1: the machine's own copy of the fold windows is the spec's `authBase`. -/
theorem blkOff_auth (child l : Nat) (hl : l < 5) : V3.blkOff child l = ClaudeWCT.W9.T3M.authBase child l := by
  have h : ∀ c < 32, ∀ l < 5, (V3.ftsPlan.getD c []).getD l 0 =
      ((ClaudeWCT.W9.T3M.authPlans.getD c ([], 0)).1).getD l 0 := by decide +kernel
  unfold V3.blkOff ClaudeWCT.W9.T3M.authBase
  rw [if_pos hl]
  exact h (child % 32) (Nat.mod_lt _ (by decide)) l hl
theorem blkOff_auth6 (child l : Nat) (hl : l < 6) : V3.blkOff child l = ClaudeWCT.W9.T3M.authBase child l := by
  by_cases h5 : l < 5
  · exact blkOff_auth child l h5
  · rw [show l = 5 by omega, ClaudeWCT.W9.T3M.authBase_five]
    unfold V3.blkOff
    rfl
theorem nodeInput_canonical (k : Fin 9) (index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) :
    V3.hashSel (ClaudeWCT.WCT9.ftsHighHeap heap) (V3.nodeInput k.val index heap left hp pad right) =
      ClaudeWCT.W9.T3M.wctNodeHashP k.val index heap left hp pad right := by
  rw [hashSel_ftsHash]
  unfold V3.nodeInput ClaudeWCT.W9.T3M.wctNodeHashP SigGolfCandidate.T3M.SecurityInputs.nodeInputPH
    SigGolfCandidate.T3M.SecurityInputs.block4
  rw [nodeHdr_canonical]
theorem leafInput_canonical (k index j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    V3.hashSel (ClaudeWCT.WCT9.ftsHighHeap (128 + j)) (V3.leafInput k index j pad ends) =
      ClaudeWCT.WCT9.leafHashP index k j pad ends := by
  rw [hashSel_ftsHash]
  unfold ClaudeWCT.WCT9.leafHashP
  congr 1
  match ends, h with
  | [e0, e1, e2, e3, e4, e5], _ =>
    simp only [V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, V3.leafFields, ClaudeWCT.WCT9.leafInputP,
      List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc]
    rfl
theorem heap_eq (j l : Nat) (hj : j < 128) (hl : l < 6) :
    (128 + j) / 2 ^ (l + 1) = 2 ^ (6 - l) + j / 2 ^ (l + 1) := by
  interval_cases l <;> norm_num [Nat.add_div] <;> omega
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem topInput_canonical (k : Fin 9) (index j : Nat) (left pad right : Digest) :
    V3.nodeInput k.val index ((128 + j) / 2 ^ 6) left 0 pad right =
      ClaudeWCT.WCT9.wctTopInput k.val index (2 + j / 2 ^ 6) left pad right := by
  have hh : (128 + j) / 2 ^ 6 = 2 + j / 2 ^ 6 := by omega
  unfold V3.nodeInput ClaudeWCT.WCT9.wctTopInput ClaudeWCT.WCT9.wctNodeHeader
  rw [hh, nodeHdr_canonical, SigGolfCandidate.T3M.SecurityInputs.withHigh_nodeTweak_zero]
theorem hashHi_top (k : Fin 9) (index j : Nat) (left pad right : Digest) :
    V3.hashHi (V3.nodeInput k.val index ((128 + j) / 2 ^ 6) left 0 pad right) =
      ClaudeWCT.WCT9.wctTopHash k.val index (2 + j / 2 ^ 6) left pad right := by
  rw [topInput_canonical]
  rfl
theorem sibling_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 6) :
    V3.sibling w k j l = ClaudeWCT.W9.T3M.wsib w k j l := by
  unfold V3.sibling ClaudeWCT.W9.T3M.wsib ClaudeWCT.W9.T3M.authSibOff V3.sibOff
  rw [if_pos hl, if_pos hl, blkOff_auth6 j l hl]
  have hb : j / 2 ^ l % 2 = 0 ∨ j / 2 ^ l % 2 = 1 := by omega
  rcases hb with hb | hb <;>
    simp only [hb, SigGolfCandidate.T3M.sibOff, V3.regionOffset, ClaudeWCT.W9.T3M.regionBase] <;> rfl
theorem nodePad_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 6) :
    V3.nodePad w k j l = ClaudeWCT.W9.T3M.wmpad w k j l := by
  unfold V3.nodePad ClaudeWCT.W9.T3M.wmpad ClaudeWCT.W9.T3M.authPadOff V3.padOff
  rw [blkOff_auth6 j l hl]
  rfl
theorem nodeHPad_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 5) :
    V3.nodeHPad w k j l = ClaudeWCT.W9.T3M.wmhpad w k j l := by
  unfold V3.nodeHPad ClaudeWCT.W9.T3M.wmhpad V3.nodeTw
  rw [blkOff_auth j l hl]
  rfl
theorem topOther_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j : Nat) :
    V3.topOther w k j = ClaudeWCT.W9.T3M.wsib w k j 6 := by
  unfold V3.topOther V3.topOtherOff ClaudeWCT.W9.T3M.wsib ClaudeWCT.W9.T3M.topSlot
  rw [if_neg (show ¬ (6 < 6) by decide), show (2 : Nat) ^ 6 = 64 by rfl]
  split_ifs <;> rfl
/-- Monadic congruence after a `mapM`: the continuations need only agree on lists of the right length. -/
theorem mapM_bind_len {α γ β : Type} (f : γ → M α) :
    ∀ (xs : List γ) (g h : List α → M β), (∀ l : List α, l.length = xs.length → g l = h l) →
      (xs.mapM f >>= g) = (xs.mapM f >>= h)
  | [], g, h, H => by simp only [List.mapM_nil, pure_bind]; exact H [] rfl
  | x :: xs, g, h, H => by
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    congr 1
    funext a
    exact mapM_bind_len f xs (fun l => g (a :: l)) (fun l => h (a :: l))
      (fun l hl => H (a :: l) (by simp [hl]))
theorem fold5_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (leaf : Digest) :
    (List.range 5).foldlM (fun value level =>
        V3.hashSel (V3.hiOut j.val (level + 1)) (V3.nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
          (if j.val / 2 ^ level % 2 = 0 then value else V3.sibling w k.val j.val level)
          (V3.nodeHPad w k.val j.val level) (V3.nodePad w k.val j.val level)
          (if j.val / 2 ^ level % 2 = 0 then V3.sibling w k.val j.val level else value))) leaf =
      (List.finRange 5).foldlM (fun value level => do
        let other := ClaudeWCT.W9.T3M.wsib w k.val j.val level.val
        let pair := if j.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
        ClaudeWCT.W9.T3M.wctNodeHashP k.val index (2 ^ (6 - level.val) + j.val / 2 ^ (level.val + 1))
          pair.1 (ClaudeWCT.W9.T3M.wmhpad w k.val j.val level.val) (ClaudeWCT.W9.T3M.wmpad w k.val j.val level.val)
          pair.2) leaf := by
  rw [← finRange_map_val (n := 5), List.foldlM_map]
  congr 1
  funext value level
  have hl := level.isLt
  rw [hiOut_heap j.val (level.val + 1) j.isLt (by omega), heap_eq j.val level.val j.isLt (by omega),
    nodeInput_canonical k index _ _ _ _ _,
    sibling_eq w k.val j.val level.val (by omega), nodeHPad_eq w k.val j.val level.val hl,
    nodePad_eq w k.val j.val level.val (by omega)]
  by_cases hb : j.val / 2 ^ level.val % 2 = 0 <;> simp [hb]
theorem coordN_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 563) (prev : Digest × Digest) (hi : index < 2 ^ 31) :
    coordN w index k j rank prev = ClaudeWCT.W9.T3M.wctCoordP w index k j rank prev := by
  unfold coordN ClaudeWCT.W9.T3M.wctCoordP N600.program
  rw [chainProgram_canonical w index k j (N600.embed rank) hi,
    (show N600.embed = ClaudeWCT.WCT9.embed from N600.embed_eq_c1)]
  unfold canonicalChains
  apply mapM_bind_len
  intro ends hends
  simp only [List.length_finRange] at hends
  unfold V3.childN
  rw [hiOut_leaf j.val j.isLt, leafInput_canonical _ _ _ _ _ hends]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext leaf
  rw [fold5_canonical]
  congr 1
  funext value
  rw [hashHi_top, sibling_eq w k.val j.val 5 (by decide), topOther_eq]
  have hb5 : j.val / 32 % 2 = 0 ∨ j.val / 32 % 2 = 1 := by omega
  have hb6 : j.val / 64 % 2 = 0 ∨ j.val / 64 % 2 = 1 := by omega
  rcases hb5 with hb5 | hb5 <;> rcases hb6 with hb6 | hb6 <;>
    simp [hb5, hb6, show (2 : Nat) ^ 5 = 32 by rfl, show (2 : Nat) ^ 6 = 64 by rfl]
theorem ftsStartW_eq (w : ClaudeWCT.W9.T3M.WBytes) : ftsStartW w = ClaudeWCT.W9.T3M.wctStart w := by
  unfold ftsStartW ClaudeWCT.W9.T3M.wctStart
  rw [nodePad_eq w 0 0 5 (by decide)]
  rfl
theorem prevOf_eq (w : ClaudeWCT.W9.T3M.WBytes) (pairs : List (Digest × Digest)) :
    prevOf w pairs = ClaudeWCT.WCT9.prevPair (ClaudeWCT.W9.T3M.wctStart w) pairs := by
  unfold prevOf ClaudeWCT.WCT9.prevPair
  rw [ftsStartW_eq]
theorem stepN_eq (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) : stepN w a = ClaudeWCT.W9.T3M.wctStep w a := by
  funext state k
  cases state with
  | none => rfl
  | some pairs =>
    unfold stepN ClaudeWCT.W9.T3M.wctStep
    dsimp only
    simp only [prevOf_eq, coordN_canonical w (idxOf a) k _ _ _ (ClaudeWCT.WCT9.digestIndex_lt a)]
/-- Nested FTS (r1-1): the machine-level FTS is track A's padded verifier FTS phase. -/
theorem ftsN_eq (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) : ftsN w a = ClaudeWCT.W9.T3M.wctP w a := by
  unfold ftsN ClaudeWCT.W9.T3M.wctP
  rw [stepN_eq]
  congr 1
end W9Drv
end
