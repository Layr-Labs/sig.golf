import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Honest
import SigGolfCandidate.W9Machine_WctN600Contract
import SigGolfCandidate.W9Machine_WctN600Assembly
import SigGolfCandidate.W9Machine_WctSourceWords
import SigGolfCandidate.W9Machine_WctPackedHeader
import SigGolfCandidate.W9Machine_WctTraceProgram
import SigGolfCandidate.ClaudeWCT_WCT9_Basic
import SigGolfCandidate.W9Drv_Gate
import SigGolfCandidate.T3M_Verify_AfterDefs
import SigGolfCandidate.T3M_Verify_Common
import SigGolfCandidate.T3M_Images_Sizes

/-- Base shift: verify layouts have shift 0 (`Chain.base = coordinateBase`). -/
macro "base0" : tactic => `(tactic| (try simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq]))

set_option Elab.async false

section


namespace W9Machine.N600
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
/-- Coordinate 2 installs the child mask; coordinates 5 and 8 reuse it to keep the selected
child bits in their packed position and avoid an extra shift. -/
def coordDispatch (p ld cpos fsh coord : Nat) (advance : Bool) : Result :=
  let raw : E := if coord ≥ 7 then .reg .x17 else if ld ≠ 0 then .ld (.c (BitVec.ofNat 64 ld)) else .reg .x16
  let dig := if ld ≠ 0 ∨ coord = 7 then mkBin .or raw (.reg .x24) else raw
  let cmask : E := if coord = 2 then .c (BitVec.ofNat 64 0x7f00000) else .reg .x27
  let child : E := if cpos = 0 then mkBin .and dig (.c 127)
    else if cpos = 57 then mkBin .srl dig (.c (BitVec.ofNat 64 57))
    else mkBin .and (mkBin .srl dig (.c (BitVec.ofNat 64 cpos))) (.c 127)
  let childSh20 : E := mkBin .and (mkBin .srl dig (.c 1)) cmask
  let pre := if advance then mkAdd (.reg .x15) (.reg .x6) else .reg .x15
  let packed := if coord = 2 ∨ coord = 5 ∨ coord = 8 then mkBin .or childSh20 pre else mkBin .or (mkBin .sll child (.c 20)) pre
  let childPc := if coord = 2 ∨ coord = 5 ∨ coord = 8 then mkAdd (mkBin .srl childSh20 (.c 12)) (.reg .x29)
    else mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let sh : E := if fsh = 5 then mkBin .sll dig (.c 1)
    else mkBin .srl dig (.c (BitVec.ofNat 64 (fsh - 6)))
  let field := mkBin .and sh (.reg .x2)
  let n := (if ld ≠ 0 then 1 else 0) + (if coord = 2 then 2 else 1) + (if advance then 9 else 7) + (if ld ≠ 0 ∨ coord = 7 then 1 else 0)
  let regs := if ld ≠ 0 then RegFile.init.set .x16 dig else RegFile.init
  let regs := if coord = 7 then regs.set .x17 dig else regs
  let regs := if coord = 2 then regs.set .x27 cmask else regs
  let regs := regs.set .x4 (if coord = 2 ∨ coord = 5 ∨ coord = 8 then childSh20 else child)
  let regs := if advance then regs.set .x15 pre else regs
  let regs := (regs.set .x31 packed).set .x23 childPc
  let regs := if advance then regs.set .x8 (addC (.reg .x8) (BitVec.ofNat 64 (2 ^ 64 - 848))) else regs
  let regs := (regs.set .x14 field).set .x1 (.c (pcOf (p + n)))
  ⟨⟨regs, [], []⟩, mkBin .and field (.c (~~~1#64)), .jump, n, n⟩
end W9Machine
end
section
namespace W9Drv
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWordsN (k : Nat) : List (BitVec 32) := [[0x7f87213,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0x181713,0x277733,0x700e7],[0x803803,0x1886833,0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xcb040413,0x181713,0x277733,0x700e7],[0x7f00db7,0x185213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x1485713,0x277733,0x700e7],[0x3985213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xcb040413,0x2385713,0x277733,0x700e7],[0x1003803,0x1886833,0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xcb040413,0x181713,0x277733,0x700e7],[0x185213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x1485713,0x277733,0x700e7],[0x3985213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xcb040413,0x2385713,0x277733,0x700e7],[0x188e8b3,0x7f8f213,0x6787b3,0x1421f93,0xffefb3,0x821b93,0x1db8bb3,0xcb040413,0x189713,0x277733,0x700e7],[0x18d213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x148d713,0x277733,0x700e7]].getD k []
def digWord (k : Nat) : Nat := [0,1,1,1,2,2,2,3,3].getD k 0
def ldOf (k : Nat) : Nat := [0,8,0,0,16,0,0,0,0].getD k 0
def cposOf (k : Nat) : Nat := [0,0,21,57,0,21,57,0,21].getD k 0
def fshOf (k : Nat) : Nat := [5,5,26,41,5,26,41,5,26].getD k 0
def dispatchLenN (k : Nat) : Nat := [8, 12, 11, 10, 12, 10, 10, 11, 10].getD k 0
def dispatchResultN (k : Nat) : Result :=
  coordDispatch (dispatchPc k) (ldOf k) (cposOf k) (fshOf k) k (decide (k ≠ 0))
theorem dispatch_all_checked : (List.range 9).all (fun k =>
    rOK (symRun {} (dispatchWordsN k) (pcOf (dispatchPc k)) (dispatchLenN k)) (dispatchResultN k)) = true := by
  decide +kernel
end W9Drv
end
section
namespace W9Drv
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
theorem dispatch_mem (k : Fin 9) (u : MachineState) (A : Word) :
    ((dispatchResult k).toState u).getMem A = u.getMem A := by
  fin_cases k <;> rfl
end W9Drv
end
section
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace W9Drv
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
  · change ((((dispatchDig 5).eval u >>> 1) &&& u.getReg .x27) >>> 12) + u.getReg .x29 =
      (((dispatchDig 5).eval u >>> 21 &&& 127#64) <<< 8) + u.getReg .x29
    rw [hm (by decide), show BitVec.ofNat 64 0x7f00000 = 0x7f00000#64 from rfl, childSh8_eq]
  · rfl
  · rfl
  · change ((((dispatchDig 8).eval u >>> 1) &&& u.getReg .x27) >>> 12) + u.getReg .x29 =
      (((dispatchDig 8).eval u >>> 21 &&& 127#64) <<< 8) + u.getReg .x29
    rw [hm (by decide), show BitVec.ofNat 64 0x7f00000 = 0x7f00000#64 from rfl, childSh8_eq]
theorem dispatch_x4 (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    ((dispatchResult k).toState u).getReg .x4 =
      if k.val = 2 ∨ k.val = 5 ∨ k.val = 8 then (dispatchChild k).eval u <<< 20 else (dispatchChild k).eval u := by
  have hm := hu.childMask
  fin_cases k
  · rfl
  · rfl
  · change ((dispatchDig 2).eval u >>> 1) &&& 0x7f00000#64 =
      ((dispatchDig 2).eval u >>> 21 &&& 127#64) <<< 20
    rw [childSh20_eq]
  · rfl
  · rfl
  · change ((dispatchDig 5).eval u >>> 1) &&& u.getReg .x27 =
      ((dispatchDig 5).eval u >>> 21 &&& 127#64) <<< 20
    rw [hm (by decide), show BitVec.ofNat 64 0x7f00000 = 0x7f00000#64 from rfl, childSh20_eq]
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
  · change (((dispatchDig 5).eval u >>> 1) &&& u.getReg .x27) ||| ((dispatchResult 5).toState u).getReg .x15 =
      (((dispatchDig 5).eval u >>> 21 &&& 127#64) <<< 20) ||| ((dispatchResult 5).toState u).getReg .x15
    rw [hm (by decide), show BitVec.ofNat 64 0x7f00000 = 0x7f00000#64 from rfl, childSh20_eq]
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
        base0; unfold coordinateBase V3.regionOffset
        omega
      · rw [if_neg (fun h => hh (by rw [Nat.add_sub_cancel_left] at h; exact h.2))]
        have hw := hu.coords k.val (Nat.le_refl _) (by omega) off ho h8 (by omega)
          (fun _ => by unfold legHand; rw [if_neg (by omega)]; exact hh)
        have he : regionAddr k.val + off - 0x1020 = V3.regionOffset k.val + off := by
          unfold regionAddr V3.regionOffset; omega
        have hb : Chain.base Frozen.layout k + off = regionAddr k.val + off := by
          base0; unfold coordinateBase regionAddr; omega
        rw [hb]
        simpa only [W9Machine.OrigW, he] using hw }
  · change ((dispatchResult k).toState u).getReg .x8 = _
    have hb := hu.baseReg
    fin_cases k <;> simp [dispatchResult, dispatchResultN, coordDispatch, ldOf, cposOf, fshOf, dispatchPc,
      Result.toState_getReg, RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hb, W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq,
      coordinateBase]
  · change ((dispatchResult k).toState u).getReg .x31 = _
    rw [dispatch_leaf pk w a k pairs u hu, hc, hnode]
    exact leafLow_or _ _ _ k.isLt hj hi
  · change ((dispatchResult k).toState u).getReg .x23 = _
    rw [dispatch_childPC pk w a k pairs u hu, hc, hu.childBlock]
    simp only [Frozen.layout, pcOf]
    rw [shl_ofNat, ← BitVec.ofNat_add]
    congr 1
    rw [Nat.shiftLeft_eq]
    omega
  · change ((dispatchResult k).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h2 h7)
end W9Drv
end
section
namespace W9Drv
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
    GoodQFor (P := P) Frozen.image s 1 0 Q A (pure (false, 0)) := by
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open W9Machine
set_option maxHeartbeats 1600000 in
theorem coord_core_good (chains : N600.AllGood (P := P) Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good (P := P) Frozen.layout ⟨38, 95, 95 - ClaudeWCT.WCT9.childSave j.val⟩ j)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 563)
    (v u : MachineState) (padL padZ : Digest) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs)
    (hu : N600.Pre Frozen.layout (V3.viewW w k.val v) index k j rank u)
    (hL : DigAt v (0x1020 + V3.regionOffset k.val + 672) padL)
    (hZ : DigAt v (0x1020 + V3.regionOffset k.val + 816) padZ)
    (hnext : ∀ ends entry, Chain.Post Frozen.layout (V3.viewW w k.val v) index k j u ends entry →
      ∀ computed t, Child.Post Frozen.layout k j entry computed t →
        GoodQFor (P := P) Frozen.image t N C Q A (K computed)) :
    GoodQFor (P := P) Frozen.image u (N + 127) (C + 184) Q
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
  (regionAddr n ≤ A ∧ A < regionAddr n + 864) ∨
    (if j / 64 % 2 = 0 then regionAddr n - (if n = 8 then 96 else 192) ≤ A ∧ A < regionAddr n - (if n = 8 then 64 else 160)
      else regionAddr n - (if n = 8 then 32 else 48) ≤ A ∧ A < regionAddr n - (if n = 8 then 0 else 16))
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
    unfold Child.writes Child.handAddr; rw [W9Machine.Frozen.base_eq]; unfold coordinateBase
    split_ifs at hn ⊢ <;> omega)]
  exact hp.frame A hA (by unfold Chain.writes; base0; unfold coordinateBase; omega)
theorem prevOf_snoc (w : ClaudeWCT.W9.T3M.WBytes) (pairs : List (Digest × Digest)) (p : Digest × Digest) :
    prevOf w (pairs ++ [p]) = p := by
  unfold prevOf; simp
theorem regionAddr_succ (n : Nat) (hn : n < 9) : regionAddr n = regionAddr (n + 1) + 848 := by
  unfold regionAddr; omega
/-- Pairing stage 1: the legacy 6-level child of coordinate 0 still writes its level-5 block (`regionAddr 0 + 784 ..
+ 864`), which overlaps the L1 layer start `WIT + 7664 = 11792`; the bound below excludes coordinate 0 (the live
shared route, `SharedCoord.writes_bounds`, has an A routine at coordinate 0 with frame `+ 784`). -/
theorem coordW_bounds {n j A : Nat} (hn : n < 9) (hn0 : n ≠ 0) (h : coordW n j A) : 1200 ≤ A ∧ A < 11792 := by
  unfold coordW regionAddr at h; split_ifs at h <;> omega
set_option maxRecDepth 100000 in
/-- The witness top sibling of coordinate `k` survives in region `k + 1` (only the other hand-off slot is written). -/
theorem next_other (w : ClaudeWCT.W9.T3M.WBytes) (k : Fin 9) (j : Nat) (u t : MachineState)
    (hf : Frame u t (coordW k.val j)) (off : Nat) (hoff : off = legL (k.val + 1) ∨ off = legR (k.val + 1))
    (hsel : if j / 64 % 2 = 0 then off = legR (k.val + 1) else off = legL (k.val + 1))
    (h0 : W9Machine.OrigW w u (regionAddr (k.val + 1) + off))
    (h1 : W9Machine.OrigW w u (regionAddr (k.val + 1) + (off + 8))) :
    DigAt t (regionAddr (k.val + 1) + off) (V3.topOther w k.val j) := by
  have hk := k.isLt
  have h1' : W9Machine.OrigW w u (regionAddr (k.val + 1) + off + 8) := by rw [Nat.add_assoc]; exact h1
  unfold legL legR at hoff hsel
  have hlo : 0x1020 ≤ regionAddr (k.val + 1) + off := by unfold regionAddr; split_ifs at hoff <;> omega
  have hdig := W9Machine.DigAt_origW h0 h1' hlo
  have he : regionAddr (k.val + 1) + off - 0x1020 = V3.topOtherOff k.val j := by
    unfold V3.topOtherOff V3.regionOffset regionAddr
    split_ifs at hsel ⊢ <;> omega
  rw [he] at hdig
  refine hdig.frame hf (by unfold regionAddr; split_ifs at hoff <;> omega) ?_ ?_
  · intro hw; unfold coordW regionAddr at hw; split_ifs at hsel hw <;> omega
  · intro hw; unfold coordW regionAddr at hw; split_ifs at hsel hw <;> omega
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
/-- The previous-pair slots after coordinate `n`: the computed node at its hand-off slot, the other one is the
witness top sibling. -/
theorem coord_next (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hk0 : k.val ≠ 0)
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
  have hm (A : Nat) (hA : A < 2^64) (hs : A < 1200 ∨ 11792 ≤ A) :
      t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    intro hw
    have := coordW_bounds hk hk0 hw
    omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      t.getReg r = (chainEntryState a k u).getReg r := by
    rw [ht.keep r (by
      simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x4,.x8,.x9,.x14,.x15,.x16,.x17,.x23,.x27,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hdr : ∀ i, 4 ≤ i → i < 6 → ¬ coordW k.val (ClaudeWCT.WCT9.child a k).val (WIT + 8 * i) := by
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
    · refine ⟨?_, fun lay hl => ?_, ?_, ?_⟩
      · rw [hm (TOPBASE-8) (by unfold TOPBASE; omega) (Or.inr (by unfold TOPBASE; omega))]
        exact hdata.mask
      · have hb := hdrAddr_bounds lay
        rw [hm (hdrAddr lay) (by unfold TOPBASE at *; omega) (Or.inr (by unfold TOPBASE at *; omega))]
        exact hdata.header lay hl
      · rw [hm (TOPB9+56) (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))]
        exact hdata.buffer3
      · rw [hm (TOPB9-288) (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))]
        exact hdata.mask6
  have hb6 : (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 0 ∨ (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 1 := by omega
  have hra := regionAddr_succ k.val hk
  have hbase : coordinateBase k = regionAddr k.val := by base0; unfold coordinateBase regionAddr; omega
  have hR9 : regionAddr (k.val + 1) ≥ 496 := by unfold regionAddr; omega
  -- the other top sibling, from the witness (region k+1 is untouched outside one hand-off slot)
  have hother : ∀ off, (off = legL (k.val + 1) ∨ off = legR (k.val + 1)) →
      (if (ClaudeWCT.WCT9.child a k).val / 64 % 2 = 0 then off = legR (k.val + 1) else off = legL (k.val + 1)) →
      DigAt t (regionAddr (k.val + 1) + off) (V3.topOther w k.val (ClaudeWCT.WCT9.child a k).val) := by
    intro off hoff hsel
    have ho : off ≤ 832 ∧ off % 8 = 0 ∧ (k.val + 1 = 9 → 768 ≤ off) := by
      unfold legL legR at hoff
      split_ifs at hoff <;> omega
    exact next_other w k _ u t hf off hoff hsel
      (hu.coords (k.val + 1) (by omega) (by omega) off (by omega) (by omega) ho.2.2
        (fun h => by omega))
      (hu.coords (k.val + 1) (by omega) (by omega) (off + 8) (by omega) (by omega)
        (fun h => by have := ho.2.2 h; omega) (fun h => by omega))
  have htop : DigAt t (Child.handAddr Frozen.layout k (ClaudeWCT.WCT9.child a k)) computed := ht.top
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
    simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq, coordinateBase] at hb
    rw [hb]
    congr 1
    try omega
  · rw [hr .x9 (by decide)]
    exact (dispatch_x9 k u).trans hu.pairPtr
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      have e : Child.handAddr Frozen.layout k (ClaudeWCT.WCT9.child a k) = regionAddr (k.val + 1) + legL (k.val + 1) := by
        unfold Child.handAddr legL; base0; rw [hbase]; unfold regionAddr; split_ifs <;> omega
      rw [← e]; exact htop
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      exact hother (legL (k.val + 1)) (Or.inl rfl) (by rw [if_neg (by omega)])
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      exact hother (legR (k.val + 1)) (Or.inr rfl) (by rw [if_pos h0])
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      have e : Child.handAddr Frozen.layout k (ClaudeWCT.WCT9.child a k) = regionAddr (k.val + 1) + legR (k.val + 1) := by
        unfold Child.handAddr legR; base0; rw [hbase]; unfold regionAddr; split_ifs <;> omega
      rw [← e]; exact htop
  · intro _
    have h12 := ht.a2
    unfold Child.handAddr at h12
    simp only [W9Machine.Frozen.base_eq] at h12
    rw [hbase] at h12
    split_ifs at h12
    all_goals first
      | (left; rw [h12]; congr 1; unfold legL regionAddr; split_ifs <;> omega)
      | (right; rw [h12]; congr 1; unfold legR regionAddr; split_ifs <;> omega)
  · intro m hm1 hm9 off hoff h8 hv hh
    have h0 := hu.coords m (by omega) hm9 off hoff h8 hv (fun h => by omega)
    unfold W9Machine.OrigW at h0 ⊢
    rw [← h0]
    apply hf _ (by unfold regionAddr; omega)
    intro hw
    unfold coordW at hw
    have hmk : regionAddr m + 848 ≤ regionAddr k.val := by unfold regionAddr; omega
    rcases Nat.lt_or_ge (k.val + 1) m with hgt | hle
    · have : regionAddr m + 848 ≤ regionAddr (k.val + 1) := by unfold regionAddr; omega
      split_ifs at hw <;> omega
    · have hm' : m = k.val + 1 := by omega
      subst hm'
      have hn := hh rfl
      unfold legHand V3.isHand at hn
      split_ifs at hn <;> split_ifs at hw <;> omega
  · exact hu.layer.frame (fun j hj h => hf _ (by unfold WIT WX at *; omega)
      (by intro hw; unfold coordW regionAddr WIT at *; split_ifs at hw <;> omega))
def finishN (w : ClaudeWCT.W9.T3M.WBytes) (state : Option (List (Digest × Digest))) :
    M (Option (Digest × Digest)) :=
  match state with
  | none => pure none
  | some pairs => pure (some (prevOf w pairs))
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => dispatchLen k + 184)).sum
def coordsAccept (a : HashOutput) (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => (dispatchLen k + 90) + (N600.rankCost (ClaudeWCT.WCT9.rank a k) +
    ClaudeWCT.WCT9.childExtra (ClaudeWCT.WCT9.child a k)))).sum
theorem fold_none (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (stepN w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, stepN, pure_bind] using ih
theorem coordsAccept_all (a : HashOutput) :
    coordsAccept a (List.finRange 9) = 904 + ClaudeWCT.WCT9.jointCost a := by
  unfold coordsAccept
  rw [List.sum_map_add]
  have hfixed : ((List.finRange 9).map (fun k => dispatchLen k + 90)).sum = 904 := by decide
  rw [hfixed]
  congr 1
  simp only [ClaudeWCT.WCT9.jointCost, ClaudeWCT.WCT9.coordCost,
    (show N600.rankCost = ClaudeWCT.WCT9.routineCost from N600.rankCost_eq_c1)]
end W9Drv
end
end

section
namespace W9Drv
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
/-- The FTS phase of the verifier refines the machine-level nested FTS `ftsN` (bridged to track A's `wctP`
in `W9Drv.SpecBridge`). -/
def FtsGoodByCost (acceptCost : HashOutput → Nat) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs),
    GatePre pk w a u → K none = pure (false, 0) →
    (∀ top t, FtsOut ⟨pk,w,a⟩ top t →
      GoodQFor (P := P) Frozen.image t N C Q A (K (some top))) →
    GoodQFor (P := P) Frozen.image u (N+2023) (C+2023) Q (A+acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ftsN w a else pure none) K)
def ftsAcceptCost (a : HashOutput) : Nat := 926 + ClaudeWCT.WCT9.jointCost a
end W9Drv
end

/-! Nested FTS (r1-1): the machine-level FTS phase `W9Drv.ftsN` is track A's padded verifier FTS phase
`ClaudeWCT.W9.T3M.wctP`. The chain part reuses the frontier bridge; the tree part matches `V3.childN` (explicit
nested pads, high-half top node) against `wctCoordP`. -/

section
set_option autoImplicit false
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
/-- Witness stack: the V3 step input is the padded verifier's input in either chain format. -/
theorem chainInput_canonical (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 6) (hs : step < 4) :
    V3.chainInput index coord child chain step a b c value =
      ClaudeWCT.W9.T3M.wctChainInputPW index coord child chain step a b c value := by
  unfold ClaudeWCT.W9.T3M.wctChainInputPW
  by_cases hG : WCT9.ftsIsG chain = true
  · rw [if_pos hG]
    change _ = blk4 value (WCT9.ftsChainHeaderP index coord child chain step b) a c
    rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
        (chainInput_length _ _ _ _ _ _ _ _ _),
      ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _),
      wordsOf_chainInput, if_pos hG, wordsOf_blk4]
    simp only [dlo, dhi, WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high,
      chainLow_canonical _ _ _ _ _ hi hk hj ht hs]
  · rw [if_neg hG]
    change _ = blk4 a (WCT9.ftsChainHeaderP index coord child chain step b) c value
    rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
        (chainInput_length _ _ _ _ _ _ _ _ _),
      ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _),
      wordsOf_chainInput, if_neg hG, wordsOf_blk4]
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
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
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
theorem nodeInput_canonical (k : Fin 9) (index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) :
    shortHash (V3.nodeInput k.val index heap left hp pad right) =
      ClaudeWCT.W9.T3M.wctNodeHashP k.val index heap left hp pad right := by
  unfold V3.nodeInput ClaudeWCT.W9.T3M.wctNodeHashP SigGolfCandidate.T3M.SecurityInputs.nodeInputPH
    SigGolfCandidate.T3M.SecurityInputs.block4
  rw [nodeHdr_canonical]
theorem leafInput_canonical (k index j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    shortHash (V3.leafInput k index j pad ends) = ClaudeWCT.WCT9.leafHashP index k j pad ends := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5], _ =>
    simp only [V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, V3.leafFields, ClaudeWCT.WCT9.leafHashP, ClaudeWCT.WCT9.leafInputP,
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
/-- Pairing stage 1: the legacy padded verifier reads coordinate 0's level-5 sibling and pad from `legacySib0` /
`legacyPad0` (that window left the witness), so the legacy machine-view identities exclude `k = 0, l = 5`. -/
theorem sibling_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 6) (h05 : k ≠ 0 ∨ l ≠ 5) :
    V3.sibling w k j l = ClaudeWCT.W9.T3M.wsib w k j l := by
  unfold V3.sibling ClaudeWCT.W9.T3M.wsib ClaudeWCT.W9.T3M.authSibOff V3.sibOff V3.blkOff
  rw [if_pos hl, if_pos hl, if_neg (show ¬ (k = 0 ∧ l = 5) by omega)]
  have hb : j / 2 ^ l % 2 = 0 ∨ j / 2 ^ l % 2 = 1 := by omega
  by_cases h5 : l < 5
  · rw [if_pos h5]
    rcases hb with hb | hb <;>
      simp only [hb, SigGolfCandidate.T3M.sibOff, V3.regionOffset, ClaudeWCT.W9.T3M.regionBase] <;> rfl
  · rw [if_neg h5, show l = 5 by omega, ClaudeWCT.W9.T3M.authBase_five]
    rw [show l = 5 by omega] at hb
    rcases hb with hb | hb <;>
      simp only [hb, SigGolfCandidate.T3M.sibOff, V3.regionOffset, ClaudeWCT.W9.T3M.regionBase] <;> rfl
theorem nodePad_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 6) (h05 : k ≠ 0 ∨ l ≠ 5) :
    V3.nodePad w k j l = ClaudeWCT.W9.T3M.wmpad w k j l := by
  unfold V3.nodePad ClaudeWCT.W9.T3M.wmpad ClaudeWCT.W9.T3M.authPadOff V3.padOff V3.blkOff
  rw [if_neg (show ¬ (k = 0 ∧ l = 5) by omega)]
  by_cases h5 : l < 5
  · rw [if_pos h5]; rfl
  · rw [if_neg h5, show l = 5 by omega, ClaudeWCT.W9.T3M.authBase_five]; rfl
theorem nodeHPad_eq (w : ClaudeWCT.W9.T3M.WBytes) (k j l : Nat) (hl : l < 5) :
    V3.nodeHPad w k j l = ClaudeWCT.W9.T3M.wmhpad w k j l := by
  unfold V3.nodeHPad ClaudeWCT.W9.T3M.wmhpad V3.nodeTw V3.blkOff
  rw [if_pos hl]
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
        shortHash (V3.nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
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
  rw [heap_eq j.val level.val j.isLt (by omega), nodeInput_canonical k index _ _ _ _ _,
    sibling_eq w k.val j.val level.val (by omega) (Or.inr (by omega)), nodeHPad_eq w k.val j.val level.val hl,
    nodePad_eq w k.val j.val level.val (by omega) (Or.inr (by omega))]
  by_cases hb : j.val / 2 ^ level.val % 2 = 0 <;> simp [hb]
theorem coordN_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 563) (prev : Digest × Digest) (hi : index < 2 ^ 31) (hk0 : k.val ≠ 0) :
    coordN w index k j rank prev = ClaudeWCT.W9.T3M.wctCoordP w index k j rank prev := by
  unfold coordN ClaudeWCT.W9.T3M.wctCoordP N600.program
  rw [chainProgram_canonical w index k j (N600.embed rank) hi,
    (show N600.embed = ClaudeWCT.WCT9.embed from N600.embed_eq_c1)]
  unfold canonicalChains
  apply mapM_bind_len
  intro ends hends
  simp only [List.length_finRange] at hends
  unfold V3.childN
  rw [leafInput_canonical _ _ _ _ _ hends]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext leaf
  rw [fold5_canonical]
  congr 1
  funext value
  rw [hashHi_top, sibling_eq w k.val j.val 5 (by decide) (Or.inl hk0), topOther_eq]
  have hb5 : j.val / 32 % 2 = 0 ∨ j.val / 32 % 2 = 1 := by omega
  have hb6 : j.val / 64 % 2 = 0 ∨ j.val / 64 % 2 = 1 := by omega
  rcases hb5 with hb5 | hb5 <;> rcases hb6 with hb6 | hb6 <;>
    simp [hb5, hb6, show (2 : Nat) ^ 5 = 32 by rfl, show (2 : Nat) ^ 6 = 64 by rfl]
/- Pairing stage 1: `ftsStartW_eq` / `prevOf_eq` / `stepN_eq` / `ftsN_eq` (legacy Frozen-layout machine FTS = legacy
padded verifier FTS) were removed: the legacy machine reads coordinate 0's level-5 window at `regionAddr 0 + 832`,
which the paired witness no longer carries (legacy `wsib`/`wmpad` read `legacySib0`/`legacyPad0` instead). They had
no users; the live route is `SharedCoord`/`SharedCanonical` below. -/
end W9Drv
end

/-! Shared-forest dispatch prototype; not yet installed in Frozen.image. -/
namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
def words (k : Nat) : List (BitVec 32) :=
  [[0x7f87213,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0x585713,0x277733,0x700e7],
    [0xe81213,0x1b27233,0x803803,0x1886833,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x585713,0x277733,0x700e7],
    [0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0xcb040413,0x1185713,0x277733,0x700e7],
    [0xe81213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x1d85713,0x277733,0x700e7],
    [0x1003803,0x1886833,0x7f87213,0x6787b3,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0xcb040413,0x585713,0x277733,0x700e7],
    [0xe81213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x1185713,0x277733,0x700e7],
    [0x1d85713,0x277733,0x7f8f213,0x6787b3,0x1421f93,0xffefb3,0x721b93,0x1cb8bb3,0xcb040413,0x700e7],
    [0x188e8b3,0xe89213,0x1b27233,0x6787b3,0xf26fb3,0xc25b93,0x1db8bb3,0xcb040413,0x58d713,0x277733,0x118d213,0x700e7],
    [0x227733,0x1b27233,0x6787b3,0xf26fb3,0xf104bc83,0xc25b93,0x19b8bb3,0xcb040413,0x700e7]].getD k []
def start (k : Nat) : Nat := [89,171,257,341,425,511,595,679,765].getD k 849
def length (k : Nat) : Nat := [8,12,10,10,12,10,10,12,9].getD k 0
def first (k : Nat) : Bool := decide (k < 8 ∧ k % 2 = 0)
def rankPosition (k : Nat) : Nat := [13,13,25,37,13,25,37,13,25].getD k 13
def result (k : Nat) : Result :=
  let fresh : E := if k = 1 then .ld (.c 8) else .ld (.c 16)
  let padded := mkBin .or fresh (.reg .x24)
  let lastPadded := mkBin .or (.reg .x17) (.reg .x24)
  let childDig : E := if k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 6 then .reg .x17 else .reg .x16
  let rankDig : E := if k = 1 ∨ k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 7 then .reg .x17 else .reg .x16
  -- Coordinate 8 (dispatch hoist): `tp` already holds `a7 >>> 17` (coordinate 7's word 689), so the child and rank
  -- fields are masked directly out of `tp`.
  let child := if first k then mkBin .and childDig (.c 127)
    else mkBin .and (if k = 8 then .reg .x4
      else mkBin .sll childDig (.c 14)) (.reg .x27)
  let node := if k = 0 then .reg .x15 else mkAdd (.reg .x15) (.reg .x6)
  let header := mkBin .or (if first k then mkBin .sll child (.c 20) else child) node
  let singletonBase := .ld (addC (.reg .x9) (BitVec.ofNat 64 (2^64 - 240)))
  let childPC := mkAdd (if first k then mkBin .sll child (.c 7)
    else mkBin .srl child (.c 12)) (if first k then .reg .x28
      else if k = 8 then singletonBase else .reg .x29)
  let field := mkBin .and (if k = 8 then .reg .x4
    else mkBin .srl rankDig (.c (BitVec.ofNat 64 (rankPosition k - 8)))) (.reg .x2)
  let regs := if k = 1 ∨ k = 4 then RegFile.init.set .x16 padded else RegFile.init
  let regs := if k = 7 then regs.set .x17 lastPadded else regs
  let regs := if k = 8 then regs.set .x25 singletonBase else regs
  -- Coordinate 7 ends with `srli tp,a7,17` (word 689): its `tp` is the hoisted shift, not the child.
  let regs := (regs.set .x4 (if k = 7 then mkBin .srl lastPadded (.c 17) else child)).set .x31 header
  let regs := if k = 0 then regs else (regs.set .x15 node).set .x8
    (addC (.reg .x8) (BitVec.ofNat 64 (2^64 - 848)))
  let regs := ((regs.set .x23 childPC).set .x14 field).set .x1 (.c (pcOf (start k + length k)))
  ⟨⟨regs, [], if k = 8 then [.valid ⟨some (.reg .x9), BitVec.ofNat 64 (2^64 - 240)⟩ 8] else []⟩,
    mkBin .and field (.c (~~~1#64)), .jump, length k, length k⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : ∀ k : Fin 9,
    rOK (symRun {} (words k.val) (pcOf (start k.val)) (length k.val)) (result k.val) = true := by
  intro k; fin_cases k <;> decide +kernel
theorem total_dispatch_words : ((List.range 9).map length).sum = 93 := by decide
theorem linked (k : Fin 9) : sliceChecked (start k.val) (words k.val) = true := by
  fin_cases k <;> decide +kernel

end W9Drv.SharedDispatch

namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def childWord (k : Nat) : Nat := [0,0,1,1,2,2,3,3,3].getD k 0
def childPos (k : Nat) : Nat := [0,6,0,6,0,6,0,6,37].getD k 0
def childOfWord (k : Fin 9) (x : Word) : Word := (x >>> childPos k.val) &&& 127#64

def childDig (k : Nat) : E :=
  let fresh : E := if k = 1 then .ld (.c 8) else .ld (.c 16)
  let padded := mkBin .or fresh (.reg .x24)
  let lastPadded := mkBin .or (.reg .x17) (.reg .x24)
  if k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 6 then .reg .x17 else .reg .x16

def rankDig (k : Nat) : E :=
  let fresh : E := if k = 1 then .ld (.c 8) else .ld (.c 16)
  let padded := mkBin .or fresh (.reg .x24)
  let lastPadded := mkBin .or (.reg .x17) (.reg .x24)
  if k = 1 ∨ k = 4 then padded else if k = 7 then lastPadded
    else if k ≥ 7 then .reg .x17 else .reg .x16

theorem child_field (a : HashOutput) (k : Fin 9) :
    childOfWord k (a.extractLsb' (64 * childWord k.val) 64) =
      BitVec.ofNat 64 (SharedForest.rawChildFromOutput a k).val := by
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> simp [childOfWord, childPos, childWord, SharedForest.rawChildFromOutput,
    SharedForest.rawChildBase, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, W9Drv.nat_and127,
    BitVec.toNat_ofNat] <;> omega

theorem child_pad (k : Fin 9) (x : Word) :
    childOfWord k (x ||| SharedCoord.rankPad) = childOfWord k x := by
  fin_cases k <;> simp only [childOfWord, childPos, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;> simp [SharedCoord.rankPad]

theorem childDig_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    (childDig k.val).eval u = a.extractLsb' (64 * childWord k.val) 64 |||
      (if k.val = 6 then 0 else SharedCoord.rankPad) := by
  have hd := hu.digest (childWord k.val) (by fin_cases k <;> decide)
  have hc := hu.cached
  have h3 := hu.cached3
  have hp := hu.jt
  fin_cases k <;> simp_all [childDig, childWord, cachedWord, mkBin_eval, E.eval, BinOp.eval]

theorem rankDig_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    (rankDig k.val).eval u = a.extractLsb' (64 * W9Drv.digWord k.val) 64 ||| SharedCoord.rankPad := by
  have hd := hu.digest (W9Drv.digWord k.val) (by fin_cases k <;> decide)
  have hc := hu.cached
  have h3 := hu.cached3
  have hp := hu.jt
  fin_cases k <;> simp_all [rankDig, W9Drv.digWord, cachedWord, mkBin_eval, E.eval, BinOp.eval]

theorem raw_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    childOfWord k ((childDig k.val).eval u) = BitVec.ofNat 64 (SharedForest.rawChildFromOutput a k).val := by
  rw [childDig_eval pk w a k pairs u hu]
  by_cases h : k.val = 6
  · rw [if_pos h]
    simpa using (child_field a k)
  · rw [if_neg h, child_pad, child_field]

theorem packed_pair (x : Word) :
    (x <<< 14) &&& 0x7f00000#64 = ((x >>> 6) &&& 127#64) <<< 20 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem packed_singleton (x : Word) :
    (x >>> 17) &&& 0x7f00000#64 = ((x >>> 37) &&& 127#64) <<< 20 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem packed_shr (x : Word) :
    (((x &&& 127#64) <<< 20) >>> 12) = (x &&& 127#64) <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem mem (k : Fin 9) (u : MachineState) (addr : Word) :
    ((result k.val).toState u).getMem addr = u.getMem addr := by
  fin_cases k <;> rfl

theorem keep (k : Fin 9) (u : MachineState) (r : Reg)
    (hr : r ∉ [.x1,.x4,.x8,.x14,.x15,.x16,.x17,.x23,.x25,.x31]) :
    ((result k.val).toState u).getReg r = u.getReg r := by
  rw [Result.toState_getReg]
  fin_cases k <;> cases r <;> first | exact False.elim (hr (by decide)) | rfl

/-- Dispatch hoist: coordinate 7's dispatcher ends with `srli tp,a7,17` (word 689) after `or a7,a7,s8`, so it leaves
coordinate 8's shared shift in `tp`. -/
theorem hoist_seven (u : MachineState) :
    ((result 7).toState u).getReg .x4 = ((result 7).toState u).getReg .x17 >>> 17 := by
  rw [Result.toState_getReg, Result.toState_getReg]
  rfl

theorem node (k : Fin 9) (u : MachineState) :
    ((result k.val).toState u).getReg .x15 =
      (if k.val = 0 then u.getReg .x15 else u.getReg .x15 + u.getReg .x6) := by
  fin_cases k <;> rfl

theorem nodeWord (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    ((result k.val).toState u).getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val (idxOf a)) := by
  have hi : idxOf a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  rw [node, nodeLow_value _ _ k.isLt hi]
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

end W9Drv.SharedDispatch

namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The packed child expression of dispatcher `k` (the `child` of `result k`): `childDig & 127` (A), or the raw child
moved to bits 20..26 (B, C). Coordinate 8 masks the hoisted `tp = a7 >>> 17`. -/
def childE (k : Nat) : E :=
  if first k then mkBin .and (childDig k) (.c 127)
  else mkBin .and (if k = 8 then .reg .x4 else mkBin .sll (childDig k) (.c 14)) (.reg .x27)

theorem packed_result (k : Fin 9) (u : MachineState)
    (hm : u.getReg .x27 = BitVec.ofNat 64 0x7f00000)
    (hx4 : k.val = 8 → u.getReg .x4 = u.getReg .x17 >>> 17) :
    (childE k.val).eval u =
      if first k.val then childOfWord k ((childDig k.val).eval u)
      else childOfWord k ((childDig k.val).eval u) <<< 20 := by
  fin_cases k
  · change ((childDig 0).eval u) &&& 127#64 = (((childDig 0).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 1).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 1).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change ((childDig 2).eval u) &&& 127#64 = (((childDig 2).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 3).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 3).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change ((childDig 4).eval u) &&& 127#64 = (((childDig 4).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 5).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 5).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change ((childDig 6).eval u) &&& 127#64 = (((childDig 6).eval u) >>> 0) &&& 127#64
    simp
  · change (((childDig 7).eval u) <<< 14) &&& u.getReg .x27 = ((((childDig 7).eval u) >>> 6) &&& 127#64) <<< 20
    rw [hm]
    exact packed_pair _
  · change u.getReg .x4 &&& u.getReg .x27 = ((u.getReg .x17 >>> 37) &&& 127#64) <<< 20
    rw [hm, hx4 rfl]
    exact packed_singleton _

theorem leaf (k : Fin 9) (u : MachineState)
    (hm : u.getReg .x27 = BitVec.ofNat 64 0x7f00000)
    (hx4 : k.val = 8 → u.getReg .x4 = u.getReg .x17 >>> 17) :
    ((result k.val).toState u).getReg .x31 =
      (childOfWord k ((childDig k.val).eval u) <<< 20) |||
        ((result k.val).toState u).getReg .x15 := by
  have he : ((result k.val).toState u).getReg .x31 =
      (if first k.val then (childE k.val).eval u <<< 20
       else (childE k.val).eval u) |||
        ((result k.val).toState u).getReg .x15 := by
    fin_cases k <;> rfl
  rw [he, packed_result k u hm hx4]
  cases first k.val <;> rfl

theorem child_pc (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    ((result k.val).toState u).getReg .x23 =
      pcOf ((SharedLayout.layout k).childWord (SharedForest.rawChildFromOutput a k)) := by
  have hraw := raw_eval pk w a k pairs u hu
  have hm := hu.childMask
  have hA := hu.aTable
  have hB := hu.childBlock
  have hC := hu.singletonTable
  have h9 := hu.pairPtr
  have hj := (SharedForest.rawChildFromOutput a k).isLt
  have hpc : ((result k.val).toState u).getReg .x23 =
      (childOfWord k ((childDig k.val).eval u) <<< (if first k.val then 7 else 8)) +
      (if first k.val then u.getReg .x28 else if k.val = 8 then
        u.getMem (BitVec.ofNat 64 (TOPB9 - 240)) else u.getReg .x29) := by
    have he : ((result k.val).toState u).getReg .x23 =
        (if first k.val then (childE k.val).eval u <<< 7
         else (childE k.val).eval u >>> 12) +
        (if first k.val then u.getReg .x28 else if k.val = 8 then
          u.getMem (u.getReg .x9 + BitVec.ofNat 64 (2^64 - 240)) else u.getReg .x29) := by
      fin_cases k <;> rfl
    rw [he, packed_result k u hm hu.hoist, h9]
    have ha : BitVec.ofNat 64 TOPB9 + BitVec.ofNat 64 (2^64 - 240) =
        BitVec.ofNat 64 (TOPB9 - 240) := by decide +kernel
    rw [ha]
    cases first k.val
    · simp only [Bool.false_eq_true, ↓reduceIte, childOfWord, packed_shr]
    · rfl
  rw [hpc, hraw, hA, hB, hC]
  generalize SharedForest.rawChildFromOutput a k = j
  have hbound := j.isLt
  have hk := k.isLt
  have hcw : (SharedLayout.layout k).childWord j = SharedLayout.childWord k.val j.val := rfl
  rw [hcw]
  generalize k.val = n at hk ⊢
  simp only [SharedLayout.childWord, first, pcOf, decide_eq_true_eq]
  split_ifs <;>
    first
    | omega
    | (rw [W9Drv.shl_ofNat, ← BitVec.ofNat_add]; congr 1; rw [Nat.shiftLeft_eq]; omega)

end W9Drv.SharedDispatch

namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def chainEntryState (k : Fin 9) (rank : Fin 563) (u : MachineState) : MachineState :=
  { (result k.val).toState u with
    pc := pcOf ((SharedLayout.layout k).chainWord (N600.embed rank)) }

theorem chain_pre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (rank : Fin 563) (pairs : List (Digest × Digest)) (u : MachineState)
    (hu : SharedCoord.Pre pk w a k.val pairs u) :
    N600.Pre (SharedLayout.layout k) (SharedV3.viewW w k.val u) (idxOf a) k
      (SharedForest.rawChildFromOutput a k) rank (chainEntryState k rank u) := by
  have hm (addr : Word) : (chainEntryState k rank u).getMem addr = u.getMem addr := rfl
  have hr (r : Reg) (h : r ∉ [.x1,.x4,.x8,.x14,.x15,.x16,.x17,.x23,.x25,.x31]) :
      (chainEntryState k rank u).getReg r = u.getReg r := keep k u r h
  have hc := raw_eval pk w a k pairs u hu
  have hi : idxOf a < 2^31 := ClaudeWCT.WCT9.digestIndex_lt a
  have hj := (SharedForest.rawChildFromOutput a k).isLt
  have hnode := nodeWord pk w a k pairs u hu
  refine {
    indexBound := hi
    pc := rfl
    baseReg := ?_
    leafWord := ?_
    nodeWord := hnode
    hashMode := (hr .x5 (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
    stepOne := (hr .x7 (by decide)).trans hu.stepOne
    stepTwo := (hr .x13 (by decide)).trans hu.stepTwo
    hashLen := (hr .x11 (by decide)).trans hu.hashLen
    childPC := child_pc pk w a k pairs u hu
    returnPC := ?_
    heaps := ?_
    witness := by
      intro off ho h8
      rw [hm]
      have hk := k.isLt
      have hr8 := V3.regionOffset_mod k.val
      have hrl := V3.regionOffset_le k.val
      rw [SharedV3.view_word w k.val u _ (by omega) (by unfold V3.regionOffset; omega)]
      by_cases hh : SharedV3.isHand off
      · rw [if_pos ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hh⟩]
        congr 2
        base0; unfold coordinateBase V3.regionOffset
        omega
      · rw [if_neg (fun h => hh (by rw [Nat.add_sub_cancel_left] at h; exact h.2))]
        have hw := hu.coords k.val (Nat.le_refl _) (by omega) off ho h8 (by omega)
          (fun _ => by simpa only [SharedCoord.isHand, if_neg (by omega : k.val ≠ 9)] using hh)
        have he : regionAddr k.val + off - 0x1020 = V3.regionOffset k.val + off := by
          unfold regionAddr V3.regionOffset; omega
        have hb : Chain.base (SharedLayout.layout k) k + off = regionAddr k.val + off := by
          base0; unfold coordinateBase regionAddr; omega
        rw [hb]
        simpa only [W9Machine.OrigW, he] using hw }
  · change ((result k.val).toState u).getReg .x8 = _
    have hb := hu.baseReg
    fin_cases k <;> simp [result, Result.toState_getReg, RegFile.get, RegFile.set, RegFile.init,
      addC_eval, E.eval, hb, W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq, coordinateBase]
  · change ((result k.val).toState u).getReg .x31 = _
    rw [leaf k u hu.childMask hu.hoist, hc, hnode]
    exact W9Drv.leafLow_or _ _ _ k.isLt hj hi
  · change ((result k.val).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h2 h7)

end W9Drv.SharedDispatch


/-! Canonical injection conditions for the shared-path arbitrary-witness source.
The serializer/expander must establish these concrete memory readouts. -/


namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rankOfWord (k : Fin 9) (x : Word) : Word := (x >>> rankPosition k.val) &&& 1023#64

theorem rank_field (a : HashOutput) (k : Fin 9) :
    rankOfWord k (a.extractLsb' (64 * W9Drv.digWord k.val) 64) =
      BitVec.ofNat 64 (SharedForest.rawForestRank a k.val) := by
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> simp [rankOfWord, rankPosition, W9Drv.digWord, SharedForest.rawForestRank,
    SharedForest.rankBase, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, W9Drv.nat_and1023,
    BitVec.toNat_ofNat] <;> omega

theorem padded_field (p : Nat) (hp : p = 13 ∨ p = 25 ∨ p = 37) (x : Word) :
    ((x ||| SharedCoord.rankPad) >>> (p - 8)) &&& 0xfff00#64 =
      (((x >>> p) &&& 1023#64) <<< 8) ||| 0xc0000#64 := by
  rcases hp with rfl | rfl | rfl <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> interval_cases i <;>
    simp [SharedCoord.rankPad]

theorem padded_low (x : Word) :
    (x &&& 0xfff00#64) &&& ~~~1#64 = x &&& 0xfff00#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

/-- The dispatch target (rank field) of coordinate `k`; coordinate 8 masks the hoisted `tp = a7 >>> 17`. -/
theorem pc_shift (k : Fin 9) (u : MachineState)
    (hx4 : k.val = 8 → u.getReg .x4 = u.getReg .x17 >>> 17) :
    (result k.val).pc.eval u =
      (((rankDig k.val).eval u >>> (rankPosition k.val - 8)) &&& u.getReg .x2) &&& ~~~1#64 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change (u.getReg .x4 &&& u.getReg .x2) &&& ~~~1#64 =
      ((u.getReg .x17 >>> 17) &&& u.getReg .x2) &&& ~~~1#64
    rw [hx4 rfl]

theorem pc_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    (result k.val).pc.eval u = pcOf (slotStart + 64 * SharedForest.rawForestRank a k.val) := by
  rw [pc_shift k u hu.hoist, hu.mask, show BitVec.ofNat 64 0xfff00 = 0xfff00#64 from rfl, padded_low,
    rankDig_eval pk w a k pairs u hu,
    padded_field _ (by fin_cases k <;> decide)]
  change (rankOfWord k (a.extractLsb' (64 * W9Drv.digWord k.val) 64) <<< 8) ||| 0xc0000#64 = _
  rw [rank_field]
  have hr : SharedForest.rawForestRank a k.val < 1024 := Nat.mod_lt _ (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    pcOf, slotStart]
  have hlow : SharedForest.rawForestRank a k.val * 2 ^ 8 < 2 ^ 18 := by omega
  rw [Nat.mod_eq_of_lt (by omega : SharedForest.rawForestRank a k.val < 2^64),
    Nat.mod_eq_of_lt (by omega : SharedForest.rawForestRank a k.val * 2^8 < 2^64)]
  have hor : (SharedForest.rawForestRank a k.val * 2^8) ||| 786432 =
      786432 + SharedForest.rawForestRank a k.val * 2^8 := by
    rw [Nat.or_comm, show 786432 = 3 <<< 18 from rfl,
      ← Nat.shiftLeft_add_eq_or_of_lt hlow]
  rw [hor, Nat.mod_eq_of_lt (by omega)]
  omega

end W9Drv.SharedDispatch
namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem core_good (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (rank : Fin 563)
    (v u : MachineState) (padL padR : Digest) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs)
    (hu : N600.Pre (SharedLayout.layout k) (SharedV3.viewW w k.val v) index k raw rank u)
    (hL : DigAt v (0x1020 + V3.regionOffset k.val + 672) padL)
    (hR : DigAt v (0x1020 + V3.regionOffset k.val + 160) padR)
    (hnext : ∀ ends entry, Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val v)
        index k raw u ends entry →
      ∀ computed t, SharedChild.Post (SharedLayout.layout k) k raw entry computed t →
        GoodQFor (P := P) Frozen.image t N C Q A (K computed)) :
    GoodQFor (P := P) Frozen.image u (N + 128) (C + 185) Q
      (A + (N600.rankCost rank + SharedChild.cost k raw))
      (ccM (N600.program w index k raw rank >>= fun ends =>
        SharedV3.childN w index k raw ends padL padR) K) := by
  have hspec : (N600.program w index k raw rank >>= fun ends =>
      SharedV3.childN w index k raw ends padL padR) =
      (N600.program (SharedV3.viewW w k.val v) index k raw rank >>= fun ends =>
        SharedV3.childProgram (SharedV3.viewW w k.val v) index k raw ends) := by
    unfold N600.program
    rw [SharedV3.chainProgram_view]
    simp only [fun ends => SharedV3.childProgram_view w index k v raw ends padL padR hL hR]
  rw [hspec, ccM_bind]
  have hc := chains k rank (SharedV3.viewW w k.val v) index k raw u (N+39) (C+96)
    (A+SharedChild.cost k raw) Q
    (fun ends => ccM (SharedV3.childProgram (SharedV3.viewW w k.val v) index k raw ends) K) hu
    (fun ends entry hp => childs k raw (SharedV3.viewW w k.val v) index ends entry N C A Q K
      (hp.sharedChild hu) (hnext ends entry hp))
  convert hc using 1 <;> first | rfl | omega

def coordN (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (rank : Fin 563) (prev : Digest × Digest) : M (Digest × Digest) :=
  SharedV3.coordinate w index k raw (N600.embed rank) prev

def stepN (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (state : Option (List (Digest × Digest))) (k : Fin 9) : M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if ¬ SharedForest.rawForestRank a k.val < 563 then return none
  let pair ← coordN w (idxOf a) k (SharedForest.rawChildFromOutput a k)
    (SharedForest.forestRank a k.val) (prevOf w pairs)
  pure (some (pairs ++ [pair]))

def ftsN (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) : M (Option (Digest × Digest)) := do
  let some pairs ← (List.finRange 9).foldlM (stepN w a) (some []) | pure none
  pure (some (prevOf w pairs))

theorem prevOf_snoc (w : ClaudeWCT.W9.T3M.WBytes) (pairs : List (Digest × Digest))
    (p : Digest × Digest) : prevOf w (pairs ++ [p]) = p := by
  unfold prevOf; simp

/-- All chain writes lie within the child routine's local frame. -/
theorem chainWrites_childWrites (k : Fin 9) (raw : Fin 128) (addr : Nat)
    (h : Chain.writes (SharedLayout.layout k) k addr) : SharedChild.writes (SharedLayout.layout k) k raw addr := by
  left
  unfold Chain.writes at h; simp only [W9Machine.SharedLayout.base_eq] at h ⊢
  split <;> omega

theorem core_frame (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (v u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hp : Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val v) index k raw u ends entry)
    (ht : SharedChild.Post (SharedLayout.layout k) k raw entry computed t) :
    Frame u t (SharedChild.writes (SharedLayout.layout k) k raw) := by
  intro addr ha hn
  rw [ht.frame addr ha hn]
  exact hp.frame addr ha (fun h => hn (chainWrites_childWrites k raw addr h))

end W9Drv.SharedCoord

namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem writes_bounds (k : Fin 9) (raw : Fin 128) (addr : Nat)
    (h : SharedChild.writes (SharedLayout.layout k) k raw addr) : 1200 ≤ addr ∧ addr < 11792 := by
  have hk := k.isLt
  unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at h; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at h; unfold coordinateBase at h
  split_ifs at h <;> omega

theorem hand_address (k : Fin 9) (raw : Fin 128) :
    SharedChild.handAddr (SharedLayout.layout k) k raw = regionAddr (k.val + 1) +
      (if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0 then SharedV3.handL (k.val + 1)
       else SharedV3.handR (k.val + 1)) := by
  have hk := k.isLt
  unfold SharedChild.handAddr; base0; unfold coordinateBase regionAddr SharedV3.handR SharedV3.handL
  split_ifs <;> omega

theorem frame_after_dispatch (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (rank : Fin 563) (u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hp : Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val u) (idxOf a) k
      (SharedForest.rawChildFromOutput a k) (SharedDispatch.chainEntryState k rank u) ends entry)
    (ht : SharedChild.Post (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k)
      entry computed t) : Frame u t (SharedChild.writes (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k)) := by
  have hf := core_frame w (idxOf a) k (SharedForest.rawChildFromOutput a k) u
    (SharedDispatch.chainEntryState k rank u) entry t ends computed hp ht
  intro addr ha hn
  exact (hf addr ha hn).trans (SharedDispatch.mem k u _)

/-- The unused hand-off slot remains the exact authentication digest supplied
by the witness, including the direct LOW singleton output layout. -/
theorem next_other (w : ClaudeWCT.W9.T3M.WBytes) (k : Fin 9) (raw : Fin 128)
    (u t : MachineState) (hf : Frame u t (SharedChild.writes (SharedLayout.layout k) k raw)) (off : Nat)
    (hoff : off = SharedV3.handL (k.val + 1) ∨ off = SharedV3.handR (k.val + 1))
    (hsel : if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0
      then off = SharedV3.handR (k.val + 1) else off = SharedV3.handL (k.val + 1))
    (h0 : W9Machine.OrigW w u (regionAddr (k.val + 1) + off))
    (h1 : W9Machine.OrigW w u (regionAddr (k.val + 1) + (off + 8))) :
    DigAt t (regionAddr (k.val + 1) + off)
      (SharedV3.topOther w k.val (SharedV3.physical k.val raw.val)) := by
  have hk := k.isLt
  have h1' : W9Machine.OrigW w u (regionAddr (k.val + 1) + off + 8) := by
    rw [Nat.add_assoc]; exact h1
  have hlo : 0x1020 ≤ regionAddr (k.val + 1) + off := by
    unfold SharedV3.handR SharedV3.handL at hoff
    unfold regionAddr
    split_ifs at hoff <;> omega
  have hd := W9Machine.DigAt_origW h0 h1' hlo
  have he : regionAddr (k.val + 1) + off - 0x1020 =
      SharedV3.topOtherOff k.val (SharedV3.physical k.val raw.val) := by
    unfold SharedV3.topOtherOff V3.regionOffset regionAddr
    unfold SharedV3.handR SharedV3.handL at hsel ⊢
    split_ifs at hsel ⊢ <;> omega
  rw [he] at hd
  refine hd.frame hf (by
    unfold SharedV3.handR SharedV3.handL at hoff
    unfold regionAddr
    split_ifs at hoff <;> omega) ?_ ?_
  all_goals
    intro hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at hw; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw; unfold coordinateBase at hw
    unfold SharedV3.handR SharedV3.handL at hoff hsel
    unfold regionAddr at hw
    split_ifs at hsel hw <;> omega

end W9Drv.SharedCoord

namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem next (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (rank : Fin 563) (pairs : List (Digest × Digest)) (u entry t : MachineState) (ends : List Digest) (computed : Digest)
    (hu : Pre pk w a k.val pairs u)
    (hp : Chain.Post (SharedLayout.layout k) (SharedV3.viewW w k.val u) (idxOf a) k (SharedForest.rawChildFromOutput a k)
      (SharedDispatch.chainEntryState k rank u) ends entry)
    (ht : SharedChild.Post (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) entry computed t) :
    Pre pk w a (k.val+1) (pairs ++ [if SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 0
      then (computed, SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val))
      else (SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val), computed)]) t := by
  have hk := k.isLt
  have hc := SharedDispatch.chain_pre pk w a k rank pairs u hu
  have hf := frame_after_dispatch w a k rank u entry t ends computed hp ht
  have hm (A : Nat) (hA : A < 2^64) (hs : A < 1200 ∨ 11792 ≤ A) :
      t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    intro hw
    have := writes_bounds k (SharedForest.rawChildFromOutput a k) A hw
    omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      t.getReg r = (SharedDispatch.chainEntryState k rank u).getReg r := by
    rw [ht.keep r (by
      simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x4,.x8,.x14,.x15,.x16,.x17,.x23,.x25,.x31]) :
      (SharedDispatch.chainEntryState k rank u).getReg r = u.getReg r := SharedDispatch.keep k u r h
  have hdr : ∀ i, 4 ≤ i → i < 6 → ¬ SharedChild.writes (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) (WIT + 8 * i) := by
    intro i h4 h6 hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at hw; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw; unfold coordinateBase WIT at hw
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
    · refine ⟨?_, fun lay hl => ?_, ?_, ?_⟩
      · rw [hm (TOPBASE-8) (by unfold TOPBASE; omega) (Or.inr (by unfold TOPBASE; omega))]
        exact hdata.mask
      · have hb := hdrAddr_bounds lay
        rw [hm (hdrAddr lay) (by unfold TOPBASE at *; omega) (Or.inr (by unfold TOPBASE at *; omega))]
        exact hdata.header lay hl
      · rw [hm (TOPB9+56) (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))]
        exact hdata.buffer3
      · rw [hm (TOPB9-288) (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))]
        exact hdata.mask6
  have hb6 : SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 0 ∨ SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 1 := by unfold SharedV3.direction; omega
  have hra := regionAddr_succ k.val hk
  have hbase : coordinateBase k = regionAddr k.val := by base0; unfold coordinateBase regionAddr; omega
  have hR9 : regionAddr (k.val + 1) ≥ 496 := by unfold regionAddr; omega
  -- the other top sibling, from the witness (region k+1 is untouched outside one hand-off slot)
  have hother : ∀ off, (off = SharedV3.handL (k.val + 1) ∨ off = SharedV3.handR (k.val + 1)) →
      (if SharedV3.direction k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val) = 0 then off = SharedV3.handR (k.val + 1) else off = SharedV3.handL (k.val + 1)) →
      DigAt t (regionAddr (k.val + 1) + off) (SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val)) := by
    intro off hoff hsel
    have ho : off ≤ 816 ∧ off % 8 = 0 ∧ (k.val + 1 = 9 → 768 ≤ off) := by
      unfold SharedV3.handR SharedV3.handL at hoff
      split_ifs at hoff <;> omega
    exact next_other w k _ u t hf off hoff hsel
      (hu.coords (k.val + 1) (by omega) (by omega) off (by omega) (by omega) ho.2.2
        (fun h => by omega))
      (hu.coords (k.val + 1) (by omega) (by omega) (off + 8) (by omega) (by omega) (fun h => by have := ho.2.2 h; omega)
        (fun h => by omega))
  have htop : DigAt t (SharedChild.handAddr (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k)) computed := ht.top
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
    d0 := (hm _ (by unfold dataBase7; omega) (Or.inr (by unfold dataBase7; omega))).trans hu.d0
    nodeReg := ?_
    cached3 := ?_
    cached := ?_
    mask := (hr .x2 (by decide)).trans ((hd .x2 (by decide)).trans hu.mask)
    childMask := (hr .x27 (by decide)).trans ((hd .x27 (by decide)).trans hu.childMask)
    aTable := (hr .x28 (by decide)).trans ((hd .x28 (by decide)).trans hu.aTable)
    singletonTable := (hm _ (by unfold TOPB9; omega) (Or.inr (by unfold TOPB9; omega))).trans hu.singletonTable
    jt := (hr .x24 (by decide)).trans ((hd .x24 (by decide)).trans hu.jt)
    childBlock := (hr .x29 (by decide)).trans ((hd .x29 (by decide)).trans hu.childBlock)
    baseReg := ?_
    pairPtr := ?_
    prevL := ?_
    prevR := ?_
    a2 := ?_
    coords := ?_
    layer := ?_
    hoist := ?_ }
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
    change ((SharedDispatch.result k.val).toState u).getReg .x15 = _
    rw [SharedDispatch.nodeWord pk w a k pairs u hu,
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
  · rw [hr .x8 (by decide), show k.val + 1 - 1 = k.val by omega]
    have hb := hc.baseReg
    simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq, coordinateBase] at hb
    rw [hb]
    congr 1
    try omega
  · rw [hr .x9 (by decide)]
    exact (SharedDispatch.keep k u .x9 (by decide)).trans hu.pairPtr
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      have e : SharedChild.handAddr (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) = regionAddr (k.val + 1) + SharedV3.handL (k.val + 1) := by
        rw [hand_address, if_pos h0]
      rw [← e]; exact htop
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      exact hother (SharedV3.handL (k.val + 1)) (Or.inl rfl) (by rw [if_neg (by omega)])
  · rw [prevOf_snoc]
    rcases hb6 with h0 | h1
    · simp only [h0, if_true]
      exact hother (SharedV3.handR (k.val + 1)) (Or.inr rfl) (by rw [if_pos h0])
    · simp only [h1, show (1 : Nat) ≠ 0 by decide, if_false]
      have e : SharedChild.handAddr (SharedLayout.layout k) k (SharedForest.rawChildFromOutput a k) = regionAddr (k.val + 1) + SharedV3.handR (k.val + 1) := by
        rw [hand_address, if_neg (by omega)]
      rw [← e]; exact htop
  · intro _
    have h12 := ht.a2
    unfold SharedChild.outputAddr SharedChild.handAddr at h12
    split_ifs at h12
    all_goals first
      | (left; rw [h12]; congr 1; base0; unfold coordinateBase regionAddr; split_ifs <;> omega)
      | (right; rw [h12]; congr 1; base0; unfold coordinateBase regionAddr; split_ifs <;> omega)
  · intro m hm1 hm9 off hoff h8 hv hh
    have h0 := hu.coords m (by omega) hm9 off hoff h8 hv (fun h => by omega)
    unfold W9Machine.OrigW at h0 ⊢
    rw [← h0]
    apply hf _ (by unfold regionAddr; omega)
    intro hw
    unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at hw; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw; unfold coordinateBase at hw
    have hmk : regionAddr m + 848 ≤ regionAddr k.val := by unfold regionAddr; omega
    rcases Nat.lt_or_ge (k.val + 1) m with hgt | hle
    · have : regionAddr m + 848 ≤ regionAddr (k.val + 1) := by unfold regionAddr; omega
      try simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at *
      unfold coordinateBase regionAddr at *
      split_ifs at hw <;> omega
    · have hm' : m = k.val + 1 := by omega
      subst hm'
      have hn := hh rfl
      unfold isHand SharedV3.isHand at hn
      try simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at *
      unfold coordinateBase regionAddr at *
      split_ifs at hn <;> split_ifs at hw <;> omega
  · exact hu.layer.frame (fun j hj h => hf _ (by unfold WIT WX at *; omega)
      (by intro hw; unfold SharedChild.writes SharedChild.outputAddr SharedChild.handAddr at *; simp only [W9Machine.Frozen.base_eq, W9Machine.SharedLayout.base_eq] at hw ⊢; unfold coordinateBase regionAddr WIT at *; split_ifs at hw <;> omega))
  · -- dispatch hoist: `tp = a7 >>> 17` from coordinate 7's dispatcher; the chain (`Chain.clobbers`) and B′ child
    -- (`Child.clobbers`) routines keep both `tp` and `a7`.
    intro h8
    have hk7 : k = ⟨7, by decide⟩ := Fin.ext (show k.val = 7 by omega)
    subst hk7
    rw [hr .x4 (by decide), hr .x17 (by decide)]
    change ((SharedDispatch.result 7).toState u).getReg .x4 =
      ((SharedDispatch.result 7).toState u).getReg .x17 >>> 17
    exact SharedDispatch.hoist_seven u

end W9Drv.SharedCoord

namespace W9Drv.SharedDispatch
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem steps (links : ∀ k : Fin 9, sliceChecked (start k.val) (words k.val) = true)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : SharedCoord.Pre pk w a k.val pairs u) :
    Steps Frozen.image u (length k.val) (length k.val) ((result k.val).toState u) := by
  have hpc : u.pc = pcOf (start k.val) := by
    rw [hu.pc]; fin_cases k <;> rfl
  have hs := symRun_sound (rOK_eq (checked k)) (slice_at _ _ (links k)) u hpc
  have hcost : (result k.val).steps = length k.val ∧ (result k.val).cycles = length k.val := by
    fin_cases k <;> exact ⟨rfl, rfl⟩
  rw [hcost.1, hcost.2] at hs
  apply hs
  change Oblig.all u (result k.val).st.obl
  rw [Oblig.all_iff]
  intro o ho
  by_cases hc : k.val = 8
  · have he : k = ⟨8, by decide⟩ := Fin.ext hc
    subst k
    change o ∈ [.valid ⟨some (.reg .x9), BitVec.ofNat 64 (2^64 - 240)⟩ 8] at ho
    simp only [List.mem_singleton] at ho
    subst o
    change accessValid (u.getReg .x9 + BitVec.ofNat 64 (2^64 - 240)) 8 = true
    rw [hu.pairPtr]
    decide +kernel
  · have ho' : (result k.val).st.obl = [] := by
      fin_cases k <;> first | rfl | exact (hc rfl).elim
    rw [ho'] at ho
    simp at ho

end W9Drv.SharedDispatch

namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem good (links : ∀ k : Fin 9, sliceChecked (SharedDispatch.start k.val) (SharedDispatch.words k.val) = true)
    (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (pairs : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Option (List (Digest × Digest)) → OracleComp HashSpec Obs)
    (hu : Pre pk w a k.val pairs u) (hnone : K none = pure (false, 0))
    (hnext : ∀ pair t, Pre pk w a (k.val+1) (pairs ++ [pair]) t →
      GoodQFor (P := P) Frozen.image t N C Q A (K (some (pairs ++ [pair])))) :
    GoodQFor (P := P) Frozen.image u (N + (SharedDispatch.length k.val + 185))
      (C + (SharedDispatch.length k.val + 185)) Q
      (A + (SharedDispatch.length k.val + (N600.rankCost (SharedForest.forestRank a k.val) +
        SharedChild.cost k (SharedForest.rawChildFromOutput a k))))
      (ccM (stepN w a (some pairs) k) K) := by
  have ds := SharedDispatch.steps links pk w a k pairs u hu
  have hpc : ((SharedDispatch.result k.val).toState u).pc =
      pcOf (slotStart + 64 * SharedForest.rawForestRank a k.val) :=
    SharedDispatch.pc_eval pk w a k pairs u hu
  have hfb : SharedForest.rawForestRank a k.val < 1024 := Nat.mod_lt _ (by decide)
  by_cases hok : SharedForest.rawForestRank a k.val < 563
  · have hrank : (SharedForest.forestRank a k.val).val = SharedForest.rawForestRank a k.val :=
      Nat.mod_eq_of_lt hok
    have hst : SharedDispatch.chainEntryState k (SharedForest.forestRank a k.val) u =
        (SharedDispatch.result k.val).toState u := by
      unfold SharedDispatch.chainEntryState
      rw [SharedLayout.chain_eq, slot_entry, hrank, ← hpc]
    have hk := k.isLt
    have hreg : 0x1020 + V3.regionOffset k.val = regionAddr k.val := by
      unfold V3.regionOffset regionAddr; omega
    have core := core_good chains childs w (idxOf a) k (SharedForest.rawChildFromOutput a k)
      (SharedForest.forestRank a k.val) u (SharedDispatch.chainEntryState k (SharedForest.forestRank a k.val) u)
      (prevOf w pairs).1 (prevOf w pairs).2 N C A Q
      (fun top => K (some (pairs ++ [SharedV3.orderPair k.val
        (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val)
        top (SharedV3.topOther w k.val (SharedV3.physical k.val (SharedForest.rawChildFromOutput a k).val))])))
      (SharedDispatch.chain_pre pk w a k (SharedForest.forestRank a k.val) pairs u hu)
      (by rw [hreg]; simpa only [SharedV3.handL, if_neg (by omega : k.val ≠ 9)] using hu.prevL)
      (by rw [hreg]; simpa only [SharedV3.handR, if_neg (by omega : k.val ≠ 9)] using hu.prevR)
      (fun ends entry hp computed t ht => hnext _ _
        (next pk w a k (SharedForest.forestRank a k.val) pairs u entry t ends computed hu hp ht))
    rw [hst] at core
    have full := core.steps ds
    simp only [stepN, coordN, hok, not_true_eq_false, ↓reduceIte, SharedV3.coordinate,
      ccM_bind, ccM_pure, bind_assoc, pure_bind]
    simp only [N600.program, ccM_bind] at full
    exact full.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · have hpast := fetch_invalid_slot _ _ hpc (by omega) hfb
    have rr : GoodQFor (P := P) Frozen.image ((SharedDispatch.result k.val).toState u) 1 0 Q 0
        (pure (false, 0)) := goodQFor_fault hpast
    have full := rr.steps ds
    simp only [stepN, hok, not_false_eq_true, ↓reduceIte, ccM_pure, hnone]
    exact full.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)

end W9Drv.SharedCoord


namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finishN (w : ClaudeWCT.W9.T3M.WBytes) (state : Option (List (Digest × Digest))) :
    M (Option (Digest × Digest)) :=
  match state with
  | none => pure none
  | some pairs => pure (some (prevOf w pairs))
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => SharedDispatch.length k.val + 185)).sum
def coordsAccept (a : HashOutput) (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => SharedDispatch.length k.val +
    (N600.rankCost (SharedForest.forestRank a k.val) + SharedChild.cost k (SharedForest.rawChildFromOutput a k)))).sum

theorem fold_none (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (stepN w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, stepN, pure_bind] using ih

theorem all_good
    (links : ∀ k : Fin 9, sliceChecked (SharedDispatch.start k.val) (SharedDispatch.words k.val) = true)
    (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw)
    (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (ks : List (Fin 9)) (n : Nat) (pairs : List (Digest × Digest)) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs)
    (horder : ks.map Fin.val = List.range' n ks.length) (hend : n + ks.length = 9)
    (hu : Pre pk w a n pairs u) (hnone : K none = pure (false, 0))
    (hnext : ∀ pairs t, Pre pk w a 9 pairs t →
      GoodQFor (P := P) Frozen.image t N C Q A (K (some (prevOf w pairs)))) :
    GoodQFor (P := P) Frozen.image u (N + coordsCost ks) (C + coordsCost ks) Q (A + coordsAccept a ks)
      (ccM (ks.foldlM (stepN w a) (some pairs) >>= finishN w) K) := by
  induction ks generalizing n pairs u with
  | nil =>
    have hn : n = 9 := by simpa using hend
    subst n
    simp only [List.foldlM_nil, pure_bind, finishN, ccM_pure]
    simpa [coordsCost, coordsAccept] using hnext pairs u hu
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at horder
    obtain ⟨hn, ht⟩ := horder
    subst n
    let K' : Option (List (Digest × Digest)) → OracleComp HashSpec Obs := fun state =>
      ccM (ks.foldlM (stepN w a) state >>= finishN w) K
    have hkNone : K' none = pure (false, 0) := by
      simp only [K', fold_none, pure_bind, finishN, ccM_pure, hnone]
    have hstep := good links chains childs pk w a k pairs u (N + coordsCost ks)
      (C + coordsCost ks) (A + coordsAccept a ks) Q K' hu hkNone
      (fun pair t hh => ih (k.val + 1) (pairs ++ [pair]) t ht
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend) hh)
    simp only [List.foldlM_cons, bind_assoc, ccM_bind]
    convert hstep using 1 <;> simp [coordsCost, coordsAccept, Nat.add_left_comm, Nat.add_comm,
      K', ccM_bind] <;> omega

end W9Drv.SharedCoord


namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option maxRecDepth 100000 in
/-- C1: the machine routine cost equals the fixed part (A 77, B and C 89) plus the source's per-child accounting
correction `2 - skips′`, for every coordinate and raw child (checked over all 9 x 128 cases). -/
theorem child_cost_all : ∀ k : Fin 9, ∀ raw : Fin 128,
    SharedChild.cost k raw = (if SharedV3.first k.val then 77 else 89) +
      SharedForest.accountingCorrection k.val raw := by
  decide +kernel

theorem child_cost_eq (k : Fin 9) (raw : Fin 128) :
    SharedChild.cost k raw = (if SharedV3.first k.val then 77 else 89) +
      SharedForest.accountingCorrection k.val raw :=
  child_cost_all k raw

theorem coordsAccept_all (a : HashOutput) :
    coordsAccept a (List.finRange 9) = 846 + SharedForest.jointAccountingCost a := by
  unfold coordsAccept
  simp_rw [child_cost_eq]
  have hfixed : ((List.finRange 9).map (fun k =>
      SharedDispatch.length k.val + (if SharedV3.first k.val then 77 else 89))).sum = 846 := by decide +kernel
  have hpoint : ∀ k : Fin 9,
      SharedDispatch.length k.val + (N600.rankCost (SharedForest.forestRank a k.val) +
        ((if SharedV3.first k.val then 77 else 89) + SharedForest.accountingCorrection k.val (SharedForest.rawChildFromOutput a k))) =
      (SharedDispatch.length k.val + (if SharedV3.first k.val then 77 else 89)) +
        SharedForest.coordinateAccountingCost a k := by
    intro k
    rw [N600.rankCost_eq_c1]
    unfold SharedForest.coordinateAccountingCost
    omega
  simp_rw [hpoint]
  rw [List.sum_map_add, hfixed]
  rfl

theorem final (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : Pre pk w a 9 pairs u) :
    FtsOut ⟨pk,w,a⟩ (prevOf w pairs) u := by
  refine ⟨hu.glob, hu.index, ?_, ?_, ?_, hu.layer, ?_, hu.hashLen,
    hu.heaps 6 (by decide) (by decide), hu.stepOne, hu.stepTwo,
    hu.heaps 7 (by decide) (by decide), hu.heaps 3 (by decide) (by decide),
    hu.heaps 4 (by decide) (by decide), hu.heaps 5 (by decide) (by decide),
    hu.coordStep, hu.pairPtr, hu.bank.top, hu.bank.top8, ?_, hu.d0⟩
  · exact hu.pc
  · have h := hu.prevL
    rwa [show regionAddr 9 + SharedV3.handL 9 = WIT by rfl] at h
  · have h := hu.prevR
    rwa [show regionAddr 9 + SharedV3.handR 9 = WIT + 48 by rfl] at h
  · rw [hu.baseReg]; rfl
  · exact hu.a2 (by decide)

end W9Drv.SharedCoord


namespace W9Drv.SharedCoord
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.Research
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def FtsGoodByCost (acceptCost : HashOutput → Nat) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs),
    SharedGate.Pre pk w a u → K none = pure (false, 0) →
    (∀ top t, FtsOut ⟨pk,w,a⟩ top t →
      GoodQFor (P := P) Frozen.image t N C Q A (K (some top))) →
    GoodQFor (P := P) Frozen.image u (N+2023) (C+2023) Q (A+acceptCost a)
      (ccM (if SharedGate.gateOk a then ftsN w a else pure none) K)

/-- C1 (stage 1) + coordinate-8 dispatch hoist: 24 (gate and setup) + 93 (dispatch) + 4 x 77 + 5 x 89 (child fixed
parts) = 870, plus the joint accounting cost (`≤ 777` on accepted digests, cap 777). -/
def ftsAcceptCost (a : HashOutput) : Nat := 870 + SharedForest.jointAccountingCost a

theorem fts_good_of
    (checkLink : sliceChecked 4 SharedGate.gCheckWords = true)
    (setupLink : sliceChecked 68 SharedGate.gSetupWords = true)
    (links : ∀ k : Fin 9, sliceChecked (SharedDispatch.start k.val) (SharedDispatch.words k.val) = true)
    (chains : ∀ k : Fin 9, N600.AllGood (P := P) (SharedLayout.layout k))
    (childs : ∀ (k : Fin 9) (raw : Fin 128), SharedChild.Good (P := P) (SharedLayout.layout k) k raw) :
    FtsGoodByCost ftsAcceptCost (P := P) := by
  intro pk w a u N C A Q K hu hnone hnext
  let KG : Bool → OracleComp HashSpec Obs := fun b =>
    if b then ccM (ftsN w a) K else K none
  have hg := SharedGate.good checkLink setupLink pk w a u (N + 1758) (C + 1758)
    (A + (846 + SharedForest.jointAccountingCost a)) Q KG hu
    (by simpa only [KG, Bool.false_eq_true, ↓reduceIte] using hnone)
    (fun t ht => by
      have hc := all_good links chains childs pk w a (List.finRange 9) 0 [] t N C A Q K
        (by decide) (by simp) ht hnone (fun pairs st hh => hnext _ st (final pk w a pairs st hh))
      rw [show coordsCost (List.finRange 9) = 1758 by decide, coordsAccept_all] at hc
      apply hc.congr
      change ccM (_ >>= finishN w) K = ccM (ftsN w a) K
      apply congrArg (fun p : M (Option (Digest × Digest)) => ccM p K)
      unfold ftsN
      apply congrArg (fun f : Option (List (Digest × Digest)) → M (Option (Digest × Digest)) =>
        (List.finRange 9).foldlM (stepN w a) (some []) >>= f)
      funext state
      cases state <;> rfl)
  change GoodQFor (P := P) Frozen.image u (N + 1782) (C + 1782) Q
    (A + (846 + SharedForest.jointAccountingCost a) + 24) (KG (SharedGate.gateOk a)) at hg
  apply (hg.mono (by omega) (by omega) (fun hq => ⟨hq, by simp only [ftsAcceptCost]; omega⟩)).congr
  cases SharedGate.gateOk a <;> simp [KG, ccM_pure]

end W9Drv.SharedCoord

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure ChainReadout (w : SharedV3.WBytes) (coord : Fin 9) (word : Rank)
    (values : Fin 6 → Digest) : Prop where
  padA : ∀ i : Fin 6, V3.chainPadA w coord.val i.val = 0
  padB : ∀ i : Fin 6, V3.chainPadB w coord.val i.val = 0
  padC : ∀ i : Fin 6, V3.chainPadC w coord.val i.val = 0
  reveal : ∀ i : Fin 6, V3.reveal w coord.val i.val (wordDigit word i) = values i

structure PathReadout (w : SharedV3.WBytes) (coord : Fin 9) (raw : Child)
    (path : Nat → Digest) : Prop where
  headerPads : ∀ l, l ≤ SharedV3.lastLevel coord.val →
    SharedV3.nodeHPad w coord.val (SharedV3.physical coord.val raw.val) l = 0
  nodePads : ∀ l, l ≤ SharedV3.lastLevel coord.val → l ≠ 4 →
    SharedV3.nodePad w coord.val (SharedV3.physical coord.val raw.val) l = 0
  siblings : ∀ l, l ≤ SharedV3.lastLevel coord.val →
    SharedV3.sibling w coord.val (SharedV3.physical coord.val raw.val) l = path l
  topOther : SharedV3.topOther w coord.val (SharedV3.physical coord.val raw.val) =
    path (SharedV3.lastLevel coord.val + 1)

theorem chainProgram_zero (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest)
    (hi : index < 2 ^ 31) (h : ChainReadout w coord word values) :
    V3.chainProgram w index coord raw (ClaudeWCT.WCT9.embed word) =
      (List.finRange 6).mapM (fun i =>
        ClaudeWCT.WCT9.chain index coord.val raw.val i.val (4 - wordDigit word i)
          (wordDigit word i) (values i)) := by
  unfold V3.chainProgram
  congr 1
  funext i
  change V3.chainP index coord.val raw.val i.val (4 - wordDigit word i) (wordDigit word i)
    (V3.chainPadA w coord.val i.val) (V3.chainPadB w coord.val i.val)
    (V3.chainPadC w coord.val i.val) (V3.reveal w coord.val i.val (wordDigit word i)) = _
  rw [h.padA, h.padB, h.padC, h.reveal,
    W9Machine.chainP_canonical _ _ _ _ _ _ _ _ _ _ hi coord.isLt raw.isLt i.isLt
      (by have := wordDigit_le_four word i; omega),
    ClaudeWCT.W9.T3M.wctChainP_zero]

theorem nodeInput_zero_header (coord : Fin 9) (index heap : Nat)
    (left pad right : Digest) :
    V3.nodeInput coord.val index heap left 0 pad right =
      wctTopInput coord.val index heap left pad right := by
  unfold V3.nodeInput wctTopInput wctNodeHeader
  rw [W9Drv.nodeHdr_canonical, SigGolfCandidate.T3M.SecurityInputs.withHigh_nodeTweak_zero]

theorem short_topInput_zero (coord index heap : Nat) (left right : Digest) :
    shortHash (wctTopInput coord index heap left 0 right) =
      wctNodeHash coord index heap left right := by
  rw [ClaudeWCT.WCT9.wctNodeHash_eq_short]
  simp only [wctTopInput, wctNodeHeader, SigGolfCandidate.T3M.bytesLE_zero16]

/-- C1: the machine's half selector is the source's `ftsHash` rule once the selector agrees with
`ftsHighHeap` of the computed heap. -/
theorem hashSel_eq_ftsHash {hi : Bool} {heap : Nat} (h : hi = ftsHighHeap heap) (input : HashInput) :
    SharedV3.hashSel hi input = ftsHash heap input := by
  subst h
  rfl

/-- C1: a packed node (zero pad) with the half selected by `hi = ftsHighHeap heap` is the source's
`wctNodeHashH`. -/
theorem sel_topInput_zero {coord index heap : Nat} {hi : Bool} (h : hi = ftsHighHeap heap)
    (left right : Digest) :
    SharedV3.hashSel hi (wctTopInput coord index heap left 0 right) =
      wctNodeHashH coord index heap left right := by
  rw [hashSel_eq_ftsHash h]
  simp only [wctTopInput, wctNodeHashH, SigGolfCandidate.T3M.bytesLE_zero16]

set_option maxRecDepth 100000 in
/-- C1: the machine selector of the leaf (`m = 0`) and of the packed fold outputs (`m = 1..4`) is the source's
`ftsHighHeap` of heap `(128 + child) / 2 ^ m`. -/
theorem hiOut_heap_all : ∀ child : Fin 128, ∀ m : Fin 5,
    SharedV3.hiOut child.val m.val = ftsHighHeap ((128 + child.val) / 2 ^ m.val) := by
  decide +kernel

theorem hiOut_heap (child m : Nat) (hc : child < 128) (hm : m < 5) :
    SharedV3.hiOut child m = ftsHighHeap ((128 + child) / 2 ^ m) :=
  hiOut_heap_all ⟨child, hc⟩ ⟨m, hm⟩

/-- The verifier's leaf input is the source's padded leaf input. -/
theorem leafInput_eq (k index j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    V3.leafInput k index j pad ends = ClaudeWCT.WCT9.leafInputP index k j pad ends := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5], _ =>
    simp only [V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, V3.leafFields, ClaudeWCT.WCT9.leafInputP,
      List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc]
    all_goals rfl

/-- C1: the verifier's half-selected leaf of physical child `child` (raw child `raw` in the header) is the source's
`leafHashH` at heap `128 + child`. -/
theorem leafSel_eq (k index raw child : Nat) (hc : child < 128) (pad : Digest) (ends : List Digest)
    (h : ends.length = 6) :
    SharedV3.hashSel (SharedV3.hiOut child 0) (V3.leafInput k index raw pad ends) =
      leafHashH (128 + child) index k raw pad ends := by
  rw [leafInput_eq _ _ _ _ _ h, leafHashH_eq]
  exact hashSel_eq_ftsHash (by rw [hiOut_heap child 0 hc (by decide), Nat.pow_zero, Nat.div_one]) _

theorem childInput_readout (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (path : Nat → Digest) (padR value : Digest) (level : Nat)
    (h : PathReadout w coord raw path) (hl : level ≤ SharedV3.lastLevel coord.val) :
    SharedV3.childInput w index coord.val (SharedV3.physical coord.val raw.val) padR value level =
      let child := SharedV3.physical coord.val raw.val
      let other := path level
      let left := if child / 2 ^ level % 2 = 0 then value else other
      let right := if child / 2 ^ level % 2 = 0 then other else value
      wctTopInput coord.val index ((128 + child) / 2 ^ (level + 1)) left
        (if level = 4 then padR else 0) right := by
  simp only [SharedV3.childInput, h.siblings level hl, h.headerPads level hl,
    nodeInput_zero_header]
  by_cases he : level = 4
  · simp only [if_pos he]
  · simp only [if_neg he, h.nodePads level hl he]


def canonicalChildInput (index coord physical : Nat) (path : Nat → Digest)
    (padR value : Digest) (level : Nat) : HashInput :=
  let other := path level
  let left := if physical / 2 ^ level % 2 = 0 then value else other
  let right := if physical / 2 ^ level % 2 = 0 then other else value
  wctTopInput coord index ((128 + physical) / 2 ^ (level + 1)) left
    (if level = 4 then padR else 0) right

def canonicalChildN (index : Nat) (coord : Fin 9) (raw : Child)
    (ends : List Digest) (padL padR : Digest) (path : Nat → Digest) : M Digest := do
  let leaf ← leafHashH (128 + SharedV3.physical coord.val raw.val) index coord.val raw.val padL ends
  let child := SharedV3.physical coord.val raw.val
  let last := SharedV3.lastLevel coord.val
  let value ← (List.range last).foldlM
    (fun value level => SharedV3.hashSel (SharedV3.hiOut child (level + 1))
      (canonicalChildInput index coord.val child path padR value level)) leaf
  if coord.val = 8 then
    SharedV3.hashSel (decide (SharedV3.direction coord.val child = 0))
      (canonicalChildInput index coord.val child path padR value last)
  else highHash (canonicalChildInput index coord.val child path padR value last)

theorem childN_canonical (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (path : Nat → Digest) (ends : List Digest) (hlen : ends.length = 6)
    (padL padR : Digest) (h : PathReadout w coord raw path) :
    SharedV3.childN w index coord raw ends padL padR =
      canonicalChildN index coord raw ends padL padR path := by
  unfold SharedV3.childN canonicalChildN
  rw [leafSel_eq _ _ _ _ (SharedV3.physical_lt _ _ raw.isLt) _ _ hlen]
  apply bind_congr
  intro leaf
  dsimp only
  have hf : (List.range (SharedV3.lastLevel coord.val)).foldlM
      (fun value level => SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) (level + 1))
        (SharedV3.childInput w index coord.val (SharedV3.physical coord.val raw.val) padR value level)) leaf =
      (List.range (SharedV3.lastLevel coord.val)).foldlM
      (fun value level => SharedV3.hashSel (SharedV3.hiOut (SharedV3.physical coord.val raw.val) (level + 1))
        (canonicalChildInput index coord.val (SharedV3.physical coord.val raw.val) path padR value level)) leaf := by
    apply foldlM_congr_mem
    intro value level hl
    rw [childInput_readout _ _ _ _ _ _ _ _ h (by have := List.mem_range.mp hl; omega)]
    rfl
  rw [hf]
  apply bind_congr
  intro value
  rw [childInput_readout _ _ _ _ _ _ _ _ h le_rfl]
  rfl

theorem length_of_support_mapM {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [length_of_support_mapM f xs zs hzs]

def canonicalCoordinate (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) : M PairRoot := do
  let ends ← (List.finRange 6).mapM fun i =>
    ClaudeWCT.WCT9.chain index coord.val raw.val i.val (4 - wordDigit word i)
      (wordDigit word i) (values i)
  let computed ← canonicalChildN index coord raw ends prev.1 prev.2 path
  pure (SharedV3.orderPair coord.val (SharedV3.physical coord.val raw.val) computed
    (path (SharedV3.lastLevel coord.val + 1)))

theorem coordinate_canonical (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest)
    (prev : PairRoot) (hi : index < 2 ^ 31)
    (hc : ChainReadout w coord word values) (hp : PathReadout w coord raw path) :
    SharedV3.coordinate w index coord raw (ClaudeWCT.WCT9.embed word) prev =
      canonicalCoordinate index coord raw word values path prev := by
  unfold SharedV3.coordinate canonicalCoordinate
  rw [chainProgram_zero _ _ _ _ _ _ hi hc]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro ends hends
  have hlen : ends.length = 6 := by
    simpa using length_of_support_mapM _ (List.finRange 6) ends hends
  rw [childN_canonical _ _ _ _ _ _ hlen _ _ hp, hp.topOther]

end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def canonicalInnerStep (first : Bool) (index coord child : Nat) (path : Nat → Digest)
    (prev : PairRoot) (value : Digest) (level : Nat) : M Digest :=
  let other := path level
  let lr := if child / 2 ^ level % 2 = 0 then (value, other) else (other, value)
  sharedNode first coord index ((128 + child) / 2 ^ (level + 1)) (fun _ => prev) lr.1 lr.2

theorem canonicalInnerStep_eq (first : Bool) (index coord child : Nat) (hc : child < 128)
    (path : Nat → Digest) (prev : PairRoot) (value : Digest) (level : Nat) (hl : level < 5) :
    canonicalInnerStep first index coord child path prev value level =
      if level = 4 ∧ first then highHash (canonicalChildInput index coord child path prev.2 value level)
      else SharedV3.hashSel (SharedV3.hiOut child (level + 1))
        (canonicalChildInput index coord child path prev.2 value level) := by
  unfold canonicalInnerStep canonicalChildInput
  by_cases he : level = 4
  · subst level
    have hge : ¬(128 + child) / 2 ^ (4 + 1) < 4 := by norm_num; omega
    have hlt : (128 + child) / 2 ^ (4 + 1) < 8 := by norm_num; omega
    have h5 : SharedV3.hiOut child (4 + 1) = false := by simp [SharedV3.hiOut]
    simp only [sharedNode, if_neg hge, if_pos hlt, if_true, true_and, h5]
    cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      split_ifs <;> rfl
  · have hge : ¬(128 + child) / 2 ^ (level + 1) < 8 := by
      interval_cases level <;> norm_num at * <;> omega
    have hg4 : ¬(128 + child) / 2 ^ (level + 1) < 4 := by omega
    simp only [sharedNode, if_neg hg4, if_neg hge, he, false_and, ↓reduceIte]
    rw [sel_topInput_zero (hiOut_heap child (level + 1) hc (by omega))]
    split_ifs <;> rfl

def sourceCoordinate (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) : M PairRoot := do
  let child : Child := ⟨SharedV3.physical coord.val raw.val, SharedV3.physical_lt _ _ raw.isLt⟩
  let inner ← recoverSharedInner (SharedV3.first coord.val) index coord.val child word values path prev
  if SharedV3.first coord.val then
    pure (SharedV3.orderPair coord.val child.val inner (path 5))
  else
    let lr := if child.val / 32 % 2 = 0 then (inner, path 5) else (path 5, inner)
    let outer ← sharedOuterHash coord.val index (2 + child.val / 64) lr.1 lr.2
    pure (SharedV3.orderPair coord.val child.val outer (path 6))

theorem recoverSharedInner_false (index coord : Nat) (child : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    recoverSharedInner false index coord child word values path prev = (do
      let ends ← (List.finRange 6).mapM fun i =>
        ClaudeWCT.WCT9.chain index coord (rawChild false child.val) i.val (4 - wordDigit word i)
          (wordDigit word i) (values i)
      let leaf ← leafHashH (128 + child.val) index coord (rawChild false child.val) prev.1 ends
      (List.range 5).foldlM (fun value level =>
        SharedV3.hashSel (SharedV3.hiOut child.val (level + 1))
          (canonicalChildInput index coord child.val path prev.2 value level)) leaf) := by
  unfold recoverSharedInner
  apply bind_congr
  intro ends
  apply bind_congr
  intro leaf
  apply foldlM_congr_mem
  intro value level hl
  exact (canonicalInnerStep_eq false index coord child.val child.isLt path prev value level
    (List.mem_range.mp hl)).trans (by simp)

theorem recoverSharedInner_true (index coord : Nat) (child : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    recoverSharedInner true index coord child word values path prev = (do
      let ends ← (List.finRange 6).mapM fun i =>
        ClaudeWCT.WCT9.chain index coord child.val i.val (4 - wordDigit word i)
          (wordDigit word i) (values i)
      let leaf ← leafHashH (128 + child.val) index coord child.val prev.1 ends
      let value ← (List.range 4).foldlM (fun value level =>
        SharedV3.hashSel (SharedV3.hiOut child.val (level + 1))
          (canonicalChildInput index coord child.val path prev.2 value level)) leaf
      highHash (canonicalChildInput index coord child.val path prev.2 value 4)) := by
  unfold recoverSharedInner
  apply bind_congr
  intro ends
  apply bind_congr
  intro leaf
  change (List.range 5).foldlM (canonicalInnerStep true index coord child.val path prev) leaf = _
  rw [show List.range 5 = List.range 4 ++ [4] from rfl, List.foldlM_append]
  have hf : (List.range 4).foldlM (canonicalInnerStep true index coord child.val path prev) leaf =
      (List.range 4).foldlM (fun value level =>
        SharedV3.hashSel (SharedV3.hiOut child.val (level + 1))
          (canonicalChildInput index coord child.val path prev.2 value level)) leaf := by
    apply foldlM_congr_mem
    intro value level hl
    rw [canonicalInnerStep_eq _ _ _ _ child.isLt _ _ _ _ (by have := List.mem_range.mp hl; omega)]
    have he : level ≠ 4 := by have := List.mem_range.mp hl; omega
    simp [he]
  rw [hf]
  apply bind_congr
  intro value
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure_comp]
  rw [canonicalInnerStep_eq _ _ _ _ child.isLt _ _ _ _ (by decide)]
  simp

end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Stage 2 (merged singleton "Cm"): the top fold of a non-first tree. For tree 8 the left top node (heap 2,
direction 0) keeps the HIGH half and the right one (heap 3) the LOW half, which is `sharedOuterHash`'s
`coord = 8 ∧ heap = 3` rule at heap `2 + p / 64`. -/
theorem canonical_top_outer (coord : Fin 9) (p : Nat) (hp : p < 128) (hf : SharedV3.first coord.val = false)
    (input : HashInput) :
    (if coord.val = 8 then SharedV3.hashSel (decide (SharedV3.direction coord.val p = 0)) input
      else highHash input) =
      (if coord.val = 8 ∧ 2 + p / 64 = 3 then shortHash input else highHash input) := by
  have hdir : SharedV3.direction coord.val p = p / 64 := by
    unfold SharedV3.direction SharedV3.lastLevel
    rw [hf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  rw [hdir]
  by_cases h8 : coord.val = 8
  · rw [if_pos h8]
    by_cases h0 : p / 64 = 0
    · rw [if_neg (fun h => by have h2 := h.2; omega), decide_eq_true h0]
      rfl
    · rw [if_pos ⟨h8, by omega⟩, decide_eq_false h0]
      rfl
  · rw [if_neg h8, if_neg (fun h => h8 h.1)]

theorem canonicalCoordinate_eq_sourceCoordinate (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    canonicalCoordinate index coord raw word values path prev =
      sourceCoordinate index coord raw word values path prev := by
  have hraw : rawChild (SharedV3.first coord.val) (SharedV3.physical coord.val raw.val) = raw.val :=
    raw_physical_child _ _ raw.isLt
  unfold canonicalCoordinate sourceCoordinate
  cases hf : SharedV3.first coord.val with
  | false =>
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      rw [recoverSharedInner_false]
      simp only [hf] at hraw
      simp only [hraw, bind_assoc]
      apply bind_congr
      intro ends
      unfold canonicalChildN
      simp only [SharedV3.lastLevel, hf, Bool.false_eq_true, ↓reduceIte, bind_assoc]
      apply bind_congr
      intro leaf
      apply bind_congr
      intro value
      rw [canonical_top_outer coord (SharedV3.physical coord.val raw.val)
        (SharedV3.physical_lt _ _ raw.isLt) hf]
      have heap : (128 + SharedV3.physical coord.val raw.val) / 2 ^ (5 + 1) =
          2 + SharedV3.physical coord.val raw.val / 64 := by norm_num; omega
      simp only [canonicalChildInput, sharedOuterHash, heap, show (5 : Nat) ≠ 4 by decide,
        if_false, show 2 ^ 5 = 32 by decide]
      split_ifs <;> rfl
  | true =>
      have hn : coord.val ≠ 8 := by
        intro he
        simp [SharedV3.first, he] at hf
      have hp : SharedV3.physical coord.val raw.val = raw.val := by
        simp [SharedV3.physical, hf, physicalChild]
      simp only [hf, ↓reduceIte]
      rw [recoverSharedInner_true]
      simp only [hp, bind_assoc]
      apply bind_congr
      intro ends
      unfold canonicalChildN
      simp only [SharedV3.lastLevel, hf, hp, ↓reduceIte, hn, bind_assoc]

end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def rawOfPhysical (first : Bool) (child : Child) : Child :=
  ⟨rawChild first child.val, by
    have h := child.isLt
    cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega⟩

theorem physical_rawOfPhysical (first : Bool) (child : Child) :
    physicalChild first (rawOfPhysical first child).val = child.val := by
  have h := child.isLt
  cases first <;> simp only [physicalChild, rawOfPhysical, rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega

def sourcePair (index : Nat) (pair : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : M PairRoot := do
  let a ← sourceCoordinate index ⟨2 * pair.val, by omega⟩
    (rawOfPhysical true (firstChild s)) aWord opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩) prev
  sourceCoordinate index ⟨2 * pair.val + 1, by omega⟩
    (rawOfPhysical false (secondChild s)) bWord opened.secondValues
    (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩) a

theorem sourcePair_eq_recoverPair (index : Nat) (pair : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) :
    sourcePair index pair s aWord bWord opened prev =
      recoverPair index pair.val s aWord bWord opened prev := by
  have hfirst : SharedV3.first (2 * pair.val) = true := by simp [SharedV3.first]; omega
  have hsecond : SharedV3.first (2 * pair.val + 1) = false := by simp [SharedV3.first]
  have ha : SharedV3.physical (2 * pair.val) (rawOfPhysical true (firstChild s)).val = (firstChild s).val := by
    simp only [SharedV3.physical, hfirst, physical_rawOfPhysical]
  have hb : SharedV3.physical (2 * pair.val + 1) (rawOfPhysical false (secondChild s)).val = (secondChild s).val := by
    simp only [SharedV3.physical, hsecond, physical_rawOfPhysical]
  unfold sourcePair sourceCoordinate recoverPair
  simp only [ha, hb, hfirst, hsecond, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
    SharedV3.orderPair, SharedV3.direction, SharedV3.lastLevel]
  rfl

def sourceSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : M PairRoot :=
  sourceCoordinate index 8 (rawOfPhysical false selected) word opened.values
    (fun i => opened.path ⟨i % 7, Nat.mod_lt _ (by decide)⟩) prev

theorem sourceSingleton_eq_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    sourceSingleton index selected word opened prev = recoverSingleton index selected word opened prev := by
  have hf : SharedV3.first 8 = false := by decide
  have hp : SharedV3.physical 8 (rawOfPhysical false selected).val = selected.val := by
    simp only [SharedV3.physical, hf, physical_rawOfPhysical]
  unfold sourceSingleton sourceCoordinate recoverSingleton
  simp only [show (8 : Fin 9).val = 8 from rfl, hp, hf, Bool.false_eq_true, ↓reduceIte, SharedV3.orderPair, SharedV3.direction,
    SharedV3.lastLevel]
  rfl

def sourceGroupedForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : M PairRoot := do
  let prev ← (List.finRange 4).foldlM (fun prev pair =>
    sourcePair index pair (selected.pairs pair) (words.first pair) (words.second pair)
      (opened.pairs pair) prev) ftsStart
  sourceSingleton index selected.singleton words.singleton opened.singleton prev

theorem sourceGroupedForest_eq_recoverForest (index : Nat) (selected : ForestSelection)
    (words : ForestWords) (opened : ForestOpening) :
    sourceGroupedForest index selected words opened = recoverForest index selected words opened := by
  unfold sourceGroupedForest recoverForest
  simp only [sourcePair_eq_recoverPair, sourceSingleton_eq_recoverSingleton]

end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def coordinateChild (selected : ForestSelection) (coord : Fin 9) : Child :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then firstChild (selected.pairs pair) else secondChild (selected.pairs pair)
  else selected.singleton

def coordinateRaw (selected : ForestSelection) (coord : Fin 9) : Child :=
  rawOfPhysical (SharedV3.first coord.val) (coordinateChild selected coord)

def coordinateWord (words : ForestWords) (coord : Fin 9) : Rank :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then words.first pair else words.second pair
  else words.singleton

def coordinateValues (opened : ForestOpening) (coord : Fin 9) : Fin 6 → Digest :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then (opened.pairs pair).firstValues else (opened.pairs pair).secondValues
  else opened.singleton.values

def coordinatePath (opened : ForestOpening) (coord : Fin 9) : Nat → Digest :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then fun level => (opened.pairs pair).firstPath ⟨level % 6, Nat.mod_lt _ (by decide)⟩
    else fun level => (opened.pairs pair).secondPath ⟨level % 7, Nat.mod_lt _ (by decide)⟩
  else fun level => opened.singleton.path ⟨level % 7, Nat.mod_lt _ (by decide)⟩

def sourceNineForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : M PairRoot :=
  (List.finRange 9).foldlM (fun prev coord =>
    sourceCoordinate index coord (coordinateRaw selected coord) (coordinateWord words coord)
      (coordinateValues opened coord) (coordinatePath opened coord) prev) ftsStart

attribute [local irreducible] sourceCoordinate rawOfPhysical

theorem sourceNineForest_eq_grouped (index : Nat) (selected : ForestSelection)
    (words : ForestWords) (opened : ForestOpening) :
    sourceNineForest index selected words opened = sourceGroupedForest index selected words opened := by
  have hnine : List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [sourceNineForest, sourceGroupedForest, hnine, hfour, List.foldlM_cons, List.foldlM_nil,
    sourcePair, sourceSingleton, bind_assoc, pure_bind]
  simp only [coordinateRaw, coordinateChild, coordinateWord, coordinateValues, coordinatePath]
  norm_num [SharedV3.first]
  rfl

theorem forest_canonical (w : SharedV3.WBytes) (index : Nat) (hi : index < 2 ^ 31)
    (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening)
    (hstart : SharedV3.initialPair w = ftsStart)
    (hc : ∀ coord, ChainReadout w coord (coordinateWord words coord) (coordinateValues opened coord))
    (hp : ∀ coord, PathReadout w coord (coordinateRaw selected coord) (coordinatePath opened coord)) :
    SharedV3.forest w index (coordinateRaw selected)
      (fun coord => ClaudeWCT.WCT9.embed (coordinateWord words coord)) =
        recoverForest index selected words opened := by
  rw [← sourceGroupedForest_eq_recoverForest, ← sourceNineForest_eq_grouped]
  unfold SharedV3.forest sourceNineForest
  rw [hstart]
  apply foldlM_congr_mem
  intro prev coord _
  exact (coordinate_canonical w index coord _ _ _ _ prev hi (hc coord) (hp coord)).trans
    (canonicalCoordinate_eq_sourceCoordinate index coord _ _ _ _ prev)

end W9Drv.SharedCanonical

namespace W9Drv.SharedAcceptedFold
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
def step (init : β) (f : β → α → m β) (ok : α → Bool)
    (state : Option (List β)) (k : α) : m (Option (List β)) := do
  let some hist := state | pure none
  if !ok k then return none
  let p ← f (hist.getLastD init) k
  pure (some (hist ++ [p]))
def finish (init : β) (state : Option (List β)) : m (Option β) :=
  match state with | none => pure none | some hist => pure (some (hist.getLastD init))
theorem accepted (init : β) (f : β → α → m β) (ok : α → Bool)
    (ks : List α) (hok : ∀ k ∈ ks, ok k = true) (hist : List β) :
    (ks.foldlM (step init f ok) (some hist) >>= finish init) = (ks.foldlM f (hist.getLastD init) >>= fun p => pure (some p)) := by
  induction ks generalizing hist with
  | nil => simp [finish]
  | cons k ks ih =>
    have hk := hok k (by simp)
    have hks : ∀ a ∈ ks, ok a = true := fun a ha => hok a (by simp [ha])
    simp only [List.foldlM_cons, step, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind_assoc, pure_bind]
    congr 1
    funext p
    rw [ih hks]
    simp
end W9Drv.SharedAcceptedFold

namespace W9Drv.SharedCoord
open W9Machine SigGolfCandidate.T3 SigGolfCandidate.Research

theorem ftsN_accepted (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (hr : ∀ k : Fin 9, SharedForest.rawForestRank a k.val < 563) :
    ftsN w a = (do
      let p ← SharedV3.forest w (idxOf a) (SharedForest.rawChildFromOutput a)
        (fun k => N600.embed (SharedForest.forestRank a k.val))
      pure (some p)) := by
  have hs : stepN w a = SharedAcceptedFold.step (SharedV3.initialPair w)
      (fun prev k => coordN w (idxOf a) k (SharedForest.rawChildFromOutput a k)
        (SharedForest.forestRank a k.val) prev)
      (fun k => decide (SharedForest.rawForestRank a k.val < 563)) := by
    funext state k
    cases state <;> simp [stepN, SharedAcceptedFold.step, hr k, prevOf]
  have h := SharedAcceptedFold.accepted (m := M) (SharedV3.initialPair w)
    (fun prev k => coordN w (idxOf a) k (SharedForest.rawChildFromOutput a k)
      (SharedForest.forestRank a k.val) prev)
    (fun k => decide (SharedForest.rawForestRank a k.val < 563))
    (List.finRange 9) (fun k _ => by simp [hr k]) []
  have he : ftsN w a =
      ((List.finRange 9).foldlM (stepN w a) (some []) >>=
        SharedAcceptedFold.finish (SharedV3.initialPair w)) := by
    unfold ftsN
    congr 1
    funext state
    cases state <;> rfl
  rw [he, hs]
  simpa only [List.getLastD_nil, SharedV3.forest, coordN] using h
end W9Drv.SharedCoord


namespace W9Drv.SharedCanonical
open W9Machine SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem coordinateRaw_output (a : HashOutput) :
    coordinateRaw (forestSelectionFromOutput a) = rawChildFromOutput a := by
  funext k
  have hc : coordinateChild (forestSelectionFromOutput a) k = physicalChildFromOutput a k := by
    fin_cases k
    · exact (physicalFromOutput_first a 0).symm
    · exact (physicalFromOutput_second a 0).symm
    · exact (physicalFromOutput_first a 1).symm
    · exact (physicalFromOutput_second a 1).symm
    · exact (physicalFromOutput_first a 2).symm
    · exact (physicalFromOutput_second a 2).symm
    · exact (physicalFromOutput_first a 3).symm
    · exact (physicalFromOutput_second a 3).symm
    · exact (physicalFromOutput_singleton a).symm
  unfold coordinateRaw
  rw [hc]
  apply Fin.ext
  exact raw_physical_child (firstCoord k.val) (rawChildFromOutput a k).val
    (rawChildFromOutput a k).isLt

theorem coordinateWord_output (a : HashOutput) (k : Fin 9) :
    coordinateWord (forestWordsFromOutput a) k = forestRank a k.val := by
  fin_cases k <;> rfl
end W9Drv.SharedCanonical

namespace W9Drv.SharedCanonical
open W9Machine SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem chainReadout_witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (word : Rank) :
    ChainReadout (Paired.witEnc output witness) k word (coordinateValues witness.signature.forest k) := by
  refine ⟨PairedReadout.chainPadA_witEnc output witness k,
    PairedReadout.chainPadB_witEnc output witness k,
    PairedReadout.chainPadC_witEnc output witness k,?_⟩
  intro i
  unfold V3.reveal
  split_ifs
  · exact Paired.wleafValue_witEnc output witness k i
  · exact Paired.wchainValue_witEnc output witness k i

theorem pathReadout_witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) :
    PathReadout (Paired.witEnc output witness) k (rawChildFromOutput output k)
      (coordinatePath witness.signature.forest k) := by
  refine ⟨?_,?_,?_,Paired.wtopOther_witEnc output witness k⟩
  · intro l hl;exact PairedReadout.nodeHPad_witEnc output witness k l
  · intro l hl hne;exact PairedReadout.nodePad_witEnc output witness k l hl hne
  · intro l hl;exact Paired.wsibling_witEnc output witness k l (by omega)

theorem forest_witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (hi:index<2^31) :
    SharedV3.forest (Paired.witEnc output witness) index (rawChildFromOutput output)
      (fun k=>ClaudeWCT.WCT9.embed (forestRank output k.val)) =
      recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest := by
  have hp:∀k,PathReadout (Paired.witEnc output witness) k
      (coordinateRaw (forestSelectionFromOutput output) k) (coordinatePath witness.signature.forest k):=by
    intro k;rw[coordinateRaw_output];exact pathReadout_witEnc output witness k
  have h:=forest_canonical (Paired.witEnc output witness) index hi
    (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest
    (PairedReadout.initialPair_witEnc output witness)
    (fun k=>chainReadout_witEnc output witness k _) hp
  simpa only[coordinateRaw_output,coordinateWord_output] using h
end W9Drv.SharedCanonical
