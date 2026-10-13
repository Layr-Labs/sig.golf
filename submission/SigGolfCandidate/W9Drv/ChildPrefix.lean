import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Machine.WctChildContract
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.T3M.Verify.Common

section
namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def childBase (j : Nat) : Nat := 246464 + 64 * j
def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def blkO (j l : Nat) : Nat := V3.blkOff j l
def curO (l j : Nat) : Nat := blkO j l + 48 * bitAt j l
def sibO (l j : Nat) : Nat := if l < 6 then blkO j l + 48 * (1 - bitAt j l) else ClaudeWCT.W9.T3M.authRoot j
def padO (j l : Nat) : Nat := blkO j l + 32
def leafO : Nat := 688
/-- Nested FTS hand-off: the heap-2/3 fold writes its 32-byte output at `B - handO j`, so its high half lands on
the next region's leaf pad (bit 6 = 0) or Z slot (bit 6 = 1). -/
def handO (j : Nat) : Nat := if bitAt j 6 = 0 then 192 else 48
def heapOf (l j : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
def w0n (k index : Nat) : Nat := W9Machine.V3.nodeLow k index
def heapReg (h : Nat) : Reg :=
  match h with
  | 1 => .x9 | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | _ => .x30
def heapRegN (h : Nat) : Nat := [0,9,13,19,20,21,26,30].getD h 30
def encI (rd rs1 imm : Nat) : BitVec 32 := BitVec.ofNat 32 (imm % 4096 * 2 ^ 20 + rs1 * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
def encS (f3 rs2 off rs1 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (off / 32 * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + f3 * 2 ^ 12 + off % 32 * 2 ^ 7 + 0x23)
def skipA2 (j l : Nat) : Bool := decide (l < 5) && decide (curO (l + 1) j = curO l j)
/-- Packed node levels (`l ≤ 3`, heaps `8..127`): `addi gp,a5,-heap; sd gp,16(a0)` and, only when the computed
child is the left input (bit 0), `sd zero,24(a0)`; for bit 1 the high tweak word stays witness memory. -/
def hiW (j l : Nat) : Bool := decide (l ≤ 3) && decide (bitAt j l = 0)
def lvlTmpl (j l : Nat) : List (BitVec 32) :=
  [encI 10 8 (blkO j l)] ++
    (if l ≤ 3 then [encI 3 15 (4096 - heapOf l j), encS 3 3 16 10] ++ (if hiW j l then [encS 3 0 24 10] else [])
     else [encS 3 15 16 10, encS 3 (heapRegN (heapOf l j)) 24 10]) ++
    (if skipA2 j l then [] else [if l = 5 then encI 12 8 (4096 - handO j) else encI 12 8 (curO (l + 1) j)]) ++
    [0x00000073]
def lvlLen (j l : Nat) : Nat := (if hiW j l then 6 else 5) - (if skipA2 j l then 1 else 0)
def childSaveC (j : Nat) : Nat := ((List.range 5).map fun l => if skipA2 j l then 1 else 0).sum +
  ((List.range 4).map fun l => if bitAt j l = 1 then 1 else 0).sum
def ChildGood : Prop := ∀ j : Fin 128, Child.Good Frozen.layout ⟨38, 95, 95 - ClaudeWCT.WCT9.childSave j.val⟩ j
def encLoad (rd rs imm : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm * 2 ^ 20 + rs * 2 ^ 15 + 3 * 2 ^ 12 + rd * 2 ^ 7 + 3)
def childTmpl (j : Nat) : List (BitVec 32) :=
  [0, encI 12 8 (curO 0 j), 0x00000073, encI 11 0 64] ++ (List.range 6).flatMap (lvlTmpl j) ++
    [0x12808067] ++ List.replicate (25 + childSaveC j) 0x00000013
def childWords (j : Nat) : List (BitVec 32) := childTmpl j
def childLook (j n : Nat) : Option (BitVec 32) :=
  if childBase j ≤ n then (childWords j)[n - childBase j]? else none
def ecIdx (j : Nat) : Nat → Nat
  | 0 => 2
  | l + 1 => ecIdx j l + lvlLen j l + (if l = 0 then 1 else 0)
def lvlSt (j l : Nat) : Nat := ecIdx j (l + 1) - ecIdx j l - 1
def childRun (j i : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 (childLook j) [] 64 (pcOf (childBase j + i)) dirs (σK []) []
def eX8 (off : Nat) : E := addC (.reg .x8) (BitVec.ofNat 64 off)
def aX8 (off : Nat) : Addr := ⟨some (.reg .x8), BitVec.ofNat 64 off⟩
def p0Res (j : Nat) : PRes :=
  ⟨⟨RegFile.init.set .x12 (eX8 (curO 0 j)), [], []⟩, pcOf (childBase j + 2), true, 1, 1, [], none⟩
def lowE (j l : Nat) : E := addC (.reg .x15) (BitVec.ofNat 64 (2 ^ 64 - heapOf l j))
def lvlRegs (j l : Nat) : RegFile :=
  let rf := if l = 0 then RegFile.init.set .x11 (.c 64) else RegFile.init
  let rf := rf.set .x10 (eX8 (blkO j l))
  let rf := if l ≤ 3 then rf.set .x3 (lowE j l) else rf
  if skipA2 j l then rf
  else rf.set .x12 (if l = 5 then addC (.reg .x8) (BitVec.ofNat 64 (2 ^ 64 - handO j)) else eX8 (curO (l + 1) j))
def lvlMem (j l : Nat) : SymMem :=
  if l ≤ 3 then (if hiW j l then [(aX8 (blkO j l + 24), .c 0)] else []) ++ [(aX8 (blkO j l + 16), lowE j l)]
  else [(aX8 (blkO j l + 24), .reg (heapReg (heapOf l j))), (aX8 (blkO j l + 16), .reg .x15)]
def lvlObl (j l : Nat) : List Oblig :=
  (if l ≤ 3 ∧ hiW j l = false then [] else [.valid (aX8 (blkO j l + 24)) 8]) ++ [.valid (aX8 (blkO j l + 16)) 8]
def lvlRes (j l : Nat) : PRes :=
  ⟨⟨lvlRegs j l, lvlMem j l, lvlObl j l⟩, pcOf (childBase j + ecIdx j (l + 1)), true, lvlSt j l, lvlSt j l, [], none⟩
def otherDest (j : Nat) : Nat := 16 * (1 - bitAt j 6)
def aX9 (off : Nat) : Addr := ⟨some (.reg .x9), BitVec.ofNat 64 off⟩
def retE : E := .bin .and (addC (.reg .x1) 296) (.c (~~~1#64))
def p7Res (_j : Nat) : PRes :=
  ⟨⟨RegFile.init, [], []⟩, 0, false, 1, 1, [], some retE⟩
def childPiecesOK (j : Nat) : Bool :=
  optBeq (childRun j 1 []) (p0Res j) &&
    (List.range 6).all (fun l => optBeq (childRun j (ecIdx j l + 1) []) (lvlRes j l)) &&
    optBeq (childRun j (ecIdx j 6 + 1) [.jmp]) (p7Res j)
def childPiecesRange (lo n : Nat) : Bool := (List.range' lo n).all childPiecesOK
def childLinkedRange (lo n : Nat) : Bool :=
  (List.range' lo n).all (fun j => sliceChecked (childBase j) (childWords j))
/-- Second tweak write of a level: `blk+24`, or (packed level, bit 1: no high write) `blk+16` again. -/
def tw24 (j l : Nat) : Nat := if l ≤ 3 ∧ hiW j l = false then blkO j l + 16 else blkO j l + 24
def stageW (j l : Nat) : List Nat :=
  [curO l j, curO l j + 8, curO l j + 16, curO l j + 24, blkO j l + 16, tw24 j l]
def stagesW (j n : Nat) : List Nat := (List.range n).flatMap (stageW j)
theorem heapOf_packed (j l : Nat) (hj : j < 128) (hl : l ≤ 3) : 8 ≤ heapOf l j ∧ heapOf l j < 128 := by
  unfold heapOf; interval_cases l <;> simp <;> omega
theorem heapOf_low (j l : Nat) (hj : j < 128) (hl4 : 4 ≤ l) (hl : l ≤ 5) : 2 ≤ heapOf l j ∧ heapOf l j ≤ 7 := by
  unfold heapOf; interval_cases l <;> simp <;> omega
theorem tw24_cases (j l : Nat) : tw24 j l = blkO j l + 16 ∨ tw24 j l = blkO j l + 24 := by
  unfold tw24; split <;> simp
def planOK (j : Nat) : Bool :=
  (List.range 6).all (fun l => decide (blkO j l % 16 = 0 ∧ blkO j l + 64 ≤ 896 ∧ curO l j + 32 ≤ 912)) &&
  (List.range 6).all (fun l => (stagesW j (l + 1)).all (fun off =>
    decide (off ≠ padO j l ∧ off ≠ padO j l + 8 ∧ off ≠ sibO l j ∧ off ≠ sibO l j + 8))) &&
  (List.range 4).all (fun l => hiW j l || (stagesW j (l + 1)).all (fun off => decide (off ≠ blkO j l + 24)))
end W9Drv.ChildProof
end
section
namespace W9Drv.ChildProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem planOK_all : ∀ j : Fin 128, planOK j.val = true := by decide +kernel
theorem childPieces_0 : childPiecesRange 0 16 = true := by decide +kernel
theorem childLinked_0 : childLinkedRange 0 16 = true := by decide +kernel
theorem childPieces_1 : childPiecesRange 16 16 = true := by decide +kernel
theorem childLinked_1 : childLinkedRange 16 16 = true := by decide +kernel
theorem childPieces_2 : childPiecesRange 32 16 = true := by decide +kernel
theorem childLinked_2 : childLinkedRange 32 16 = true := by decide +kernel
theorem childPieces_3 : childPiecesRange 48 16 = true := by decide +kernel
theorem childLinked_3 : childLinkedRange 48 16 = true := by decide +kernel
theorem childPieces_4 : childPiecesRange 64 16 = true := by decide +kernel
theorem childLinked_4 : childLinkedRange 64 16 = true := by decide +kernel
theorem childPieces_5 : childPiecesRange 80 16 = true := by decide +kernel
theorem childLinked_5 : childLinkedRange 80 16 = true := by decide +kernel
theorem childPieces_6 : childPiecesRange 96 16 = true := by decide +kernel
theorem childLinked_6 : childLinkedRange 96 16 = true := by decide +kernel
theorem childPieces_7 : childPiecesRange 112 16 = true := by decide +kernel
theorem childLinked_7 : childLinkedRange 112 16 = true := by decide +kernel
open SigGolfCandidate.T3M.Verify W9Machine
theorem childPiecesOK_at (j : Nat) (hj : j < 128) : childPiecesOK j = true := by
  have hall : ∀ lo n, childPiecesRange lo n = true → lo ≤ j → j < lo + n → childPiecesOK j = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : j < 16; · exact hall 0 16 childPieces_0 (by omega) (by omega)
  by_cases h1 : j < 32; · exact hall 16 16 childPieces_1 (by omega) (by omega)
  by_cases h2 : j < 48; · exact hall 32 16 childPieces_2 (by omega) (by omega)
  by_cases h3 : j < 64; · exact hall 48 16 childPieces_3 (by omega) (by omega)
  by_cases h4 : j < 80; · exact hall 64 16 childPieces_4 (by omega) (by omega)
  by_cases h5 : j < 96; · exact hall 80 16 childPieces_5 (by omega) (by omega)
  by_cases h6 : j < 112; · exact hall 96 16 childPieces_6 (by omega) (by omega)
  exact hall 112 16 childPieces_7 (by omega) (by omega)
theorem childRun_p0 (j : Nat) (hj : j < 128) : childRun j 1 [] = some (p0Res j) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq h.1.1
theorem childRun_lvl (j : Nat) (hj : j < 128) (l : Nat) (hl : l < 6) :
    childRun j (ecIdx j l + 1) [] = some (lvlRes j l) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq (List.all_eq_true.mp h.1.2 l (List.mem_range.mpr hl))
theorem childRun_p7 (j : Nat) (hj : j < 128) : childRun j (ecIdx j 6 + 1) [.jmp] = some (p7Res j) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq h.2
theorem child_linked (j : Nat) (hj : j < 128) : sliceChecked (childBase j) (childWords j) = true := by
  have hall : ∀ lo n, childLinkedRange lo n = true → lo ≤ j → j < lo + n → sliceChecked (childBase j) (childWords j) = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : j < 16; · exact hall 0 16 childLinked_0 (by omega) (by omega)
  by_cases h1 : j < 32; · exact hall 16 16 childLinked_1 (by omega) (by omega)
  by_cases h2 : j < 48; · exact hall 32 16 childLinked_2 (by omega) (by omega)
  by_cases h3 : j < 64; · exact hall 48 16 childLinked_3 (by omega) (by omega)
  by_cases h4 : j < 80; · exact hall 64 16 childLinked_4 (by omega) (by omega)
  by_cases h5 : j < 96; · exact hall 80 16 childLinked_5 (by omega) (by omega)
  by_cases h6 : j < 112; · exact hall 96 16 childLinked_6 (by omega) (by omega)
  exact hall 112 16 childLinked_7 (by omega) (by omega)
theorem planOK_at (j : Nat) (hj : j < 128) : planOK j = true := planOK_all ⟨j, hj⟩
theorem blk_bounds (j : Nat) (hj : j < 128) (l : Nat) (hl : l < 6) :
    blkO j l % 16 = 0 ∧ blkO j l + 64 ≤ 896 ∧ curO l j + 32 ≤ 912 := by
  have h := planOK_at j hj
  simp only [planOK, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.1.1 l (List.mem_range.mpr hl)
  simpa only [decide_eq_true_eq] using this
theorem stagesW_free {j l off : Nat} (hj : j < 128) (hl : l < 6) (h : off ∈ stagesW j (l + 1)) :
    off ≠ padO j l ∧ off ≠ padO j l + 8 ∧ off ≠ sibO l j ∧ off ≠ sibO l j + 8 := by
  have hp := planOK_at j hj
  simp only [planOK, Bool.and_eq_true] at hp
  have := List.all_eq_true.mp (List.all_eq_true.mp hp.1.2 l (List.mem_range.mpr hl)) off h
  simpa only [decide_eq_true_eq] using this
theorem tw_free {j l off : Nat} (hj : j < 128) (hl : l < 4) (hw : hiW j l = false) (h : off ∈ stagesW j (l + 1)) :
    off ≠ blkO j l + 24 := by
  have hp := planOK_at j hj
  simp only [planOK, Bool.and_eq_true] at hp
  have h1 := List.all_eq_true.mp hp.2 l (List.mem_range.mpr hl)
  rw [hw, Bool.false_or] at h1
  have := List.all_eq_true.mp h1 off h
  simpa only [decide_eq_true_eq] using this
end W9Drv.ChildProof
end
section
namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
def ChildCodeAt (im : Image) (j : Nat) : Prop :=
  ∀ i w, (childWords j)[i]? = some w → im.code[childBase j + i]? = some w
structure ChildPre (j B k index : Nat) (leaf pads sibs tws : Nat → Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (childBase j + 1)
  base8 : B % 8 = 0
  baseHi : B + 1024 ≤ MEMORY_BYTES
  t0 : u.getReg .x5 = 0
  s0 : u.getReg .x8 = BitVec.ofNat 64 B
  a0 : u.getReg .x10 = BitVec.ofNat 64 (B + leafO)
  a1 : u.getReg .x11 = BitVec.ofNat 64 128
  w0 : u.getReg .x15 = BitVec.ofNat 64 (w0n k index)
  tp : u.getReg .x4 = BitVec.ofNat 64 (([none, none, some 20, none, none, some 20, none, none, some 20].getD k none).elim j (j <<< ·))
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 h
  leafAt : ∀ i, i < 8 → DigAt u (B + leafO + 16 * i) (leaf i)
  padAt : ∀ l, l < 6 → DigAt u (B + padO j l) (pads l)
  sibAt : ∀ l, l < 6 → DigAt u (B + sibO l j) (sibs l)
  twAt : ∀ l, l < 6 → DigAt u (B + blkO j l + 16) (tws l)
theorem childLook_ok {im : Image} {j : Nat} (h : ChildCodeAt im j) : LookOK im (childLook j) := by
  intro n w hw
  unfold childLook at hw
  split at hw
  · rename_i hle
    have := h (n - childBase j) w hw
    rwa [Nat.add_sub_cancel' hle] at this
  · cases hw
theorem childRun_sound {im : Image} {j i : Nat} {dirs : List Dir} {r : PRes} (hcode : ChildCodeAt im j)
    (h : childRun j i dirs = some r) (s : MachineState) (hpc : s.pc = pcOf (childBase j + i))
    (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : r.brs = []) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h (childLook_ok hcode) s hpc (by intro p hp; cases hp) hobl
    (by rw [hbr]; intro b hb; cases hb)
theorem aX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (aX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  simp only [aX8, Addr.eval, E.eval, hB, ofNat_add_ofNat]
theorem eX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (eX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  rw [eX8, addC_eval]; simp only [E.eval, hB, ofNat_add_ofNat]
theorem valid_aX8 {s : MachineState} {B off w : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B)
    (hal : (B + off) % w = 0) (hhi : B + off + w ≤ MEMORY_BYTES) : (Oblig.valid (aX8 off) w).holds s := by
  simp only [Oblig.holds, aX8_eval hB, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
  rw [toNat_ofNat_lt (by unfold MEMORY_BYTES at hhi; omega)]
  exact ⟨hhi, hal⟩
theorem lvlObl_holds {s : MachineState} {B : Nat} (j : Nat) (hj : j < 128) (l : Nat) (hl : l < 6)
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (h8 : B % 8 = 0) (hhi : B + 1024 ≤ MEMORY_BYTES) :
    ∀ o ∈ lvlObl j l, o.holds s := by
  have hb := blk_bounds j hj l hl
  intro o ho
  unfold lvlObl at ho
  rw [List.mem_append] at ho
  rcases ho with ho | ho
  · split at ho
    · simp at ho
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho; exact valid_aX8 hB (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho; exact valid_aX8 hB (by omega) (by omega)
theorem lvlRegs_x12 (j l : Nat) (hl : l < 5) :
    (lvlRegs j l).get .x12 = if skipA2 j l then .reg .x12 else eX8 (curO (l + 1) j) := by
  unfold lvlRegs
  by_cases hs : skipA2 j l = true
  · simp only [hs, if_true]; split_ifs <;> rfl
  · simp only [hs, Bool.false_eq_true, if_false]; rw [RegFile.get_set_self _ _ (by decide), if_neg (by omega)]
theorem skipA2_cur {j l : Nat} (h : skipA2 j l = true) : curO (l + 1) j = curO l j := by
  simp only [skipA2, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
theorem skipA2_five (j : Nat) : skipA2 j 5 = false := by simp [skipA2]
theorem lvlRegs_x10 (j l : Nat) : (lvlRegs j l).get .x10 = eX8 (blkO j l) := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_x11 (j l : Nat) : (lvlRegs j l).get .x11 = if l = 0 then .c 64 else .reg .x11 := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_x3 (j l : Nat) :
    (lvlRegs j l).get .x3 = if l ≤ 3 then lowE j l else .reg .x3 := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_other (j l : Nat) (r : Reg) (h3 : r ≠ .x3) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
    (h12 : r ≠ .x12) : (lvlRegs j l).get r = RegFile.init.get r := by
  unfold lvlRegs
  simp only
  split_ifs <;> simp only [RegFile.get_set_ne _ _ h3, RegFile.get_set_ne _ _ h10, RegFile.get_set_ne _ _ h11,
    RegFile.get_set_ne _ _ h12]
theorem heapReg_ne (h : Nat) : heapReg h ≠ .x3 ∧ heapReg h ≠ .x10 ∧ heapReg h ≠ .x11 ∧ heapReg h ≠ .x12 := by
  unfold heapReg; split <;> decide
theorem lvlMem_get {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B)
    (hb : B + 1024 < 2 ^ 64) (j : Nat) (hj : j < 128) (l A : Nat) (hl : l < 6) (hA : A < 2 ^ 64) :
    memEval s (lvlMem j l) (BitVec.ofNat 64 A) =
      if A = B + blkO j l + 24 ∧ (l ≤ 3 → hiW j l = true) then
        (if l ≤ 3 then 0 else s.getReg (heapReg (heapOf l j)))
      else if A = B + blkO j l + 16 then (if l ≤ 3 then (lowE j l).eval s else s.getReg .x15)
      else s.getMem (BitVec.ofNat 64 A) := by
  have hbl := blk_bounds j hj l hl
  have e24 := ofNat_inj hA (show B + blkO j l + 24 < 2 ^ 64 by omega)
  have e16 := ofNat_inj hA (show B + blkO j l + 16 < 2 ^ 64 by omega)
  unfold lvlMem
  by_cases h3 : l ≤ 3
  · by_cases hw : hiW j l = true
    · simp only [if_pos h3, hw, if_true, List.cons_append, List.nil_append]
      rw [memEval_cons, memEval_cons, memEval_nil, aX8_eval hB, aX8_eval hB]
      simp only [← Nat.add_assoc, E.eval, e24, e16, implies_true, and_true]
    · simp only [if_pos h3, hw, Bool.false_eq_true, if_false, List.nil_append]
      rw [memEval_cons, memEval_nil, aX8_eval hB]
      simp only [← Nat.add_assoc, e16, imp_false, not_true_eq_false, and_false, if_false, h3]
  · simp only [if_neg h3]
    rw [memEval_cons, memEval_cons, memEval_nil, aX8_eval hB, aX8_eval hB]
    simp only [← Nat.add_assoc, E.eval, e24, e16, h3, false_imp_iff, and_true]
theorem heapReg_eval {s : MachineState} {j l : Nat} (hj : j < 128) (hl4 : 4 ≤ l) (hl : l ≤ 5)
    (hheap : ∀ h, 2 ≤ h → h ≤ 7 → s.getReg (heapReg h) = BitVec.ofNat 64 h) :
    s.getReg (heapReg (heapOf l j)) = BitVec.ofNat 64 (heapOf l j) := by
  have hb := heapOf_low j l hj hl4 hl
  exact hheap _ hb.1 hb.2
theorem frame_writeHash4 (t : MachineState) (a : BitVec 256) (d : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 d) (hd : d + 32 < 2 ^ 64) :
    Frame t (writeHash t a) (fun A => A = d ∨ A = d + 8 ∨ A = d + 16 ∨ A = d + 24) := by
  intro A hA hn
  simp only [not_or] at hn
  rw [getMem_writeHash t a d A h12 hd hA, if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2.1, if_neg hn.2.2.2]
theorem mem_stagesW {j m n off : Nat} (hm : m < n) (h : off ∈ stageW j m) : off ∈ stagesW j n :=
  List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, h⟩
theorem bitAt_lt (j l : Nat) : bitAt j l < 2 := Nat.mod_lt _ (by decide)
theorem curO_cases (j l : Nat) : curO l j = blkO j l ∨ curO l j = blkO j l + 48 := by
  have := bitAt_lt j l; unfold curO; omega
theorem sibO_cases (j l : Nat) (hl : l < 6) :
    (bitAt j l = 0 ∧ curO l j = blkO j l ∧ sibO l j = blkO j l + 48) ∨
    (bitAt j l = 1 ∧ curO l j = blkO j l + 48 ∧ sibO l j = blkO j l) := by
  have := bitAt_lt j l; unfold curO sibO; rw [if_pos hl]; omega
theorem stagesW_bound {j n off : Nat} (hj : j < 128) (hn : n ≤ 6) (h : off ∈ stagesW j n) :
    off % 8 = 0 ∧ off + 8 ≤ 912 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hb := blk_bounds j hj m (by omega)
  have hc := curO_cases j m
  have ht := tw24_cases j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by omega, by omega⟩
theorem stagesW_mono {j n n' off : Nat} (h : off ∈ stagesW j n) (hn : n ≤ n') : off ∈ stagesW j n' := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  exact mem_stagesW (by have := List.mem_range.mp hm; omega) ho
end W9Drv.ChildProof
end
section
namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
def nodeHeader (k index heap : Nat) (hp : BitVec 64) : Digest := V3.nodeHdr k index heap hp
/-- High tweak word hashed at level `l`: the witness word for packed bit-1 levels, else 0 (written or unused). -/
def hpOf (j : Nat) (tws : Nat → Digest) (l : Nat) : BitVec 64 :=
  if l < 4 ∧ bitAt j l = 1 then (tws l).extractLsb' 64 64 else 0
def leafBytes (leaf : Nat → Digest) : List UInt8 := (List.range 8).flatMap fun i => bytesLE 16 (leaf i)
def childLevelP (k index j : Nat) (pads : Nat → Digest) (hps : Nat → BitVec 64) (sibs : Nat → Digest)
    (value : Digest) (l : Nat) : M Digest :=
  let pair := if bitAt j l = 0 then (value, sibs l) else (sibs l, value)
  shortHash (blk4 pair.1 (nodeHeader k index (heapOf l j) (hps l)) (pads l) pair.2)
structure Mid (j B k index : Nat) (u : MachineState) (l : Nat) (v : Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (childBase j + ecIdx j l + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  a1 : l ≠ 0 → s.getReg .x11 = BitVec.ofNat 64 64
  a2 : s.getReg .x12 = BitVec.ofNat 64 (B + curO l j)
  node : DigAt s (B + curO l j) v
  frame : Frame u s (fun A => ∃ off ∈ stagesW j (l + 1), A = B + off)
def nodeIn (k index j : Nat) (pads : Nat → Digest) (hps : Nat → BitVec 64) (sibs : Nat → Digest) (v : Digest)
    (l : Nat) : List UInt8 :=
  let pair := if bitAt j l = 0 then (v, sibs l) else (sibs l, v)
  blk4 pair.1 (nodeHeader k index (heapOf l j) (hps l)) (pads l) pair.2
theorem childLevelP_eq (k index j : Nat) (pads : Nat → Digest) (tws sibs : Nat → Digest) (v : Digest) (l : Nat) :
    childLevelP k index j pads (hpOf j tws) sibs v l = shortHash (nodeIn k index j pads (hpOf j tws) sibs v l) := rfl
theorem nodeIn_blocks (k index j : Nat) (pads : Nat → Digest) (tws sibs : Nat → Digest) (v : Digest) (l : Nat) :
    (toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l))).blocks = 1 := by
  unfold nodeIn; exact blocks_blk4 _ _ _ _
theorem hdr11_lo (k index heap : Nat) (hp : BitVec 64) :
    (nodeHeader k index heap hp).extractLsb' 0 64 =
      BitVec.ofNat 64 (if 8 ≤ heap ∧ heap < 128 then w0n k index - heap else w0n k index) := by
  unfold nodeHeader V3.nodeHdr w0n
  split <;> exact BitVec.extractLsb'_append_eq_right
theorem hdr11_hi (k index heap : Nat) (hp : BitVec 64) :
    (nodeHeader k index heap hp).extractLsb' 64 64 = if 8 ≤ heap ∧ heap < 128 then hp else BitVec.ofNat 64 heap := by
  unfold nodeHeader V3.nodeHdr
  split <;> exact BitVec.extractLsb'_append_eq_left
theorem ofNat_add_neg (a h : Nat) (hh : h ≤ a) (ha : a < 2 ^ 64) (hh0 : 0 < h) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 (2 ^ 64 - h) = BitVec.ofNat 64 (a - h) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show 2 ^ 64 - h < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a - h < 2 ^ 64 by omega)]
  omega
theorem DigAt.of_eq {X Y : MachineState} {a : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 a) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (a + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y a d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
theorem hashInput_blk4 (t : MachineState) (A : Nat) (a b c d : Digest)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (hA : A % 8 = 0)
    (hA' : A + 64 < 2 ^ 64) (ha : DigAt t A a) (hb : DigAt t (A + 16) b) (hc : DigAt t (A + 32) c)
    (hd : DigAt t (A + 48) d) : hashInput t = toQ (pad64 (blk4 a b c d)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA hA' h11
  rw [wordsOf_blk4, ha.1, ha.2, hb.1, hc.1, hd.1, show A + 24 = A + 16 + 8 by omega, hb.2,
    show A + 40 = A + 32 + 8 by omega, hc.2, show A + 56 = A + 48 + 8 by omega, hd.2]
theorem lvl_core {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (l : Nat) (hl : l < 6) (v : Digest) (s : MachineState)
    (hs : Mid j B k index u l v s) :
    ∃ t, Steps im s (lvlSt j l) (lvlSt j l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      t.getReg .x10 = BitVec.ofNat 64 (B + blkO j l) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = ((lvlRegs j l).get .x12).eval s ∧
      t.pc = pcOf (childBase j + ecIdx j (l + 1)) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      t.getReg .x3 = ((lvlRegs j l).get .x3).eval s ∧
      hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) ∧
      Frame s t (fun A => A = B + tw24 j l ∨ A = B + blkO j l + 16) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hbl := blk_bounds j hj l hl
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (childBase j + (ecIdx j l + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, hec⟩ := childRun_sound hcode (childRun_lvl j hj l hl) s hpc
    (lvlObl_holds j hj l hl hx8 h8 (by unfold MEMORY_BYTES; omega)) rfl
  have hreg : ∀ x, ((lvlRes j l).toState s).getReg x = ((lvlRegs j l).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((lvlRes j l).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO j l + 24 ∧ (l ≤ 3 → hiW j l = true) then
        (if l ≤ 3 then 0 else s.getReg (heapReg (heapOf l j)))
      else if A = B + blkO j l + 16 then (if l ≤ 3 then (lowE j l).eval s else s.getReg .x15)
      else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j hj l A hl hA)
  have hpcT : ((lvlRes j l).toState s).pc = pcOf (childBase j + ecIdx j (l + 1)) := by
    rw [PRes.toState_pc (lvlRes j l) s rfl]; rfl
  generalize ht : (lvlRes j l).toState s = t at hst hec hreg hmem hpcT
  have hb := bitAt_lt j l
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + blkO j l) := by rw [hreg, lvlRegs_x10, eX8_eval hx8]
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
    rw [hreg, lvlRegs_x11]
    split_ifs with h0
    · rfl
    · exact hs.a1 h0
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h3 h10' h11' h12'
    rw [hreg, lvlRegs_other j l r h3 h10' h11' h12', RegFile.init_get_eval]
    exact hkeep r h3 h10' h11' h12'
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.t0
  have tS : ∀ o, o ≤ 1024 → o ≠ blkO j l + 16 → o ≠ blkO j l + 24 →
      t.getMem (BitVec.ofNat 64 (B + o)) = s.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho h16 h24
    rw [hmem _ (by omega), if_neg (fun h => h24 (by have := h.1; omega)), if_neg (by omega)]
  have sU : ∀ o, o ≤ 1024 → o ∉ stagesW j (l + 1) →
      s.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho hn
    refine hs.frame (B + o) (by omega) ?_
    rintro ⟨off, hoff, he⟩
    have : off = o := by omega
    subst this; exact hn hoff
  have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) hj hl h
  have hpad : DigAt t (B + blkO j l + 32) (pads l) := by
    have hP := hu.padAt l hl
    unfold padO at hP
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).1 (by unfold padO; rfl))]
    · rw [show B + (blkO j l + 32) + 8 = B + (blkO j l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        sU _ (by omega) (fun h => (hf _ h).2.1 (by unfold padO; omega))]
  have hcs := sibO_cases j l hl
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l hl
    have hsb : sibO l j = blkO j l ∨ sibO l j = blkO j l + 48 := by omega
    refine DigAt.of_eq hS ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.1 rfl)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.2 rfl)]
  have hnode : DigAt t (B + curO l j) v := by
    have hcb := curO_cases j l
    refine DigAt.of_eq hs.node ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega)]
  have hx15 : s.getReg .x15 = BitVec.ofNat 64 (w0n k index) :=
    (hkeep .x15 (by decide) (by decide) (by decide) (by decide)).trans hu.w0
  have hw0 : 1537 ≤ w0n k index ∧ w0n k index < 2 ^ 64 := by
    have := Nat.mod_lt index (show 0 < 2 ^ 31 by norm_num)
    have := Nat.mod_lt k (show 0 < 16 by norm_num)
    unfold w0n V3.nodeLow ClaudeWCT.WCT9.ftsLeafLow
    omega
  have hhdr : DigAt t (B + blkO j l + 16) (nodeHeader k index (heapOf l j) (hpOf j tws l)) := by
    by_cases h3 : l ≤ 3
    · have hpk := heapOf_packed j l hj h3
      constructor
      · rw [hmem _ (by omega), if_neg (fun h => by have := h.1; omega), if_pos rfl, if_pos h3, hdr11_lo,
          if_pos hpk]
        unfold lowE
        rw [addC_eval]
        simp only [E.eval]
        rw [hx15]
        exact ofNat_add_neg _ _ (by omega) hw0.2 (by omega)
      · rw [show B + blkO j l + 16 + 8 = B + blkO j l + 24 by omega, hdr11_hi, if_pos hpk]
        by_cases hw : hiW j l = true
        · have hb0 : bitAt j l = 0 := by
            simp only [hiW, Bool.and_eq_true, decide_eq_true_eq] at hw; exact hw.2
          rw [hmem _ (by omega), if_pos ⟨rfl, fun _ => hw⟩, if_pos h3]
          unfold hpOf; rw [if_neg (by omega)]
        · have hb1 : bitAt j l = 1 := by
            simp only [hiW, Bool.and_eq_true, decide_eq_true_eq, not_and] at hw; have := hw h3; omega
          have hwf : hiW j l = false := by simpa using hw
          rw [hmem _ (by omega), if_neg (fun h => hw (h.2 h3)), if_neg (by omega),
            show B + blkO j l + 24 = B + (blkO j l + 24) by omega,
            sU _ (by omega) (fun hm => tw_free hj (by omega) hwf hm rfl)]
          have hT := (hu.twAt l hl).2
          rw [show B + blkO j l + 16 + 8 = B + (blkO j l + 24) by omega] at hT
          rw [hT]
          unfold hpOf; rw [if_pos ⟨by omega, hb1⟩]
    · have hlo := heapOf_low j l hj (by omega) (by omega)
      have hnp : ¬ (8 ≤ heapOf l j ∧ heapOf l j < 128) := by omega
      constructor
      · rw [hmem _ (by omega), if_neg (fun h => by have := h.1; omega), if_pos rfl, if_neg h3, hdr11_lo,
          if_neg hnp, hx15]
      · rw [show B + blkO j l + 16 + 8 = B + blkO j l + 24 by omega, hmem _ (by omega),
          if_pos ⟨rfl, fun h => absurd h h3⟩, if_neg h3, hdr11_hi, if_neg hnp]
        have hr := heapReg_eval (s := s) (l := l) hj (by omega) (by omega) (fun h h1 h7 => by
          obtain ⟨n3, n10, n11, n12⟩ := heapReg_ne h
          rw [hkeep _ n3 n10 n11 n12]; exact hu.heaps h h1 h7)
        exact hr
  have hin : hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) := by
    unfold nodeIn
    rcases hcs with ⟨e0, ec, es⟩ | ⟨e1, ec, es⟩
    · simp only [e0, if_true]
      rw [ec] at hnode; rw [es, ← Nat.add_assoc] at hsib
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by omega) (by omega) hnode hhdr hpad hsib
    · simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
      rw [ec, ← Nat.add_assoc] at hnode; rw [es] at hsib
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by omega) (by omega) hsib hhdr hpad hnode
  refine ⟨t, hst, hec rfl, h5, h10, h11, hreg .x12, hpcT, hother, hreg .x3, hin, ?_⟩
  intro A hA hn
  simp only [not_or] at hn
  rw [hmem A hA, if_neg ?_, if_neg hn.2]
  rintro ⟨h24, hc⟩
  apply hn.1
  unfold tw24
  split
  · rename_i hx; exact absurd (hc hx.1) (by simp [hx.2])
  · exact h24
theorem lvl_step {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (l : Nat) (hl : l < 5) (v : Digest) (s : MachineState)
    (hs : Mid j B k index u l v s) :
    ∃ t, Steps im s (lvlSt j l) (lvlSt j l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v l)) ∧
      ∀ a : BitVec 256, Mid j B k index u (l + 1) (a.extractLsb' 0 128) (writeHash t a) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, hec, h5, h10, h11, h12', hpcT, hother, h3', hin, hP⟩ := lvl_core hj hcode hu l (by omega) v s hs
  have hbl := blk_bounds j hj l (by omega)
  have hbl1 := blk_bounds j hj (l + 1) (by omega)
  have hb1 := bitAt_lt j (l + 1)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + curO (l + 1) j) := by
    rw [h12', lvlRegs_x12 j l hl]
    by_cases hsk : skipA2 j l = true
    · rw [if_pos hsk, skipA2_cur hsk]
      simp only [E.eval]
      exact (hs.a2)
    · rw [if_neg hsk, eX8_eval hx8]
  have hcur : curO (l + 1) j % 8 = 0 ∧ curO (l + 1) j + 32 ≤ 912 := by
    have := curO_cases j (l + 1); omega
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO j l) 64 (B + curO (l + 1) j) h10 h11 h12 (by omega) (by decide)
      (by omega) (by omega) (by omega)
  refine ⟨t, hst, hec, h5, hv, hin, fun a => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]
  · intro r h3 h10' h11' h12'; rw [writeHash_getReg]; exact hother r h3 h10' h11' h12'
  · intro _; rw [writeHash_getReg]; exact h11
  · rw [writeHash_getReg]; exact h12
  · exact DigAt.writeHash_lo t a _ h12 (by omega)
  · have hW := frame_writeHash4 t a (B + curO (l + 1) j) h12 (by omega)
    refine ((hs.frame.trans hP).trans hW).mono ?_
    intro A _ hA
    rcases hA with (⟨off, hoff, rfl⟩ | (rfl | rfl)) | (rfl | rfl | rfl | rfl)
    · exact ⟨off, stagesW_mono hoff (by omega), rfl⟩
    · exact ⟨tw24 j l, mem_stagesW (m := l) (by omega) (by simp [stageW]), rfl⟩
    · exact ⟨blkO j l + 16, mem_stagesW (m := l) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), rfl⟩
    · exact ⟨curO (l + 1) j + 8, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j + 16, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j + 24, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
def fuelR (j : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | l, n + 1 => lvlSt j l + 1 + fuelR j (l + 1) n
def cycR (j : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | l, n + 1 => lvlSt j l + 8 + cycR j (l + 1) n
theorem rcheck_all : ∀ j : Fin 128, fuelR j.val 0 5 + childSaveC j.val = 30 ∧ cycR j.val 0 5 + childSaveC j.val = 65 ∧
    childSaveC j.val ≤ 5 ∧ ecIdx j.val 6 + childSaveC j.val = 37 ∧
    childSaveC j.val = ClaudeWCT.WCT9.childSave j.val := by decide +kernel
theorem fuelR_05 (j : Nat) (hj : j < 128) : fuelR j 0 5 + childSaveC j = 30 := (rcheck_all ⟨j, hj⟩).1
theorem cycR_05 (j : Nat) (hj : j < 128) : cycR j 0 5 + childSaveC j = 65 := (rcheck_all ⟨j, hj⟩).2.1
theorem childSaveC_le (j : Nat) (hj : j < 128) : childSaveC j ≤ 5 := (rcheck_all ⟨j, hj⟩).2.2.1
theorem ecIdx_six (j : Nat) (hj : j < 128) : ecIdx j 6 + childSaveC j = 37 := (rcheck_all ⟨j, hj⟩).2.2.2.1
theorem childSaveC_eq (j : Nat) (hj : j < 128) : childSaveC j = ClaudeWCT.WCT9.childSave j :=
  (rcheck_all ⟨j, hj⟩).2.2.2.2
theorem child_rest {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, Mid j B k index u 5 v t → GoodQFor im t N C Q A (K v)) :
    ∀ n l v s, l + n = 5 → Mid j B k index u l v s →
      GoodQFor im s (N + fuelR j l n) (C + cycR j l n) Q (A + cycR j l n)
        (ccM ((List.range' l n).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v) K) := by
  intro n
  induction n with
  | zero =>
    intro l v s hln hs
    have hl5 : l = 5 := by omega
    subst l
    simpa only [List.range'_zero, List.foldlM_nil, ccM_pure, fuelR, cycR, Nat.add_zero] using hK v s hs
  | succ m ih =>
    intro l v s hln hs
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step hj hcode hu l (by omega) v s hs
    rw [List.range'_succ, List.foldlM_cons, childLevelP_eq]
    have H : ∀ a : BitVec 256, GoodQFor im (writeHash t a) (N + fuelR j (l + 1) m) (C + cycR j (l + 1) m) Q
        (A + cycR j (l + 1) m)
        (ccM ((fun v' => (List.range' (l + 1) m).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v')
          (a.extractLsb' 0 128)) K) :=
      fun a => ih (l + 1) _ _ (by omega) (hpost a)
    have hg := GoodQFor.shortHash_bind
      (f := fun v' => (List.range' (l + 1) m).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v') hf h5 hv hin H
    rw [nodeIn_blocks] at hg
    simp only [fuelR, cycR]
    exact GoodQFor.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
theorem leafBytes_length (leaf : Nat → Digest) : (leafBytes leaf).length = 128 := by
  simp [leafBytes, List.length_flatMap, bytesLE_length]
theorem leaf_blocks (leaf : Nat → Digest) : (toQ (pad64 (leafBytes leaf))).blocks = 2 := by
  rw [pad64_of_aligned _ (by rw [leafBytes_length]), blocks_toQ (by rw [Aligned, leafBytes_length]; omega),
    leafBytes_length]
theorem child_prefix_good (im : Image) (j : Nat) (hj : j < 128) (hcode : ChildCodeAt im j)
    (B k index : Nat) (leaf pads sibs tws : Nat → Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs)
    (hu : ChildPre j B k index leaf pads sibs tws u)
    (hK : ∀ v t, Mid j B k index u 5 v t → GoodQFor im t N C Q A (K v)) :
    GoodQFor im u (N + (32 - childSaveC j)) (C + (82 - childSaveC j)) Q (A + (82 - childSaveC j))
      (ccM (shortHash (leafBytes leaf) >>= fun v => (List.range 5).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v) K) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hobl : ∀ o ∈ (p0Res j).st.obl, o.holds u := by
    intro o ho
    simp only [p0Res, List.not_mem_nil] at ho
  obtain ⟨hst, hec⟩ := childRun_sound hcode (childRun_p0 j hj) u hu.pc hobl rfl
  have hreg : ∀ x, ((p0Res j).toState u).getReg x =
      ((RegFile.init.set .x12 (eX8 (curO 0 j))).get x).eval u := fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((p0Res j).toState u).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [PRes.toState_getMem]
    simp only [p0Res, memEval_nil]
  have hpcT : ((p0Res j).toState u).pc = pcOf (childBase j + 2) := PRes.toState_pc (p0Res j) u rfl
  generalize ht : (p0Res j).toState u = t at hst hec hreg hmem hpcT
  have hother : ∀ r : Reg, r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h12; rw [hreg, RegFile.get_set_ne _ _ h12, RegFile.init_get_eval]
  have hb0 := blk_bounds j hj 0 (by decide)
  have hc0 : curO 0 j % 8 = 0 ∧ curO 0 j + 32 ≤ 912 := by have := curO_cases j 0; omega
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + leafO) := (hother .x10 (by decide)).trans hu.a0
  have h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (1 + 1)) := (hother .x11 (by decide)).trans hu.a1
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + curO 0 j) := by
    rw [hreg, RegFile.get_set_self _ _ (by decide), eX8_eval hu.s0]
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide)).trans hu.t0
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + leafO) 128 (B + curO 0 j) h10 h11 h12 (by unfold leafO; omega) (by decide)
      (by unfold leafO; omega) (by omega) (by omega)
  have hslot : ∀ i, i < 8 → DigAt t (B + leafO + 16 * i) (leaf i) := by
    intro i hi
    refine DigAt.of_eq (hu.leafAt i hi) ?_ ?_
    · rw [hmem _ (by unfold leafO; omega)]
    · rw [hmem _ (by unfold leafO; omega)]
  have hin : hashInput t = toQ (pad64 (leafBytes leaf)) := by
    rw [pad64_of_aligned _ (by rw [leafBytes_length])]
    apply hashInput_toQ t _ 1 (B + leafO) (leafBytes_length leaf) h10 (by unfold leafO; omega)
      (by unfold leafO; omega) h11 (by norm_num)
    have hD : DigsAt t (B + leafO) ((List.range 8).map leaf) := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      have e : ((List.range 8).map leaf).getD i 0 = leaf i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rw [e]
      exact hslot i hi
    have hw := hD.words
    simp only [List.length_map, List.length_range] at hw
    rw [hw]
    rfl
  have H : ∀ a : BitVec 256, GoodQFor im (writeHash t a) (N + fuelR j 0 5) (C + cycR j 0 5) Q (A + cycR j 0 5)
      (ccM ((fun v => (List.range 5).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v) (a.extractLsb' 0 128)) K) := by
    intro a
    have hmid : Mid j B k index u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, fun h => absurd rfl h, ?_, ?_, ?_⟩
      · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]; rfl
      · intro r _ _ _ h12'; rw [writeHash_getReg]; exact hother r h12'
      · rw [writeHash_getReg]; exact h12
      · exact DigAt.writeHash_lo t a _ h12 (by omega)
      · have hT : Frame u t (fun _ => False) := by
          intro A hA _
          rw [hmem A hA]
        refine (hT.trans (frame_writeHash4 t a (B + curO 0 j) h12 (by omega))).mono ?_
        intro A _ hA
        rcases hA with hF | (rfl | rfl | rfl | rfl)
        · exact hF.elim
        · exact ⟨curO 0 j, mem_stagesW (m := 0) (by omega) (by simp [stageW]), rfl⟩
        · exact ⟨curO 0 j + 8, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
        · exact ⟨curO 0 j + 16, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
        · exact ⟨curO 0 j + 24, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
    show GoodQFor im (writeHash t a) (N + fuelR j 0 5) (C + cycR j 0 5) Q (A + cycR j 0 5)
      (ccM ((List.range 5).foldlM (childLevelP k index j pads (hpOf j tws) sibs) (a.extractLsb' 0 128)) K)
    rw [List.range_eq_range']
    exact child_rest hj hcode hu K N C A Q hK 5 0 _ _ rfl hmid
  have hg := GoodQFor.shortHash_bind
    (f := fun v => (List.range 5).foldlM (childLevelP k index j pads (hpOf j tws) sibs) v) (hec rfl) h5 hv hin H
  rw [leaf_blocks] at hg
  have hf5 := fuelR_05 j hj
  have hc5 := cycR_05 j hj
  exact GoodQFor.steps' hst hg (by simp only [p0Res]; omega) (by simp only [p0Res]; omega)
    (fun q => ⟨q, by simp only [p0Res]; omega⟩)
end W9Drv.ChildProof
end
section
namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
def prefixWrites (B A : Nat) : Prop := B ≤ A ∧ A < B + 912
theorem stagesW_prefix {j off B : Nat} (hj : j < 128) (h : off ∈ stagesW j 6) : prefixWrites B (B + off) := by
  have hb := stagesW_bound hj (by decide) h
  unfold prefixWrites at *
  omega
theorem handO_cases (j : Nat) : handO j = 192 ∨ handO j = 48 := by
  unfold handO; split <;> simp
theorem last_setup {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 192 ≤ B)
    (v : Digest) (s : MachineState) (hs : Mid j B k index u 5 v s) :
    ∃ t, Steps im s 4 4 t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads (hpOf j tws) sibs v 5)) ∧
      t.pc = pcOf (childBase j + ecIdx j 6) ∧ t.getReg .x11 = 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (B - handO j) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      Frame u t (fun A => ∃ off ∈ stagesW j 6, A = B + off) := by
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have h8 := hu.base8
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B :=
    (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, hec, h5, h10, h11, h12', hpcT, hother, -, hin, hP⟩ := lvl_core hj hcode hu 5 (by decide) v s hs
  have hl5 : lvlSt j 5 = 4 := by
    have h6 : ecIdx j 6 = ecIdx j 5 + lvlLen j 5 + (if 5 = 0 then 1 else 0) := rfl
    have hlen : lvlLen j 5 = 5 := by simp [lvlLen, skipA2_five, hiW]
    unfold lvlSt; rw [h6, hlen, if_neg (by decide)]; omega
  rw [hl5] at hst
  have hbl := blk_bounds j hj 5 (by decide)
  have hho := handO_cases j
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B - handO j) := by
    rw [h12', show (lvlRegs j 5).get .x12 = addC (.reg .x8) (BitVec.ofNat 64 (2 ^ 64 - handO j)) by
      unfold lvlRegs; rw [skipA2_five]; rfl, addC_eval]
    simp only [E.eval, hx8]
    exact ofNat_add_neg B (handO j) (by omega) (by omega) (by omega)
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO j 5) 64 (B - handO j) h10 h11 h12 (by omega) (by decide)
      (by omega) (by omega) (by omega)
  refine ⟨t, hst, hec, h5, hv, hin, hpcT, h11, h12, hother, ?_⟩
  apply (hs.frame.trans hP).mono
  intro A hA h
  rcases h with h | rfl | rfl
  · exact h
  · exact ⟨tw24 j 5, mem_stagesW (m := 5) (by omega) (by simp [stageW]), rfl⟩
  · exact ⟨blkO j 5 + 16, mem_stagesW (m := 5) (by omega) (by simp [stageW]), by omega⟩
/-- The heap-2/3 level hashed for its high half (the nested FTS top node). -/
def childLevelHi (k index j : Nat) (pads : Nat → Digest) (hps : Nat → BitVec 64) (sibs : Nat → Digest)
    (value : Digest) : M Digest :=
  V3.hashHi (nodeIn k index j pads hps sibs value 5)
structure HandPost (B j : Nat) (u : MachineState) (computed : Digest) (t : MachineState) : Prop where
  pc : t.pc = (u.getReg .x1 + 296) &&& ~~~1#64
  a1 : t.getReg .x11 = 64
  top : DigAt t (B - handO j + 16) computed
  a2 : t.getReg .x12 = BitVec.ofNat 64 (B - handO j)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r
  frame : Frame u t (fun A => prefixWrites B A ∨ (B - handO j ≤ A ∧ A < B - handO j + 32))
theorem tail_good {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs tws : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 192 ≤ B)
    (v : Digest) (s : MachineState) (hs : Mid j B k index u 5 v s)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs)
    (hK : ∀ computed t, HandPost B j u computed t → GoodQFor im t N C Q A (K computed)) :
    GoodQFor im s (N + 6) (C + 13) Q (A + 13)
      (ccM (childLevelHi k index j pads (hpOf j tws) sibs v) K) := by
  have hBhi := hu.baseHi
  unfold MEMORY_BYTES at hBhi
  have hho := handO_cases j
  obtain ⟨t, hst, hf, h5, hv, hin, hpc, h11, h12, hkeep, hframe⟩ :=
    last_setup hj hcode hu hlo v s hs
  have H : ∀ ans : BitVec 256, GoodQFor im (writeHash t ans) (N + 1) (C + 1) Q (A + 1)
      (ccM (pure (ans.extractLsb' 128 128)) K) := by
    intro ans
    have hdest : B - handO j + 32 < 2 ^ 64 := by omega
    let z := (p7Res j).toState (writeHash t ans)
    have hpcW : (writeHash t ans).pc = pcOf (childBase j + (ecIdx j 6 + 1)) := by
      rw [writeHash_pc, hpc, SigGolfCandidate.T3M.pcOf_add4, Nat.add_assoc]
    obtain ⟨hz, -⟩ := childRun_sound hcode (childRun_p7 j hj) (writeHash t ans) hpcW
      (by intro o ho; simp [p7Res] at ho) rfl
    have hzreg : ∀ x, z.getReg x = (writeHash t ans).getReg x := by
      intro x
      rw [PRes.toState_getReg]
      simp only [p7Res, RegFile.init_get_eval]
    have hzmem : ∀ A, z.getMem A = (writeHash t ans).getMem A := by
      intro A
      rw [PRes.toState_getMem]
      simp only [p7Res, memEval_nil]
    have hp : HandPost B j u (ans.extractLsb' 128 128) z := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have e : z.pc = ((writeHash t ans).getReg .x1 + 296) &&& ~~~1#64 := rfl
        rw [e, writeHash_getReg, hkeep .x1 (by decide) (by decide) (by decide) (by decide)]
      · rw [hzreg, writeHash_getReg, h11]
      · have hd := DigAt.writeHash_hi t ans _ h12 hdest
        exact ⟨(hzmem _).trans hd.1, (hzmem _).trans hd.2⟩
      · rw [hzreg, writeHash_getReg]; exact h12
      · intro r h3 h10 h11' h12'
        rw [hzreg, writeHash_getReg]
        exact hkeep r h3 h10 h11' h12'
      · have hw := frame_writeHash4 t ans _ h12 hdest
        have hF : Frame u (writeHash t ans)
            (fun A => prefixWrites B A ∨ (B - handO j ≤ A ∧ A < B - handO j + 32)) := by
          apply (hframe.trans hw).mono
          intro addr _ hh
          rcases hh with ⟨off, hoff, rfl⟩ | hw
          · exact Or.inl (stagesW_prefix hj hoff)
          · right
            rcases hw with rfl | rfl | rfl | rfl <;> omega
        intro A hA hn
        rw [hzmem]
        exact hF A hA hn
    have hfin := GoodQFor.steps hz (hK _ z hp)
    simpa only [ccM_pure, p7Res] using hfin
  have hh := GoodQFor.publicHash_bind (f := fun a => (pure (a.extractLsb' 128 128) : M Digest)) (K := K) hf h5 hv hin H
  rw [nodeIn_blocks] at hh
  unfold childLevelHi V3.hashHi
  exact GoodQFor.steps' hst hh (by omega) (by omega) (fun q => ⟨q, by omega⟩)
end W9Drv.ChildProof
end
section
namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
theorem nodeInput_eq (k index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) :
    V3.nodeInput k index heap left hp pad right = blk4 left (nodeHeader k index heap hp) pad right := by
  simp only [V3.nodeInput, blk4, nodeHeader, List.append_assoc]
theorem heapOf_eq (j l : Nat) (hl : l < 6) : heapOf l j = (128 + j) / 2 ^ (l + 1) := by
  interval_cases l <;> norm_num [heapOf, Nat.add_div] <;> omega
theorem source_level (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (v : Digest) (l : Nat) (hl : l < 6) :
    (let other := V3.sibling w k.val j.val l
     let left := if j.val / 2 ^ l % 2 = 0 then v else other
     let right := if j.val / 2 ^ l % 2 = 0 then other else v
     shortHash (V3.nodeInput k.val index ((128 + j.val) / 2 ^ (l + 1)) left (V3.nodeHPad w k.val j.val l)
       (V3.nodePad w k.val j.val l) right)) =
    childLevelP k.val index j.val (V3.nodePad w k.val j.val) (V3.nodeHPad w k.val j.val) (V3.sibling w k.val j.val) v l := by
  dsimp only
  rw [nodeInput_eq, ← heapOf_eq _ _ hl]
  unfold childLevelP bitAt
  split_ifs <;> rfl
theorem childProgram_split (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (ends : List Digest) :
    V3.childProgram w index k j ends =
      (shortHash (leafBytes (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends)) >>= fun v =>
        (List.range 5).foldlM (childLevelP k.val index j.val (V3.nodePad w k.val j.val) (V3.nodeHPad w k.val j.val) (V3.sibling w k.val j.val)) v >>=
        fun v5 => childLevelHi k.val index j.val (V3.nodePad w k.val j.val) (V3.nodeHPad w k.val j.val)
          (V3.sibling w k.val j.val) v5) := by
  unfold V3.childProgram V3.childN
  congr 1
  funext v
  have hfold (ls : List Nat) (hls : ∀ l ∈ ls, l < 6) (v : Digest) :
      ls.foldlM (fun value level =>
        let other := V3.sibling w k.val j.val level
        let left := if j.val / 2 ^ level % 2 = 0 then value else other
        let right := if j.val / 2 ^ level % 2 = 0 then other else value
        shortHash (V3.nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
          left (V3.nodeHPad w k.val j.val level) (V3.nodePad w k.val j.val level) right)) v =
      ls.foldlM (childLevelP k.val index j.val (V3.nodePad w k.val j.val) (V3.nodeHPad w k.val j.val) (V3.sibling w k.val j.val)) v := by
    induction ls generalizing v with
    | nil => rfl
    | cons l ls ih =>
      rw [List.foldlM_cons, List.foldlM_cons, source_level w index k j v l (hls l (by simp))]
      congr 1
      funext v'
      exact ih (fun i hi => hls i (List.mem_cons_of_mem _ hi)) v'
  rw [hfold (List.range 5) (fun l hl => by have := List.mem_range.mp hl; omega)]
  congr 1
  funext v5
  have hp : V3.nodeHPad w k.val j.val 5 = 0 := by simp [V3.nodeHPad]
  have hh : (128 + j.val) / 2 ^ 6 = heapOf 5 j.val := (heapOf_eq _ _ (by decide)).symm
  simp only [childLevelHi, nodeIn, nodeInput_eq, hp, hh, bitAt]
  by_cases h : j.val / 32 % 2 = 0 <;> simp [h]
theorem child_code (j : Nat) (hj : j < 128) : ChildCodeAt Frozen.image j := by
  have hc := (slice_at _ _ (child_linked j hj)).2.2.2
  have hp : (pcOf (childBase j)).toNat = 4096 + 4 * childBase j := by
    simp only [pcOf, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by unfold childBase; omega)
  rw [hp, show (4096 + 4 * childBase j - 4096) / 4 = childBase j by omega] at hc
  intro i word hi
  obtain ⟨hbound, hval⟩ := List.getElem?_eq_some_iff.mp hi
  have h := List.prefix_iff_getElem?.mp hc i hbound
  simpa only [List.getElem?_drop, hval] using h
theorem sibO_v3 (j l : Nat) (hl : l < 6) : sibO l j = V3.sibOff j l := by
  unfold sibO V3.sibOff blkO bitAt
  rw [if_pos hl]
theorem child_pre (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (ends : List Digest)
    (u : MachineState) (hu : Child.Pre Frozen.layout w index k j ends u) :
    ChildPre j.val (coordinateBase k) k.val index (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends)
      (V3.nodePad w k.val j.val) (V3.sibling w k.val j.val) (V3.nodeTw w k.val j.val) u := by
  refine ⟨hu.pc, ?_, ?_, hu.hashMode, hu.baseReg, hu.hashInput, hu.hashLen, hu.nodeWord, hu.childIdx,
    ?_, hu.leafAt, hu.padAt, ?_, ?_⟩
  · unfold coordinateBase
    omega
  · have hk := k.isLt
    unfold coordinateBase MEMORY_BYTES
    omega
  · intro h h2 h7
    have he : heapReg h = Child.heapReg h := by interval_cases h <;> rfl
    rw [he]
    exact hu.heaps h h2 h7
  · intro l hl
    rw [sibO_v3 j.val l hl]
    exact hu.sibAt l hl
  · intro l hl
    exact hu.twAt l hl
theorem hpOf_nodeTw (w : ClaudeWCT.W9.T3M.WBytes) (k j : Nat) :
    hpOf j (V3.nodeTw w k j) = V3.nodeHPad w k j := by
  funext l
  unfold hpOf V3.nodeHPad bitAt
  rfl
set_option maxRecDepth 100000 in
theorem child_good : ChildGood := by
  intro j w index k ends u N C A Q K hu hK
  have hp := child_pre w index k j ends u hu
  have hcode := child_code j.val j.isLt
  have hlo : 192 ≤ coordinateBase k := by unfold coordinateBase; omega
  have hg := child_prefix_good Frozen.image j.val j.isLt hcode (coordinateBase k) k.val index
    (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends) (V3.nodePad w k.val j.val) (V3.sibling w k.val j.val)
    (V3.nodeTw w k.val j.val) u
    (N + 6) (C + 13) (A + 13) Q
    (fun v => ccM (childLevelHi k.val index j.val (V3.nodePad w k.val j.val) (hpOf j.val (V3.nodeTw w k.val j.val))
      (V3.sibling w k.val j.val) v) K)
    hp (fun v s hs => by
      apply tail_good j.isLt hcode hp hlo v s hs N C A Q K
      intro computed t ht
      have hb6 : bitAt j.val 6 = j.val / 64 % 2 := rfl
      have hhand : coordinateBase k - handO j.val + 16 = Child.handAddr k j ∧
          coordinateBase k - handO j.val = Child.handAddr k j - 16 := by
        have := hlo
        unfold handO Child.handAddr
        rw [hb6]
        split_ifs <;> omega
      apply hK _ t
      refine ⟨?_, ht.a1, ?_, ?_, ?_, ?_⟩
      · rw [ht.pc, hu.returnPC]
        fin_cases k <;> decide
      · rw [← hhand.1]; exact ht.top
      · rw [ht.a2, hhand.2]
      · intro r hr
        simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact ht.keep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1
      · apply ht.frame.mono
        intro A _ hA
        unfold Child.writes
        unfold prefixWrites at hA
        omega)
  rw [childProgram_split]
  rw [hpOf_nodeTw] at hg
  have hsv := childSaveC_le j.val j.isLt
  have hse := childSaveC_eq j.val j.isLt
  simp only [ccM_bind, Nat.add_assoc] at hg ⊢
  exact hg.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
end W9Drv.ChildProof
end
theorem W9Drv.childGood : ∀ j : Fin 128,
    W9Machine.Child.Good W9Machine.Frozen.layout ⟨38, 95, 95 - ClaudeWCT.WCT9.childSave j.val⟩ j :=
  W9Drv.ChildProof.child_good
