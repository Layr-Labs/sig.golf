import SigGolfCandidate.Merge052

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_OldWit ====
section

/-! # The pre-witness-stack (opus-choice, W 23236) witness layout, frozen for the expand port

Copied from the pre-port `ClaudeWCT.W9.T3M.Witness.{Layout,Encode,Honest}` (layout/encoding part only). The
img-merged expander runs the old layer/leaf-buffer code unchanged and leaves the bytes `[8096, 23236)` of this
layout at absolute `2904 + offset` before the witness-stack post-pass (words 49400..54175) moves them into the
current layout (`ClaudeWCT.W9.T3M.witList`, at absolute 4128). -/

section
namespace ClaudeWCT.W9.Machine.Expand.OldW
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff chainP nodeHashP PubGood allQ_bind allQ_mapM allQ_foldlM pubGood_chainP
  pubGood_leafHash pubGood_nodeHashP)
open SigGolfCandidate.T3M.SecurityExtraction (hashPath merkleInput foldlM_finRange_eq_hashPath)
/-- The pre-witness-stack G rule: only odd chains of lower layers (the top layer was all F). -/
def isG (lay : Layer) (i : Nat) : Bool := decide (lay ≠ 0) && decide (i % 2 = 1)
@[simp] theorem isG_top (i : Nat) : isG 0 i = false := by simp [isG]
theorem isG_eq_true {lay : Layer} {i : Nat} : isG lay i = true ↔ lay ≠ 0 ∧ i % 2 = 1 := by simp [isG]
theorem isG_eq_false {lay : Layer} {i : Nat} (h : lay = 0 ∨ i % 2 = 0) : isG lay i = false := by
  rcases h with h | h <;> simp [isG, h]
theorem isG_zero (lay : Layer) : isG lay 0 = false := isG_eq_false (Or.inr rfl)
def wsize : Nat := 23236
abbrev WBytes := BitVec (8 * 23236)
def wbyte (w : WBytes) (i : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * i) 8)
def wdig (w : WBytes) (off : Nat) : Digest := w.extractLsb' (8 * off) 128
def wle32 (w : WBytes) (off : Nat) : BitVec 32 := w.extractLsb' (8 * off) 32
def rhoOff : Nat := 23208
def dcOff : Nat := 23232
def layerBase (lay : Layer) : Nat := (![8096, 12320, 14968, 17536] : Layer → Nat) lay
def pathSlots (lay : Layer) : Nat := (![48, 25, 20, 20] : Layer → Nat) lay
def lowerPlanL1 : List (List Nat) :=[[1,4,7,10,13,21,16],[0,4,7,10,13,21,16],[1,8,12,15,18,21,4],[0,8,12,15,18,21,4],[1,4,11,15,18,21,7],[0,4,11,15,18,21,7],[1,11,8,15,18,21,4],[0,11,8,15,18,21,4],[1,4,7,14,18,21,10],[0,4,7,14,18,21,10],[1,11,15,8,18,21,4],[0,11,15,8,18,21,4],[1,4,14,11,18,21,7],[0,4,14,11,18,21,7],[1,14,11,8,18,21,4],[0,14,11,8,18,21,4],[1,4,7,10,17,21,13],[0,4,7,10,17,21,13],[1,11,15,18,8,21,4],[0,11,15,18,8,21,4],[1,4,14,18,11,21,7],[0,4,14,18,11,21,7],[1,14,11,18,8,21,4],[0,14,11,18,8,21,4],[1,4,7,17,14,21,10],[0,4,7,17,14,21,10],[1,14,18,11,8,21,4],[0,14,18,11,8,21,4],[1,4,17,14,11,21,7],[0,4,17,14,11,21,7],[1,17,14,11,8,21,4],[0,17,14,11,8,21,4],[1,4,7,10,13,20,16],[0,4,7,10,13,20,16],[1,11,15,18,21,8,4],[0,11,15,18,21,8,4],[1,4,14,18,21,11,7],[0,4,14,18,21,11,7],[1,14,11,18,21,8,4],[0,14,11,18,21,8,4],[1,4,7,17,21,14,10],[0,4,7,17,21,14,10],[1,14,18,11,21,8,4],[0,14,18,11,21,8,4],[1,4,17,14,21,11,7],[0,4,17,14,21,11,7],[1,17,14,11,21,8,4],[0,17,14,11,21,8,4],[1,4,7,10,20,17,13],[0,4,7,10,20,17,13],[1,14,18,21,11,8,4],[0,14,18,21,11,8,4],[1,4,17,21,14,11,7],[0,4,17,21,14,11,7],[1,17,14,21,11,8,4],[0,17,14,21,11,8,4],[1,4,7,20,17,14,10],[0,4,7,20,17,14,10],[1,17,21,14,11,8,4],[0,17,21,14,11,8,4],[1,4,20,17,14,11,7],[0,4,20,17,14,11,7],[1,20,17,14,11,8,4],[0,20,17,14,11,8,4],[1,4,7,10,18,21,14],[0,4,7,10,18,21,14],[1,8,12,15,18,21,5],[0,8,12,15,18,21,5],[1,4,11,15,18,21,8],[0,4,11,15,18,21,8],[1,11,8,15,18,21,5],[0,11,8,15,18,21,5],[1,4,7,14,18,21,11],[0,4,7,14,18,21,11],[1,11,15,8,18,21,5],[0,11,15,8,18,21,5],[1,4,14,11,18,21,8],[0,4,14,11,18,21,8],[1,14,11,8,18,21,5],[0,14,11,8,18,21,5],[1,4,7,10,17,21,14],[0,4,7,10,17,21,14],[1,11,15,18,8,21,5],[0,11,15,18,8,21,5],[1,4,14,18,11,21,8],[0,4,14,18,11,21,8],[1,14,11,18,8,21,5],[0,14,11,18,8,21,5],[1,4,7,17,14,21,11],[0,4,7,17,14,21,11],[1,14,18,11,8,21,5],[0,14,18,11,8,21,5],[1,4,17,14,11,21,8],[0,4,17,14,11,21,8],[1,17,14,11,8,21,5],[0,17,14,11,8,21,5],[1,4,7,10,21,17,14],[0,4,7,10,21,17,14],[1,11,15,18,21,8,5],[0,11,15,18,21,8,5],[1,4,14,18,21,11,8],[0,4,14,18,21,11,8],[1,14,11,18,21,8,5],[0,14,11,18,21,8,5],[1,4,7,17,21,14,11],[0,4,7,17,21,14,11],[1,14,18,11,21,8,5],[0,14,18,11,21,8,5],[1,4,17,14,21,11,8],[0,4,17,14,21,11,8],[1,17,14,11,21,8,5],[0,17,14,11,21,8,5],[1,4,7,10,20,17,14],[0,4,7,10,20,17,14],[1,14,18,21,11,8,5],[0,14,18,21,11,8,5],[1,4,17,21,14,11,8],[0,4,17,21,14,11,8],[1,17,14,21,11,8,5],[0,17,14,21,11,8,5],[1,4,7,20,17,14,11],[0,4,7,20,17,14,11],[1,17,21,14,11,8,5],[0,17,21,14,11,8,5],[1,4,20,17,14,11,8],[0,4,20,17,14,11,8],[1,20,17,14,11,8,5],[0,20,17,14,11,8,5]]
def lowerPlanL32 : List (List Nat) :=[[1,4,7,10,13,16],[0,4,7,10,13,16],[4,0,7,10,13,16],[3,0,7,10,13,16],[4,7,0,10,13,16],[3,7,0,10,13,16],[7,3,0,10,13,16],[6,3,0,10,13,16],[4,7,10,0,13,16],[3,7,10,0,13,16],[7,3,10,0,13,16],[6,3,10,0,13,16],[7,10,3,0,13,16],[6,10,3,0,13,16],[10,6,3,0,13,16],[9,6,3,0,13,16],[4,7,10,13,0,16],[3,7,10,13,0,16],[7,3,10,13,0,16],[6,3,10,13,0,16],[7,10,3,13,0,16],[6,10,3,13,0,16],[10,6,3,13,0,16],[9,6,3,13,0,16],[7,10,13,3,0,16],[6,10,13,3,0,16],[10,6,13,3,0,16],[9,6,13,3,0,16],[10,13,6,3,0,16],[9,13,6,3,0,16],[13,9,6,3,0,16],[12,9,6,3,0,16],[4,7,10,13,16,0],[3,7,10,13,16,0],[7,3,10,13,16,0],[6,3,10,13,16,0],[7,10,3,13,16,0],[6,10,3,13,16,0],[10,6,3,13,16,0],[9,6,3,13,16,0],[7,10,13,3,16,0],[6,10,13,3,16,0],[10,6,13,3,16,0],[9,6,13,3,16,0],[10,13,6,3,16,0],[9,13,6,3,16,0],[13,9,6,3,16,0],[12,9,6,3,16,0],[7,10,13,16,3,0],[6,10,13,16,3,0],[10,6,13,16,3,0],[9,6,13,16,3,0],[10,13,6,16,3,0],[9,13,6,16,3,0],[13,9,6,16,3,0],[12,9,6,16,3,0],[10,13,16,6,3,0],[9,13,16,6,3,0],[13,9,16,6,3,0],[12,9,16,6,3,0],[13,16,9,6,3,0],[12,16,9,6,3,0],[16,12,9,6,3,0],[15,12,9,6,3,0]]
def lowerPlan (lay : Layer) (leaf : Nat) : List Nat :=
  if lay.val = 1 then lowerPlanL1.getD (leaf % 128) [] else lowerPlanL32.getD (leaf % 64) []
/-! ### C4 top window plan (48 slots, two lines; rows from c4-top/topplan_lean.txt, generated from logs/plan_c4.json)
Slot `s` is witness offset `layerBase 0 + 16 * s`. Line A (`topPlanA`, row `leaf % 64`) places the windows of levels
0..5, line B (`topPlanB`, row `leaf / 64 % 64`) those of levels 6..11. A window at slot `A` holds the left input at
`A`, the label word at `A + 1` (bytes 0..8 written by the verifier, bytes 8..16 the witness high pad), the Z pad at
`A + 2` and the right input at `A + 3`; the sibling sits at `A + 3` when the node bit is 0 and at `A` when it is 1
(`sibOff`). `topRootSlot k` is the slot of the root answer read by the compare of upper copy `k` (machine only). -/
def topPlanA : List (List Nat) :=[[30,33,36,39,42,25],[29,33,36,39,42,25],[30,34,38,41,44,25],[29,34,38,41,44,25],[30,33,37,41,44,25],[29,33,37,41,44,25],[30,37,34,41,44,25],[29,37,34,41,44,25],[30,33,36,40,44,25],[29,33,36,40,44,25],[30,37,41,34,44,25],[29,37,41,34,44,25],[30,33,40,37,44,25],[29,33,40,37,44,25],[30,40,37,34,44,25],[29,40,37,34,44,25],[30,33,36,39,43,25],[29,33,36,39,43,25],[30,37,41,44,34,25],[29,37,41,44,34,25],[30,33,40,44,37,25],[29,33,40,44,37,25],[30,40,37,44,34,25],[29,40,37,44,34,25],[30,33,36,43,40,25],[29,33,36,43,40,25],[30,40,44,37,34,25],[29,40,44,37,34,25],[30,33,43,40,37,25],[29,33,43,40,37,25],[30,43,40,37,34,25],[29,43,40,37,34,25],[29,32,35,38,41,25],[28,32,35,38,41,25],[29,33,37,40,43,25],[28,33,37,40,43,25],[29,32,36,40,43,25],[28,32,36,40,43,25],[29,33,44,37,40,25],[28,33,44,37,40,25],[29,32,35,39,43,25],[28,32,35,39,43,25],[29,33,37,44,40,25],[28,33,37,44,40,25],[29,32,36,44,40,25],[28,32,36,44,40,25],[29,33,44,41,37,25],[28,33,44,41,37,25],[29,32,35,38,42,25],[28,32,35,38,42,25],[29,33,37,40,44,25],[28,33,37,40,44,25],[29,32,36,40,44,25],[28,32,36,40,44,25],[29,33,44,37,41,25],[28,33,44,37,41,25],[29,32,35,39,44,25],[28,32,35,39,44,25],[29,33,37,44,41,25],[28,33,37,44,41,25],[29,32,36,44,41,25],[28,32,36,44,41,25],[29,33,44,41,38,25],[28,33,44,41,38,25]]
def topPlanB : List (List Nat) :=[[0,3,6,9,12,15],[0,4,7,10,13,16],[0,4,8,11,14,17],[0,5,9,12,15,18],[0,3,7,11,14,17],[0,4,8,12,15,18],[0,4,9,13,16,19],[0,5,10,14,17,20],[0,3,6,10,14,17],[0,4,7,11,15,18],[0,4,8,12,16,19],[0,5,9,13,17,20],[0,3,7,12,16,19],[0,4,8,13,17,20],[0,4,9,20,13,16],[0,5,13,10,17,20],[0,3,6,9,13,17],[0,4,7,10,14,18],[0,4,8,11,15,19],[0,5,9,12,16,20],[0,3,7,11,15,19],[0,4,8,12,16,20],[0,4,9,13,20,16],[0,5,13,17,10,20],[0,3,6,10,15,19],[0,4,7,11,16,20],[0,4,8,12,20,16],[0,5,9,16,13,20],[0,3,7,12,20,16],[0,4,8,16,13,20],[0,4,9,20,17,13],[0,5,16,13,10,20],[0,3,6,9,12,16],[0,4,7,10,13,17],[0,4,8,11,14,18],[0,5,9,12,15,19],[0,3,7,11,14,18],[0,4,8,12,15,19],[0,4,9,13,16,20],[0,5,13,17,20,10],[0,3,6,10,14,18],[0,4,7,11,15,19],[0,4,8,12,16,20],[0,5,9,16,20,13],[0,3,7,12,16,20],[0,4,8,16,20,13],[0,4,9,20,13,17],[0,5,16,13,20,10],[0,3,6,9,13,18],[0,4,7,10,14,19],[0,4,8,11,15,20],[0,5,9,12,19,16],[0,3,7,11,15,20],[0,4,8,12,19,16],[0,4,9,13,20,17],[0,5,16,20,13,10],[0,3,6,10,15,20],[0,4,7,11,19,16],[0,4,8,12,20,17],[0,5,9,19,16,13],[0,3,7,12,20,17],[0,4,8,19,16,13],[0,4,9,20,17,14],[0,5,19,16,13,10]]
def topRootSlot : List Nat :=[14,15,16,17,16,17,18,19,16,17,18,19,18,19,15,19,16,17,18,19,18,19,15,19,18,19,15,19,15,19,12,19,19,20,21,22,21,22,23,13,21,22,23,16,23,16,20,13,21,22,23,19,23,19,20,13,23,19,20,16,20,16,17,13]
/-- C4: slot of the level-`j` top window of leaf `leaf`. -/
def topPlanSlot (leaf j : Nat) : Nat :=
  if j < 6 then (topPlanA.getD (leaf % 64) []).getD j 0 else (topPlanB.getD (leaf / 64 % 64) []).getD (j - 6) 0
def merkleBlock (lay : Layer) (leaf j : Nat) : Nat :=
  layerBase lay + (if lay.val = 0 then 16 * topPlanSlot leaf j else 16 * (lowerPlan lay leaf).getD j 0)
/-- Pairing stage 1: offset of chain `i`'s block inside the chain area of layer `lay`. Top: 64-byte F blocks, chain 0
highest; T51: the top keeps #938's 54 blocks (chain `i` at block `53 - i`, the blocks of chains 51..53 stay zero),
so the offset is `64 (53 - i)`, not `64 (chainCount 0 - 1 - i)`. Lower layers: chain 0's F block is highest (offset 2184); pair `p` (G chain `2p+1`, F chain `2p+2`) occupies
`[104 (20 - p), +104)`: a 16-byte junk gap, the G block at `+16` and the F block at `+40` (overlapping the G block's
zero tail). -/
def chainSlot (lay : Layer) (i : Nat) : Nat :=
  if lay.val = 0 then 64 * (53 - i)
  else if i = 0 then 2184 else if i % 2 = 1 then 104 * (20 - i / 2) + 16 else 104 * (21 - i / 2) + 40
/-- Bytes of the chain area of layer `lay` (T51 top: #938's 54 blocks, a constant). -/
def chainArea (lay : Layer) : Nat := if lay.val = 0 then 3456 else 2248
def chainBlock (lay : Layer) (i : Nat) : Nat :=
  layerBase lay + 16 * pathSlots lay + chainSlot lay i
def wrho (w : WBytes) : Digest := wdig w rhoOff
def wdc (w : WBytes) : BitVec 32 := wle32 w dcOff
def wdcWord (w : WBytes) : BitVec 64 := w.extractLsb' (8 * dcOff) 64
theorem wdc_toNat_le (w : WBytes) : (wdc w).toNat ≤ (wdcWord w).toNat := by
  unfold wdc wle32 wdcWord
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  rw [show (2 : Nat) ^ 32 = 2 ^ 32 from rfl, ← Nat.mod_mod_of_dvd _ (show 2 ^ 32 ∣ 2 ^ 64 by norm_num)]
  exact Nat.mod_le _ _
/-- Offset of the supplied value inside a chain block: 48 (F) or 0 (G, value first). -/
def valueOff (lay : Layer) (i : Nat) : Nat := if isG lay i then 0 else 48
/-- Offsets of the two zero pads inside a chain block: 0 and 32 (F) or 32 and 48 (G). -/
def pad0Off (lay : Layer) (i : Nat) : Nat := if isG lay i then 32 else 0
def pad1Off (lay : Layer) (i : Nat) : Nat := if isG lay i then 48 else 32
def wvalue (w : WBytes) (lay : Layer) (i : Nat) : Digest := wdig w (chainBlock lay i + valueOff lay i)
/-- Offsets in expanded witness memory, before its 2048-byte machine base. -/
def leafBufferBase (lay : Layer) : Nat := (![22296,21576,20840,20104] : Layer → Nat) lay

/-- T51 ("endpad"): every leaf buffer, the top included, is `end_0 | tweak | end_1 ..` (top: end_0 at 22296, the
tweak / choice byte at 22312, end_i at 22312 + 16 i; #938's top was `pad16 | tweak | end_0 ..`). -/
def leafBufferSlot (lay : Layer) (i : Nat) : Nat :=
  leafBufferBase lay + (if i = 0 then 0 else 16+16*i)

/-- The verifier reads a skipped endpoint from its preserved leaf-buffer slot.
No equality with the redundant old chain value is assumed for arbitrary witnesses. -/
def wvalueFor (w : WBytes) (lay : Layer) (digits : List Nat) (i : Nat) : Digest :=
  if WCT9.safeZeroCopy lay digits i then wdig w (leafBufferSlot lay i) else wvalue w lay i

theorem wvalueFor_skip (w : WBytes) (lay : Layer) (digits : List Nat) (i : Nat)
    (h : WCT9.safeZeroCopy lay digits i) :
    wvalueFor w lay digits i = wdig w (leafBufferSlot lay i) := by simp [wvalueFor,h]

theorem wvalueFor_copy (w : WBytes) (lay : Layer) (digits : List Nat) (i : Nat)
    (h : ¬WCT9.safeZeroCopy lay digits i) :
    wvalueFor w lay digits i = wvalue w lay i := by simp [wvalueFor,h]


theorem leafBufferSlot_mono (lay : Layer) (i j : Nat) (h : i ≤ j) :
    leafBufferSlot lay i ≤ leafBufferSlot lay j := by
  unfold leafBufferSlot
  split_ifs <;> omega

theorem leafBufferSlot_gap (lay : Layer) (i j : Nat) (h : i < j) :
    leafBufferSlot lay i + 16 ≤ leafBufferSlot lay j := by
  unfold leafBufferSlot
  split_ifs <;> omega

theorem leafBufferSlot_gap_two (lay : Layer) (i j : Nat) (h : i + 2 ≤ j) :
    leafBufferSlot lay i + 32 ≤ leafBufferSlot lay j := by
  unfold leafBufferSlot
  split_ifs <;> omega

theorem leafBufferSlot_head_gap (lay : Layer) (_h : lay ≠ 0) :
    leafBufferSlot lay 0 + 32 ≤ leafBufferSlot lay 1 := by
  simp [leafBufferSlot]

theorem leafBufferBase_bounds (lay : Layer) :
    20104 ≤ leafBufferBase lay ∧ leafBufferBase lay ≤ 22296 ∧ leafBufferBase lay % 8 = 0 := by
  fin_cases lay <;> decide +kernel

theorem leafBufferSlot_bounds (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    20104 ≤ leafBufferSlot lay i ∧ leafBufferSlot lay i + 32 ≤ 23208 ∧
      leafBufferSlot lay i % 8 = 0 := by
  fin_cases lay <;> simp only [chainCount, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_succ] at hi
  all_goals simp only [leafBufferSlot,leafBufferBase,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_succ,show (0:Layer)=0 from rfl,if_true] at *
  all_goals norm_num at *
  all_goals (try split_ifs) <;> omega

/-- Every actual endpoint operation writes at most 16 bytes for a zero-step
chain and 32 bytes for a chain that performs at least one hash. -/
def leafBufferWriteEnd (lay : Layer) (digits : List Nat) (i : Nat) : Nat :=
  leafBufferSlot lay i + (if digits.getD i 0 < maxDigit lay i then 32 else 16)

-- T51: leafBuffer_safe_separate (dead in #938, false shape for the endpad top leaf) deleted.

/-- Allowed leaf-buffer writes before processing endpoint `i`. -/
def leafBufferPast (lay : Layer) (digits : List Nat) (i0 i A : Nat) : Prop :=
  ∃ j, i0 ≤ j ∧ j < i ∧ leafBufferSlot lay j ≤ A ∧ A < leafBufferWriteEnd lay digits j

theorem leafBufferPast_mono (lay : Layer) (digits : List Nat) (i0 i k A : Nat)
    (hik : i ≤ k) (h : leafBufferPast lay digits i0 i A) :
    leafBufferPast lay digits i0 k A := by
  obtain ⟨j,hj0,hji,hlo,hhi⟩ := h
  exact ⟨j,hj0,lt_of_lt_of_le hji hik,hlo,hhi⟩

theorem leafBufferPast_write (lay : Layer) (digits : List Nat) (i0 i A : Nat)
    (hi0 : i0 ≤ i) (hlo : leafBufferSlot lay i ≤ A) (hhi : A < leafBufferWriteEnd lay digits i) :
    leafBufferPast lay digits i0 (i+1) A := ⟨i,hi0,by omega,hlo,hhi⟩

theorem leafBufferPast_copy (lay : Layer) (digits : List Nat) (i0 i A : Nat)
    (hi0 : i0 ≤ i) (hlo : leafBufferSlot lay i ≤ A) (hhi : A < leafBufferSlot lay i + 16) :
    leafBufferPast lay digits i0 (i+1) A := by
  apply leafBufferPast_write lay digits i0 i A hi0 hlo
  unfold leafBufferWriteEnd
  split <;> omega

theorem leafBufferPast_hash (lay : Layer) (digits : List Nat) (i0 i A : Nat)
    (hi0 : i0 ≤ i) (hd : digits.getD i 0 < maxDigit lay i)
    (hlo : leafBufferSlot lay i ≤ A) (hhi : A < leafBufferSlot lay i + 32) :
    leafBufferPast lay digits i0 (i+1) A := by
  exact leafBufferPast_write lay digits i0 i A hi0 hlo (by simpa only [leafBufferWriteEnd,if_pos hd] using hhi)

-- T51: leafBufferPast_not_safe (dead, used only leafBuffer_safe_separate) deleted.

def wchainPads (w : WBytes) (lay : Layer) (i : Nat) : Digest × Digest :=
  (wdig w (chainBlock lay i + pad0Off lay i), wdig w (chainBlock lay i + pad1Off lay i))
def wchainHeaderPad (w : WBytes) (lay : Layer) (i : Nat) : BitVec 64 :=
  (wdig w (chainBlock lay i + 16)).extractLsb' 64 64
def wpath (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest :=
  wdig w (merkleBlock lay leaf j + sibOff (leaf / 2 ^ j % 2))
def wmerklePad (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest := wdig w (merkleBlock lay leaf j + 32)
/-- C2 + C4: the high tweak word of a fold window (witness bytes `[merkleBlock + 24, +8)`; honest 0; C4: the top
windows too). -/
def wmerkleHigh (w : WBytes) (lay : Layer) (leaf j : Nat) : BitVec 64 :=
  (wdig w (merkleBlock lay leaf j + 16)).extractLsb' 64 64
/-- C3: the leaf tweak's high word (witness bytes `[leafBufferBase lay + 24, +8)`; honest 0). -/
def wleafHigh (w : WBytes) (lay : Layer) : BitVec 64 := (wdig w (leafBufferBase lay + 16)).extractLsb' 64 64
/-- Restricted top choice (configuration (1)+(2), e7b head): the choice hint byte is witness byte
`choiceOff = 22312` (= `leafBufferBase 0 + 16`, the low byte of the top leaf tweak's low word, which the verifier
overwrites with the leaf label after reading the hint; absolute 2904 + 22312 = 25216). The hint is bit 7; expand
writes 128 (HIGH) or 0 (LOW). -/
def choiceOff : Nat := 22312
theorem choiceOff_eq : choiceOff = leafBufferBase 0 + 16 := rfl
/-- The raw choice hint byte. -/
def wchoice (w : WBytes) : BitVec 8 := w.extractLsb' (8 * choiceOff) 8
/-- The verifier's top hint: bit 7 of the choice byte (the other 7 bits are ignored). -/
def wtopHigh (w : WBytes) : Bool := (wchoice w).getLsbD 7
/-- The honest choice byte for the hint `high`. -/
def choiceByte (high : Bool) : UInt8 := if high then 128 else 0
theorem choiceByte_bit7 (high : Bool) : (choiceByte high).toBitVec.getLsbD 7 = high := by
  cases high <;> decide
theorem layerBase_values : List.ofFn (fun lay : Layer => layerBase lay) = [8096, 12320, 14968, 17536] := rfl
-- T51: layerBase_tiles (dead in #938) deleted.

theorem layerBase_end : layerBase 3 + 16 * pathSlots 3 + chainArea 3 = leafBufferBase 3 := rfl
/-- Every chain block lies inside its layer's chain area. -/
theorem chainSlot_bound (lay : Layer) (i : Nat) (hi : i < chainCount lay) : chainSlot lay i + 64 ≤ chainArea lay := by
  unfold chainSlot chainArea
  fin_cases lay <;> simp [chainCount] at hi ⊢ <;> (try split_ifs) <;> omega
theorem chainSlot_G {lay : Layer} {i : Nat} (hl : lay ≠ 0) (ho : i % 2 = 1) :
    chainSlot lay i = 104 * (20 - i / 2) + 16 := by
  have : lay.val ≠ 0 := fun h => hl (Fin.ext h)
  simp [chainSlot, this, ho, show i ≠ 0 by omega]
theorem chainSlot_F_pair {lay : Layer} {i : Nat} (hl : lay ≠ 0) (he : i % 2 = 0) (h0 : i ≠ 0) :
    chainSlot lay i = chainSlot lay (i - 1) + 24 := by
  have : lay.val ≠ 0 := fun h => hl (Fin.ext h)
  simp [chainSlot, this, h0, show i - 1 ≠ 0 by omega, show (i - 1) % 2 = 1 by omega,
    show i % 2 ≠ 1 by omega]
  omega
theorem dcOff_end : dcOff + 4 = wsize := rfl
end ClaudeWCT.W9.Machine.Expand.OldW
end

section
namespace ClaudeWCT.W9.Machine.Expand.OldW
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (zeros layerBytes sibOff)
open SphincsSecurity (bytesLE)
/-- Nested FTS (r1-1): the 80 bytes before coordinate 8's region (virtual tree 9; witness trim, was 176). Offset 0
is the L3 block's left slot (L8), 32 its counter, 48 its right slot, 64 the R9 slot. Coordinate 8's supplied top
sibling sits at `topSlot 8 child` (offset 0 or 64). -/
def headerBytes (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
    zeros 8 ++ bytesLE 8 (1 : BitVec 64) ++ bytesLE 4 (w.counters 3) ++ zeros 28 ++
    (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16)
def authByte (child : Nat) (op : WCT9.Opening) (p : Nat) : UInt8 :=
  match (List.finRange 7).find? (fun l => decide (authSibOff child l.val ≤ p ∧ p < authSibOff child l.val + 16)) with
  | some l => (bytesLE 16 (op.path l)).getD (p - authSibOff child l.val) 0
  | none => 0
/-- Nested FTS (r1-1): the fold blocks of levels 0..4 (`[0, 320)` of a region); levels 5 and 6 are placed
elsewhere. -/
def authByte5 (child : Nat) (op : WCT9.Opening) (p : Nat) : UInt8 :=
  match (List.finRange 5).find? (fun l => decide (authSibOff child l.val ≤ p ∧ p < authSibOff child l.val + 16)) with
  | some l => (bytesLE 16 (op.path (Fin.castLE (by decide) l))).getD (p - authSibOff child l.val) 0
  | none => 0
def merkleBytes (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.range 320).map (authByte5 child op)
def chainBytes (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 5).reverse.flatMap fun i => zeros 48 ++ bytesLE 16 (op.values i.succ)
/-- Leaf block: `end0 | header slot (zero) | leaf pad | end1..end5`. -/
def leafBytes (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  bytesLE 16 (op.values 0) ++ zeros 16 ++ pad ++ (List.finRange 5).flatMap fun i => bytesLE 16 (op.values i.succ)
/-- Nested FTS (r1-1): the level-6 fold block `[left | header (zero) | pad | right]` at offset 832 of a region; the
supplied level-5 sibling is on the side opposite the computed value. -/
def topBlockBytes (child : Nat) (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  (if child / 2 ^ 5 % 2 = 1 then bytesLE 16 (op.path 5) else zeros 16) ++ zeros 16 ++ pad ++
    (if child / 2 ^ 5 % 2 = 0 then bytesLE 16 (op.path 5) else zeros 16)
/-- Region of coordinate `k` (896 bytes). `padL`/`padZ` hold coordinate `k - 1`'s supplied top sibling (16 bytes in
one of them, zeros in the other; both zero for `k = 0`). -/
def regionBytes (child : Nat) (op : WCT9.Opening) (padL padZ : List UInt8) : List UInt8 :=
  merkleBytes child op ++ chainBytes op ++ zeros 48 ++ leafBytes op padL ++ zeros 16 ++ topBlockBytes child op padZ
/-- Coordinate `k - 1`'s top sibling in coordinate `k`'s leaf pad (bit 6 of its child set) or level-6 pad. -/
def prevSibL (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : List UInt8 :=
  if k = 0 then zeros 16 else
    if (WCT9.child N (Fin.ofNat 9 (k - 1))).val / 2 ^ 6 % 2 = 1 then
      bytesLE 16 ((sig.openings (Fin.ofNat 9 (k - 1))).path 6) else zeros 16
def prevSibZ (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : List UInt8 :=
  if k = 0 then zeros 16 else
    if (WCT9.child N (Fin.ofNat 9 (k - 1))).val / 2 ^ 6 % 2 = 0 then
      bytesLE 16 ((sig.openings (Fin.ofNat 9 (k - 1))).path 6) else zeros 16
/-- Pairing stage 1: region 0 keeps its first 832 bytes (its level-5 window is removed) and is followed by
coordinate 0's level-5 sibling (`legacySib0`). -/
def wctBytes (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).reverse.flatMap fun k =>
    if k.val = 0 then
      (regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val)).take 832 ++
        bytesLE 16 ((sig.openings k).path 5)
    else regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val)
def lowerSibSlot (lay : Layer) (leaf j : Nat) : Nat := 16 * (lowerPlan lay leaf).getD j 0 + sibOff (leaf / 2 ^ j % 2)
def lowerCtrSlot (lay : Layer) (leaf : Nat) : Nat := 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 32
/-- C2/C3 (FULL): the root window's row-tweak high word (honest LE64 1). -/
def lowerHiSlot (lay : Layer) (leaf : Nat) : Nat := 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 24
def lowerPathByte (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) (p : Nat) : UInt8 :=
  match (List.finRange (height lay)).find?
      (fun j => decide (lowerSibSlot lay leaf j.val ≤ p ∧ p < lowerSibSlot lay leaf j.val + 16)) with
  | some j => (bytesLE 16 (ls.path j)).getD (p - lowerSibSlot lay leaf j.val) 0
  | none => if lowerCtrSlot lay leaf ≤ p ∧ p < lowerCtrSlot lay leaf + 4 then
      (bytesLE 4 ctr).getD (p - lowerCtrSlot lay leaf) 0
    else if lowerHiSlot lay leaf ≤ p ∧ p < lowerHiSlot lay leaf + 8 then
      (bytesLE 8 (1 : BitVec 64)).getD (p - lowerHiSlot lay leaf) 0 else 0
def lowerPathBytes (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  (List.range (16 * pathSlots lay)).map (lowerPathByte lay leaf ls ctr)
/-- C4: offset of the level-`j` top sibling inside the top path area (`16 * topPlanSlot + sibOff`). -/
def topSibSlot (leaf j : Nat) : Nat := 16 * topPlanSlot leaf j + sibOff (leaf / 2 ^ j % 2)
/-- C4: the top path area holds only the 12 siblings (labels are verifier-written, high and Z pads honest 0). Stated
for any layer signature; it is used at `lay = 0`. -/
def topPathByte {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) (p : Nat) : UInt8 :=
  match (List.finRange (height lay)).find?
      (fun j => decide (topSibSlot leaf j.val ≤ p ∧ p < topSibSlot leaf j.val + 16)) with
  | some j => (bytesLE 16 (ls.path j)).getD (p - topSibSlot leaf j.val) 0
  | none => 0
/-- C4: the 768-byte top path area (48 slots). -/
def topPathBytes {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  (List.range (16 * pathSlots lay)).map (topPathByte leaf ls)
/-- Value `i` of a layer signature (0 out of range). -/
def lsValue {lay : Layer} (ls : LayerSignature lay) (i : Nat) : Digest :=
  if h : i < chainCount lay then ls.values ⟨i, h⟩ else 0
/-- Pairing stage 1: pair `p` of a lower chain area (104 bytes): a 16-byte gap, G chain `2p+1`'s block
`[value | 0 ..]` and F chain `2p+2`'s block starting 24 bytes later (value at the pair's offset 88). -/
def pairBytes {lay : Layer} (ls : LayerSignature lay) (p : Nat) : List UInt8 :=
  zeros 16 ++ bytesLE 16 (lsValue ls (2 * p + 1)) ++ zeros 56 ++ bytesLE 16 (lsValue ls (2 * p + 2))
/-- Pairing stage 1: the 2248-byte chain area of a lower layer: pairs 20..0, then chain 0's F block. -/
def lowerChainBytes {lay : Layer} (ls : LayerSignature lay) : List UInt8 :=
  (List.range 21).reverse.flatMap (pairBytes ls) ++ zeros 48 ++ bytesLE 16 (lsValue ls 0)
/-- C4: the top region is the plan-placed path area followed by the top chain blocks (T51: the 3 zero blocks of
#938's chains 51..53, then the 51 blocks of chains 50..0); a lower region is its
plan-placed path area (siblings, counter, row-tweak high word) followed by its chain blocks. -/
def layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then
    topPathBytes (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay) ++
      (zeros 192 ++ (layerBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)).drop (64 * height lay))
  else lowerPathBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
      (w.counters (Fin.ofNat 4 (lay.val - 1))) ++ lowerChainBytes (w.signature.layers lay)
def endpointBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  (List.finRange (chainCount lay)).flatMap fun i => bytesLE 16 ((sig.layers lay).values i)
/-- T51: the top leaf buffer is `end_0 | zeros16 | end_1..end_50 | zeros80` (912 bytes, the final layout's 896 + 16);
#938's was `zeros32 | end_0..end_53 | zeros16`. -/
def leafBufferBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  (endpointBytes sig lay).take 16 ++ zeros 16 ++ (endpointBytes sig lay).drop 16 ++
    zeros (if lay = 0 then 80 else if lay.val = 1 then 16 else 32)
def leafBuffersBytes (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 4).reverse.flatMap (leafBufferBytes sig)
def tailBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter ++ zeros 4
def witList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++ leafBuffersBytes w.signature ++ tailBytes w
def witEnc (N : HashOutput) (w : WCT9.Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))
end ClaudeWCT.W9.Machine.Expand.OldW
end

section
namespace ClaudeWCT.W9.Machine.Expand.OldW
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff zeros
  layerBytes layerBytes_length layerBytes_merkle layerBytes_chain
  window window_append_left window_append_right window_flatMap window_flatMap_const window_full window_zeros
  window_take readDigest_zeros readLE_bytesLE_32 extract_readLE readLE_append)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
theorem zeros_len (n : Nat) : (zeros n).length = n := List.length_replicate ..
theorem ite_slot_length (p : Prop) [Decidable p] (d : Digest) :
    (if p then bytesLE 16 d else zeros 16).length = 16 := by
  split <;> simp [zeros, bytesLE_length]
theorem headerBytes_length (N : HashOutput) (w : WCT9.Witness) : (headerBytes N w).length = 80 := by
  simp only [headerBytes, List.length_append, ite_slot_length, zeros_len, bytesLE_length]
theorem merkleBytes_length (c : Nat) (op : WCT9.Opening) : (merkleBytes c op).length = 320 := by
  simp [merkleBytes]
theorem chainBytes_length (op : WCT9.Opening) : (chainBytes op).length = 320 := by
  simp [chainBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem leafBytes_length' (op : WCT9.Opening) (pad : List UInt8) :
    (leafBytes op pad).length = 112 + pad.length := by
  simp [leafBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
  omega
theorem leafBytes_length (op : WCT9.Opening) (pad : List UInt8) (h : pad.length = 16) :
    (leafBytes op pad).length = 128 := by
  rw [leafBytes_length', h]
theorem topBlockBytes_length (c : Nat) (op : WCT9.Opening) (pad : List UInt8) (h : pad.length = 16) :
    (topBlockBytes c op pad).length = 64 := by
  simp only [topBlockBytes, List.length_append, ite_slot_length, zeros_len, h]
theorem regionBytes_length (c : Nat) (op : WCT9.Opening) (padL padZ : List UInt8) (hL : padL.length = 16)
    (hZ : padZ.length = 16) : (regionBytes c op padL padZ).length = 896 := by
  simp only [regionBytes, List.length_append, merkleBytes_length, chainBytes_length, leafBytes_length _ _ hL,
    topBlockBytes_length _ _ _ hZ, zeros, List.length_replicate]
theorem prevSibL_length (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : (prevSibL N sig k).length = 16 := by
  unfold prevSibL; split
  · simp [zeros]
  · exact ite_slot_length _ _
theorem prevSibZ_length (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : (prevSibZ N sig k).length = 16 := by
  unfold prevSibZ; split
  · simp [zeros]
  · exact ite_slot_length _ _
def regionLen (k : WCT9.Coord) : Nat := if k.val = 0 then 848 else 896
/-- One cell of `wctBytes`: the region of coordinate `k`; pairing stage 1: for `k = 0` its first 832 bytes followed by
coordinate 0's level-5 sibling (`legacySib0`). -/
def regionCell (N : HashOutput) (sig : WCT9.Signature) (k : WCT9.Coord) : List UInt8 :=
  if k.val = 0 then
    (regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val)).take 832 ++
      bytesLE 16 ((sig.openings k).path 5)
  else regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val)
theorem wctBytes_eq (N : HashOutput) (sig : WCT9.Signature) :
    wctBytes N sig = (List.finRange 9).reverse.flatMap (regionCell N sig) := by
  unfold wctBytes regionCell; rfl
theorem regionCell_length (N : HashOutput) (sig : WCT9.Signature) (k : WCT9.Coord) :
    (regionCell N sig k).length = regionLen k := by
  unfold regionCell regionLen
  have := regionBytes_length (WCT9.child N k).val (sig.openings k) _ _ (prevSibL_length N sig k.val)
    (prevSibZ_length N sig k.val)
  split
  · rw [List.length_append, List.length_take, this, bytesLE_length]; rfl
  · exact this
theorem wct_prefix (k : WCT9.Coord) :
    ((((List.finRange 9).reverse).take (8 - k.val)).map regionLen).sum = 896 * (8 - k.val) := by
  fin_cases k <;> decide
theorem wctBytes_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytes N sig).length = 8016 := by
  rw [wctBytes_eq, List.length_flatMap, List.map_congr_left (fun k _ => regionCell_length N sig k)]
  decide
theorem height_pos' (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem lowerPathBytes_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (lowerPathBytes lay leaf ls ctr).length = 16 * pathSlots lay := by
  simp [lowerPathBytes]
theorem top_path_eq : 16 * pathSlots 0 = 64 * height 0 := rfl
theorem topPathBytes_length {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) :
    (topPathBytes leaf ls).length = 16 * pathSlots lay := by
  simp [topPathBytes]
theorem pairBytes_length {lay : Layer} (ls : LayerSignature lay) (p : Nat) : (pairBytes ls p).length = 104 := by
  simp [pairBytes, zeros, bytesLE_length]
theorem lowerChainBytes_length {lay : Layer} (ls : LayerSignature lay) : (lowerChainBytes ls).length = 2248 := by
  simp only [lowerChainBytes, List.length_append, List.length_flatMap, pairBytes_length, zeros_len, bytesLE_length]
  simp
theorem layerRegion_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegion N w lay).length = 16 * pathSlots lay + chainArea lay := by
  unfold layerRegion chainArea; split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    rw [List.length_append, topPathBytes_length, List.length_append, zeros_len, List.length_drop, layerBytes_length]
    decide
  · rw [List.length_append, lowerPathBytes_length, lowerChainBytes_length]
theorem endpointBytes_length (sig : WCT9.Signature) (lay : Layer) :
    (endpointBytes sig lay).length = 16 * chainCount lay := by
  simp [endpointBytes, List.length_flatMap, bytesLE_length, List.sum_replicate, Nat.mul_comm]
def leafBufferLen (lay : Layer) : Nat := if lay = 0 then 912 else if lay.val = 1 then 720 else 736
theorem leafBufferBytes_length (sig : WCT9.Signature) (lay : Layer) :
    (leafBufferBytes sig lay).length = leafBufferLen lay := by
  fin_cases lay <;> simp [leafBufferBytes, leafBufferLen, endpointBytes_length, zeros, chainCount]

theorem leafBuffersBytes_length (sig : WCT9.Signature) : (leafBuffersBytes sig).length = 3104 := by
  simp only [leafBuffersBytes, List.length_flatMap, leafBufferBytes_length]
  decide
theorem tailBytes_length (w : WCT9.Witness) : (tailBytes w).length = 32 := by
  simp [tailBytes, zeros, bytesLE_length]
theorem layers_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegion N w)).length = 12008 := by
  simp only [List.length_flatMap, layerRegion_length]
  decide

theorem witList_length_eq (N : HashOutput) (w : WCT9.Witness) : (witList N w).length = 23240 := by
  unfold witList
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, leafBuffersBytes_length,
    tailBytes_length]
theorem extract_readLE_lt (L : List UInt8) (n : Nat) (hlt : readLE L < 2 ^ (8 * n)) (off k : Nat) :
    (BitVec.ofNat (8 * n) (readLE L)).extractLsb' (8 * off) (8 * k) =
      BitVec.ofNat (8 * k) (readLE ((L.drop off).take k)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.shiftRight_eq_div_pow, show 2 ^ (8 * off) = 256 ^ off by rw [pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop,
    show 2 ^ (8 * k) = 256 ^ k by rw [pow_mul]; norm_num, SigGolfCandidate.T3M.readLE_take]
  rw [Nat.mod_eq_of_lt]
  have := SigGolfCandidate.T3M.readLE_lt ((L.drop off).take k)
  calc readLE ((L.drop off).take k) < 256 ^ ((L.drop off).take k).length := this
    _ ≤ 256 ^ k := Nat.pow_le_pow_right (by norm_num) (by simp)
/-- The serialized list keeps 4 trailing zero bytes after the 32-bit digest counter (the expand
machine still writes whole words); the witness is its first `wsize = 23236` bytes. -/
theorem witList_readLE_lt (N : HashOutput) (w : WCT9.Witness) : readLE (witList N w) < 2 ^ (8 * 23236) := by
  have hsplit : witList N w = ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)) ++
      zeros 4 := by
    simp only [witList, tailBytes, List.append_assoc]
  have hlen : ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)).length =
      23236 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, leafBuffersBytes_length,
      bytesLE_length, zeros, List.length_replicate]
  have hz : readLE (zeros 4) = 0 := by decide
  have h256 : ∀ n : Nat, (256 : Nat) ^ n = 2 ^ (8 * n) := fun n => by rw [pow_mul]; norm_num
  rw [hsplit, readLE_append, hz, Nat.mul_zero, Nat.add_zero, ← h256, ← hlen]
  exact SigGolfCandidate.T3M.readLE_lt _
theorem wdig_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wdig (witEnc N w) off = readDigest (window (witList N w) off 16) := by
  unfold wdig witEnc readDigest window
  exact extract_readLE_lt (witList N w) 23236 (witList_readLE_lt N w) off 16
theorem wle32_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wle32 (witEnc N w) off = BitVec.ofNat 32 (readLE (window (witList N w) off 4)) := by
  unfold wle32 witEnc window
  exact extract_readLE_lt (witList N w) 23236 (witList_readLE_lt N w) off 4
theorem extractLsb'_extractLsb'_add {n : Nat} (x : BitVec n) (a b c : Nat) (h : b + c ≤ 128) :
    (x.extractLsb' a 128).extractLsb' b c = x.extractLsb' (a + b) c := by
  ext k hk
  simp [BitVec.getElem_extractLsb']
  rw [show a + b + k = a + (b + k) by omega]
  simp; omega
/-- The high word of a witness digest is the 64-bit witness word 8 bytes further. -/
theorem wdig_high (x : WBytes) (off : Nat) : (wdig x off).extractLsb' 64 64 = x.extractLsb' (8 * (off + 8)) 64 := by
  unfold wdig
  rw [extractLsb'_extractLsb'_add _ _ _ _ (by omega), show 8 * off + 64 = 8 * (off + 8) by omega]
theorem wword_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    (witEnc N w).extractLsb' (8 * off) 64 = BitVec.ofNat 64 (readLE (window (witList N w) off 8)) := by
  unfold witEnc window
  exact extract_readLE_lt (witList N w) 23236 (witList_readLE_lt N w) off 8
theorem witList_split (N : HashOutput) (w : WCT9.Witness) :
    witList N w = ((headerBytes N w ++ wctBytes N w.signature) ++ (List.finRange 4).flatMap (layerRegion N w)) ++
      (leafBuffersBytes w.signature ++ tailBytes w) := by simp only [witList, List.append_assoc]
section header
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_header (off n : Nat) (h : off + n ≤ 80) :
    window (witList N w) off n = window (headerBytes N w) off n := by
  rw [witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_left _ _ _ _ (by rw [headerBytes_length]; omega)]
/-- The header as a slot, the L3 row tweak block (8 zero bytes, then the high word LE64 1: C2/C3 FULL), the L3
counter, 28 zero bytes and the R9 slot (witness trim: was 108 zero bytes, the R9 slot and 16 zero bytes). -/
theorem headerBytes_eq : headerBytes N w =
    (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
      ((zeros 8 ++ bytesLE 8 (1 : BitVec 64)) ++ (bytesLE 4 (w.counters 3) ++ (zeros 28 ++
        (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16)))) := by
  simp only [headerBytes, List.append_assoc]
theorem win_header_mid (off n : Nat) (h0 : 36 ≤ off) (h : off + n ≤ 64) :
    window (witList N w) off n = zeros n := by
  rw [win_header N w off n (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
    window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]; omega)]
  exact window_zeros _ _ _ (by simp [bytesLE_length, zeros]; omega)
theorem wctr3_witEnc : wle32 (witEnc N w) 32 = w.counters 3 := by
  rw [wle32_witEnc, win_header _ _ _ _ (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 32 - 16 - (zeros 8 ++ bytesLE 8 (1 : BitVec 64)).length = 0 by simp [zeros, bytesLE_length],
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wpad3_witEnc : (witEnc N w).extractLsb' (8 * 36) 96 = 0 := by
  have h := extract_readLE_lt (witList N w) 23236 (witList_readLE_lt N w) 36 12
  unfold witEnc
  rw [show (96 : Nat) = 8 * 12 from rfl, h, show ((witList N w).drop 36).take 12 = window (witList N w) 36 12 from rfl,
    win_header_mid _ _ _ _ le_rfl (by omega)]
  rfl
theorem wright3_witEnc : wdig (witEnc N w) 48 = 0 := by
  rw [wdig_witEnc, win_header_mid _ _ _ _ (by omega) (by omega), readDigest_zeros]
/-- C2/C3 (FULL): the L3 row tweak's high word (witness 24) is LE64 1. -/
theorem win_header_hi : window (witList N w) 24 8 = bytesLE 8 (1 : BitVec 64) := by
  rw [win_header _ _ _ _ (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
    window_append_right _ _ _ _ (by simp [zeros]),
    show 24 - 16 - (zeros 8).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
end header
section tail
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_tail (off n : Nat) (h : off + n ≤ 32) :
    window (witList N w) (23208 + off) n = window (tailBytes w) off n := by
  rw [witList_split, window_append_right _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_right _ _ _ _ (by rw [leafBuffersBytes_length]; omega), leafBuffersBytes_length]
  exact congrArg (fun k : Nat => window (tailBytes w) k n)
    (show 23208 + off - (80 + 8016 + 12008) - 3104 = off by omega)
theorem wrho_witEnc : wrho (witEnc N w) = w.signature.rho := by
  unfold wrho rhoOff
  rw [wdig_witEnc, show (23208 : Nat) = 23208 + 0 from rfl, win_tail _ _ _ _ (by omega)]
  unfold tailBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]), window_full _ _ (bytesLE_length _ _),
    Correctness.readDigest_bytesLE]
theorem tail_counter_window : window (tailBytes w) 24 8 = bytesLE 4 w.digestCounter ++ zeros 4 := by
  rw [show tailBytes w = (bytesLE 16 w.signature.rho ++ zeros 8) ++ (bytesLE 4 w.digestCounter ++ zeros 4) by
    simp only [tailBytes, List.append_assoc]]
  rw [window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 24 - (bytesLE 16 w.signature.rho ++ zeros 8).length = 0 by simp [bytesLE_length, zeros]]
  exact window_full _ _ (by simp [bytesLE_length, zeros])
theorem wdc_witEnc : wdc (witEnc N w) = w.digestCounter := by
  unfold wdc dcOff
  rw [wle32_witEnc, show (23232 : Nat) = 23208 + 24 from rfl, win_tail _ _ _ _ (by omega)]
  have h : window (tailBytes w) 24 4 = window (window (tailBytes w) 24 8) 0 4 := by
    unfold window; rw [List.drop_zero, List.take_take, Nat.min_eq_left (by omega)]
  rw [h, tail_counter_window, window_append_left _ _ _ _ (by simp [bytesLE_length]),
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wdcWord_witEnc : (wdcWord (witEnc N w)).toNat = w.digestCounter.toNat := by
  unfold wdcWord witEnc dcOff
  rw [show (64 : Nat) = 8 * 8 from rfl, extract_readLE_lt (witList N w) 23236 (witList_readLE_lt N w) 23232 8,
    show ((witList N w).drop 23232).take 8 = window (witList N w) (23208 + 24) 8 from rfl,
    win_tail _ _ _ _ (by omega), tail_counter_window, readLE_append, bytesLE_length,
    Correctness.readLE_bytesLE]
  have hz : readLE (zeros 4) = 0 := by decide
  rw [hz, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans w.digestCounter.isLt (by decide))
end tail
theorem layerBase_ge (lay : Layer) : 8096 ≤ layerBase lay := by
  fin_cases lay <;> simp [layerBase]
theorem layerEnd_le (lay : Layer) : layerBase lay + (16 * pathSlots lay + chainArea lay) ≤ 20104 := by
  fin_cases lay <;> decide
theorem layer_prefix (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (((List.finRange 4).take lay.val).map fun l => (layerRegion N w l).length).sum = layerBase lay - 8096 := by
  simp only [layerRegion_length]
  fin_cases lay <;> decide

theorem win_layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (j m : Nat)
    (hjm : j + m ≤ 16 * pathSlots lay + chainArea lay) :
    window (witList N w) (layerBase lay + j) m = window (layerRegion N w lay) j m := by
  have hb := layerBase_ge lay
  have he := layerEnd_le lay
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := window_flatMap (List.finRange 4) (layerRegion N w) lay.val (by simp) j m
    (by rw [hlen, layerRegion_length]; omega)
  rw [layer_prefix N w lay, hlen] at key
  rw [witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_right _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length]
  rw [show layerBase lay + j - (80 + 8016) = (layerBase lay - 8096) + j by omega, key]
/-- Pairing stage 1: the honest 64-byte cell of chain `i` (F: zeros then the value; G: the value then zeros). -/
def chainCell (lay : Layer) (ls : LayerSignature lay) (i : Nat) : List UInt8 :=
  if isG lay i then bytesLE 16 (lsValue ls i) ++ zeros 48 else zeros 48 ++ bytesLE 16 (lsValue ls i)
theorem pairBytes_G {lay : Layer} (ls : LayerSignature lay) (p : Nat) : pairBytes ls p =
    zeros 16 ++ ((bytesLE 16 (lsValue ls (2 * p + 1)) ++ zeros 48) ++ (zeros 8 ++ bytesLE 16 (lsValue ls (2 * p + 2)))) := by
  unfold pairBytes
  rw [show zeros 56 = zeros 48 ++ zeros 8 from List.replicate_add 48 8 0]
  simp only [List.append_assoc]
theorem pairBytes_F {lay : Layer} (ls : LayerSignature lay) (p : Nat) : pairBytes ls p =
    (zeros 16 ++ bytesLE 16 (lsValue ls (2 * p + 1)) ++ zeros 8) ++ (zeros 48 ++ bytesLE 16 (lsValue ls (2 * p + 2))) := by
  unfold pairBytes
  rw [show zeros 56 = zeros 8 ++ zeros 48 from List.replicate_add 8 48 0]
  simp only [List.append_assoc]
theorem pairs_length {lay : Layer} (ls : LayerSignature lay) :
    ((List.range 21).reverse.flatMap (pairBytes ls)).length = 2184 := by
  simp [List.length_flatMap, pairBytes_length]
theorem lowerChain_window {lay : Layer} (hl : lay ≠ 0) (ls : LayerSignature lay) (i : Nat) (hi : i < 43) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (lowerChainBytes ls) (chainSlot lay i + o) 16 = window (chainCell lay ls i) o 16 := by
  have hlv : lay.val ≠ 0 := fun h => hl (Fin.ext h)
  unfold lowerChainBytes
  rw [List.append_assoc]
  by_cases h0 : i = 0
  · subst h0
    have : chainSlot lay 0 = 2184 := by simp [chainSlot, hlv]
    rw [this, window_append_right _ _ _ _ (by rw [pairs_length]; omega), pairs_length,
      show 2184 + o - 2184 = o by omega]
    simp [chainCell, isG_zero]
  · rw [window_append_left _ _ _ _ (by
      rw [pairs_length]; unfold chainSlot; simp only [hlv, if_false, h0]; split <;> omega)]
    by_cases ho1 : i % 2 = 1
    · have hs : chainSlot lay i + o = 104 * (20 - i / 2) + (16 + o) := by
        rw [chainSlot_G hl ho1]; omega
      rw [hs, window_flatMap_const _ _ 104 (pairBytes_length ls) (20 - i / 2) (by simp; omega) _ _ (by omega)]
      have hidx : ((List.range 21).reverse)[20 - i / 2]'(by simp; omega) = i / 2 := by
        simp; omega
      rw [hidx, pairBytes_G, window_append_right _ _ _ _ (by simp [zeros]),
        show 16 + o - (zeros 16).length = o by simp [zeros],
        window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
        show 2 * (i / 2) + 1 = i by omega]
      simp [chainCell, isG_eq_true.mpr ⟨hl, ho1⟩]
    · have hs : chainSlot lay i + o = 104 * (21 - i / 2) + (40 + o) := by
        simp only [chainSlot, hlv, if_false, h0, ho1]; omega
      rw [hs, window_flatMap_const _ _ 104 (pairBytes_length ls) (21 - i / 2) (by simp; omega) _ _ (by omega)]
      have hidx : ((List.range 21).reverse)[21 - i / 2]'(by simp; omega) = i / 2 - 1 := by
        simp; omega
      rw [hidx, pairBytes_F, window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        show 40 + o - (zeros 16 ++ bytesLE 16 (lsValue ls (2 * (i / 2 - 1) + 1)) ++ zeros 8).length = o by
          simp [zeros, bytesLE_length],
        show 2 * (i / 2 - 1) + 2 = i by omega]
      simp [chainCell, isG_eq_false (Or.inr (show i % 2 = 0 by omega))]
theorem win_chain (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (i : Fin (chainCount lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (witList N w) (chainBlock lay i.val + o) 16 =
      window (chainCell lay (w.signature.layers lay) i.val) o 16 := by
  have hi := i.isLt
  have hsb := chainSlot_bound lay i.val hi
  unfold chainBlock
  rw [show layerBase lay + 16 * pathSlots lay + chainSlot lay i.val + o =
      layerBase lay + (16 * pathSlots lay + (chainSlot lay i.val + o)) by omega,
    win_layerRegion _ _ _ _ _ (by omega)]
  unfold layerRegion
  split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    have hc51 : chainCount (0 : Layer) = 51 := rfl
    have hs : chainSlot 0 i.val + o = 192 + (64 * (chainCount 0 - 1 - i.val) + o) := by
      show 64 * (53 - i.val) + o = _; omega
    rw [window_append_right _ _ _ _ (by rw [topPathBytes_length]; omega), topPathBytes_length,
      Nat.add_sub_cancel_left, hs, window_append_right _ _ _ _ (by rw [zeros_len]; omega), zeros_len,
      Nat.add_sub_cancel_left]
    have hc : chainCell 0 (w.signature.layers 0) i.val = zeros 48 ++ bytesLE 16 ((w.signature.layers 0).values i) := by
      simp [chainCell, lsValue, hi]
    rw [hc]
    unfold window
    rw [List.drop_drop, show 64 * height 0 + (64 * (chainCount 0 - 1 - i.val) + o) =
      64 * height 0 + 64 * (chainCount 0 - 1 - i.val) + o by omega]
    exact layerBytes_chain _ _ _ i o ho
  · rename_i h
    have hl : lay ≠ 0 := fun h' => h (by rw [h']; rfl)
    have hi43 : i.val < 43 := by fin_cases lay <;> simp_all [chainCount]
    rw [window_append_right _ _ _ _ (by rw [lowerPathBytes_length]; omega), lowerPathBytes_length,
      Nat.add_sub_cancel_left]
    exact lowerChain_window hl _ i.val hi43 o ho
section t3
variable (N : HashOutput) (w : WCT9.Witness)
theorem wvalue_witEnc (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (witEnc N w) lay i.val = (w.signature.layers lay).values i := by
  have hv : lsValue (w.signature.layers lay) i.val = (w.signature.layers lay).values i := by simp [lsValue, i.isLt]
  unfold wvalue valueOff
  rw [wdig_witEnc, win_chain _ _ _ _ _ (by split <;> omega)]
  unfold chainCell
  split
  · rename_i hG; rw [window_append_left _ _ _ _ (by simp [bytesLE_length]),
      window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE, hv]
  · rename_i hG; rw [window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _),
      Correctness.readDigest_bytesLE, hv]
theorem chainCell_zero_window (lay : Layer) (ls : LayerSignature lay) (i : Nat) (o : Nat)
    (ho : if isG lay i then 16 ≤ o ∧ o + 16 ≤ 64 else o + 16 ≤ 48) :
    window (chainCell lay ls i) o 16 = zeros 16 := by
  unfold chainCell
  split
  · rename_i hG; rw [if_pos hG] at ho
    rw [window_append_right _ _ _ _ (by simp [bytesLE_length]; omega)]
    exact window_zeros _ _ _ (by simp [bytesLE_length]; omega)
  · rename_i hG; rw [if_neg hG] at ho
    rw [window_append_left _ _ _ _ (by simp [zeros]; omega)]
    exact window_zeros _ _ _ ho
theorem wchainPads_witEnc (lay : Layer) (i : Fin (chainCount lay)) : wchainPads (witEnc N w) lay i.val = (0, 0) := by
  unfold wchainPads pad0Off pad1Off
  rw [wdig_witEnc, wdig_witEnc, win_chain _ _ _ _ _ (by split <;> omega), win_chain _ _ _ _ _ (by split <;> omega),
    chainCell_zero_window _ _ _ _ (by split <;> simp_all), chainCell_zero_window _ _ _ _ (by split <;> simp_all),
    readDigest_zeros]
theorem wchainHeaderPad_witEnc (lay : Layer) (i : Fin (chainCount lay)) :
    wchainHeaderPad (witEnc N w) lay i.val = 0 := by
  unfold wchainHeaderPad
  rw [wdig_witEnc, win_chain _ _ _ _ _ (by omega), chainCell_zero_window _ _ _ _ (by split <;> simp_all),
    readDigest_zeros]
  rfl
end t3
theorem lower_sib_bound (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, lowerSibSlot lay leaf j + 16 ≤ 16 * pathSlots lay := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_pad_bound (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, 16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * pathSlots lay := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_sib_disjoint (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      lowerSibSlot lay leaf j + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ lowerSibSlot lay leaf j := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_pad_disjoint (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD j 0 + 32 + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_pad_pad_disjoint (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j' 0 + 32 ∨
        16 * (lowerPlan lay leaf).getD j' 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
/-- C2/C3 (FULL): the high tweak word of a lower fold window (`16 P_j + 24`, levels below the root window) is clear
of every sibling slot. -/
theorem lower_hp_sib (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay - 1, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD j 0 + 32 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 24 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
/-- ... and of the root window's row tweak high word and counter (`16 P_r + 24 .. 16 P_r + 36`); so is its Z pad. -/
theorem lower_hp_root (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay - 1,
      (16 * (lowerPlan lay leaf).getD j 0 + 32 ≤ 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 24 ∨
        16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 36 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 24) ∧
      (16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 24 ∨
        16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 36 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32) := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
/-- The root window's row tweak high word is clear of every sibling slot. -/
theorem lower_hi_sib (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 32 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 24 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lowerSlots_ok (lay : Layer) (hlay : lay.val ≠ 0) :
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, lowerSibSlot lay leaf j + 16 ≤ 16 * pathSlots lay) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, 16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * pathSlots lay) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      lowerSibSlot lay leaf j + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ lowerSibSlot lay leaf j) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD j 0 + 32 + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j' 0 + 32 ∨
        16 * (lowerPlan lay leaf).getD j' 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32) :=
  ⟨lower_sib_bound lay hlay, lower_pad_bound lay hlay, lower_sib_disjoint lay hlay, lower_pad_disjoint lay hlay,
    lower_pad_pad_disjoint lay hlay⟩
theorem window_map_range (f : Nat → UInt8) (n off m : Nat) (h : off + m ≤ n) :
    window ((List.range n).map f) off m = (List.range m).map (fun i => f (off + i)) := by
  unfold window
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
theorem map_range_getD (L : List UInt8) (n : Nat) (h : L.length = n) :
    (List.range n).map (fun i => L.getD i 0) = L := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]
section lowerPath
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay)
  (ls : LayerSignature lay) (ctr : BitVec 32)
include hlay hleaf
theorem lowerPathByte_sib (j : Fin (height lay)) {i : Nat} (hi : i < 16) :
    lowerPathByte lay leaf ls ctr (lowerSibSlot lay leaf j.val + i) = (bytesLE 16 (ls.path j)).getD i 0 := by
  unfold lowerPathByte
  generalize hf : (List.finRange (height lay)).find? _ = r
  rcases r with _ | j'
  · exfalso
    have := List.find?_eq_none.mp hf j (List.mem_finRange j)
    simp only [decide_eq_true_eq, not_and, not_lt] at this
    have := this (by omega)
    omega
  · have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have hjj : j' = j := by
      by_contra hne
      have hd := lower_sib_disjoint lay hlay leaf hleaf j'.val j'.isLt j.val j.isLt (fun e => hne (Fin.ext e))
      omega
    subst hjj
    simp only [Nat.add_sub_cancel_left]
omit hlay hleaf in
theorem lowerPathByte_free {p : Nat} (hp : ∀ j : Fin (height lay), p < lowerSibSlot lay leaf j.val ∨
    lowerSibSlot lay leaf j.val + 16 ≤ p) :
    lowerPathByte lay leaf ls ctr p = if lowerCtrSlot lay leaf ≤ p ∧ p < lowerCtrSlot lay leaf + 4 then
      (bytesLE 4 ctr).getD (p - lowerCtrSlot lay leaf) 0
    else if lowerHiSlot lay leaf ≤ p ∧ p < lowerHiSlot lay leaf + 8 then
      (bytesLE 8 (1 : BitVec 64)).getD (p - lowerHiSlot lay leaf) 0 else 0 := by
  unfold lowerPathByte
  rw [List.find?_eq_none.mpr (fun j _ => by
    have := hp j
    simp only [decide_eq_true_eq, not_and, not_lt]
    omega)]
theorem lowerPath_sib (j : Fin (height lay)) :
    window (lowerPathBytes lay leaf ls ctr) (lowerSibSlot lay leaf j.val) 16 = bytesLE 16 (ls.path j) := by
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (lower_sib_bound lay hlay leaf hleaf j.val j.isLt),
    List.map_congr_left (fun i hi => lowerPathByte_sib hlay hleaf ls ctr j (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem lowerPath_pad {j : Nat} (hj : j + 1 < height lay) :
    window (lowerPathBytes lay leaf ls ctr) (16 * (lowerPlan lay leaf).getD j 0 + 32) 16 = zeros 16 := by
  have hz : ∀ i, i < 16 → lowerPathByte lay leaf ls ctr (16 * (lowerPlan lay leaf).getD j 0 + 32 + i) = 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_pad_disjoint lay hlay leaf hleaf j (by omega) j'.val j'.isLt
      omega)]
    have hd := lower_pad_pad_disjoint lay hlay leaf hleaf j (by omega) (height lay - 1) (by omega) (by omega)
    have hr := (lower_hp_root lay hlay leaf hleaf j (by omega)).2
    unfold lowerCtrSlot lowerHiSlot
    rw [if_neg (by omega), if_neg (by omega)]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by have := lower_pad_bound lay hlay leaf hleaf j (by omega); omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
theorem lowerPath_ctr :
    window (lowerPathBytes lay leaf ls ctr) (lowerCtrSlot lay leaf) 4 = bytesLE 4 ctr := by
  have hb := lower_pad_bound lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
  have hz : ∀ i, i < 4 → lowerPathByte lay leaf ls ctr (lowerCtrSlot lay leaf + i) = (bytesLE 4 ctr).getD i 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_pad_disjoint lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
        j'.val j'.isLt
      unfold lowerCtrSlot; omega), if_pos (by omega), Nat.add_sub_cancel_left]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by unfold lowerCtrSlot; omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem lowerPath_rowPad :
    window (lowerPathBytes lay leaf ls ctr) (lowerCtrSlot lay leaf + 4) 12 = zeros 12 := by
  have hb := lower_pad_bound lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
  have hz : ∀ i, i < 12 → lowerPathByte lay leaf ls ctr (lowerCtrSlot lay leaf + 4 + i) = 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_pad_disjoint lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
        j'.val j'.isLt
      unfold lowerCtrSlot; omega), if_neg (by omega), if_neg (by unfold lowerHiSlot lowerCtrSlot; omega)]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by unfold lowerCtrSlot; omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
/-- C2/C3 (FULL): the root window's row tweak high word holds LE64 1. -/
theorem lowerPath_hi :
    window (lowerPathBytes lay leaf ls ctr) (lowerHiSlot lay leaf) 8 = bytesLE 8 (1 : BitVec 64) := by
  have hb := lower_pad_bound lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
  have hz : ∀ i, i < 8 → lowerPathByte lay leaf ls ctr (lowerHiSlot lay leaf + i) =
      (bytesLE 8 (1 : BitVec 64)).getD i 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_hi_sib lay hlay leaf hleaf j'.val j'.isLt
      unfold lowerHiSlot; omega), if_neg (by unfold lowerHiSlot lowerCtrSlot; omega), if_pos (by omega),
      Nat.add_sub_cancel_left]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by unfold lowerHiSlot; omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
/-- C2 (FULL): the high tweak word of a lower fold window below the root is zero. -/
theorem lowerPath_hp {j : Nat} (hj : j + 1 < height lay) :
    window (lowerPathBytes lay leaf ls ctr) (16 * (lowerPlan lay leaf).getD j 0 + 24) 8 = zeros 8 := by
  have hb := lower_pad_bound lay hlay leaf hleaf j (by omega)
  have hr := (lower_hp_root lay hlay leaf hleaf j (by omega)).1
  have hz : ∀ i, i < 8 → lowerPathByte lay leaf ls ctr (16 * (lowerPlan lay leaf).getD j 0 + 24 + i) = 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_hp_sib lay hlay leaf hleaf j (by omega) j'.val j'.isLt
      omega), if_neg (by unfold lowerCtrSlot; omega), if_neg (by unfold lowerHiSlot; omega)]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
end lowerPath
theorem route_leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ height lay := by
  unfold route; exact Nat.mod_lt _ (by positivity)
theorem win_lowerPath (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (hlay : lay.val ≠ 0) (o m : Nat)
    (h : o + m ≤ 16 * pathSlots lay) :
    window (witList N w) (layerBase lay + o) m =
      window (lowerPathBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
        (w.counters (Fin.ofNat 4 (lay.val - 1)))) o m := by
  rw [win_layerRegion N w lay o m (by omega)]
  unfold layerRegion
  rw [if_neg hlay, window_append_left _ _ _ _ (by rw [lowerPathBytes_length]; exact h)]
/-! ### C4 top path area: plan-placed siblings, honest zero high words and Z pads
Line A (levels 0..5, row `leaf % 64`) lies in bytes `[400, 768)`, line B (levels 6..11, row `leaf / 64 % 64`) in
`[0, 384)`; within a line the sibling slots and the pad areas `[16 P_j + 24, 16 P_j + 48)` are disjoint (kernel
checks over the 64 rows). -/
def topSlotA (r j : Nat) : Nat := (topPlanA.getD r []).getD j 0
def topSlotB (r j : Nat) : Nat := (topPlanB.getD r []).getD j 0
def topSibA (r j : Nat) : Nat := 16 * topSlotA r j + sibOff (r / 2 ^ j % 2)
def topSibB (r j : Nat) : Nat := 16 * topSlotB r j + sibOff (r / 2 ^ j % 2)
theorem topA_range : ∀ r < 64, ∀ j < 6, 400 ≤ 16 * topSlotA r j ∧ 16 * topSlotA r j + 64 ≤ 768 := by decide
theorem topB_range : ∀ r < 64, ∀ j < 6, 16 * topSlotB r j + 64 ≤ 384 := by decide
theorem topA_sib : ∀ r < 64, ∀ j < 6, ∀ j' < 6, j ≠ j' →
    topSibA r j + 16 ≤ topSibA r j' ∨ topSibA r j' + 16 ≤ topSibA r j := by decide
theorem topB_sib : ∀ r < 64, ∀ j < 6, ∀ j' < 6, j ≠ j' →
    topSibB r j + 16 ≤ topSibB r j' ∨ topSibB r j' + 16 ≤ topSibB r j := by decide
theorem topA_pad : ∀ r < 64, ∀ j < 6, ∀ j' < 6,
    16 * topSlotA r j + 48 ≤ topSibA r j' ∨ topSibA r j' + 16 ≤ 16 * topSlotA r j + 24 := by decide
theorem topB_pad : ∀ r < 64, ∀ j < 6, ∀ j' < 6,
    16 * topSlotB r j + 48 ≤ topSibB r j' ∨ topSibB r j' + 16 ≤ 16 * topSlotB r j + 24 := by decide
theorem sibOff_le (b : Nat) : sibOff b ≤ 48 := by unfold sibOff; split <;> omega
theorem topPlanSlot_lo {leaf j : Nat} (hj : j < 6) : topPlanSlot leaf j = topSlotA (leaf % 64) j := by
  unfold topPlanSlot topSlotA; rw [if_pos hj]
theorem topPlanSlot_hi {leaf j : Nat} (hj : 6 ≤ j) : topPlanSlot leaf j = topSlotB (leaf / 64 % 64) (j - 6) := by
  unfold topPlanSlot topSlotB; rw [if_neg (by omega)]
theorem bit_lo (leaf j : Nat) (hj : j < 6) : leaf / 2 ^ j % 2 = leaf % 64 / 2 ^ j % 2 := by
  interval_cases j <;> simp only [Nat.reducePow] <;> omega
theorem bit_hi (leaf j : Nat) (h1 : 6 ≤ j) (h2 : j < 12) : leaf / 2 ^ j % 2 = leaf / 64 % 64 / 2 ^ (j - 6) % 2 := by
  interval_cases j <;> simp only [Nat.reducePow, Nat.reduceSub] <;> omega
theorem topSibSlot_lo {leaf j : Nat} (hj : j < 6) : topSibSlot leaf j = topSibA (leaf % 64) j := by
  unfold topSibSlot topSibA; rw [topPlanSlot_lo hj, bit_lo leaf j hj]
theorem topSibSlot_hi {leaf j : Nat} (h1 : 6 ≤ j) (h2 : j < 12) :
    topSibSlot leaf j = topSibB (leaf / 64 % 64) (j - 6) := by
  unfold topSibSlot topSibB; rw [topPlanSlot_hi h1, bit_hi leaf j h1 h2]
theorem height_top : height (0 : Layer) = 12 := rfl
theorem pathSlots_top : 16 * pathSlots (0 : Layer) = 768 := rfl
/-- Every top window's sibling slot and pad area lie in its line's range. -/
theorem top_ranges (leaf j : Nat) (hj : j < height 0) :
    (j < 6 → 400 ≤ topSibSlot leaf j ∧ topSibSlot leaf j + 16 ≤ 768 ∧
      400 ≤ 16 * topPlanSlot leaf j ∧ 16 * topPlanSlot leaf j + 48 ≤ 768) ∧
    (6 ≤ j → topSibSlot leaf j + 16 ≤ 384 ∧ 16 * topPlanSlot leaf j + 48 ≤ 384) := by
  rw [height_top] at hj
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr' : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  refine ⟨fun h6 => ?_, fun h6 => ?_⟩
  · have := topA_range _ hr j h6
    have := sibOff_le (leaf % 64 / 2 ^ j % 2)
    rw [topSibSlot_lo h6, topPlanSlot_lo h6]
    unfold topSibA
    omega
  · have := topB_range _ hr' (j - 6) (by omega)
    have := sibOff_le (leaf / 64 % 64 / 2 ^ (j - 6) % 2)
    rw [topSibSlot_hi h6 hj, topPlanSlot_hi h6]
    unfold topSibB
    omega
theorem top_sib_bound (leaf j : Nat) (hj : j < height 0) : topSibSlot leaf j + 16 ≤ 768 := by
  have h := top_ranges leaf j hj
  by_cases h6 : j < 6
  · exact (h.1 h6).2.1
  · have := (h.2 (by omega)).1; omega
theorem top_pad_bound (leaf j : Nat) (hj : j < height 0) : 16 * topPlanSlot leaf j + 48 ≤ 768 := by
  have h := top_ranges leaf j hj
  by_cases h6 : j < 6
  · exact (h.1 h6).2.2.2
  · have := (h.2 (by omega)).2; omega
theorem top_sib_disjoint (leaf j j' : Nat) (hj : j < height 0) (hj' : j' < height 0) (hne : j ≠ j') :
    topSibSlot leaf j + 16 ≤ topSibSlot leaf j' ∨ topSibSlot leaf j' + 16 ≤ topSibSlot leaf j := by
  have h := top_ranges leaf j hj
  have h' := top_ranges leaf j' hj'
  rw [height_top] at hj hj'
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr' : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · rw [topSibSlot_lo h6, topSibSlot_lo h6']; exact topA_sib _ hr j h6 j' h6' hne
  · have := (h.1 h6).1; have := (h'.2 (by omega)).1; omega
  · have := (h.2 (by omega)).1; have := (h'.1 h6').1; omega
  · rw [topSibSlot_hi (by omega) hj, topSibSlot_hi (by omega) hj']
    exact topB_sib _ hr' (j - 6) (by omega) (j' - 6) (by omega) (by omega)
theorem top_pad_sib (leaf j j' : Nat) (hj : j < height 0) (hj' : j' < height 0) :
    16 * topPlanSlot leaf j + 48 ≤ topSibSlot leaf j' ∨ topSibSlot leaf j' + 16 ≤ 16 * topPlanSlot leaf j + 24 := by
  have h := top_ranges leaf j hj
  have h' := top_ranges leaf j' hj'
  rw [height_top] at hj hj'
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr' : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · rw [topPlanSlot_lo h6, topSibSlot_lo h6']; exact topA_pad _ hr j h6 j' h6'
  · have := (h.1 h6).2.2.1; have := (h'.2 (by omega)).1; omega
  · have := (h.2 (by omega)).2; have := (h'.1 h6').1; omega
  · rw [topPlanSlot_hi (by omega), topSibSlot_hi (by omega) hj']
    exact topB_pad _ hr' (j - 6) (by omega) (j' - 6) (by omega)
section topPath
variable (leaf : Nat) (ls : LayerSignature 0)
theorem topPathByte_sib (j : Fin (height 0)) {i : Nat} (hi : i < 16) :
    topPathByte leaf ls (topSibSlot leaf j.val + i) = (bytesLE 16 (ls.path j)).getD i 0 := by
  unfold topPathByte
  generalize hf : (List.finRange (height 0)).find? _ = r
  rcases r with _ | j'
  · exfalso
    have := List.find?_eq_none.mp hf j (List.mem_finRange j)
    simp only [decide_eq_true_eq, not_and, not_lt] at this
    have := this (by omega)
    omega
  · have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have hjj : j' = j := by
      by_contra hne
      have hd := top_sib_disjoint leaf j'.val j.val j'.isLt j.isLt (fun e => hne (Fin.ext e))
      omega
    subst hjj
    simp only [Nat.add_sub_cancel_left]
theorem topPathByte_free {p : Nat}
    (hp : ∀ j : Fin (height 0), p < topSibSlot leaf j.val ∨ topSibSlot leaf j.val + 16 ≤ p) :
    topPathByte leaf ls p = 0 := by
  unfold topPathByte
  rw [List.find?_eq_none.mpr (fun j _ => by
    have := hp j
    simp only [decide_eq_true_eq, not_and, not_lt]
    omega)]
theorem topPath_sib (j : Fin (height 0)) :
    window (topPathBytes leaf ls) (topSibSlot leaf j.val) 16 = bytesLE 16 (ls.path j) := by
  unfold topPathBytes
  rw [window_map_range _ _ _ _ (by rw [pathSlots_top]; exact top_sib_bound leaf j.val j.isLt),
    List.map_congr_left (fun i hi => topPathByte_sib leaf ls j (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem topPath_zero {a m : Nat} (hb : a + m ≤ 768)
    (hc : ∀ j : Fin (height 0), a + m ≤ topSibSlot leaf j.val ∨ topSibSlot leaf j.val + 16 ≤ a) :
    window (topPathBytes leaf ls) a m = zeros m := by
  have hz : ∀ i, i < m → topPathByte leaf ls (a + i) = 0 := by
    intro i hi
    exact topPathByte_free leaf ls (fun j => by have := hc j; omega)
  unfold topPathBytes
  rw [window_map_range _ _ _ _ (by rw [pathSlots_top]; exact hb),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
theorem topPath_pad {j : Nat} (hj : j < height 0) :
    window (topPathBytes leaf ls) (16 * topPlanSlot leaf j + 32) 16 = zeros 16 :=
  topPath_zero leaf ls (by have := top_pad_bound leaf j hj; omega)
    (fun j' => by have := top_pad_sib leaf j j'.val hj j'.isLt; omega)
theorem topPath_hp {j : Nat} (hj : j < height 0) :
    window (topPathBytes leaf ls) (16 * topPlanSlot leaf j + 24) 8 = zeros 8 :=
  topPath_zero leaf ls (by have := top_pad_bound leaf j hj; omega)
    (fun j' => by have := top_pad_sib leaf j j'.val hj j'.isLt; omega)
end topPath
theorem win_topPath (N : HashOutput) (w : WCT9.Witness) (o m : Nat) (h : o + m ≤ 768) :
    window (witList N w) (layerBase 0 + o) m =
      window (topPathBytes (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) o m := by
  rw [win_layerRegion N w 0 o m (by rw [pathSlots_top]; omega)]
  unfold layerRegion
  rw [if_pos (show (0 : Layer).val = 0 from rfl),
    window_append_left _ _ _ _ (by rw [topPathBytes_length, pathSlots_top]; exact h)]
theorem win_endpointBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (endpointBytes sig lay) (16 * i.val) 16 = bytesLE 16 ((sig.layers lay).values i) := by
  have h := window_flatMap_const (List.finRange (chainCount lay))
    (fun j => bytesLE 16 ((sig.layers lay).values j)) 16 (fun j => bytesLE_length _ _)
    i.val (by simpa using i.isLt) 0 16 (by omega)
  simpa [endpointBytes, window_full _ _ (bytesLE_length _ _)] using h

theorem win_leafBufferBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (leafBufferBytes sig lay)
      (if i.val = 0 then 0 else 16 + 16 * i.val) 16 =
      bytesLE 16 ((sig.layers lay).values i) := by
  have hi := i.isLt
  have hc : 0 < chainCount lay := by fin_cases lay <;> decide
  unfold leafBufferBytes
  · have htlen : ((endpointBytes sig lay).take 16).length = 16 := by
      rw [List.length_take, endpointBytes_length, Nat.min_eq_left (by omega)]
    by_cases hz : i.val = 0
    · rw [if_pos hz]
      rw [window_append_left _ _ _ _ (by simp [htlen, zeros]),
        window_append_left _ _ _ _ (by simp [htlen, zeros]),
        window_append_left _ _ _ _ (by rw [htlen]), window_take _ _ _ _ (by omega)]
      simpa [hz] using win_endpointBytes sig lay i
    · rw [if_neg hz]
      rw [window_append_left _ _ _ _ (by
        simp only [List.length_append, htlen, zeros, List.length_replicate, List.length_drop, endpointBytes_length]
        omega), window_append_right _ _ _ _ (by
        simp only [List.length_append, htlen, zeros, List.length_replicate]
        omega)]
      simp only [List.length_append, htlen, zeros, List.length_replicate]
      unfold window
      rw [List.drop_drop, show 16 + (16 + 16 * i.val - (16 + 16)) = 16 * i.val by omega]
      exact win_endpointBytes sig lay i

theorem win_leafBuffersBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (leafBuffersBytes sig) (leafBufferSlot lay i.val - 20104) 16 =
      bytesLE 16 ((sig.layers lay).values i) := by
  have hi := i.isLt
  have hidx : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have hget : (List.finRange 4).reverse[3 - lay.val]'hidx = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes sig l).length)).sum = leafBufferBase lay - 20104 := by
    simp only [leafBufferBytes_length]
    fin_cases lay <;> decide
  let off := if i.val = 0 then 0 else 16 + 16 * i.val
  have hb : off + 16 ≤ (leafBufferBytes sig lay).length := by
    rw [leafBufferBytes_length]
    fin_cases lay <;> norm_num [off, leafBufferLen, chainCount] at *
    all_goals (try split_ifs) <;> omega
  have h := window_flatMap (List.finRange 4).reverse (leafBufferBytes sig)
    (3 - lay.val) hidx off 16 (by simpa only [hget] using hb)
  rw [hp, hget] at h
  have hbase : 20104 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hoff : leafBufferSlot lay i.val - 20104 = leafBufferBase lay - 20104 + off := by
    unfold leafBufferSlot
    change leafBufferBase lay + off - 20104 = leafBufferBase lay - 20104 + off
    omega
  rw [hoff]
  exact h.trans (win_leafBufferBytes sig lay i)
theorem win_leafBuffer (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (o n : Nat) (h : o + n ≤ leafBufferLen lay) :
    window (witList N w) (leafBufferBase lay + o) n = window (leafBufferBytes w.signature lay) o n := by
  have hidx : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have hget : (List.finRange 4).reverse[3 - lay.val]'hidx = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes w.signature l).length)).sum = leafBufferBase lay - 20104 := by
    simp only [leafBufferBytes_length]
    fin_cases lay <;> decide
  have hb : o + n ≤ (leafBufferBytes w.signature lay).length := by rw [leafBufferBytes_length]; exact h
  have key := window_flatMap (List.finRange 4).reverse (leafBufferBytes w.signature) (3 - lay.val) hidx o n
    (by simpa only [hget] using hb)
  rw [hp, hget] at key
  have hbase : 20104 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hend : leafBufferBase lay + leafBufferLen lay ≤ 23208 := by fin_cases lay <;> decide
  rw [witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
    omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega),
    show leafBufferBase lay + o - (80 + 8016 + 12008) = leafBufferBase lay - 20104 + o by omega]
  exact key
-- T51: wtopLeafPad / wtopLeafPad_witEnc deleted (the top leaf buffer starts with end_0; no pad; unused).
/-- C3 (FULL): the honest leaf tweak high words are zero. -/
theorem wleafHigh_witEnc (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : wleafHigh (witEnc N w) lay = 0 := by
  unfold wleafHigh
  rw [wdig_witEnc, win_leafBuffer N w lay 16 16 (by fin_cases lay <;> decide)]
  have hz : window (leafBufferBytes w.signature lay) 16 16 = zeros 16 := by
    unfold leafBufferBytes
    · have hc : 1 ≤ chainCount lay := by fin_cases lay <;> decide
      have htlen : ((endpointBytes w.signature lay).take 16).length = 16 := by
        rw [List.length_take, endpointBytes_length]; omega
      rw [window_append_left _ _ _ _ (by
          simp only [List.length_append, htlen, zeros, List.length_replicate, List.length_drop, endpointBytes_length]
          omega),
        window_append_left _ _ _ _ (by simp only [List.length_append, htlen, zeros, List.length_replicate]; omega),
        window_append_right _ _ _ _ (by rw [htlen]), htlen, window_zeros _ _ _ (by omega)]
  rw [hz, readDigest_zeros]
  decide
theorem wbuffer_witEnc (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (i : Fin (chainCount lay)) :
    wdig (witEnc N w) (leafBufferSlot lay i.val) = (w.signature.layers lay).values i := by
  have hb := leafBufferSlot_bounds lay i.val i.isLt
  rw [wdig_witEnc, witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
    omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega)]
  rw [show 80 + 8016 + 12008 = 20104 by decide,
    win_leafBuffersBytes, Correctness.readDigest_bytesLE]
end ClaudeWCT.W9.Machine.Expand.OldW
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ChoiceWord ====
section

/-! # The choice hint word of the paired witness (configuration e7b, expand readout)

The 8-byte witness word at byte `choiceOff = 21104 = 8 * 2638` is the legacy word with its low byte replaced by
`choiceByte witness.topHigh`; the expand `end` routine produces exactly this with `sb` of the choice flag. -/

namespace ClaudeWCT.W9.T3M.PairedReadout
open RiscvZkvm.Rv64 SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem choiceByte_extract (output : HashOutput) (witness : SharedForest.Witness) :
    (Paired.witEnc output witness).extractLsb' (8 * choiceOff) (8 * 1) = (choiceByte witness.topHigh).toBitVec := by
  have hlen : choiceOff < (Paired.witListBase output witness).length := by
    rw [witListBase_length]; decide
  unfold Paired.witEnc
  rw [extract_readLE _ 22012 choiceOff 1 (by decide)]
  have hd : ((Paired.witList output witness).drop choiceOff).take 1 = [choiceByte witness.topHigh] := by
    unfold Paired.witList
    rw [List.drop_set, if_neg (lt_irrefl _), Nat.sub_self]
    obtain ⟨y, ys, hy⟩ : ∃ y ys, (Paired.witListBase output witness).drop choiceOff = y :: ys := by
      cases h : (Paired.witListBase output witness).drop choiceOff with
      | nil => have := congrArg List.length h; simp at this; omega
      | cons y ys => exact ⟨y, ys, rfl⟩
    rw [hy]; rfl
  rw [hd]
  cases witness.topHigh <;> decide

theorem choiceWord_witEnc (output : HashOutput) (witness : SharedForest.Witness) :
    (Paired.witEnc output witness).extractLsb' (8*(8*2638)) 64 =
      replaceByte ((ClaudeWCT.W9.T3M.witEnc output (Paired.mainWitness witness)).extractLsb' (8*(8*2638)) 64) 0
        (choiceByte witness.topHigh).toBitVec := by
  have hb : (baseEnc output witness).extractLsb' (8*(8*2638)) 64 =
      (ClaudeWCT.W9.T3M.witEnc output (Paired.mainWitness witness)).extractLsb' (8*(8*2638)) 64 :=
    word_prefixEnc _ (Paired.forestBytes_length output witness) _ _ (8*2638) (by norm_num)
  have hc := choiceByte_extract output witness
  rw [← hb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hco : choiceOff = 8*2638 := rfl
  simp only [replaceByte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    Nat.zero_mul, Nat.sub_zero, show ¬ (i < 0) by omega, decide_false, Bool.not_false]
  by_cases h8 : i < 8
  · have e := congrArg (fun x : BitVec 8 => x.getLsbD i) hc
    simp only [BitVec.getLsbD_extractLsb', show i < 8*1 by omega, decide_true, Bool.true_and, hco] at e
    have h2 : (255 : Nat).testBit i = true := by
      have : (255 : Nat) = 2 ^ 8 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; simp; omega
    simp [BitVec.getLsbD_ofNat, h2, h8, e]
    all_goals (intros; omega)
  · have h2 : (255 : Nat).testBit i = false := by
      have : (255 : Nat) = 2 ^ 8 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; simpa using h8
    rw [witEnc_getLsbD _ _ _ (by rw [hco]; omega)]
    simp [BitVec.getLsbD_ofNat, h2, BitVec.getLsbD_of_ge _ i (by omega : 8 ≤ i)]
end ClaudeWCT.W9.T3M.PairedReadout
end
