import SigGolfCandidate.ClaudeWCT_WCT9_Core
import SigGolfCandidate.T3M_Witness_Queries

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff chainP nodeHashP PubGood allQ_bind allQ_mapM allQ_foldlM pubGood_chainP
  pubGood_leafHash pubGood_nodeHashP)
open SigGolfCandidate.T3M.SecurityExtraction (hashPath merkleInput foldlM_finRange_eq_hashPath)
/-- Nested FTS (r1-1): the witness starts at absolute 1216. C2: W 24860 -> 24924 (ends at 26140; message at 26144).
Witness trim: the witness starts at absolute 1312 (W 24924 -> 24828, same end 26140); old offsets >= 176 drop by 96.
Pairing stage 1: the lower chain blocks are paired (G chain + F chain in 104 bytes), the dead FTS region-0 top block
(64 B) and the layer-1 leaf-buffer tail (16 B) are removed: W 24828 -> 23236.
Witness stack (charge 86): top chains paired (27 pairs), FTS chains paired (G1/F2, G3/F4), stride 848, the three
leaf-buffer tails removed, 42-slot top window: W 23236 -> 22012, the witness starts at absolute 4128. -/
def wsize : Nat := 22012
abbrev WBytes := BitVec (8 * 22012)
def wbyte (w : WBytes) (i : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * i) 8)
def wdig (w : WBytes) (off : Nat) : Digest := w.extractLsb' (8 * off) 128
def wle32 (w : WBytes) (off : Nat) : BitVec 32 := w.extractLsb' (8 * off) 32
def rhoOff : Nat := 21984
def dcOff : Nat := 22008
def layerBase (lay : Layer) : Nat := (![7664, 11144, 13792, 16360] : Layer → Nat) lay
def pathSlots (lay : Layer) : Nat := (![42, 25, 20, 20] : Layer → Nat) lay
def lowerPlanL1 : List (List Nat) :=[[1,4,7,10,13,21,16],[0,4,7,10,13,21,16],[1,8,12,15,18,21,4],[0,8,12,15,18,21,4],[1,4,11,15,18,21,7],[0,4,11,15,18,21,7],[1,11,8,15,18,21,4],[0,11,8,15,18,21,4],[1,4,7,14,18,21,10],[0,4,7,14,18,21,10],[1,11,15,8,18,21,4],[0,11,15,8,18,21,4],[1,4,14,11,18,21,7],[0,4,14,11,18,21,7],[1,14,11,8,18,21,4],[0,14,11,8,18,21,4],[1,4,7,10,17,21,13],[0,4,7,10,17,21,13],[1,11,15,18,8,21,4],[0,11,15,18,8,21,4],[1,4,14,18,11,21,7],[0,4,14,18,11,21,7],[1,14,11,18,8,21,4],[0,14,11,18,8,21,4],[1,4,7,17,14,21,10],[0,4,7,17,14,21,10],[1,14,18,11,8,21,4],[0,14,18,11,8,21,4],[1,4,17,14,11,21,7],[0,4,17,14,11,21,7],[1,17,14,11,8,21,4],[0,17,14,11,8,21,4],[1,4,7,10,13,20,16],[0,4,7,10,13,20,16],[1,11,15,18,21,8,4],[0,11,15,18,21,8,4],[1,4,14,18,21,11,7],[0,4,14,18,21,11,7],[1,14,11,18,21,8,4],[0,14,11,18,21,8,4],[1,4,7,17,21,14,10],[0,4,7,17,21,14,10],[1,14,18,11,21,8,4],[0,14,18,11,21,8,4],[1,4,17,14,21,11,7],[0,4,17,14,21,11,7],[1,17,14,11,21,8,4],[0,17,14,11,21,8,4],[1,4,7,10,20,17,13],[0,4,7,10,20,17,13],[1,14,18,21,11,8,4],[0,14,18,21,11,8,4],[1,4,17,21,14,11,7],[0,4,17,21,14,11,7],[1,17,14,21,11,8,4],[0,17,14,21,11,8,4],[1,4,7,20,17,14,10],[0,4,7,20,17,14,10],[1,17,21,14,11,8,4],[0,17,21,14,11,8,4],[1,4,20,17,14,11,7],[0,4,20,17,14,11,7],[1,20,17,14,11,8,4],[0,20,17,14,11,8,4],[1,4,7,10,18,21,14],[0,4,7,10,18,21,14],[1,8,12,15,18,21,5],[0,8,12,15,18,21,5],[1,4,11,15,18,21,8],[0,4,11,15,18,21,8],[1,11,8,15,18,21,5],[0,11,8,15,18,21,5],[1,4,7,14,18,21,11],[0,4,7,14,18,21,11],[1,11,15,8,18,21,5],[0,11,15,8,18,21,5],[1,4,14,11,18,21,8],[0,4,14,11,18,21,8],[1,14,11,8,18,21,5],[0,14,11,8,18,21,5],[1,4,7,10,17,21,14],[0,4,7,10,17,21,14],[1,11,15,18,8,21,5],[0,11,15,18,8,21,5],[1,4,14,18,11,21,8],[0,4,14,18,11,21,8],[1,14,11,18,8,21,5],[0,14,11,18,8,21,5],[1,4,7,17,14,21,11],[0,4,7,17,14,21,11],[1,14,18,11,8,21,5],[0,14,18,11,8,21,5],[1,4,17,14,11,21,8],[0,4,17,14,11,21,8],[1,17,14,11,8,21,5],[0,17,14,11,8,21,5],[1,4,7,10,21,17,14],[0,4,7,10,21,17,14],[1,11,15,18,21,8,5],[0,11,15,18,21,8,5],[1,4,14,18,21,11,8],[0,4,14,18,21,11,8],[1,14,11,18,21,8,5],[0,14,11,18,21,8,5],[1,4,7,17,21,14,11],[0,4,7,17,21,14,11],[1,14,18,11,21,8,5],[0,14,18,11,21,8,5],[1,4,17,14,21,11,8],[0,4,17,14,21,11,8],[1,17,14,11,21,8,5],[0,17,14,11,21,8,5],[1,4,7,10,20,17,14],[0,4,7,10,20,17,14],[1,14,18,21,11,8,5],[0,14,18,21,11,8,5],[1,4,17,21,14,11,8],[0,4,17,21,14,11,8],[1,17,14,21,11,8,5],[0,17,14,21,11,8,5],[1,4,7,20,17,14,11],[0,4,7,20,17,14,11],[1,17,21,14,11,8,5],[0,17,21,14,11,8,5],[1,4,20,17,14,11,8],[0,4,20,17,14,11,8],[1,20,17,14,11,8,5],[0,20,17,14,11,8,5]]
def lowerPlanL32 : List (List Nat) :=[[1,4,7,10,13,16],[0,4,7,10,13,16],[4,0,7,10,13,16],[3,0,7,10,13,16],[4,7,0,10,13,16],[3,7,0,10,13,16],[7,3,0,10,13,16],[6,3,0,10,13,16],[4,7,10,0,13,16],[3,7,10,0,13,16],[7,3,10,0,13,16],[6,3,10,0,13,16],[7,10,3,0,13,16],[6,10,3,0,13,16],[10,6,3,0,13,16],[9,6,3,0,13,16],[4,7,10,13,0,16],[3,7,10,13,0,16],[7,3,10,13,0,16],[6,3,10,13,0,16],[7,10,3,13,0,16],[6,10,3,13,0,16],[10,6,3,13,0,16],[9,6,3,13,0,16],[7,10,13,3,0,16],[6,10,13,3,0,16],[10,6,13,3,0,16],[9,6,13,3,0,16],[10,13,6,3,0,16],[9,13,6,3,0,16],[13,9,6,3,0,16],[12,9,6,3,0,16],[4,7,10,13,16,0],[3,7,10,13,16,0],[7,3,10,13,16,0],[6,3,10,13,16,0],[7,10,3,13,16,0],[6,10,3,13,16,0],[10,6,3,13,16,0],[9,6,3,13,16,0],[7,10,13,3,16,0],[6,10,13,3,16,0],[10,6,13,3,16,0],[9,6,13,3,16,0],[10,13,6,3,16,0],[9,13,6,3,16,0],[13,9,6,3,16,0],[12,9,6,3,16,0],[7,10,13,16,3,0],[6,10,13,16,3,0],[10,6,13,16,3,0],[9,6,13,16,3,0],[10,13,6,16,3,0],[9,13,6,16,3,0],[13,9,6,16,3,0],[12,9,6,16,3,0],[10,13,16,6,3,0],[9,13,16,6,3,0],[13,9,16,6,3,0],[12,9,16,6,3,0],[13,16,9,6,3,0],[12,16,9,6,3,0],[16,12,9,6,3,0],[15,12,9,6,3,0]]
def lowerPlan (lay : Layer) (leaf : Nat) : List Nat :=
  if lay.val = 1 then lowerPlanL1.getD (leaf % 128) [] else lowerPlanL32.getD (leaf % 64) []
/-! ### C4 top window plan (witness stack: the a08a5843/b12e3be7 42-slot plan; two lines; rows from c4-top/topplan_lean.txt, generated from logs/plan_c4.json)
Slot `s` is witness offset `layerBase 0 + 16 * s`. Line A (`topPlanA`, row `leaf % 64`) places the windows of levels
0..5, line B (`topPlanB`, row `leaf / 64 % 64`) those of levels 6..11. A window at slot `A` holds the left input at
`A`, the label word at `A + 1` (bytes 0..8 written by the verifier, bytes 8..16 the witness high pad), the Z pad at
`A + 2` and the right input at `A + 3`; the sibling sits at `A + 3` when the node bit is 0 and at `A` when it is 1
(`sibOff`). `topRootSlot k` is the slot of the root answer read by the compare of upper copy `k` (machine only). -/
def topPlanA : List (List Nat) :=[[26,29,32,35,38,21],[25,29,32,35,38,21],[29,25,32,35,38,21],[28,25,32,35,38,21],[29,32,25,35,38,21],[28,32,25,35,38,21],[32,28,25,35,38,21],[31,28,25,35,38,21],[29,32,35,25,38,21],[28,32,35,25,38,21],[32,28,35,25,38,21],[31,28,35,25,38,21],[32,35,28,25,38,21],[31,35,28,25,38,21],[35,31,28,25,38,21],[34,31,28,25,38,21],[29,32,35,38,25,21],[28,32,35,38,25,21],[32,28,35,38,25,21],[31,28,35,38,25,21],[32,35,28,38,25,21],[31,35,28,38,25,21],[35,31,28,38,25,21],[34,31,28,38,25,21],[32,35,38,28,25,21],[31,35,38,28,25,21],[35,31,38,28,25,21],[34,31,38,28,25,21],[35,38,31,28,25,21],[34,38,31,28,25,21],[38,34,31,28,25,21],[37,34,31,28,25,21],[25,28,31,34,37,21],[24,28,31,34,37,21],[28,24,31,34,37,21],[27,24,31,34,37,21],[28,31,24,34,37,21],[27,31,24,34,37,21],[31,27,24,34,37,21],[30,27,24,34,37,21],[28,31,34,24,37,21],[27,31,34,24,37,21],[31,27,34,24,37,21],[30,27,34,24,37,21],[31,34,27,24,37,21],[30,34,27,24,37,21],[34,30,27,24,37,21],[33,30,27,24,37,21],[28,31,34,37,24,21],[27,31,34,37,24,21],[31,27,34,37,24,21],[30,27,34,37,24,21],[31,34,27,37,24,21],[30,34,27,37,24,21],[34,30,27,37,24,21],[33,30,27,37,24,21],[31,34,37,27,24,21],[30,34,37,27,24,21],[34,30,37,27,24,21],[33,30,37,27,24,21],[34,37,30,27,24,21],[33,37,30,27,24,21],[37,33,30,27,24,21],[36,33,30,27,24,21]]
def topPlanB : List (List Nat) :=[[0,3,6,9,12,15],[0,4,7,10,13,16],[4,0,7,10,13,16],[3,0,7,10,13,16],[4,7,0,10,13,16],[3,7,0,10,13,16],[7,3,0,10,13,16],[6,3,0,10,13,16],[4,7,10,0,13,16],[3,7,10,0,13,16],[7,3,10,0,13,16],[6,3,10,0,13,16],[7,10,3,0,13,16],[6,10,3,0,13,16],[10,6,3,0,13,16],[9,6,3,0,13,16],[4,7,10,13,0,16],[3,7,10,13,0,16],[7,3,10,13,0,16],[6,3,10,13,0,16],[7,10,3,13,0,16],[6,10,3,13,0,16],[10,6,3,13,0,16],[9,6,3,13,0,16],[7,10,13,3,0,16],[6,10,13,3,0,16],[10,6,13,3,0,16],[9,6,13,3,0,16],[10,13,6,3,0,16],[9,13,6,3,0,16],[13,9,6,3,0,16],[12,9,6,3,0,16],[4,7,10,13,16,0],[3,7,10,13,16,0],[7,3,10,13,16,0],[6,3,10,13,16,0],[7,10,3,13,16,0],[6,10,3,13,16,0],[10,6,3,13,16,0],[9,6,3,13,16,0],[7,10,13,3,16,0],[6,10,13,3,16,0],[10,6,13,3,16,0],[9,6,13,3,16,0],[10,13,6,3,16,0],[9,13,6,3,16,0],[13,9,6,3,16,0],[12,9,6,3,16,0],[7,10,13,16,3,0],[6,10,13,16,3,0],[10,6,13,16,3,0],[9,6,13,16,3,0],[10,13,6,16,3,0],[9,13,6,16,3,0],[13,9,6,16,3,0],[12,9,6,16,3,0],[10,13,16,6,3,0],[9,13,16,6,3,0],[13,9,16,6,3,0],[12,9,16,6,3,0],[13,16,9,6,3,0],[12,16,9,6,3,0],[16,12,9,6,3,0],[15,12,9,6,3,0]]
def topRootSlot : List Nat :=[14,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3]
/-- C4: slot of the level-`j` top window of leaf `leaf`. -/
def topPlanSlot (leaf j : Nat) : Nat :=
  if j < 6 then (topPlanA.getD (leaf % 64) []).getD j 0 else (topPlanB.getD (leaf / 64 % 64) []).getD (j - 6) 0
def merkleBlock (lay : Layer) (leaf j : Nat) : Nat :=
  layerBase lay + (if lay.val = 0 then 16 * topPlanSlot leaf j else 16 * (lowerPlan lay leaf).getD j 0)
/-- Pairing stage 1: offset of chain `i`'s block inside the chain area of layer `lay`. Lower layers: chain 0's F block
is highest (offset 2184); pair `p` (G chain `2p+1`, F chain `2p+2`) occupies `[104 (20 - p), +104)`: a 16-byte junk
gap, the G block at `+16` and the F block at `+40` (overlapping the G block's zero tail). Witness stack: top pair `p`
(G chain `2p`, F chain `2p+1`, `p < 27`) occupies `[104 (26 - p), +104)` the same way (chain 0 highest). -/
def chainSlot (lay : Layer) (i : Nat) : Nat :=
  if lay.val = 0 then (if i % 2 = 0 then 104 * (26 - i / 2) + 16 else 104 * (26 - i / 2) + 40)
  else if i = 0 then 2184 else if i % 2 = 1 then 104 * (20 - i / 2) + 16 else 104 * (21 - i / 2) + 40
/-- Bytes of the chain area of layer `lay`. -/
def chainArea (lay : Layer) : Nat := if lay.val = 0 then 2808 else 2248
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
def valueOff (lay : Layer) (i : Nat) : Nat := if WCT9.isG lay i then 0 else 48
/-- Offsets of the two zero pads inside a chain block: 0 and 32 (F) or 32 and 48 (G). -/
def pad0Off (lay : Layer) (i : Nat) : Nat := if WCT9.isG lay i then 32 else 0
def pad1Off (lay : Layer) (i : Nat) : Nat := if WCT9.isG lay i then 48 else 32
def wvalue (w : WBytes) (lay : Layer) (i : Nat) : Digest := wdig w (chainBlock lay i + valueOff lay i)
/-- Offsets in expanded witness memory, before its 2048-byte machine base. -/
def leafBufferBase (lay : Layer) : Nat := (![21088,20368,19648,18928] : Layer → Nat) lay

/-- Leaf-buffer slot of chain `i`: every layer (T51: the top included, "endpad") stores `end_0 | tweak | end_1 ..`, so
end `i ≥ 1` sits at `base + 16 + 16 i` (top: end_0 at 21088, tweak at 21104, end_i at 21120 + 16 (i - 1)). -/
def leafBufferSlot (lay : Layer) (i : Nat) : Nat :=
  leafBufferBase lay + (if lay = 0 then (if i = 0 then 0 else 16+16*i) else if i = 0 then 0 else 16+16*i)

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

theorem leafBufferSlot_head_gap (lay : Layer) (h : lay ≠ 0) :
    leafBufferSlot lay 0 + 32 ≤ leafBufferSlot lay 1 := by
  simp [leafBufferSlot,h]

theorem leafBufferBase_bounds (lay : Layer) :
    18928 ≤ leafBufferBase lay ∧ leafBufferBase lay ≤ 21088 ∧ leafBufferBase lay % 8 = 0 := by
  fin_cases lay <;> decide +kernel

theorem leafBufferSlot_bounds (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    18928 ≤ leafBufferSlot lay i ∧ leafBufferSlot lay i + 16 ≤ 21984 ∧
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

theorem leafBuffer_safe_separate (lay : Layer) (digits : List Nat) (i j : Nat)
    (hsafe : WCT9.safeZeroCopy lay digits i) (hji : j < i) :
    leafBufferWriteEnd lay digits j ≤ leafBufferSlot lay i := by
  by_cases hj : j + 2 ≤ i
  · have := leafBufferSlot_gap_two lay j i hj
    unfold leafBufferWriteEnd
    split <;> omega
  · have hpred : i-1=j := by omega
    obtain ⟨-, hfirst | hsecond | hprevious⟩ := hsafe
    · omega
    · obtain ⟨hlay,hi⟩ := hsecond
      have hj0 : j=0 := by omega
      have hgap := leafBufferSlot_head_gap lay hlay
      rw [hi, hj0]
      unfold leafBufferWriteEnd
      split <;> omega
    · have hjmax : digits.getD j 0 = maxDigit lay j := by
        simpa only [hpred] using hprevious.2.2.2
      have := leafBufferSlot_gap lay j i hji
      unfold leafBufferWriteEnd
      rw [if_neg (by omega : ¬digits.getD j 0 < maxDigit lay j)]
      exact this

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

theorem leafBufferPast_not_safe (lay : Layer) (digits : List Nat) (i0 i k A : Nat)
    (hik : i ≤ k) (hsafe : WCT9.safeZeroCopy lay digits k) (hA : leafBufferSlot lay k ≤ A) :
    ¬leafBufferPast lay digits i0 i A := by
  rintro ⟨j,hj0,hji,hlo,hhi⟩
  have := leafBuffer_safe_separate lay digits k j hsafe (lt_of_lt_of_le hji hik)
  omega


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
/-- C3: the top leaf pad, the first 16 bytes of the top leaf buffer (honest 0). -/
def wtopLeafPad (w : WBytes) : Digest := wdig w (leafBufferBase 0)
/-- C3: the leaf tweak's high word (witness bytes `[leafBufferBase lay + 24, +8)`; honest 0). -/
def wleafHigh (w : WBytes) (lay : Layer) : BitVec 64 := (wdig w (leafBufferBase lay + 16)).extractLsb' 64 64
/-- Restricted top choice (configuration (1)+(2), e7b head): the choice hint byte is witness byte
`choiceOff = 21104` (= `leafBufferBase 0 + 16`, the low byte of the top leaf tweak's low word, which the verifier
overwrites with the leaf label after reading the hint; absolute 4128 + 21104 = 25232). The hint is bit 7; expand
writes 128 (HIGH) or 0 (LOW). -/
def choiceOff : Nat := 21104
theorem choiceOff_eq : choiceOff = leafBufferBase 0 + 16 := rfl
/-- The raw choice hint byte. -/
def wchoice (w : WBytes) : BitVec 8 := w.extractLsb' (8 * choiceOff) 8
/-- The verifier's top hint: bit 7 of the choice byte (the other 7 bits are ignored). -/
def wtopHigh (w : WBytes) : Bool := (wchoice w).getLsbD 7
/-- The honest choice byte for the hint `high`. -/
def choiceByte (high : Bool) : UInt8 := if high then 128 else 0
theorem choiceByte_bit7 (high : Bool) : (choiceByte high).toBitVec.getLsbD 7 = high := by
  cases high <;> decide
/-- Pairing stage 1: the padded step input in either format (header in bytes 16..32 in both): `chainInputP` (F) or
`value | header | pad0 | pad1` (G). -/
def chainInputPW (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64)
    (value : Digest) : HashInput :=
  if WCT9.isG lay i then
    SphincsSecurity.bytesLE 16 value ++
      SphincsSecurity.bytesLE 16 (SigGolfCandidate.T3M.chainHeaderP lay tree leaf i step headerPad) ++
      SphincsSecurity.bytesLE 16 pad0 ++ SphincsSecurity.bytesLE 16 pad1
  else SigGolfCandidate.T3M.chainInputP lay tree leaf i step pad0 pad1 headerPad value
theorem chainInputPW_F {lay : Layer} {i : Nat} (hG : WCT9.isG lay i = false) (tree leaf step : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value : Digest) :
    chainInputPW lay tree leaf i step pad0 pad1 headerPad value =
      SigGolfCandidate.T3M.chainInputP lay tree leaf i step pad0 pad1 headerPad value := by
  simp [chainInputPW, hG]
theorem chainInputPW_length (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64)
    (value : Digest) : (chainInputPW lay tree leaf i step pad0 pad1 headerPad value).length = 64 := by
  unfold chainInputPW SigGolfCandidate.T3M.chainInputP
  split <;> simp [SphincsSecurity.bytesLE_length]
open SigGolfCandidate.T3M.SecurityInputs (block4 pad64_block4 block4_injective) in
theorem chainInputPW_eq_block4 (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64)
    (value : Digest) : chainInputPW lay tree leaf i step pad0 pad1 headerPad value =
      if WCT9.isG lay i then block4 value (SigGolfCandidate.T3M.chainHeaderP lay tree leaf i step headerPad) pad0 pad1
      else block4 pad0 (SigGolfCandidate.T3M.chainHeaderP lay tree leaf i step headerPad) pad1 value := by
  unfold chainInputPW; split <;> rfl
open SigGolfCandidate.T3M.SecurityInputs (block4 pad64_block4 block4_injective) in
@[simp] theorem pad64_chainInputPW (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) :
    pad64 (chainInputPW lay tree leaf i step pad0 pad1 headerPad value) =
      chainInputPW lay tree leaf i step pad0 pad1 headerPad value := by
  rw [chainInputPW_eq_block4]; split <;> exact pad64_block4 _ _ _ _
/-- Same-position injectivity of the padded step input (either format). -/
theorem chainInputPW_fields {lay : Layer} {tree leaf i step : Nat}
    {pad0 pad1 value pad0' pad1' value' : Digest} {headerPad headerPad' : BitVec 64}
    (h : chainInputPW lay tree leaf i step pad0 pad1 headerPad value =
      chainInputPW lay tree leaf i step pad0' pad1' headerPad' value') :
    pad0 = pad0' ∧ headerPad = headerPad' ∧ pad1 = pad1' ∧ value = value' := by
  rw [chainInputPW_eq_block4, chainInputPW_eq_block4] at h
  split at h
  · obtain ⟨hv, hh, h0, h1⟩ := SigGolfCandidate.T3M.SecurityInputs.block4_injective h
    have := congrArg (fun x : Digest => x.extractLsb' 64 64) hh
    simp only [SigGolfCandidate.T3M.chainHeaderP, BitVec.extractLsb'_append_eq_left] at this
    exact ⟨h0, this, h1, hv⟩
  · obtain ⟨h0, hh, h1, hv⟩ := SigGolfCandidate.T3M.SecurityInputs.block4_injective h
    have := congrArg (fun x : Digest => x.extractLsb' 64 64) hh
    simp only [SigGolfCandidate.T3M.chainHeaderP, BitVec.extractLsb'_append_eq_left] at this
    exact ⟨h0, this, h1, hv⟩
/-- The header block (bytes 16..32) of either format. -/
theorem chainInputPW_header (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64)
    (value : Digest) : ((chainInputPW lay tree leaf i step pad0 pad1 headerPad value).drop 16).take 16 =
      SphincsSecurity.bytesLE 16 (SigGolfCandidate.T3M.chainHeaderP lay tree leaf i step headerPad) := by
  unfold chainInputPW SigGolfCandidate.T3M.chainInputP
  split <;> simp [List.append_assoc, SphincsSecurity.bytesLE_length]
/-- Zero pads give the honest step input of the current scheme. -/
theorem chainInputW_eq_zero (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    WCT9.chainInputW lay tree leaf i step value = chainInputPW lay tree leaf i step 0 0 0 value := by
  unfold WCT9.chainInputW chainInputPW
  split
  · rw [SigGolfCandidate.T3M.chainHeaderP_zero lay tree leaf i step ht hl hi hs, WCT9.bytesLE_zero16]
  · exact SigGolfCandidate.T3M.SecurityInputs.chainInput_eq_zero lay tree leaf i step value ht hl hi hs
/-- C3 + pairing stage 1: the verifier chain (`chainP` with the high halves of `WCT9.chainHigh`, G inputs). -/
def chainPW (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64)
    (value : Digest) : M Digest :=
  (List.range' start count).foldlM (fun value step => WCT9.halfHash (WCT9.chainHigh lay i step)
    (chainInputPW lay tree leaf i step pad0 pad1 headerPad value)) value
theorem chainPW_of_low {lay : Layer} {i start count : Nat} (hG : WCT9.isG lay i = false)
    (h : ∀ step, start ≤ step → step < start + count → WCT9.chainHigh lay i step = false)
    (tree leaf : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64) (value : Digest) :
    chainPW lay tree leaf i start count pad0 pad1 headerPad value =
      chainP lay tree leaf i start count pad0 pad1 headerPad value := by
  unfold chainPW chainP
  apply WCT9.foldlM_congr_of_mem
  intro step hs b
  rw [List.mem_range'_1] at hs
  rw [h step hs.1 hs.2, chainInputPW_F hG]; rfl
/-- Witness stack: a top F chain (odd, or `> 52`) is `chainP`. -/
theorem chainPW_top_F {i : Nat} (hG : SigGolfCandidate.T3.topIsG i = false) (tree leaf start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value : Digest) :
    chainPW 0 tree leaf i start count pad0 pad1 headerPad value =
      chainP 0 tree leaf i start count pad0 pad1 headerPad value :=
  chainPW_of_low (by rw [WCT9.isG_top_eq, hG])
    (fun _ _ _ => by rw [WCT9.chainHigh_top_eq, WCT9.topChainHigh_of_F hG]) tree leaf pad0 pad1 headerPad value
theorem layerBase_values : List.ofFn (fun lay : Layer => layerBase lay) = [7664, 11144, 13792, 16360] := rfl
theorem layerBase_tiles : ∀ lay : Fin 3,
    layerBase lay.castSucc + 16 * pathSlots lay.castSucc + chainArea lay.castSucc = layerBase lay.succ := by
  decide
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
/-- The top layer after decoding (C4: the folds are `WCT9.lowerNodeHashP` with the witness high pad, the same as
`topFinishP`; `topLayerP_of_decode`). Stated for any layer; it is used at `lay = 0`. -/
def layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
  let value ← WCT9.leafHashW lay tree leaf (wtopLeafPad w) (wleafHigh w lay) ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    WCT9.lowerNodeHashP lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerkleHigh w lay leaf j.val) (wmerklePad w lay leaf j.val) pair.2) value
def layerLeafP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
  WCT9.leafHashW lay tree leaf (wtopLeafPad w) (wleafHigh w lay) ends
theorem pubGood_halfHash (high : Bool) (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (WCT9.halfHash high input) PubGood := by
  rw [WCT9.halfHash_eq]
  exact allQ_bind (SigGolfCandidate.T3M.pubGood_publicHash input h) fun _ => SigGolfCandidate.T3M.allQ_pure _
theorem pubGood_lowerHash (lay heap : Nat) (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (WCT9.lowerHash lay heap input) PubGood := pubGood_halfHash _ _ h
theorem leafInputW_length (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    (WCT9.leafInputW lay tree leaf pad hi ends).length = (leafInput lay tree leaf ends).length := by
  unfold WCT9.leafInputW leafInput
  split <;> simp [SphincsSecurity.bytesLE_length, zero16] <;> omega
theorem leafInputW_length_pos (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    0 < (WCT9.leafInputW lay tree leaf pad hi ends).length := by
  rw [leafInputW_length, leafInput_length]; split_ifs <;> omega
theorem pubGood_leafHashW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashW lay tree leaf pad hi ends) PubGood :=
  pubGood_lowerHash _ _ _ (leafInputW_length_pos lay tree leaf pad hi ends)
theorem pubGood_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.lowerLeafHash lay tree leaf ends) PubGood := pubGood_leafHashW _ _ _ _ _ _
theorem pubGood_lowerNodeHashP (lay tree heap : Nat) (l : Digest) (hp : BitVec 64) (p r : Digest) :
    AllQueriesSatisfy (WCT9.lowerNodeHashP lay tree heap l hp p r) PubGood :=
  pubGood_lowerHash _ _ _ (by simp [WCT9.lowerNodeInputP, SphincsSecurity.bytesLE_length])
theorem pubGood_lowerNodeHash (lay tree heap : Nat) (l r : Digest) :
    AllQueriesSatisfy (WCT9.lowerNodeHash lay tree heap l r) PubGood :=
  pubGood_lowerHash _ _ _ (by simp [WCT9.merkleNodeInput, SphincsSecurity.bytesLE_length])
theorem pubGood_chainPW (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64)
    (value : Digest) : AllQueriesSatisfy (chainPW lay tree leaf i start count pad0 pad1 headerPad value) PubGood := by
  unfold chainPW
  exact allQ_foldlM _ _ (fun _ _ => pubGood_halfHash _ _ (by rw [chainInputPW_length]; omega)) _
theorem pubGood_layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (layerP w index lay digits) PubGood := by
  unfold layerP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chainPW _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHashW _ _ _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_lowerNodeHashP _ _ _ _ _ _ _) _
end ClaudeWCT.W9.T3M
