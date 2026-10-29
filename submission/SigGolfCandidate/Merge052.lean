import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge051

-- ==== merged from ClaudeWCT_W9_T3M_Witness_Layout ====
section

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
end
-- ==== merged from W9Machine_WctLayout ====
section

set_option autoImplicit false
namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
structure Layout where
  image : Image
  chainWord : Fin 666 → Nat
  childWord : Fin 128 → Nat
  returnWord : Fin 9 → Nat
  /-- Base shift of the FTS frame in 8-byte units: verify runs the shared banks at `coordinateBase` (`0`); expand
  runs them 1224 bytes lower (`153`) and moves the block up afterwards. Only `min delta8 153` is used. -/
  delta8 : Nat
def GoodQFor (im : Image) (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat)
    (X : OracleComp HashSpec Obs) (P : Hash → Prop := HashOk) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F im s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F im s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F im s)).exit = .success → P hash →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ A)
structure Budget where
  fuel : Nat
  allCycles : Nat
  acceptCycles : Nat
def layerEntryWord : Nat := 32951
def layerWitnessOffset : Nat := 7664
def forestRootAddress : Nat := 0x100
/-- Nested FTS (r1-1, witness stack): region `n` (tree `n`, `n ≤ 8`) at `10992 - 848 n`; region 9 is the virtual tree below tree 8
(its leaf-pad and Z slots receive tree 8's top pair). -/
def regionAddr (n : Nat) : Nat := 10992 - 848 * n
def coordinateBase (k : Fin 9) : Nat := 4208 + 848 * (8 - k.val)
/-- Byte shift of the FTS frame of a layout (`0` for verify, `1224` for expand). -/
def Layout.shift (L : Layout) : Nat := 8 * min L.delta8 153
namespace Chain
/-- Base register `x8` of coordinate `k` in layout `L`. -/
abbrev base (L : Layout) (k : Fin 9) : Nat := coordinateBase k - L.shift
end Chain
theorem Layout.shift_le (L : Layout) : L.shift ≤ 1224 ∧ L.shift % 8 = 0 := by
  unfold Layout.shift; omega
theorem Chain.base_bounds (L : Layout) (k : Fin 9) :
    2984 ≤ Chain.base L k ∧ Chain.base L k ≤ 10992 ∧ Chain.base L k % 8 = 0 ∧
      Chain.base L k + L.shift = coordinateBase k := by
  have := k.isLt; unfold Chain.base coordinateBase Layout.shift; omega
def headerTable (k : Fin 9) : Nat := 0xfee600 + 512 * k.val
def forestInputAddress : Nat := 0xffbdf0
def pairAddress (k : Fin 9) : Nat := forestInputAddress + 32 + 32 * k.val
abbrev WBytes := ClaudeWCT.W9.T3M.WBytes
abbrev wdig (w : WBytes) (off : Nat) : SigGolfCandidate.T3.Digest := ClaudeWCT.W9.T3M.wdig w off
def OrigW (w : WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A - 0x1020)) 64
/-- `OrigW` for a frame shifted down by `d` bytes (witness byte `o` at `0x1020 - d + o`). -/
def OrigWD (d : Nat) (w : WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A + d - 0x1020)) 64
theorem wdig_lo (w : WBytes) (off : Nat) : (wdig w off).extractLsb' 0 64 = w.extractLsb' (8 * off) 64 := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem wdig_hi (w : WBytes) (off : Nat) :
    (wdig w off).extractLsb' 64 64 = w.extractLsb' (8 * (off + 8)) 64 := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (off + 8) = 8 * off + 64 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize w.toNat / 2 ^ (8 * off) = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem DigAt_origW {w : WBytes} {s : MachineState} {A : Nat} (h0 : OrigW w s A) (h1 : OrigW w s (A + 8))
    (hA : 0x1020 ≤ A) : DigAt s A (wdig w (A - 0x1020)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 - 0x1020 = A - 0x1020 + 8 by omega]
theorem DigAt_origWD {d : Nat} {w : WBytes} {s : MachineState} {A : Nat} (h0 : OrigWD d w s A)
    (h1 : OrigWD d w s (A + 8)) (hA : 0x1020 ≤ A + d) : DigAt s A (wdig w (A + d - 0x1020)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 + d - 0x1020 = A + d - 0x1020 + 8 by omega]
end W9Machine
end
-- ==== merged from ClaudeWCT_W9_T3M_Witness_VerifyP ====
section

section
namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff)
/-- Nested FTS (r1-1): region stride 896; coordinate `k`'s region starts at `80 + 896 (8 - k)` (absolute
`1392 + 896 (8 - k)`; witness trim: the witness starts at 1312). Witness stack (charge 86): stride 848, the witness
starts at absolute 4128. -/
def regionBase (k : Nat) : Nat := 80 + 848 * (8 - k)
def wctEnd : Nat := 7664
/-- Witness stack: offset of FTS chain `t`'s block in its region. Chain 0 (F) at 592 (its value slot is the leaf
block), pair (G1, F2) at 504/528, pair (G3, F4) at 400/424, chain 5 (F) at 320. -/
def wctChainOff (t : Nat) : Nat :=
  if t = 0 then 592 else if t = 5 then 320 else if t % 2 = 1 then 504 - 104 * (t / 2) else 528 - 104 * (t / 2 - 1)
def wctChainBlock (k t : Nat) : Nat := regionBase k + wctChainOff t
def wctLeafBlock (k : Nat) : Nat := regionBase k + 640
def wctLeafSlot (k t : Nat) : Nat := regionBase k + (if t = 0 then 640 else 672 + 16 * t)
/-- Witness stack: offset of the supplied value / of the two zero pads inside an FTS chain block (F: 48 / 0, 32;
G: 0 / 32, 48). -/
def wctValueOff (t : Nat) : Nat := if WCT9.ftsIsG t then 0 else 48
def wctPad0Off (t : Nat) : Nat := if WCT9.ftsIsG t then 32 else 0
def wctPad1Off (t : Nat) : Nat := if WCT9.ftsIsG t then 48 else 32
def authPlans : List (List Nat × Nat) :=
  [([0,32,64,96,128,784], 224),
   ([0,48,80,112,144,784], 240),
   ([48,0,80,112,144,784], 240),
   ([32,112,160,192,224,784], 0),
   ([48,80,144,192,224,784], 0),
   ([32,80,144,192,224,784], 0),
   ([80,32,144,192,224,784], 0),
   ([64,16,144,192,224,784], 0),
   ([48,80,112,176,224,784], 0),
   ([32,80,112,176,224,784], 0),
   ([80,32,112,176,224,784], 0),
   ([272,16,64,160,208,784], 0),
   ([80,112,32,176,224,784], 0),
   ([64,112,16,176,224,784], 0),
   ([112,64,16,176,224,784], 0),
   ([256,208,160,0,48,784], 144),
   ([48,80,112,144,208,784], 0),
   ([32,80,112,144,208,784], 0),
   ([80,32,112,144,208,784], 0),
   ([272,16,64,176,128,784], 0),
   ([80,112,32,144,208,784], 0),
   ([64,112,16,144,208,784], 0),
   ([112,64,16,144,208,784], 0),
   ([288,240,16,64,128,784], 0),
   ([80,112,144,32,208,784], 0),
   ([64,112,144,16,208,784], 0),
   ([112,64,144,16,208,784], 0),
   ([288,112,160,240,0,784], 224),
   ([112,144,64,16,208,784], 0),
   ([128,176,288,240,0,784], 112),
   ([176,128,288,240,0,784], 112),
   ([272,224,176,128,0,784], 112),
   ([48,80,112,144,256,784], 0),
   ([32,80,112,144,256,784], 0),
   ([80,32,112,144,256,784], 0),
   ([272,16,64,96,208,784], 0),
   ([80,112,32,144,256,784], 0),
   ([64,112,16,144,256,784], 0),
   ([112,64,16,144,256,784], 0),
   ([288,240,16,64,176,784], 0),
   ([80,112,144,32,256,784], 0),
   ([64,112,144,16,256,784], 0),
   ([112,64,144,16,256,784], 0),
   ([288,112,160,0,48,784], 224),
   ([112,144,64,16,256,784], 0),
   ([128,176,288,16,64,784], 0),
   ([176,128,288,16,64,784], 0),
   ([272,224,176,48,96,784], 160),
   ([80,112,144,256,208,784], 0),
   ([64,112,144,256,208,784], 0),
   ([112,64,144,256,208,784], 0),
   ([288,112,160,48,0,784], 224),
   ([112,144,64,256,208,784], 0),
   ([128,176,16,64,288,784], 0),
   ([176,128,16,64,288,784], 0),
   ([272,224,96,144,48,784], 208),
   ([112,144,256,208,64,784], 0),
   ([128,176,64,16,288,784], 0),
   ([176,128,64,16,288,784], 0),
   ([272,144,192,96,48,784], 256),
   ([176,112,64,16,288,784], 0),
   ([192,240,144,96,48,784], 304),
   ([240,192,144,96,48,784], 304),
   ([256,208,160,112,64,784], 0)]
def authBase (child l : Nat) : Nat := ((authPlans.getD (child % 64) ([], 0)).1).getD l 0
theorem authBase_five (child : Nat) : authBase child 5 = 784 := by
  have h : ∀ c < 64, ((authPlans.getD c ([], 0)).1).getD 5 0 = 784 := by decide
  exact h (child % 64) (Nat.mod_lt _ (by decide))
def authRoot (child : Nat) : Nat := (authPlans.getD (child % 64) ([], 0)).2
def authSibOff (child l : Nat) : Nat :=
  if l < 6 then authBase child l + sibOff (child / 2 ^ l % 2) else authRoot child
def authPadOff (child l : Nat) : Nat := authBase child l + 32
def wopen (w : WBytes) (k t : Nat) : Digest := wdig w (wctChainBlock k t + wctValueOff t)
def wleaf (w : WBytes) (k t : Nat) : Digest := wdig w (wctLeafSlot k t)
def wreveal (w : WBytes) (k t d : Nat) : Digest := if d = 0 then wleaf w k t else wopen w k t
def wcpads (w : WBytes) (k t : Nat) : Digest × Digest :=
  (wdig w (wctChainBlock k t + wctPad0Off t), wdig w (wctChainBlock k t + wctPad1Off t))
/-- Nested FTS (r1-1): the supplied top sibling of coordinate `k` sits in coordinate `k + 1`'s region: its leaf pad
slot (`regionBase k - 176`) when the computed top is the right one (bit 6 set), else its level-6 pad slot
(`regionBase k - 32`). For `k = 8` these are the L3 block's left slot (offset 0) and the R9 slot (witness trim:
offset 64, the 16 bytes after the L3 block's hash input). -/
def topSlot (k child : Nat) : Nat :=
  if k = 8 then (if child / 2 ^ 6 % 2 = 0 then 64 else 0)
  else regionBase k - (if child / 2 ^ 6 % 2 = 0 then 32 else 176)
/-- Pairing stage 1: the legacy level-5 window of coordinate 0 (`regionBase 0 + 832`, 64 bytes) is removed from the
witness. The legacy padded verifier reads coordinate 0's level-5 sibling from `legacySib0` (the 16 bytes after
region 0's leaf area; the live paired forest never uses coordinate 0's level 5) and its pad from `legacyPad0` (region
0's zero cell at offset 816). Witness stack: 7648 and offset 768. -/
def legacySib0 : Nat := 7648
def legacyPad0 : Nat := regionBase 0 + 768
def wsib (w : WBytes) (k child l : Nat) : Digest :=
  if l < 6 then (if k = 0 ∧ l = 5 then wdig w legacySib0 else wdig w (regionBase k + authSibOff child l))
  else wdig w (topSlot k child)
def wmpad (w : WBytes) (k child l : Nat) : Digest :=
  if k = 0 ∧ l = 5 then wdig w legacyPad0 else wdig w (regionBase k + authPadOff child l)
/-- High tweak word of a packed FTS node (levels `< 4`) whose computed child is the right input: the verifier
writes only the low tweak word there, the high word stays witness memory (honest 0). Elsewhere it is 0. -/
def wmhpad (w : WBytes) (k child l : Nat) : BitVec 64 :=
  if l < 4 ∧ child / 2 ^ l % 2 = 1 then (wdig w (regionBase k + authBase child l + 16)).extractLsb' 64 64 else 0
def wcHeaderPad (w : WBytes) (k t : Nat) : BitVec 64 := (wdig w (wctChainBlock k t + 16)).extractLsb' 64 64
/-- FTS leaf pad (campaign T8): the 16-byte slot after the leaf header (`regionBase k + 720`); the verifier never
writes it, the honest witness holds 0. -/
def wleafPad (w : WBytes) (k : Nat) : Digest := wdig w (wctLeafBlock k + 32)
def upLayer (lay : Layer) : Layer := Fin.ofNat 4 (lay.val + 1)
def rowBlock (index : Nat) (lay : Layer) : Nat :=
  if lay.val = 3 then 0 else merkleBlock (upLayer lay) (route index (upLayer lay)).1 (height (upLayer lay) - 1)
def bcCounterOff (index : Nat) (lay : Layer) : Nat := rowBlock index lay + 32
def wbcCtr (w : WBytes) (index : Nat) (lay : Layer) : BitVec 32 := wle32 w (bcCounterOff index lay)
def wbcPad (w : WBytes) (index : Nat) (lay : Layer) : BitVec 96 := w.extractLsb' (8 * (bcCounterOff index lay + 4)) 96
def wbcRight (w : WBytes) : Digest := wdig w 48
/-- C2/C3 (FULL): the high word of encoding `lay`'s row tweak (witness bytes `[rowBlock + 24, +8)`: L3 at witness 24,
else the root window of `upLayer lay`; honest 1). -/
def wbcHigh (w : WBytes) (index : Nat) (lay : Layer) : BitVec 64 := (wdig w (rowBlock index lay + 16)).extractLsb' 64 64
theorem wctLeafSlot_zero (k : Nat) : wctLeafSlot k 0 = wctChainBlock k 0 + 48 := by
  simp [wctLeafSlot, wctChainBlock, wctChainOff]
theorem wctValueOff_zero : wctValueOff 0 = 48 := by simp [wctValueOff, WCT9.ftsIsG]
theorem wleaf_zero (w : WBytes) (k : Nat) : wleaf w k 0 = wopen w k 0 := by
  unfold wleaf wopen; rw [wctLeafSlot_zero, wctValueOff_zero]
end ClaudeWCT.W9.T3M
end
section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (chainP nodeHashP recoverLayerP)
open SphincsSecurity (bytesLE)
def wctChainInputP (index coord child t step : Nat) (padA : Digest) (padB : BitVec 64) (padC value : Digest) :
    HashInput :=
  bytesLE 16 padA ++ bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step padB) ++ bytesLE 16 padC ++
    bytesLE 16 value
/-- Witness stack: the padded FTS step input in either format (G chains 1, 3: `value | header | padA | padC`). -/
def wctChainInputPW (index coord child t step : Nat) (padA : Digest) (padB : BitVec 64) (padC value : Digest) :
    HashInput :=
  if WCT9.ftsIsG t then
    bytesLE 16 value ++ bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step padB) ++ bytesLE 16 padA ++
      bytesLE 16 padC
  else wctChainInputP index coord child t step padA padB padC value
def wctChainP (index coord child t start count : Nat) (padA : Digest) (padB : BitVec 64) (padC value : Digest) :
    M Digest :=
  (List.range' start count).foldlM
    (fun value step => projHash (WCT9.ftsChainHigh t step) (wctChainInputPW index coord child t step padA padB padC value))
    value
def wctNodeHashP (coord index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : M Digest :=
  shortHash (SigGolfCandidate.T3M.SecurityInputs.nodeInputPH 3 (WCT9.nodeLayer coord) index heap left hp pad right)
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ WCT9.digestVerifyWindow then pure none else some <$> digest (wrho w) m (wdc w)
def gateOk (N : HashOutput) : Bool := decide (N.toNat / 2 ^ 242 % 2 ^ 14 < WCT9.gateLimit)
def fieldOk (N : HashOutput) (coord : WCT9.Coord) : Bool := decide (WCT9.field N coord < WCT9.fieldLimit)
/-- One FTS coordinate of the padded verifier (nested FTS r1-1): `prev` is the previous coordinate's top pair; its
left value is this coordinate's leaf pad and its right value the pad of the top node hash (high half). -/
def wctCoordP (w : WBytes) (index : Nat) (coord : WCT9.Coord) (child : WCT9.Child) (word : WCT9.Rank)
    (prev : Digest × Digest) : M (Digest × Digest) := do
  let ends ← (List.finRange 6).mapM fun t =>
    wctChainP index coord.val child.val t.val (4 - WCT9.wordDigit word t) (WCT9.wordDigit word t)
      (wcpads w coord.val t.val).1 (wcHeaderPad w coord.val t.val) (wcpads w coord.val t.val).2
      (wreveal w coord.val t.val (WCT9.wordDigit word t))
  let leaf ← WCT9.leafHashP index coord.val child.val prev.1 ends
  let value ← (List.finRange 5).foldlM (fun value level => do
    let other := wsib w coord.val child.val level.val
    let pair := if child.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + child.val / 2 ^ (level.val + 1)) pair.1
      (wmhpad w coord.val child.val level.val) (wmpad w coord.val child.val level.val) pair.2) leaf
  let other5 := wsib w coord.val child.val 5
  let pair5 := if child.val / 2 ^ 5 % 2 = 0 then (value, other5) else (other5, value)
  let top ← WCT9.wctTopHash coord.val index (2 + child.val / 2 ^ 6) pair5.1 prev.2 pair5.2
  let other := wsib w coord.val child.val 6
  pure (if child.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
/-- Nested FTS (r1-1): coordinate 0's pads are free witness slots (honest 0). -/
def wctStart (w : WBytes) : Digest × Digest := (wleafPad w 0, wmpad w 0 0 5)
def wctStep (w : WBytes) (N : HashOutput) (state : Option (List (Digest × Digest))) (coord : WCT9.Coord) :
    M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if !fieldOk N coord then return none
  let pair ← wctCoordP w (WCT9.digestIndex N) coord (WCT9.child N coord) (WCT9.rank N coord)
    (WCT9.prevPair (wctStart w) pairs)
  pure (some (pairs ++ [pair]))
/-- The FTS phase (nested FTS r1-1): the last coordinate's top pair, the L3 message. -/
def wctP (w : WBytes) (N : HashOutput) : M (Option (Digest × Digest)) := do
  let some pairs ← (List.finRange 9).foldlM (wctStep w N) (some []) | pure none
  pure (some (WCT9.prevPair (wctStart w) pairs))
/-- The verifier's encoding input (C2/C3 FULL: the row tweak's high word `hi` is a witness pad, honest 1). -/
def layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) : HashInput :=
  match msg with
  | .forest root => WCT9.pairEncodingInputH lay tree leaf root padR counter pad hi
  | .pair left right => WCT9.pairEncodingInputH lay tree leaf left right counter pad hi
def layerPairP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
  let value ← WCT9.leafHashW lay tree leaf (wtopLeafPad w) (wleafHigh w lay) ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    WCT9.lowerNodeHashP lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerkleHigh w lay leaf j.val) (wmerklePad w lay leaf j.val) pair.2) value
  let other := wpath w lay leaf (height lay - 1)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def layerChainP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) (i : Nat) : M Digest :=
  chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
    (maxDigit lay i - digits.getD i 0) (wchainPads w lay (i % chainCount lay)).1
    (wchainPads w lay (i % chainCount lay)).2 (wchainHeaderPad w lay (i % chainCount lay))
    (wvalueFor w lay digits (i % chainCount lay))
def layerGuardedPairP (w : WBytes) (index : Nat) (lay : Layer) (answer : Digest) (digits : List Nat) :
    M (Option (Digest × Digest)) :=
  WCT9.lowerGuardedRun (layerChainP w index lay digits) (layerPairP w index lay digits) answer
def topChainP (w : WBytes) (tree leaf : Nat) (digits : List Nat) (i : Fin (chainCount 0)) (digit : Nat) : M Digest :=
  chainPW 0 tree leaf i.val digit (maxDigit 0 i.val - digit) (wchainPads w 0 i.val).1 (wchainPads w 0 i.val).2
    (wchainHeaderPad w 0 i.val) (wvalueFor w 0 digits i.val)
/-- C4: the top leaf (half by leaf parity) and the 12 top folds with the one-word label `topNodeWord heap`, the
witness high pad `wmerkleHigh w 0` and Z pad `wmerklePad w 0` (half by heap parity; the root, heap 1, low). -/
def topFinishP (w : WBytes) (tree leaf : Nat) (ends : List Digest) : M Digest := do
  let value ← WCT9.leafHashW 0 tree leaf (wtopLeafPad w) (wleafHigh w 0) ends
  (List.finRange (height 0)).foldlM (fun value j => do
    let other := wpath w 0 leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    WCT9.lowerNodeHashP (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerkleHigh w 0 leaf j.val) (wmerklePad w 0 leaf j.val) pair.2) value
def topLayerP (w : WBytes) (index : Nat) (answer : Digest) : M (Option Digest) :=
  WCT9.topDecodeRun (topChainP w (route index 0).2 (route index 0).1 (dataDigits 0 answer)) (topFinishP w (route index 0).2 (route index 0).1)
    answer
def layersBC (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w)
        (wbcHigh w index lay))
      if n = 0 then topLayerP w index answer
      else do
        let some digits := decode lay answer | pure none
        let some pair ← layerGuardedPairP w index lay answer digits | pure none
        layersBC w index n (.pair pair.1 pair.2)
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some top ← wctP w N | pure false
  let some root ← layersBC w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def layersBCPrepass (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w)
        (wbcHigh w index lay))
      let some digits := decode lay answer | pure none
      if n = 0 then some <$> layerP w index lay digits
      else do
        let pair ← layerPairP w index lay digits
        layersBCPrepass w index n (.pair pair.1 pair.2)
def verifyPPrepass (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some top ← wctP w N | pure false
  let some root ← layersBCPrepass w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
structure Pads where
  wctChain : WCT9.Coord → Fin 6 → Digest × Digest
  wctChainHigh : WCT9.Coord → Fin 6 → BitVec 64
  wctMerkle : WCT9.Coord → Fin 7 → Digest
  /-- High tweak words of the packed FTS nodes (honest 0). -/
  wctMerkleHigh : WCT9.Coord → Fin 7 → BitVec 64
  /-- FTS leaf pad (campaign T8; honest 0). -/
  wctLeaf : WCT9.Coord → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest
  chainHeader : (lay : Layer) → Fin (chainCount lay) → BitVec 64
  bc : Layer → BitVec 96
  bcRight : Digest
  /-- Difference between the prefilled endpoint and its raw chain value. Honest witnesses have zero masks. -/
  endpointMask : (lay : Layer) → Fin (chainCount lay) → Digest
  /-- C2 + C4: high tweak words of the one-word fold labels (lay 1..3 levels `< height - 1`, and every top level;
  honest 0). -/
  merkleHigh : (lay : Layer) → Fin (height lay) → BitVec 64
  /-- C3: the top leaf pad (the leading 16 bytes of the top leaf input; honest 0). -/
  topLeaf : Digest
  /-- C3: the leaf tweak's high word (honest 0). -/
  leafHigh : Layer → BitVec 64
  /-- C2/C3: XOR mask of the encoding row tweak's high word (the verifier uses `bcHigh lay ^^^ 1`; honest mask 0). -/
  bcHigh : Layer → BitVec 64
instance : Zero Pads :=
  ⟨⟨fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0,
    fun _ => 0, 0, fun _ _ => 0, fun _ _ => 0, 0, fun _ => 0, fun _ => 0⟩⟩
def Pads.toT3 (pads : Pads) : SigGolfCandidate.T3M.Pads :=
  ⟨fun _ => 0, fun _ => 0, pads.chain, pads.merkle, pads.chainHeader⟩
def recoverCoordinateP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) (prev : Digest × Digest) : M (Digest × Digest) := do
  let selected := WCT9.child output coord
  let word := WCT9.rank output coord
  let ends ← (List.finRange 6).mapM fun i =>
    wctChainP index coord.val selected.val i.val (4 - WCT9.wordDigit word i) (WCT9.wordDigit word i)
      (pads.wctChain coord i).1 (pads.wctChainHigh coord i) (pads.wctChain coord i).2
      ((sig.openings coord).values i)
  let root ← WCT9.leafHashP index coord.val selected.val prev.1 ends
  let value ← (List.finRange 5).foldlM (fun value level => do
    let other := (sig.openings coord).path (Fin.castLE (by decide) level)
    let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    wctNodeHashP coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1)) pair.1
      (pads.wctMerkleHigh coord (Fin.castLE (by decide) level)) (pads.wctMerkle coord (Fin.castLE (by decide) level))
      pair.2) root
  let other5 := (sig.openings coord).path 5
  let pair5 := if selected.val / 2 ^ 5 % 2 = 0 then (value, other5) else (other5, value)
  let top ← WCT9.wctTopHash coord.val index (2 + selected.val / 2 ^ 6) pair5.1 prev.2 pair5.2
  let other := (sig.openings coord).path 6
  pure (if selected.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
/-- Nested FTS (r1-1): coordinate 0's pads in the abstract padded verifier. -/
def Pads.start (pads : Pads) : Digest × Digest := (pads.wctLeaf 0, pads.wctMerkle 0 5)
def recoverFtsP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput) : M (Digest × Digest) := do
  let pairs ← (List.finRange 9).foldlM (fun (pairs : List (Digest × Digest)) coord => do
    let pair ← recoverCoordinateP sig pads index output coord (WCT9.prevPair pads.start pairs)
    pure (pairs ++ [pair])) []
  pure (WCT9.prevPair pads.start pairs)
/-- Effective input of a chain, including the endpoint stored in a skipped-copy slot. -/
def valueP (sig : WCT9.Signature) (pads : Pads) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) : Digest :=
  if WCT9.safeZeroCopy lay digits i.val then
    (sig.layers lay).values i ^^^ pads.endpointMask lay i else (sig.layers lay).values i

@[simp] theorem valueP_zero (sig : WCT9.Signature) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) : valueP sig 0 lay digits i = (sig.layers lay).values i := by
  unfold valueP
  split
  · change (sig.layers lay).values i ^^^ (0 : Digest) = (sig.layers lay).values i
    exact BitVec.xor_zero
  · rfl

/-- A single-layer view after its encoding digits are known; other layers are irrelevant to this view. -/
def effectiveSignature (sig : WCT9.Signature) (pads : Pads) (digits : List Nat) : WCT9.Signature :=
  { sig with layers := fun lay => { sig.layers lay with values := valueP sig pads lay digits } }

def recoverLayerPairP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (pads.chain lay i).1 (pads.chain lay i).2 (pads.chainHeader lay i) (valueP sig pads lay digits i)
  let value ← WCT9.leafHashW lay tree leaf pads.topLeaf (pads.leafHigh lay) ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    WCT9.lowerNodeHashP lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkleHigh lay (Fin.castLE (Nat.sub_le _ _) j)) (pads.merkle lay (Fin.castLE (Nat.sub_le _ _) j))
      pair.2) value
  let other := (sig.layers lay).path (WCT9.topLevel lay)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
def recoverLayerPairGuardP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) : M (Option (Digest × Digest)) :=
  WCT9.lowerGuardedRun
    (fun i => let j : Fin (chainCount lay) := ⟨i % chainCount lay, Nat.mod_lt _ (by fin_cases lay <;> decide)⟩
      chainPW lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
        (maxDigit lay i - digits.getD i 0) (pads.chain lay j).1 (pads.chain lay j).2
        (pads.chainHeader lay j) (valueP sig pads lay digits j))
    (recoverLayerPairP sig pads index lay digits) answer
def verifyTopP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (answer : Digest) : M (Option Digest) :=
  let leaf := (route index 0).1
  let tree := (route index 0).2
  WCT9.topDecodeRun
    (fun i digit => chainPW 0 tree leaf i.val digit (maxDigit 0 i.val - digit) (pads.chain 0 i).1
      (pads.chain 0 i).2 (pads.chainHeader 0 i) (valueP sig pads 0 (dataDigits 0 answer) i))
    (fun ends => do
      let value ← WCT9.leafHashW 0 tree leaf pads.topLeaf (pads.leafHigh 0) ends
      (List.finRange (height 0)).foldlM (fun value j => do
        let other := (sig.layers 0).path j
        let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        WCT9.lowerNodeHashP (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
          (pads.merkleHigh 0 j) (pads.merkle 0 j) pair.2) value)
    answer
def verifyLayersBCP (w : WCT9.Witness) (pads : Pads) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter (pads.bc lay) pads.bcRight
        (pads.bcHigh lay ^^^ 1))
      if n = 0 then verifyTopP w.signature pads index answer
      else do
        let some digits := decode lay answer | pure none
        let some pair ← recoverLayerPairGuardP w.signature pads index lay answer digits | pure none
        verifyLayersBCP w pads index n (.pair pair.1 pair.2)
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if !WCT9.admissible output then return false
  let index := WCT9.digestIndex output
  let top ← recoverFtsP w.signature pads index output
  let some root ← verifyLayersBCP w pads index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def verifyPads (m : Message) (pk : Digest) (w : WCT9.Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ WCT9.digestAttemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads
end ClaudeWCT.W9.T3M
end

section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (allQ_pure allQ_bind allQ_map allQ_ite allQ_mapM)

theorem allQ_lowerGuardedRun {α : Type} {P : Spec.Domain → Prop}
    (run : Nat → M Digest) (finish : M α) (answer : Digest)
    (hrun : ∀ i, AllQueriesSatisfy (run i) P) (hfinish : AllQueriesSatisfy finish P) :
    AllQueriesSatisfy (WCT9.lowerGuardedRun run finish answer) P := by
  unfold WCT9.lowerGuardedRun
  exact allQ_ite _ (allQ_map _ hfinish)
    (allQ_bind (allQ_mapM _ _ hrun) fun _ => allQ_pure _)

theorem eval_lowerGuardedRun_none {α : Type} (answers : QueryImpl Spec Id)
    (run : Nat → M Digest) (finish : M α) (answer : Digest) (h : ¬ WCT9.lowerRankGood answer) :
    evalWithAnswerFn answers (WCT9.lowerGuardedRun run finish answer) = none := by
  simp [WCT9.lowerGuardedRun, h, evalWithAnswerFn_bind]

theorem layerGuardedPairP_of_good (w : WBytes) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) (h : WCT9.lowerRankGood answer) :
    layerGuardedPairP w index lay answer digits = some <$> layerPairP w index lay digits := by
  simp [layerGuardedPairP, WCT9.lowerGuardedRun, h]

theorem layerGuardedPairP_good_of_some (answers : QueryImpl Spec Id) (w : WBytes)
    (index : Nat) (lay : Layer) (answer : Digest) (digits : List Nat) (pair : Digest × Digest)
    (h : evalWithAnswerFn answers (layerGuardedPairP w index lay answer digits) = some pair) :
    WCT9.lowerRankGood answer := by
  by_contra hn
  have hz := eval_lowerGuardedRun_none answers (layerChainP w index lay digits)
    (layerPairP w index lay digits) answer hn
  change evalWithAnswerFn answers (layerGuardedPairP w index lay answer digits) = none at hz
  rw [hz] at h
  cases h
end ClaudeWCT.W9.T3M
end

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
/-- Padded canonical layers retain the machine ordering of rank checks and HASH calls. Configuration (1)+(2): the
top word is read with the witness choice hint `wtopHigh w` (`WCT9.verificationHash`; lower layers ignore it). -/
def layersCanonicalBC (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.verificationHash lay (wtopHigh w)
        (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay))
      if n = 0 then topLayerP w index answer
      else do
        let some digits := WCT9.CanonicalPolicy.decode lay answer | pure none
        let some pair ← layerGuardedPairP w index lay answer digits | pure none
        layersCanonicalBC w index n (.pair pair.1 pair.2)
end ClaudeWCT.W9.T3M
end
-- ==== merged from W9Machine_WctV3Source ====
section

set_option autoImplicit false
namespace W9Machine.V3
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE)
/-- Campaign S2 (as S1): the coordinate nibble carries `coord + 1` (every FTS word is `≥ 2^16`). -/
def chainPrefix (index coord child : Nat) : Nat :=
  (index <<< 27) ||| ((coord + 1) <<< 16) ||| (child <<< 20)
def chainLow (index coord child chain step : Nat) : Nat :=
  0x80 ||| (chain <<< 2) ||| (step <<< 8) ||| chainPrefix index coord child
abbrev HeaderPad := BitVec 64
/-- Witness stack: F chains (0, 2, 4, 5) hash `a | header | c | value`, G chains (1, 3) hash
`value | header | a | c`. -/
def chainInput (index coord child chain step : Nat) (a : Digest) (b : HeaderPad)
    (c value : Digest) : HashInput :=
  if ClaudeWCT.WCT9.ftsIsG chain then
    bytesLE 16 value ++ bytesLE 8 (chainLow index coord child chain step) ++ bytesLE 8 b ++
      bytesLE 16 a ++ bytesLE 16 c
  else
    bytesLE 16 a ++ bytesLE 8 (chainLow index coord child chain step) ++ bytesLE 8 b ++
      bytesLE 16 c ++ bytesLE 16 value
/-- Witness stack: interior G steps keep the high half (`ftsChainHigh`), every other step the low half. -/
def chainP (index coord child chain start count : Nat) (a : Digest) (b : HeaderPad)
    (c value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun v step => projHash (ClaudeWCT.WCT9.ftsChainHigh chain step)
      (chainInput index coord child chain step a b c v)) value
def regionOffset (coord : Nat) : Nat := 80 + 848 * (8 - coord)
def chainOffset (coord chain : Nat) : Nat := regionOffset coord + ClaudeWCT.W9.T3M.wctChainOff chain
def leafSlot (chain : Nat) : Nat := if chain = 0 then 640 else 672 + 16 * chain
def chainPadA (w : WBytes) (coord chain : Nat) : Digest :=
  wdig w (chainOffset coord chain + ClaudeWCT.W9.T3M.wctPad0Off chain)
def chainPadB (w : WBytes) (coord chain : Nat) : HeaderPad :=
  w.extractLsb' (8 * (chainOffset coord chain + 24)) 64
def chainPadC (w : WBytes) (coord chain : Nat) : Digest :=
  wdig w (chainOffset coord chain + ClaudeWCT.W9.T3M.wctPad1Off chain)
def reveal (w : WBytes) (coord chain deficit : Nat) : Digest :=
  if deficit = 0 then wdig w (regionOffset coord + leafSlot chain)
  else wdig w (chainOffset coord chain + ClaudeWCT.W9.T3M.wctValueOff chain)
def chainProgram (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 666) : M (List Digest) :=
  (List.finRange 6).mapM fun t =>
    let d := ClaudeWCT.WCT9.digit rank t
    chainP index k.val j.val t.val (4 - d) d
      (chainPadA w k.val t.val) (chainPadB w k.val t.val)
      (chainPadC w k.val t.val) (reveal w k.val t.val d)
def leafLow (index coord child : Nat) : Nat := ClaudeWCT.WCT9.ftsLeafLow index coord child
def nodeLow (coord index : Nat) : Nat := ClaudeWCT.WCT9.ftsLeafLow index coord 0
/-- Node tweak as the verifier writes it: packed heaps (`8..127`) carry `nodeLow - heap` and a witness high
word `hp`; the other heaps carry `nodeLow` and the heap. -/
def nodeHdr (coord index heap : Nat) (hp : BitVec 64) : Digest :=
  if 8 ≤ heap ∧ heap < 128 then hp ++ BitVec.ofNat 64 (nodeLow coord index - heap)
  else BitVec.ofNat 64 heap ++ BitVec.ofNat 64 (nodeLow coord index)
def nodeInput (coord index heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (nodeHdr coord index heap hp) ++ bytesLE 16 pad ++ bytesLE 16 right
/-- Nested FTS (r1-1): fold block offset of child level `level` in a region. Levels 0..4 follow the child plan;
level 5 (heaps 2, 3) uses the fixed block at 784, `left | hdr | Z | right`. -/
def blkOff (child level : Nat) : Nat := if level < 5 then ClaudeWCT.W9.T3M.authBase child level else 784
def sibOff (child level : Nat) : Nat := blkOff child level + 48 * (1 - child / 2 ^ level % 2)
def padOff (child level : Nat) : Nat := blkOff child level + 32
def nodePad (w : WBytes) (coord child level : Nat) : Digest := wdig w (regionOffset coord + padOff child level)
/-- The 16-byte tweak slot of a child level in the witness (`blkOff + 16`). -/
def nodeTw (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (regionOffset coord + blkOff child level + 16)
/-- High tweak word of a packed node (levels `< 4`) whose computed child is the right input; elsewhere 0. -/
def nodeHPad (w : WBytes) (coord child level : Nat) : BitVec 64 :=
  if level < 4 ∧ child / 2 ^ level % 2 = 1 then (nodeTw w coord child level).extractLsb' 64 64 else 0
def sibling (w : WBytes) (coord child level : Nat) : Digest := wdig w (regionOffset coord + sibOff child level)
/-- FTS leaf pad slot (`regionOffset coord + 672`): tree `coord - 1`'s left top node in the nested FTS. -/
def leafPad (w : WBytes) (coord : Nat) : Digest := wdig w (regionOffset coord + 672)
/-- The high 16 bytes of a public hash: the value of a heap-2/3 node. -/
def hashHi (input : HashInput) : M Digest := do
  pure ((← publicHash input).extractLsb' 128 128)
/-- Witness slot of tree `coord`'s top sibling: the Z slot (`+816`) of the region below when the computed top
node is the left one, its leaf pad (`+672`) otherwise; below tree 8 this is the virtual region (witness trim:
offsets 64 (the R9 slot), 0). -/
def topOtherOff (coord child : Nat) : Nat :=
  if coord = 8 then (if child / 64 % 2 = 0 then 64 else 0) else
  if child / 64 % 2 = 0 then regionOffset coord - 32 else regionOffset coord - 176
def topOther (w : WBytes) (coord child : Nat) : Digest := wdig w (topOtherOff coord child)
/-- The eight 16-byte fields of the T8 leaf `end0 | header | pad | end1..end5`. -/
def leafFields (coord index child : Nat) (pad : Digest) (ends : List Digest) (slot : Nat) : Digest :=
  if slot = 0 then ends.getD 0 0
  else if slot = 1 then ClaudeWCT.WCT9.ftsLeafHeader index coord child
  else if slot = 2 then pad else ends.getD (slot - 2) 0
def leafInput (coord index child : Nat) (pad : Digest) (ends : List Digest) : HashInput :=
  (List.range 8).flatMap fun slot => bytesLE 16 (leafFields coord index child pad ends slot)
structure RootPair where
  left : Digest
  right : Digest
def orderPair (child : Nat) (computed other : Digest) : RootPair :=
  if child / 64 % 2 = 0 then ⟨computed, other⟩ else ⟨other, computed⟩
/-- One nested FTS tree with explicit nested pads: `padL` in the leaf pad slot and `padZ` in the level-5 (heap 2/3)
fold's pad slot. Levels 0..4 keep the low half; level 5 keeps the high half. Returns the computed top node. -/
def childN (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (ends : List Digest)
    (padL padZ : Digest) : M Digest := do
  let leaf ← shortHash (leafInput k.val index j.val padL ends)
  let v ← (List.range 5).foldlM (fun value level =>
    let other := sibling w k.val j.val level
    let left := if j.val / 2 ^ level % 2 = 0 then value else other
    let right := if j.val / 2 ^ level % 2 = 0 then other else value
    shortHash (nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
      left (nodeHPad w k.val j.val level) (nodePad w k.val j.val level) right)) leaf
  let other := sibling w k.val j.val 5
  let left := if j.val / 2 ^ 5 % 2 = 0 then v else other
  let right := if j.val / 2 ^ 5 % 2 = 0 then other else v
  hashHi (nodeInput k.val index ((128 + j.val) / 2 ^ 6) left 0 padZ right)
/-- One nested FTS tree from the witness view `w`: the pads are read from `w` (the coordinate proof uses the view
of `w` with the previous tree's pair in the hand-off slots). -/
def childProgram (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) : M Digest :=
  childN w index k j ends (leafPad w k.val) (nodePad w k.val j.val 5)
end W9Machine.V3

/-! The arbitrary-witness source for the shared-path verifier. Chain addresses
retain raw child indices; only authentication paths use the rotated B placement. -/
namespace W9Machine.SharedV3
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.Research
abbrev WBytes := ClaudeWCT.W9.T3M.WBytes
abbrev PairRoot := Digest × Digest

def first (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)
def physical (coord raw : Nat) : Nat := SharedForest.physicalChild (first coord) raw
def lastLevel (coord : Nat) : Nat := if first coord then 4 else 5

def blkOff (child level : Nat) : Nat :=
  if level < 5 then SharedPathPacking.block child level else 784
def sibOff (child level : Nat) : Nat := blkOff child level + 48 * (1 - child / 2 ^ level % 2)
def nodePad (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (V3.regionOffset coord + blkOff child level + 32)
def nodeTw (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (V3.regionOffset coord + blkOff child level + 16)
/-- C1: the high tweak word of a packed node (levels `< 4`, heaps `8..127`) is witness memory (honest 0) for both
child directions; the verifier writes only the low tweak word there. Elsewhere 0. -/
def nodeHPad (w : WBytes) (coord child level : Nat) : BitVec 64 :=
  if level < 4 then (nodeTw w coord child level).extractLsb' 64 64 else 0
def sibling (w : WBytes) (coord child level : Nat) : Digest :=
  wdig w (V3.regionOffset coord + sibOff child level)
def leafPad (w : WBytes) (coord : Nat) : Digest := V3.leafPad w coord
/-- The incoming R pad of a region: the level-four window is pinned at 128, so its pad is at 160 (the previous
coordinate's hand-off writes 32 bytes at 144: junk low half on the level-four header, value on the pad). -/
def handR (coord : Nat) : Nat := if coord = 9 then 816 else 160
/-- Witness trim: the incoming leaf-pad (L) slot of a region; the virtual region 9 (offset `80 - 848`) has it at
`768` (witness offset 0, absolute `WIT = 4128`), every real region at `672`. -/
def handL (coord : Nat) : Nat := if coord = 9 then 768 else 672

/-- C1 (FTS Merkle half-swap): the value computed at child level `m` (the leaf for `m = 0`, the output of fold
level `m - 1` otherwise) is the high half of its hash output when it is a left input at a heap in `16..255`, i.e.
`m ≤ 3` and bit `m` of the physical child is clear. -/
def hiOut (child m : Nat) : Bool := decide (m ≤ 3) && decide (child / 2 ^ m % 2 = 0)
/-- The 16-byte node value of a public hash: high half if `hi`, low half otherwise. -/
def hashSel (hi : Bool) (input : HashInput) : M Digest := if hi then V3.hashHi input else shortHash input

def childInput (w : WBytes) (index coord physical : Nat) (padR value : Digest)
    (level : Nat) : HashInput :=
  let other := sibling w coord physical level
  let left := if physical / 2 ^ level % 2 = 0 then value else other
  let right := if physical / 2 ^ level % 2 = 0 then other else value
  V3.nodeInput coord index ((128 + physical) / 2 ^ (level + 1)) left
    (nodeHPad w coord physical level) (if level = 4 then padR else nodePad w coord physical level) right

/-- The side of the computed top node in the next pair: 0 = left (heap 2 for the final singleton), 1 = right. -/
def direction (coord child : Nat) : Nat := child / 2 ^ (lastLevel coord + 1) % 2

/-- A/B children keep the high half of their top node. The final singleton (merged "Cm", stage 2) keeps the HIGH
half of its left top node (heap 2, direction 0; the value lands on `WIT + 0`, the junk low half below the witness)
and the LOW half of its right top node (heap 3, direction 1; at `WIT + 48`). -/
def childN (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (ends : List Digest)
    (padL padR : Digest) : M Digest := do
  let leaf ← hashSel (hiOut (physical k.val raw.val) 0) (V3.leafInput k.val index raw.val padL ends)
  let j := physical k.val raw.val
  let n := lastLevel k.val
  let value ← (List.range n).foldlM
    (fun value level => hashSel (hiOut j (level + 1)) (childInput w index k.val j padR value level)) leaf
  if k.val = 8 then hashSel (decide (direction k.val j = 0)) (childInput w index k.val j padR value n)
  else V3.hashHi (childInput w index k.val j padR value n)

def childProgram (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (ends : List Digest) : M Digest :=
  childN w index k raw ends (leafPad w k.val) (nodePad w k.val (physical k.val raw.val) 4)

def topOtherOff (coord child : Nat) : Nat :=
  V3.regionOffset coord + (if direction coord child = 0 then handR (coord + 1) else handL (coord + 1)) - 848

def topOther (w : WBytes) (coord child : Nat) : Digest := wdig w (topOtherOff coord child)

def orderPair (coord child : Nat) (computed other : Digest) : PairRoot :=
  if direction coord child = 0 then (computed, other) else (other, computed)

def initialPair (w : WBytes) : PairRoot :=
  (leafPad w 0, wdig w (V3.regionOffset 0 + 160))

def coordinate (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (rank : Fin 666)
    (prev : PairRoot) : M PairRoot := do
  let ends ← V3.chainProgram w index k raw rank
  let computed ← childN w index k raw ends prev.1 prev.2
  pure (orderPair k.val (physical k.val raw.val) computed
    (topOther w k.val (physical k.val raw.val)))

def forest (w : WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 666) : M PairRoot :=
  (List.finRange 9).foldlM (fun prev k => coordinate w index k (raw k) (ranks k) prev) (initialPair w)

theorem physical_lt (coord raw : Nat) (h : raw < 128) : physical coord raw < 128 :=
  SharedForest.physicalChild_lt _ _ h

theorem lastLevel_cases (coord : Nat) : lastLevel coord = 4 ∨ lastLevel coord = 5 := by
  unfold lastLevel; split <;> simp

set_option maxRecDepth 100000 in
/-- The pinned level-four window: every child plan places level 4 at 128 (R pad at 160). -/
theorem block_four : ∀ j : Fin 128, SharedPathPacking.block j.val 4 = 128 := by
  decide +kernel

theorem pad4 (w : WBytes) (coord child : Nat) (h : child < 128) :
    nodePad w coord child 4 = wdig w (V3.regionOffset coord + 160) := by
  have hb : SharedPathPacking.block child 4 = 128 := block_four ⟨child, h⟩
  simp only [nodePad, blkOff, show 4 < 5 by decide, ↓reduceIte, hb]
end W9Machine.SharedV3
end
-- ==== merged from ClaudeWCT_W9_T3M_Witness_Encode ====
section

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (zeros layerBytes sibOff)
open SphincsSecurity (bytesLE)
/-- The H2 expander (two omitted signature bytes recovered by search), with the digest output. -/
def expandN (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) :=
  WCT9.expandS WCT9.digestAttemptLimit message pk sig
/-- The expander before H2 (the full signature), with the digest output. -/
def expandN0 (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) := do
  let some (counter, output) ← WCT9.digestSearch sig.rho message 0 WCT9.digestAttemptLimit | pure none
  let index := WCT9.digestIndex output
  let top ← WCT9.recoverFts sig index output
  let some (root, counters) ← WCT9.expandLayersBC sig index 4 (.pair top.1 top.2) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
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
/-- Witness stack (charge 86): an FTS chain pair (G chain `a` at `+16`, F chain `b` at `+40`, value at `+88`):
`zeros16 | v_a | zeros56 | v_b` (104 bytes). -/
def ftsPairBytes (a b : Digest) : List UInt8 := zeros 16 ++ bytesLE 16 a ++ zeros 56 ++ bytesLE 16 b
/-- Witness stack (charge 86): the FTS chain area `[320, 592)` of a region: chain 5's F block (value at 368), the pair
(G3 at 400, F4 at 424) and the pair (G1 at 504, F2 at 528). Chain 0's F block (592) ends in the leaf block. -/
def chainBytes (op : WCT9.Opening) : List UInt8 :=
  zeros 48 ++ bytesLE 16 (op.values 5) ++ ftsPairBytes (op.values 3) (op.values 4) ++
    ftsPairBytes (op.values 1) (op.values 2)
/-- Leaf block: `end0 | header slot (zero) | leaf pad | end1..end5`. -/
def leafBytes (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  bytesLE 16 (op.values 0) ++ zeros 16 ++ pad ++ (List.finRange 5).flatMap fun i => bytesLE 16 (op.values i.succ)
/-- Nested FTS (r1-1): the level-6 fold block `[left | header (zero) | pad | right]` at offset 784 of a region; the
supplied level-5 sibling is on the side opposite the computed value. -/
def topBlockBytes (child : Nat) (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  (if child / 2 ^ 5 % 2 = 1 then bytesLE 16 (op.path 5) else zeros 16) ++ zeros 16 ++ pad ++
    (if child / 2 ^ 5 % 2 = 0 then bytesLE 16 (op.path 5) else zeros 16)
/-- Region of coordinate `k` (848 bytes). `padL`/`padZ` hold coordinate `k - 1`'s supplied top sibling (16 bytes in
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
/-- Pairing stage 1: region 0 keeps its first 784 bytes (its level-5 window is removed) and is followed by
coordinate 0's level-5 sibling (`legacySib0`). -/
def wctBytes (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).reverse.flatMap fun k =>
    if k.val = 0 then
      (regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val)).take 784 ++
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
/-- C4: the 672-byte top path area (42 slots). -/
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
/-- Witness stack (charge 86): top pair `p` (104 bytes): a 16-byte gap, G chain `2p`'s block `[value | 0 ..]` and F
chain `2p+1`'s block starting 24 bytes later (value at the pair's offset 88). -/
def topPairBytes {lay : Layer} (ls : LayerSignature lay) (p : Nat) : List UInt8 :=
  zeros 16 ++ bytesLE 16 (lsValue ls (2 * p)) ++ zeros 56 ++ bytesLE 16 (lsValue ls (2 * p + 1))
/-- Witness stack (charge 86): the 2808-byte top chain area: pairs 26..0 (chain 0's pair highest). -/
def topChainBytes {lay : Layer} (ls : LayerSignature lay) : List UInt8 :=
  (List.range 27).reverse.flatMap (topPairBytes ls)
/-- C4: the top region is the plan-placed path area followed by the top chain blocks; a lower region is its
plan-placed path area (siblings, counter, row-tweak high word) followed by its chain blocks. -/
def layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then
    topPathBytes (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay) ++
      topChainBytes (w.signature.layers lay)
  else lowerPathBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
      (w.counters (Fin.ofNat 4 (lay.val - 1))) ++ lowerChainBytes (w.signature.layers lay)
def endpointBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  (List.finRange (chainCount lay)).flatMap fun i => bytesLE 16 ((sig.layers lay).values i)
/-- Witness stack (charge 86): leaf buffers 720 bytes apart (the 16-byte tails are removed): top (T51 "endpad")
`end0 | zeros16 | end1..end50 | zeros64` (896 bytes; #938: `zeros32 ++ 54 endpoints`), lower
`end0 | zeros16 | end1..end42 | zeros16` (720 bytes). -/
def leafBufferBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  if lay = 0 then (endpointBytes sig lay).take 16 ++ zeros 16 ++ (endpointBytes sig lay).drop 16 ++ zeros 64
  else (endpointBytes sig lay).take 16 ++ zeros 16 ++ (endpointBytes sig lay).drop 16 ++ zeros 16
def leafBuffersBytes (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 4).reverse.flatMap (leafBufferBytes sig)
def tailBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter ++ zeros 4
def witList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++ leafBuffersBytes w.signature ++ tailBytes w
def witEnc (N : HashOutput) (w : WCT9.Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))
def expandB (message : Message) (pk : Digest) (sig : WCT9.Signature) : M (Option WBytes) :=
  (Option.map fun x => witEnc x.1 x.2) <$> expandN message pk sig
def witDecP (N : HashOutput) (w : WBytes) : WCT9.Witness where
  signature :=
    { rho := wrho w
      openings := fun k =>
        ⟨fun t => wreveal w k.val t.val (WCT9.wordDigit (WCT9.rank N k) t),
          fun l => wsib w k.val (WCT9.child N k).val l.val⟩
      layers := fun lay =>
        ⟨fun i => wvalue w lay i.val, fun j => wpath w lay (route (WCT9.digestIndex N) lay).1 j.val⟩ }
  digestCounter := wdc w
  counters := fun lay => wbcCtr w (WCT9.digestIndex N) lay
def padDecP (N : HashOutput) (w : WBytes) : Pads where
  wctChain k t := wcpads w k.val t.val
  wctChainHigh k t := wcHeaderPad w k.val t.val
  wctMerkle k l := if l.val < 5 ∨ (l.val = 5 ∧ k.val = 0) then wmpad w k.val (WCT9.child N k).val l.val else 0
  wctMerkleHigh k l := wmhpad w k.val (WCT9.child N k).val l.val
  wctLeaf k := if k.val = 0 then wleafPad w 0 else 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := if j.val + 1 < height lay ∨ lay.val = 0 then
    wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val else 0
  chainHeader lay i := wchainHeaderPad w lay i.val
  bc lay := wbcPad w (WCT9.digestIndex N) lay
  bcRight := wbcRight w
  endpointMask lay i := wvalue w lay i.val ^^^ wdig w (leafBufferSlot lay i.val)
  merkleHigh lay j := if j.val + 1 < height lay ∨ lay.val = 0 then
    wmerkleHigh w lay (route (WCT9.digestIndex N) lay).1 j.val else 0
  topLeaf := 0  -- T51 ("endpad"): the top leaf has no witness pad (its leading block is end_0), see `WCT9.leafInputW`
  leafHigh lay := wleafHigh w lay
  bcHigh lay := wbcHigh w (WCT9.digestIndex N) lay ^^^ 1
@[simp] theorem valueP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) :
    valueP (witDecP N w).signature (padDecP N w) lay digits i = wvalueFor w lay digits i.val := by
  simp [valueP, witDecP, padDecP, wvalueFor, BitVec.xor_assoc]
def Shaped (N : HashOutput) (_w : WBytes) : Prop := WCT9.admissible N = true
instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some top ← wctP w N | pure false
  let some root ← layersBC w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def rejectTail (w : WBytes) (N : HashOutput) : M Bool :=
  if !gateOk N then pure false else (fun _ => false) <$> wctP w N
end ClaudeWCT.W9.T3M


namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open W9Machine
open SphincsSecurity (bytesLE)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Canonical coordinate views of the compact four-pair forest. -/
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

/-- Each reveal is present at the chain input and at the endpoint location used
by a zero-step chain. Authentication siblings use the installed shared layout. -/
def coordinateSlots (output : HashOutput) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (coord : Fin 9) : List (Nat × Digest) :=
  let physical := SharedV3.physical coord.val (rawChildFromOutput output coord).val
  let values := coordinateValues sig.forest coord
  let path := coordinatePath sig.forest coord
  ((List.finRange 6).flatMap fun i =>
    [(V3.chainOffset coord.val i.val + ClaudeWCT.W9.T3M.wctValueOff i.val, values i),
      (V3.regionOffset coord.val + V3.leafSlot i.val, values i)]) ++
    ((List.range (SharedV3.lastLevel coord.val + 1)).map fun level =>
      (V3.regionOffset coord.val + SharedV3.sibOff physical level, path level)) ++
    [(SharedV3.topOtherOff coord.val physical, path (SharedV3.lastLevel coord.val + 1))]

def forestSlots (output : HashOutput) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    List (Nat × Digest) := (List.finRange 9).flatMap (coordinateSlots output sig)

def slotByte (slots : List (Nat × Digest)) (offset : Nat) : UInt8 :=
  match slots.find? (fun p => decide (p.1 ≤ offset ∧ offset < p.1 + 16)) with
  | some p => (bytesLE 16 p.2).getD (offset - p.1) 0
  | none => 0

def forestBytes (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : List UInt8 :=
  (List.range 7664).map fun offset =>
    if 24 ≤ offset ∧ offset < 32 then (bytesLE 8 (1 : BitVec 64)).getD (offset - 24) 0
    else if 32 ≤ offset ∧ offset < 36 then (bytesLE 4 (witness.counters 3)).getD (offset - 32) 0
    else slotByte (forestSlots output witness.signature) offset

def mainWitness (witness : SigGolfCandidate.Research.SharedForest.Witness) : WCT9.Witness :=
  ⟨mainSignature witness.signature, witness.digestCounter, witness.counters⟩

/-- The encoded witness bytes without the choice hint (byte `choiceOff` is 0 there). -/
def witListBase (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : List UInt8 :=
  forestBytes output witness ++ (ClaudeWCT.W9.T3M.witList output (mainWitness witness)).drop 7664

/-- Configuration (1)+(2): the choice hint byte (`choiceByte witness.topHigh`) at `choiceOff`. -/
def witList (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : List UInt8 :=
  (witListBase output witness).set choiceOff (choiceByte witness.topHigh)

theorem witList_length (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) :
    (witList output witness).length = (witListBase output witness).length := by
  simp [witList]

theorem witList_getD_choice (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (h : choiceOff < (witListBase output witness).length) :
    (witList output witness).getD choiceOff 0 = choiceByte witness.topHigh := by
  simp [witList, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem witList_getD_ne (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    {i : Nat} (hi : i ≠ choiceOff) :
    (witList output witness).getD i 0 = (witListBase output witness).getD i 0 := by
  simp [witList, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hi)]

def witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : WBytes :=
  BitVec.ofNat _ (readLE (witList output witness))

/-! ### Top-bytes layer: the top node nonces (img-v6 / opus-topbytes)
The nonce of the top node of height `j + 1` (`j < 11`; the root has none) is a 64-bit counter stored in the Z pad of
its window: witness bytes `[merkleBlock 0 leaf j + 32, +8)` (`Pads.merkle 0 j`, read by the verifier as
`wmerklePad w 0 leaf j`), bytes `+8 .. +16` stay 0. The 22,012-byte layout already reserves these pads: in the 42-slot
top plan they are disjoint from every sibling, high-pad and other pad window (all 4096 leaves). `witListN` /
`witEncN` = `witList` / `witEnc` with these 11 words written. -/
/-- Witness offset of the nonce of the level-`j` top node. -/
def noncePos (output : HashOutput) (j : Nat) : Nat := merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 32
/-- The 8 little-endian bytes of nonce `j` (`nonces.getD j 0` mod `2^64`). -/
def nonceWord (nonces : List Nat) (j : Nat) : List UInt8 := bytesLE 8 (BitVec.ofNat 64 (nonces.getD j 0))
/-- Byte `i` with the nonces written (`b` = the nonce-free byte). -/
def nonceByte (output : HashOutput) (nonces : List Nat) (i : Nat) (b : UInt8) : UInt8 :=
  match (List.range 11).find? (fun j => decide (noncePos output j ≤ i ∧ i < noncePos output j + 8)) with
  | some j => (nonceWord nonces j).getD (i - noncePos output j) 0
  | none => b
def witListN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : List UInt8 :=
  (witList output witness).mapIdx fun i b => nonceByte output witness.topNonces i b
def witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : WBytes :=
  BitVec.ofNat _ (readLE (witListN output witness))

@[simp] theorem forestBytes_length (output : HashOutput)
    (witness : SigGolfCandidate.Research.SharedForest.Witness) : (forestBytes output witness).length = 7664 := by
  simp [forestBytes]

/-- Query-identical expansion retaining the digest output needed by the memory encoder (img-v6: mirrors
`SharedForest.expandFill`; `expand = expandFill ∘ normTop`). -/
def expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    M (Option (HashOutput × SigGolfCandidate.Research.SharedForest.Witness)) := do
  if sig.policyHints.toNat ≥ 7744 then return none
  let sig0 := fillTopSignature sig 0
  let some (counter, output) ← sharedDigestSearch sig0.rho message 0 WCT9.digestAttemptLimit | pure none
  let index := WCT9.digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) sig0.forest
  let some layers ← recoverHintedLayers sig0 index ((sig0.layers 0).path WCT9.topJ)
    4 (.pair forest.1 forest.2) (conditionalTopFloor output) | pure none
  if !policyHintsValid sig0.policyHints layers.digits layers.lows
      (conditionalCredit output) then return none
  if layers.root = pk then
    return some (output, ⟨sig0, counter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true), layers.nonces⟩)
  let some c ← WCT9.searchTop index layers.foldedTop ((sig0.layers 0).path WCT9.topJ) pk WCT9.searchFuel 1 | pure none
  pure (some (output, ⟨fillTopSignature sig0 c, counter, fun lay => layers.counters.getD lay.val 0,
    !(layers.lows.getD 0 true), layers.nonces⟩))

/-- img-v6: the expand output carries the top node nonces (`witEncN`; r3h HonestN). -/
def expandB (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    M (Option WBytes) := (Option.map fun p => witEncN p.1 p.2) <$> expandN message pk sig

/-- Invalid ranks stop at their coordinate after the preceding coordinates' queries. -/
def ftsStep (w : WBytes) (output : HashOutput) (state : Option (List (Digest × Digest)))
    (coord : Fin 9) : M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if ¬rawForestRank output coord.val < 563 then return none
  let pair ← SharedV3.coordinate w (WCT9.digestIndex output) coord (rawChildFromOutput output coord)
    (WCT9.embed (forestRank output coord.val)) (pairs.getLastD (SharedV3.initialPair w))
  pure (some (pairs ++ [pair]))

def ftsP (w : WBytes) (output : HashOutput) : M (Option (Digest × Digest)) := do
  if !(decide (output.toNat / 2^242 % 16384 < 791) : Bool) then return none
  let some pairs ← (List.finRange 9).foldlM (ftsStep w output) (some []) | pure none
  pure (some (pairs.getLastD (SharedV3.initialPair w)))

def verifyP (message : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some output ← digestP message w | pure false
  let some top ← ftsP w output | pure false
  let some root ← layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2) | pure false
  pure (root == pk)

theorem expandN_snd (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    Option.map Prod.snd <$> expandN message pk sig =
      SigGolfCandidate.Research.SharedForest.expandFill message pk sig := by
  unfold expandN SigGolfCandidate.Research.SharedForest.expandFill
  split
  · simp
  · try simp only [map_bind]
    apply bind_congr
    intro result
    cases result with
    | none => simp
    | some result =>
      obtain ⟨counter,output⟩ := result
      dsimp only
      try simp only [map_bind]
      apply bind_congr
      intro forest
      try simp only [map_bind]
      apply bind_congr
      intro layers
      cases layers with
      | none => simp
      | some layers =>
        dsimp only
        split
        · simp
        · split
          · simp
          · try simp only [map_bind]
            apply bind_congr
            intro completed
            cases completed <;> simp

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def plainFtsStep (w : WBytes) (output : HashOutput) (prev : Digest × Digest) (coord : Fin 9) :
    M (Digest × Digest) :=
  SharedV3.coordinate w (WCT9.digestIndex output) coord (rawChildFromOutput output coord)
    (WCT9.embed (forestRank output coord.val)) prev

theorem fts_fold_none (w : WBytes) (output : HashOutput) (xs : List (Fin 9)) :
    xs.foldlM (ftsStep w output) none = pure none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldlM_cons, ftsStep, pure_bind, ih]

theorem fts_fold_cons_good (w : WBytes) (output : HashOutput) (x : Fin 9) (xs : List (Fin 9))
    (pairs : List (Digest × Digest)) (hr : rawForestRank output x.val < 563) :
    (x::xs).foldlM (ftsStep w output) (some pairs) =
      (plainFtsStep w output (pairs.getLastD (SharedV3.initialPair w)) x >>= fun pair =>
        xs.foldlM (ftsStep w output) (some (pairs ++ [pair]))) := by
  simp only [List.foldlM_cons, ftsStep, hr, not_true_eq_false, if_false, bind_assoc, pure_bind]
  rfl

theorem fts_fold_success (answers : Answers) (w : WBytes) (output : HashOutput) :
    ∀ (xs : List (Fin 9)) (pairs found : List (Digest × Digest)),
    evalWithAnswerFn answers (xs.foldlM (ftsStep w output) (some pairs)) = some found →
    (∀ coord ∈ xs, rawForestRank output coord.val < 563) ∧
    evalWithAnswerFn answers (xs.foldlM (plainFtsStep w output) (pairs.getLastD (SharedV3.initialPair w))) =
      found.getLastD (SharedV3.initialPair w) ∧
    queried answers (xs.foldlM (plainFtsStep w output) (pairs.getLastD (SharedV3.initialPair w))) =
      queried answers (xs.foldlM (ftsStep w output) (some pairs)) := by
  intro xs
  induction xs with
  | nil =>
      intro pairs found h
      simp only [List.foldlM_nil, evalWithAnswerFn_pure, Option.some.injEq] at h
      subst found
      exact ⟨fun _ h => False.elim (List.not_mem_nil h), rfl, rfl⟩
  | cons x xs ih =>
      intro pairs found h
      have hr : rawForestRank output x.val < 563 := by
        by_contra hn
        simp only [List.foldlM_cons, ftsStep, hn, not_false_eq_true, if_true, pure_bind,
          fts_fold_none, evalWithAnswerFn_pure] at h
        cases h
      rw [fts_fold_cons_good w output x xs pairs hr, evalWithAnswerFn_bind] at h
      obtain ⟨hgood, heval, hqueries⟩ := ih (pairs ++ [evalWithAnswerFn answers
        (plainFtsStep w output (pairs.getLastD (SharedV3.initialPair w)) x)]) found h
      simp only [List.getLastD_concat] at heval hqueries
      refine ⟨fun coord hc => ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact hr
        · exact hgood coord hc
      · rw [List.foldlM_cons, evalWithAnswerFn_bind]
        exact heval
      · rw [List.foldlM_cons, queried_bind, fts_fold_cons_good w output x xs pairs hr, queried_bind]
        exact congrArg (fun tail => queried answers
          (plainFtsStep w output (pairs.getLastD (SharedV3.initialPair w)) x) ++ tail) hqueries

theorem ftsP_success (answers : Answers) (w : WBytes) (output : HashOutput) (top : Digest × Digest)
    (h : evalWithAnswerFn answers (ftsP w output) = some top) :
    output.toNat / 2^242 % 16384 < 791 ∧
    (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
    evalWithAnswerFn answers (SharedV3.forest w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) = top ∧
    queried answers (SharedV3.forest w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) =
      queried answers (ftsP w output) := by
  have hg : output.toNat / 2^242 % 16384 < 791 := by
    by_contra hn
    simp only [ftsP, hn, decide_false, Bool.not_false, ↓reduceIte, evalWithAnswerFn_pure] at h
    cases h
  simp only [ftsP, hg, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    evalWithAnswerFn_bind] at h
  cases hf : evalWithAnswerFn answers ((List.finRange 9).foldlM (ftsStep w output) (some [])) with
  | none => rw [hf] at h; simp at h
  | some pairs =>
      rw [hf, evalWithAnswerFn_pure, Option.some.injEq] at h
      obtain ⟨hr, he, hq⟩ := fts_fold_success answers w output (List.finRange 9) [] pairs hf
      refine ⟨hg, fun coord => hr coord (List.mem_finRange coord), ?_, ?_⟩
      · exact he.trans h
      · simp only [ftsP, hg, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          queried_bind, hf, queried_pure, List.append_nil]
        exact hq
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_split (answers : Answers) (message : Message) (pk : Digest) (w : WBytes)
    (h : evalWithAnswerFn answers (verifyP message pk w) = true) :
    ∃ output top,
      evalWithAnswerFn answers (digestP message w) = some output ∧
      evalWithAnswerFn answers (ftsP w output) = some top ∧
      evalWithAnswerFn answers (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2)) = some pk ∧
      (∀ q ∈ queried answers (digestP message w), q ∈ queried answers (verifyP message pk w)) ∧
      (∀ q ∈ queried answers (ftsP w output), q ∈ queried answers (verifyP message pk w)) ∧
      (∀ q ∈ queried answers (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2)),
        q ∈ queried answers (verifyP message pk w)) := by
  rw [verifyP, evalWithAnswerFn_bind] at h
  cases hd : evalWithAnswerFn answers (digestP message w) with
  | none => rw [hd] at h; simp at h
  | some output =>
      rw [hd, evalWithAnswerFn_bind] at h
      cases hf : evalWithAnswerFn answers (ftsP w output) with
      | none => rw [hf] at h; simp at h
      | some top =>
          rw [hf, evalWithAnswerFn_bind] at h
          cases hl : evalWithAnswerFn answers
            (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2)) with
          | none => rw [hl] at h; simp at h
          | some root =>
              rw [hl, evalWithAnswerFn_pure, beq_iff_eq] at h
              subst root
              have hq : queried answers (verifyP message pk w) =
                  queried answers (digestP message w) ++
                    (queried answers (ftsP w output) ++
                      queried answers (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2))) := by
                simp only [verifyP, queried_bind, hd, hf, hl, queried_pure, List.append_nil]
              refine ⟨output, top, (by first | exact hd | rfl), (by first | exact hf | rfl), (by first | exact hl | rfl), ?_, ?_, ?_⟩
              · intro q hqD
                rw [hq]
                exact List.mem_append_left _ hqD
              · intro q hqF
                rw [hq]
                exact List.mem_append_right _ (List.mem_append_left _ hqF)
              · intro q hqL
                rw [hq]
                exact List.mem_append_right _ (List.mem_append_right _ hqL)

theorem digestP_success (answers : Answers) (message : Message) (w : WBytes) (output : HashOutput)
    (h : evalWithAnswerFn answers (digestP message w) = some output) :
    (wdc w).toNat < WCT9.digestVerifyWindow ∧
    evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output ∧
    queried answers (digestP message w) =
      [.inl (.inr (pad64 (digestInput (wrho w) message (wdc w))))] := by
  unfold digestP at h ⊢
  split_ifs at h ⊢ with hc
  · simp at h
  · simp only [evalWithAnswerFn_map, Option.some.injEq] at h
    refine ⟨by omega, h, ?_⟩
    rw [map_eq_bind_pure_comp, queried_bind]
    rfl
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expandN_selections (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    sig.policyHints.toNat < 7744 ∧ ∃ counter result c,
      evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) =
        some (counter, output) ∧
      evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0) (WCT9.digestIndex output)
        (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)
        (conditionalTopFloor output)) = some result ∧
      policyHintsValid sig.policyHints result.digits result.lows
        (conditionalCredit output) = true ∧
      w.signature = fillTopSignature sig c ∧ w.digestCounter = counter ∧
      (∀ lay, w.counters lay = result.counters.getD lay.val 0) ∧ w.topHigh = !(result.lows.getD 0 true) := by
  unfold expandN at he
  simp only [show (fillTopSignature sig 0).rho = sig.rho from rfl,
    show (fillTopSignature sig 0).forest = sig.forest from rfl,
    show (fillTopSignature sig 0).policyHints = sig.policyHints from rfl] at he
  by_cases hh : sig.policyHints.toNat ≥ 7744
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  · simp only [hh, if_false, evalWithAnswerFn_bind] at he
    cases hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) with
    | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some found =>
        obtain ⟨counter, N⟩ := found
        simp only [hd, evalWithAnswerFn_bind] at he
        let forest := evalWithAnswerFn answers (recoverForest (WCT9.digestIndex N)
          (forestSelectionFromOutput N) (forestWordsFromOutput N) sig.forest)
        cases hr : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0)
          (WCT9.digestIndex N) (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
          (.pair forest.1 forest.2) (conditionalTopFloor N)) with
        | none =>
            dsimp only [forest] at hr
            simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
        | some result =>
            dsimp only [forest] at hr
            simp only [hr] at he
            by_cases hp : policyHintsValid sig.policyHints result.digits result.lows
                (conditionalCredit N) = true
            · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hk : result.root = pk
              · simp only [hk, if_true, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                exact ⟨by omega, counter, result, 0, (by first | exact hd | rfl), (by first | exact hr | rfl), hp, rfl, rfl, fun _ => rfl, rfl⟩
              · simp only [hk, if_false, evalWithAnswerFn_bind] at he
                cases hc : evalWithAnswerFn answers (WCT9.searchTop (WCT9.digestIndex N) result.foldedTop
                  (((fillTopSignature sig 0).layers 0).path WCT9.topJ) pk WCT9.searchFuel 1) with
                | none => simp only [hc, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    simp only [hc, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                    obtain ⟨rfl, rfl⟩ := he
                    exact ⟨by omega, counter, result, c, (by first | exact hd | rfl), (by first | exact hr | rfl), hp,
                      fillTopSignature_fillTopSignature sig 0 c, rfl, fun _ => rfl, rfl⟩
            · have hp0 := Bool.eq_false_of_not_eq_true hp
              simp only [hp0, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem forest_eq_of_coordinates (a b : ForestOpening)
    (hv : ∀ (coord : Fin 9) (i : Fin 6), coordinateValues a coord i = coordinateValues b coord i)
    (hp : ∀ (coord : Fin 9) level, level < (if coord.val < 8 ∧ coord.val % 2 = 0 then 6 else 7) →
      coordinatePath a coord level = coordinatePath b coord level) : a = b := by
  have hpair : a.pairs = b.pairs := by
    funext pair
    have hvalA : (a.pairs pair).firstValues = (b.pairs pair).firstValues := by
      funext i
      have h := hv ⟨2*pair.val,by have := pair.isLt;omega⟩ i
      fin_cases pair <;> simpa only [coordinateValues, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod,
        Nat.reduceDiv, dite_true, if_true] using h
    have hvalB : (a.pairs pair).secondValues = (b.pairs pair).secondValues := by
      funext i
      have h := hv ⟨2*pair.val+1,by have := pair.isLt;omega⟩ i
      fin_cases pair <;> simpa only [coordinateValues, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceMod, Nat.reduceDiv, dite_true, Nat.reduceEqDiff, if_false] using h
    have hpathA : (a.pairs pair).firstPath = (b.pairs pair).firstPath := by
      funext i
      have h := hp ⟨2*pair.val,by have := pair.isLt;omega⟩ i.val
        (by fin_cases pair <;> simpa using i.isLt)
      fin_cases pair <;> simpa [coordinatePath, Nat.mod_eq_of_lt i.isLt] using h
    have hpathB : (a.pairs pair).secondPath = (b.pairs pair).secondPath := by
      funext i
      have h := hp ⟨2*pair.val+1,by have := pair.isLt;omega⟩ i.val
        (by fin_cases pair <;> simpa using i.isLt)
      fin_cases pair <;> simpa [coordinatePath, Nat.mod_eq_of_lt i.isLt] using h
    cases ha : a.pairs pair
    cases hb : b.pairs pair
    simp only [ha,hb] at hvalA hvalB hpathA hpathB
    cases hvalA;cases hvalB;cases hpathA;cases hpathB;rfl
  have hsingleton : a.singleton = b.singleton := by
    have hval : a.singleton.values = b.singleton.values := by
      funext i
      exact hv 8 i
    have hpath : a.singleton.path = b.singleton.path := by
      funext i
      have h := hp 8 i.val (by simpa using i.isLt)
      simpa [coordinatePath, Nat.mod_eq_of_lt i.isLt] using h
    cases ha : a.singleton
    cases hb : b.singleton
    simp only [ha,hb] at hval hpath
    cases hval;cases hpath;rfl
  cases a
  cases b
  simp only [ForestOpening.mk.injEq]
  exact ⟨hpair,hsingleton⟩
end ClaudeWCT.W9.T3M.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Witness_TopLayer ====
section

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (chainP nodeHashP recoverLayerP)
/-- Campaign T51: on the top layer the skipped-copy reads see the same digits with or without the checksum digit
(the checksum chain 50 is never a safe zero copy). -/
theorem safeZeroCopy_top_append (answer : Digest) (c i : Nat) (hi : i < 51) :
    WCT9.safeZeroCopy 0 (dataDigits 0 answer ++ [c]) i ↔ WCT9.safeZeroCopy 0 (dataDigits 0 answer) i := by
  have hl := WCT9.dataDigits_top_length answer
  unfold WCT9.safeZeroCopy
  by_cases h50 : i < 50
  · rw [List.getD_append _ _ _ i (by omega), List.getD_append _ _ _ (i - 1) (by omega)]
  · have : i = 50 := by omega
    subst this
    simp
theorem wvalueFor_top_append (w : WBytes) (answer : Digest) (c i : Nat) (hi : i < 51) :
    wvalueFor w 0 (dataDigits 0 answer ++ [c]) i = wvalueFor w 0 (dataDigits 0 answer) i := by
  unfold wvalueFor
  rw [if_congr (safeZeroCopy_top_append answer c i hi) rfl rfl]
theorem topLayerP_of_decode (w : WBytes) (index : Nat) {answer : Digest} {digits : List Nat}
    (h : decode 0 answer = some digits) : topLayerP w index answer = some <$> layerP w index 0 digits := by
  unfold topLayerP
  rw [WCT9.topDecodeRun_of_decode h]
  have hd := (WCT9.decode_top_some h).2.2.2
  unfold layerP topChainP topFinishP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  have hv : ∀ i : Fin (chainCount 0), wvalueFor w 0 (dataDigits 0 answer) i.val = wvalueFor w 0 digits i.val := by
    intro i
    rw [hd, wvalueFor_top_append w answer _ i.val i.isLt]
  simp only [hv]

theorem topLayerP_of_decode_none (w : WBytes) (index : Nat) {answer : Digest} (h : decode 0 answer = none) :
    topLayerP w index answer =
      (fun _ => none) <$> WCT9.topRejectChains (topChainP w (route index 0).2 (route index 0).1 (dataDigits 0 answer)) answer := by
  unfold topLayerP
  exact WCT9.topDecodeRun_of_decode_none h
theorem eval_topLayerP_none (answers : QueryImpl Spec Id) (w : WBytes) (index : Nat) {answer : Digest}
    (h : decode 0 answer = none) : evalWithAnswerFn answers (topLayerP w index answer) = none :=
  WCT9.eval_topDecodeRun_none answers h
theorem decode_of_eval_topLayerP (answers : QueryImpl Spec Id) (w : WBytes) (index : Nat) {answer out : Digest}
    (h : evalWithAnswerFn answers (topLayerP w index answer) = some out) :
    ∃ digits, decode 0 answer = some digits :=
  WCT9.decode_of_eval_topDecodeRun answers h
theorem eval_verifyTopP_none (answers : QueryImpl Spec Id) (sig : WCT9.Signature) (pads : Pads) (index : Nat)
    {answer : Digest} (h : decode 0 answer = none) :
    evalWithAnswerFn answers (verifyTopP sig pads index answer) = none :=
  WCT9.eval_topDecodeRun_none answers h
end ClaudeWCT.W9.T3M
end
-- ==== merged from ClaudeWCT_W9_T3M_Witness_Honest ====
section

section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (chainP nodeHashP recoverLayerP chainP_zero_route nodeHashP_zero bytesLE_zero16)
open SphincsSecurity (bytesLE)
set_option linter.unusedSimpArgs false
@[simp] theorem Pads.zero_wctChain (k : WCT9.Coord) (t : Fin 6) : (0 : Pads).wctChain k t = (0, 0) := rfl
@[simp] theorem Pads.zero_wctChainHigh (k : WCT9.Coord) (t : Fin 6) : (0 : Pads).wctChainHigh k t = 0 := rfl
@[simp] theorem Pads.zero_wctMerkle (k : WCT9.Coord) (l : Fin 7) : (0 : Pads).wctMerkle k l = 0 := rfl
@[simp] theorem Pads.zero_wctMerkleHigh (k : WCT9.Coord) (l : Fin 7) : (0 : Pads).wctMerkleHigh k l = 0 := rfl
@[simp] theorem Pads.zero_wctLeaf (k : WCT9.Coord) : (0 : Pads).wctLeaf k = 0 := rfl
@[simp] theorem Pads.zero_chain' (lay : Layer) (i : Fin (chainCount lay)) : (0 : Pads).chain lay i = (0, 0) := rfl
@[simp] theorem Pads.zero_merkle' (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkle lay j = 0 := rfl
@[simp] theorem Pads.zero_chainHeader (lay : Layer) (i : Fin (chainCount lay)) :
    (0 : Pads).chainHeader lay i = 0 := rfl
@[simp] theorem Pads.zero_bc (lay : Layer) : (0 : Pads).bc lay = 0 := rfl
@[simp] theorem Pads.zero_bcRight : (0 : Pads).bcRight = 0 := rfl
@[simp] theorem Pads.zero_toT3 : (0 : Pads).toT3 = 0 := rfl
@[simp] theorem Pads.zero_merkleHigh (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkleHigh lay j = 0 := rfl
@[simp] theorem Pads.zero_topLeaf : (0 : Pads).topLeaf = 0 := rfl
@[simp] theorem Pads.zero_leafHigh (lay : Layer) : (0 : Pads).leafHigh lay = 0 := rfl
@[simp] theorem Pads.zero_bcHigh (lay : Layer) : (0 : Pads).bcHigh lay ^^^ 1 = 1 := by
  show (0 : BitVec 64) ^^^ 1 = 1; decide
/-- C3: the verifier chain with zero pads on a routed leaf is the chain of the current scheme. -/
theorem chainPW_zero_route (index : Nat) (lay : Layer) (i : Fin (chainCount lay))
    (digit : Nat) (value : Digest) (hindex : index < 2 ^ 31) :
    chainPW lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) 0 0 0 value =
    WCT9.chainW lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) value := by
  have hi := i.isLt
  have ht : (route index lay).2 < 2 ^ 31 := by fin_cases lay <;> simp [route, height] <;> omega
  have hl : (route index lay).1 < 4096 := by fin_cases lay <;> simp [route, height] <;> omega
  have hi64 : i.val < 64 := by fin_cases lay <;> simp [chainCount] at hi <;> omega
  have hm : maxDigit lay i.val ≤ 7 := by unfold maxDigit; split_ifs <;> decide
  unfold chainPW WCT9.chainW
  apply WCT9.foldlM_congr_of_mem
  intro s hs v
  have hs8 : s < 8 := by have := List.mem_range'_1.mp hs; omega
  rw [chainInputW_eq_zero _ _ _ _ _ _ ht hl hi64 hs8]
theorem leafHashW_zero (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    WCT9.leafHashW lay tree leaf 0 0 ends = WCT9.lowerLeafHash lay tree leaf ends := rfl
theorem wctChainInputP_zero (index coord child t step : Nat) (value : Digest) :
    wctChainInputP index coord child t step 0 0 0 value = WCT9.chainInput index coord child t step value := by
  simp only [wctChainInputP, WCT9.chainInput, WCT9.ftsChainHeader, bytesLE_zero16]
/-- Witness stack: zero pads give the paired FTS step input of the scheme (either format). -/
theorem wctChainInputPW_zero (index coord child t step : Nat) (value : Digest) :
    wctChainInputPW index coord child t step 0 0 0 value = WCT9.ftsChainInputW index coord child t step value := by
  unfold wctChainInputPW WCT9.ftsChainInputW
  split
  · simp only [WCT9.ftsChainHeader, bytesLE_zero16, zero16]
  · exact wctChainInputP_zero index coord child t step value
@[simp] theorem wctChainP_zero (index coord child t start count : Nat) (value : Digest) :
    wctChainP index coord child t start count 0 0 0 value = WCT9.chain index coord child t start count value := by
  simp only [wctChainP, WCT9.chain, wctChainInputPW_zero]
@[simp] theorem wctNodeHashP_zero (coord index heap : Nat) (left right : Digest) :
    wctNodeHashP coord index heap left 0 0 right = WCT9.wctNodeHash coord index heap left right := by
  rw [WCT9.wctNodeHash_eq_short]
  simp only [wctNodeHashP, SigGolfCandidate.T3M.SecurityInputs.nodeInputPH_zero]
  rfl
theorem recoverCoordinateP_zero (sig : WCT9.Signature) (index : Nat) (output : HashOutput) (coord : WCT9.Coord)
    (prev : Digest × Digest) :
    recoverCoordinateP sig 0 index output coord prev = WCT9.recoverCoordinate sig index output coord prev := by
  simp only [recoverCoordinateP, WCT9.recoverCoordinate, Pads.zero_wctChain, Pads.zero_wctChainHigh,
    Pads.zero_wctMerkle, Pads.zero_wctMerkleHigh, Pads.zero_wctLeaf, WCT9.leafHashP_zero, wctChainP_zero,
    wctNodeHashP_zero]
theorem recoverFtsP_zero (sig : WCT9.Signature) (index : Nat) (output : HashOutput) :
    recoverFtsP sig 0 index output = WCT9.recoverFts sig index output := by
  unfold recoverFtsP WCT9.recoverFts WCT9.recoverFtsFrom
  simp only [recoverCoordinateP_zero]
  rfl
theorem shortHash_congr {x y : HashInput} (h : pad64 x = pad64 y) : shortHash x = shortHash y := by
  have hp : publicHash x = publicHash y := by
    unfold publicHash
    rw [h]
  unfold shortHash
  rw [hp]
theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32) :
    pad64 (encodingInput lay tree leaf root counter) = WCT9.pairEncodingInputP lay tree leaf root 0 counter 0 := by
  have h12 : bytesLE 12 (0 : BitVec 96) = List.replicate 12 0 := by decide
  unfold encodingInput WCT9.pairEncodingInputP pad64
  simp only [List.length_append, SphincsSecurity.bytesLE_length, bytesLE_zero16, h12, zero16, List.append_assoc,
    List.replicate_append_replicate]
theorem encodingHash_layerEncodingInputP_zero (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter 0 0 1) =
      ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter) := by
  cases msg with
  | forest root =>
      show WCT9.encodingHash lay (WCT9.pairEncodingInputP lay tree leaf root 0 counter 0) =
        WCT9.encodingHash lay (encodingInput lay tree leaf root counter)
      apply WCT9.encodingHash_congr
      have hlen : (WCT9.pairEncodingInputP lay tree leaf root 0 counter 0).length = 64 := by
        simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
      rw [pad64_encodingInput]
      simp only [pad64, hlen]
      simp
  | pair left right => rfl
theorem recoverLayerPairP_zero (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hindex : index < 2 ^ 31) (hlay : lay ≠ 0) :
    recoverLayerPairP sig 0 index lay digits = WCT9.recoverLayerPair sig index lay digits := by
  have hv : lay.val ≠ 0 := fun e => hlay (Fin.ext e)
  simp only [recoverLayerPairP, WCT9.recoverLayerPair, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    chainPW_zero_route _ _ _ _ _ hindex, Pads.zero_merkle', Pads.zero_merkleHigh, Pads.zero_topLeaf,
    Pads.zero_leafHigh, leafHashW_zero, ← WCT9.lowerNodeHash_eqP hv]
private theorem mapM_congr_guard {α β : Type} {f g : α → M β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
      rw [List.mapM_cons, List.mapM_cons, h x (by simp),
        mapM_congr_guard l (fun y hy => h y (by simp [hy]))]
theorem recoverLayerPairGuardP_zero (sig : WCT9.Signature) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) (hindex : index < 2 ^ 31) (hlay : lay ≠ 0) :
    recoverLayerPairGuardP sig 0 index lay answer digits =
      WCT9.recoverLayerPairGuard sig index lay answer digits := by
  simp only [recoverLayerPairGuardP, WCT9.recoverLayerPairGuard, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    recoverLayerPairP_zero _ _ _ _ hindex hlay]
  unfold WCT9.lowerGuardedRun
  split_ifs
  · rfl
  · apply congrArg (fun p : M (List Digest) => p >>= fun _ => pure none)
    apply mapM_congr_guard
    intro i hi
    have hi' : i < chainCount lay := by
      have hb := WCT9.lowerFirstBad_le answer
      have := List.mem_range.mp hi
      have hc : 43 ≤ chainCount lay := by fin_cases lay <;> decide
      omega
    exact chainPW_zero_route index lay ⟨i, hi'⟩ _ _ hindex
/-- Witness stack: the zero-padded top verifier chain is the scheme's top chain (`T3.layChain 0`). -/
theorem chainPW_zero_top (index : Nat) (i : Fin (chainCount 0)) (digit : Nat) (value : Digest)
    (hindex : index < 2 ^ 31) :
    chainPW 0 (route index 0).2 (route index 0).1 i.val digit (maxDigit 0 i.val - digit) 0 0 0 value =
      layChain 0 (route index 0).2 (route index 0).1 i.val digit (maxDigit 0 i.val - digit) value := by
  have ht : (route index 0).2 = 0 := by
    simp only [route, height, Matrix.cons_val_zero]
    exact Nat.div_eq_of_lt (lt_of_lt_of_eq hindex (by norm_num))
  rw [chainPW_zero_route index 0 i digit value hindex, layChain_top, ht, WCT9.chainW_top_eq]
theorem verifyTopP_zero (sig : WCT9.Signature) (index : Nat) (answer : Digest) (hindex : index < 2 ^ 31) :
    verifyTopP sig 0 index answer = WCT9.verifyTop sig index answer := by
  simp only [verifyTopP, WCT9.verifyTop, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    chainPW_zero_top _ _ _ _ hindex, Pads.zero_merkle', Pads.zero_merkleHigh, ← WCT9.lowerNodeHash_eqP',
    Fin.val_zero, WCT9.lowerNodeHash_top, Pads.zero_topLeaf, Pads.zero_leafHigh, leafHashW_zero,
    WCT9.lowerLeafHash_top]
theorem verifyLayersBCP_zero (w : WCT9.Witness) (index : Nat) (hindex : index < 2 ^ 31) : ∀ n, n ≤ 4 → ∀ msg,
    verifyLayersBCP w 0 index n msg = WCT9.verifyLayersBC w index n msg := by
  intro n
  induction n with
  | zero => intro _ msg; rfl
  | succ n ih =>
      intro hn msg
      have hguard : n ≠ 0 → ∀ answer digits, recoverLayerPairGuardP w.signature 0 index (Fin.ofNat 4 n) answer digits =
          WCT9.recoverLayerPairGuard w.signature index (Fin.ofNat 4 n) answer digits := by
        intro h0 answer digits
        apply recoverLayerPairGuardP_zero _ _ _ _ _ hindex
        intro e; have := congrArg Fin.val e; simp [Fin.val_ofNat] at this; omega
      by_cases h0 : n = 0
      · simp only [verifyLayersBCP, WCT9.verifyLayersBC, Pads.zero_bc, Pads.zero_bcRight, Pads.zero_bcHigh,
          encodingHash_layerEncodingInputP_zero, verifyTopP_zero _ _ _ hindex, h0, ↓reduceIte]
      · simp only [verifyLayersBCP, WCT9.verifyLayersBC, Pads.zero_bc, Pads.zero_bcRight, Pads.zero_bcHigh,
          encodingHash_layerEncodingInputP_zero, hguard h0, ih (by omega), h0, ↓reduceIte]
        rfl
theorem verifyPads_zero (m : Message) (pk : Digest) (w : WCT9.Witness) :
    verifyPads m pk w 0 = WCT9.Rev3.verify m pk w := by
  unfold verifyPads verifyPadsTail WCT9.Rev3.verify WCT9.verifyWith
  simp only [recoverFtsP_zero, verifyLayersBCP_zero _ _ (WCT9.digestIndex_lt _) 4 le_rfl]
  rfl
theorem layerPairP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat) :
    layerPairP w (WCT9.digestIndex N) lay digits =
      recoverLayerPairP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) lay digits := by
  unfold layerPairP recoverLayerPairP
  have hm : ∀ j : Fin (height lay - 1),
      (padDecP N w).merkle lay (Fin.castLE (Nat.sub_le _ _) j) =
        wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val := by
    intro j
    simp only [padDecP, Fin.val_castLE]
    rw [if_pos (Or.inl (by omega))]
  have hmh : ∀ j : Fin (height lay - 1),
      (padDecP N w).merkleHigh lay (Fin.castLE (Nat.sub_le _ _) j) =
        wmerkleHigh w lay (route (WCT9.digestIndex N) lay).1 j.val := by
    intro j
    simp only [padDecP, Fin.val_castLE]
    rw [if_pos (by omega)]
  simp only [hm, hmh, valueP_dec]
  rfl
theorem layerGuardedPairP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (answer : Digest)
    (digits : List Nat) :
    layerGuardedPairP w (WCT9.digestIndex N) lay answer digits =
      recoverLayerPairGuardP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) lay answer digits := by
  unfold layerGuardedPairP recoverLayerPairGuardP layerChainP
  rw [layerPairP_dec N w]
  simp only [valueP_dec]
  rfl
theorem topLayerP_dec (N : HashOutput) (w : WBytes) (answer : Digest) :
    topLayerP w (WCT9.digestIndex N) answer =
      verifyTopP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) answer := by
  unfold topLayerP verifyTopP topChainP topFinishP
  simp only [valueP_dec]
  simp only [padDecP, witDecP, Fin.val_zero, or_true, ↓reduceIte]
  rfl

theorem padDecP_bcHigh (N : HashOutput) (w : WBytes) (lay : Layer) :
    (padDecP N w).bcHigh lay ^^^ 1 = wbcHigh w (WCT9.digestIndex N) lay := by
  simp only [padDecP, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
theorem layersBC_dec (N : HashOutput) (w : WBytes) : ∀ n msg,
    layersBC w (WCT9.digestIndex N) n msg =
      verifyLayersBCP (witDecP N w) (padDecP N w) (WCT9.digestIndex N) n msg := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
      intro msg
      unfold layersBC verifyLayersBCP
      simp only [padDecP_bcHigh]
      by_cases hn : n = 0
      · subst n
        simp only [if_true, topLayerP_dec N w]
        rfl
      · simp only [hn, if_false, layerGuardedPairP_dec N w, ih]
        rfl
theorem wctStep_none (w : WBytes) (N : HashOutput) (coord : WCT9.Coord) : wctStep w N none coord = pure none := rfl
theorem foldlM_wctStep_none (w : WBytes) (N : HashOutput) :
    ∀ l : List WCT9.Coord, l.foldlM (wctStep w N) none = pure none
  | [] => rfl
  | k :: ks => by rw [List.foldlM_cons, wctStep_none, pure_bind, foldlM_wctStep_none w N ks]
theorem wctCoordP_dec (N : HashOutput) (w : WBytes) (index : Nat) (coord : WCT9.Coord) (prev : Digest × Digest) :
    wctCoordP w index coord (WCT9.child N coord) (WCT9.rank N coord) prev =
      recoverCoordinateP (witDecP N w).signature (padDecP N w) index N coord prev := by
  unfold wctCoordP recoverCoordinateP
  have hm : ∀ level : Fin 5,
      (padDecP N w).wctMerkle coord (Fin.castLE (by decide) level) =
        wmpad w coord.val (WCT9.child N coord).val level.val := by
    intro level
    simp only [padDecP, Fin.val_castLE]
    rw [if_pos (Or.inl level.isLt)]
  have hh : ∀ level : Fin 5,
      (padDecP N w).wctMerkleHigh coord (Fin.castLE (by decide) level) =
        wmhpad w coord.val (WCT9.child N coord).val level.val := by
    intro level
    simp only [padDecP, Fin.val_castLE]
  simp only [hm, hh]
  rfl
/-- The decoded pads of coordinate 0 are the free witness slots read by `wctP`. -/
theorem wmpad_five (w : WBytes) {k : Nat} (hk : k ≠ 0) (c : Nat) : wmpad w k c 5 = wdig w (regionBase k + 816) := by
  unfold wmpad authPadOff; rw [if_neg (by omega), authBase_five]
/-- Pairing stage 1: coordinate 0's legacy level-5 pad is read from `legacyPad0`. -/
theorem wmpad_zero_five (w : WBytes) (c : Nat) : wmpad w 0 c 5 = wdig w legacyPad0 := by
  unfold wmpad; rw [if_pos ⟨rfl, rfl⟩]
theorem padDecP_start (N : HashOutput) (w : WBytes) : (padDecP N w).start = wctStart w := by
  simp [Pads.start, wctStart, padDecP, wmpad_zero_five]
theorem foldlM_wctStep_ok (w : WBytes) (N : HashOutput) (hok : ∀ k, fieldOk N k = true) :
    ∀ (l : List WCT9.Coord) (acc : List (Digest × Digest)),
      l.foldlM (wctStep w N) (some acc) =
        some <$> l.foldlM (fun (pairs : List (Digest × Digest)) k => do
          let pair ← wctCoordP w (WCT9.digestIndex N) k (WCT9.child N k) (WCT9.rank N k)
            (WCT9.prevPair (wctStart w) pairs)
          pure (pairs ++ [pair])) acc
  | [], acc => by simp
  | k :: ks, acc => by
      rw [List.foldlM_cons, List.foldlM_cons]
      have hs : wctStep w N (some acc) k =
          (fun pair => some (acc ++ [pair])) <$>
            wctCoordP w (WCT9.digestIndex N) k (WCT9.child N k) (WCT9.rank N k) (WCT9.prevPair (wctStart w) acc) := by
        simp only [wctStep, hok k, Bool.not_true, Bool.false_eq_true, if_false, map_eq_bind_pure_comp]
        rfl
      rw [hs, bind_map_left, map_bind, bind_assoc]
      congr 1; funext pair
      rw [foldlM_wctStep_ok w N hok ks (acc ++ [pair]), pure_bind]
theorem fieldOk_of_admissible {N : HashOutput} (h : WCT9.admissible N = true) (k : WCT9.Coord) :
    fieldOk N k = true := by
  have := ((WCT9.admissible_iff N).1 h).2 k
  exact decide_eq_true this
theorem gateOk_of_admissible {N : HashOutput} (h : WCT9.admissible N = true) : gateOk N = true := by
  unfold gateOk
  apply decide_eq_true
  simpa only [WCT9.gateLimit] using ((WCT9.admissible_iff N).1 h).1
theorem admissible_of_ok {N : HashOutput} (hg : gateOk N = true) (hf : ∀ k, fieldOk N k = true) :
    WCT9.admissible N = true := by
  unfold gateOk at hg
  have hgate := of_decide_eq_true hg
  rw [WCT9.admissible_iff]
  refine ⟨by simpa only [WCT9.gateLimit] using hgate, fun k => ?_⟩
  have := hf k
  exact of_decide_eq_true this
theorem wctP_shaped (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    wctP w N = some <$> recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N := by
  unfold wctP recoverFtsP
  rw [foldlM_wctStep_ok w N (fieldOk_of_admissible h) _ [], bind_map_left, map_bind, padDecP_start]
  simp only [wctCoordP_dec, map_pure]
theorem foldlM_wctStep_bad (w : WBytes) (N : HashOutput) :
    ∀ (l : List WCT9.Coord) (st : Option (List (Digest × Digest))),
    (∃ k ∈ l, fieldOk N k = false) → ∀ r ∈ support (l.foldlM (wctStep w N) st), r = none := by
  intro l
  induction l with
  | nil => intro st h; obtain ⟨k, hk, -⟩ := h; simp at hk
  | cons k ks ih =>
      intro st h r hr
      rw [List.foldlM_cons, mem_support_bind_iff] at hr
      obtain ⟨s, hs, hr⟩ := hr
      by_cases hk : fieldOk N k = false
      · have h0 : wctStep w N st k = pure none := by
          rcases st with _ | roots
          · rfl
          · simp only [wctStep, hk, Bool.not_false, if_true]
        rw [h0] at hs
        simp only [support_pure, Set.mem_singleton_iff] at hs
        subst hs
        rw [foldlM_wctStep_none] at hr
        simpa using hr
      · obtain ⟨k', hk', hbad⟩ := h
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact absurd hbad hk
        · exact ih s ⟨k', hk', hbad⟩ r hr
theorem wctP_bad (w : WBytes) (N : HashOutput) (h : ∃ k, fieldOk N k = false) :
    ∀ r ∈ support (wctP w N), r = none := by
  intro r hr
  unfold wctP at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨s, hs, hr⟩ := hr
  obtain ⟨k, hk⟩ := h
  have := foldlM_wctStep_bad w N _ _ ⟨k, List.mem_finRange k, hk⟩ s hs
  subst this
  simpa using hr
theorem verifyP_eq_tail (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w = ((do
      let some N ← digestP m w | pure false
      verifyTailP pk w N) : M Bool) := rfl
theorem verifyTailP_shaped (pk : Digest) (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    verifyTailP pk w N = verifyPadsTail pk N (witDecP N w) (padDecP N w) := by
  unfold verifyTailP verifyPadsTail
  have hg := gateOk_of_admissible h
  have ha : WCT9.admissible N = true := h
  simp only [hg, ha, Bool.not_true, Bool.false_eq_true, if_false]
  rw [wctP_shaped N w h, bind_map_left]
  refine bind_congr (fun root => ?_)
  dsimp only
  rw [layersBC_dec]
  try rfl
theorem rejectTail_false (w : WBytes) (N : HashOutput) : ∀ b ∈ support (rejectTail w N), b = false := by
  intro b hb
  unfold rejectTail at hb
  split at hb
  · simpa using hb
  · rw [support_map] at hb
    obtain ⟨_, _, rfl⟩ := hb
    rfl
theorem verifyP_normal (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w =
      if (wdc w).toNat ≥ WCT9.digestVerifyWindow then pure false else (do
        let N ← digest (wrho w) m (wdc w)
        if Shaped N w then verifyPadsTail pk N (witDecP N w) (padDecP N w) else rejectTail w N) := by
  rw [verifyP_eq_tail]
  unfold digestP
  split_ifs with h
  · simp
  · rw [bind_map_left]
    refine bind_congr (fun N => ?_)
    dsimp only
    split_ifs with hS
    · exact verifyTailP_shaped pk N w hS
    · unfold verifyTailP rejectTail
      by_cases hg : gateOk N = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, if_false]
        have hbad : ∃ k, fieldOk N k = false := by
          by_contra hall
          push Not at hall
          exact hS (admissible_of_ok hg fun k => by simpa using hall k)
        rw [map_eq_bind_pure_comp]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro r hr
        rw [wctP_bad w N hbad r hr]
        rfl
      · simp [hg]
end ClaudeWCT.W9.T3M
end
section
namespace ClaudeWCT.W9.T3M
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
theorem ftsPairBytes_length (a b : Digest) : (ftsPairBytes a b).length = 104 := by
  simp [ftsPairBytes, zeros, bytesLE_length]
theorem chainBytes_length (op : WCT9.Opening) : (chainBytes op).length = 272 := by
  simp [chainBytes, zeros, bytesLE_length, ftsPairBytes_length]
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
    (hZ : padZ.length = 16) : (regionBytes c op padL padZ).length = 848 := by
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
def regionLen (k : WCT9.Coord) : Nat := if k.val = 0 then 800 else 848
/-- One cell of `wctBytes`: the region of coordinate `k`; pairing stage 1: for `k = 0` its first 784 bytes followed by
coordinate 0's level-5 sibling (`legacySib0`). -/
def regionCell (N : HashOutput) (sig : WCT9.Signature) (k : WCT9.Coord) : List UInt8 :=
  if k.val = 0 then
    (regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val)).take 784 ++
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
    ((((List.finRange 9).reverse).take (8 - k.val)).map regionLen).sum = 848 * (8 - k.val) := by
  fin_cases k <;> decide
theorem wctBytes_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytes N sig).length = 7584 := by
  rw [wctBytes_eq, List.length_flatMap, List.map_congr_left (fun k _ => regionCell_length N sig k)]
  decide
theorem height_pos' (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem lowerPathBytes_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (lowerPathBytes lay leaf ls ctr).length = 16 * pathSlots lay := by
  simp [lowerPathBytes]
theorem topPathBytes_length {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) :
    (topPathBytes leaf ls).length = 16 * pathSlots lay := by
  simp [topPathBytes]
theorem pairBytes_length {lay : Layer} (ls : LayerSignature lay) (p : Nat) : (pairBytes ls p).length = 104 := by
  simp [pairBytes, zeros, bytesLE_length]
theorem lowerChainBytes_length {lay : Layer} (ls : LayerSignature lay) : (lowerChainBytes ls).length = 2248 := by
  simp only [lowerChainBytes, List.length_append, List.length_flatMap, pairBytes_length, zeros_len, bytesLE_length]
  simp
theorem topPairBytes_length {lay : Layer} (ls : LayerSignature lay) (p : Nat) : (topPairBytes ls p).length = 104 := by
  simp [topPairBytes, zeros, bytesLE_length]
theorem topChainBytes_length {lay : Layer} (ls : LayerSignature lay) : (topChainBytes ls).length = 2808 := by
  simp [topChainBytes, List.length_flatMap, topPairBytes_length]
theorem layerRegion_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegion N w lay).length = 16 * pathSlots lay + chainArea lay := by
  unfold layerRegion chainArea; split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    rw [List.length_append, topPathBytes_length, topChainBytes_length]
  · rw [List.length_append, lowerPathBytes_length, lowerChainBytes_length]
theorem endpointBytes_length (sig : WCT9.Signature) (lay : Layer) :
    (endpointBytes sig lay).length = 16 * chainCount lay := by
  simp [endpointBytes, List.length_flatMap, bytesLE_length, List.sum_replicate, Nat.mul_comm]
def leafBufferLen (lay : Layer) : Nat := if lay = 0 then 896 else 720
theorem leafBufferBytes_length (sig : WCT9.Signature) (lay : Layer) :
    (leafBufferBytes sig lay).length = leafBufferLen lay := by
  fin_cases lay <;> simp [leafBufferBytes, leafBufferLen, endpointBytes_length, zeros, chainCount]
theorem leafBuffersBytes_length (sig : WCT9.Signature) : (leafBuffersBytes sig).length = 3056 := by
  simp only [leafBuffersBytes, List.length_flatMap, leafBufferBytes_length]
  decide
theorem tailBytes_length (w : WCT9.Witness) : (tailBytes w).length = 32 := by
  simp [tailBytes, zeros, bytesLE_length]
theorem layers_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegion N w)).length = 11264 := by
  simp only [List.length_flatMap, layerRegion_length]
  decide
theorem witList_length_eq (N : HashOutput) (w : WCT9.Witness) : (witList N w).length = 22016 := by
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
machine still writes whole words); the witness is its first `wsize = 22012` bytes. -/
theorem witList_readLE_lt (N : HashOutput) (w : WCT9.Witness) : readLE (witList N w) < 2 ^ (8 * 22012) := by
  have hsplit : witList N w = ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)) ++
      zeros 4 := by
    simp only [witList, tailBytes, List.append_assoc]
  have hlen : ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)).length =
      22012 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, leafBuffersBytes_length,
      bytesLE_length, zeros, List.length_replicate]
  have hz : readLE (zeros 4) = 0 := by decide
  have h256 : ∀ n : Nat, (256 : Nat) ^ n = 2 ^ (8 * n) := fun n => by rw [pow_mul]; norm_num
  rw [hsplit, readLE_append, hz, Nat.mul_zero, Nat.add_zero, ← h256, ← hlen]
  exact SigGolfCandidate.T3M.readLE_lt _
theorem wdig_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wdig (witEnc N w) off = readDigest (window (witList N w) off 16) := by
  unfold wdig witEnc readDigest window
  exact extract_readLE_lt (witList N w) 22012 (witList_readLE_lt N w) off 16
theorem wle32_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wle32 (witEnc N w) off = BitVec.ofNat 32 (readLE (window (witList N w) off 4)) := by
  unfold wle32 witEnc window
  exact extract_readLE_lt (witList N w) 22012 (witList_readLE_lt N w) off 4
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
  exact extract_readLE_lt (witList N w) 22012 (witList_readLE_lt N w) off 8
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
  have h := extract_readLE_lt (witList N w) 22012 (witList_readLE_lt N w) 36 12
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
    window (witList N w) (21984 + off) n = window (tailBytes w) off n := by
  rw [witList_split, window_append_right _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_right _ _ _ _ (by rw [leafBuffersBytes_length]; omega), leafBuffersBytes_length]
  exact congrArg (fun k : Nat => window (tailBytes w) k n)
    (show 21984 + off - (80 + 7584 + 11264) - 3056 = off by omega)
theorem wrho_witEnc : wrho (witEnc N w) = w.signature.rho := by
  unfold wrho rhoOff
  rw [wdig_witEnc, show (21984 : Nat) = 21984 + 0 from rfl, win_tail _ _ _ _ (by omega)]
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
  rw [wle32_witEnc, show (22008 : Nat) = 21984 + 24 from rfl, win_tail _ _ _ _ (by omega)]
  have h : window (tailBytes w) 24 4 = window (window (tailBytes w) 24 8) 0 4 := by
    unfold window; rw [List.drop_zero, List.take_take, Nat.min_eq_left (by omega)]
  rw [h, tail_counter_window, window_append_left _ _ _ _ (by simp [bytesLE_length]),
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wdcWord_witEnc : (wdcWord (witEnc N w)).toNat = w.digestCounter.toNat := by
  unfold wdcWord witEnc dcOff
  rw [show (64 : Nat) = 8 * 8 from rfl, extract_readLE_lt (witList N w) 22012 (witList_readLE_lt N w) 22008 8,
    show ((witList N w).drop 22008).take 8 = window (witList N w) (21984 + 24) 8 from rfl,
    win_tail _ _ _ _ (by omega), tail_counter_window, readLE_append, bytesLE_length,
    Correctness.readLE_bytesLE]
  have hz : readLE (zeros 4) = 0 := by decide
  rw [hz, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans w.digestCounter.isLt (by decide))
end tail
theorem layerBase_ge (lay : Layer) : 7664 ≤ layerBase lay := by
  fin_cases lay <;> simp [layerBase]
theorem layerEnd_le (lay : Layer) : layerBase lay + (16 * pathSlots lay + chainArea lay) ≤ 18928 := by
  fin_cases lay <;> decide
theorem layer_prefix (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (((List.finRange 4).take lay.val).map fun l => (layerRegion N w l).length).sum = layerBase lay - 7664 := by
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
  rw [show layerBase lay + j - (80 + 7584) = (layerBase lay - 7664) + j by omega, key]
/-- Pairing stage 1: the honest 64-byte cell of chain `i` (F: zeros then the value; G: the value then zeros). -/
def chainCell (lay : Layer) (ls : LayerSignature lay) (i : Nat) : List UInt8 :=
  if WCT9.isG lay i then bytesLE 16 (lsValue ls i) ++ zeros 48 else zeros 48 ++ bytesLE 16 (lsValue ls i)
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
    simp [chainCell, WCT9.isG_zero hl]
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
      simp [chainCell, WCT9.isG_eq_true.mpr (Or.inl ⟨hl, ho1⟩)]
    · have hs : chainSlot lay i + o = 104 * (21 - i / 2) + (40 + o) := by
        simp only [chainSlot, hlv, if_false, h0, ho1]; omega
      rw [hs, window_flatMap_const _ _ 104 (pairBytes_length ls) (21 - i / 2) (by simp; omega) _ _ (by omega)]
      have hidx : ((List.range 21).reverse)[21 - i / 2]'(by simp; omega) = i / 2 - 1 := by
        simp; omega
      rw [hidx, pairBytes_F, window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        show 40 + o - (zeros 16 ++ bytesLE 16 (lsValue ls (2 * (i / 2 - 1) + 1)) ++ zeros 8).length = o by
          simp [zeros, bytesLE_length],
        show 2 * (i / 2 - 1) + 2 = i by omega]
      simp [chainCell, WCT9.isG_eq_false (Or.inl ⟨hl, show i % 2 = 0 by omega⟩)]
theorem topPairBytes_G {lay : Layer} (ls : LayerSignature lay) (p : Nat) : topPairBytes ls p =
    zeros 16 ++ ((bytesLE 16 (lsValue ls (2 * p)) ++ zeros 48) ++ (zeros 8 ++ bytesLE 16 (lsValue ls (2 * p + 1)))) := by
  unfold topPairBytes
  rw [show zeros 56 = zeros 48 ++ zeros 8 from List.replicate_add 48 8 0]
  simp only [List.append_assoc]
theorem topPairBytes_F {lay : Layer} (ls : LayerSignature lay) (p : Nat) : topPairBytes ls p =
    (zeros 16 ++ bytesLE 16 (lsValue ls (2 * p)) ++ zeros 8) ++ (zeros 48 ++ bytesLE 16 (lsValue ls (2 * p + 1))) := by
  unfold topPairBytes
  rw [show zeros 56 = zeros 8 ++ zeros 48 from List.replicate_add 8 48 0]
  simp only [List.append_assoc]
/-- Witness stack (charge 86): the paired top chain area (G chain `2p` at `+16`, F chain `2p+1` at `+40` of pair
`p`, at `104 (26 - p)`). -/
theorem topChain_window (ls : LayerSignature 0) (i : Nat) (hi : i < 51) (o : Nat) (ho : o + 16 ≤ 64) :
    window (topChainBytes ls) (chainSlot 0 i + o) 16 = window (chainCell 0 ls i) o 16 := by
  unfold topChainBytes
  by_cases he : i % 2 = 0
  · have hs : chainSlot 0 i + o = 104 * (26 - i / 2) + (16 + o) := by
      unfold chainSlot; rw [if_pos (show (0 : Layer).val = 0 from rfl), if_pos he]; omega
    rw [hs, window_flatMap_const _ _ 104 (topPairBytes_length ls) (26 - i / 2) (by simp; omega) _ _ (by omega)]
    have hidx : ((List.range 27).reverse)[26 - i / 2]'(by simp; omega) = i / 2 := by
      simp; omega
    rw [hidx, topPairBytes_G, window_append_right _ _ _ _ (by simp [zeros]),
      show 16 + o - (zeros 16).length = o by simp [zeros],
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      show 2 * (i / 2) = i by omega]
    simp [chainCell, WCT9.isG_eq_true.mpr (Or.inr ⟨rfl, he, by omega⟩)]
  · have hs : chainSlot 0 i + o = 104 * (26 - i / 2) + (40 + o) := by
      unfold chainSlot; rw [if_pos (show (0 : Layer).val = 0 from rfl), if_neg he]; omega
    rw [hs, window_flatMap_const _ _ 104 (topPairBytes_length ls) (26 - i / 2) (by simp; omega) _ _ (by omega)]
    have hidx : ((List.range 27).reverse)[26 - i / 2]'(by simp; omega) = i / 2 := by
      simp; omega
    rw [hidx, topPairBytes_F, window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
      show 40 + o - (zeros 16 ++ bytesLE 16 (lsValue ls (2 * (i / 2))) ++ zeros 8).length = o by
        simp [zeros, bytesLE_length],
      show 2 * (i / 2) + 1 = i by omega]
    simp [chainCell, WCT9.isG_eq_false (Or.inr ⟨rfl, Or.inl (show i % 2 = 1 by omega)⟩)]

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
    rw [window_append_right _ _ _ _ (by rw [topPathBytes_length]; omega), topPathBytes_length,
      Nat.add_sub_cancel_left]
    exact topChain_window _ i.val (by simpa [chainCount] using hi) o ho
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
    (ho : if WCT9.isG lay i then 16 ≤ o ∧ o + 16 ≤ 64 else o + 16 ≤ 48) :
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
Line A (levels 0..5, row `leaf % 64`) lies in bytes `[336, 672)`, line B (levels 6..11, row `leaf / 64 % 64`) in
`[0, 320)`; within a line the sibling slots and the pad areas `[16 P_j + 24, 16 P_j + 48)` are disjoint (kernel
checks over the 64 rows). -/
def topSlotA (r j : Nat) : Nat := (topPlanA.getD r []).getD j 0
def topSlotB (r j : Nat) : Nat := (topPlanB.getD r []).getD j 0
def topSibA (r j : Nat) : Nat := 16 * topSlotA r j + sibOff (r / 2 ^ j % 2)
def topSibB (r j : Nat) : Nat := 16 * topSlotB r j + sibOff (r / 2 ^ j % 2)
theorem topA_range : ∀ r < 64, ∀ j < 6, 336 ≤ 16 * topSlotA r j ∧ 16 * topSlotA r j + 64 ≤ 672 := by decide
theorem topB_range : ∀ r < 64, ∀ j < 6, 16 * topSlotB r j + 64 ≤ 320 := by decide
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
theorem pathSlots_top : 16 * pathSlots (0 : Layer) = 672 := rfl
/-- Every top window's sibling slot and pad area lie in its line's range. -/
theorem top_ranges (leaf j : Nat) (hj : j < height 0) :
    (j < 6 → 336 ≤ topSibSlot leaf j ∧ topSibSlot leaf j + 16 ≤ 672 ∧
      336 ≤ 16 * topPlanSlot leaf j ∧ 16 * topPlanSlot leaf j + 48 ≤ 672) ∧
    (6 ≤ j → topSibSlot leaf j + 16 ≤ 320 ∧ 16 * topPlanSlot leaf j + 48 ≤ 320) := by
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
theorem top_sib_bound (leaf j : Nat) (hj : j < height 0) : topSibSlot leaf j + 16 ≤ 672 := by
  have h := top_ranges leaf j hj
  by_cases h6 : j < 6
  · exact (h.1 h6).2.1
  · have := (h.2 (by omega)).1; omega
theorem top_pad_bound (leaf j : Nat) (hj : j < height 0) : 16 * topPlanSlot leaf j + 48 ≤ 672 := by
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
theorem topPath_zero {a m : Nat} (hb : a + m ≤ 672)
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
theorem win_topPath (N : HashOutput) (w : WCT9.Witness) (o m : Nat) (h : o + m ≤ 672) :
    window (witList N w) (layerBase 0 + o) m =
      window (topPathBytes (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) o m := by
  rw [win_layerRegion N w 0 o m (by rw [pathSlots_top]; omega)]
  unfold layerRegion
  rw [if_pos (show (0 : Layer).val = 0 from rfl),
    window_append_left _ _ _ _ (by rw [topPathBytes_length, pathSlots_top]; exact h)]
section t3b
variable (N : HashOutput) (w : WCT9.Witness)
theorem wpath_witEnc (lay : Layer) (j : Fin (height lay)) :
    wpath (witEnc N w) lay (route (WCT9.digestIndex N) lay).1 j.val = (w.signature.layers lay).path j := by
  by_cases hlay : lay.val = 0
  · have hl : lay = 0 := Fin.ext hlay
    subst hl
    unfold wpath merkleBlock
    rw [if_pos (show (0 : Layer).val = 0 from rfl), Nat.add_assoc,
      show 16 * topPlanSlot (route (WCT9.digestIndex N) 0).1 j.val +
        sibOff ((route (WCT9.digestIndex N) 0).1 / 2 ^ j.val % 2) =
        topSibSlot (route (WCT9.digestIndex N) 0).1 j.val from rfl, wdig_witEnc,
      win_topPath _ _ _ _ (top_sib_bound _ j.val j.isLt), topPath_sib, Correctness.readDigest_bytesLE]
  · have hleaf := route_leaf_lt (WCT9.digestIndex N) lay
    unfold wpath merkleBlock
    rw [if_neg hlay, Nat.add_assoc, show 16 * (lowerPlan lay (route (WCT9.digestIndex N) lay).1).getD j.val 0 +
        sibOff ((route (WCT9.digestIndex N) lay).1 / 2 ^ j.val % 2) =
        lowerSibSlot lay (route (WCT9.digestIndex N) lay).1 j.val from rfl, wdig_witEnc,
      win_lowerPath _ _ _ hlay _ _ (lower_sib_bound lay hlay _ hleaf j.val j.isLt),
      lowerPath_sib hlay hleaf, Correctness.readDigest_bytesLE]
theorem wmerklePad_witEnc (lay : Layer) (j : Fin (height lay)) (hj : j.val + 1 < height lay ∨ lay.val = 0) :
    wmerklePad (witEnc N w) lay (route (WCT9.digestIndex N) lay).1 j.val = 0 := by
  by_cases hlay : lay.val = 0
  · have hl : lay = 0 := Fin.ext hlay
    subst hl
    unfold wmerklePad merkleBlock
    rw [if_pos (show (0 : Layer).val = 0 from rfl), Nat.add_assoc, wdig_witEnc,
      win_topPath _ _ _ _ (by have := top_pad_bound (route (WCT9.digestIndex N) 0).1 j.val j.isLt; omega),
      topPath_pad _ _ j.isLt, readDigest_zeros]
  · have hleaf := route_leaf_lt (WCT9.digestIndex N) lay
    have hj' : j.val + 1 < height lay := hj.resolve_right hlay
    unfold wmerklePad merkleBlock
    rw [if_neg hlay, Nat.add_assoc, wdig_witEnc,
      win_lowerPath _ _ _ hlay _ _ (by have := lower_pad_bound lay hlay _ hleaf j.val j.isLt; omega),
      lowerPath_pad hlay hleaf _ _ hj', readDigest_zeros]
theorem rowBlock_upper (index : Nat) (lay : Layer) (h : lay.val < 3) :
    rowBlock index lay + 32 = layerBase (upLayer lay) + lowerCtrSlot (upLayer lay) (route index (upLayer lay)).1 := by
  have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
  unfold rowBlock merkleBlock lowerCtrSlot
  rw [if_neg (by omega), if_neg hv]
  omega
theorem upLayer_down (lay : Layer) (h : lay.val < 3) : (Fin.ofNat 4 ((upLayer lay).val - 1) : Layer) = lay := by
  apply Fin.ext
  unfold upLayer
  simp [Fin.val_ofNat]
  omega
theorem wbcCtr_witEnc (lay : Layer) : wbcCtr (witEnc N w) (WCT9.digestIndex N) lay = w.counters lay := by
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    exact wctr3_witEnc N w
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
    have hleaf := route_leaf_lt (WCT9.digestIndex N) (upLayer lay)
    have hb := lower_pad_bound (upLayer lay) hv _ hleaf (height (upLayer lay) - 1)
      (by have := height_pos' (upLayer lay); omega)
    unfold wbcCtr bcCounterOff
    rw [rowBlock_upper _ _ hlt, wle32_witEnc,
      win_lowerPath _ _ _ hv _ _ (by unfold lowerCtrSlot; omega), upLayer_down lay hlt,
      lowerPath_ctr hv hleaf, readLE_bytesLE_32]
theorem wbcPad_witEnc (lay : Layer) : wbcPad (witEnc N w) (WCT9.digestIndex N) lay = 0 := by
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    exact wpad3_witEnc N w
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
    have hleaf := route_leaf_lt (WCT9.digestIndex N) (upLayer lay)
    have hb := lower_pad_bound (upLayer lay) hv _ hleaf (height (upLayer lay) - 1)
      (by have := height_pos' (upLayer lay); omega)
    unfold wbcPad witEnc bcCounterOff
    rw [rowBlock_upper _ _ hlt, show (96 : Nat) = 8 * 12 from rfl,
      extract_readLE_lt (witList N w) 22012 (witList_readLE_lt N w) _ 12,
      show ((witList N w).drop (layerBase (upLayer lay) +
          lowerCtrSlot (upLayer lay) (route (WCT9.digestIndex N) (upLayer lay)).1 + 4)).take 12 =
        window (witList N w) (layerBase (upLayer lay) +
          (lowerCtrSlot (upLayer lay) (route (WCT9.digestIndex N) (upLayer lay)).1 + 4)) 12 by
        unfold window; rw [Nat.add_assoc],
      win_lowerPath _ _ _ hv _ _ (by unfold lowerCtrSlot; omega), lowerPath_rowPad hv hleaf]
    rfl
theorem rowBlock_hi (index : Nat) (lay : Layer) (h : lay.val < 3) :
    rowBlock index lay + 16 + 8 = layerBase (upLayer lay) + lowerHiSlot (upLayer lay) (route index (upLayer lay)).1 := by
  have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
  unfold rowBlock merkleBlock lowerHiSlot
  rw [if_neg (by omega), if_neg hv]
  omega
/-- C2/C3 (FULL): the honest encoding row tweak high words are 1. -/
theorem wbcHigh_witEnc (lay : Layer) : wbcHigh (witEnc N w) (WCT9.digestIndex N) lay = 1 := by
  unfold wbcHigh
  rw [wdig_high, wword_witEnc]
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    rw [show rowBlock (WCT9.digestIndex N) 3 + 16 + 8 = 24 by simp [rowBlock], win_header_hi]
    decide
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
    have hleaf := route_leaf_lt (WCT9.digestIndex N) (upLayer lay)
    have hb := lower_pad_bound (upLayer lay) hv _ hleaf (height (upLayer lay) - 1)
      (by have := height_pos' (upLayer lay); omega)
    rw [rowBlock_hi _ _ hlt, win_lowerPath _ _ _ hv _ _ (by unfold lowerHiSlot; omega), lowerPath_hi hv hleaf]
    decide
/-- C2 (FULL) + C4: the honest high tweak words of the fold windows are 0 (lower windows below the root, every top
window). -/
theorem wmerkleHigh_witEnc (lay : Layer) (j : Fin (height lay)) (hj : j.val + 1 < height lay ∨ lay.val = 0) :
    wmerkleHigh (witEnc N w) lay (route (WCT9.digestIndex N) lay).1 j.val = 0 := by
  unfold wmerkleHigh
  by_cases hlay : lay.val = 0
  · have hl : lay = 0 := Fin.ext hlay
    subst hl
    have hb := top_pad_bound (route (WCT9.digestIndex N) 0).1 j.val j.isLt
    rw [wdig_high, wword_witEnc]
    unfold merkleBlock
    rw [if_pos (show (0 : Layer).val = 0 from rfl),
      show layerBase 0 + 16 * topPlanSlot (route (WCT9.digestIndex N) 0).1 j.val + 16 + 8 =
        layerBase 0 + (16 * topPlanSlot (route (WCT9.digestIndex N) 0).1 j.val + 24) by omega,
      win_topPath _ _ _ _ (by omega), topPath_hp _ _ j.isLt]
    decide
  · have hj : j.val + 1 < height lay := hj.resolve_right hlay
    have hleaf := route_leaf_lt (WCT9.digestIndex N) lay
    have hb := lower_pad_bound lay hlay _ hleaf j.val j.isLt
    rw [wdig_high, wword_witEnc]
    unfold merkleBlock
    rw [if_neg hlay, show layerBase lay + 16 * (lowerPlan lay (route (WCT9.digestIndex N) lay).1).getD j.val 0 + 16 + 8 =
        layerBase lay + (16 * (lowerPlan lay (route (WCT9.digestIndex N) lay).1).getD j.val 0 + 24) by omega,
      win_lowerPath _ _ _ hlay _ _ (by omega), lowerPath_hp hlay hleaf _ _ hj]
    decide
end t3b
theorem win_region (N : HashOutput) (w : WCT9.Witness) (k : WCT9.Coord) (o n : Nat) (h : o + n ≤ 848)
    (h0 : k.val ≠ 0 ∨ o + n ≤ 784 := by first | exact Or.inr (by omega) | exact Or.inl (by omega)) :
    window (witList N w) (regionBase k.val + o) n =
      window (regionBytes (WCT9.child N k).val (w.signature.openings k) (prevSibL N w.signature k.val)
        (prevSibZ N w.signature k.val)) o n := by
  have hk := k.isLt
  have hrb : regionBase k.val = 80 + 848 * (8 - k.val) := rfl
  rw [witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    show regionBase k.val + o - 80 = 848 * (8 - k.val) + o by omega]
  have hidx : ((List.finRange 9).reverse[8 - k.val]'(by simp; omega)) = k := by
    rw [List.getElem_reverse]; ext; simp; omega
  have key := window_flatMap (List.finRange 9).reverse (regionCell N w.signature) (8 - k.val) (by simp; omega) o n
    (by rw [hidx, regionCell_length]; unfold regionLen; split <;> omega)
  simp only [regionCell_length] at key
  rw [wct_prefix, hidx] at key
  rw [wctBytes_eq, key]
  unfold regionCell
  split
  · rename_i hk0
    have h784 : o + n ≤ 784 := by omega
    rw [window_append_left _ _ _ _ (by
      rw [List.length_take, regionBytes_length _ _ _ _ (prevSibL_length _ _ _) (prevSibZ_length _ _ _)]; omega),
      window_take _ _ _ _ h784]
  · rfl
/-- Pairing stage 1: coordinate 0's level-5 sibling sits at `legacySib0` (after region 0's first 784 bytes). -/
theorem wdig_legacySib0 (N : HashOutput) (w : WCT9.Witness) :
    wdig (witEnc N w) legacySib0 = (w.signature.openings 0).path 5 := by
  rw [wdig_witEnc, witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; unfold legacySib0; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; unfold legacySib0; omega),
    window_append_right _ _ _ _ (by rw [headerBytes_length]; unfold legacySib0; omega), headerBytes_length,
    show legacySib0 - 80 = 848 * 8 + 784 from rfl]
  have hidx : ((List.finRange 9).reverse[8]'(by simp)) = (0 : WCT9.Coord) := by decide
  have key := window_flatMap (List.finRange 9).reverse (regionCell N w.signature) 8 (by simp) 784 16
    (by rw [hidx, regionCell_length]; decide)
  simp only [regionCell_length] at key
  rw [show ((((List.finRange 9).reverse).take 8).map regionLen).sum = 848 * 8 by decide, hidx] at key
  rw [wctBytes_eq, key]
  unfold regionCell
  rw [if_pos (show (0 : WCT9.Coord).val = 0 from rfl), window_append_right _ _ _ _ (by
      rw [List.length_take, regionBytes_length _ _ _ _ (prevSibL_length _ _ _) (prevSibZ_length _ _ _)]; decide),
    List.length_take, regionBytes_length _ _ _ _ (prevSibL_length _ _ _) (prevSibZ_length _ _ _),
    show 784 - min 784 848 = 0 from rfl, window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
theorem wdig_region (N : HashOutput) (w : WCT9.Witness) (k : WCT9.Coord) (o : Nat) (h : o + 16 ≤ 848)
    (h0 : k.val ≠ 0 ∨ o + 16 ≤ 784 := by first | exact Or.inr (by omega) | exact Or.inl (by omega)) :
    wdig (witEnc N w) (regionBase k.val + o) =
      readDigest (window (regionBytes (WCT9.child N k).val (w.signature.openings k) (prevSibL N w.signature k.val)
        (prevSibZ N w.signature k.val)) o 16) := by
  rw [wdig_witEnc, win_region N w k o 16 h h0]
theorem auth_sib_bound : ∀ c < 128, ∀ l < 5, authSibOff c l + 16 ≤ 320 := by decide
theorem auth_pad_bound : ∀ c < 128, ∀ l < 5, authPadOff c l + 16 ≤ 320 ∨ authPadOff c l = 320 := by decide
theorem auth_sib_disjoint : ∀ c < 128, ∀ l < 5, ∀ l' < 5, l ≠ l' →
    authSibOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authSibOff c l := by decide
theorem auth_pad_disjoint : ∀ c < 128, ∀ l < 5, ∀ l' < 5,
    authPadOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authPadOff c l := by decide
theorem find_finRange_eq (l : Fin 5) : (List.finRange 5).find? (fun l' => decide (l' = l)) = some l := by
  revert l; decide
theorem authByte5_sib {c : Nat} (hc : c < 128) (op : WCT9.Opening) (l : Fin 5) {i : Nat} (hi : i < 16) :
    authByte5 c op (authSibOff c l.val + i) = (bytesLE 16 (op.path (Fin.castLE (by decide) l))).getD i 0 := by
  have hP : (fun l' : Fin 5 => decide (authSibOff c l'.val ≤ authSibOff c l.val + i ∧
      authSibOff c l.val + i < authSibOff c l'.val + 16)) = fun l' => decide (l' = l) := by
    funext l'
    by_cases h : l' = l
    · subst h; simp only [decide_true, decide_eq_true_eq]; omega
    · have hd := auth_sib_disjoint c hc l'.val l'.isLt l.val l.isLt (fun e => h (Fin.ext e))
      simp only [h, decide_false, decide_eq_false_iff_not, not_and, not_lt]
      omega
  unfold authByte5
  rw [hP, find_finRange_eq]
  simp only [Nat.add_sub_cancel_left]
theorem authByte5_none {c : Nat} (op : WCT9.Opening) {p : Nat}
    (hp : ∀ l : Fin 5, p < authSibOff c l.val ∨ authSibOff c l.val + 16 ≤ p) : authByte5 c op p = 0 := by
  unfold authByte5
  rw [List.find?_eq_none.mpr (fun l _ => by
    have := hp l
    simp only [decide_eq_true_eq, not_and, not_lt]
    omega)]
theorem merkleBytes_sib {c : Nat} (hc : c < 128) (op : WCT9.Opening) (l : Fin 5) :
    window (merkleBytes c op) (authSibOff c l.val) 16 = bytesLE 16 (op.path (Fin.castLE (by decide) l)) := by
  unfold merkleBytes
  rw [window_map_range _ _ _ _ (auth_sib_bound c hc l.val l.isLt),
    List.map_congr_left (fun i hi => authByte5_sib hc op l (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem merkleBytes_pad {c : Nat} (hc : c < 128) (op : WCT9.Opening) {l : Nat} (hl : l < 5) (hb : authPadOff c l + 16 ≤ 320) :
    window (merkleBytes c op) (authPadOff c l) 16 = zeros 16 := by
  unfold merkleBytes
  rw [window_map_range _ _ _ _ hb,
    List.map_congr_left (fun i hi => authByte5_none op (fun l' => by
      have := auth_pad_disjoint c hc l hl l'.val l'.isLt
      have := List.mem_range.mp hi
      omega))]
  simp [zeros, List.map_const']
theorem auth_tw_bound : ∀ c < 128, ∀ l < 4, c / 2 ^ l % 2 = 1 → authBase c l + 16 + 16 ≤ 320 := by decide
theorem auth_tw_disjoint : ∀ c < 128, ∀ l < 4, c / 2 ^ l % 2 = 1 → ∀ l' < 5,
    authBase c l + 16 + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authBase c l + 16 := by decide
theorem merkleBytes_tw {c : Nat} (hc : c < 128) (op : WCT9.Opening) {l : Nat} (hl : l < 4) (hbit : c / 2 ^ l % 2 = 1)
    (hb : authBase c l + 16 + 16 ≤ 320) :
    window (merkleBytes c op) (authBase c l + 16) 16 = zeros 16 := by
  unfold merkleBytes
  rw [window_map_range _ _ _ _ hb,
    List.map_congr_left (fun i hi => authByte5_none op (fun l' => by
      have := auth_tw_disjoint c hc l hl hbit l'.val l'.isLt
      have := List.mem_range.mp hi
      omega))]
  simp [zeros, List.map_const']
section region
variable (c : Nat) (op : WCT9.Opening) (padL padZ : List UInt8)
theorem region_merkle (o n : Nat) (h : o + n ≤ 320) :
    window (regionBytes c op padL padZ) o n = window (merkleBytes c op) o n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length]; omega)]
theorem region_chain (o n : Nat) (h0 : 320 ≤ o) (h : o + n ≤ 592) :
    window (regionBytes c op padL padZ) o n = window (chainBytes op) (o - 320) n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length]; omega), merkleBytes_length]
theorem region_prefix (o n : Nat) (h0 : 592 ≤ o) (h : o + n ≤ 640) :
    window (regionBytes c op padL padZ) o n = zeros n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length]
  exact window_zeros _ _ _ (by omega)
theorem region_leaf (hL : padL.length = 16) (o n : Nat) (h0 : 640 ≤ o) (h : o + n ≤ 768) :
    window (regionBytes c op padL padZ) o n = window (leafBytes op padL) (o - 640) n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length, zeros, List.length_replicate]
theorem region_top (hL : padL.length = 16) (o n : Nat) (h0 : 784 ≤ o) :
    window (regionBytes c op padL padZ) o n = window (topBlockBytes c op padZ) (o - 784) n := by
  unfold regionBytes
  rw [window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length, leafBytes_length', hL, zeros,
    List.length_replicate]
/-- The zero cell at region offset 768 (between the leaf block and the level-5 window). -/
theorem region_gap (hL : padL.length = 16) : window (regionBytes c op padL padZ) 768 16 = zeros 16 := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', hL, zeros]),
    window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', hL, zeros])]
  simp only [List.length_append, merkleBytes_length, chainBytes_length, leafBytes_length', hL, zeros,
    List.length_replicate]
  exact window_zeros _ _ _ (by omega)
theorem ftsPair_G (a b : Digest) : ftsPairBytes a b =
    zeros 16 ++ ((bytesLE 16 a ++ zeros 48) ++ (zeros 8 ++ bytesLE 16 b)) := by
  unfold ftsPairBytes
  rw [show zeros 56 = zeros 48 ++ zeros 8 from List.replicate_add 48 8 0]
  simp only [List.append_assoc]
theorem ftsPair_F (a b : Digest) : ftsPairBytes a b =
    (zeros 16 ++ bytesLE 16 a ++ zeros 8) ++ (zeros 48 ++ bytesLE 16 b) := by
  unfold ftsPairBytes
  rw [show zeros 56 = zeros 8 ++ zeros 48 from List.replicate_add 8 48 0]
  simp only [List.append_assoc]
/-- A window inside the middle part `C` of `A ++ (C ++ B)`. -/
theorem window_cell {L A C B : List UInt8} (hL : L = A ++ (C ++ B)) {a o n : Nat} (ha : A.length = a)
    (h : o + n ≤ C.length) : window L (a + o) n = window C o n := by
  subst hL; subst ha
  rw [window_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, window_append_left _ _ _ _ h]
/-- Witness stack (charge 86): the honest 64-byte FTS chain block of chain `t` (G chains 1, 3: the value then zeros;
F chains: zeros then the value). -/
def ftsCell (t : Fin 6) : List UInt8 :=
  if WCT9.ftsIsG t.val then bytesLE 16 (op.values t) ++ zeros 48 else zeros 48 ++ bytesLE 16 (op.values t)
theorem ftsCell_length (t : Fin 6) : (ftsCell op t).length = 64 := by
  unfold ftsCell; split <;> simp [zeros, bytesLE_length]
theorem chainBytes_cell (t : Fin 6) (ht : t.val ≠ 0) :
    ∃ A B, chainBytes op = A ++ (ftsCell op t ++ B) ∧ A.length = wctChainOff t.val - 320 := by
  fin_cases t
  · exact absurd rfl ht
  · refine ⟨zeros 48 ++ bytesLE 16 (op.values 5) ++ ftsPairBytes (op.values 3) (op.values 4) ++ zeros 16,
      zeros 8 ++ bytesLE 16 (op.values 2), ?_, by simp [zeros, bytesLE_length, ftsPairBytes_length, wctChainOff]⟩
    rw [chainBytes, ftsPair_G (op.values 1)]
    simp [ftsCell, WCT9.ftsIsG, List.append_assoc]
  · refine ⟨zeros 48 ++ bytesLE 16 (op.values 5) ++ ftsPairBytes (op.values 3) (op.values 4) ++
      (zeros 16 ++ bytesLE 16 (op.values 1) ++ zeros 8), [], ?_,
      by simp [zeros, bytesLE_length, ftsPairBytes_length, wctChainOff]⟩
    rw [chainBytes, ftsPair_F (op.values 1)]
    simp [ftsCell, WCT9.ftsIsG, List.append_assoc]
  · refine ⟨zeros 48 ++ bytesLE 16 (op.values 5) ++ zeros 16,
      zeros 8 ++ bytesLE 16 (op.values 4) ++ ftsPairBytes (op.values 1) (op.values 2), ?_,
      by simp [zeros, bytesLE_length, wctChainOff]⟩
    rw [chainBytes, ftsPair_G (op.values 3)]
    simp [ftsCell, WCT9.ftsIsG, List.append_assoc]
  · refine ⟨zeros 48 ++ bytesLE 16 (op.values 5) ++ (zeros 16 ++ bytesLE 16 (op.values 3) ++ zeros 8),
      ftsPairBytes (op.values 1) (op.values 2), ?_, by simp [zeros, bytesLE_length, wctChainOff]⟩
    rw [chainBytes, ftsPair_F (op.values 3)]
    simp [ftsCell, WCT9.ftsIsG, List.append_assoc]
  · refine ⟨[], ftsPairBytes (op.values 3) (op.values 4) ++ ftsPairBytes (op.values 1) (op.values 2), ?_,
      by simp [wctChainOff]⟩
    simp [chainBytes, ftsCell, WCT9.ftsIsG, List.append_assoc]
theorem wctChainOff_bound (t : Fin 6) : 320 ≤ wctChainOff t.val ∧ wctChainOff t.val + 64 ≤ 656 ∧
    (t.val ≠ 0 → wctChainOff t.val + 64 ≤ 592) := by
  fin_cases t <;> simp [wctChainOff]
/-- Witness stack (charge 86): every FTS chain block `[wctChainOff t, +64)` of a region holds `ftsCell`. -/
theorem region_cell (hL : padL.length = 16) (t : Fin 6) (o : Nat) (ho : o + 16 ≤ 64) :
    window (regionBytes c op padL padZ) (wctChainOff t.val + o) 16 = window (ftsCell op t) o 16 := by
  have hb := wctChainOff_bound t
  by_cases ht : t.val = 0
  · have h0 : t = 0 := Fin.ext ht
    subst h0
    have hc : ftsCell op 0 = zeros 48 ++ bytesLE 16 (op.values 0) := by simp [ftsCell, WCT9.ftsIsG]
    rw [hc]
    refine window_cell (A := merkleBytes c op ++ chainBytes op)
      (B := (zeros 16 ++ padL ++ (List.finRange 5).flatMap fun i => bytesLE 16 (op.values i.succ)) ++ zeros 16 ++
        topBlockBytes c op padZ) ?_ (by simp [merkleBytes_length, chainBytes_length, wctChainOff])
      (by simp [zeros, bytesLE_length]; omega)
    simp only [regionBytes, leafBytes, List.append_assoc]
  · obtain ⟨A, B, hAB, hA⟩ := chainBytes_cell op t ht
    rw [region_chain _ _ _ _ _ _ (by omega) (by have := hb.2.2 ht; omega),
      show wctChainOff t.val + o - 320 = (wctChainOff t.val - 320) + o by omega]
    exact window_cell hAB hA (by rw [ftsCell_length]; omega)
theorem ftsCell_value (t : Fin 6) : window (ftsCell op t) (wctValueOff t.val) 16 = bytesLE 16 (op.values t) := by
  unfold ftsCell wctValueOff
  by_cases hG : WCT9.ftsIsG t.val = true
  · rw [if_pos hG, if_pos hG, window_append_left _ _ _ _ (by simp [bytesLE_length]),
      window_full _ _ (bytesLE_length _ _)]
  · rw [if_neg hG, if_neg hG, window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
theorem ftsCell_zero (t : Fin 6) (o : Nat)
    (ho : if WCT9.ftsIsG t.val then 16 ≤ o ∧ o + 16 ≤ 64 else o + 16 ≤ 48) :
    window (ftsCell op t) o 16 = zeros 16 := by
  unfold ftsCell
  split
  · rename_i hG; rw [if_pos hG] at ho
    rw [window_append_right _ _ _ _ (by simp [bytesLE_length]; omega)]
    exact window_zeros _ _ _ (by simp [bytesLE_length]; omega)
  · rename_i hG; rw [if_neg hG] at ho
    rw [window_append_left _ _ _ _ (by simp [zeros]; omega)]
    exact window_zeros _ _ _ ho
theorem leafBytes_window_zero : window (leafBytes op padL) 0 16 = bytesLE 16 (op.values 0) := by
  unfold leafBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
theorem leafBytes_window_pad (hL : padL.length = 16) : window (leafBytes op padL) 32 16 = padL := by
  unfold leafBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros, hL]),
    window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 32 - (bytesLE 16 (op.values 0) ++ zeros 16).length = 0 by simp [bytesLE_length, zeros],
    window_full _ _ hL]
theorem leafBytes_window_succ (hL : padL.length = 16) (i : Fin 5) :
    window (leafBytes op padL) (48 + 16 * i.val) 16 = bytesLE 16 (op.values i.succ) := by
  have hi := i.isLt
  unfold leafBytes
  rw [window_append_right _ _ _ _ (by simp [bytesLE_length, zeros, hL]),
    show 48 + 16 * i.val - (bytesLE 16 (op.values 0) ++ zeros 16 ++ padL).length = 16 * i.val + 0 by
      simp [bytesLE_length, zeros, hL],
    window_flatMap_const _ _ 16 (fun j => bytesLE_length _ _) i.val (by simp [hi]) 0 16 le_rfl,
    window_full _ _ (bytesLE_length _ _)]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
theorem topBlock_sib (hZ : padZ.length = 16) :
    window (topBlockBytes c op padZ) (sibOff (c / 2 ^ 5 % 2)) 16 = bytesLE 16 (op.path 5) := by
  unfold topBlockBytes sibOff
  by_cases hb : c / 2 ^ 5 % 2 = 1
  · rw [if_pos hb, if_pos hb, if_neg (show ¬(c / 2 ^ 5 % 2 = 0) by omega),
      window_append_left _ _ _ _ (by simp [bytesLE_length, zeros, hZ]),
      window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
      window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
  · rw [if_neg hb, if_neg hb, if_pos (show c / 2 ^ 5 % 2 = 0 by omega),
      window_append_right _ _ _ _ (by simp [zeros, hZ]),
      show 48 - (zeros 16 ++ zeros 16 ++ padZ).length = 0 by simp [zeros, hZ],
      window_full _ _ (bytesLE_length _ _)]
theorem topBlock_pad (hZ : padZ.length = 16) : window (topBlockBytes c op padZ) 32 16 = padZ := by
  unfold topBlockBytes
  rw [window_append_left _ _ _ _ (by simp only [List.length_append, ite_slot_length, zeros_len, hZ]; omega),
    window_append_right _ _ _ _ (by simp only [List.length_append, ite_slot_length, zeros_len]; omega),
    show 32 - ((if c / 2 ^ 5 % 2 = 1 then bytesLE 16 (op.path 5) else zeros 16) ++ zeros 16).length = 0 by
      simp only [List.length_append, ite_slot_length, zeros_len],
    window_full _ _ hZ]
end region
section fields
variable (N : HashOutput) (w : WCT9.Witness)
theorem wopen_witEnc (k : WCT9.Coord) (t : Fin 6) :
    wopen (witEnc N w) k.val t.val = (w.signature.openings k).values t := by
  have hb := wctChainOff_bound t
  have hv : wctValueOff t.val ≤ 48 := by unfold wctValueOff; split <;> omega
  unfold wopen wctChainBlock
  rw [Nat.add_assoc, wdig_region N w k _ (by omega),
    region_cell _ _ _ _ (prevSibL_length _ _ _) t _ (by omega), ftsCell_value, Correctness.readDigest_bytesLE]
theorem wleaf_witEnc (k : WCT9.Coord) (t : Fin 6) :
    wleaf (witEnc N w) k.val t.val = (w.signature.openings k).values t := by
  rcases t with ⟨_ | i, ht⟩
  · rw [show (⟨0, ht⟩ : Fin 6).val = 0 from rfl, wleaf_zero]
    exact wopen_witEnc N w k ⟨0, ht⟩
  · have hi : i < 5 := by omega
    unfold wleaf wctLeafSlot
    dsimp only
    rw [if_neg (by omega), show regionBase k.val + (672 + 16 * (i + 1)) = regionBase k.val + (640 + (48 + 16 * i)) by
        omega, wdig_region N w k _ (by omega),
      region_leaf _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega) (by omega),
      show 640 + (48 + 16 * i) - 640 = 48 + 16 * (⟨i, hi⟩ : Fin 5).val by simp,
      leafBytes_window_succ _ _ (prevSibL_length _ _ _), Correctness.readDigest_bytesLE]
    rfl
theorem wreveal_witEnc (k : WCT9.Coord) (t : Fin 6) (d : Nat) :
    wreveal (witEnc N w) k.val t.val d = (w.signature.openings k).values t := by
  unfold wreveal
  split
  · exact wleaf_witEnc N w k t
  · exact wopen_witEnc N w k t
theorem wcpads_witEnc (k : WCT9.Coord) (t : Fin 6) : wcpads (witEnc N w) k.val t.val = (0, 0) := by
  have hb := wctChainOff_bound t
  have h0 : wctPad0Off t.val ≤ 48 := by unfold wctPad0Off; split <;> omega
  have h1 : wctPad1Off t.val ≤ 48 := by unfold wctPad1Off; split <;> omega
  unfold wcpads wctChainBlock
  rw [Nat.add_assoc, Nat.add_assoc, wdig_region N w k _ (by omega), wdig_region N w k _ (by omega),
    region_cell _ _ _ _ (prevSibL_length _ _ _) t _ (by omega),
    region_cell _ _ _ _ (prevSibL_length _ _ _) t _ (by omega),
    ftsCell_zero _ _ _ (by unfold wctPad0Off; split <;> simp_all),
    ftsCell_zero _ _ _ (by unfold wctPad1Off; split <;> simp_all), readDigest_zeros]
theorem wcHeaderPad_witEnc (k : WCT9.Coord) (t : Fin 6) : wcHeaderPad (witEnc N w) k.val t.val = 0 := by
  have hb := wctChainOff_bound t
  unfold wcHeaderPad wctChainBlock
  rw [Nat.add_assoc, wdig_region N w k _ (by omega),
    region_cell _ _ _ _ (prevSibL_length _ _ _) t _ (by omega),
    ftsCell_zero _ _ _ (by split <;> simp_all), readDigest_zeros]
  rfl
theorem prev_coord (k : WCT9.Coord) : (Fin.ofNat 9 (k.val + 1 - 1) : WCT9.Coord) = k :=
  Fin.ext (by rw [Fin.val_ofNat, Nat.add_sub_cancel, Nat.mod_eq_of_lt k.isLt])
theorem prevSibL_succ (sig : WCT9.Signature) (k : WCT9.Coord) :
    prevSibL N sig (k.val + 1) =
      if (WCT9.child N k).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((sig.openings k).path 6) else zeros 16 := by
  unfold prevSibL; rw [if_neg (by omega), prev_coord]
theorem prevSibZ_succ (sig : WCT9.Signature) (k : WCT9.Coord) :
    prevSibZ N sig (k.val + 1) =
      if (WCT9.child N k).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((sig.openings k).path 6) else zeros 16 := by
  unfold prevSibZ; rw [if_neg (by omega), prev_coord]
/-- Nested FTS (r1-1): the level-5 fold pad of coordinate `k` holds coordinate `k - 1`'s right-slot sibling. -/
theorem wmpad_five_witEnc (k : WCT9.Coord) (hk : k.val ≠ 0) (c : Nat) :
    wmpad (witEnc N w) k.val c 5 = readDigest (prevSibZ N w.signature k.val) := by
  unfold wmpad authPadOff
  rw [if_neg (by omega), authBase_five, wdig_region N w k _ (by omega) (Or.inl hk),
    region_top _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega), show 784 + 32 - 784 = 32 from rfl,
    topBlock_pad _ _ _ (prevSibZ_length _ _ _)]
/-- Nested FTS (r1-1): the leaf pad of coordinate `k` holds coordinate `k - 1`'s left-slot sibling. -/
theorem wleafPad_prev_witEnc (k : WCT9.Coord) :
    wleafPad (witEnc N w) k.val = readDigest (prevSibL N w.signature k.val) := by
  unfold wleafPad wctLeafBlock
  rw [show regionBase k.val + 640 + 32 = regionBase k.val + 672 by omega, wdig_region N w k _ (by omega),
    region_leaf _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega) (by omega), show 672 - 640 = 32 from rfl,
    leafBytes_window_pad _ _ (prevSibL_length _ _ _)]
theorem wmpad_start_witEnc (c : Nat) : wmpad (witEnc N w) 0 c 5 = 0 := by
  unfold wmpad legacyPad0
  rw [if_pos ⟨rfl, rfl⟩, show regionBase 0 + 768 = regionBase (0 : WCT9.Coord).val + 768 from rfl,
    wdig_region N w 0 768 (by omega), region_gap _ _ _ _ (prevSibL_length _ _ _), readDigest_zeros]
theorem wleafPad_witEnc : wleafPad (witEnc N w) 0 = 0 :=
  (wleafPad_prev_witEnc N w 0).trans (by unfold prevSibL; rw [if_pos (show (0 : WCT9.Coord).val = 0 from rfl), readDigest_zeros])
theorem wctStart_witEnc : wctStart (witEnc N w) = (0, 0) := by
  unfold wctStart; rw [wleafPad_witEnc, wmpad_start_witEnc]
/-- Nested FTS (r1-1): the supplied top sibling of coordinate `k` (level 6) sits in coordinate `k + 1`'s region, or in
the header for `k = 8`. -/
theorem wtop_witEnc (k : WCT9.Coord) :
    wdig (witEnc N w) (topSlot k.val (WCT9.child N k).val) = (w.signature.openings k).path 6 := by
  have hk := k.isLt
  by_cases h8 : k.val = 8
  · obtain rfl : k = 8 := Fin.ext h8
    by_cases h0 : (WCT9.child N 8).val / 2 ^ 6 % 2 = 0
    · rw [show topSlot (8 : WCT9.Coord).val (WCT9.child N 8).val = 64 by
          unfold topSlot; rw [if_pos h8, if_pos h0],
        wdig_witEnc, win_header _ _ _ _ (by omega), headerBytes_eq,
        if_neg (show ¬((WCT9.child N 8).val / 2 ^ 6 % 2 = 1) by omega), if_pos h0,
        window_append_right _ _ _ _ (by simp [zeros]), window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        show 64 - (zeros 16).length - (zeros 8 ++ bytesLE 8 (1 : BitVec 64)).length -
            (bytesLE 4 (w.counters 3)).length - (zeros 28).length = 0
          by simp [zeros, bytesLE_length],
        window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
    · have h1 : (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 := by omega
      rw [show topSlot (8 : WCT9.Coord).val (WCT9.child N 8).val = 0 by
          unfold topSlot; rw [if_pos h8, if_neg h0],
        wdig_witEnc, win_header _ _ _ _ (by omega), headerBytes_eq, if_pos h1,
        window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
        Correctness.readDigest_bytesLE]
  · have hk' : k.val + 1 < 9 := by omega
    by_cases h0 : (WCT9.child N k).val / 2 ^ 6 % 2 = 0
    · rw [show topSlot k.val (WCT9.child N k).val = regionBase (⟨k.val + 1, hk'⟩ : WCT9.Coord).val + 816 by
          unfold topSlot regionBase; rw [if_neg h8, if_pos h0]; dsimp only; omega,
        wdig_region N w _ _ (by omega) (Or.inl (by simp)), region_top _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega),
        show 816 - 784 = 32 from rfl, topBlock_pad _ _ _ (prevSibZ_length _ _ _)]
      show readDigest (prevSibZ N w.signature (k.val + 1)) = _
      rw [prevSibZ_succ, if_pos h0, Correctness.readDigest_bytesLE]
    · have h1 : (WCT9.child N k).val / 2 ^ 6 % 2 = 1 := by omega
      rw [show topSlot k.val (WCT9.child N k).val = regionBase (⟨k.val + 1, hk'⟩ : WCT9.Coord).val + 672 by
          unfold topSlot regionBase; rw [if_neg h8, if_neg h0]; dsimp only; omega,
        wdig_region N w _ _ (by omega), region_leaf _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega) (by omega),
        show 672 - 640 = 32 from rfl, leafBytes_window_pad _ _ (prevSibL_length _ _ _)]
      show readDigest (prevSibL N w.signature (k.val + 1)) = _
      rw [prevSibL_succ, if_pos h1, Correctness.readDigest_bytesLE]
theorem wsib_witEnc (k : WCT9.Coord) (l : Fin 7) :
    wsib (witEnc N w) k.val (WCT9.child N k).val l.val = (w.signature.openings k).path l := by
  have hc := (WCT9.child N k).isLt
  unfold wsib
  rcases l with ⟨l, hl⟩
  dsimp only
  by_cases h5 : l < 5
  · rw [if_pos (by omega), if_neg (by omega), wdig_region N w k _ (by have := auth_sib_bound _ hc l h5; omega)
        (Or.inr (by have := auth_sib_bound _ hc l h5; omega)),
      region_merkle _ _ _ _ _ _ (auth_sib_bound _ hc l h5), merkleBytes_sib hc _ ⟨l, h5⟩,
      Correctness.readDigest_bytesLE]
    rfl
  · by_cases h6 : l = 5
    · subst h6
      by_cases hk0 : k.val = 0
      · obtain rfl : k = 0 := Fin.ext hk0
        rw [if_pos (by omega), if_pos ⟨rfl, rfl⟩, wdig_legacySib0]
        rfl
      have hs : sibOff ((WCT9.child N k).val / 2 ^ 5 % 2) ≤ 48 := by unfold sibOff; split <;> omega
      rw [if_pos (by omega), if_neg (by omega), show authSibOff (WCT9.child N k).val 5 = 784 + sibOff ((WCT9.child N k).val / 2 ^ 5 % 2) by
          unfold authSibOff; rw [if_pos (by omega), authBase_five],
        wdig_region N w k _ (by omega) (Or.inl hk0), region_top _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega),
        Nat.add_sub_cancel_left, topBlock_sib _ _ _ (prevSibZ_length _ _ _), Correctness.readDigest_bytesLE]
      rfl
    · obtain rfl : l = 6 := by omega
      rw [if_neg (by omega), wtop_witEnc]
      rfl
theorem wmpad_witEnc (k : WCT9.Coord) (l : Nat) (hl : l < 5) : wmpad (witEnc N w) k.val (WCT9.child N k).val l = 0 := by
  have hc := (WCT9.child N k).isLt
  by_cases hp : authPadOff (WCT9.child N k).val l = 320
  · unfold wmpad
    rw [if_neg (by omega), hp]
    have hz := congrArg Prod.fst (wcpads_witEnc N w k (5 : Fin 6))
    simpa [wcpads, wctChainBlock, wctChainOff, wctPad0Off, WCT9.ftsIsG] using hz
  · have hb : authPadOff (WCT9.child N k).val l + 16 ≤ 320 :=
      (auth_pad_bound _ hc l hl).resolve_right hp
    unfold wmpad
    rw [if_neg (by omega), wdig_region N w k _ (by omega),
      region_merkle _ _ _ _ _ _ hb, merkleBytes_pad hc _ hl hb, readDigest_zeros]
theorem wmhpad_witEnc (k : WCT9.Coord) (l : Nat) : wmhpad (witEnc N w) k.val (WCT9.child N k).val l = 0 := by
  have hc := (WCT9.child N k).isLt
  unfold wmhpad
  split
  · rename_i hl
    have hb := auth_tw_bound _ hc l hl.1 hl.2
    rw [Nat.add_assoc, wdig_region N w k _ (by omega), region_merkle _ _ _ _ _ _ hb, merkleBytes_tw hc _ hl.1 hl.2 hb,
      readDigest_zeros]
    rfl
  · rfl
end fields
theorem witDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : witDecP N (witEnc N w) = w := by
  obtain ⟨⟨rho, openings, layers⟩, dc, ctr⟩ := w
  unfold witDecP
  simp only [WCT9.Witness.mk.injEq, WCT9.Signature.mk.injEq]
  refine ⟨⟨wrho_witEnc N _, funext fun k => ?_, funext fun lay => ?_⟩, wdc_witEnc N _,
    funext fun lay => wbcCtr_witEnc N _ lay⟩
  · have hv := fun t => wreveal_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr⟩ k t
      (WCT9.wordDigit (WCT9.rank N k) t)
    have hp := fun l => wsib_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr⟩ k l
    simp only at hv hp
    rcases ho : openings k with ⟨vals, path⟩
    rw [ho] at hv hp
    simp only [WCT9.Opening.mk.injEq]
    exact ⟨funext hv, funext hp⟩
  · exact SigGolfCandidate.T3M.LayerSignature.ext' (funext fun i => wvalue_witEnc N _ lay i)
      (funext fun j => wpath_witEnc N _ lay j)
theorem win_endpointBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (endpointBytes sig lay) (16 * i.val) 16 = bytesLE 16 ((sig.layers lay).values i) := by
  have h := window_flatMap_const (List.finRange (chainCount lay))
    (fun j => bytesLE 16 ((sig.layers lay).values j)) 16 (fun j => bytesLE_length _ _)
    i.val (by simpa using i.isLt) 0 16 (by omega)
  simpa [endpointBytes, window_full _ _ (bytesLE_length _ _)] using h

/-- Campaign T51 ("endpad"): every leaf buffer, the top one included, is `end0 | 0^16 | end1.. | 0^k`. -/
theorem win_leafBufferBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (leafBufferBytes sig lay)
      (if lay = 0 then (if i.val = 0 then 0 else 16 + 16 * i.val) else if i.val = 0 then 0 else 16 + 16 * i.val) 16 =
      bytesLE 16 ((sig.layers lay).values i) := by
  have hi := i.isLt
  have hc : 0 < chainCount lay := by fin_cases lay <;> decide
  have htlen : ((endpointBytes sig lay).take 16).length = 16 := by
    rw [List.length_take, endpointBytes_length, Nat.min_eq_left (by omega)]
  have key : ∀ k : Nat, window ((endpointBytes sig lay).take 16 ++ zeros 16 ++ (endpointBytes sig lay).drop 16 ++
      zeros k) (if i.val = 0 then 0 else 16 + 16 * i.val) 16 = bytesLE 16 ((sig.layers lay).values i) := by
    intro k
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
  unfold leafBufferBytes
  by_cases ht : lay = 0
  · rw [if_pos ht, if_pos ht]
    exact key 64
  · rw [if_neg ht, if_neg ht]
    exact key 16

theorem win_leafBuffersBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (leafBuffersBytes sig) (leafBufferSlot lay i.val - 18928) 16 =
      bytesLE 16 ((sig.layers lay).values i) := by
  have hi := i.isLt
  have hidx : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have hget : (List.finRange 4).reverse[3 - lay.val]'hidx = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes sig l).length)).sum = leafBufferBase lay - 18928 := by
    simp only [leafBufferBytes_length]
    fin_cases lay <;> decide
  let off := if lay = 0 then (if i.val = 0 then 0 else 16 + 16 * i.val) else if i.val = 0 then 0 else 16 + 16 * i.val
  have hb : off + 16 ≤ (leafBufferBytes sig lay).length := by
    rw [leafBufferBytes_length]
    fin_cases lay <;> norm_num [off, leafBufferLen, chainCount] at *
    all_goals (try split_ifs) <;> omega
  have h := window_flatMap (List.finRange 4).reverse (leafBufferBytes sig)
    (3 - lay.val) hidx off 16 (by simpa only [hget] using hb)
  rw [hp, hget] at h
  have hbase : 18928 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hoff : leafBufferSlot lay i.val - 18928 = leafBufferBase lay - 18928 + off := by
    unfold leafBufferSlot
    change leafBufferBase lay + off - 18928 = leafBufferBase lay - 18928 + off
    omega
  rw [hoff]
  exact h.trans (win_leafBufferBytes sig lay i)

theorem win_leafBuffer (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (o n : Nat) (h : o + n ≤ leafBufferLen lay) :
    window (witList N w) (leafBufferBase lay + o) n = window (leafBufferBytes w.signature lay) o n := by
  have hidx : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have hget : (List.finRange 4).reverse[3 - lay.val]'hidx = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes w.signature l).length)).sum = leafBufferBase lay - 18928 := by
    simp only [leafBufferBytes_length]
    fin_cases lay <;> decide
  have hb : o + n ≤ (leafBufferBytes w.signature lay).length := by rw [leafBufferBytes_length]; exact h
  have key := window_flatMap (List.finRange 4).reverse (leafBufferBytes w.signature) (3 - lay.val) hidx o n
    (by simpa only [hget] using hb)
  rw [hp, hget] at key
  have hbase : 18928 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hend : leafBufferBase lay + leafBufferLen lay ≤ 21984 := by fin_cases lay <;> decide
  rw [witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
    omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega),
    show leafBufferBase lay + o - (80 + 7584 + 11264) = leafBufferBase lay - 18928 + o by omega]
  exact key
/-- C3 (FULL): the honest leaf tweak high words are zero. -/
theorem wleafHigh_witEnc (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : wleafHigh (witEnc N w) lay = 0 := by
  unfold wleafHigh
  rw [wdig_witEnc, win_leafBuffer N w lay 16 16 (by fin_cases lay <;> decide)]
  have hz : window (leafBufferBytes w.signature lay) 16 16 = zeros 16 := by
    have hc : 1 ≤ chainCount lay := by fin_cases lay <;> decide
    have htlen : ((endpointBytes w.signature lay).take 16).length = 16 := by
      rw [List.length_take, endpointBytes_length]; omega
    unfold leafBufferBytes
    split
    all_goals
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
  rw [show 80 + 7584 + 11264 = 18928 by decide,
    win_leafBuffersBytes, Correctness.readDigest_bytesLE]
/-- Campaign T51 ("endpad"): the honest top leaf buffer starts with chain 0's signature value (#938: a zero pad). -/
theorem wtopLeafPad_witEnc (N : HashOutput) (w : WCT9.Witness) :
    wtopLeafPad (witEnc N w) = (w.signature.layers 0).values ⟨0, by decide⟩ := by
  have h := wbuffer_witEnc N w 0 ⟨0, by decide⟩
  unfold wtopLeafPad
  simpa [leafBufferSlot] using h
theorem padDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : padDecP N (witEnc N w) = 0 := by
  unfold padDecP
  show Pads.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = Pads.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  congr 1
  · funext k t; exact wcpads_witEnc N w k t
  · funext k t; exact wcHeaderPad_witEnc N w k t
  · funext k l; split
    · rename_i hl
      rcases hl with hl | ⟨hl5, hk0⟩
      · exact wmpad_witEnc N w k l.val hl
      · rw [hk0, hl5]; exact wmpad_start_witEnc N w _
    · rfl
  · funext k l; exact wmhpad_witEnc N w k l.val
  · funext k; split
    · exact wleafPad_witEnc N w
    · rfl
  · funext lay i; exact wchainPads_witEnc N w lay i
  · funext lay j; split
    · rename_i h; exact wmerklePad_witEnc N w lay j h
    · rfl
  · funext lay i; exact wchainHeaderPad_witEnc N w lay i
  · funext lay; exact wbcPad_witEnc N w lay
  · exact wright3_witEnc N w
  · funext lay i
    rw [wvalue_witEnc, wbuffer_witEnc, BitVec.xor_self]
    rfl
  · funext lay j; split
    · rename_i h; exact wmerkleHigh_witEnc N w lay j h
    · rfl
  · funext lay; exact wleafHigh_witEnc N w lay
  · funext lay; rw [wbcHigh_witEnc N w lay]; decide

end ClaudeWCT.W9.T3M
end
section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (eval_countCalls_bind_congr eval_countCalls_fst eval_map)
set_option linter.unusedSimpArgs false
def honestProgramCore (message : Message) : M Bool := do
  let keys ← WCT9.Rev3.keygen
  let sig ← WCT9.Rev3.sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← WCT9.Rev3.expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => WCT9.Rev3.verify message keys.1 witness
def honestProgramB (message : Message) : M Bool := do
  let keys ← WCT9.Rev3.keygen
  let sig ← WCT9.Rev3.sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let wb ← expandB message keys.1 sig
    match wb with
    | none => pure false
    | some wb => verifyP message keys.1 wb
def ExpandEqExpandN : Prop := ∀ (m : Message) (pk : Digest) (σ : WCT9.Signature),
  WCT9.Rev3.expand m pk σ = Option.map Prod.snd <$> expandN m pk σ
def VerifyPWitEncEval : Prop := ∀ (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness),
  evalWithAnswerFn answers (expandN m pk σ) = some (N, w) →
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w))
def HonestBEval : Prop := ∀ (answers : Correctness.Answers) (m : Message),
  evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m)
theorem expand_eq_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    WCT9.Rev3.expand m pk σ = Option.map Prod.snd <$> expandN m pk σ := rfl
theorem expandEqExpandN_holds : ExpandEqExpandN := expand_eq_expandN
theorem expandN0_eq (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    expandN0 m pk σ = WCT9.expandWithN WCT9.digestAttemptLimit m pk σ := rfl
structure ExpandFacts0 (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) : Prop where
  sig : w.signature = σ
  dc : w.digestCounter.toNat < WCT9.digestAttemptLimit
  digest : evalWithAnswerFn answers (digest σ.rho m w.digestCounter) = N
  adm : WCT9.admissible N = true
  cap : WCT9.capOk N = true
theorem expandN0_facts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN0 m pk σ) = some (N, w)) :
    ExpandFacts0 answers m pk σ N w := by
  simp only [expandN0, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (WCT9.digestSearch σ.rho m 0 WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (WCT9.expandLayersBC σ (WCT9.digestIndex output) 4
          (.pair (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex output) output)).1
            (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex output) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            obtain ⟨_, hcounter, houtput, hadm⟩ := WCT9.digestSearch_some_good answers σ.rho m
              WCT9.digestAttemptLimit 0 counter output (by unfold WCT9.digestAttemptLimit; norm_num) hd
            exact ⟨rfl, by simpa using hcounter, houtput, WCT9.admissible_of_producer hadm,
              (WCT9.capOk_iff output).2 ((WCT9.producerAdmissible_iff output).1 hadm).2⟩
/-- An H2 expansion is the old expansion of a completion `fillTop σ c`. -/
theorem expandN_completion (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    ∃ c, c < 2 ^ 19 ∧ w.signature = WCT9.fillTop σ c ∧
      evalWithAnswerFn answers (expandN0 m pk (WCT9.fillTop σ c)) = some (N, w) :=
  WCT9.eval_expandS answers _ m pk σ N w he
structure ExpandFacts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) : Prop where
  rho : w.signature.rho = σ.rho
  fill : ∃ c, c < 2 ^ 19 ∧ w.signature = WCT9.fillTop σ c ∧
    evalWithAnswerFn answers (expandN0 m pk (WCT9.fillTop σ c)) = some (N, w)
  dc : w.digestCounter.toNat < WCT9.digestAttemptLimit
  digest : evalWithAnswerFn answers (digest σ.rho m w.digestCounter) = N
  adm : WCT9.admissible N = true
  cap : WCT9.capOk N = true
theorem expandN_facts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    ExpandFacts answers m pk σ N w := by
  obtain ⟨c, hc, hsig, h0⟩ := expandN_completion answers m pk σ N w he
  have F := expandN0_facts answers m pk _ N w h0
  exact ⟨by rw [hsig]; rfl, ⟨c, hc, hsig, h0⟩, F.dc, F.digest, F.adm, F.cap⟩
theorem verifyP_witEnc_eval0 (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN0 m pk σ) = some (N, w)) :
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w)) := by
  have F := expandN0_facts answers m pk σ N w he
  have hv : verifyP m pk (witEnc N w) =
      digest w.signature.rho m w.digestCounter >>= verifyTailP pk (witEnc N w) := by
    rw [verifyP_eq_tail]
    unfold digestP
    rw [wdc_witEnc, wrho_witEnc, if_neg (by have := w.digestCounter.isLt; unfold WCT9.digestVerifyWindow; omega), bind_map_left]
  have hw : WCT9.Rev3.verify m pk w =
      digest w.signature.rho m w.digestCounter >>= fun N' => verifyPadsTail pk N' w 0 := by
    rw [← verifyPads_zero]
    unfold verifyPads
    rw [if_neg (by have := F.dc; omega)]
  rw [hv, hw]
  apply eval_countCalls_bind_congr
  rw [F.sig, F.digest, verifyTailP_shaped pk N _ F.adm, witDecP_witEnc, padDecP_witEnc]
theorem verifyP_witEnc_eval (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w)) := by
  obtain ⟨c, -, -, h0⟩ := expandN_completion answers m pk σ N w he
  exact verifyP_witEnc_eval0 answers m pk _ N w h0
theorem verifyPWitEncEval_holds : VerifyPWitEncEval := verifyP_witEnc_eval
theorem expandN_proj (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    expandN m pk (WCT9.proj σ) = expandN m pk σ := by
  unfold expandN WCT9.expandS
  rw [WCT9.proj_proj]
theorem expandB_proj (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    expandB m pk (WCT9.proj σ) = expandB m pk σ := by
  unfold expandB; rw [expandN_proj]
theorem eval_expandB (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    evalWithAnswerFn answers (expandB m pk σ) =
      (evalWithAnswerFn answers (expandN m pk σ)).map (fun x => witEnc x.1 x.2) := by
  unfold expandB; rw [eval_map]
theorem honestB_eval (answers : Correctness.Answers) (m : Message) :
    evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m) := by
  unfold honestProgramB honestProgramCore
  simp only [evalWithAnswerFn_bind]
  cases hs : evalWithAnswerFn answers (WCT9.Rev3.sign (evalWithAnswerFn answers WCT9.Rev3.keygen).2 m) with
  | none => rfl
  | some sig =>
      simp only []
      rw [expand_eq_expandN, evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_map, eval_expandB]
      cases hx : evalWithAnswerFn answers (expandN m (evalWithAnswerFn answers WCT9.Rev3.keygen).1 sig) with
      | none => rfl
      | some x =>
          obtain ⟨N, w⟩ := x
          simp only [Option.map_some]
          have := verifyP_witEnc_eval answers m _ sig N w hx
          have h1 := congrArg Prod.fst this
          rwa [eval_countCalls_fst, eval_countCalls_fst] at h1
theorem honestBEval_holds : HonestBEval := honestB_eval
end ClaudeWCT.W9.T3M
end

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def prefixList (p : List UInt8) (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  p ++ (witList N w).drop 7664

def prefixEnc (p : List UInt8) (N : HashOutput) (w : WCT9.Witness) : WBytes :=
  BitVec.ofNat _ (readLE (prefixList p N w))

theorem prefixList_readLE_lt (p : List UInt8) (hp : p.length=7664)
    (N : HashOutput) (w : WCT9.Witness) : readLE (prefixList p N w)<2^(8*22012) := by
  let pre := (headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)
  have hs : witList N w=pre++zeros 4 := by simp only [pre,witList,tailBytes,List.append_assoc]
  have hl : pre.length=22012 := by
    simp only [pre,List.length_append,headerBytes_length,wctBytes_length,layers_length,
      leafBuffersBytes_length,bytesLE_length,zeros,List.length_replicate]
  have hh : prefixList p N w=(p++pre.drop 7664)++zeros 4 := by
    rw [prefixList,hs,List.drop_append_of_le_length (by omega),List.append_assoc]
  have hlen : (p++pre.drop 7664).length=22012 := by simp [hp,hl]
  have hz : readLE (zeros 4)=0 := by decide
  have h256 : ∀ n : Nat,(256:Nat)^n=2^(8*n) := fun n=>by rw [pow_mul];norm_num
  rw [hh,readLE_append,hz,Nat.mul_zero,Nat.add_zero,←h256,←hlen]
  exact SigGolfCandidate.T3M.readLE_lt _

theorem prefix_window (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (off k : Nat) (ho : 7664≤off) :
    window (prefixList p N w) off k=window (witList N w) off k := by
  unfold prefixList
  rw [window_append_right _ _ _ _ (by omega),hp]
  unfold window
  rw [List.drop_drop,Nat.add_sub_of_le ho]

theorem wdig_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : 7664≤off) : wdig (prefixEnc p N w) off=wdig (witEnc N w) off := by
  rw [wdig_witEnc]
  have h := extract_readLE_lt (prefixList p N w) 22012 (prefixList_readLE_lt p hp N w) off 16
  change wdig (BitVec.ofNat _ (readLE (prefixList p N w))) off=_
  rw [wdig,h]
  exact congrArg readDigest (prefix_window p hp N w off 16 ho)

theorem wle32_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : 7664≤off) : wle32 (prefixEnc p N w) off=wle32 (witEnc N w) off := by
  rw [wle32_witEnc]
  have h := extract_readLE_lt (prefixList p N w) 22012 (prefixList_readLE_lt p hp N w) off 4
  change wle32 (BitVec.ofNat _ (readLE (prefixList p N w))) off=_
  rw [wle32,h]
  exact congrArg (fun bs=>BitVec.ofNat 32 (readLE bs)) (prefix_window p hp N w off 4 ho)

/-! ### Configuration (1)+(2): the top choice hint byte
`Paired.witEnc` writes `choiceByte witness.topHigh` at witness byte `choiceOff = 21104` (`Paired.witList :=
witListBase.set choiceOff ..`). Every other byte is the former paired encoding `baseEnc`
(= `prefixEnc (forestBytes ..) ..`), so readouts whose window avoids `choiceOff` transfer unchanged. -/
def baseEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : WBytes :=
  prefixEnc (Paired.forestBytes output witness) output (Paired.mainWitness witness)

theorem extract_ofNat_width (x n m s len : Nat) (h1 : s + len ≤ n) (h2 : s + len ≤ m) :
    (BitVec.ofNat n x).extractLsb' s len = (BitVec.ofNat m x).extractLsb' s len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    show s + i < n by omega, show s + i < m by omega]

theorem extract_readLE (L : List UInt8) (n off k : Nat) (hk : off + k ≤ n) :
    (BitVec.ofNat (8 * n) (readLE L)).extractLsb' (8 * off) (8 * k) =
      BitVec.ofNat (8 * k) (readLE ((L.drop off).take k)) := by
  rw [extract_ofNat_width (readLE L) (8 * n) (8 * (n + L.length)) _ _ (by omega) (by omega)]
  apply extract_readLE_lt
  calc readLE L < 256 ^ L.length := SigGolfCandidate.T3M.readLE_lt L
    _ = 2 ^ (8 * L.length) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ (8 * (n + L.length)) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem window_set (l : List UInt8) (c : Nat) (x : UInt8) (off k : Nat) (h : off + k ≤ c ∨ c < off) :
    ((l.set c x).drop off).take k = (l.drop off).take k := by
  rw [List.drop_set]
  split_ifs with hc
  · rfl
  · rcases h with h | h
    · exact List.take_set_of_le (by omega)
    · omega

theorem witEnc_getLsbD (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (i : Nat) (hi : i / 8 ≠ choiceOff) :
    (Paired.witEnc output witness).getLsbD i = (baseEnc output witness).getLsbD i := by
  by_cases hw : i < 8 * 22012
  · have e : ∀ x : WBytes, x.getLsbD i = (x.extractLsb' (8 * (i / 8)) (8 * 1)).getLsbD (i % 8) := by
      intro x
      rw [BitVec.getLsbD_extractLsb']
      simp [show i % 8 < 8 * 1 by omega, show 8 * (i / 8) + i % 8 = i by omega]
    have hx : (Paired.witEnc output witness).extractLsb' (8 * (i / 8)) (8 * 1) =
        (baseEnc output witness).extractLsb' (8 * (i / 8)) (8 * 1) := by
      unfold Paired.witEnc baseEnc prefixEnc Paired.witList
      rw [extract_readLE _ 22012 _ 1 (by omega), extract_readLE _ 22012 _ 1 (by omega),
        window_set _ _ _ _ _ (by omega)]
      try rfl
    rw [e (Paired.witEnc output witness), e (baseEnc output witness), hx]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

theorem witEnc_extract (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (off k : Nat) (h : off + k ≤ choiceOff ∨ choiceOff < off) :
    (Paired.witEnc output witness).extractLsb' (8 * off) (8 * k) =
      (baseEnc output witness).extractLsb' (8 * off) (8 * k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', witEnc_getLsbD _ _ _ (by omega)]

theorem wdig_witEnc_base (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : off + 16 ≤ choiceOff ∨ choiceOff < off) :
    wdig (Paired.witEnc output witness) off = wdig (baseEnc output witness) off :=
  witEnc_extract output witness off 16 h

theorem wle32_witEnc_base (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : off + 4 ≤ choiceOff ∨ choiceOff < off) :
    wle32 (Paired.witEnc output witness) off = wle32 (baseEnc output witness) off :=
  witEnc_extract output witness off 4 h

theorem witListBase_length (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) :
    (Paired.witListBase output witness).length = 22016 := by
  simp [Paired.witListBase, witList_length_eq]

theorem wtopHigh_witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) :
    wtopHigh (Paired.witEnc output witness) = witness.topHigh := by
  have hlen : choiceOff < (Paired.witListBase output witness).length := by
    rw [witListBase_length]; decide
  unfold wtopHigh wchoice
  have e : (Paired.witEnc output witness).extractLsb' (8 * choiceOff) 8 =
      (Paired.witEnc output witness).extractLsb' (8 * choiceOff) (8 * 1) := rfl
  rw [e]
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

theorem getD_getD_le (T : List (List Nat)) (B : Nat) (hT : ∀ r ∈ T, ∀ x ∈ r, x ≤ B) (i j : Nat) :
    (T.getD i []).getD j 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases h1 : T[i]? with
  | none => simp
  | some r =>
    have hr : r ∈ T := List.mem_of_getElem? h1
    cases h2 : r[j]? with
    | none => simp [h2]
    | some x => simpa [h2] using hT r hr x (List.mem_of_getElem? h2)
theorem topPlanA_le : ∀ r ∈ topPlanA, ∀ x ∈ r, x ≤ 47 := by decide +kernel
theorem topPlanB_le : ∀ r ∈ topPlanB, ∀ x ∈ r, x ≤ 47 := by decide +kernel
theorem lowerPlanL1_le : ∀ r ∈ lowerPlanL1, ∀ x ∈ r, x ≤ 21 := by decide +kernel
theorem lowerPlanL32_le : ∀ r ∈ lowerPlanL32, ∀ x ∈ r, x ≤ 21 := by decide +kernel
theorem topPlanSlot_le (leaf j : Nat) : topPlanSlot leaf j ≤ 47 := by
  unfold topPlanSlot; split
  · exact getD_getD_le _ _ topPlanA_le _ _
  · exact getD_getD_le _ _ topPlanB_le _ _
theorem lowerPlan_le (lay : Layer) (leaf j : Nat) : (lowerPlan lay leaf).getD j 0 ≤ 21 := by
  unfold lowerPlan; split
  · exact getD_getD_le _ _ lowerPlanL1_le _ _
  · exact getD_getD_le _ _ lowerPlanL32_le _ _
/-- Every Merkle window (and so every encoding row) lies below the top leaf buffer. -/
theorem merkleBlock_le (lay : Layer) (leaf j : Nat) : merkleBlock lay leaf j + 64 ≤ 21088 := by
  have h1 := topPlanSlot_le leaf j
  have h2 := lowerPlan_le lay leaf j
  unfold merkleBlock
  fin_cases lay <;> simp [layerBase] at h2 ⊢ <;> omega
/-- Every chain block lies below the top leaf buffer. -/
theorem chainBlock_le (lay : Layer) (i : Nat) : chainBlock lay i + 64 ≤ 21088 := by
  unfold chainBlock chainSlot
  fin_cases lay <;> simp [layerBase, pathSlots, chainCount] <;> (try split_ifs) <;> omega
theorem leafBufferSlot_choice (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    (leafBufferSlot lay i + 16 ≤ choiceOff ∨ choiceOff < leafBufferSlot lay i) ∧
      leafBufferSlot lay i + 16 ≤ 22012 := by
  have := leafBufferSlot_bounds lay i hi
  unfold leafBufferSlot choiceOff at *
  fin_cases lay <;> simp [leafBufferBase, chainCount] at * <;> (try split_ifs at *) <;> omega
theorem rowBlock_le (index : Nat) (lay : Layer) : rowBlock index lay + 64 ≤ 21088 := by
  unfold rowBlock
  split
  · omega
  · exact merkleBlock_le _ _ _

theorem wbcCtr_witEnc_base (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (lay : Layer) :
    wbcCtr (Paired.witEnc output witness) index lay = wbcCtr (baseEnc output witness) index lay := by
  have := rowBlock_le index lay
  unfold wbcCtr bcCounterOff
  exact wle32_witEnc_base output witness _ (Or.inl (by unfold choiceOff; omega))
theorem wbcPad_witEnc_base (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (lay : Layer) :
    wbcPad (Paired.witEnc output witness) index lay = wbcPad (baseEnc output witness) index lay := by
  have := rowBlock_le index lay
  unfold wbcPad bcCounterOff
  exact witEnc_extract output witness _ 12 (Or.inl (by unfold choiceOff; omega))
theorem wbcHigh_witEnc_base (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (lay : Layer) :
    wbcHigh (Paired.witEnc output witness) index lay = wbcHigh (baseEnc output witness) index lay := by
  have := rowBlock_le index lay
  unfold wbcHigh
  rw [wdig_witEnc_base output witness _ (Or.inl (by unfold choiceOff; omega))]
theorem wdig_hi_extract (x : WBytes) (off : Nat) :
    (wdig x off).extractLsb' 64 64 = x.extractLsb' (8 * (off + 8)) (8 * 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [wdig, BitVec.getLsbD_extractLsb']
  simp [hi, show 64 + i < 128 by omega, show 8 * off + (64 + i) = 8 * (off + 8) + i by omega,
    show i < 8 * 8 by omega]
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layerBase_lower (lay : Layer) : 7664≤layerBase lay := by fin_cases lay <;> decide

theorem wrho_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness) :
    wrho (prefixEnc p N w)=w.signature.rho := by
  unfold wrho
  rw [wdig_prefixEnc p hp N w _ (by decide)]
  exact wrho_witEnc N w

theorem wdc_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness) :
    wdc (prefixEnc p N w)=w.digestCounter := by
  unfold wdc
  rw [wle32_prefixEnc p hp N w _ (by decide)]
  exact wdc_witEnc N w

theorem wvalue_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (prefixEnc p N w) lay i.val=(w.signature.layers lay).values i := by
  unfold wvalue
  rw [wdig_prefixEnc p hp N w _ (by have := layerBase_lower lay;unfold chainBlock;omega)]
  exact wvalue_witEnc N w lay i

theorem wpath_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (i : Fin (height lay)) :
    wpath (prefixEnc p N w) lay (route (WCT9.digestIndex N) lay).1 i.val=(w.signature.layers lay).path i := by
  unfold wpath
  rw [wdig_prefixEnc p hp N w _ (by have := layerBase_lower lay;unfold merkleBlock;omega)]
  exact wpath_witEnc N w lay i

theorem wbcCtr_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (hl : lay≠3) : wbcCtr (prefixEnc p N w) (WCT9.digestIndex N) lay=w.counters lay := by
  unfold wbcCtr
  rw [wle32_prefixEnc p hp N w _ (by
    have hn : lay.val≠3 := fun h=>hl (Fin.ext h)
    have := layerBase_lower (upLayer lay)
    unfold bcCounterOff rowBlock
    rw [if_neg hn]
    unfold merkleBlock
    omega)]
  exact wbcCtr_witEnc N w lay
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wbuffer_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wdig (prefixEnc p N w) (leafBufferSlot lay i.val)=(w.signature.layers lay).values i := by
  rw [wdig_prefixEnc p hp N w _ (by have := leafBufferSlot_bounds lay i.val i.isLt;omega)]
  exact wbuffer_witEnc N w lay i

theorem wbcPad_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (hl : lay≠3) : wbcPad (prefixEnc p N w) (WCT9.digestIndex N) lay=0 := by
  have hlow : 7664≤bcCounterOff (WCT9.digestIndex N) lay+4 := by
    have hn : lay.val≠3 := fun h=>hl (Fin.ext h)
    have := layerBase_lower (upLayer lay)
    unfold bcCounterOff rowBlock
    rw [if_neg hn]
    unfold merkleBlock
    omega
  have hh : wbcPad (prefixEnc p N w) (WCT9.digestIndex N) lay=wbcPad (witEnc N w) (WCT9.digestIndex N) lay := by
    unfold wbcPad prefixEnc witEnc
    rw [show (96:Nat)=8*12 by rfl,
      extract_readLE_lt (prefixList p N w) 22012 (prefixList_readLE_lt p hp N w) _ 12,
      extract_readLE_lt (witList N w) 22012 (witList_readLE_lt N w) _ 12]
    exact congrArg (fun bs=>BitVec.ofNat 96 (readLE bs)) (prefix_window p hp N w _ 12 hlow)
  rw [hh,wbcPad_witEnc]

/-- Stage 2 (C2/C3): the row tweak high words of the L2/L1/top encodings lie in the retained tail. -/
theorem wbcHigh_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (hl : lay≠3) :
    wbcHigh (prefixEnc p N w) (WCT9.digestIndex N) lay=wbcHigh (witEnc N w) (WCT9.digestIndex N) lay := by
  unfold wbcHigh
  rw [wdig_prefixEnc p hp N w _ (by
    have hn : lay.val≠3 := fun h=>hl (Fin.ext h)
    have := layerBase_lower (upLayer lay)
    unfold rowBlock
    rw [if_neg hn]
    unfold merkleBlock
    omega)]

theorem prefix_window_left (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (off k : Nat) (ho : off+k≤7664) :
    window (prefixList p N w) off k=window p off k := by
  exact window_append_left _ _ _ _ (by omega)

theorem wdig_prefixEnc_left (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : off+16≤7664) :
    wdig (prefixEnc p N w) off=readDigest (window p off 16) := by
  unfold wdig prefixEnc
  rw [extract_readLE_lt (prefixList p N w) 22012 (prefixList_readLE_lt p hp N w) off 16]
  exact congrArg readDigest (prefix_window_left p hp N w off 16 ho)

theorem wle32_prefixEnc_left (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : off+4≤7664) :
    wle32 (prefixEnc p N w) off=BitVec.ofNat 32 (readLE (window p off 4)) := by
  unfold wle32 prefixEnc
  rw [show (32:Nat)=8*4 by rfl,
    extract_readLE_lt (prefixList p N w) 22012 (prefixList_readLE_lt p hp N w) off 4]
  exact congrArg (fun bs=>BitVec.ofNat 32 (readLE bs)) (prefix_window_left p hp N w off 4 ho)

/-- The prefix counter bytes are independent of every forest slot. Stage 2 (C3): the L3 encoding row tweak's high
word at `WIT + 24` is a witness pad with honest value `LE64 1` (`countedPrefix_pad24`); this must stay the same
function as `Paired.forestBytes` (`Witness/Encode.lean`). -/
def countedPrefix (counter : BitVec 32) (byte : Nat→UInt8) : List UInt8 :=
  (List.range 7664).map fun offset=>if 24≤offset ∧ offset<32 then
    (bytesLE 8 (1:BitVec 64)).getD (offset-24) 0 else if 32≤offset ∧ offset<36 then
    (bytesLE 4 counter).getD (offset-32) 0 else byte offset

theorem countedPrefix_length (counter : BitVec 32) (byte : Nat→UInt8) :
    (countedPrefix counter byte).length=7664 := by simp [countedPrefix]

theorem countedPrefix_counter (counter : BitVec 32) (byte : Nat→UInt8) :
    window (countedPrefix counter byte) 32 4=bytesLE 4 counter := by
  unfold countedPrefix
  rw [window_map_range _ 7664 32 4 (by decide)]
  calc
    _ = (List.range 4).map (fun i=>(bytesLE 4 counter).getD i 0) := by
      apply List.map_congr_left
      intro i hi
      have hi' : i<4 := List.mem_range.mp hi
      simp [show ¬(24≤32+i ∧ 32+i<32) by omega, show 32≤32+i ∧ 32+i<36 by omega]
    _ = bytesLE 4 counter := map_range_getD _ 4 (by simp [bytesLE_length])

/-- Stage 2 (C3): the honest prefix carries the L3 row tweak's high word `LE64 1` at `WIT + 24`. -/
theorem countedPrefix_pad24 (counter : BitVec 32) (byte : Nat→UInt8) :
    window (countedPrefix counter byte) 24 8=bytesLE 8 (1:BitVec 64) := by
  unfold countedPrefix
  rw [window_map_range _ 7664 24 8 (by decide)]
  calc
    _ = (List.range 8).map (fun i=>(bytesLE 8 (1:BitVec 64)).getD i 0) := by
      apply List.map_congr_left
      intro i hi
      have hi' : i<8 := List.mem_range.mp hi
      simp [show 24≤24+i ∧ 24+i<32 by omega]
    _ = bytesLE 8 (1:BitVec 64) := map_range_getD _ 8 (by simp [bytesLE_length])

theorem wctr3_countedPrefix (counter : BitVec 32) (byte : Nat→UInt8) (N : HashOutput) (w : WCT9.Witness) :
    wbcCtr (prefixEnc (countedPrefix counter byte) N w) (WCT9.digestIndex N) 3=counter := by
  change wle32 (prefixEnc _ N w) 32=counter
  rw [wle32_prefixEnc_left _ (countedPrefix_length _ _) _ _ _ (by decide),countedPrefix_counter,
    readLE_bytesLE_32]

/-- Stage 2 (C3): the L3 encoding row tweak's high word of the honest paired prefix is 1. -/
theorem wbcHigh3_countedPrefix (counter : BitVec 32) (byte : Nat→UInt8) (N : HashOutput) (w : WCT9.Witness) :
    wbcHigh (prefixEnc (countedPrefix counter byte) N w) (WCT9.digestIndex N) 3=1 := by
  unfold wbcHigh
  rw [wdig_high]
  change (prefixEnc (countedPrefix counter byte) N w).extractLsb' (8*24) 64=1
  unfold prefixEnc
  rw [show (64:Nat)=8*8 by rfl,
    extract_readLE_lt _ 22012 (prefixList_readLE_lt _ (countedPrefix_length _ _) N w) 24 8]
  change BitVec.ofNat 64 (readLE (window _ 24 8))=1
  rw [prefix_window_left _ (countedPrefix_length _ _) _ _ _ _ (by decide),countedPrefix_pad24]
  decide

end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

@[simp] theorem wrho_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wrho (witEnc output w) = w.signature.rho := by
  rw [show wrho (witEnc output w) = wrho (PairedReadout.baseEnc output w) from
    PairedReadout.wdig_witEnc_base output w rhoOff (Or.inr (by decide))]
  exact PairedReadout.wrho_prefixEnc _ (forestBytes_length output w) output (mainWitness w)

@[simp] theorem wdc_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wdc (witEnc output w) = w.digestCounter := by
  rw [show wdc (witEnc output w) = wdc (PairedReadout.baseEnc output w) from
    PairedReadout.wle32_witEnc_base output w dcOff (Or.inr (by decide))]
  exact PairedReadout.wdc_prefixEnc _ (forestBytes_length output w) output (mainWitness w)

theorem wvalue_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (witEnc output w) lay i.val = (w.signature.layers lay).values i := by
  have hb := PairedReadout.chainBlock_le lay i.val
  have hv : valueOff lay i.val ≤ 48 := by unfold valueOff; split_ifs <;> omega
  rw [show wvalue (witEnc output w) lay i.val = wvalue (PairedReadout.baseEnc output w) lay i.val from
    PairedReadout.wdig_witEnc_base output w _ (Or.inl (by unfold choiceOff; omega))]
  exact PairedReadout.wvalue_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay i

theorem wbuffer_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wdig (witEnc output w) (leafBufferSlot lay i.val) = (w.signature.layers lay).values i := by
  rw [PairedReadout.wdig_witEnc_base output w _ (PairedReadout.leafBufferSlot_choice lay i.val i.isLt).1]
  exact PairedReadout.wbuffer_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay i

theorem wvalueFor_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (digits : List Nat) (i : Fin (chainCount lay)) :
    wvalueFor (witEnc output w) lay digits i.val = (w.signature.layers lay).values i := by
  unfold wvalueFor
  split
  · exact wbuffer_witEnc output w lay i
  · exact wvalue_witEnc output w lay i

theorem wpath_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (i : Fin (height lay)) :
    wpath (witEnc output w) lay (route (WCT9.digestIndex output) lay).1 i.val =
      (w.signature.layers lay).path i := by
  have hb := PairedReadout.merkleBlock_le lay (route (WCT9.digestIndex output) lay).1 i.val
  have hs : ∀ x, SigGolfCandidate.T3M.sibOff x ≤ 48 := fun x => by
    unfold SigGolfCandidate.T3M.sibOff; split_ifs <;> omega
  have hs' := hs ((route (WCT9.digestIndex output) lay).1 / 2 ^ i.val % 2)
  rw [show wpath (witEnc output w) lay (route (WCT9.digestIndex output) lay).1 i.val =
      wpath (PairedReadout.baseEnc output w) lay (route (WCT9.digestIndex output) lay).1 i.val from
    PairedReadout.wdig_witEnc_base output w _ (Or.inl (by unfold choiceOff; omega))]
  exact PairedReadout.wpath_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay i

@[simp] theorem wbcCtr_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) : wbcCtr (witEnc output w) (WCT9.digestIndex output) lay = w.counters lay := by
  rw [PairedReadout.wbcCtr_witEnc_base]
  by_cases hl : lay = 3
  · subst lay
    exact PairedReadout.wctr3_countedPrefix (w.counters 3)
      (slotByte (forestSlots output w.signature)) output (mainWitness w)
  · exact PairedReadout.wbcCtr_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay hl

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
/-- Address and logical field number for one shared coordinate, including both
copies of each chain reveal. Authentication fields are numbered from six. Witness stack (charge 86): the chain
values sit at `wctChainOff i + wctValueOff i` (G chains 1, 3 value-first, 8-byte aligned). -/
def coreSlots (child count : Nat) : List (Nat × Nat) :=
  ((List.range 6).flatMap fun i=>[(ClaudeWCT.W9.T3M.wctChainOff i+ClaudeWCT.W9.T3M.wctValueOff i,i),
    (if i=0 then 640 else 672+16*i,i)]) ++
  ((List.range count).map fun level=>
    ((if level<5 then SharedPathPacking.block child level else 784)+48*(1-child/2^level%2),6+level))

/-- Witness stack (charge 86): slots are 8-byte aligned, inside the 848-byte region, clear of the two hand-off slots
(`160`, `672`), functional, and two slots at different offsets do not overlap. -/
def CoreLayoutOK (child : Nat) : Bool :=
  let slots:=coreSlots child 6
  slots.all (fun p=>decide (p.1%8=0 ∧ p.1+16≤848 ∧ (p.1+16≤160 ∨ 176≤p.1) ∧ (p.1+16≤672 ∨ 688≤p.1))) &&
  slots.all (fun p=>slots.all (fun q=>decide ((p.1=q.1→p.2=q.2) ∧ (p.1=q.1 ∨ p.1+16≤q.1 ∨ q.1+16≤p.1))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem coreLayoutOK_all : ∀child : Fin 128,CoreLayoutOK child.val=true := by
  intro child
  fin_cases child <;> decide +kernel

theorem coreSlots_subset (child count : Nat) (hc : count≤6) :
    coreSlots child count ⊆ coreSlots child 6 := by
  intro p hp
  simp only [coreSlots,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range] at hp ⊢
  rcases hp with h | ⟨i,hi,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,by omega,rfl⟩

theorem coreSlots_range (child : Fin 128) (count : Nat) (hc : count≤6)
    (p : Nat × Nat) (hp : p∈coreSlots child.val count) :
    p.1%8=0 ∧ p.1+16≤848 ∧ (p.1+16≤160 ∨ 176≤p.1) ∧ (p.1+16≤672 ∨ 688≤p.1) := by
  have h:=coreLayoutOK_all child
  simp only [CoreLayoutOK,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  exact h.1 p (coreSlots_subset child.val count hc hp)

theorem coreSlots_functional (child : Fin 128) (count : Nat) (hc : count≤6)
    (p q : Nat × Nat) (hp : p∈coreSlots child.val count) (hq : q∈coreSlots child.val count)
    (he : p.1=q.1) : p.2=q.2 := by
  have h:=coreLayoutOK_all child
  simp only [CoreLayoutOK,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  exact (h.2 p (coreSlots_subset child.val count hc hp) q (coreSlots_subset child.val count hc hq)).1 he

theorem coreSlots_disjoint (child : Fin 128) (count : Nat) (hc : count≤6)
    (p q : Nat × Nat) (hp : p∈coreSlots child.val count) (hq : q∈coreSlots child.val count) :
    p.1=q.1 ∨ p.1+16≤q.1 ∨ q.1+16≤p.1 := by
  have h:=coreLayoutOK_all child
  simp only [CoreLayoutOK,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  exact (h.2 p (coreSlots_subset child.val count hc hp) q (coreSlots_subset child.val count hc hq)).2
def CoreLayout5OK (child : Nat) : Bool := (coreSlots child 5).all (fun p=>decide (p.1+16≤784))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem coreLayout5OK_all : ∀child : Fin 128,CoreLayout5OK child.val=true := by
  intro child
  fin_cases child <;> decide +kernel
/-- Pairing stage 1: without its level-5 slot (`count ≤ 5`) a coordinate's slots end below offset 784. -/
theorem coreSlots_range5 (child : Fin 128) (count : Nat) (hc : count≤5)
    (p : Nat × Nat) (hp : p∈coreSlots child.val count) : p.1+16≤784 := by
  have h:=coreLayout5OK_all child
  simp only [CoreLayout5OK,List.all_eq_true,decide_eq_true_eq] at h
  refine h p ?_
  simp only [coreSlots,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range] at hp ⊢
  rcases hp with h | ⟨i,hi,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,by omega,rfl⟩
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def slotRegion (k : Nat) : Nat :=80+848*(8-k)
/-- C1 (X = 128): a pair's handed-off top value lands on the next region's R pad at `+160` (right) or on its leaf
pad at `+672` (left). -/
def handSlot (k : Nat) (right : Bool) : Nat :=
  if k=8 then (if right then 48 else 0)
  else slotRegion (k+1)+(if right then 160 else 672)

inductive SlotAt (children : Fin 9→Fin 128) (counts : Fin 9→Nat) (sides : Fin 9→Bool) :
    Nat→(Fin 9×Nat)→Prop
  | core (k : Fin 9) (p : Nat×Nat) (hp : p∈coreSlots (children k).val (counts k)) :
      SlotAt children counts sides (slotRegion k.val+p.1) (k,p.2)
  | hand (k : Fin 9) : SlotAt children counts sides (handSlot k.val (sides k)) (k,6+counts k)

theorem slotRegion_injective (k l a b : Nat) (hk : k<9) (hl : l<9)
    (ha : a<848) (hb : b<848) (he : slotRegion k+a=slotRegion l+b) : k=l ∧ a=b := by
  unfold slotRegion at he
  omega

/-- Witness stack (charge 86): two slots that overlap are at the same address. -/
theorem SlotAt.eq_of_overlap {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) {a b : Nat} {p q : Fin 9×Nat}
    (hp : SlotAt children counts sides a p) (hq : SlotAt children counts sides b q)
    (h1 : a<b+16) (h2 : b<a+16) : a=b := by
  cases hp with
  | core k x hx =>
    have xr:=coreSlots_range (children k) (counts k) (hc k) x hx
    have hk:=k.isLt
    cases hq with
    | core l y hy =>
      have yr:=coreSlots_range (children l) (counts l) (hc l) y hy
      have hl:=l.isLt
      by_cases he:k=l
      · subst l
        have hd:=coreSlots_disjoint (children k) (counts k) (hc k) x y hx hy
        omega
      · have hn:k.val≠l.val:=fun hv=>he (Fin.ext hv)
        unfold slotRegion at h1 h2 ⊢
        omega
    | hand l =>
      exfalso
      have hl:=l.isLt
      unfold handSlot slotRegion at h1 h2
      by_cases h8:l.val=8
      · simp only [h8,↓reduceIte] at h1 h2
        generalize sides l = s at h1 h2; cases s <;> simp at h1 h2 <;> omega
      · simp only [h8,↓reduceIte] at h1 h2
        generalize sides l = s at h1 h2; cases s <;> simp at h1 h2 <;> omega
  | hand k =>
    have hk:=k.isLt
    cases hq with
    | core l y hy =>
      exfalso
      have yr:=coreSlots_range (children l) (counts l) (hc l) y hy
      have hl:=l.isLt
      unfold handSlot slotRegion at h1 h2
      by_cases h8:k.val=8
      · simp only [h8,↓reduceIte] at h1 h2
        generalize sides k = s at h1 h2; cases s <;> simp at h1 h2 <;> omega
      · simp only [h8,↓reduceIte] at h1 h2
        generalize sides k = s at h1 h2; cases s <;> simp at h1 h2 <;> omega
    | hand l =>
      have hl:=l.isLt
      by_cases hkl:k=l
      · subst l; rfl
      · exfalso
        have hn:k.val≠l.val:=fun hv=>hkl (Fin.ext hv)
        unfold handSlot slotRegion at h1 h2
        by_cases hk8:k.val=8 <;> by_cases hl8:l.val=8
        · omega
        all_goals simp only [hk8,hl8,↓reduceIte] at h1 h2
        all_goals (generalize sides k = s at h1 h2; generalize sides l = s' at h1 h2; cases s <;> cases s' <;> simp at h1 h2 <;> omega)

theorem SlotAt.functional_of_addr {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) {a b : Nat} {p q : Fin 9×Nat}
    (hp : SlotAt children counts sides a p) (hq : SlotAt children counts sides b q) (heq : a=b) : p=q := by
  cases hp with
  | core k x hx =>
    have xr:=coreSlots_range (children k) (counts k) (hc k) x hx
    cases hq with
    | core l y hy =>
      have yr:=coreSlots_range (children l) (counts l) (hc l) y hy
      have hh:=slotRegion_injective k.val l.val x.1 y.1 k.isLt l.isLt (by omega) (by omega) heq
      have kl:k=l:=Fin.ext hh.1
      subst l
      have hxy:=coreSlots_functional (children k) (counts k) (hc k) x y hx hy hh.2
      exact Prod.ext rfl hxy
    | hand l =>
      exfalso
      have hk:=k.isLt; have hl:=l.isLt
      by_cases h8:l.val=8
      · simp only [handSlot,h8,↓reduceIte] at heq; unfold slotRegion at heq
        generalize sides l = s at heq; cases s <;> simp at heq <;> omega
      · simp only [handSlot,h8,↓reduceIte] at heq
        have hh:=slotRegion_injective k.val (l.val+1) x.1 (if sides l then 160 else 672)
          k.isLt (by omega) (by omega) (by cases sides l <;> decide) heq
        generalize sides l = s at hh; cases s <;> simp at hh <;> omega
  | hand k =>
    cases hq with
    | core l y hy =>
      exfalso
      have yr:=coreSlots_range (children l) (counts l) (hc l) y hy
      have hk:=k.isLt; have hl:=l.isLt
      by_cases h8:k.val=8
      · simp only [handSlot,h8,↓reduceIte] at heq; unfold slotRegion at heq
        generalize sides k = s at heq; cases s <;> simp at heq <;> omega
      · simp only [handSlot,h8,↓reduceIte] at heq
        have hh:=slotRegion_injective (k.val+1) l.val (if sides k then 160 else 672) y.1
          (by omega) l.isLt (by cases sides k <;> decide) (by omega) heq
        generalize sides k = s at hh; cases s <;> simp at hh <;> omega
    | hand l =>
      have kl : k=l := by
        by_contra hkl
        have hn:k.val≠l.val:=fun hv=>hkl (Fin.ext hv)
        have hk:=k.isLt; have hl:=l.isLt
        unfold handSlot slotRegion at heq
        by_cases hk8:k.val=8 <;> by_cases hl8:l.val=8
        · omega
        · simp only [hk8,hl8,↓reduceIte] at heq
          generalize sides k = s at heq; generalize sides l = s' at heq; cases s <;> cases s' <;> simp at heq <;> omega
        · simp only [hk8,hl8,↓reduceIte] at heq
          generalize sides k = s at heq; generalize sides l = s' at heq; cases s <;> cases s' <;> simp at heq <;> omega
        · simp only [hk8,hl8,↓reduceIte] at heq
          have hh:=slotRegion_injective (k.val+1) (l.val+1) (if sides k then 160 else 672)
            (if sides l then 160 else 672) (by omega) (by omega)
            (by cases sides k <;> decide) (by cases sides l <;> decide) (by unfold slotRegion; exact heq)
          omega
      subst l
      rfl
theorem SlotAt.functional {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) {a : Nat} {p q : Fin 9×Nat}
    (hp : SlotAt children counts sides a p) (hq : SlotAt children counts sides a q) : p=q :=
  SlotAt.functional_of_addr hc hp hq rfl
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem SlotAt.layout {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) (h0 : counts 0≤5) {a : Nat} {tag : Fin 9×Nat} (h : SlotAt children counts sides a tag) :
    a%8=0 ∧ a+16≤7664 ∧ (a+16≤16 ∨ 48≤a) := by
  cases h with
  | core k p hp =>
    have hr:=coreSlots_range (children k) (counts k) (hc k) p hp
    have hk:=k.isLt
    have h5 : k.val≠0 ∨ p.1+16≤784 := by
      by_cases hk0 : k.val=0
      · obtain rfl : k=0 := Fin.ext hk0
        exact Or.inr (coreSlots_range5 (children 0) (counts 0) h0 p hp)
      · exact Or.inl hk0
    unfold slotRegion
    omega
  | hand k =>
    have hk:=k.isLt
    by_cases he:k.val=8
    · cases sides k <;> simp [handSlot,he]
    · cases sides k <;> simp [handSlot,he,slotRegion] <;> omega

def readSlot (slots : List (Nat×Digest)) (offset : Nat) : UInt8 :=
  match slots.find? (fun p=>decide (p.1≤offset ∧ offset<p.1+16)) with
  | some p=>(bytesLE 16 p.2).getD (offset-p.1) 0
  | none=>0

theorem readSlot_at (slots : List (Nat×Digest))
    (ha : ∀p∈slots,∀q∈slots,p.1<q.1+16→q.1<p.1+16→p.1=q.1)
    (hf : ∀p∈slots,∀q∈slots,p.1=q.1→p.2=q.2)
    (a : Nat) (d : Digest) (hm : (a,d)∈slots) (i : Nat) (hi : i<16) :
    readSlot slots (a+i)=(bytesLE 16 d).getD i 0 := by
  unfold readSlot
  generalize he : slots.find? _=found
  cases found with
  | none =>
    have hn:=List.find?_eq_none.mp he (a,d) hm
    simp only [decide_eq_true_eq] at hn
    omega
  | some p =>
    have hp:=List.mem_of_find?_eq_some he
    have hr:=List.find?_some he
    simp only [decide_eq_true_eq] at hr
    have hpa:p.1=a:=ha p hp (a,d) hm (by simp only; omega) (by simp only; omega)
    have hpd:=hf p hp (a,d) hm hpa
    simp only [hpa,hpd,Nat.add_sub_cancel_left]

theorem readSlot_free (slots : List (Nat×Digest)) (off : Nat)
    (hf : ∀p∈slots,off<p.1∨p.1+16≤off) : readSlot slots off=0 := by
  unfold readSlot
  rw [List.find?_eq_none.mpr (fun p hp=>by
    have hh:=hf p hp
    simp only [decide_eq_true_eq]
    omega)]

theorem countedPrefix_digest (counter : BitVec 32) (slots : List (Nat×Digest))
    (ha : ∀p∈slots,∀q∈slots,p.1<q.1+16→q.1<p.1+16→p.1=q.1)
    (hf : ∀p∈slots,∀q∈slots,p.1=q.1→p.2=q.2)
    (a : Nat) (d : Digest) (hm : (a,d)∈slots) (hb : a+16≤7664)
    (hn : a+16≤24∨36≤a) :
    window (countedPrefix counter (readSlot slots)) a 16=bytesLE 16 d := by
  unfold countedPrefix
  rw [window_map_range _ _ _ _ hb]
  calc
    _ = (List.range 16).map (fun i=>(bytesLE 16 d).getD i 0) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<16:=List.mem_range.mp hi
      rw [if_neg (by omega),if_neg (by omega),readSlot_at slots ha hf a d hm i hi']
    _ = bytesLE 16 d := map_range_getD _ _ (bytesLE_length _ _)

theorem countedPrefix_pad3 (counter : BitVec 32) (slots : List (Nat×Digest))
    (hf : ∀p∈slots,p.1+16≤36∨48≤p.1) :
    window (countedPrefix counter (readSlot slots)) 36 12=zeros 12 := by
  unfold countedPrefix
  rw [window_map_range _ _ _ _ (by decide)]
  calc
    _ = (List.range 12).map (fun _=> (0:UInt8)) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<12:=List.mem_range.mp hi
      rw [if_neg (by omega),if_neg (by omega)]
      exact readSlot_free slots _ (fun p hp=>by have :=hf p hp;omega)
    _ = zeros 12 := by simp [zeros]

theorem wpad3_countedPrefix (counter : BitVec 32) (slots : List (Nat×Digest))
    (hf : ∀p∈slots,p.1+16≤36∨48≤p.1) (N : HashOutput) (w : WCT9.Witness) :
    wbcPad (prefixEnc (countedPrefix counter (readSlot slots)) N w) (WCT9.digestIndex N) 3=0 := by
  change (prefixEnc _ N w).extractLsb' (8*36) 96=0
  unfold prefixEnc
  rw [show (96:Nat)=8*12 by rfl,
    extract_readLE_lt _ 22012 (prefixList_readLE_lt _ (countedPrefix_length _ _) N w) 36 12]
  change BitVec.ofNat 96 (readLE (window _ 36 12))=0
  rw [prefix_window_left _ (countedPrefix_length _ _) _ _ _ _ (by decide),countedPrefix_pad3 counter slots hf]
  rfl
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def physicalChildren (output : HashOutput) (k : Fin 9) : Fin 128 :=
  ⟨SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val,
    SharedForest.physicalChild_lt _ _ (SharedForest.rawChildFromOutput output k).isLt⟩
def pathCounts (k : Fin 9) : Nat :=SharedV3.lastLevel k.val+1
def handSides (output : HashOutput) (k : Fin 9) : Bool :=
  decide (SharedV3.direction k.val (physicalChildren output k).val=0)
def fieldValue (sig : SharedForest.Signature) (tag : Fin 9×Nat) : Digest :=
  if h:tag.2<6 then Paired.coordinateValues sig.forest tag.1 ⟨tag.2,h⟩
  else Paired.coordinatePath sig.forest tag.1 (tag.2-6)

theorem pathCounts_le (k : Fin 9) : pathCounts k≤6 := by
  unfold pathCounts SharedV3.lastLevel
  split <;> omega

theorem topOtherOff_handSlot (output : HashOutput) (k : Fin 9) :
    SharedV3.topOtherOff k.val (physicalChildren output k).val=handSlot k.val (handSides output k) := by
  have hk:=k.isLt
  unfold SharedV3.topOtherOff V3.regionOffset handSlot handSides slotRegion SharedV3.handR SharedV3.handL
  by_cases h:k.val=8 <;> by_cases hd:SharedV3.direction k.val (physicalChildren output k).val=0
  all_goals try simp only [h] at hd
  all_goals simp [h,hd]
  all_goals omega

theorem coordinateSlot_entry (output : HashOutput) (sig : SharedForest.Signature) (k : Fin 9)
    (entry : Nat×Digest) (hm : entry∈Paired.coordinateSlots output sig k) :
    ∃tag,SlotAt (physicalChildren output) pathCounts (handSides output) entry.1 tag ∧ entry.2=fieldValue sig tag := by
  unfold Paired.coordinateSlots at hm
  simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with (⟨i,hi,he⟩ | ⟨level,hl,he⟩) | he
  · rcases he with he | he
    · subst entry
      refine ⟨(k,i.val),?_,?_⟩
      · have ha : V3.chainOffset k.val i.val+ClaudeWCT.W9.T3M.wctValueOff i.val=
            slotRegion k.val+(ClaudeWCT.W9.T3M.wctChainOff i.val+ClaudeWCT.W9.T3M.wctValueOff i.val) := by
          unfold V3.chainOffset V3.regionOffset slotRegion; omega
        show SlotAt _ _ _ (V3.chainOffset k.val i.val+ClaudeWCT.W9.T3M.wctValueOff i.val) _
        rw [ha]
        exact SlotAt.core k (ClaudeWCT.W9.T3M.wctChainOff i.val+ClaudeWCT.W9.T3M.wctValueOff i.val,i.val) (by
          apply List.mem_append_left
          apply List.mem_flatMap.mpr
          exact ⟨i.val,List.mem_range.mpr i.isLt,by simp⟩)
      · simp [fieldValue,i.isLt]
    · subst entry
      refine ⟨(k,i.val),?_,?_⟩
      · exact SlotAt.core k (V3.leafSlot i.val,i.val) (by
          apply List.mem_append_left
          apply List.mem_flatMap.mpr
          exact ⟨i.val,List.mem_range.mpr i.isLt,by simp [V3.leafSlot]⟩)
      · simp [fieldValue,i.isLt]
  · subst entry
    refine ⟨(k,6+level),?_,?_⟩
    · exact SlotAt.core k (SharedV3.sibOff (physicalChildren output k).val level,6+level) (by
        apply List.mem_append_right
        apply List.mem_map.mpr
        exact ⟨level,hl,rfl⟩)
    · simp [fieldValue]
  · subst entry
    refine ⟨(k,6+pathCounts k),?_,?_⟩
    · rw [show SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val=(physicalChildren output k).val from rfl,
        topOtherOff_handSlot]
      exact SlotAt.hand k
    · simp [fieldValue,pathCounts]

theorem forestSlot_entry (output : HashOutput) (sig : SharedForest.Signature)
    (entry : Nat×Digest) (hm : entry∈Paired.forestSlots output sig) :
    ∃tag,SlotAt (physicalChildren output) pathCounts (handSides output) entry.1 tag ∧ entry.2=fieldValue sig tag := by
  rcases List.mem_flatMap.mp hm with ⟨k,hk,he⟩
  exact coordinateSlot_entry output sig k entry he

theorem forestSlot_layout (output : HashOutput) (sig : SharedForest.Signature)
    (entry : Nat×Digest) (hm : entry∈Paired.forestSlots output sig) :
    entry.1%8=0 ∧ entry.1+16≤7664 ∧ (entry.1+16≤16∨48≤entry.1) := by
  obtain ⟨tag,hh,_⟩:=forestSlot_entry output sig entry hm
  exact hh.layout pathCounts_le (by decide)

theorem forestSlot_overlap (output : HashOutput) (sig : SharedForest.Signature)
    (p q : Nat×Digest) (hp : p∈Paired.forestSlots output sig) (hq : q∈Paired.forestSlots output sig)
    (h1 : p.1<q.1+16) (h2 : q.1<p.1+16) : p.1=q.1 := by
  obtain ⟨pt,ph,-⟩:=forestSlot_entry output sig p hp
  obtain ⟨qt,qh,-⟩:=forestSlot_entry output sig q hq
  exact ph.eq_of_overlap pathCounts_le qh h1 h2

theorem forestSlot_functional (output : HashOutput) (sig : SharedForest.Signature)
    (p q : Nat×Digest) (hp : p∈Paired.forestSlots output sig) (hq : q∈Paired.forestSlots output sig)
    (he : p.1=q.1) : p.2=q.2 := by
  obtain ⟨pt,ph,pv⟩:=forestSlot_entry output sig p hp
  obtain ⟨qt,qh,qv⟩:=forestSlot_entry output sig q hq
  rw [pv,qv,ph.functional_of_addr pathCounts_le qh he]

theorem wdig_paired_slot (output : HashOutput) (witness : SharedForest.Witness)
    (a : Nat) (d : Digest) (hm : (a,d)∈Paired.forestSlots output witness.signature) :
    wdig (Paired.witEnc output witness) a=d := by
  have hr:=forestSlot_layout output witness.signature (a,d) hm
  rw [wdig_witEnc_base output witness a (Or.inl (by unfold choiceOff; omega))]
  change wdig (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)) a=d
  rw [wdig_prefixEnc_left _ (countedPrefix_length _ _) _ _ _ hr.2.1,
    countedPrefix_digest _ _ (fun p hp q hq h1 h2=>forestSlot_overlap _ _ p q hp hq h1 h2)
      (fun p hp q hq he=>forestSlot_functional output witness.signature p q hp hq he) a d hm hr.2.1 (by omega),Correctness.readDigest_bytesLE]

theorem wpad3_paired (output : HashOutput) (witness : SharedForest.Witness) :
    wbcPad (Paired.witEnc output witness) (WCT9.digestIndex output) 3=0 := by
  rw [wbcPad_witEnc_base]
  exact wpad3_countedPrefix (witness.counters 3) (Paired.forestSlots output witness.signature)
    (fun p hp=>by have hh:=forestSlot_layout output witness.signature p hp;omega) output (Paired.mainWitness witness)
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wchainValue_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEnc output witness) (V3.chainOffset k.val i.val+ClaudeWCT.W9.T3M.wctValueOff i.val)=
      coordinateValues witness.signature.forest k i := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨i,List.mem_finRange i,by simp⟩

theorem wleafValue_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEnc output witness) (V3.regionOffset k.val+V3.leafSlot i.val)=coordinateValues witness.signature.forest k i := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨i,List.mem_finRange i,by simp⟩

theorem wsibling_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (level : Nat) (hl : level<SharedV3.lastLevel k.val+1) :
    SharedV3.sibling (witEnc output witness) k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) level =
      coordinatePath witness.signature.forest k level := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨level,List.mem_range.mpr hl,rfl⟩

theorem wtopOther_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) :
    SharedV3.topOther (witEnc output witness) k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) =
      coordinatePath witness.signature.forest k (SharedV3.lastLevel k.val+1) := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_right
  simp

theorem wbcPad_witEnc (output : HashOutput) (witness : SharedForest.Witness) (lay : Layer) :
    wbcPad (witEnc output witness) (WCT9.digestIndex output) lay=0 := by
  by_cases h:lay=3
  · subst lay;exact PairedReadout.wpad3_paired output witness
  · rw [PairedReadout.wbcPad_witEnc_base]
    exact PairedReadout.wbcPad_prefixEnc (forestBytes output witness) (forestBytes_length _ _) output (mainWitness witness) lay h

/-- Stage 2 (C2/C3): the honest paired witness has every encoding row tweak high word 1 (the L3 one at `WIT + 24` in
the forest prefix, the others in the retained tail); the paired counterpart of `ClaudeWCT.W9.T3M.wbcHigh_witEnc`. -/
theorem wbcHigh_witEnc (output : HashOutput) (witness : SharedForest.Witness) (lay : Layer) :
    wbcHigh (witEnc output witness) (WCT9.digestIndex output) lay=1 := by
  rw [PairedReadout.wbcHigh_witEnc_base]
  by_cases h:lay=3
  · subst lay
    exact PairedReadout.wbcHigh3_countedPrefix (witness.counters 3)
      (slotByte (forestSlots output witness.signature)) output (mainWitness witness)
  · -- `witEnc` is `prefixEnc (forestBytes ..)` only up to unfolding, so chain the equations with `exact`
    -- (as `wbcPad_witEnc` does) instead of rewriting.
    exact (PairedReadout.wbcHigh_prefixEnc (forestBytes output witness) (forestBytes_length _ _) output
      (mainWitness witness) lay h).trans (ClaudeWCT.W9.T3M.wbcHigh_witEnc output (mainWitness witness) lay)
end ClaudeWCT.W9.T3M.Paired

/-! ### Top-bytes layer: read-back of the top node nonces (`Paired.witEncN`)
The nonce of the level-`j` top node (`j < 11`) sits in the Z pad of its window (`noncePos`, 8 bytes; the next 8 bytes
stay 0). The pads of the 42-slot plan are pairwise disjoint and lie in `[7696, 8320)` (line-A slots 21..38, line-B
slots 0..16), so `witEncN` agrees with `witEnc` outside them. -/
namespace ClaudeWCT.W9.T3M.PairedNonce
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem topPlanA_bounds : ∀ r, r < 64 → ∀ j, j < 6 →
    21 ≤ (topPlanA.getD r []).getD j 0 ∧ (topPlanA.getD r []).getD j 0 ≤ 38 := by decide
theorem topPlanB_bounds : ∀ r, r < 64 → ∀ k, k < 5 → (topPlanB.getD r []).getD k 0 ≤ 16 := by decide
theorem topPlanA_inj : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 = (topPlanA.getD r []).getD j' 0 → j = j' := by decide
theorem topPlanB_inj : ∀ r, r < 64 → ∀ k, k < 5 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 = (topPlanB.getD r []).getD k' 0 → k = k' := by decide

theorem slot_bound (leaf j : Nat) (hj : j < 11) :
    (j < 6 → 21 ≤ topPlanSlot leaf j) ∧ topPlanSlot leaf j ≤ 38 ∧ (6 ≤ j → topPlanSlot leaf j ≤ 16) := by
  unfold topPlanSlot
  by_cases h6 : j < 6
  · rw [if_pos h6]
    have := topPlanA_bounds (leaf % 64) (Nat.mod_lt _ (by decide)) j h6
    exact ⟨fun _ => this.1, this.2, fun h => absurd h (by omega)⟩
  · rw [if_neg h6]
    have := topPlanB_bounds (leaf / 64 % 64) (Nat.mod_lt _ (by decide)) (j - 6) (by omega)
    exact ⟨fun h => absurd h h6, by omega, fun _ => this⟩

theorem slot_inj (leaf j j' : Nat) (hj : j < 11) (hj' : j' < 11) (h : topPlanSlot leaf j = topPlanSlot leaf j') :
    j = j' := by
  have b := slot_bound leaf j hj
  have b' := slot_bound leaf j' hj'
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · unfold topPlanSlot at h; rw [if_pos h6, if_pos h6'] at h
    exact topPlanA_inj _ (Nat.mod_lt _ (by decide)) j h6 j' h6' h
  · have := b.1 h6; have := b'.2.2 (by omega); omega
  · have := b'.1 h6'; have := b.2.2 (by omega); omega
  · unfold topPlanSlot at h; rw [if_neg h6, if_neg h6'] at h
    have := topPlanB_inj _ (Nat.mod_lt _ (by decide)) (j - 6) (by omega) (j' - 6) (by omega) h
    omega

theorem noncePos_eq (output : HashOutput) (j : Nat) :
    noncePos output j = 7664 + 16 * topPlanSlot (route (WCT9.digestIndex output) 0).1 j + 32 := by
  unfold noncePos merkleBlock
  rw [if_pos (show (0 : Layer).val = 0 from rfl)]
  rfl

theorem noncePos_bounds (output : HashOutput) (j : Nat) (hj : j < 11) :
    7696 ≤ noncePos output j ∧ noncePos output j + 16 ≤ 8320 := by
  have := (slot_bound (route (WCT9.digestIndex output) 0).1 j hj).2.1
  rw [noncePos_eq]; omega

theorem noncePos_disjoint (output : HashOutput) (j j' : Nat) (hj : j < 11) (hj' : j' < 11) (hne : j ≠ j') :
    noncePos output j + 16 ≤ noncePos output j' ∨ noncePos output j' + 16 ≤ noncePos output j := by
  have := slot_inj (route (WCT9.digestIndex output) 0).1 j j' hj hj'
  rw [noncePos_eq, noncePos_eq]
  omega

theorem nonceByte_free (output : HashOutput) (nonces : List Nat) (i : Nat) (b : UInt8)
    (h : ∀ j, j < 11 → i < noncePos output j ∨ noncePos output j + 8 ≤ i) : nonceByte output nonces i b = b := by
  unfold nonceByte
  rw [List.find?_eq_none.mpr]
  intro j hj
  have := h j (List.mem_range.mp hj)
  simp only [decide_eq_true_eq, not_and, not_lt]
  omega

theorem nonceByte_in (output : HashOutput) (nonces : List Nat) (j : Nat) (hj : j < 11) (i : Nat) (b : UInt8)
    (hi : noncePos output j ≤ i ∧ i < noncePos output j + 8) :
    nonceByte output nonces i b = (nonceWord nonces j).getD (i - noncePos output j) 0 := by
  unfold nonceByte
  cases hf : (List.range 11).find? (fun j => decide (noncePos output j ≤ i ∧ i < noncePos output j + 8)) with
  | none =>
      have := List.find?_eq_none.mp hf j (List.mem_range.mpr hj)
      simp only [decide_eq_true_eq] at this
      exact absurd hi this
  | some j' =>
      have hp := List.find?_some hf
      have hm := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      simp only [decide_eq_true_eq] at hp
      have : j' = j := by
        by_contra hne
        have := noncePos_disjoint output j' j hm hj hne
        omega
      subst this
      rfl

theorem witListN_length (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    (witListN output w).length = 22016 := by
  rw [witListN, List.length_mapIdx, Paired.witList_length, witListBase_length]

theorem witListN_getElem? (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (n : Nat) :
    (witListN output w)[n]? = (Paired.witList output w)[n]?.map (nonceByte output w.topNonces n) := by
  rw [witListN, List.getElem?_mapIdx]

/-- Windows avoiding every nonce pad are those of the nonce-free encoding. -/
theorem witListN_window_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k : Nat) (h : ∀ i, off ≤ i → i < off + k → ∀ j, j < 11 → i < noncePos output j ∨ noncePos output j + 8 ≤ i) :
    ((witListN output w).drop off).take k = ((Paired.witList output w).drop off).take k := by
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop, witListN_getElem?]
  split_ifs with hn
  · cases (Paired.witList output w)[off + n]? with
    | none => rfl
    | some b => simp only [Option.map_some]; rw [nonceByte_free _ _ _ _ (h (off + n) (by omega) (by omega))]
  · rfl

theorem witEncN_extract_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k : Nat) (hk : off + k ≤ 22012)
    (h : ∀ i, off ≤ i → i < off + k → ∀ j, j < 11 → i < noncePos output j ∨ noncePos output j + 8 ≤ i) :
    (witEncN output w).extractLsb' (8 * off) (8 * k) = (Paired.witEnc output w).extractLsb' (8 * off) (8 * k) := by
  unfold witEncN Paired.witEnc
  rw [extract_readLE _ 22012 _ _ hk, extract_readLE _ 22012 _ _ hk, witListN_window_free output w off k h]

/-- Outside the nonce pads area `[7696, 8320)` the nonce-carrying encoding is the former one. -/
theorem witEncN_extract_outside (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k : Nat) (hk : off + k ≤ 22012) (h : off + k ≤ 7696 ∨ 8320 ≤ off) :
    (witEncN output w).extractLsb' (8 * off) (8 * k) = (Paired.witEnc output w).extractLsb' (8 * off) (8 * k) := by
  apply witEncN_extract_free output w off k hk
  intro i hi1 hi2 j hj
  have := noncePos_bounds output j hj
  omega

theorem witListN_nonce_window (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) :
    ((witListN output w).drop (noncePos output j)).take 8 = nonceWord w.topNonces j := by
  have hb := noncePos_bounds output j hj
  have hl : (nonceWord w.topNonces j).length = 8 := by simp [nonceWord, SphincsSecurity.bytesLE_length]
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take, List.getElem?_drop, witListN_getElem?]
  split_ifs with hn
  · have hlt : noncePos output j + n < (Paired.witList output w).length := by
      rw [Paired.witList_length, witListBase_length]; omega
    rw [List.getElem?_eq_getElem hlt, Option.map_some,
      nonceByte_in output w.topNonces j hj _ _ ⟨by omega, by omega⟩, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [List.getElem?_eq_none (by omega)]

/-- The low word of the level-`j` pad is the nonce. -/
theorem witEncN_nonce_lo (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) :
    (witEncN output w).extractLsb' (8 * noncePos output j) (8 * 8) = BitVec.ofNat 64 (w.topNonces.getD j 0) := by
  have hb := noncePos_bounds output j hj
  unfold witEncN
  rw [extract_readLE _ 22012 _ _ (by omega), witListN_nonce_window output w j hj, nonceWord,
    SigGolfCandidate.T3M.readLE_bytesLE]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- The nonce-free encoding has a zero pad there (the former honest top Z pad). -/
theorem witEnc_noncePos_zero (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) : wdig (Paired.witEnc output w) (noncePos output j) = 0 := by
  have hb := noncePos_bounds output j hj
  rw [wdig_witEnc_base output w _ (Or.inl (by unfold choiceOff; omega))]
  unfold baseEnc
  rw [wdig_prefixEnc _ (forestBytes_length output w) output (mainWitness w) _ (by omega)]
  have := wmerklePad_witEnc output (mainWitness w) (0 : Layer) ⟨j, by
    show j < height 0; have : height (0 : Layer) = 12 := rfl; omega⟩ (Or.inr rfl)
  unfold wmerklePad at this
  exact this

/-- The high word of the level-`j` pad is 0. -/
theorem witEncN_nonce_hi (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) :
    (witEncN output w).extractLsb' (8 * (noncePos output j + 8)) (8 * 8) = 0 := by
  have hb := noncePos_bounds output j hj
  rw [witEncN_extract_free output w _ 8 (by omega) (by
    intro i hi1 hi2 j' hj'
    by_cases he : j' = j
    · subst he; omega
    · have := noncePos_disjoint output j j' hj hj' (Ne.symm he); omega)]
  rw [← wdig_hi_extract, witEnc_noncePos_zero output w j hj]
  rfl

/-- Read-back: the verifier's level-`j` top pad (`Pads.merkle 0 j = wmerklePad w 0 leaf j`) is the nonce. -/
theorem wmerklePad_witEncN_lo (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) :
    (wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j).extractLsb' 0 64 =
      BitVec.ofNat 64 (w.topNonces.getD j 0) := by
  unfold wmerklePad
  rw [W9Machine.wdig_lo]
  exact witEncN_nonce_lo output w j hj
theorem wmerklePad_witEncN_hi (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) :
    (wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j).extractLsb' 64 64 = 0 := by
  unfold wmerklePad
  rw [wdig_hi_extract]
  exact witEncN_nonce_hi output w j hj

/-- With no nonces (this tree's expander), the nonce-carrying encoding is the former one. -/
theorem witEncN_nil (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hn : w.topNonces = []) : witEncN output w = Paired.witEnc output w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hw : ∃ j, j < 11 ∧ noncePos output j ≤ i / 8 ∧ i / 8 < noncePos output j + 8
  · obtain ⟨j, hj, h1, h2⟩ := hw
    have hb := noncePos_bounds output j hj
    have e : ∀ x : WBytes, x.getLsbD i =
        (x.extractLsb' (8 * noncePos output j) (8 * 8)).getLsbD (i - 8 * noncePos output j) := by
      intro x
      rw [BitVec.getLsbD_extractLsb']
      simp [show i - 8 * noncePos output j < 8 * 8 by omega, show 8 * noncePos output j + (i - 8 * noncePos output j) = i by omega]
    have hz : (Paired.witEnc output w).extractLsb' (8 * noncePos output j) (8 * 8) = 0 := by
      have h0 := congrArg (fun d : Digest => d.extractLsb' 0 64) (witEnc_noncePos_zero output w j hj)
      have h1 := W9Machine.wdig_lo (Paired.witEnc output w) (noncePos output j)
      exact h1.symm.trans h0
    rw [e (witEncN output w), e (Paired.witEnc output w), witEncN_nonce_lo output w j hj, hn, hz]
    rfl
  · by_cases hlt : i < 8 * 22012
    · have e : ∀ x : WBytes, x.getLsbD i = (x.extractLsb' (8 * (i / 8)) (8 * 1)).getLsbD (i % 8) := by
        intro x
        rw [BitVec.getLsbD_extractLsb']
        simp [show i % 8 < 8 * 1 by omega, show 8 * (i / 8) + i % 8 = i by omega]
      rw [e (witEncN output w), e (Paired.witEnc output w), witEncN_extract_free output w (i / 8) 1 (by omega) (by
        intro i' hi1 hi2 j hj
        by_contra hc
        exact hw ⟨j, hj, by omega, by omega⟩)]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]
end ClaudeWCT.W9.T3M.PairedNonce

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.PairedNonce
/-- img-v6: the nonce words lie in `[7696, 8320)`, so `rho` reads the same in `witEncN`. -/
@[simp] theorem wrho_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wrho (witEncN output w) = w.signature.rho := by
  rw [← wrho_witEnc output w]
  exact witEncN_extract_outside output w rhoOff 16 (by decide) (Or.inr (by decide))
@[simp] theorem wdc_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wdc (witEncN output w) = w.digestCounter := by
  rw [← wdc_witEnc output w]
  exact witEncN_extract_outside output w dcOff 4 (by decide) (Or.inr (by decide))
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expandN_digest (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    evalWithAnswerFn answers (digest (wrho (witEncN output w)) message
      (wdc (witEncN output w))) = output := by
  obtain ⟨_,counter,_,c,hs,_,_,hw,hc,_⟩ := expandN_selections answers message pk sig output w he
  have hd := (sharedDigestSearch_some answers sig.rho message WCT9.digestAttemptLimit 0
    counter output (by decide) hs).2.2.2
  rw [wrho_witEncN,wdc_witEncN,hw,hc,nonce_retained]
  exact hd

theorem expandB_some (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (wb : WBytes)
    (he : evalWithAnswerFn answers (expandB message pk sig) = some wb) :
    ∃ output w, evalWithAnswerFn answers (expandN message pk sig) = some (output,w) ∧
      wb = witEncN output w := by
  unfold expandB at he
  rw [evalWithAnswerFn_map] at he
  cases hn : evalWithAnswerFn answers (expandN message pk sig) with
  | none => simp only [hn,Option.map_none,reduceCtorEq] at he
  | some found =>
      obtain ⟨output,w⟩ := found
      simp only [hn,Option.map_some,Option.some.injEq] at he
      exact ⟨output,w,rfl,he.symm⟩

theorem expandN_nonce (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    wrho (witEncN output w) = sig.rho := by
  obtain ⟨_,_,_,c,_,_,_,hw,_,_⟩ := expandN_selections answers message pk sig output w he
  rw [wrho_witEncN,hw,nonce_retained]
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem countedPrefix_freeWord (counter : BitVec 32) (slots : List (Nat×Digest))
    (off : Nat) (hb : off+8≤7664) (hn : off+8≤24 ∨ 36≤off)
    (hf : ∀p∈slots,off+8≤p.1 ∨ p.1+16≤off) :
    window (countedPrefix counter (readSlot slots)) off 8=zeros 8 := by
  unfold countedPrefix
  rw [window_map_range _ _ _ _ hb]
  calc
    _=(List.range 8).map (fun _=>(0:UInt8)) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<8:=List.mem_range.mp hi
      rw [if_neg (by omega),if_neg (by omega)]
      exact readSlot_free slots _ (fun p hp=>by have :=hf p hp;omega)
    _=zeros 8 := by simp [zeros]

theorem word_prefixEnc_free (counter : BitVec 32) (slots : List (Nat×Digest))
    (N : HashOutput) (w : WCT9.Witness) (off : Nat)
    (hb : off+8≤7664) (hn : off+8≤24 ∨ 36≤off)
    (hf : ∀p∈slots,off+8≤p.1 ∨ p.1+16≤off) :
    (prefixEnc (countedPrefix counter (readSlot slots)) N w).extractLsb' (8*off) 64=0 := by
  unfold prefixEnc
  rw [show (64:Nat)=8*8 by rfl,
    extract_readLE_lt _ 22012 (prefixList_readLE_lt _ (countedPrefix_length _ _) N w) off 8]
  change BitVec.ofNat 64 (readLE (window _ off 8))=0
  rw [prefix_window_left _ (countedPrefix_length _ _) _ _ _ _ hb,
    countedPrefix_freeWord counter slots off hb hn hf]
  rfl
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem countedPrefix_free (counter : BitVec 32) (slots : List (Nat×Digest))
    (off n : Nat) (hb:off+n≤7664) (hn:off+n≤32 ∨ 36≤off ∨ counter=0) (hq:off+n≤24 ∨ 32≤off)
    (hf:∀p∈slots,off+n≤p.1 ∨ p.1+16≤off) :
    window (countedPrefix counter (readSlot slots)) off n=zeros n := by
  unfold countedPrefix
  rw[window_map_range _ _ _ _ hb]
  calc
    _=(List.range n).map (fun _=>(0:UInt8)) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<n:=List.mem_range.mp hi
      split_ifs with hpad h
      · exfalso;omega
      · have hc:counter=0:=by rcases hn with hn|hn|hn <;> omega
        rw[hc]
        have he:bytesLE 4 (0:BitVec 32)=List.replicate 4 (0:UInt8):=by decide
        rw[he]
        have hx:off+i-32=0∨off+i-32=1∨off+i-32=2∨off+i-32=3:=by omega
        rcases hx with hx|hx|hx|hx <;> rw[hx] <;> rfl
      · exact readSlot_free slots _ (fun p hp=>by have:=hf p hp;omega)
    _=zeros n:=by simp[zeros]

theorem extract_prefixEnc_free (counter : BitVec 32) (slots : List (Nat×Digest))
    (N : HashOutput) (w : WCT9.Witness) (off n : Nat)
    (hb:off+n≤7664) (hn:off+n≤32 ∨ 36≤off ∨ counter=0) (hq:off+n≤24 ∨ 32≤off)
    (hf:∀p∈slots,off+n≤p.1 ∨ p.1+16≤off) :
    (prefixEnc (countedPrefix counter (readSlot slots)) N w).extractLsb' (8*off) (8*n)=0 := by
  unfold prefixEnc
  rw[extract_readLE_lt _ 22012 (prefixList_readLE_lt _ (countedPrefix_length _ _) N w) off n]
  change BitVec.ofNat (8*n) (readLE (window _ off n))=0
  rw[prefix_window_left _ (countedPrefix_length _ _) _ _ _ _ hb,
    countedPrefix_free counter slots off n hb hn hq hf]
  simp only[zeros,readLE_replicate_zero]
  rfl
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem SlotAt.free_local {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) (k : Fin 9) (off len : Nat) (hb:off+len≤848)
    (hf:∀p∈coreSlots (children k).val (counts k),off+len≤p.1 ∨ p.1+16≤off)
    (h160:off+len≤160 ∨ 176≤off) (h720:off+len≤672 ∨ 688≤off)
    {a : Nat} {tag : Fin 9×Nat} (h:SlotAt children counts sides a tag) :
    slotRegion k.val+off+len≤a ∨ a+16≤ slotRegion k.val+off := by
  cases h with
  | core l p hp =>
    have hr:=coreSlots_range (children l) (counts l) (hc l) p hp
    by_cases he:k=l
    · subst l;have hh:=hf p hp;omega
    · have hk:=k.isLt;have hl:=l.isLt
      have hn:k.val≠l.val:=by intro hv;exact he (Fin.ext hv)
      unfold slotRegion
      omega
  | hand l =>
    have hk:=k.isLt;have hl:=l.isLt
    by_cases he:l.val=8
    · cases sides l <;> simp only[handSlot,he,↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega
    · by_cases heq:k.val=l.val+1
      · simp only [handSlot,if_neg he]
        rw[←heq]
        cases sides l <;> simp only[↓reduceIte,Bool.false_eq_true] <;> omega
      · unfold handSlot
        rw[if_neg he]
        cases sides l <;> simp only[↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.Research
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Witness fields whose honest value is zero: chain pads, node pads below the R pad and (C1) the high header
word of every packed level `0..3`. -/
def zeroFields (child : Nat) : List (Nat×Nat) :=
  ((List.range 6).flatMap fun i=>[(ClaudeWCT.W9.T3M.wctChainOff i+ClaudeWCT.W9.T3M.wctPad0Off i,16),
    (ClaudeWCT.W9.T3M.wctChainOff i+24,8),(ClaudeWCT.W9.T3M.wctChainOff i+ClaudeWCT.W9.T3M.wctPad1Off i,16)]) ++
  ((List.range 6).filterMap fun l=>if l=4 then none else
    some ((if l<5 then SharedPathPacking.block child l else 784)+32,16)) ++
  ((List.range 4).map fun l=>(SharedPathPacking.block child l+24,8))

def ZeroLayoutOK (child : Nat) : Bool := (zeroFields child).all fun q=>
  decide (q.1+q.2≤848 ∧ (q.1+q.2≤160∨176≤q.1) ∧ (q.1+q.2≤672∨688≤q.1)) &&
    (coreSlots child 6).all (fun p=>decide (q.1+q.2≤p.1∨p.1+16≤q.1))

theorem zeroLayoutOK_all : ∀child : Fin 128,ZeroLayoutOK child.val=true := by
  intro child
  fin_cases child <;> decide +kernel

theorem zeroFields_free (child : Fin 128) (q : Nat×Nat) (hq:q∈zeroFields child.val) :
    q.1+q.2≤848 ∧ (q.1+q.2≤160∨176≤q.1) ∧ (q.1+q.2≤672∨688≤q.1) ∧
    (∀p∈coreSlots child.val 6,q.1+q.2≤p.1∨p.1+16≤q.1) := by
  have hh:=zeroLayoutOK_all child
  simp only[ZeroLayoutOK,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨(hh q hq).1.1,(hh q hq).1.2.1,(hh q hq).1.2.2,(hh q hq).2⟩

theorem SlotAt.zero_fields {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc:∀k,counts k≤6) (k:Fin 9) (q:Nat×Nat) (hq:q∈zeroFields (children k).val)
    {a:Nat} {tag:Fin 9×Nat} (h:SlotAt children counts sides a tag) :
    slotRegion k.val+q.1+q.2≤a ∨ a+16≤ slotRegion k.val+q.1 := by
  have hh:=zeroFields_free (children k) q hq
  exact h.free_local hc k q.1 q.2 hh.1
    (fun p hp=>hh.2.2.2 p (coreSlots_subset _ _ (hc k) hp)) hh.2.1 hh.2.2.1
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem extract_witEnc_zero_field (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (q : Nat×Nat) (hq:q∈zeroFields (physicalChildren output k).val)
    (h0 : k.val≠0 ∨ q.1+q.2≤784) :
    (Paired.witEnc output witness).extractLsb' (8*(V3.regionOffset k.val+q.1)) (8*q.2)=0 := by
  have hf:=zeroFields_free (physicalChildren output k) q hq
  have hb : V3.regionOffset k.val+q.1+q.2≤7664 := by have hk:=k.isLt;unfold V3.regionOffset;omega
  rw [witEnc_extract output witness _ _ (Or.inl (by unfold choiceOff; omega))]
  change (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)).extractLsb' _ _=0
  apply extract_prefixEnc_free
  · exact hb
  · right;left;unfold V3.regionOffset;omega
  · right;unfold V3.regionOffset;omega
  · intro p hp
    obtain ⟨tag,hs,_⟩:=forestSlot_entry output witness.signature p hp
    exact hs.zero_fields pathCounts_le k q hq

theorem chain_zero_fields (child : Nat) (i : Fin 6) :
    (ClaudeWCT.W9.T3M.wctChainOff i.val+ClaudeWCT.W9.T3M.wctPad0Off i.val,16)∈zeroFields child ∧
    (ClaudeWCT.W9.T3M.wctChainOff i.val+24,8)∈zeroFields child ∧
    (ClaudeWCT.W9.T3M.wctChainOff i.val+ClaudeWCT.W9.T3M.wctPad1Off i.val,16)∈zeroFields child := by
  have hs:∀q∈[(ClaudeWCT.W9.T3M.wctChainOff i.val+ClaudeWCT.W9.T3M.wctPad0Off i.val,16),
      (ClaudeWCT.W9.T3M.wctChainOff i.val+24,8),
      (ClaudeWCT.W9.T3M.wctChainOff i.val+ClaudeWCT.W9.T3M.wctPad1Off i.val,16)],q∈zeroFields child:=by
    intro q hq
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨i.val,List.mem_range.mpr i.isLt,hq⟩
  exact ⟨hs _ (by simp),hs _ (by simp),hs _ (by simp)⟩

/-- Witness stack (charge 86): the FTS chain blocks end below region offset 656. -/
theorem chain_field_bound (i : Fin 6) : ClaudeWCT.W9.T3M.wctChainOff i.val+64≤656 ∧
    ClaudeWCT.W9.T3M.wctPad0Off i.val≤48 ∧ ClaudeWCT.W9.T3M.wctPad1Off i.val≤48 := by
  fin_cases i <;> simp [ClaudeWCT.W9.T3M.wctChainOff,ClaudeWCT.W9.T3M.wctPad0Off,ClaudeWCT.W9.T3M.wctPad1Off,
    ClaudeWCT.WCT9.ftsIsG]

theorem chainPadA_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) : V3.chainPadA (Paired.witEnc output witness) k.val i.val=0 := by
  have hb:=chain_field_bound i
  simpa only[V3.chainPadA,V3.chainOffset,W9Machine.wdig,ClaudeWCT.W9.T3M.wdig,Nat.add_assoc] using
    extract_witEnc_zero_field output witness k _ (chain_zero_fields _ i).1 (Or.inr (by simp only; omega))

theorem chainPadB_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) : V3.chainPadB (Paired.witEnc output witness) k.val i.val=0 := by
  have hb:=chain_field_bound i
  simpa only[V3.chainPadB,V3.chainOffset,Nat.add_assoc] using
    extract_witEnc_zero_field output witness k _ (chain_zero_fields _ i).2.1 (Or.inr (by simp only; omega))

theorem chainPadC_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) : V3.chainPadC (Paired.witEnc output witness) k.val i.val=0 := by
  have hb:=chain_field_bound i
  simpa only[V3.chainPadC,V3.chainOffset,W9Machine.wdig,ClaudeWCT.W9.T3M.wdig,Nat.add_assoc] using
    extract_witEnc_zero_field output witness k _ (chain_zero_fields _ i).2.2 (Or.inr (by simp only; omega))

end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem node_zero_fields (child l : Nat) (hl:l<6) (hne:l≠4) :
    ((if l<5 then SharedPathPacking.block child l else 784)+32,16)∈zeroFields child := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_filterMap.mpr ⟨l,List.mem_range.mpr hl,by simp[hne]⟩

theorem header_zero_fields (child l : Nat) (hl:l<4) :
    (SharedPathPacking.block child l+24,8)∈zeroFields child := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨l,List.mem_range.mpr hl,rfl⟩

theorem block_bound (child : Fin 128) (l : Nat) (hl : l<5) : SharedPathPacking.block child.val l+64≤640 := by
  have h : ∀ c : Fin 128, ∀ l < 5, SharedPathPacking.block c.val l+64≤640 := by decide
  exact h child l hl
theorem nodePad_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (l : Nat) (hl:l≤SharedV3.lastLevel k.val) (hne:l≠4) :
    SharedV3.nodePad (Paired.witEnc output witness) k.val (physicalChildren output k).val l=0 := by
  have h6:l<6:=by unfold SharedV3.lastLevel at hl;split at hl <;> omega
  have h0 : k.val≠0 ∨ ((if l<5 then SharedPathPacking.block (physicalChildren output k).val l else 784)+32,16).1 +
      ((if l<5 then SharedPathPacking.block (physicalChildren output k).val l else 784)+32,16).2≤784 := by
    by_cases hk0 : k.val=0
    · right
      have hl5 : l<5 := by
        rw [hk0] at hl; unfold SharedV3.lastLevel SharedV3.first at hl; simp at hl; omega
      have hb := block_bound (physicalChildren output k) l hl5
      simp only [if_pos hl5]; omega
    · exact Or.inl hk0
  simpa only[SharedV3.nodePad,SharedV3.blkOff,W9Machine.wdig,ClaudeWCT.W9.T3M.wdig,Nat.add_assoc] using
    extract_witEnc_zero_field output witness k _ (node_zero_fields _ l h6 hne) h0

theorem nodeHPad_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (l : Nat) :
    SharedV3.nodeHPad (Paired.witEnc output witness) k.val (physicalChildren output k).val l=0 := by
  unfold SharedV3.nodeHPad
  split_ifs with hh
  · rw[SharedV3.nodeTw,W9Machine.wdig_hi]
    have hz:=extract_witEnc_zero_field output witness k _ (header_zero_fields _ l hh)
      (Or.inr (by have := block_bound (physicalChildren output k) l (by omega); simp; omega))
    simpa only[SharedV3.blkOff,if_pos (show l<5 by omega),Nat.add_assoc] using hz
  · rfl

theorem SlotAt.initial_free {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc:∀k,counts k≤6) (off:Nat) (ho:off=160∨off=672)
    {a:Nat} {tag:Fin 9×Nat} (h:SlotAt children counts sides a tag) :
    slotRegion 0+off+16≤a ∨ a+16≤ slotRegion 0+off := by
  cases h with
  | core k p hp =>
    have hr:=coreSlots_range (children k) (counts k) (hc k) p hp
    have hk:=k.isLt
    by_cases hz:k.val=0
    · unfold slotRegion
      rw[hz]
      rcases ho with ho|ho <;> omega
    · unfold slotRegion
      rcases ho with ho|ho <;> omega
  | hand k =>
    have hk:=k.isLt
    by_cases hz:k.val=8
    · cases sides k <;> simp only[handSlot,hz,↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega
    · cases sides k <;> simp only[handSlot,if_neg hz,↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega

theorem initial_word_zero (output : HashOutput) (witness : SharedForest.Witness)
    (off:Nat) (ho:off=160∨off=672) :
    W9Machine.wdig (Paired.witEnc output witness) (V3.regionOffset 0+off)=0 := by
  have hb : V3.regionOffset 0+off+16≤7664 := by rcases ho with ho|ho <;> rw[ho] <;> decide
  change (Paired.witEnc output witness).extractLsb' (8*(V3.regionOffset 0+off)) (8*16)=0
  rw [witEnc_extract output witness _ _ (Or.inl (by unfold choiceOff; omega))]
  change (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)).extractLsb' _ (8*16)=0
  apply extract_prefixEnc_free
  · rcases ho with ho|ho <;> rw[ho] <;> decide
  · right;left;unfold V3.regionOffset;omega
  · right;unfold V3.regionOffset;omega
  · intro p hp
    obtain ⟨tag,hs,_⟩:=forestSlot_entry output witness.signature p hp
    exact hs.initial_free pathCounts_le off ho

theorem initialPair_witEnc (output : HashOutput) (witness : SharedForest.Witness) :
    SharedV3.initialPair (Paired.witEnc output witness)=(0,0) := by
  exact Prod.ext (initial_word_zero output witness 672 (by simp))
    (initial_word_zero output witness 160 (by simp))
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem original_prefix_of_slots (output : HashOutput) (witness : SharedForest.Witness)
    (s t : MachineState) (W : Nat→Prop)
    (hslots : ∀p∈Paired.forestSlots output witness.signature,∀half,half<2→W (4128+p.1+8*half))
    (hread : ∀A,W A→W9Machine.OrigW (Paired.witEnc output witness) t A)
    (hframe : ∀A,A<2^64→¬W A→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))
    (hzero : ∀ (off : Nat), off + 8 ≤ 7664 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (4128+off))=0)
    (off:Nat) (hb:off+8≤7664) (ha:off%8=0) (hc:off≠32∨witness.counters 3=0) (hp:off≠24) :
    W9Machine.OrigW (Paired.witEnc output witness) t (4128+off) := by
  by_cases hw:W (4128+off)
  · exact hread _ hw
  have hf:∀p∈Paired.forestSlots output witness.signature,off+8≤p.1∨p.1+16≤off:=by
    intro p hp
    have hal: p.1%8=0:=(forestSlot_layout output witness.signature p hp).1
    by_contra hn
    have he:off=p.1∨off=p.1+8:=by omega
    rcases he with he|he
    · exact hw (by simpa[he] using hslots p hp 0 (by decide))
    · exact hw (by simpa[he,Nat.add_assoc] using hslots p hp 1 (by decide))
  have hz:(Paired.witEnc output witness).extractLsb' (8*off) 64=0:=by
    change (Paired.witEnc output witness).extractLsb' (8*off) (8*8)=0
    rw [witEnc_extract output witness _ _ (Or.inl (by unfold choiceOff; omega))]
    change (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)).extractLsb' _ (8*8)=0
    refine extract_prefixEnc_free _ _ _ _ _ _ hb ?_ (by omega) hf
    rcases hc with hc|hc
    · omega
    · exact Or.inr (Or.inr hc)
  unfold W9Machine.OrigW
  rw[hframe _ (by omega) hw,hzero off hb ha,show 4128+off-0x1020=off by omega,hz]
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem counterWord_witEnc (output : HashOutput) (witness : SharedForest.Witness) :
    (witEnc output witness).extractLsb' (8*32) 64=(witness.counters 3).setWidth 64 := by
  have hlo:=wbcCtr_witEnc output witness 3
  have hhi:=PairedReadout.wpad3_paired output witness
  change (witEnc output witness).extractLsb' 256 32=witness.counters 3 at hlo
  change (witEnc output witness).extractLsb' 288 96=0 at hhi
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hj,decide_true,Bool.true_and]
  by_cases h:j<32
  · have hh:=congrArg (fun x:BitVec 32=>x.getLsbD j) hlo
    simpa only [BitVec.getLsbD_extractLsb',h,decide_true,Bool.true_and] using hh
  · have hh:=congrArg (fun x:BitVec 96=>x.getLsbD (j-32)) hhi
    simp only [BitVec.getLsbD_extractLsb',show j-32<96 by omega,decide_true,
      Bool.true_and,BitVec.getLsbD_zero] at hh
    rw[BitVec.getLsbD_of_ge (witness.counters 3) j (by omega)]
    have hh0 : (0:BitVec 96).getLsbD (j-32)=false:=by simp
    rw[hh0] at hh
    simpa only [show 288+(j-32)=8*32+j by omega] using hh
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem word_prefixEnc (p : List UInt8) (hp : p.length=7664) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : 7664≤off) :
    (prefixEnc p N w).extractLsb' (8*off) 64=(ClaudeWCT.W9.T3M.witEnc N w).extractLsb' (8*off) 64 := by
  have h:=congrArg (fun d:Digest=>d.extractLsb' 0 64) (wdig_prefixEnc p hp N w off ho)
  change (W9Machine.wdig (prefixEnc p N w) off).extractLsb' 0 64=
    (W9Machine.wdig (ClaudeWCT.W9.T3M.witEnc N w) off).extractLsb' 0 64 at h
  rw[W9Machine.wdig_lo,W9Machine.wdig_lo] at h
  exact h
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research

/-- Configuration (1)+(2): away from the word holding the choice hint byte (`hc`). -/
theorem word_witEnc_tail (output : HashOutput) (witness : SharedForest.Witness)
    (off : Nat) (ho : 7664≤off) (hc : off+8≤choiceOff ∨ choiceOff<off) :
    (witEnc output witness).extractLsb' (8*off) 64=
      (ClaudeWCT.W9.T3M.witEnc output (mainWitness witness)).extractLsb' (8*off) 64 := by
  rw [show (64:Nat)=8*8 from rfl, PairedReadout.witEnc_extract output witness off 8 hc]
  exact PairedReadout.word_prefixEnc _ (PairedReadout.countedPrefix_length _ _) _ _ off ho
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research

theorem original_prefix_restore (output : HashOutput) (witness : SharedForest.Witness)
    (s t : MachineState)
    (hs : ∀ (off:Nat), off+8≤7664 → off%8=0 → off≠32 → W9Machine.OrigW (Paired.witEnc output witness) s (4128+off))
    (hf : Frame s t (fun A=>A=4160))
    (hc : t.getMem 4160=(witness.counters 3).setWidth 64)
    (off : Nat) (hb : off+8≤7664) (ha : off%8=0) :
    W9Machine.OrigW (Paired.witEnc output witness) t (4128+off) := by
  unfold W9Machine.OrigW
  rw[show 4128+off-0x1020=off by omega]
  by_cases he:off=32
  · subst off
    rw[Paired.counterWord_witEnc]
    exact hc
  · rw[hf.get (by omega) (by omega)]
    have h:=hs off hb ha he
    simpa only [W9Machine.OrigW,show 4128+off-0x1020=off by omega] using h
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (nodeHashP_zero)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Configuration (1)+(2): the retained tail away from the choice hint byte `choiceOff` (the top leaf tweak's
low word, which the program never reads as data; its high word is `hlh`). -/
def TailAgree (a b : WBytes) : Prop :=
  ∀ off, 7664 ≤ off → (off + 16 ≤ choiceOff ∨ choiceOff < off) → wdig a off = wdig b off

theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide

/-- Layer execution reads its chain and Merkle data only from the retained tail. -/
theorem layer_tail_fields (a b : WBytes) (h : TailAgree a b) (lay : Layer) :
    (∀ i,wchainPads a lay i=wchainPads b lay i) ∧
    (∀ i,wchainHeaderPad a lay i=wchainHeaderPad b lay i) ∧
    (∀ digits (i : Fin (chainCount lay)),wvalueFor a lay digits i.val=wvalueFor b lay digits i.val) ∧
    (∀ digits i,wvalueFor a lay digits (i % chainCount lay)=wvalueFor b lay digits (i % chainCount lay)) ∧
    (∀ leaf j,wpath a lay leaf j=wpath b lay leaf j) ∧
    (∀ leaf j,wmerklePad a lay leaf j=wmerklePad b lay leaf j) := by
  have hb : 7664≤layerBase lay := by fin_cases lay <;> decide
  have hl : 7664≤leafBufferBase lay := by fin_cases lay <;> decide
  have hh : ∀ off, 7664 ≤ off → off + 16 ≤ 21104 → wdig a off = wdig b off :=
    fun off h1 h2 => h off h1 (Or.inl (by unfold choiceOff; omega))
  have hvf : ∀ digits i, i < chainCount lay → wvalueFor a lay digits i = wvalueFor b lay digits i := by
    intro digits i hi
    unfold wvalueFor
    split
    · have := PairedReadout.leafBufferSlot_choice lay i hi
      exact h _ (by unfold leafBufferSlot; omega) this.1
    · have := PairedReadout.chainBlock_le lay i
      have hv : valueOff lay i ≤ 48 := by unfold valueOff; split_ifs <;> omega
      unfold wvalue
      exact hh _ (by unfold chainBlock; omega) (by omega)
  refine ⟨?_,?_,fun digits i => hvf digits i.val i.isLt,
    fun digits i => hvf digits _ (Nat.mod_lt _ (chainCount_pos lay)),?_,?_⟩
  · intro i
    have := PairedReadout.chainBlock_le lay i
    have h0 : pad0Off lay i ≤ 48 := by unfold pad0Off; split_ifs <;> omega
    have h1 : pad1Off lay i ≤ 48 := by unfold pad1Off; split_ifs <;> omega
    unfold wchainPads
    rw [hh _ (by unfold chainBlock; omega) (by omega), hh _ (by unfold chainBlock; omega) (by omega)]
  · intro i
    have := PairedReadout.chainBlock_le lay i
    unfold wchainHeaderPad
    rw [hh _ (by unfold chainBlock; omega) (by omega)]
  · intro leaf j
    have := PairedReadout.merkleBlock_le lay leaf j
    have hs : SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j % 2) ≤ 48 := by
      unfold SigGolfCandidate.T3M.sibOff; split_ifs <;> omega
    unfold wpath
    exact hh _ (by unfold merkleBlock; omega) (by omega)
  · intro leaf j
    have := PairedReadout.merkleBlock_le lay leaf j
    unfold wmerklePad
    exact hh _ (by unfold merkleBlock; omega) (by omega)

theorem topLeafPad_tail (a b : WBytes) (h : TailAgree a b) : wtopLeafPad a=wtopLeafPad b := by
  unfold wtopLeafPad
  exact h _ (by decide) (Or.inl (by decide))

theorem merkleHigh_tail (a b : WBytes) (h : TailAgree a b) (lay : Layer) (leaf j : Nat) :
    wmerkleHigh a lay leaf j=wmerkleHigh b lay leaf j := by
  have hb : 7664≤layerBase lay := by fin_cases lay <;> decide
  have := PairedReadout.merkleBlock_le lay leaf j
  unfold wmerkleHigh
  rw [h _ (by unfold merkleBlock; omega) (Or.inl (by unfold choiceOff; omega))]

theorem layerPairP_tail (a b : WBytes) (h : TailAgree a b) (hlh : ∀ lay, wleafHigh a lay = wleafHigh b lay)
    (index : Nat) (lay : Layer) (digits : List Nat) :
    layerPairP a index lay digits=layerPairP b index lay digits := by
  obtain ⟨hcp,hh,hv,-,hp,hm⟩ := layer_tail_fields a b h lay
  simp only [layerPairP,hcp,hh,hv,hp,hm,topLeafPad_tail a b h,hlh,merkleHigh_tail a b h]

theorem layerGuardedPairP_tail (a b : WBytes) (h : TailAgree a b) (hlh : ∀ lay, wleafHigh a lay = wleafHigh b lay)
    (index : Nat) (lay : Layer) (answer : Digest) (digits : List Nat) :
    layerGuardedPairP a index lay answer digits=layerGuardedPairP b index lay answer digits := by
  obtain ⟨hcp,hh,-,hv,hp,hm⟩ := layer_tail_fields a b h lay
  have hc : layerChainP a index lay digits=layerChainP b index lay digits := by
    funext i;simp only [layerChainP,hcp,hh,hv]
  simp only [layerGuardedPairP,hc,layerPairP_tail a b h hlh]

theorem topLayerP_tail (a b : WBytes) (h : TailAgree a b) (hlh : ∀ lay, wleafHigh a lay = wleafHigh b lay)
    (index : Nat) (answer : Digest) :
    topLayerP a index answer=topLayerP b index answer := by
  obtain ⟨hcp,hh,hv,-,hp,hm⟩ := layer_tail_fields a b h 0
  have hc : topChainP a (route index 0).2 (route index 0).1 (dataDigits 0 answer)=
      topChainP b (route index 0).2 (route index 0).1 (dataDigits 0 answer) := by
    funext i digit;simp only [topChainP,hcp,hh,hv]
  have hf : topFinishP a (route index 0).2 (route index 0).1=
      topFinishP b (route index 0).2 (route index 0).1 := by
    funext ends;simp only [topFinishP,hp,hm,topLeafPad_tail a b h,hlh,merkleHigh_tail a b h]
  simp only [topLayerP,hc,hf]

/-- `layersCanonicalBC` with the top choice hint as an explicit argument (it reads `wtopHigh w`). -/
def layersCanonicalBCH (high : Bool) (w : WBytes) (index : Nat) : Nat → WCT9.LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wbcCtr w index lay
      if counter.toNat ≥ WCT9.verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.verificationHash lay high
        (layerEncodingInputP lay tree leaf msg counter (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay))
      if n = 0 then topLayerP w index answer
      else do
        let some digits := WCT9.CanonicalPolicy.decode lay answer | pure none
        let some pair ← layerGuardedPairP w index lay answer digits | pure none
        layersCanonicalBCH high w index n (.pair pair.1 pair.2)

theorem layersCanonicalBC_eq_H (w : WBytes) (index : Nat) :
    ∀ n msg, layersCanonicalBC w index n msg = layersCanonicalBCH (wtopHigh w) w index n msg := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
    intro msg
    simp only [layersCanonicalBC, layersCanonicalBCH, ih]

theorem layersCanonicalBCH_tail (high : Bool) (a b : WBytes) (index : Nat) (h : TailAgree a b)
    (hlh : ∀ lay, wleafHigh a lay = wleafHigh b lay)
    (hc : ∀ lay,wbcCtr a index lay=wbcCtr b index lay)
    (hp : ∀ lay,wbcPad a index lay=wbcPad b index lay)
    (hh : ∀ lay,wbcHigh a index lay=wbcHigh b index lay) :
    ∀n left right,layersCanonicalBCH high a index n (.pair left right)=
      layersCanonicalBCH high b index n (.pair left right) := by
  intro n
  induction n with
  | zero=>intro left right;rfl
  | succ n ih=>
    intro left right
    -- Stage 2 (C2/C3): the encoding row tweak's high word `wbcHigh` is a witness pad (`hh`).
    simp only [layersCanonicalBCH,hc,hp,hh,layerEncodingInputP,topLayerP_tail a b h hlh,
      layerGuardedPairP_tail a b h hlh,ih]

end ClaudeWCT.W9.T3M.Paired
end
