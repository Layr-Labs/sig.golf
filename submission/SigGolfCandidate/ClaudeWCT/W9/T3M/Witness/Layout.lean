import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.T3M.Witness.Queries

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff chainP nodeHashP PubGood allQ_bind allQ_mapM allQ_foldlM pubGood_chainP
  pubGood_leafHash pubGood_nodeHashP)
open SigGolfCandidate.T3M.SecurityExtraction (hashPath merkleInput merkleInputH merkleHigh foldlM_finRange_eq_hashPath)
/-- Nested FTS (r1-1): the witness starts at absolute 1216 (was 2048). Campaign S2 (S1 lower/top on 926c9bce): W 24908,
it ends at 26124 and the message moves to 26128. -/
def wsize : Nat := 24908
abbrev WBytes := BitVec (8 * 24908)
def wbyte (w : WBytes) (i : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * i) 8)
def wdig (w : WBytes) (off : Nat) : Digest := w.extractLsb' (8 * off) 128
def wle32 (w : WBytes) (off : Nat) : BitVec 32 := w.extractLsb' (8 * off) 32
def rhoOff : Nat := 24880
def dcOff : Nat := 24904
def layerBase (lay : Layer) : Nat := (![8256, 12496, 15616, 18688] : Layer → Nat) lay
def pathSlots (lay : Layer) : Nat := (![49, 23, 20, 20] : Layer → Nat) lay
def lowerPlanL1 : List (List Nat) :=[[1,4,7,10,13,16,19],[0,4,7,10,13,16,19],[4,0,7,10,13,16,19],[3,0,7,10,13,16,19],[4,7,0,10,13,16,19],[3,7,0,10,13,16,19],[7,3,0,10,13,16,19],[6,3,0,10,13,16,19],[4,7,10,0,13,16,19],[3,7,10,0,13,16,19],[7,3,10,0,13,16,19],[6,3,10,0,13,16,19],[7,10,3,0,13,16,19],[6,10,3,0,13,16,19],[10,6,3,0,13,16,19],[9,6,3,0,13,16,19],[4,7,10,13,0,16,19],[3,7,10,13,0,16,19],[7,3,10,13,0,16,19],[6,3,10,13,0,16,19],[7,10,3,13,0,16,19],[6,10,3,13,0,16,19],[10,6,3,13,0,16,19],[9,6,3,13,0,16,19],[7,10,13,3,0,16,19],[6,10,13,3,0,16,19],[10,6,13,3,0,16,19],[9,6,13,3,0,16,19],[10,13,6,3,0,16,19],[9,13,6,3,0,16,19],[13,9,6,3,0,16,19],[12,9,6,3,0,16,19],[4,7,10,13,16,0,19],[3,7,10,13,16,0,19],[7,3,10,13,16,0,19],[6,3,10,13,16,0,19],[7,10,3,13,16,0,19],[6,10,3,13,16,0,19],[10,6,3,13,16,0,19],[9,6,3,13,16,0,19],[7,10,13,3,16,0,19],[6,10,13,3,16,0,19],[10,6,13,3,16,0,19],[9,6,13,3,16,0,19],[10,13,6,3,16,0,19],[9,13,6,3,16,0,19],[13,9,6,3,16,0,19],[12,9,6,3,16,0,19],[7,10,13,16,3,0,19],[6,10,13,16,3,0,19],[10,6,13,16,3,0,19],[9,6,13,16,3,0,19],[10,13,6,16,3,0,19],[9,13,6,16,3,0,19],[13,9,6,16,3,0,19],[12,9,6,16,3,0,19],[10,13,16,6,3,0,19],[9,13,16,6,3,0,19],[13,9,16,6,3,0,19],[12,9,16,6,3,0,19],[13,16,9,6,3,0,19],[12,16,9,6,3,0,19],[16,12,9,6,3,0,19],[15,12,9,6,3,0,19],[4,7,10,13,16,19,0],[3,7,10,13,16,19,0],[7,3,10,13,16,19,0],[6,3,10,13,16,19,0],[7,10,3,13,16,19,0],[6,10,3,13,16,19,0],[10,6,3,13,16,19,0],[9,6,3,13,16,19,0],[7,10,13,3,16,19,0],[6,10,13,3,16,19,0],[10,6,13,3,16,19,0],[9,6,13,3,16,19,0],[10,13,6,3,16,19,0],[9,13,6,3,16,19,0],[13,9,6,3,16,19,0],[12,9,6,3,16,19,0],[7,10,13,16,3,19,0],[6,10,13,16,3,19,0],[10,6,13,16,3,19,0],[9,6,13,16,3,19,0],[10,13,6,16,3,19,0],[9,13,6,16,3,19,0],[13,9,6,16,3,19,0],[12,9,6,16,3,19,0],[10,13,16,6,3,19,0],[9,13,16,6,3,19,0],[13,9,16,6,3,19,0],[12,9,16,6,3,19,0],[13,16,9,6,3,19,0],[12,16,9,6,3,19,0],[16,12,9,6,3,19,0],[15,12,9,6,3,19,0],[7,10,13,16,19,3,0],[6,10,13,16,19,3,0],[10,6,13,16,19,3,0],[9,6,13,16,19,3,0],[10,13,6,16,19,3,0],[9,13,6,16,19,3,0],[13,9,6,16,19,3,0],[12,9,6,16,19,3,0],[10,13,16,6,19,3,0],[9,13,16,6,19,3,0],[13,9,16,6,19,3,0],[12,9,16,6,19,3,0],[13,16,9,6,19,3,0],[12,16,9,6,19,3,0],[16,12,9,6,19,3,0],[15,12,9,6,19,3,0],[10,13,16,19,6,3,0],[9,13,16,19,6,3,0],[13,9,16,19,6,3,0],[12,9,16,19,6,3,0],[13,16,9,19,6,3,0],[12,16,9,19,6,3,0],[16,12,9,19,6,3,0],[15,12,9,19,6,3,0],[13,16,19,9,6,3,0],[12,16,19,9,6,3,0],[16,12,19,9,6,3,0],[15,12,19,9,6,3,0],[16,19,12,9,6,3,0],[15,19,12,9,6,3,0],[19,15,12,9,6,3,0],[18,15,12,9,6,3,0]]
def lowerPlanL32 : List (List Nat) :=[[1,4,7,10,13,16],[0,4,7,10,13,16],[4,0,7,10,13,16],[3,0,7,10,13,16],[4,7,0,10,13,16],[3,7,0,10,13,16],[7,3,0,10,13,16],[6,3,0,10,13,16],[4,7,10,0,13,16],[3,7,10,0,13,16],[7,3,10,0,13,16],[6,3,10,0,13,16],[7,10,3,0,13,16],[6,10,3,0,13,16],[10,6,3,0,13,16],[9,6,3,0,13,16],[4,7,10,13,0,16],[3,7,10,13,0,16],[7,3,10,13,0,16],[6,3,10,13,0,16],[7,10,3,13,0,16],[6,10,3,13,0,16],[10,6,3,13,0,16],[9,6,3,13,0,16],[7,10,13,3,0,16],[6,10,13,3,0,16],[10,6,13,3,0,16],[9,6,13,3,0,16],[10,13,6,3,0,16],[9,13,6,3,0,16],[13,9,6,3,0,16],[12,9,6,3,0,16],[4,7,10,13,16,0],[3,7,10,13,16,0],[7,3,10,13,16,0],[6,3,10,13,16,0],[7,10,3,13,16,0],[6,10,3,13,16,0],[10,6,3,13,16,0],[9,6,3,13,16,0],[7,10,13,3,16,0],[6,10,13,3,16,0],[10,6,13,3,16,0],[9,6,13,3,16,0],[10,13,6,3,16,0],[9,13,6,3,16,0],[13,9,6,3,16,0],[12,9,6,3,16,0],[7,10,13,16,3,0],[6,10,13,16,3,0],[10,6,13,16,3,0],[9,6,13,16,3,0],[10,13,6,16,3,0],[9,13,6,16,3,0],[13,9,6,16,3,0],[12,9,6,16,3,0],[10,13,16,6,3,0],[9,13,16,6,3,0],[13,9,16,6,3,0],[12,9,16,6,3,0],[13,16,9,6,3,0],[12,16,9,6,3,0],[16,12,9,6,3,0],[15,12,9,6,3,0]]
/-- Campaign S1 top path: line A (levels 0..5, region offsets in [400,784), VER table P = 448) indexed by `leaf % 64`. -/
def topPlanA : List (List Nat) :=[[416,544,592,640,688,464],[400,544,592,640,688,464],[416,528,592,640,688,464],[400,528,592,640,688,464],[416,544,608,672,720,464],[400,544,608,672,720,464],[416,528,608,672,720,464],[400,528,608,672,720,464],[416,544,592,656,720,464],[400,544,592,656,720,464],[416,528,592,656,720,464],[400,528,592,656,720,464],[416,544,656,608,720,464],[400,544,656,608,720,464],[416,528,656,608,720,464],[400,528,656,608,720,464],[416,544,592,640,704,464],[400,544,592,640,704,464],[416,528,592,640,704,464],[400,528,592,640,704,464],[416,544,656,720,608,464],[400,544,656,720,608,464],[416,528,656,720,608,464],[400,528,656,720,608,464],[416,544,592,704,656,464],[400,544,592,704,656,464],[416,528,592,704,656,464],[400,528,592,704,656,464],[416,544,704,656,608,464],[400,544,704,656,608,464],[416,528,704,656,608,464],[400,528,704,656,608,464],[464,528,592,656,720,400],[464,528,592,656,720,400],[528,464,592,656,720,400],[528,464,592,656,720,400],[528,592,464,656,720,400],[528,592,464,656,720,400],[592,528,464,656,720,400],[592,528,464,656,720,400],[528,592,656,464,720,400],[528,592,656,464,720,400],[592,528,656,464,720,400],[592,528,656,464,720,400],[592,656,528,464,720,400],[592,656,528,464,720,400],[656,592,528,464,720,400],[656,592,528,464,720,400],[528,592,656,720,464,400],[528,592,656,720,464,400],[592,528,656,720,464,400],[592,528,656,720,464,400],[592,656,528,720,464,400],[592,656,528,720,464,400],[656,592,528,720,464,400],[656,592,528,720,464,400],[592,656,720,528,464,400],[592,656,720,528,464,400],[656,592,720,528,464,400],[656,592,720,528,464,400],[656,720,592,528,464,400],[656,720,592,528,464,400],[720,656,592,528,464,400],[720,656,592,528,464,400]]
/-- Campaign S1 top path: line B (levels 6..11, region offsets in [0,384), standard line rule on bits 6..11) indexed by
`leaf / 64 % 64`. -/
def topPlanB : List (List Nat) :=[[0,64,128,192,256,320],[0,64,128,192,256,320],[64,0,128,192,256,320],[64,0,128,192,256,320],[64,128,0,192,256,320],[64,128,0,192,256,320],[128,64,0,192,256,320],[128,64,0,192,256,320],[64,128,192,0,256,320],[64,128,192,0,256,320],[128,64,192,0,256,320],[128,64,192,0,256,320],[128,192,64,0,256,320],[128,192,64,0,256,320],[192,128,64,0,256,320],[192,128,64,0,256,320],[64,128,192,256,0,320],[64,128,192,256,0,320],[128,64,192,256,0,320],[128,64,192,256,0,320],[128,192,64,256,0,320],[128,192,64,256,0,320],[192,128,64,256,0,320],[192,128,64,256,0,320],[128,192,256,64,0,320],[128,192,256,64,0,320],[192,128,256,64,0,320],[192,128,256,64,0,320],[192,256,128,64,0,320],[192,256,128,64,0,320],[256,192,128,64,0,320],[256,192,128,64,0,320],[64,128,192,256,320,0],[64,128,192,256,320,0],[128,64,192,256,320,0],[128,64,192,256,320,0],[128,192,64,256,320,0],[128,192,64,256,320,0],[192,128,64,256,320,0],[192,128,64,256,320,0],[128,192,256,64,320,0],[128,192,256,64,320,0],[192,128,256,64,320,0],[192,128,256,64,320,0],[192,256,128,64,320,0],[192,256,128,64,320,0],[256,192,128,64,320,0],[256,192,128,64,320,0],[128,192,256,320,64,0],[128,192,256,320,64,0],[192,128,256,320,64,0],[192,128,256,320,64,0],[192,256,128,320,64,0],[192,256,128,320,64,0],[256,192,128,320,64,0],[256,192,128,320,64,0],[192,256,320,128,64,0],[192,256,320,128,64,0],[256,192,320,128,64,0],[256,192,320,128,64,0],[256,320,192,128,64,0],[256,320,192,128,64,0],[320,256,192,128,64,0],[320,256,192,128,64,0]]
def topPlan (leaf j : Nat) : Nat :=
  if j < 6 then (topPlanA.getD (leaf % 64) []).getD j 0 else (topPlanB.getD (leaf / 64 % 64) []).getD (j - 6) 0
def lowerPlan (lay : Layer) (leaf : Nat) : List Nat :=
  if lay.val = 1 then lowerPlanL1.getD (leaf % 128) [] else lowerPlanL32.getD (leaf % 64) []
/-- Offset of the level-`j` fold window of the authentication path inside the layer's path area (campaign S1: the top
path follows the two-line `topPlan`, lower paths their `lowerPlan` slots). -/
def pathOff (lay : Layer) (leaf j : Nat) : Nat :=
  if lay.val = 0 then topPlan leaf j else 16 * (lowerPlan lay leaf).getD j 0
def merkleBlock (lay : Layer) (leaf j : Nat) : Nat :=
  layerBase lay + pathOff lay leaf j
def chainBlock (lay : Layer) (i : Nat) : Nat :=
  layerBase lay + 16 * pathSlots lay + 64 * (chainCount lay - 1 - i)
def wrho (w : WBytes) : Digest := wdig w rhoOff
def wdc (w : WBytes) : BitVec 32 := wle32 w dcOff
def wdcWord (w : WBytes) : BitVec 64 := w.extractLsb' (8 * dcOff) 64
theorem wdc_toNat_le (w : WBytes) : (wdc w).toNat ≤ (wdcWord w).toNat := by
  unfold wdc wle32 wdcWord
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  rw [show (2 : Nat) ^ 32 = 2 ^ 32 from rfl, ← Nat.mod_mod_of_dvd _ (show 2 ^ 32 ∣ 2 ^ 64 by norm_num)]
  exact Nat.mod_le _ _
def wvalue (w : WBytes) (lay : Layer) (i : Nat) : Digest := wdig w (chainBlock lay i + 48)
/-- Offsets in expanded witness memory, before its 2048-byte machine base. -/
def leafBufferBase (lay : Layer) : Nat := (![23968,23232,22496,21760] : Layer → Nat) lay

def leafBufferSlot (lay : Layer) (i : Nat) : Nat :=
  leafBufferBase lay + (if lay = 0 then 32+16*i else if i = 0 then 0 else 16+16*i)

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
    21760 ≤ leafBufferBase lay ∧ leafBufferBase lay ≤ 23968 ∧ leafBufferBase lay % 16 = 0 := by
  fin_cases lay <;> decide +kernel

theorem leafBufferSlot_bounds (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    21760 ≤ leafBufferSlot lay i ∧ leafBufferSlot lay i + 32 ≤ 24880 ∧
      leafBufferSlot lay i % 16 = 0 := by
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
        simpa only [hpred] using hprevious.2.2
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
  (wdig w (chainBlock lay i), wdig w (chainBlock lay i + 32))
def wchainHeaderPad (w : WBytes) (lay : Layer) (i : Nat) : BitVec 64 :=
  (wdig w (chainBlock lay i + 16)).extractLsb' 64 64
def wpath (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest :=
  wdig w (merkleBlock lay leaf j + sibOff (leaf / 2 ^ j % 2))
def wmerklePad (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest := wdig w (merkleBlock lay leaf j + 32)
theorem layerBase_values : List.ofFn (fun lay : Layer => layerBase lay) = [8256, 12496, 15616, 18688] := rfl
theorem layerBase_tiles : ∀ lay : Fin 3,
    layerBase lay.castSucc + 16 * pathSlots lay.castSucc + 64 * chainCount lay.castSucc = layerBase lay.succ := by
  decide
theorem layerBase_end : layerBase 3 + 16 * pathSlots 3 + 64 * chainCount 3 = leafBufferBase 3 := rfl
theorem dcOff_end : dcOff + 4 = wsize := rfl
/-- Campaign S2: high word of a top/lower fold tweak (bytes 24..32 of the fold window), a witness pad (honest 0). -/
def wmerkleHigh (w : WBytes) (lay : Layer) (leaf j : Nat) : BitVec 64 :=
  (wdig w (merkleBlock lay leaf j + 16)).extractLsb' 64 64
/-- Campaign S2 padded fold: the one-word label's high word `hp` and the pad at bytes 32..48 come from the witness;
the answer is projected by side (`nodeHigh`). -/
def nodeHashPH (lay tree heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : M Digest :=
  projHash (nodeHigh 3 lay heap) (SigGolfCandidate.T3M.SecurityInputs.nodeInputPH 3 lay tree heap left hp pad right)
theorem pubGood_nodeHashPH (lay tree heap : Nat) (l : Digest) (hp : BitVec 64) (p r : Digest) :
    AllQueriesSatisfy (nodeHashPH lay tree heap l hp p r) PubGood :=
  SigGolfCandidate.T3M.pubGood_projHash _ _
    (by simp [SigGolfCandidate.T3M.SecurityInputs.nodeInputPH, SigGolfCandidate.T3M.SecurityInputs.block4,
      SphincsSecurity.bytesLE_length])
def topLeafHigh (w : WBytes) : BitVec 64 :=
  (wdig w (leafBufferBase 0 + 16)).extractLsb' 64 64
def topLeafInputP (tree leaf : Nat) (hp : BitVec 64) (ends : List Digest) : HashInput :=
  zero16 ++ SphincsSecurity.bytesLE 16 (hp ++ hyperWord 0 (tree * 2 ^ height 0 + leaf)) ++
    ends.flatMap (SphincsSecurity.bytesLE 16)
def topLeafHashP (tree leaf : Nat) (hp : BitVec 64) (ends : List Digest) : M Digest :=
  projHash (leafHigh leaf) (topLeafInputP tree leaf hp ends)
theorem topLeafHashP_zero (tree leaf : Nat) (ends : List Digest) :
    topLeafHashP tree leaf 0 ends = leafHash 0 tree leaf ends := by
  simp [topLeafHashP, topLeafInputP, leafHash, leafInput, leafTweak]
def leafFor (w : WBytes) (lay : Layer) (tree leaf : Nat) (ends : List Digest) : M Digest :=
  if lay = 0 then topLeafHashP tree leaf (topLeafHigh w) ends else leafHash lay tree leaf ends
theorem pubGood_topLeafHashP (tree leaf : Nat) (hp : BitVec 64) (ends : List Digest) :
    AllQueriesSatisfy (topLeafHashP tree leaf hp ends) PubGood :=
  SigGolfCandidate.T3M.pubGood_projHash _ _
    (by simp [topLeafInputP, SphincsSecurity.bytesLE_length, zero16])
theorem pubGood_leafFor (w : WBytes) (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafFor w lay tree leaf ends) PubGood := by
  unfold leafFor
  split_ifs
  · exact pubGood_topLeafHashP _ _ _ _
  · exact SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _
def layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
  let value ← leafFor w lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashPH lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerkleHigh w lay leaf j.val) (wmerklePad w lay leaf j.val) pair.2) value
def layerLeafP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
  leafFor w lay tree leaf ends
theorem layerP_eq_hashPath (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = (layerLeafP w index lay digits >>= fun value =>
      hashPath (merkleHigh 3 lay.val (height lay) (route index lay).1)
        (merkleInputH 3 lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1)) (height lay) value) := by
  unfold layerP layerLeafP
  rcases route index lay with ⟨leaf, tree⟩
  dsimp only
  rw [bind_assoc]
  congr 1
  funext ends
  congr 1
  funext value
  exact foldlM_finRange_eq_hashPath (merkleHigh 3 lay.val (height lay) leaf)
    (merkleInputH 3 lay.val tree (height lay) leaf (wpath w lay leaf) (wmerklePad w lay leaf) (wmerkleHigh w lay leaf))
    (height lay) value
theorem pubGood_layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (layerP w index lay digits) PubGood := by
  unfold layerP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chainP _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafFor _ _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHashPH _ _ _ _ _ _ _) _
end ClaudeWCT.W9.T3M
