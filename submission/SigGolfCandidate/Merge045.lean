import SigGolfCandidate.LegacyCodec

section

/-! Compact serialization for the shared forest. -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
abbrev SharedSignature := SigGolfCandidate.Research.SharedForest.Signature
open SigGolfCandidate.T3M (digNat getD_append_left' getD_append_right' getD_ofFn'
  chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)

def pairList (p : PairOpening) : List Digest :=
  ((List.ofFn p.firstValues ++ List.ofFn p.firstPath) ++
    List.ofFn p.secondValues) ++ List.ofFn p.secondPath
def singletonList (p : SingletonOpening) : List Digest :=
  List.ofFn p.values ++ List.ofFn p.path
def layerList (s : SharedSignature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
def sigDigests (s : SharedSignature) : List Digest :=
  (([s.rho] ++ (List.ofFn s.forest.pairs).flatMap pairList) ++ singletonList s.forest.singleton) ++
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3)))
/-- T51: top values at 114..164, top path 165..176, L1 at 177, L2 at 227, L3 at 276 (325 digests). -/
def layIdx (lay : Layer) : Nat := (![114,177,227,276] : Layer → Nat) lay
theorem pairList_length (p : PairOpening) : (pairList p).length = 25 := by simp [pairList]
theorem singletonList_length (p : SingletonOpening) : (singletonList p).length = 13 := by
  simp [singletonList]
theorem pairs_length (s : SharedSignature) : ((List.ofFn s.forest.pairs).flatMap pairList).length = 100 := by
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, pairList_length]
  rfl
theorem layerList_length (s : SharedSignature) (lay : Layer) :
    (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem sigDigests_length (s : SharedSignature) : (sigDigests s).length = 325 := by
  simp only [sigDigests, List.length_append, List.length_singleton, pairs_length,
    singletonList_length, layerList_length]
  rfl

/-- U16b: the 5,193-byte compact signature (324 digests + a 9-byte tail; T51: 5,195 bytes, #938 img-v6: 5,239). -/
abbrev CBytes := Bytes 5192
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- Offset of the X field in the top `b_j = topZeroBits j` bits of the path node at height `j` (`j = 1..10`):
`Σ_{h < j} b_h` = 0, 2, 4, 7, 11, 16, 22, 29 for `j = 3..10` (heights 1, 2 carry no bits). -/
def xOff (j : Nat) : Nat := ((List.range j).map topZeroBits).sum
def clearTop (j : Nat) (d : Digest) : Digest := BitVec.ofNat 128 (d.toNat % 2 ^ (128 - j))
def topBits (j : Nat) (d : Digest) : Nat := d.toNat / 2 ^ (128 - j)
/-- T51: the 37-bit X field read from the top `b_j` bits of the path nodes of heights 3..10 (digests 168..175). -/
def xOfB (b : CBytes) : Nat :=
  topBits 2 (cDig b 168) + topBits 2 (cDig b 169) * 2 ^ 2 + topBits 3 (cDig b 170) * 2 ^ 4 +
  topBits 4 (cDig b 171) * 2 ^ 7 + topBits 5 (cDig b 172) * 2 ^ 11 + topBits 6 (cDig b 173) * 2 ^ 16 +
  topBits 7 (cDig b 174) * 2 ^ 22 + topBits 8 (cDig b 175) * 2 ^ 29
/-- U16b: zero bits `b` of the ground lower path sibling at compact index `k` (index after erasing digest 176): L1
path heights 6/5/4 (225/224/223) carry 3/2/1 bits, L2 and L3 heights 5/4/3 (274/273/272, 323/322/321) carry 2/2/1. -/
def gBits : Nat → Nat
  | 225 => 3 | 224 => 2 | 223 => 1 | 274 => 2 | 273 => 2 | 272 => 1 | 323 => 2 | 322 => 2 | 321 => 1 | _ => 0
/-- U16b: offset of slot `k`'s bits in the 16-bit V field (top sibling bits 72..87). -/
def gOff : Nat → Nat
  | 225 => 0 | 224 => 3 | 223 => 5 | 274 => 6 | 273 => 8 | 272 => 10 | 323 => 11 | 322 => 13 | 321 => 15 | _ => 0
/-- U16b: the 16-bit V field read from the top `gBits k` bits of the ground lower path siblings. -/
def vOfB (b : CBytes) : Nat :=
  topBits 3 (cDig b 225) + topBits 2 (cDig b 224) * 2 ^ 3 + topBits 1 (cDig b 223) * 2 ^ 5 +
  topBits 2 (cDig b 274) * 2 ^ 6 + topBits 2 (cDig b 273) * 2 ^ 8 + topBits 1 (cDig b 272) * 2 ^ 10 +
  topBits 2 (cDig b 323) * 2 ^ 11 + topBits 2 (cDig b 322) * 2 ^ 13 + topBits 1 (cDig b 321) * 2 ^ 15
/-- Decoded digest `k`: the path nodes of heights 1..10 (digests 166..175) lose their top `b_j` bits; index 176 (top
sibling) = tail 80 bits + X bits 0..23 (bits 80..103; bits 104..127 zero, 111..127 brute-forced by expand). -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 176 then (if 166 ≤ k then clearTop (topZeroBits (k - 165)) (cDig b k) else cDig b k)
  else if k = 176 then BitVec.ofNat 128 (b.toNat / 2 ^ (128 * 324) % 2 ^ 64 + vOfB b * 2 ^ 64 + xOfB b % 2 ^ 24 * 2 ^ 80)
  else if gBits (k - 1) = 0 then cDig b (k - 1) else clearTop (gBits (k - 1)) (cDig b (k - 1))
def sigDecC (b : CBytes) : SharedSignature where
  rho := digC b 0
  policyHints := BitVec.ofNat 16 (xOfB b / 2 ^ 24)
  forest := {
    pairs := fun p => {
      firstValues := fun i => digC b (1 + 25 * p.val + i.val)
      firstPath := fun i => digC b (1 + 25 * p.val + 6 + i.val)
      secondValues := fun i => digC b (1 + 25 * p.val + 12 + i.val)
      secondPath := fun i => digC b (1 + 25 * p.val + 18 + i.val) }
    singleton := {
      values := fun i => digC b (101 + i.val)
      path := fun i => digC b (107 + i.val) } }
  layers := fun lay => {
    values := fun i => digC b (layIdx lay + i.val)
    path := fun i => digC b (layIdx lay + chainCount lay + i.val) }
/-- T51: X = top sibling bits 80..103 (24) | hint (13 bits) << 24 (37 bits). -/
def xField (s : SharedSignature) : Nat :=
  ((sigDigests s).getD 176 0).toNat / 2 ^ 80 % 2 ^ 24 + s.policyHints.toNat % 2 ^ 13 * 2 ^ 24
/-- T51: the path node of height `j` with X bits `xOff j ..` in its top `b_j = topZeroBits j` bits. -/
def packD (j : Nat) (d : Digest) (x : Nat) : Digest :=
  BitVec.ofNat 128 (d.toNat % 2 ^ (128 - topZeroBits j) +
    x / 2 ^ xOff j % 2 ^ topZeroBits j * 2 ^ (128 - topZeroBits j))
/-- U16b: V = top sibling bits 72..87 (16). -/
def vField (s : SharedSignature) : Nat := ((sigDigests s).getD 176 0).toNat / 2 ^ 64 % 2 ^ 16
/-- U16b: the ground lower path sibling at compact index `k` with V bits `gOff k ..` OR-ed into its top `gBits k` bits
(the sign pack routine only ORs; the bits are clear unless the ground search hit its cap). -/
def packG (k : Nat) (d : Digest) (v : Nat) : Digest :=
  BitVec.ofNat 128 (d.toNat ||| v / 2 ^ gOff k % 2 ^ gBits k * 2 ^ (128 - gBits k))
/-- U16b: the ground slots of `s` have their top `gBits k` bits clear (`LowerPathOK`, `groundClear_of_lowerPathOK`). -/
def GroundClear (s : SharedSignature) : Prop :=
  ∀ k, gBits k ≠ 0 → topBits (gBits k) (((sigDigests s).eraseIdx 176).getD k 0) = 0
def encList (s : SharedSignature) : List Digest :=
  (List.range 324).map fun k => if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
    (xField s) else if gBits k = 0 then ((sigDigests s).eraseIdx 176).getD k 0
    else packG k (((sigDigests s).eraseIdx 176).getD k 0) (vField s)
def sigBC (s : SharedSignature) : CBytes :=
  BitVec.ofNat _ (digNat (encList s) + 2 ^ (128 * 324) * (((sigDigests s).getD 176 0).toNat % 2 ^ 64))
theorem compact_length : 324 * 16 + 8 = 5192 := by decide
/-- The normal form a decoded signature has (T51): path tops of heights 1..10 clear (`b_j` bits), top sibling below
bit 104, hint 13 bits. -/
def normD (k : Nat) (d : Digest) : Digest :=
  if 166 ≤ k ∧ k ≤ 175 then clearTop (topZeroBits (k - 165)) d
  else if k = 176 then BitVec.ofNat 128 (d.toNat % 2 ^ 104)
  else if 177 ≤ k ∧ gBits (k - 1) ≠ 0 then clearTop (gBits (k - 1)) d else d
theorem normD_of_lt (k : Nat) (d : Digest) (hk : k < 166) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => by omega)]
theorem sigDigests_rho (s : SharedSignature) : (sigDigests s).getD 0 0 = s.rho := by rfl
theorem sigDigests_pair (s : SharedSignature) (p : Fin 4) (i : Nat) (hi : i < 25) :
    (sigDigests s).getD (1 + 25 * p.val + i) 0 = (pairList (s.forest.pairs p)).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
        pairs_length, singletonList_length]; omega),
    getD_append_left' (by simp only [List.length_append, List.length_singleton, pairs_length]; omega),
    getD_append_right' (by simp; omega), List.length_singleton,
    show 1 + 25 * p.val + i - 1 = 25 * p.val + i by omega,
    ClaudeWCT.W9.T3M.getD_flatMap_chunks pairList 25 0 pairList_length _ p.val i (by simp) hi,
    List.getElem_ofFn]
theorem pairList_firstValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD i.val 0 = p.firstValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_left' (by simp), getD_ofFn']
theorem pairList_firstPath (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (6 + i.val) 0 = p.firstPath i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_right' (by simp), List.length_ofFn, Nat.add_sub_cancel_left, getD_ofFn']
theorem pairList_secondValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (12 + i.val) 0 = p.secondValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 12 + i.val - (6 + 6) = i.val by omega, getD_ofFn']
theorem pairList_secondPath (p : PairOpening) (i : Fin 7) :
    (pairList p).getD (18 + i.val) 0 = p.secondPath i := by
  unfold pairList
  rw [getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 18 + i.val - (6 + 6 + 6) = i.val by omega, getD_ofFn']
theorem sigDigests_singleton (s : SharedSignature) (i : Nat) (hi : i < 13) :
    (sigDigests s).getD (101 + i) 0 = (singletonList s.forest.singleton).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
      pairs_length, singletonList_length]; omega), getD_append_right' (by
      simp only [List.length_append, List.length_singleton, pairs_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length]
  rw [show 101 + i - (1 + 100) = i by omega]
theorem sigDigests_tail (s : SharedSignature) (k : Nat) (hk : 114 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 114) 0 := by
  unfold sigDigests
  rw [getD_append_right' (by simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]
theorem sigDigests_layer (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (layerList s lay).getD i 0 := by
  have l0 := layerList_length s 0
  have l1 := layerList_length s 1
  have l2 := layerList_length s 2
  rw [chainCount_0, height_0] at l0
  rw [chainCount_1, height_1] at l1
  rw [chainCount_2, height_2] at l2
  fin_cases lay
  · show (sigDigests s).getD (114 + i) 0 = (layerList s 0).getD i 0
    have hi' : i < 63 := hi
    rw [sigDigests_tail s _ (by omega), show 114 + i - 114 = i by omega, getD_append_left' (by omega)]
  · show (sigDigests s).getD (177 + i) 0 = (layerList s 1).getD i 0
    have hi' : i < 50 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_left' (by omega),
      show 177 + i - 114 - 63 = i by omega]
  · show (sigDigests s).getD (227 + i) 0 = (layerList s 2).getD i 0
    have hi' : i < 49 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_left' (by omega), show 227 + i - 114 - 63 - 50 = i by omega]
  · show (sigDigests s).getD (276 + i) 0 = (layerList s 3).getD i 0
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_right' (by omega), l2, show 276 + i - 114 - 63 - 50 - 49 = i by omega]
theorem sigDigests_layValue (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (s.layers lay).values ⟨i, hi⟩ := by
  rw [sigDigests_layer s lay i (by omega), layerList, getD_append_left' (by simpa using hi), getD_ofFn']
theorem sigDigests_layPath (s : SharedSignature) (lay : Layer) (j : Nat) (hj : j < height lay) :
    (sigDigests s).getD (layIdx lay + (chainCount lay + j)) 0 = (s.layers lay).path ⟨j, hj⟩ := by
  rw [sigDigests_layer s lay _ (by omega), layerList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']

end ClaudeWCT.W9.T3M.SharedCodec


namespace ClaudeWCT.W9.T3M.SharedCodec
/-- Internal expansion retains the four unused seventh A-path slots. T51: the expander's slot layout keeps #938's
lower-layer slots, so the top path follows the 51 top values (slots 169..180) and three unused slots 181..183 precede
L1 (slot 184): digest `k` sits at slot `k + 4` for `114 ≤ k ≤ 176`, `k + 7` for `k ≥ 177`. -/
def internalFullIndex (k : Nat) : Nat :=
  k + (if 13 ≤ k then 1 else 0) + (if 38 ≤ k then 1 else 0) +
    (if 63 ≤ k then 1 else 0) + (if 88 ≤ k then 1 else 0) + (if 177 ≤ k then 3 else 0)
def externalFullIndex (k : Nat) : Nat :=
  k - ((if 13 < k then 1 else 0) + (if 39 < k then 1 else 0) +
    (if 65 < k then 1 else 0) + (if 91 < k then 1 else 0) + (if 183 < k then 3 else 0))
def internalDummy (k : Nat) : Bool := decide (k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 181 ∨ k = 182 ∨ k = 183)
theorem internalFullIndex_spec (k : Nat) :
    internalFullIndex k = k + (([13,38,63,88].filter fun skip => decide (skip ≤ k)).length) +
      (if 177 ≤ k then 3 else 0) := by
  unfold internalFullIndex
  by_cases h13 : 13 ≤ k <;> by_cases h38 : 38 ≤ k <;> by_cases h63 : 63 ≤ k <;> by_cases h88 : 88 ≤ k <;>
    simp [h13, h38, h63, h88] <;> omega

theorem internalFullIndex_bound (k : Nat) (hk : k < 325) : internalFullIndex k < 332 := by
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_dummy (k : Nat) : internalDummy (internalFullIndex k) = false := by
  simp only [internalDummy, decide_eq_false_iff_not]
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_inverse (k : Nat) : externalFullIndex (internalFullIndex k) = k := by
  unfold externalFullIndex internalFullIndex
  split_ifs <;> omega
def inflatedRead {α : Type} (zero : α) (read : Nat → α) (k : Nat) : α :=
  if internalDummy k then zero else read (externalFullIndex k)
theorem inflatedRead_internal {α : Type} (zero : α) (read : Nat → α) (k : Nat) :
    inflatedRead zero read (internalFullIndex k) = read k := by
  simp only [inflatedRead, internalFullIndex_dummy, Bool.false_eq_true, ↓reduceIte,
    internalFullIndex_inverse]
theorem internalFullIndex_main (k : Nat) (hk : 114 ≤ k) (hk' : k ≤ 176) : internalFullIndex k = k + 4 := by
  unfold internalFullIndex
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)]
theorem internalFullIndex_lower (k : Nat) (hk : 177 ≤ k) : internalFullIndex k = k + 7 := by
  unfold internalFullIndex
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos hk]
theorem internalFullIndex_tail : internalFullIndex 176 = 180 := by rfl
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.T3
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def serializedWord (read : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  if k < 26 then read k else if k < 28 then 0 else
  if k < 78 then read (k - 2) else if k < 80 then 0 else
  if k < 130 then read (k - 4) else if k < 132 then 0 else
  if k < 182 then read (k - 6) else if k < 184 then 0 else
  if k < 366 then read (k - 8) else if k = 366 then read 654 else
  if k = 367 then (read 655 <<< 16) >>> 16 else read (k - 10)

theorem externalFullIndex_tail_iff (k : Nat) : externalFullIndex k = 176 ↔ k = 180 := by
  unfold externalFullIndex
  split_ifs <;> omega

theorem extract_digest_word {n : Nat} (x : BitVec n) (a i : Nat) (hi : i < 2) :
    (x.extractLsb' a 128).extractLsb' (64*i) 64 = x.extractLsb' (a+64*i) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [show decide (64*i+j < 128) = true from decide_eq_true (by omega), Bool.true_and]
  congr 1
  omega

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit lt_split split_mod split_div)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem length_eraseIdx_sig (s : SharedSignature) :
    ((sigDigests s).eraseIdx 176).length = 324 := by
  rw [List.length_eraseIdx,sigDigests_length];decide

theorem encList_length (s : SharedSignature) : (encList s).length = 324 := by simp [encList]

theorem encList_getD (s : SharedSignature) (k : Nat) (hk : k < 324) :
    (encList s).getD k 0 = if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
      (xField s) else if gBits k = 0 then ((sigDigests s).eraseIdx 176).getD k 0
      else packG k (((sigDigests s).eraseIdx 176).getD k 0) (vField s) := by
  simp [encList, List.getD_eq_getElem?_getD, hk]

theorem sigBC_toNat (s : SharedSignature) :
    (sigBC s).toNat = digNat (encList s) + 2^(128*324)*(((sigDigests s).getD 176 0).toNat%2^64) := by
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 176 0).toNat (show 0<2^64 by positivity))
  simpa only [←pow_add] using hT

theorem encoded_low (s : SharedSignature) : (sigBC s).toNat%2^(128*324)=digNat (encList s) := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_mod _ _ _ hD]

theorem encoded_tail (s : SharedSignature) :
    (sigBC s).toNat/2^(128*324)%2^64=((sigDigests s).getD 176 0).toNat%2^64 := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_div _ _ _ hD, Nat.mod_mod]

theorem cDig_sigBC (s : SharedSignature) (j : Nat) (hj : j<324) : cDig (sigBC s) j=(encList s).getD j 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,←digNat_digit]
  rw [←mod_digit _ 324 j hj,encoded_low]

theorem pack_gen (b : Nat) (hb : b ≤ 128) (d : Digest) (y : Nat) :
    clearTop b (BitVec.ofNat 128 (d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b))) = clearTop b d ∧
      topBits b (BitVec.ofNat 128 (d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b))) = y % 2 ^ b := by
  have hd : d.toNat % 2 ^ (128 - b) < 2 ^ (128 - b) := Nat.mod_lt _ (by positivity)
  have hf : y % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  have hlt : d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b) < 2 ^ 128 := by
    have : y % 2 ^ b * 2 ^ (128 - b) ≤ (2 ^ b - 1) * 2 ^ (128 - b) := Nat.mul_le_mul_right _ (by omega)
    have e : (2 ^ b - 1) * 2 ^ (128 - b) + 2 ^ (128 - b) = 2 ^ 128 := by
      rw [Nat.sub_mul, one_mul, ← pow_add, show b + (128 - b) = 128 by omega]
      have : 2 ^ (128 - b) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  unfold clearTop topBits
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
  · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hd, zero_add]

theorem topZeroBits_le_eight (j : Nat) (hj : j ≤ 11) : topZeroBits j ≤ 8 := by interval_cases j <;> decide

/-- T51: the X bits stored in the top `b_j = topZeroBits j` bits of a packed path node (`b` names `b_j`). -/
theorem pack_facts (j b : Nat) (hj : 1 ≤ j ∧ j ≤ 10) (hb : topZeroBits j = b) (d : Digest) (x : Nat) :
    clearTop b (packD j d x) = clearTop b d ∧ topBits b (packD j d x) = x / 2 ^ xOff j % 2 ^ b := by
  subst hb
  exact pack_gen (topZeroBits j) (by have := topZeroBits_le_eight j (by omega); omega) d (x / 2 ^ xOff j)

theorem xOff_vals : xOff 3 = 0 ∧ xOff 4 = 2 ∧ xOff 5 = 4 ∧ xOff 6 = 7 ∧ xOff 7 = 11 ∧ xOff 8 = 16 ∧ xOff 9 = 22 ∧
    xOff 10 = 29 := by decide

theorem xField_lt (s : SharedSignature) : xField s < 2 ^ 37 := by
  unfold xField
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 80) (show 0 < 2 ^ 24 by positivity)
  have h2 := Nat.mod_lt s.policyHints.toNat (show 0 < 2 ^ 13 by positivity)
  omega

theorem xOfB_sigBC (s : SharedSignature) : xOfB (sigBC s) = xField s := by
  have hx := xField_lt s
  obtain ⟨o3, o4, o5, o6, o7, o8, o9, o10⟩ := xOff_vals
  unfold xOfB
  simp only [cDig_sigBC s _ (by norm_num : (168:Nat) < 324), cDig_sigBC s _ (by norm_num : (169:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (170:Nat) < 324), cDig_sigBC s _ (by norm_num : (171:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (172:Nat) < 324), cDig_sigBC s _ (by norm_num : (173:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (174:Nat) < 324), cDig_sigBC s _ (by norm_num : (175:Nat) < 324)]
  simp only [encList_getD s _ (by norm_num : (168:Nat) < 324), encList_getD s _ (by norm_num : (169:Nat) < 324),
    encList_getD s _ (by norm_num : (170:Nat) < 324), encList_getD s _ (by norm_num : (171:Nat) < 324),
    encList_getD s _ (by norm_num : (172:Nat) < 324), encList_getD s _ (by norm_num : (173:Nat) < 324),
    encList_getD s _ (by norm_num : (174:Nat) < 324), encList_getD s _ (by norm_num : (175:Nat) < 324)]
  norm_num only [if_true, and_self, ite_true]
  rw [(pack_facts 3 2 (by norm_num) rfl _ _).2, (pack_facts 4 2 (by norm_num) rfl _ _).2,
    (pack_facts 5 3 (by norm_num) rfl _ _).2, (pack_facts 6 4 (by norm_num) rfl _ _).2,
    (pack_facts 7 5 (by norm_num) rfl _ _).2, (pack_facts 8 6 (by norm_num) rfl _ _).2,
    (pack_facts 9 7 (by norm_num) rfl _ _).2, (pack_facts 10 8 (by norm_num) rfl _ _).2,
    o3, o4, o5, o6, o7, o8, o9, o10]
  norm_num
  omega

/-- U16b: zero bits of the ground slots, at most 3. -/
theorem gBits_le (k : Nat) : gBits k ≤ 3 := by
  unfold gBits; split <;> omega

theorem gBits_eq_zero (k : Nat) (hk : k < 223 ∨ (225 < k ∧ k < 272) ∨ (274 < k ∧ k < 321) ∨ 323 < k) :
    gBits k = 0 := by
  unfold gBits; split <;> omega

theorem or_shift (h l y m : Nat) (hl : l < 2 ^ m) :
    (h * 2 ^ m + l) ||| (y * 2 ^ m) = (h ||| y) * 2 ^ m + l := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, mul_comm h, mul_comm y, mul_comm (h ||| y),
    Nat.testBit_two_pow_mul_add _ hl, Nat.testBit_two_pow_mul_add _ hl,
    show 2 ^ m * y = 2 ^ m * y + 0 by rfl, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos m)]
  split <;> simp [Nat.testBit_or]
/-- U16b: a packed ground slot: the slot's own top bits OR the V bits, above its untouched low bits. -/
theorem packG_toNat (k : Nat) (d : Digest) (v : Nat) :
    (packG k d v).toNat = (topBits (gBits k) d ||| v / 2 ^ gOff k % 2 ^ gBits k) * 2 ^ (128 - gBits k) +
      d.toNat % 2 ^ (128 - gBits k) := by
  have hb := gBits_le k
  have hl : d.toNat % 2 ^ (128 - gBits k) < 2 ^ (128 - gBits k) := Nat.mod_lt _ (by positivity)
  have hdm := Nat.div_add_mod d.toNat (2 ^ (128 - gBits k))
  have ht : topBits (gBits k) d < 2 ^ gBits k := by
    unfold topBits
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show gBits k + (128 - gBits k) = 128 by omega]
    exact d.isLt
  have hy : v / 2 ^ gOff k % 2 ^ gBits k < 2 ^ gBits k := Nat.mod_lt _ (by positivity)
  have hor : topBits (gBits k) d ||| v / 2 ^ gOff k % 2 ^ gBits k < 2 ^ gBits k := Nat.or_lt_two_pow ht hy
  unfold packG
  rw [BitVec.toNat_ofNat]
  have he : d.toNat = topBits (gBits k) d * 2 ^ (128 - gBits k) + d.toNat % 2 ^ (128 - gBits k) := by
    unfold topBits; rw [mul_comm]; exact hdm.symm
  rw [he, or_shift _ _ _ _ hl, ← he]
  apply Nat.mod_eq_of_lt
  have h1 : (topBits (gBits k) d ||| v / 2 ^ gOff k % 2 ^ gBits k) * 2 ^ (128 - gBits k) ≤
      (2 ^ gBits k - 1) * 2 ^ (128 - gBits k) := Nat.mul_le_mul_right _ (by omega)
  have e : (2 ^ gBits k - 1) * 2 ^ (128 - gBits k) + 2 ^ (128 - gBits k) = 2 ^ 128 := by
    rw [Nat.sub_mul, one_mul, ← pow_add, show gBits k + (128 - gBits k) = 128 by omega]
    have : 2 ^ (128 - gBits k) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega
/-- U16b: on a slot whose top bits are clear, `packG` stores the V bits exactly (the T1-era additive form). -/
theorem packG_of_clear (k : Nat) (d : Digest) (v : Nat) (h : topBits (gBits k) d = 0) :
    packG k d v = BitVec.ofNat 128 (d.toNat % 2 ^ (128 - gBits k) + v / 2 ^ gOff k % 2 ^ gBits k * 2 ^ (128 - gBits k)) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := (packG k d v).isLt
  rw [packG_toNat, h, Nat.zero_or] at hlt
  rw [packG_toNat, h, Nat.zero_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (a := d.toNat % 2 ^ (128 - gBits k) + v / 2 ^ gOff k % 2 ^ gBits k * 2 ^ (128 - gBits k)) (by omega)]
  omega
/-- U16b: the V bits OR-ed into the top `gBits k` bits of a packed ground slot (exactly the V bits when the slot's
own top bits are clear). -/
theorem packG_facts (k : Nat) (d : Digest) (v : Nat) :
    clearTop (gBits k) (packG k d v) = clearTop (gBits k) d ∧
      topBits (gBits k) (packG k d v) = topBits (gBits k) d ||| v / 2 ^ gOff k % 2 ^ gBits k := by
  have hb := gBits_le k
  have hl : d.toNat % 2 ^ (128 - gBits k) < 2 ^ (128 - gBits k) := Nat.mod_lt _ (by positivity)
  constructor
  · apply BitVec.eq_of_toNat_eq
    unfold clearTop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, packG_toNat, Nat.mul_add_mod_of_lt hl]
  · unfold topBits
    rw [packG_toNat, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hl, Nat.zero_add]
    rfl

theorem vField_lt (s : SharedSignature) : vField s < 2 ^ 16 := by
  unfold vField; exact Nat.mod_lt _ (by positivity)

theorem vOfB_sigBC (s : SharedSignature) (hg : GroundClear s) : vOfB (sigBC s) = vField s := by
  have hv := vField_lt s
  unfold vOfB
  simp only [cDig_sigBC s _ (by norm_num : (225:Nat) < 324), cDig_sigBC s _ (by norm_num : (224:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (223:Nat) < 324), cDig_sigBC s _ (by norm_num : (274:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (273:Nat) < 324), cDig_sigBC s _ (by norm_num : (272:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (323:Nat) < 324), cDig_sigBC s _ (by norm_num : (322:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (321:Nat) < 324)]
  simp only [encList_getD s _ (by norm_num : (225:Nat) < 324), encList_getD s _ (by norm_num : (224:Nat) < 324),
    encList_getD s _ (by norm_num : (223:Nat) < 324), encList_getD s _ (by norm_num : (274:Nat) < 324),
    encList_getD s _ (by norm_num : (273:Nat) < 324), encList_getD s _ (by norm_num : (272:Nat) < 324),
    encList_getD s _ (by norm_num : (323:Nat) < 324), encList_getD s _ (by norm_num : (322:Nat) < 324),
    encList_getD s _ (by norm_num : (321:Nat) < 324)]
  have g225 : gBits 225 = 3 := rfl
  have g224 : gBits 224 = 2 := rfl
  have g223 : gBits 223 = 1 := rfl
  have g274 : gBits 274 = 2 := rfl
  have g273 : gBits 273 = 2 := rfl
  have g272 : gBits 272 = 1 := rfl
  have g323 : gBits 323 = 2 := rfl
  have g322 : gBits 322 = 2 := rfl
  have g321 : gBits 321 = 1 := rfl
  rw [if_neg (show ¬ (166 ≤ 225 ∧ 225 ≤ 175) by norm_num), if_neg (show ¬ gBits 225 = 0 by rw [g225]; norm_num), if_neg (show ¬ (166 ≤ 224 ∧ 224 ≤ 175) by norm_num), if_neg (show ¬ gBits 224 = 0 by rw [g224]; norm_num), if_neg (show ¬ (166 ≤ 223 ∧ 223 ≤ 175) by norm_num), if_neg (show ¬ gBits 223 = 0 by rw [g223]; norm_num), if_neg (show ¬ (166 ≤ 274 ∧ 274 ≤ 175) by norm_num), if_neg (show ¬ gBits 274 = 0 by rw [g274]; norm_num), if_neg (show ¬ (166 ≤ 273 ∧ 273 ≤ 175) by norm_num), if_neg (show ¬ gBits 273 = 0 by rw [g273]; norm_num), if_neg (show ¬ (166 ≤ 272 ∧ 272 ≤ 175) by norm_num), if_neg (show ¬ gBits 272 = 0 by rw [g272]; norm_num), if_neg (show ¬ (166 ≤ 323 ∧ 323 ≤ 175) by norm_num), if_neg (show ¬ gBits 323 = 0 by rw [g323]; norm_num), if_neg (show ¬ (166 ≤ 322 ∧ 322 ≤ 175) by norm_num), if_neg (show ¬ gBits 322 = 0 by rw [g322]; norm_num), if_neg (show ¬ (166 ≤ 321 ∧ 321 ≤ 175) by norm_num), if_neg (show ¬ gBits 321 = 0 by rw [g321]; norm_num)]
  have e225 := (packG_facts 225 (((sigDigests s).eraseIdx 176).getD 225 0) (vField s)).2
  rw [hg 225 (by decide), Nat.zero_or] at e225
  have e224 := (packG_facts 224 (((sigDigests s).eraseIdx 176).getD 224 0) (vField s)).2
  rw [hg 224 (by decide), Nat.zero_or] at e224
  have e223 := (packG_facts 223 (((sigDigests s).eraseIdx 176).getD 223 0) (vField s)).2
  rw [hg 223 (by decide), Nat.zero_or] at e223
  have e274 := (packG_facts 274 (((sigDigests s).eraseIdx 176).getD 274 0) (vField s)).2
  rw [hg 274 (by decide), Nat.zero_or] at e274
  have e273 := (packG_facts 273 (((sigDigests s).eraseIdx 176).getD 273 0) (vField s)).2
  rw [hg 273 (by decide), Nat.zero_or] at e273
  have e272 := (packG_facts 272 (((sigDigests s).eraseIdx 176).getD 272 0) (vField s)).2
  rw [hg 272 (by decide), Nat.zero_or] at e272
  have e323 := (packG_facts 323 (((sigDigests s).eraseIdx 176).getD 323 0) (vField s)).2
  rw [hg 323 (by decide), Nat.zero_or] at e323
  have e322 := (packG_facts 322 (((sigDigests s).eraseIdx 176).getD 322 0) (vField s)).2
  rw [hg 322 (by decide), Nat.zero_or] at e322
  have e321 := (packG_facts 321 (((sigDigests s).eraseIdx 176).getD 321 0) (vField s)).2
  rw [hg 321 (by decide), Nat.zero_or] at e321
  rw [g225] at e225; rw [g224] at e224; rw [g223] at e223; rw [g274] at e274; rw [g273] at e273
  rw [g272] at e272; rw [g323] at e323; rw [g322] at e322; rw [g321] at e321
  rw [e225, e224, e223, e274, e273, e272, e323, e322, e321]
  simp only [gOff, Nat.reducePow]
  omega

/-- U16b: the T1 (5,195-byte) compact list: no ground packing. -/
def encListT1 (s : SharedSignature) : List Digest :=
  (List.range 324).map fun k => if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
    (xField s) else ((sigDigests s).eraseIdx 176).getD k 0
/-- U16b: the T1 compact bytes (5,195 bytes: tail = top sibling bits 0..87). -/
def sigBCT1 (s : SharedSignature) : Bytes 5194 :=
  BitVec.ofNat _ (digNat (encListT1 s) + 2 ^ (128 * 324) * (((sigDigests s).getD 176 0).toNat % 2 ^ 80))

theorem encListT1_length (s : SharedSignature) : (encListT1 s).length = 324 := by simp [encListT1]
theorem encListT1_getD (s : SharedSignature) (k : Nat) (hk : k < 324) :
    (encListT1 s).getD k 0 = if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
      (xField s) else ((sigDigests s).eraseIdx 176).getD k 0 := by
  simp [encListT1, List.getD_eq_getElem?_getD, hk]

theorem sigBCT1_toNat (s : SharedSignature) :
    (sigBCT1 s).toNat = digNat (encListT1 s) + 2^(128*324)*(((sigDigests s).getD 176 0).toNat%2^80) := by
  unfold sigBCT1
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt (encListT1 s)
  rw [encListT1_length] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 176 0).toNat (show 0<2^80 by positivity))
  simpa only [←pow_add] using hT

/-- 64-bit word `2 j + h` (`h < 2`) of a number is the `h`-th half of its 128-bit digit `j`. -/
theorem word_of_digit (X j h : Nat) (hh : h < 2) :
    X / 2 ^ (64 * (2 * j + h)) % 2 ^ 64 = X / 2 ^ (128 * j) % 2 ^ 128 / 2 ^ (64 * h) % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 64
  · simp only [hi, decide_true, Bool.true_and]
    ring_nf
    simp only [show i + h * 64 < 128 by omega, decide_true, Bool.true_and]
  · simp [hi]

/-- Word `k < 648` of the compact bytes is the matching half of compact digit `k / 2`. -/
theorem word_digits (L : List Digest) (hL : L.length = 324) (T k : Nat) (hk : k < 648) :
    (digNat L + 2 ^ (128 * 324) * T) / 2 ^ (64 * k) % 2 ^ 64 = (L.getD (k / 2) 0).toNat / 2 ^ (64 * (k % 2)) % 2 ^ 64 := by
  have hD := digNat_lt L
  rw [hL] at hD
  rw [show k = 2 * (k / 2) + k % 2 by omega, word_of_digit _ _ _ (Nat.mod_lt _ (by decide)),
    ← mod_digit _ 324 _ (by omega), split_mod _ _ _ hD, digNat_digit]
  simp only [show (2 * (k / 2) + k % 2) / 2 = k / 2 by omega, show (2 * (k / 2) + k % 2) % 2 = k % 2 by omega]

theorem word_tail (D T : Nat) (hD : D < 2 ^ (128 * 324)) (h : Nat) (hh : h < 2) :
    (D + 2 ^ (128 * 324) * T) / 2 ^ (64 * (648 + h)) = T / 2 ^ (64 * h) := by
  rw [show 64 * (648 + h) = 128 * 324 + 64 * h by omega, pow_add, ← Nat.div_div_eq_div_mul, split_div _ _ _ hD]

theorem packG_word0 (k : Nat) (d : Digest) (v : Nat) : (packG k d v).toNat % 2 ^ 64 = d.toNat % 2 ^ 64 := by
  have hb := gBits_le k
  rw [packG_toNat, show 2 ^ (128 - gBits k) = 2 ^ (64 - gBits k) * 2 ^ 64 by
      rw [← pow_add]; congr 1; omega, ← mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mul_left_mod]

theorem packG_word1 (k : Nat) (d : Digest) (v : Nat) :
    (packG k d v).toNat / 2 ^ 64 % 2 ^ 64 =
      d.toNat / 2 ^ 64 % 2 ^ 64 ||| v / 2 ^ gOff k % 2 ^ gBits k * 2 ^ (64 - gBits k) := by
  have hb := gBits_le k
  set m := 128 - gBits k with hm
  have hsplit : 2 ^ m = 2 ^ (64 - gBits k) * 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hl : d.toNat % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
  have hl' : d.toNat % 2 ^ m / 2 ^ 64 < 2 ^ (64 - gBits k) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← hsplit]; exact hl
  have he : d.toNat = topBits (gBits k) d * 2 ^ m + d.toNat % 2 ^ m := by
    unfold topBits; rw [mul_comm]; exact (Nat.div_add_mod _ _).symm
  have ht : topBits (gBits k) d < 2 ^ gBits k := by
    unfold topBits
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show gBits k + (128 - gBits k) = 128 by omega]
    exact d.isLt
  have hy : v / 2 ^ gOff k % 2 ^ gBits k < 2 ^ gBits k := Nat.mod_lt _ (by positivity)
  have hor := Nat.or_lt_two_pow ht hy
  have key : ∀ H l, H < 2 ^ gBits k → l < 2 ^ m → (H * 2 ^ m + l) / 2 ^ 64 % 2 ^ 64 =
      H * 2 ^ (64 - gBits k) + l / 2 ^ 64 := by
    intro H l hH hl0
    rw [hsplit] at hl0 ⊢
    have hl1 : l / 2 ^ 64 < 2 ^ (64 - gBits k) := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; exact hl0
    rw [← mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.add_comm]
    apply Nat.mod_eq_of_lt
    have h1 : H * 2 ^ (64 - gBits k) ≤ (2 ^ gBits k - 1) * 2 ^ (64 - gBits k) := Nat.mul_le_mul_right _ (by omega)
    have e : (2 ^ gBits k - 1) * 2 ^ (64 - gBits k) + 2 ^ (64 - gBits k) = 2 ^ 64 := by
      rw [Nat.sub_mul, one_mul, ← pow_add, show gBits k + (64 - gBits k) = 64 by omega]
      have : 2 ^ (64 - gBits k) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  rw [packG_toNat, key _ _ hor hl]
  conv_rhs => rw [he, key _ _ ht hl]
  rw [or_shift _ _ _ _ hl']

/-- U16b (for the sign pack routine): 64-bit word `k < 650` of the 5,193 compact bytes is the T1 word `k` (5,195
bytes) with the V bits OR-ed into the top `gBits` bits of the high word of each ground slot; word 649 keeps only its
low byte (T1 bytes 5192..5194 = V move into the ground slots). -/
theorem sigBC_word (s : SharedSignature) (k : Nat) (hk : k < 650) :
    (sigBC s).toNat / 2 ^ (64 * k) % 2 ^ 64 =
      if k = 649 then (sigBCT1 s).toNat / 2 ^ (64 * k) % 2 ^ 0
      else (sigBCT1 s).toNat / 2 ^ (64 * k) % 2 ^ 64 |||
        (if k % 2 = 1 ∧ gBits (k / 2) ≠ 0 then vField s / 2 ^ gOff (k / 2) % 2 ^ gBits (k / 2) * 2 ^ (64 - gBits (k / 2))
          else 0) := by
  rw [sigBC_toNat, sigBCT1_toNat]
  by_cases hlo : k < 648
  · rw [if_neg (by omega), word_digits _ (encList_length s) _ _ hlo, word_digits _ (encListT1_length s) _ _ hlo,
      encList_getD s _ (by omega), encListT1_getD s _ (by omega)]
    by_cases hp : 166 ≤ k / 2 ∧ k / 2 ≤ 175
    · have hg : gBits (k / 2) = 0 := gBits_eq_zero _ (by omega)
      rw [if_pos hp, if_pos hp, if_neg (by omega), Nat.or_zero]
    · rw [if_neg hp, if_neg hp]
      by_cases hg : gBits (k / 2) = 0
      · rw [if_pos hg, if_neg (by omega), Nat.or_zero]
      · rw [if_neg hg]
        rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
        · rw [h0, if_neg (by omega), Nat.or_zero, Nat.mul_zero, pow_zero, Nat.div_one, Nat.div_one, packG_word0]
        · rw [h1, if_pos ⟨rfl, hg⟩, Nat.mul_one, packG_word1]
  · have hD := digNat_lt (encList s)
    have hD1 := digNat_lt (encListT1 s)
    rw [encList_length] at hD
    rw [encListT1_length] at hD1
    generalize hx : ((sigDigests s).getD 176 0).toNat = x
    by_cases h8 : k = 648
    · subst h8
      have h0 := word_tail _ (x % 2 ^ 64) hD 0 (by decide)
      have h1 := word_tail _ (x % 2 ^ 80) hD1 0 (by decide)
      simp only [Nat.add_zero, Nat.mul_zero, pow_zero, Nat.div_one] at h0 h1
      rw [h0, h1, if_neg (by decide), if_neg (by decide), Nat.or_zero,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 64 ≤ 64)),
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 64 ≤ 80))]
    · have h9 : k = 649 := by omega
      subst h9
      have h0 := word_tail _ (x % 2 ^ 64) hD 1 (by decide)
      have h1 := word_tail _ (x % 2 ^ 80) hD1 1 (by decide)
      simp only [Nat.mul_one] at h0 h1
      rw [show 64 * 649 = 64 * (648 + 1) by rfl, h0, h1, if_pos rfl]
      simp only [pow_zero, Nat.mod_one, Nat.zero_mod, Nat.div_eq_of_lt (Nat.mod_lt x (show 0 < 2 ^ 64 by positivity))]

/-- U16b: V = bits 8..23 of T1 word 649 (old bytes 5192..5194). -/
theorem vField_sigBCT1 (s : SharedSignature) :
    vField s = (sigBCT1 s).toNat / 2 ^ (64 * 649) / 2 ^ 0 % 2 ^ 16 := by
  have hD1 := digNat_lt (encListT1 s)
  rw [encListT1_length] at hD1
  rw [sigBCT1_toNat, show 64 * 649 = 64 * (648 + 1) by rfl, word_tail _ _ hD1 1 (by decide), Nat.div_div_eq_div_mul,
    ← pow_add]
  unfold vField
  rw [show (2:Nat) ^ 80 = 2 ^ (64 * 1 + 0) * 2 ^ 16 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem digC_sigBC (s : SharedSignature) (k : Nat) (hk : k<325) (hg : k ≠ 176 ∨ GroundClear s) :
    digC (sigBC s) k = normD k ((sigDigests s).getD k 0) := by
  by_cases hlt : k<176
  · rw [digC, if_pos hlt, cDig_sigBC s k (by omega), encList_getD s k (by omega), getD_eraseIdx, if_pos hlt]
    by_cases hp : 166 ≤ k
    · rw [if_pos hp, if_pos ⟨hp, by omega⟩, (pack_facts _ _ ⟨by omega, by omega⟩ rfl _ _).1, normD,
        if_pos ⟨hp, by omega⟩]
    · rw [if_neg hp, if_neg (by omega), if_pos (gBits_eq_zero k (by omega)), normD_of_lt _ _ (by omega)]
  · by_cases he : k=176
    · subst he
      rw [digC, if_neg (by decide), if_pos rfl, encoded_tail, vOfB_sigBC s (hg.resolve_left (by decide)), xOfB_sigBC,
        normD, if_neg (by decide),
        if_pos rfl]
      congr 1
      unfold xField vField
      generalize ((sigDigests s).getD 176 0).toNat = x
      have h72 : x % 2 ^ 80 = x % 2 ^ 64 + 2 ^ 64 * (x / 2 ^ 64 % 2 ^ 16) := by
        rw [show (2:Nat) ^ 80 = 2 ^ 64 * 2 ^ 16 by norm_num, Nat.mod_mul]
      have hm : x % 2 ^ 104 = x % 2 ^ 80 + 2 ^ 80 * (x / 2 ^ 80 % 2 ^ 24) := by
        rw [show (2:Nat) ^ 104 = 2 ^ 80 * 2 ^ 24 by norm_num, Nat.mod_mul]
      have h88 := Nat.mod_lt (x / 2 ^ 80) (show 0 < 2 ^ 24 by positivity)
      rw [hm, h72]
      omega
    · have hg' : ¬ (166 ≤ k-1 ∧ k-1 ≤ 175) := by omega
      have he' : ¬ (k-1 < 176) := by omega
      by_cases hg : gBits (k-1) = 0
      · rw [digC, if_neg hlt, if_neg he, if_pos hg, cDig_sigBC s (k-1) (by omega), encList_getD s _ (by omega),
          if_neg hg', if_pos hg, getD_eraseIdx, if_neg he', show k-1+1=k by omega, normD, if_neg (by omega),
          if_neg he, if_neg (fun h => h.2 hg)]
      · rw [digC, if_neg hlt, if_neg he, if_neg hg, cDig_sigBC s (k-1) (by omega), encList_getD s _ (by omega),
          if_neg hg', if_neg hg, (packG_facts _ _ _).1, getD_eraseIdx, if_neg he', show k-1+1=k by omega, normD,
          if_neg (by omega), if_neg he, if_pos ⟨by omega, hg⟩]

theorem policyHints_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).policyHints = BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13) := by
  change BitVec.ofNat 16 (xOfB (sigBC s) / 2 ^ 24) = _
  rw [xOfB_sigBC]
  unfold xField
  congr 1
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 80) (show 0 < 2 ^ 24 by positivity)
  omega

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (getD_append_left' getD_append_right' getD_ofFn')
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem forest_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).forest=s.forest := by
  have hp : (sigDecC (sigBC s)).forest.pairs=s.forest.pairs := by
    funext p
    have h1 : ((sigDecC (sigBC s)).forest.pairs p).firstValues=(s.forest.pairs p).firstValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)),normD_of_lt _ _ (by omega),sigDigests_pair s p i.val (by omega),pairList_firstValue]
    have h2 : ((sigDecC (sigBC s)).forest.pairs p).firstPath=(s.forest.pairs p).firstPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+6+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)),normD_of_lt _ _ (by omega),show 1+25*p.val+6+i.val=1+25*p.val+(6+i.val) by omega,
        sigDigests_pair s p (6+i.val) (by omega),pairList_firstPath]
    have h3 : ((sigDecC (sigBC s)).forest.pairs p).secondValues=(s.forest.pairs p).secondValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+12+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)),normD_of_lt _ _ (by omega),show 1+25*p.val+12+i.val=1+25*p.val+(12+i.val) by omega,
        sigDigests_pair s p (12+i.val) (by omega),pairList_secondValue]
    have h4 : ((sigDecC (sigBC s)).forest.pairs p).secondPath=(s.forest.pairs p).secondPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+18+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)),normD_of_lt _ _ (by omega),show 1+25*p.val+18+i.val=1+25*p.val+(18+i.val) by omega,
        sigDigests_pair s p (18+i.val) (by omega),pairList_secondPath]
    cases h : (sigDecC (sigBC s)).forest.pairs p
    cases h' : s.forest.pairs p
    simp only [h,h'] at h1 h2 h3 h4
    cases h1;cases h2;cases h3;cases h4;rfl
  have hs : (sigDecC (sigBC s)).forest.singleton=s.forest.singleton := by
    have h1 : (sigDecC (sigBC s)).forest.singleton.values=s.forest.singleton.values := by
      funext i
      change digC (sigBC s) (101+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)),normD_of_lt _ _ (by omega),sigDigests_singleton s i.val (by omega),singletonList,
        getD_append_left' (by simp),getD_ofFn']
    have h2 : (sigDecC (sigBC s)).forest.singleton.path=s.forest.singleton.path := by
      funext i
      change digC (sigBC s) (107+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)),normD_of_lt _ _ (by omega),show 107+i.val=101+(6+i.val) by omega,
        sigDigests_singleton s (6+i.val) (by omega),singletonList,getD_append_right' (by simp),
        List.length_ofFn,Nat.add_sub_cancel_left,getD_ofFn']
    cases h : (sigDecC (sigBC s)).forest.singleton
    cases h' : s.forest.singleton
    simp only [h,h'] at h1 h2
    cases h1;cases h2;rfl
  cases h : (sigDecC (sigBC s)).forest
  cases h' : s.forest
  simp only [h,h'] at hp hs
  cases hp;cases hs;rfl

/-- Normal form (what the compact codec keeps; T51: 5,195 bytes). -/
def normalizeV6 (s : SharedSignature) : SharedSignature :=
  { s with
    policyHints := BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13)
    layers := fun lay => ⟨(s.layers lay).values,
      fun j => normD (layIdx lay + chainCount lay + j.val) ((s.layers lay).path j)⟩ }

theorem normD_of_out (k : Nat) (d : Digest) (hk : k < 166 ∨ (176 < k ∧ gBits (k - 1) = 0)) : normD k d = d := by
  unfold normD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by rintro ⟨h1, h2⟩; rcases hk with hk | hk <;> [omega; exact h2 hk.2])]

theorem sigDecC_sigBC (s : SharedSignature) (hg : GroundClear s) : sigDecC (sigBC s) = normalizeV6 s := by
  have hr : (sigDecC (sigBC s)).rho=s.rho := by
    change digC (sigBC s) 0=s.rho
    rw [digC_sigBC s 0 (by decide) (Or.inl (by decide)),normD_of_lt _ _ (by decide),sigDigests_rho]
  have hh := policyHints_sigDecC_sigBC s
  have hf := forest_sigDecC_sigBC s
  have hl : (sigDecC (sigBC s)).layers=(normalizeV6 s).layers := by
    funext lay
    have hc : layIdx lay+chainCount lay≤325 := by fin_cases lay <;> decide
    have hp : layIdx lay+chainCount lay+height lay≤325 := by fin_cases lay <;> decide
    have hv : ((sigDecC (sigBC s)).layers lay).values=((normalizeV6 s).layers lay).values := by
      funext i
      change digC (sigBC s) (layIdx lay+i.val)=(s.layers lay).values i
      have hn : layIdx lay+i.val < 166 ∨ (176 < layIdx lay+i.val ∧ gBits (layIdx lay+i.val-1) = 0) := by
        have h1 : layIdx lay+i.val < 166 ∨ (176 < layIdx lay+i.val ∧ (layIdx lay+i.val-1 < 223 ∨
            (225 < layIdx lay+i.val-1 ∧ layIdx lay+i.val-1 < 272) ∨ (274 < layIdx lay+i.val-1 ∧
              layIdx lay+i.val-1 < 321) ∨ 323 < layIdx lay+i.val-1)) := by
          fin_cases lay <;> simp [layIdx,chainCount] at * <;> omega
        rcases h1 with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, gBits_eq_zero _ h'⟩
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)),normD_of_out _ _ hn,sigDigests_layValue]
    have hpath : ((sigDecC (sigBC s)).layers lay).path=((normalizeV6 s).layers lay).path := by
      funext i
      change digC (sigBC s) (layIdx lay+chainCount lay+i.val) =
        normD (layIdx lay + chainCount lay + i.val) ((s.layers lay).path i)
      rw [digC_sigBC s _ (by omega) (Or.inr hg), show layIdx lay+chainCount lay+i.val=layIdx lay+(chainCount lay+i.val) by omega,
        sigDigests_layPath s lay i.val i.isLt]
    cases h : (sigDecC (sigBC s)).layers lay
    cases h' : (normalizeV6 s).layers lay
    simp only [h,h'] at hv hpath
    cases hv;cases hpath;rfl
  have hf' : (sigDecC (sigBC s)).forest=(normalizeV6 s).forest := hf
  have hr' : (sigDecC (sigBC s)).rho=(normalizeV6 s).rho := hr
  have hh' : (sigDecC (sigBC s)).policyHints=(normalizeV6 s).policyHints := hh
  cases h : sigDecC (sigBC s)
  cases h' : normalizeV6 s
  simp only [h,h'] at hr' hh' hf' hl
  cases hr';cases hh';cases hf';cases hl;rfl

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_eq_of_digits getD_append_left' getD_append_right' getD_ofFn'
 chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem sigDigests_sigDecC (b : CBytes) (k : Nat) (hk : k<325) :
    (sigDigests (sigDecC b)).getD k 0=digC b k := by
  by_cases h0:k=0
  · subst h0;exact sigDigests_rho _
  by_cases hp:k<101
  · have hq:(k-1)/25<4:=by omega
    let p : Fin 4:=⟨(k-1)/25,hq⟩
    let j : Nat:=(k-1)%25
    have hj:j<25:=Nat.mod_lt _ (by decide)
    have he:k=1+25*p.val+j:=by dsimp [p,j];omega
    rw [he,sigDigests_pair _ p j hj]
    by_cases h1:j<6
    · rw [pairList_firstValue _ ⟨j,h1⟩]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · by_cases h2:j<12
      · rw [show j=6+(j-6) by omega,pairList_firstPath _ ⟨j-6,by omega⟩]
        change digC b _=digC b _
        congr 1 <;> simp only [Fin.val_mk] <;> omega
      · by_cases h3:j<18
        · rw [show j=12+(j-12) by omega,pairList_secondValue _ ⟨j-12,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
        · rw [show j=18+(j-18) by omega,pairList_secondPath _ ⟨j-18,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
  by_cases hs:k<114
  · have he:k=101+(k-101):=by omega
    rw [he,sigDigests_singleton _ (k-101) (by omega)]
    by_cases h1:k-101<6
    · unfold singletonList
      rw [getD_append_left' (by simp;omega),getD_ofFn' _ (k-101) h1]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · unfold singletonList
      rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ ((k-101)-6) (by omega)]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
  have key:∀ (lay:Layer) (i:Nat),i<chainCount lay+height lay→layIdx lay+i=k→
      (sigDigests (sigDecC b)).getD k 0=digC b k := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi]
    unfold layerList
    by_cases hc:i<chainCount lay
    · rw [getD_append_left' (by simpa using hc),getD_ofFn' _ i hc];rfl
    · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (i-chainCount lay) (by omega)]
      change digC b (layIdx lay+chainCount lay+(i-chainCount lay))=_
      congr 1;omega
  by_cases h1:k<177
  · exact key 0 (k-114) (by rw [chainCount_0,height_0];omega) (by simp [layIdx];omega)
  by_cases h2:k<227
  · exact key 1 (k-177) (by rw [chainCount_1,height_1];omega) (by simp [layIdx];omega)
  by_cases h3:k<276
  · exact key 2 (k-227) (by rw [chainCount_2,height_2];omega) (by simp [layIdx];omega)
  · exact key 3 (k-276) (by rw [chainCount_3,height_3];omega) (by simp [layIdx];omega)

theorem topBits_lt (j : Nat) (hj : j ≤ 128) (d : Digest) : topBits j d < 2 ^ j := by
  unfold topBits
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show j + (128 - j) = 128 by omega]
  exact d.isLt

theorem topBits_zero (d : Digest) : topBits 0 d = 0 := by
  unfold topBits; exact Nat.div_eq_of_lt d.isLt

theorem xOfB_digit (b : CBytes) (j : Nat) (h1 : 1 ≤ j) (h10 : j ≤ 10) :
    xOfB b / 2 ^ xOff j % 2 ^ topZeroBits j = topBits (topZeroBits j) (cDig b (165 + j)) := by
  have t3 := topBits_lt 2 (by norm_num) (cDig b 168); have t4 := topBits_lt 2 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 3 (by norm_num) (cDig b 170); have t6 := topBits_lt 4 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 5 (by norm_num) (cDig b 172); have t8 := topBits_lt 6 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 7 (by norm_num) (cDig b 174); have t10 := topBits_lt 8 (by norm_num) (cDig b 175)
  obtain ⟨o3, o4, o5, o6, o7, o8, o9, o10⟩ := xOff_vals
  unfold xOfB
  interval_cases j
  · rw [show topZeroBits 1 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  · rw [show topZeroBits 2 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  all_goals
    first
      | (rw [o3, show topZeroBits 3 = 2 from rfl]; norm_num at *; omega)
      | (rw [o4, show topZeroBits 4 = 2 from rfl]; norm_num at *; omega)
      | (rw [o5, show topZeroBits 5 = 3 from rfl]; norm_num at *; omega)
      | (rw [o6, show topZeroBits 6 = 4 from rfl]; norm_num at *; omega)
      | (rw [o7, show topZeroBits 7 = 5 from rfl]; norm_num at *; omega)
      | (rw [o8, show topZeroBits 8 = 6 from rfl]; norm_num at *; omega)
      | (rw [o9, show topZeroBits 9 = 7 from rfl]; norm_num at *; omega)
      | (rw [o10, show topZeroBits 10 = 8 from rfl]; norm_num at *; omega)

theorem xOfB_lt (b : CBytes) : xOfB b < 2 ^ 37 := by
  have t3 := topBits_lt 2 (by norm_num) (cDig b 168); have t4 := topBits_lt 2 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 3 (by norm_num) (cDig b 170); have t6 := topBits_lt 4 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 5 (by norm_num) (cDig b 172); have t8 := topBits_lt 6 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 7 (by norm_num) (cDig b 174); have t10 := topBits_lt 8 (by norm_num) (cDig b 175)
  unfold xOfB
  norm_num at *
  omega

theorem gBits_ne_zero (k : Nat) (h : gBits k ≠ 0) :
    k = 225 ∨ k = 224 ∨ k = 223 ∨ k = 274 ∨ k = 273 ∨ k = 272 ∨ k = 323 ∨ k = 322 ∨ k = 321 := by
  unfold gBits at h; split at h <;> first | omega | (exfalso; exact h rfl)

theorem vOfB_digit (b : CBytes) (k : Nat) (hk : gBits k ≠ 0) :
    vOfB b / 2 ^ gOff k % 2 ^ gBits k = topBits (gBits k) (cDig b k) := by
  have t1 := topBits_lt 3 (by norm_num) (cDig b 225); have t2 := topBits_lt 2 (by norm_num) (cDig b 224)
  have t3 := topBits_lt 1 (by norm_num) (cDig b 223); have t4 := topBits_lt 2 (by norm_num) (cDig b 274)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 273); have t6 := topBits_lt 1 (by norm_num) (cDig b 272)
  have t7 := topBits_lt 2 (by norm_num) (cDig b 323); have t8 := topBits_lt 2 (by norm_num) (cDig b 322)
  have t9 := topBits_lt 1 (by norm_num) (cDig b 321)
  unfold vOfB
  rcases gBits_ne_zero k hk with h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [gBits, gOff, Nat.reducePow] at * <;> omega

theorem vOfB_lt (b : CBytes) : vOfB b < 2 ^ 16 := by
  have t1 := topBits_lt 3 (by norm_num) (cDig b 225); have t2 := topBits_lt 2 (by norm_num) (cDig b 224)
  have t3 := topBits_lt 1 (by norm_num) (cDig b 223); have t4 := topBits_lt 2 (by norm_num) (cDig b 274)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 273); have t6 := topBits_lt 1 (by norm_num) (cDig b 272)
  have t7 := topBits_lt 2 (by norm_num) (cDig b 323); have t8 := topBits_lt 2 (by norm_num) (cDig b 322)
  have t9 := topBits_lt 1 (by norm_num) (cDig b 321)
  unfold vOfB
  simp only [Nat.reducePow] at *
  omega

/-- U16b: the decoded top sibling: tail (72 bits) + V (bits 72..87) + X bits 0..15 (bits 88..103). -/
theorem digC_176_toNat (b : CBytes) : (digC b 176).toNat =
    b.toNat / 2 ^ (128 * 324) % 2 ^ 64 + vOfB b * 2 ^ 64 + xOfB b % 2 ^ 24 * 2 ^ 80 := by
  rw [digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 64 by positivity)
  have h2 := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 24 by positivity)
  have h3 := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 64 = t at *
  generalize xOfB b % 2 ^ 24 = x at *
  generalize vOfB b = v at *
  simp only [Nat.reducePow] at *
  omega

theorem vField_sigDecC (b : CBytes) : vField (sigDecC b) = vOfB b := by
  unfold vField
  rw [sigDigests_sigDecC b 176 (by decide), digC_176_toNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 64 by positivity)
  have h3 := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 64 = t at *
  generalize xOfB b % 2 ^ 24 = x at *
  generalize vOfB b = v at *
  simp only [Nat.reducePow] at *
  omega

theorem xField_sigDecC (b : CBytes) : xField (sigDecC b) = xOfB b := by
  have hx := xOfB_lt b
  unfold xField
  rw [sigDigests_sigDecC b 176 (by decide)]
  change (digC b 176).toNat / 2 ^ 80 % 2 ^ 24 + (BitVec.ofNat 16 (xOfB b / 2 ^ 24)).toNat % 2 ^ 13 * 2 ^ 24 = _
  rw [digC_176_toNat, BitVec.toNat_ofNat]
  have ht := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 64 by positivity)
  have hv := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 64 = t at *
  generalize vOfB b = v at *
  norm_num at *
  omega

theorem packD_clear (j : Nat) (hj : 1 ≤ j ∧ j ≤ 10) (c : Digest) (x : Nat)
    (hx : x / 2 ^ xOff j % 2 ^ topZeroBits j = topBits (topZeroBits j) c) :
    packD j (clearTop (topZeroBits j) c) x = c := by
  have hb := topZeroBits_le_eight j (by omega)
  apply BitVec.eq_of_toNat_eq
  unfold packD clearTop
  unfold topBits at hx
  rw [hx, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hm : c.toNat % 2 ^ (128 - topZeroBits j) < 2 ^ 128 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.mod_eq_of_lt hm, Nat.mod_mod]
  have e := Nat.mod_add_div c.toNat (2 ^ (128 - topZeroBits j))
  rw [mul_comm] at e
  rw [e]
  exact Nat.mod_eq_of_lt c.isLt

theorem packG_clear (k : Nat) (c : Digest) (v : Nat)
    (hv : v / 2 ^ gOff k % 2 ^ gBits k = topBits (gBits k) c) :
    packG k (clearTop (gBits k) c) v = c := by
  have hb := gBits_le k
  have hz : topBits (gBits k) (clearTop (gBits k) c) = 0 := by
    unfold topBits clearTop
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    exact Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity))
  rw [packG_of_clear k _ v hz]
  apply BitVec.eq_of_toNat_eq
  unfold clearTop
  unfold topBits at hv
  rw [hv, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hm : c.toNat % 2 ^ (128 - gBits k) < 2 ^ 128 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.mod_eq_of_lt hm, Nat.mod_mod]
  have e := Nat.mod_add_div c.toNat (2 ^ (128 - gBits k))
  rw [mul_comm] at e
  rw [e]
  exact Nat.mod_eq_of_lt c.isLt

theorem sigBC_sigDecC (b : CBytes) : sigBC (sigDecC b)=b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigBC_toNat]
  have hD : digNat (encList (sigDecC b))=b.toNat%2^(128*324) := by
    apply digNat_eq_of_digits
    · rw [encList_length];exact Nat.mod_lt _ (by positivity)
    · intro k hk
      rw [encList_length] at hk
      rw [mod_digit _ 324 k hk, encList_getD _ k hk, getD_eraseIdx]
      by_cases hp : 166 ≤ k ∧ k ≤ 175
      · rw [if_pos hp, if_pos (by omega), sigDigests_sigDecC b k (by omega), xField_sigDecC]
        have hj : 1 ≤ k - 165 ∧ k - 165 ≤ 10 := by omega
        have hdig := xOfB_digit b (k - 165) hj.1 hj.2
        rw [show 165 + (k - 165) = k by omega] at hdig
        have hc : digC b k = clearTop (topZeroBits (k - 165)) (cDig b k) := by
          rw [digC, if_pos (by omega), if_pos (by omega)]
        rw [hc, packD_clear _ hj _ _ hdig, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      · rw [if_neg hp]
        by_cases hlt : k < 176
        · have hg : gBits k = 0 := gBits_eq_zero k (by omega)
          rw [if_pos hg, if_pos hlt, sigDigests_sigDecC b k (by omega), digC, if_pos hlt,
            if_neg (show ¬ (166 ≤ k) by omega), cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
        · by_cases hg : gBits k = 0
          · rw [if_pos hg, if_neg hlt, sigDigests_sigDecC b (k+1) (by omega), digC,
              if_neg (show ¬ (k+1 < 176) by omega), if_neg (show ¬ (k+1 = 176) by omega), show k+1-1=k by omega,
              if_pos hg, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
          · rw [if_neg hg, if_neg hlt, sigDigests_sigDecC b (k+1) (by omega), digC,
              if_neg (show ¬ (k+1 < 176) by omega), if_neg (show ¬ (k+1 = 176) by omega), show k+1-1=k by omega,
              if_neg hg, vField_sigDecC, packG_clear k _ _ (vOfB_digit b k hg), cDig, BitVec.extractLsb'_toNat,
              Nat.shiftRight_eq_div_pow]
  have hT : ((sigDigests (sigDecC b)).getD 176 0).toNat%2^64=b.toNat/2^(128*324)%2^64 := by
    rw [sigDigests_sigDecC b 176 (by decide), digC_176_toNat]
    rw [show b.toNat / 2 ^ (128 * 324) % 2 ^ 64 + vOfB b * 2 ^ 64 + xOfB b % 2 ^ 24 * 2 ^ 80 =
      b.toNat / 2 ^ (128 * 324) % 2 ^ 64 + (vOfB b + xOfB b % 2 ^ 24 * 2 ^ 16) * 2 ^ 64 by ring,
      Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [hD,hT]
  have hb : b.toNat / 2 ^ (128 * 324) < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact b.isLt
  rw [Nat.mod_eq_of_lt hb]
  exact Nat.mod_add_div _ _
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest

theorem normalizeV6_fill (sig : SharedSignature) (c : Nat) :
    normalizeV6 (fillTopSignature sig c) = normalizeV6 sig := by
  unfold normalizeV6 fillTopSignature
  congr 1
  funext lay
  congr 1
  funext j
  simp only [ClaudeWCT.WCT9.fillLayer]
  split
  · rename_i h
    obtain ⟨hl, hj⟩ := h
    have : lay = 0 := Fin.ext hl
    subst this
    have hidx : layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val = 176 := by
      simp [layIdx, SigGolfCandidate.T3.chainCount, hj]
    rw [hidx]
    unfold normD
    rw [if_neg (by decide), if_pos rfl, if_neg (by decide), if_pos rfl, ClaudeWCT.WCT9.setTop_toNat]
    congr 1
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 104 ≤ 111)),
      show c % 2 ^ 17 * 2 ^ 111 % 2 ^ 104 = 0 from
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]
  · rfl

theorem sigDigests_fill (sig : SharedSignature) (c : Nat) :
    sigDigests (fillTopSignature sig c) =
      (sigDigests sig).set 176 (ClaudeWCT.WCT9.setTop ((sig.layers 0).path ClaudeWCT.WCT9.topJ) c) := by
  have hR : ∀ l : SigGolfCandidate.T3.Layer, l.val ≠ 0 → layerList (fillTopSignature sig c) l = layerList sig l := by
    intro l h
    simp only [layerList, fillTopSignature, ClaudeWCT.WCT9.fillLayer_ne _ _ _ h]
  unfold sigDigests
  rw [hR 1 (by decide), hR 2 (by decide), hR 3 (by decide)]
  have hA : (([sig.rho] ++ (List.ofFn sig.forest.pairs).flatMap pairList) ++ singletonList sig.forest.singleton).length
      = 114 := by
    simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]
  rw [List.set_append_right _ _ (by omega), hA, List.set_append_left _ _ (by simp [layerList_length]; decide)]
  congr 2

/-- The compact bytes ignore the brute-forced top sibling bits 111..127 (unconditional; U16b: proved directly, the
round trip now needs clear ground slots). -/
theorem sigBC_fillTopSignature (sig : SharedSignature) (c : Nat) :
    sigBC (fillTopSignature sig c) = sigBC sig := by
  have h176 : 176 < (sigDigests sig).length := by rw [sigDigests_length]; decide
  have hd : (sigDigests sig).getD 176 0 = (sig.layers 0).path ClaudeWCT.WCT9.topJ := by
    have := sigDigests_layPath sig 0 11 (by decide)
    exact this
  have hx : ∀ x : Nat, ∀ y : Nat, (x % 2 ^ 111 + y % 2 ^ 17 * 2 ^ 111) % 2 ^ 104 = x % 2 ^ 104 := by
    intro x y
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 104 ≤ 111)),
      show y % 2 ^ 17 * 2 ^ 111 % 2 ^ 104 = 0 from
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]
  have hm : ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat % 2 ^ 104 =
      ((sigDigests sig).getD 176 0).toNat % 2 ^ 104 := by
    rw [sigDigests_fill, List.getD_eq_getElem _ _ (by rw [List.length_set]; exact h176), List.getElem_set_self,
      ClaudeWCT.WCT9.setTop_toNat, hx, hd]
  have hv : vField (fillTopSignature sig c) = vField sig := by
    unfold vField
    rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self ((sigDigests sig).getD 176 0).toNat,
      show (2:Nat) ^ 64 * 2 ^ 16 = 2 ^ 80 by norm_num,
      ← Nat.mod_mod_of_dvd ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat
        (Nat.pow_dvd_pow 2 (by norm_num : 80 ≤ 104)),
      ← Nat.mod_mod_of_dvd ((sigDigests sig).getD 176 0).toNat (Nat.pow_dvd_pow 2 (by norm_num : 80 ≤ 104)), hm]
  have hxf : xField (fillTopSignature sig c) = xField sig := by
    unfold xField
    rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self ((sigDigests sig).getD 176 0).toNat,
      show (2:Nat) ^ 80 * 2 ^ 24 = 2 ^ 104 by norm_num, hm]
    rfl
  have ht : ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat % 2 ^ 64 =
      ((sigDigests sig).getD 176 0).toNat % 2 ^ 64 := by
    rw [← Nat.mod_mod_of_dvd ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat
        (Nat.pow_dvd_pow 2 (by norm_num : 64 ≤ 104)),
      ← Nat.mod_mod_of_dvd ((sigDigests sig).getD 176 0).toNat (Nat.pow_dvd_pow 2 (by norm_num : 64 ≤ 104)), hm]
  have he : (sigDigests (fillTopSignature sig c)).eraseIdx 176 = (sigDigests sig).eraseIdx 176 := by
    rw [sigDigests_fill, List.eraseIdx_set_eq]
  unfold sigBC encList
  rw [he, hv, hxf, ht]


theorem layIdx_ge (l : SigGolfCandidate.T3.Layer) (h : l.val ≠ 0) : 177 ≤ layIdx l := by
  revert h; revert l; decide

/-- U16b: the codec's ground slots are the lower path nodes with `lowerPathBits` zero bits (compact index
`layIdx lay + chainCount lay + j - 1`, after erasing digest 176). -/
theorem gBits_lowerPath : ∀ (lay : SigGolfCandidate.T3.Layer) (j : Fin (SigGolfCandidate.T3.height lay)),
    lay.val ≠ 0 → gBits (layIdx lay + SigGolfCandidate.T3.chainCount lay + j.val - 1) = lowerPathBits lay j.val := by
  decide

/-- The codec's normal form is the normal form `SharedForest.normTop` that `expand` applies first. -/
theorem normalizeV6_eq_normTop (s : SharedSignature) : normalizeV6 s = normTop s := by
  unfold normalizeV6 normTop
  congr 1
  funext lay
  unfold normLayer
  congr 1
  funext j
  by_cases h0 : lay.val = 0
  · have hl : lay = 0 := Fin.ext h0
    subst hl
    rw [if_pos (show ((0 : SigGolfCandidate.T3.Layer) : Nat) = 0 from rfl)]
    have hk : layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val = 165 + j.val := rfl
    have hj : j.val < 12 := j.isLt
    rw [hk]
    unfold normD normPathD clearTop
    rw [show 165 + j.val - 165 = j.val by omega]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [if_neg h0]
    have hg := gBits_lowerPath lay j h0
    have := layIdx_ge lay h0
    unfold normD normLowerPathD clearTop
    rw [if_neg (by omega), if_neg (by omega), hg]
    by_cases hz : lowerPathBits lay j.val = 0
    · rw [if_neg (fun h => h.2 hz), if_pos hz]
    · rw [if_pos ⟨by omega, hz⟩, if_neg hz]

/-- U16b: `LowerPathOK` signatures have clear ground slots. -/
theorem groundClear_of_lowerPathOK (s : SharedSignature) (h : LowerPathOK s) : GroundClear s := by
  have key : ∀ (lay : SigGolfCandidate.T3.Layer) (j : Fin (SigGolfCandidate.T3.height lay)), lay.val ≠ 0 →
      topBits (gBits (layIdx lay + SigGolfCandidate.T3.chainCount lay + j.val - 1))
        (((sigDigests s).eraseIdx 176).getD (layIdx lay + SigGolfCandidate.T3.chainCount lay + j.val - 1) 0) = 0 := by
    intro lay j h0
    have hi := layIdx_ge lay h0
    rw [getD_eraseIdx, if_neg (by omega), show layIdx lay + SigGolfCandidate.T3.chainCount lay + j.val - 1 + 1 =
      layIdx lay + (SigGolfCandidate.T3.chainCount lay + j.val) by omega, sigDigests_layPath s lay j.val j.isLt,
      gBits_lowerPath lay j h0]
    exact h lay (fun e => h0 (congrArg Fin.val e)) j
  intro k hk
  rcases gBits_ne_zero k hk with h | h | h | h | h | h | h | h | h <;> subst h
  · exact key 1 ⟨6, by decide⟩ (by decide)
  · exact key 1 ⟨5, by decide⟩ (by decide)
  · exact key 1 ⟨4, by decide⟩ (by decide)
  · exact key 2 ⟨5, by decide⟩ (by decide)
  · exact key 2 ⟨4, by decide⟩ (by decide)
  · exact key 2 ⟨3, by decide⟩ (by decide)
  · exact key 3 ⟨5, by decide⟩ (by decide)
  · exact key 3 ⟨4, by decide⟩ (by decide)
  · exact key 3 ⟨3, by decide⟩ (by decide)

/-- img-v6 codec round trip in the form used by the final pipeline (U16b: on clear ground slots, e.g. `LowerPathOK`). -/
theorem sigDecC_sigBC_normTop (s : SharedSignature) (hg : GroundClear s) : sigDecC (sigBC s) = normTop s :=
  (sigDecC_sigBC s hg).trans (normalizeV6_eq_normTop s)

/-- U16b: the compact encoder is injective up to the normal form `normTop` (on clear ground slots). -/
theorem sigBC_injective_normTop (s t : SharedSignature) (hs : GroundClear s) (ht : GroundClear t)
    (h : sigBC s = sigBC t) : normTop s = normTop t := by
  rw [← sigDecC_sigBC_normTop s hs, h, sigDecC_sigBC_normTop t ht]

/-- U16b: a lower path node that passes its zero test is its own normal form. -/
theorem normLowerPathD_of_zero (lay : SigGolfCandidate.T3.Layer) (j : Nat) (d : BitVec 128)
    (h : d.toNat / 2 ^ (128 - lowerPathBits lay j) = 0) : normLowerPathD lay j d = d := by
  unfold normLowerPathD
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    have hlt : d.toNat < 2 ^ (128 - lowerPathBits lay j) := by
      rcases Nat.lt_or_ge d.toNat (2 ^ (128 - lowerPathBits lay j)) with h' | h'
      · exact h'
      · exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.div_pos h' (by positivity)))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt d.isLt]

/-- U16b: under `LowerPathOK` the codec normal form leaves the lower layers unchanged. -/
theorem normTop_layers_lower (s : SharedSignature) (hok : LowerPathOK s) (lay : SigGolfCandidate.T3.Layer)
    (h0 : lay ≠ 0) : (normTop s).layers lay = s.layers lay := by
  have h0' : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
  change normLayer lay (s.layers lay) = s.layers lay
  unfold normLayer
  have hp : (fun j : Fin (SigGolfCandidate.T3.height lay) => if lay.val = 0 then normPathD j.val ((s.layers lay).path j)
      else normLowerPathD lay j.val ((s.layers lay).path j)) = (s.layers lay).path := by
    funext j
    rw [if_neg h0']
    exact normLowerPathD_of_zero lay j.val _ (hok lay h0 j)
  rw [hp]

end ClaudeWCT.W9.T3M.SharedCodec

/-! ## T51 decoded-signature facts (KEYCODEC, round 2)

The expander's decoder DEC (words 54569..54738) writes digest `k` of the 5,195-byte signature at slot
`internalFullIndex k` (16 bytes per slot from `0x7000`), zero at the dummy slots (`internalDummy`), and the hint
`xOfB b / 2^24` at `0x66000`. `fill_sigDecC`: the decoded signature has its brute-forced field (top sibling bits
111..127) clear. The `inflatedRead_*` lemmas read the slot layout back without letting the kernel unfold `digC` against
`inflatedRead` (that comparison blows up on T51's `digC`). -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

/-- T51: the decoded top sibling (digest 176) is below `2^104` (bits 104..111 zero-test, 111..127 filled by expand). -/
theorem digC_176_lt (b : CBytes) : (digC b 176).toNat < 2 ^ 104 := by
  rw [digC_176_toNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 64 by positivity)
  have h2 := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 24 by positivity)
  have h3 := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 64 = t at *
  generalize xOfB b % 2 ^ 24 = x at *
  generalize vOfB b = v at *
  simp only [Nat.reducePow] at *
  omega

/-- T51: the decoded signature has its brute-forced top-sibling field (bits 111..127) clear. -/
theorem fill_sigDecC (b : CBytes) : fillTopSignature (sigDecC b) 0 = sigDecC b := by
  have hl : (fun lay => ClaudeWCT.WCT9.fillLayer lay ((sigDecC b).layers lay) 0) = (sigDecC b).layers := by
    funext lay
    have hp : (fun j : Fin (height lay) => if lay.val = 0 ∧ j.val = 11 then
        ClaudeWCT.WCT9.setTop (((sigDecC b).layers lay).path j) 0 else ((sigDecC b).layers lay).path j) =
        ((sigDecC b).layers lay).path := by
      funext j
      split
      · rename_i h
        obtain ⟨hl0, hj⟩ := h
        have : lay = 0 := Fin.ext hl0
        subst this
        apply BitVec.eq_of_toNat_eq
        rw [ClaudeWCT.WCT9.setTop_toNat]
        change (digC b (layIdx 0 + chainCount 0 + j.val)).toNat % 2 ^ 111 + 0 % 2 ^ 17 * 2 ^ 111 =
          (digC b (layIdx 0 + chainCount 0 + j.val)).toNat
        have hidx : layIdx 0 + chainCount 0 + j.val = 176 := by
          simp [layIdx, chainCount, hj]
        rw [hidx, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
        exact Nat.mod_eq_of_lt (lt_trans (digC_176_lt b) (by norm_num))
      · rfl
    unfold ClaudeWCT.WCT9.fillLayer
    rw [hp]
  unfold fillTopSignature
  rw [hl]

/-- T51: the decoded policy hints are the top 13 bits of the 37-bit X field. -/
theorem policyHints_sigDecC_toNat (b : CBytes) : (sigDecC b).policyHints.toNat = xOfB b / 2 ^ 24 := by
  change (BitVec.ofNat 16 (xOfB b / 2 ^ 24)).toNat = _
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := xOfB_lt b
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at *
  omega

theorem policyHints_sigDecC_lt (b : CBytes) : (sigDecC b).policyHints.toNat < 2 ^ 13 := by
  rw [policyHints_sigDecC_toNat]
  have := xOfB_lt b
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at *
  omega

/-! ### The slot layout (`internalFullIndex`) read back through `inflatedRead` -/

theorem inflatedRead_main {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : 114 ≤ k) (hk' : k ≤ 176) :
    inflatedRead z read (k + 4) = read k := by
  rw [← internalFullIndex_main k hk hk', inflatedRead_internal]

theorem inflatedRead_lower {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : 177 ≤ k) :
    inflatedRead z read (k + 7) = read k := by
  rw [← internalFullIndex_lower k hk, inflatedRead_internal]

/-- Slot 0 is `rho` (stated through `inflatedRead_internal`, so the kernel never unfolds `digC` against `inflatedRead`). -/
theorem inflatedRead_rho (b : CBytes) : inflatedRead (0 : Digest) (digC b) 0 = (sigDecC b).rho :=
  inflatedRead_internal (0 : Digest) (digC b) 0

theorem inflatedRead_dummy {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : internalDummy k = true) :
    inflatedRead z read k = z := by
  unfold inflatedRead; rw [if_pos hk]

theorem externalFullIndex_lt (k : Nat) (hk : k < 332) (hd : internalDummy k = false) : externalFullIndex k < 325 := by
  simp only [internalDummy, decide_eq_false_iff_not] at hd
  unfold externalFullIndex
  split_ifs <;> omega

theorem internalFullIndex_external (k : Nat) (hd : internalDummy k = false) :
    internalFullIndex (externalFullIndex k) = k := by
  simp only [internalDummy, decide_eq_false_iff_not] at hd
  unfold internalFullIndex externalFullIndex
  split_ifs <;> omega

end ClaudeWCT.W9.T3M.SharedCodec
end
