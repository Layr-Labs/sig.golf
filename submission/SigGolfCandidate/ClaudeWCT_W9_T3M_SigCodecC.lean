import SigGolfCandidate.ClaudeWCT_W9_T3M_SigCodec
import SigGolfCandidate.ClaudeWCT_WCT9_Omit
import SigGolfCandidate.Research_V7Composed198Gate

/-! # The compact (H2) signature bytes

5,310 bytes: the 332 digests of `sigDigests` with digest 183 (the top layer's level-11 sibling) cut out, then that
digest's low 14 bytes. `sigBC` encodes, `sigDecC` decodes (the omitted 16 bits decode as zero), and
`sigDecC (sigBC σ) = proj σ`, `sigBC (sigDecC b) = b`, `sigBC (proj σ) = sigBC σ`. -/

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit digNat_eq_of_digits getD_append_left' getD_append_right'
  getD_ofFn' chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
set_option maxRecDepth 10000

abbrev CBytes := Bytes 5310
def sibIdx : Nat := 183
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- The digest at full-layout index `k` of the compact bytes. -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 183 then cDig b k else if k = 183 then cDig b 331 else cDig b (k - 1)
def sigDecC (b : CBytes) : WCT9.Signature where
  rho := digC b 0
  openings := fun k => ⟨fun t => digC b (1 + 13 * k.val + t.val), fun l => digC b (1 + 13 * k.val + 6 + l.val)⟩
  layers := fun lay => ⟨fun i => digC b (layIdx lay + i.val), fun j => digC b (layIdx lay + (chainCount lay + j.val))⟩
def sigBC (s : WCT9.Signature) : CBytes :=
  BitVec.ofNat _ (digNat ((sigDigests s).eraseIdx 183) + 2 ^ (128 * 331) * (((sigDigests s).getD 183 0).toNat % 2 ^ 112))


theorem cDig_toNat (b : CBytes) (k : Nat) : (cDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem cTail_lt (b : CBytes) : b.toNat / 2 ^ (128 * 331) < 2 ^ 112 := by
  have hb := b.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  exact lt_of_lt_of_eq hb (by norm_num)

theorem getD_eraseIdx {α : Type} (l : List α) (i j : Nat) (d : α) :
    (l.eraseIdx i).getD j d = if j < i then l.getD j d else l.getD (j + 1) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  split <;> rfl


theorem mod_digit (B n k : Nat) (hk : k < n) :
    B % 2 ^ (128 * n) / 2 ^ (128 * k) % 2 ^ 128 = B / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [show 2 ^ (128 * n) = 2 ^ (128 * k) * 2 ^ (128 * (n - k)) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 2 (by omega)

theorem lt_split (X y A M : Nat) (hX : X < 2 ^ A) (hy : y < M) : X + 2 ^ A * y < 2 ^ A * M := by
  have : 2 ^ A * y + 2 ^ A ≤ 2 ^ A * M := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  omega

theorem split_mod (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) % 2 ^ A = D := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hD]

theorem split_div (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) / 2 ^ A = T := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hD, Nat.zero_add]

theorem pow_5310 : (2 : Nat) ^ (8 * 5310) = 2 ^ (128 * 331) * 2 ^ 112 := by rw [← pow_add]

set_option exponentiation.threshold 50000 in



theorem digC_183 (b : CBytes) : digC b 183 = cDig b 331 := by
  unfold digC; rw [if_neg (by decide), if_pos rfl]

end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_cons digNat_nil)

/-- Full-layout digest index of compact digest slot `k` (slot 331 holds the top sibling). -/
def cIdx (k : Nat) : Nat := if k < 183 then k else if k < 331 then k + 1 else 183
def compactList (s : WCT9.Signature) : List Digest := (List.range 332).map fun k => (sigDigests s).getD (cIdx k) 0

theorem digNat_append (L1 L2 : List Digest) : digNat (L1 ++ L2) = digNat L1 + 2 ^ (128 * L1.length) * digNat L2 := by
  induction L1 with
  | nil => simp [digNat_nil]
  | cons d L ih =>
    rw [List.cons_append, digNat_cons, digNat_cons, ih, List.length_cons,
      show 128 * (L.length + 1) = 128 + 128 * L.length by ring, pow_add]
    ring


theorem mod_split (X y A M : Nat) (hX : X < 2 ^ A) (hM : 0 < M) :
    (X + 2 ^ A * y) % (2 ^ A * M) = X + 2 ^ A * (y % M) := by
  conv_lhs => rw [← Nat.div_add_mod y M]
  rw [show X + 2 ^ A * (M * (y / M) + y % M) = (X + 2 ^ A * (y % M)) + (2 ^ A * M) * (y / M) by ring,
    Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hr : y % M < M := Nat.mod_lt _ hM
  have h1 : 2 ^ A * (y % M) + 2 ^ A ≤ 2 ^ A * M := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  omega
end ClaudeWCT.W9.T3M

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

/-- T51: the 5,195-byte compact signature (324 digests + an 11-byte tail; #938 img-v6: 5,239 bytes). -/
abbrev CBytes := Bytes 5195
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- Offset of the X field in the top `b_j = topZeroBits j` bits of the path node at height `j` (`j = 1..10`):
`Σ_{h < j} b_h` = 0, 1, 2, 4, 7, 11, 16, 22 for `j = 3..10` (heights 1, 2 carry no bits). -/
def xOff (j : Nat) : Nat := ((List.range j).map topZeroBits).sum
def clearTop (j : Nat) (d : Digest) : Digest := BitVec.ofNat 128 (d.toNat % 2 ^ (128 - j))
def topBits (j : Nat) (d : Digest) : Nat := d.toNat / 2 ^ (128 - j)
/-- T51: the 29-bit X field read from the top `b_j` bits of the path nodes of heights 3..10 (digests 168..175). -/
def xOfB (b : CBytes) : Nat :=
  topBits 1 (cDig b 168) + topBits 1 (cDig b 169) * 2 ^ 1 + topBits 2 (cDig b 170) * 2 ^ 2 +
  topBits 3 (cDig b 171) * 2 ^ 4 + topBits 4 (cDig b 172) * 2 ^ 7 + topBits 5 (cDig b 173) * 2 ^ 11 +
  topBits 6 (cDig b 174) * 2 ^ 16 + topBits 7 (cDig b 175) * 2 ^ 22
/-- Decoded digest `k`: the path nodes of heights 1..10 (digests 166..175) lose their top `b_j` bits; index 176 (top
sibling) = tail 88 bits + X bits 0..15 (bits 88..103; bits 104..127 zero, 112..127 brute-forced by expand). -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 176 then (if 166 ≤ k then clearTop (topZeroBits (k - 165)) (cDig b k) else cDig b k)
  else if k = 176 then BitVec.ofNat 128 (b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88)
  else cDig b (k - 1)
def sigDecC (b : CBytes) : SharedSignature where
  rho := digC b 0
  policyHints := BitVec.ofNat 16 (xOfB b / 2 ^ 16)
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
/-- T51: X = top sibling bits 88..103 (16) | hint (13 bits) << 16 (29 bits). -/
def xField (s : SharedSignature) : Nat :=
  ((sigDigests s).getD 176 0).toNat / 2 ^ 88 % 2 ^ 16 + s.policyHints.toNat % 2 ^ 13 * 2 ^ 16
/-- T51: the path node of height `j` with X bits `xOff j ..` in its top `b_j = topZeroBits j` bits. -/
def packD (j : Nat) (d : Digest) (x : Nat) : Digest :=
  BitVec.ofNat 128 (d.toNat % 2 ^ (128 - topZeroBits j) +
    x / 2 ^ xOff j % 2 ^ topZeroBits j * 2 ^ (128 - topZeroBits j))
def encList (s : SharedSignature) : List Digest :=
  (List.range 324).map fun k => if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
    (xField s) else ((sigDigests s).eraseIdx 176).getD k 0
def sigBC (s : SharedSignature) : CBytes :=
  BitVec.ofNat _ (digNat (encList s) + 2 ^ (128 * 324) * (((sigDigests s).getD 176 0).toNat % 2 ^ 88))
theorem compact_length : 324 * 16 + 11 = 5195 := by decide
/-- The normal form a decoded signature has (T51): path tops of heights 1..10 clear (`b_j` bits), top sibling below
bit 104, hint 13 bits. -/
def normD (k : Nat) (d : Digest) : Digest :=
  if 166 ≤ k ∧ k ≤ 175 then clearTop (topZeroBits (k - 165)) d
  else if k = 176 then BitVec.ofNat 128 (d.toNat % 2 ^ 104) else d
theorem normD_of_lt (k : Nat) (d : Digest) (hk : k < 166) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega)]
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
      (xField s) else ((sigDigests s).eraseIdx 176).getD k 0 := by
  simp [encList, List.getD_eq_getElem?_getD, hk]

theorem sigBC_toNat (s : SharedSignature) :
    (sigBC s).toNat = digNat (encList s) + 2^(128*324)*(((sigDigests s).getD 176 0).toNat%2^88) := by
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 176 0).toNat (show 0<2^88 by positivity))
  simpa only [←pow_add] using hT

theorem encoded_low (s : SharedSignature) : (sigBC s).toNat%2^(128*324)=digNat (encList s) := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_mod _ _ _ hD]

theorem encoded_tail (s : SharedSignature) :
    (sigBC s).toNat/2^(128*324)%2^88=((sigDigests s).getD 176 0).toNat%2^88 := by
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

theorem xOff_vals : xOff 3 = 0 ∧ xOff 4 = 1 ∧ xOff 5 = 2 ∧ xOff 6 = 4 ∧ xOff 7 = 7 ∧ xOff 8 = 11 ∧ xOff 9 = 16 ∧
    xOff 10 = 22 := by decide

theorem xField_lt (s : SharedSignature) : xField s < 2 ^ 29 := by
  unfold xField
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
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
  rw [(pack_facts 3 1 (by norm_num) rfl _ _).2, (pack_facts 4 1 (by norm_num) rfl _ _).2,
    (pack_facts 5 2 (by norm_num) rfl _ _).2, (pack_facts 6 3 (by norm_num) rfl _ _).2,
    (pack_facts 7 4 (by norm_num) rfl _ _).2, (pack_facts 8 5 (by norm_num) rfl _ _).2,
    (pack_facts 9 6 (by norm_num) rfl _ _).2, (pack_facts 10 7 (by norm_num) rfl _ _).2,
    o3, o4, o5, o6, o7, o8, o9, o10]
  norm_num
  omega

theorem digC_sigBC (s : SharedSignature) (k : Nat) (hk : k<325) :
    digC (sigBC s) k = normD k ((sigDigests s).getD k 0) := by
  by_cases hlt : k<176
  · rw [digC, if_pos hlt, cDig_sigBC s k (by omega), encList_getD s k (by omega), getD_eraseIdx, if_pos hlt]
    by_cases hp : 166 ≤ k
    · rw [if_pos hp, if_pos ⟨hp, by omega⟩, (pack_facts _ _ ⟨by omega, by omega⟩ rfl _ _).1, normD,
        if_pos ⟨hp, by omega⟩]
    · rw [if_neg hp, if_neg (by omega), normD_of_lt _ _ (by omega)]
  · by_cases he : k=176
    · subst he
      rw [digC, if_neg (by decide), if_pos rfl, encoded_tail, xOfB_sigBC, normD, if_neg (by decide), if_pos rfl]
      congr 1
      unfold xField
      have h88 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
      have hm : ((sigDigests s).getD 176 0).toNat % 2 ^ 104 =
          ((sigDigests s).getD 176 0).toNat % 2 ^ 88 + 2 ^ 88 * (((sigDigests s).getD 176 0).toNat / 2 ^ 88 % 2 ^ 16) := by
        rw [show (2:Nat) ^ 104 = 2 ^ 88 * 2 ^ 16 by norm_num, Nat.mod_mul]
      rw [hm]
      omega
    · rw [digC, if_neg hlt, if_neg he, cDig_sigBC s (k-1) (by omega), encList_getD s _ (by omega),
        if_neg (by omega), getD_eraseIdx, if_neg (by omega), show k-1+1=k by omega, normD, if_neg (by omega),
        if_neg he]

theorem policyHints_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).policyHints = BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13) := by
  change BitVec.ofNat 16 (xOfB (sigBC s) / 2 ^ 16) = _
  rw [xOfB_sigBC]
  unfold xField
  congr 1
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
  omega

#print axioms digC_sigBC
#print axioms policyHints_sigDecC_sigBC
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
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),sigDigests_pair s p i.val (by omega),pairList_firstValue]
    have h2 : ((sigDecC (sigBC s)).forest.pairs p).firstPath=(s.forest.pairs p).firstPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+6+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+6+i.val=1+25*p.val+(6+i.val) by omega,
        sigDigests_pair s p (6+i.val) (by omega),pairList_firstPath]
    have h3 : ((sigDecC (sigBC s)).forest.pairs p).secondValues=(s.forest.pairs p).secondValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+12+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+12+i.val=1+25*p.val+(12+i.val) by omega,
        sigDigests_pair s p (12+i.val) (by omega),pairList_secondValue]
    have h4 : ((sigDecC (sigBC s)).forest.pairs p).secondPath=(s.forest.pairs p).secondPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+18+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+18+i.val=1+25*p.val+(18+i.val) by omega,
        sigDigests_pair s p (18+i.val) (by omega),pairList_secondPath]
    cases h : (sigDecC (sigBC s)).forest.pairs p
    cases h' : s.forest.pairs p
    simp only [h,h'] at h1 h2 h3 h4
    cases h1;cases h2;cases h3;cases h4;rfl
  have hs : (sigDecC (sigBC s)).forest.singleton=s.forest.singleton := by
    have h1 : (sigDecC (sigBC s)).forest.singleton.values=s.forest.singleton.values := by
      funext i
      change digC (sigBC s) (101+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),sigDigests_singleton s i.val (by omega),singletonList,
        getD_append_left' (by simp),getD_ofFn']
    have h2 : (sigDecC (sigBC s)).forest.singleton.path=s.forest.singleton.path := by
      funext i
      change digC (sigBC s) (107+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 107+i.val=101+(6+i.val) by omega,
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

theorem normD_of_out (k : Nat) (d : Digest) (hk : k < 166 ∨ 176 < k) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega)]

theorem sigDecC_sigBC (s : SharedSignature) : sigDecC (sigBC s) = normalizeV6 s := by
  have hr : (sigDecC (sigBC s)).rho=s.rho := by
    change digC (sigBC s) 0=s.rho
    rw [digC_sigBC s 0 (by decide),normD_of_lt _ _ (by decide),sigDigests_rho]
  have hh := policyHints_sigDecC_sigBC s
  have hf := forest_sigDecC_sigBC s
  have hl : (sigDecC (sigBC s)).layers=(normalizeV6 s).layers := by
    funext lay
    have hc : layIdx lay+chainCount lay≤325 := by fin_cases lay <;> decide
    have hp : layIdx lay+chainCount lay+height lay≤325 := by fin_cases lay <;> decide
    have hv : ((sigDecC (sigBC s)).layers lay).values=((normalizeV6 s).layers lay).values := by
      funext i
      change digC (sigBC s) (layIdx lay+i.val)=(s.layers lay).values i
      have hn : layIdx lay+i.val < 166 ∨ 176 < layIdx lay+i.val := by
        fin_cases lay <;> simp [layIdx,chainCount] at * <;> omega
      rw [digC_sigBC s _ (by omega),normD_of_out _ _ hn,sigDigests_layValue]
    have hpath : ((sigDecC (sigBC s)).layers lay).path=((normalizeV6 s).layers lay).path := by
      funext i
      change digC (sigBC s) (layIdx lay+chainCount lay+i.val) =
        normD (layIdx lay + chainCount lay + i.val) ((s.layers lay).path i)
      rw [digC_sigBC s _ (by omega), show layIdx lay+chainCount lay+i.val=layIdx lay+(chainCount lay+i.val) by omega,
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

#print axioms sigDecC_sigBC
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
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 1 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 170); have t6 := topBits_lt 3 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 4 (by norm_num) (cDig b 172); have t8 := topBits_lt 5 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 6 (by norm_num) (cDig b 174); have t10 := topBits_lt 7 (by norm_num) (cDig b 175)
  obtain ⟨o3, o4, o5, o6, o7, o8, o9, o10⟩ := xOff_vals
  unfold xOfB
  interval_cases j
  · rw [show topZeroBits 1 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  · rw [show topZeroBits 2 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  all_goals
    first
      | (rw [o3, show topZeroBits 3 = 1 from rfl]; norm_num at *; omega)
      | (rw [o4, show topZeroBits 4 = 1 from rfl]; norm_num at *; omega)
      | (rw [o5, show topZeroBits 5 = 2 from rfl]; norm_num at *; omega)
      | (rw [o6, show topZeroBits 6 = 3 from rfl]; norm_num at *; omega)
      | (rw [o7, show topZeroBits 7 = 4 from rfl]; norm_num at *; omega)
      | (rw [o8, show topZeroBits 8 = 5 from rfl]; norm_num at *; omega)
      | (rw [o9, show topZeroBits 9 = 6 from rfl]; norm_num at *; omega)
      | (rw [o10, show topZeroBits 10 = 7 from rfl]; norm_num at *; omega)

theorem xOfB_lt (b : CBytes) : xOfB b < 2 ^ 29 := by
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 1 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 170); have t6 := topBits_lt 3 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 4 (by norm_num) (cDig b 172); have t8 := topBits_lt 5 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 6 (by norm_num) (cDig b 174); have t10 := topBits_lt 7 (by norm_num) (cDig b 175)
  unfold xOfB
  norm_num at *
  omega

theorem xField_sigDecC (b : CBytes) : xField (sigDecC b) = xOfB b := by
  have hx := xOfB_lt b
  unfold xField
  rw [sigDigests_sigDecC b 176 (by decide)]
  change (digC b 176).toNat / 2 ^ 88 % 2 ^ 16 + (BitVec.ofNat 16 (xOfB b / 2 ^ 16)).toNat % 2 ^ 13 * 2 ^ 16 = _
  rw [digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have ht := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
  have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 128 := by
    have := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
    norm_num at *
    omega
  rw [Nat.mod_eq_of_lt hlt]
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
        split
        · rename_i hlt
          rw [sigDigests_sigDecC b k (by omega),digC,if_pos hlt,if_neg (by omega),cDig,BitVec.extractLsb'_toNat,
            Nat.shiftRight_eq_div_pow]
        · rename_i hge
          rw [sigDigests_sigDecC b (k+1) (by omega),digC,if_neg (by omega),if_neg (by omega),
            show k+1-1=k by omega,cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  have hT : ((sigDigests (sigDecC b)).getD 176 0).toNat%2^88=b.toNat/2^(128*324)%2^88 := by
    rw [sigDigests_sigDecC b 176 (by decide),digC,if_neg (by decide),if_pos rfl,BitVec.toNat_ofNat]
    have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 128 := by
      have := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
      have := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
      norm_num at *
      omega
    rw [Nat.mod_eq_of_lt hlt, Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [hD,hT]
  have hb : b.toNat / 2 ^ (128 * 324) < 2 ^ 88 := by
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
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 104 ≤ 112)),
      show c % 2 ^ 16 * 2 ^ 112 % 2 ^ 104 = 0 from
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]
  · rfl

theorem sigBC_fillTopSignature (sig : SharedSignature) (c : Nat) :
    sigBC (fillTopSignature sig c) = sigBC sig := by
  calc
    sigBC (fillTopSignature sig c) = sigBC (sigDecC (sigBC (fillTopSignature sig c))) := (sigBC_sigDecC _).symm
    _ = sigBC (normalizeV6 (fillTopSignature sig c)) := by rw [sigDecC_sigBC]
    _ = sigBC (normalizeV6 sig) := by rw [normalizeV6_fill]
    _ = sigBC (sigDecC (sigBC sig)) := by rw [sigDecC_sigBC]
    _ = sigBC sig := sigBC_sigDecC _

#print axioms sigBC_fillTopSignature

theorem layIdx_ge (l : SigGolfCandidate.T3.Layer) (h : l.val ≠ 0) : 177 ≤ layIdx l := by
  revert h; revert l; decide

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
    rw [hk]
    unfold normD normPathD clearTop
    rw [show 165 + j.val - 165 = j.val by omega]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [if_neg h0]
    apply normD_of_out
    right
    have := layIdx_ge lay h0
    omega

/-- img-v6 codec round trip in the form used by the final pipeline. -/
theorem sigDecC_sigBC_normTop (s : SharedSignature) : sigDecC (sigBC s) = normTop s :=
  (sigDecC_sigBC s).trans (normalizeV6_eq_normTop s)

#print axioms sigDecC_sigBC_normTop
end ClaudeWCT.W9.T3M.SharedCodec

/-! ## T51 decoded-signature facts (KEYCODEC, round 2)

The expander's decoder DEC (words 54569..54738) writes digest `k` of the 5,195-byte signature at slot
`internalFullIndex k` (16 bytes per slot from `0x7000`), zero at the dummy slots (`internalDummy`), and the hint
`xOfB b / 2^16` at `0x66000`. `fill_sigDecC`: the decoded signature has its brute-forced field (top sibling bits
112..127) clear. The `inflatedRead_*` lemmas read the slot layout back without letting the kernel unfold `digC` against
`inflatedRead` (that comparison blows up on T51's `digC`). -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

/-- T51: the decoded top sibling (digest 176) is below `2^104` (bits 104..111 zero-test, 112..127 filled by expand). -/
theorem digC_176_lt (b : CBytes) : (digC b 176).toNat < 2 ^ 104 := by
  rw [digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
  have h2 := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
  have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 104 := by
    norm_num at *
    omega
  rw [Nat.mod_eq_of_lt (lt_trans hlt (by norm_num))]
  exact hlt

/-- T51: the decoded signature has its brute-forced top-sibling field (bits 112..127) clear. -/
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
        change (digC b (layIdx 0 + chainCount 0 + j.val)).toNat % 2 ^ 112 + 0 % 2 ^ 16 * 2 ^ 112 =
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

/-- T51: the decoded policy hints are the top 13 bits of the 29-bit X field. -/
theorem policyHints_sigDecC_toNat (b : CBytes) : (sigDecC b).policyHints.toNat = xOfB b / 2 ^ 16 := by
  change (BitVec.ofNat 16 (xOfB b / 2 ^ 16)).toNat = _
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

#print axioms fill_sigDecC
end ClaudeWCT.W9.T3M.SharedCodec
