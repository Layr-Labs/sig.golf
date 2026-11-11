import SigGolfCandidate.LegacyCodec
set_option debug.skipKernelTC true
set_option linter.all false

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

/-- Y5: the 5,186-byte compact signature (324 digests + a 2-byte tail; N7g: 5,187 bytes, R6: 5,188 bytes, E8: 5,189
bytes, E11: 5,190 bytes, U16b: 5,192 bytes, T51: 5,195 bytes). -/
abbrev CBytes := Bytes 5186
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- Offset of the X field in the top `b_j = topZeroBits j` bits of the path node at height `j` (`j = 1..10`):
`Σ_{h < j} b_h` = 0, 1, 3, 6, 10, 15, 21, 28 for `j = 3..10` (R6; heights 1, 2 carry no bits). -/
def xOff (j : Nat) : Nat := ((List.range j).map topZeroBits).sum
def clearTop (j : Nat) (d : Digest) : Digest := BitVec.ofNat 128 (d.toNat % 2 ^ (128 - j))
def topBits (j : Nat) (d : Digest) : Nat := d.toNat / 2 ^ (128 - j)
/-- R6 (F4), Y5: the 36-bit X field read from the top `b_j` bits of the path nodes of heights 3..10 (digests
168..175): bits 0..32 are top-sibling bits 66..98, bits 33..35 are bits 128..130 of `N`. -/
def xOfB (b : CBytes) : Nat :=
  topBits 1 (cDig b 168) + topBits 2 (cDig b 169) * 2 ^ 1 + topBits 3 (cDig b 170) * 2 ^ 3 +
  topBits 4 (cDig b 171) * 2 ^ 6 + topBits 5 (cDig b 172) * 2 ^ 10 + topBits 6 (cDig b 173) * 2 ^ 15 +
  topBits 7 (cDig b 174) * 2 ^ 21 + topBits 8 (cDig b 175) * 2 ^ 28
/-- Y5 (hint trim): the hint alphabets `A1 = {6, 10, 12, 14}`, `A2 = {6, 10, 12, 14, 16, 18}`, `A3 = {6, 9..22}`, read
from an index (the expand decode's additive form). -/
def hintA1 (i : Nat) : Nat := 6 + (if 1 ≤ i then 4 else 0) + (if 2 ≤ i then 2 else 0) + (if 3 ≤ i then 2 else 0)
def hintA2 (i : Nat) : Nat := 6 + (if 1 ≤ i then 4 else 0) + (if 2 ≤ i then 2 else 0) + (if 3 ≤ i then 2 else 0) + (if 4 ≤ i then 2 else 0) + (if 5 ≤ i then 2 else 0)
def hintA3 (i : Nat) : Nat := if i = 0 then 6 else i + 8
/-- Y5: the index of a digit in its alphabet (the sign tail's counting form; `A3`: `f - 8` on `9..22`, 0 on 6). -/
def hintI1 (f : Nat) : Nat := (if 10 ≤ f then 1 else 0) + (if 12 ≤ f then 1 else 0) + (if 14 ≤ f then 1 else 0)
def hintI2 (f : Nat) : Nat :=
  (if 10 ≤ f then 1 else 0) + (if 12 ≤ f then 1 else 0) + (if 14 ≤ f then 1 else 0) + (if 16 ≤ f then 1 else 0) +
    (if 18 ≤ f then 1 else 0)
def hintI3 (f : Nat) : Nat := if 8 ≤ f then f - 8 else 0
/-- Y5 (hint trim; C13R68 skip-2 had `t = 418 f1' + 22 f2 + f3 < 5852`): the hint digits `h = 529 f1 + 23 f2 + f3`
as the index code `t = (i1 · 6 + i2) · 15 + i3 < 360` of the alphabet indices. Hints `≥ 8192` (only the
non-canonical decode `hintOfN`) map to `h - 8192`. -/
def hintT (h : Nat) : Nat :=
  if h < 8192 then (hintI1 (h / 529) * 6 + hintI2 (h % 529 / 23)) * 15 + hintI3 (h % 23) else h - 8192
/-- Y5: re-pack the index code `t < 360` to the hint `529 A1[t / 90] + 23 A2[t / 15 % 6] + A3[t % 15]`
(expand decode). -/
def packH (t : Nat) : Nat := 529 * hintA1 (t / 90) + 23 * hintA2 (t / 15 % 6) + hintA3 (t % 15)
/-- R6 (F4), Y5: the 131-bit compact rho/hint field `N = rho * 360 + t` of compact bytes: slot 0 (`N mod 2^128`)
plus X bits 33..35 (`N / 2^128`). -/
def nOfB (b : CBytes) : Nat := (cDig b 0).toNat + xOfB b / 2 ^ 33 * 2 ^ 128
/-- N7g (canonical check), Y5: the decoded hint word. Canonical `N < R * 360`: the re-packed hint `packH (N % 360)`
(always `< 8192`). Non-canonical `N` (`R * 360 ≤ N < 2^131`, so `N % 360 = N - R * 360 < 248`): `8192 + N % 360`,
which the expand spec rejects (`policyHints ≥ 8192`) exactly as DEC branches to word 354; `hintT` inverts both
branches, so `sigBC ∘ sigDecC` stays the identity on all compact bytes. -/
def hintOfN (n : Nat) : Nat := if n < R * 360 then packH (n % 360) else 8192 + n % 360
/-- N7g (B): zero bits `b` of the ground slot at compact index `k` (index after erasing digest 176). Lower path
siblings: L1 heights 6/5/4/3 (225/224/223/222) and L2, L3 heights 5/4/3/2 (274..271, 323..320) carry 4/3/2/1 bits
(heaps 2..3 / 4..7 / 8..15 / 16..31; R6: L1 3/2/2/1, L2, L3 3/2/1/1); FTS level-4 auth siblings (heaps 8..15) of
coordinates 0..8 (compact 11, 23, 36, 48, 61, 73, 86, 98, 111) carry 1, 1, 2, 2, 2, 2, 2, 2, 2 bits; Y5: the
level-5 auth siblings (heaps 16..31) of coordinates 0..3 (compact 10, 22, 35, 47) carry 1 bit each. -/
def gBits : Nat → Nat
  | 225 => 4 | 224 => 3 | 223 => 2 | 222 => 1 | 274 => 4 | 273 => 3 | 272 => 2 | 271 => 1 | 323 => 4 | 322 => 3 | 321 => 2 | 320 => 1 | 11 => 1 | 23 => 1 | 36 => 2 | 48 => 2 | 61 => 2 | 73 => 2 | 86 => 2 | 98 => 2 | 111 => 2 | 10 => 1 | 22 => 1 | 35 => 1 | 47 => 1 | _ => 0
/-- N7g (B, V46), Y5 (V50): offset of slot `k`'s bits in the 50-bit V field (top sibling bits 16..65). -/
def gOff : Nat → Nat
  | 225 => 0 | 224 => 4 | 223 => 7 | 222 => 9 | 274 => 10 | 273 => 14 | 272 => 17 | 271 => 19 | 323 => 20 | 322 => 24 | 321 => 27 | 320 => 29 | 11 => 30 | 23 => 31 | 36 => 32 | 48 => 34 | 61 => 36 | 73 => 38 | 86 => 40 | 98 => 42 | 111 => 44 | 10 => 46 | 22 => 47 | 35 => 48 | 47 => 49 | _ => 0
/-- N7g (B, V46), Y5 (V50): the 50-bit V field read from the top `gBits k` bits of the ground slots. -/
def vOfB (b : CBytes) : Nat :=
  topBits 4 (cDig b 225) * 2 ^ 0 +
  topBits 3 (cDig b 224) * 2 ^ 4 +
  topBits 2 (cDig b 223) * 2 ^ 7 +
  topBits 1 (cDig b 222) * 2 ^ 9 +
  topBits 4 (cDig b 274) * 2 ^ 10 +
  topBits 3 (cDig b 273) * 2 ^ 14 +
  topBits 2 (cDig b 272) * 2 ^ 17 +
  topBits 1 (cDig b 271) * 2 ^ 19 +
  topBits 4 (cDig b 323) * 2 ^ 20 +
  topBits 3 (cDig b 322) * 2 ^ 24 +
  topBits 2 (cDig b 321) * 2 ^ 27 +
  topBits 1 (cDig b 320) * 2 ^ 29 +
  topBits 1 (cDig b 11) * 2 ^ 30 +
  topBits 1 (cDig b 23) * 2 ^ 31 +
  topBits 2 (cDig b 36) * 2 ^ 32 +
  topBits 2 (cDig b 48) * 2 ^ 34 +
  topBits 2 (cDig b 61) * 2 ^ 36 +
  topBits 2 (cDig b 73) * 2 ^ 38 +
  topBits 2 (cDig b 86) * 2 ^ 40 +
  topBits 2 (cDig b 98) * 2 ^ 42 +
  topBits 2 (cDig b 111) * 2 ^ 44 +
  topBits 1 (cDig b 10) * 2 ^ 46 +
  topBits 1 (cDig b 22) * 2 ^ 47 +
  topBits 1 (cDig b 35) * 2 ^ 48 +
  topBits 1 (cDig b 47) * 2 ^ 49
/-- Decoded digest `k`: R6 (F4): index 0 is `rho = N / 360`; the path nodes of heights 1..10 (digests 166..175)
lose their top `b_j` bits, the ground slots their top `gBits` bits; index 176 (top sibling) = tail 16 bits (Y5; N7g
B: 24, R6: 32) + V (bits 16..65) + X bits 0..32 (bits 66..98; bits 99..127 zero, 108..127 brute-forced by expand). -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k = 0 then BitVec.ofNat 128 (nOfB b / 360)
  else if k < 176 then (if 166 ≤ k then clearTop (topZeroBits (k - 165)) (cDig b k)
    else if gBits k = 0 then cDig b k else clearTop (gBits k) (cDig b k))
  else if k = 176 then BitVec.ofNat 128 (b.toNat / 2 ^ (128 * 324) % 2 ^ 16 + vOfB b * 2 ^ 16 + xOfB b % 2 ^ 33 * 2 ^ 66)
  else if gBits (k - 1) = 0 then cDig b (k - 1) else clearTop (gBits (k - 1)) (cDig b (k - 1))
def sigDecC (b : CBytes) : SharedSignature where
  rho := digC b 0
  policyHints := BitVec.ofNat 16 (hintOfN (nOfB b))
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
/-- R6 (F4), Y5: `N = rho * 360 + t` of a signature, `t = hintT policyHints`. -/
def rhoN (s : SharedSignature) : Nat := s.rho.toNat * 360 + hintT s.policyHints.toNat
/-- Y5: an in-alphabet hint (`h = 529 f1 + 23 f2 + f3` with `f1 ∈ A1, f2 ∈ A2, f3 ∈ A3`): its index code is below
360 and re-packs to `h`. -/
def HintOK (h : Nat) : Prop := hintT h < 360 ∧ packH (hintT h) = h
instance (h : Nat) : Decidable (HintOK h) := inferInstanceAs (Decidable (_ ∧ _))
/-- R6 (F4), Y5: honest rho/hint range: `rho < R` (so `N < R * 360 < 2^131`, canonical) and an in-alphabet hint. -/
def RhoHintOK (s : SharedSignature) : Prop :=
  s.rho.toNat < R ∧ HintOK s.policyHints.toNat
/-- R6 (F4), Y5: X = top sibling bits 66..98 (33) | N bits 128..130 (3) << 33 (36 bits). -/
def xField (s : SharedSignature) : Nat :=
  ((sigDigests s).getD 176 0).toNat / 2 ^ 66 % 2 ^ 33 + rhoN s / 2 ^ 128 % 2 ^ 3 * 2 ^ 33
/-- T51: the path node of height `j` with X bits `xOff j ..` in its top `b_j = topZeroBits j` bits. -/
def packD (j : Nat) (d : Digest) (x : Nat) : Digest :=
  BitVec.ofNat 128 (d.toNat % 2 ^ (128 - topZeroBits j) +
    x / 2 ^ xOff j % 2 ^ topZeroBits j * 2 ^ (128 - topZeroBits j))
/-- N7g (B), Y5: V = top sibling bits 16..65 (50; N7g: 24..69, R6: 32..69). -/
def vField (s : SharedSignature) : Nat := ((sigDigests s).getD 176 0).toNat / 2 ^ 16 % 2 ^ 50
/-- U16b: the ground lower path sibling at compact index `k` with V bits `gOff k ..` OR-ed into its top `gBits k` bits
(the sign pack routine only ORs; the bits are clear unless the ground search hit its cap). -/
def packG (k : Nat) (d : Digest) (v : Nat) : Digest :=
  BitVec.ofNat 128 (d.toNat ||| v / 2 ^ gOff k % 2 ^ gBits k * 2 ^ (128 - gBits k))
/-- U16b: the ground slots of `s` have their top `gBits k` bits clear (`LowerPathOK`, `groundClear_of_lowerPathOK`). -/
def GroundClear (s : SharedSignature) : Prop :=
  ∀ k, gBits k ≠ 0 → topBits (gBits k) (((sigDigests s).eraseIdx 176).getD k 0) = 0
def encList (s : SharedSignature) : List Digest :=
  (List.range 324).map fun k => if k = 0 then BitVec.ofNat 128 (rhoN s % 2 ^ 128) else if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
    (xField s) else if gBits k = 0 then ((sigDigests s).eraseIdx 176).getD k 0
    else packG k (((sigDigests s).eraseIdx 176).getD k 0) (vField s)
def sigBC (s : SharedSignature) : CBytes :=
  BitVec.ofNat _ (digNat (encList s) + 2 ^ (128 * 324) * (((sigDigests s).getD 176 0).toNat % 2 ^ 16))
theorem compact_length : 324 * 16 + 2 = 5186 := by decide
/-- The normal form a decoded signature has (T51): path tops of heights 1..10 clear (`b_j` bits), top sibling below
bit 99 (R6; E11: 101), hint 13 bits. -/
def normD (k : Nat) (d : Digest) : Digest :=
  if 166 ≤ k ∧ k ≤ 175 then clearTop (topZeroBits (k - 165)) d
  else if k = 176 then BitVec.ofNat 128 (d.toNat % 2 ^ 99)
  else if 177 ≤ k ∧ gBits (k - 1) ≠ 0 then clearTop (gBits (k - 1)) d
  else if k < 166 ∧ gBits k ≠ 0 then clearTop (gBits k) d else d
theorem normD_of_lt (k : Nat) (d : Digest) (hk : k < 166) (hg : gBits k = 0) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => by omega), if_neg (fun h => h.2 hg)]
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

/-- R6 (F4): compact digit `k`: slot 0 holds `N mod 2^128`. -/
theorem encList_getD (s : SharedSignature) (k : Nat) (hk : k < 324) :
    (encList s).getD k 0 = if k = 0 then BitVec.ofNat 128 (rhoN s % 2 ^ 128)
      else if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
      (xField s) else if gBits k = 0 then ((sigDigests s).eraseIdx 176).getD k 0
      else packG k (((sigDigests s).eraseIdx 176).getD k 0) (vField s) := by
  rw [encList, List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_map, List.getElem_range]

/-- Y5: `packH` of an index code `t < 360` is a hint `≤ 7934 < 8192`. -/
theorem packH_le_7934 (t : Nat) (ht : t < 360) : packH t ≤ 7934 := by
  have h1 : t / 90 < 4 := by omega
  have h2 : t / 15 % 6 < 6 := Nat.mod_lt _ (by decide)
  have h3 : t % 15 < 15 := Nat.mod_lt _ (by decide)
  unfold packH hintA1 hintA2 hintA3
  generalize t / 90 = a at *; generalize t / 15 % 6 = b at *; generalize t % 15 = c at *
  split_ifs <;> omega

/-- Y5: every index code `t < 360` re-packs to an in-alphabet hint, and `hintT` inverts `packH` (checked on all 360
codes). -/
theorem packH_table : ∀ t : Fin 360, hintT (packH t.val) = t.val := by decide +kernel

theorem hintT_packH (t : Nat) (ht : t < 360) : hintT (packH t) = t := packH_table ⟨t, ht⟩

theorem hintOK_packH (t : Nat) (ht : t < 360) : HintOK (packH t) := by
  unfold HintOK; rw [hintT_packH t ht]; exact ⟨ht, rfl⟩

/-- R6 (F4), Y5: the canonical bound `R * 360` as a literal (machine `nCanon`). -/
theorem R_mul_360 : R * 360 = 2722258935367507707706996859454145691400 := by decide

/-- R6 (F4): an honest (`RhoHintOK`) signature has a canonical field `N < R * 360`. -/
theorem rhoN_lt (s : SharedSignature) (hr : RhoHintOK s) : rhoN s < R * 360 := by
  obtain ⟨h0, ht, -⟩ := hr
  unfold rhoN
  generalize hintT s.policyHints.toNat = t at *
  generalize s.rho.toNat = r at *
  generalize R = q at *
  omega

theorem sigBC_toNat (s : SharedSignature) :
    (sigBC s).toNat = digNat (encList s) + 2^(128*324)*(((sigDigests s).getD 176 0).toNat%2^16) := by
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 176 0).toNat (show 0<2^16 by positivity))
  simpa only [←pow_add] using hT

theorem encoded_low (s : SharedSignature) : (sigBC s).toNat%2^(128*324)=digNat (encList s) := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_mod _ _ _ hD]

theorem encoded_tail (s : SharedSignature) :
    (sigBC s).toNat/2^(128*324)%2^16=((sigDigests s).getD 176 0).toNat%2^16 := by
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

/-- R6: the level-11 window is 9 bits (`topZeroAlloc`), so the bound is 9 (name kept for downstream users). -/
theorem topZeroBits_le_eight (j : Nat) (hj : j ≤ 11) : topZeroBits j ≤ 9 := by interval_cases j <;> decide

/-- T51: the X bits stored in the top `b_j = topZeroBits j` bits of a packed path node (`b` names `b_j`). -/
theorem pack_facts (j b : Nat) (hj : 1 ≤ j ∧ j ≤ 10) (hb : topZeroBits j = b) (d : Digest) (x : Nat) :
    clearTop b (packD j d x) = clearTop b d ∧ topBits b (packD j d x) = x / 2 ^ xOff j % 2 ^ b := by
  subst hb
  exact pack_gen (topZeroBits j) (by have := topZeroBits_le_eight j (by omega); omega) d (x / 2 ^ xOff j)

theorem xOff_vals : xOff 3 = 0 ∧ xOff 4 = 1 ∧ xOff 5 = 3 ∧ xOff 6 = 6 ∧ xOff 7 = 10 ∧ xOff 8 = 15 ∧ xOff 9 = 21 ∧
    xOff 10 = 28 := by decide

theorem xField_lt (s : SharedSignature) : xField s < 2 ^ 37 := by
  unfold xField
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 66) (show 0 < 2 ^ 33 by positivity)
  have h2 := Nat.mod_lt (rhoN s / 2 ^ 128) (show 0 < 2 ^ 3 by positivity)
  omega

/-- R6 (F4): the X bits stored in the top `b_j` bits of compact path node `165 + j`. -/
theorem topBits_sigBC_path (s : SharedSignature) (j : Nat) (hj : 1 ≤ j ∧ j ≤ 10) :
    topBits (topZeroBits j) (cDig (sigBC s) (165 + j)) = xField s / 2 ^ xOff j % 2 ^ topZeroBits j := by
  rw [cDig_sigBC s _ (by omega), encList_getD s _ (by omega), if_neg (by omega), if_pos (by omega),
    show 165 + j - 165 = j by omega]
  exact (pack_facts j _ hj rfl _ _).2

/-- `x mod 2^(o+g)` splits into `x mod 2^o` and the `g`-bit digit at `o` (digit chains of the X and V fields). -/
theorem mod_two_pow_split (x o g n : Nat) (h : o + g = n) : x % 2 ^ n = x % 2 ^ o + x / 2 ^ o % 2 ^ g * 2 ^ o := by
  subst h; rw [Nat.pow_add, Nat.mod_mul, Nat.mul_comm]

theorem xField_lt36 (s : SharedSignature) : xField s < 2 ^ 36 := by
  unfold xField
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 66) (show 0 < 2 ^ 33 by positivity)
  have h2 := Nat.mod_lt (rhoN s / 2 ^ 128) (show 0 < 2 ^ 3 by positivity)
  omega

theorem xOfB_sigBC (s : SharedSignature) : xOfB (sigBC s) = xField s := by
  have hx := xField_lt36 s
  have e3 : topBits 1 (cDig (sigBC s) 168) = xField s / 2 ^ 0 % 2 ^ 1 := topBits_sigBC_path s 3 (by omega)
  have e4 : topBits 2 (cDig (sigBC s) 169) = xField s / 2 ^ 1 % 2 ^ 2 := topBits_sigBC_path s 4 (by omega)
  have e5 : topBits 3 (cDig (sigBC s) 170) = xField s / 2 ^ 3 % 2 ^ 3 := topBits_sigBC_path s 5 (by omega)
  have e6 : topBits 4 (cDig (sigBC s) 171) = xField s / 2 ^ 6 % 2 ^ 4 := topBits_sigBC_path s 6 (by omega)
  have e7 : topBits 5 (cDig (sigBC s) 172) = xField s / 2 ^ 10 % 2 ^ 5 := topBits_sigBC_path s 7 (by omega)
  have e8 : topBits 6 (cDig (sigBC s) 173) = xField s / 2 ^ 15 % 2 ^ 6 := topBits_sigBC_path s 8 (by omega)
  have e9 : topBits 7 (cDig (sigBC s) 174) = xField s / 2 ^ 21 % 2 ^ 7 := topBits_sigBC_path s 9 (by omega)
  have e10 : topBits 8 (cDig (sigBC s) 175) = xField s / 2 ^ 28 % 2 ^ 8 := topBits_sigBC_path s 10 (by omega)
  unfold xOfB
  rw [e3, e4, e5, e6, e7, e8, e9, e10]
  generalize xField s = x at *
  conv_rhs => rw [← Nat.mod_eq_of_lt hx]
  rw [mod_two_pow_split x 28 8 36 rfl, mod_two_pow_split x 21 7 28 rfl, mod_two_pow_split x 15 6 21 rfl, mod_two_pow_split x 10 5 15 rfl, mod_two_pow_split x 6 4 10 rfl, mod_two_pow_split x 3 3 6 rfl, mod_two_pow_split x 1 2 3 rfl, mod_two_pow_split x 0 1 1 rfl, Nat.pow_zero, Nat.mod_one, Nat.zero_add, Nat.mul_one]

/-- E11: zero bits of the ground slots, at most 4. -/
theorem gBits_le (k : Nat) : gBits k ≤ 4 := by
  unfold gBits; split <;> omega

/-- E8 (P1): the ground slots. -/
def gKeys : List Nat := [225, 224, 223, 222, 274, 273, 272, 271, 323, 322, 321, 320, 11, 23, 36, 48, 61, 73, 86, 98, 111,
  10, 22, 35, 47]

theorem gBits_eq_zero (k : Nat) (hk : k ∉ gKeys) : gBits k = 0 := by
  unfold gKeys at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  unfold gBits; split <;> simp_all

theorem gBits_mem (k : Nat) (h : gBits k ≠ 0) : k ∈ gKeys := by
  by_contra hk; exact h (gBits_eq_zero k hk)

/-- E8 (P1): the ground slots lie below the top path (`< 166`, FTS) or in the lower layers (`> 221`). -/
theorem gBits_range (k : Nat) (h : gBits k ≠ 0) : k < 166 ∨ (221 < k ∧ k < 324) := by
  have := gBits_mem k h
  unfold gKeys at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  omega

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

/-- Y5: V is 50 bits (N7g: 46, R6: 38). -/
theorem vField_lt (s : SharedSignature) : vField s < 2 ^ 50 := by
  unfold vField; exact Nat.mod_lt _ (by positivity)

/-- U16b: the V bits stored in the (clear) top `gBits k` bits of a compact ground slot. -/
theorem topBits_sigBC_ground (s : SharedSignature) (hg : GroundClear s) (k : Nat) (hk : k < 324) (h0 : gBits k ≠ 0) :
    topBits (gBits k) (cDig (sigBC s) k) = vField s / 2 ^ gOff k % 2 ^ gBits k := by
  have hr := gBits_range k h0
  have hk0 : k ≠ 0 := fun h => h0 (by subst h; rfl)
  rw [cDig_sigBC s k hk, encList_getD s k hk, if_neg hk0, if_neg (by omega), if_neg h0, (packG_facts _ _ _).2,
    hg k h0, Nat.zero_or]

theorem vOfB_sigBC (s : SharedSignature) (hg : GroundClear s) : vOfB (sigBC s) = vField s := by
  have hv := vField_lt s
  have e225 : topBits 4 (cDig (sigBC s) 225) = vField s / 2 ^ 0 % 2 ^ 4 :=
    topBits_sigBC_ground s hg 225 (by decide) (by decide)
  have e224 : topBits 3 (cDig (sigBC s) 224) = vField s / 2 ^ 4 % 2 ^ 3 :=
    topBits_sigBC_ground s hg 224 (by decide) (by decide)
  have e223 : topBits 2 (cDig (sigBC s) 223) = vField s / 2 ^ 7 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 223 (by decide) (by decide)
  have e222 : topBits 1 (cDig (sigBC s) 222) = vField s / 2 ^ 9 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 222 (by decide) (by decide)
  have e274 : topBits 4 (cDig (sigBC s) 274) = vField s / 2 ^ 10 % 2 ^ 4 :=
    topBits_sigBC_ground s hg 274 (by decide) (by decide)
  have e273 : topBits 3 (cDig (sigBC s) 273) = vField s / 2 ^ 14 % 2 ^ 3 :=
    topBits_sigBC_ground s hg 273 (by decide) (by decide)
  have e272 : topBits 2 (cDig (sigBC s) 272) = vField s / 2 ^ 17 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 272 (by decide) (by decide)
  have e271 : topBits 1 (cDig (sigBC s) 271) = vField s / 2 ^ 19 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 271 (by decide) (by decide)
  have e323 : topBits 4 (cDig (sigBC s) 323) = vField s / 2 ^ 20 % 2 ^ 4 :=
    topBits_sigBC_ground s hg 323 (by decide) (by decide)
  have e322 : topBits 3 (cDig (sigBC s) 322) = vField s / 2 ^ 24 % 2 ^ 3 :=
    topBits_sigBC_ground s hg 322 (by decide) (by decide)
  have e321 : topBits 2 (cDig (sigBC s) 321) = vField s / 2 ^ 27 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 321 (by decide) (by decide)
  have e320 : topBits 1 (cDig (sigBC s) 320) = vField s / 2 ^ 29 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 320 (by decide) (by decide)
  have e11 : topBits 1 (cDig (sigBC s) 11) = vField s / 2 ^ 30 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 11 (by decide) (by decide)
  have e23 : topBits 1 (cDig (sigBC s) 23) = vField s / 2 ^ 31 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 23 (by decide) (by decide)
  have e36 : topBits 2 (cDig (sigBC s) 36) = vField s / 2 ^ 32 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 36 (by decide) (by decide)
  have e48 : topBits 2 (cDig (sigBC s) 48) = vField s / 2 ^ 34 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 48 (by decide) (by decide)
  have e61 : topBits 2 (cDig (sigBC s) 61) = vField s / 2 ^ 36 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 61 (by decide) (by decide)
  have e73 : topBits 2 (cDig (sigBC s) 73) = vField s / 2 ^ 38 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 73 (by decide) (by decide)
  have e86 : topBits 2 (cDig (sigBC s) 86) = vField s / 2 ^ 40 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 86 (by decide) (by decide)
  have e98 : topBits 2 (cDig (sigBC s) 98) = vField s / 2 ^ 42 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 98 (by decide) (by decide)
  have e111 : topBits 2 (cDig (sigBC s) 111) = vField s / 2 ^ 44 % 2 ^ 2 :=
    topBits_sigBC_ground s hg 111 (by decide) (by decide)
  have e10 : topBits 1 (cDig (sigBC s) 10) = vField s / 2 ^ 46 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 10 (by decide) (by decide)
  have e22 : topBits 1 (cDig (sigBC s) 22) = vField s / 2 ^ 47 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 22 (by decide) (by decide)
  have e35 : topBits 1 (cDig (sigBC s) 35) = vField s / 2 ^ 48 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 35 (by decide) (by decide)
  have e47 : topBits 1 (cDig (sigBC s) 47) = vField s / 2 ^ 49 % 2 ^ 1 :=
    topBits_sigBC_ground s hg 47 (by decide) (by decide)
  unfold vOfB
  rw [e225, e224, e223, e222, e274, e273, e272, e271, e323, e322, e321, e320, e11, e23, e36, e48, e61, e73, e86,
    e98, e111, e10, e22, e35, e47]
  generalize vField s = v at *
  conv_rhs => rw [← Nat.mod_eq_of_lt hv]
  rw [mod_two_pow_split v 49 1 50 rfl, mod_two_pow_split v 48 1 49 rfl, mod_two_pow_split v 47 1 48 rfl,
    mod_two_pow_split v 46 1 47 rfl, mod_two_pow_split v 44 2 46 rfl, mod_two_pow_split v 42 2 44 rfl, mod_two_pow_split v 40 2 42 rfl, mod_two_pow_split v 38 2 40 rfl, mod_two_pow_split v 36 2 38 rfl, mod_two_pow_split v 34 2 36 rfl, mod_two_pow_split v 32 2 34 rfl, mod_two_pow_split v 31 1 32 rfl, mod_two_pow_split v 30 1 31 rfl, mod_two_pow_split v 29 1 30 rfl, mod_two_pow_split v 27 2 29 rfl, mod_two_pow_split v 24 3 27 rfl, mod_two_pow_split v 20 4 24 rfl, mod_two_pow_split v 19 1 20 rfl, mod_two_pow_split v 17 2 19 rfl, mod_two_pow_split v 14 3 17 rfl, mod_two_pow_split v 10 4 14 rfl, mod_two_pow_split v 9 1 10 rfl, mod_two_pow_split v 7 2 9 rfl, mod_two_pow_split v 4 3 7 rfl, mod_two_pow_split v 0 4 4 rfl, Nat.pow_zero, Nat.mod_one, Nat.zero_add]

/-- U16b: the T1 (5,195-byte) compact list: no ground packing. -/
def encListT1 (s : SharedSignature) : List Digest :=
  (List.range 324).map fun k => if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
    (xField s) else ((sigDigests s).eraseIdx 176).getD k 0
/-- E11: the T1 compact bytes (the sign buffer before packing: tail = top sibling bits 0..76). -/
def sigBCT1 (s : SharedSignature) : Bytes 5194 :=
  BitVec.ofNat _ (digNat (encListT1 s) + 2 ^ (128 * 324) * (((sigDigests s).getD 176 0).toNat % 2 ^ 77))

theorem encListT1_length (s : SharedSignature) : (encListT1 s).length = 324 := by simp [encListT1]
theorem encListT1_getD (s : SharedSignature) (k : Nat) (hk : k < 324) :
    (encListT1 s).getD k 0 = if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
      (xField s) else ((sigDigests s).eraseIdx 176).getD k 0 := by
  simp [encListT1, List.getD_eq_getElem?_getD, hk]

theorem sigBCT1_toNat (s : SharedSignature) :
    (sigBCT1 s).toNat = digNat (encListT1 s) + 2^(128*324)*(((sigDigests s).getD 176 0).toNat%2^77) := by
  unfold sigBCT1
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt (encListT1 s)
  rw [encListT1_length] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 176 0).toNat (show 0<2^77 by positivity))
  rw [← pow_add] at hT
  exact lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (by norm_num))

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

/-- E11 / N7g (for the sign pack routine): 64-bit word `2 ≤ k < 650` of the compact bytes is the T1 word `k` with the
V bits OR-ed into the top `gBits` bits of the high word of each ground slot; word 648 keeps only its low 3 bytes (the
tail; N7g B) and word 649 is empty (T1 bits 24..69 of the top sibling = V move into the ground slots). Words 0, 1
(slot 0) hold `N mod 2^128` (R6, `encList_getD`). -/
theorem sigBC_word (s : SharedSignature) (k : Nat) (hk2 : 2 ≤ k) (hk : k < 650) :
    (sigBC s).toNat / 2 ^ (64 * k) % 2 ^ 64 =
      if k = 649 then (sigBCT1 s).toNat / 2 ^ (64 * k) % 2 ^ 0
      else if k = 648 then (sigBCT1 s).toNat / 2 ^ (64 * k) % 2 ^ 64 % 2 ^ 16
      else (sigBCT1 s).toNat / 2 ^ (64 * k) % 2 ^ 64 |||
        (if k % 2 = 1 ∧ gBits (k / 2) ≠ 0 then vField s / 2 ^ gOff (k / 2) % 2 ^ gBits (k / 2) * 2 ^ (64 - gBits (k / 2))
          else 0) := by
  rw [sigBC_toNat, sigBCT1_toNat]
  by_cases hlo : k < 648
  · rw [if_neg (by omega), if_neg (by omega), word_digits _ (encList_length s) _ _ hlo,
      word_digits _ (encListT1_length s) _ _ hlo, encList_getD s _ (by omega), encListT1_getD s _ (by omega),
      if_neg (show ¬ (k / 2 = 0) by omega)]
    by_cases hp : 166 ≤ k / 2 ∧ k / 2 ≤ 175
    · have hg : gBits (k / 2) = 0 := by
        by_contra hg; have := gBits_range _ hg; omega
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
      have h0 := word_tail _ (x % 2 ^ 16) hD 0 (by decide)
      have h1 := word_tail _ (x % 2 ^ 77) hD1 0 (by decide)
      simp only [Nat.add_zero, Nat.mul_zero, pow_zero, Nat.div_one] at h0 h1
      rw [h0, h1, if_neg (by decide), if_pos rfl,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 16 ≤ 64)),
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 16 ≤ 77))]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    · have h9 : k = 649 := by omega
      subst h9
      have h0 := word_tail _ (x % 2 ^ 16) hD 1 (by decide)
      have h1 := word_tail _ (x % 2 ^ 77) hD1 1 (by decide)
      simp only [Nat.mul_one] at h0 h1
      rw [show 64 * 649 = 64 * (648 + 1) by rfl, h0, h1, if_pos rfl]
      have : x % 2 ^ 16 / 2 ^ 64 = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt x (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
      simp only [pow_zero, Nat.mod_one, this, Nat.zero_mod]

/-- N7g (B), Y5 (V50): V = bits 16..63 of T1 word 648 and bits 0..1 of T1 word 649 (top sibling bits 16..65). -/
theorem vField_sigBCT1 (s : SharedSignature) :
    vField s = ((sigBCT1 s).toNat / 2 ^ (64 * 648) % 2 ^ 64 / 2 ^ 16 +
      (sigBCT1 s).toNat / 2 ^ (64 * 649) % 2 ^ 64 * 2 ^ 48) % 2 ^ 50 := by
  have hD1 := digNat_lt (encListT1 s)
  rw [encListT1_length] at hD1
  have h0 := word_tail _ (((sigDigests s).getD 176 0).toNat % 2 ^ 77) hD1 0 (by decide)
  have h1 := word_tail _ (((sigDigests s).getD 176 0).toNat % 2 ^ 77) hD1 1 (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mul_one] at h0 h1
  rw [sigBCT1_toNat, h0, show 64 * 649 = 64 * (648 + 1) by rfl, h1]
  unfold vField
  generalize ((sigDigests s).getD 176 0).toNat = x
  simp only [Nat.reducePow, Nat.reduceMul]
  omega

/-- R6 (F4): the compact field of an encoded signature is `N mod 2^131` (slot 0 plus X bits 29..35). -/
theorem nOfB_sigBC (s : SharedSignature) : nOfB (sigBC s) = rhoN s % 2 ^ 131 := by
  unfold nOfB
  rw [xOfB_sigBC, cDig_sigBC s 0 (by decide), encList_getD s 0 (by decide), if_pos rfl, BitVec.toNat_ofNat,
    Nat.mod_mod]
  unfold xField
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 66) (show 0 < 2 ^ 33 by positivity)
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt h1, Nat.zero_add,
    show (2:Nat) ^ 131 = 2 ^ 128 * 2 ^ 3 by norm_num, Nat.mod_mul, Nat.mul_comm (2 ^ 128)]

theorem nOfB_sigBC_of (s : SharedSignature) (hr : RhoHintOK s) : nOfB (sigBC s) = rhoN s := by
  rw [nOfB_sigBC, Nat.mod_eq_of_lt (lt_trans (rhoN_lt s hr) R_mul_lt)]

/-- R6 (F4): honest encodings are canonical (`N < R * 360`), so DEC never rejects them. -/
theorem nOfB_sigBC_lt (s : SharedSignature) (hr : RhoHintOK s) : nOfB (sigBC s) < R * 360 := by
  have h := rhoN_lt s hr
  rwa [← nOfB_sigBC_of s hr] at h

/-- R6 (F4): the round trip of one digest. Slot 0 (`rho`) needs `RhoHintOK`, the top sibling clear ground slots. -/
theorem digC_sigBC (s : SharedSignature) (k : Nat) (hk : k<325) (hg : k ≠ 176 ∨ GroundClear s)
    (hr : k ≠ 0 ∨ RhoHintOK s) :
    digC (sigBC s) k = normD k ((sigDigests s).getD k 0) := by
  by_cases h0 : k = 0
  · subst h0
    have hr' := hr.resolve_left (by decide)
    rw [normD_of_lt _ _ (by decide) rfl, sigDigests_rho, digC, if_pos rfl, nOfB_sigBC_of s hr']
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    obtain ⟨-, ht, -⟩ := hr'
    unfold rhoN
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt ht, Nat.zero_add,
      Nat.mod_eq_of_lt s.rho.isLt]
  by_cases hlt : k<176
  · rw [digC, if_neg h0, if_pos hlt, cDig_sigBC s k (by omega), encList_getD s k (by omega), if_neg h0,
      getD_eraseIdx, if_pos hlt]
    by_cases hp : 166 ≤ k
    · rw [if_pos hp, if_pos ⟨hp, by omega⟩, (pack_facts _ _ ⟨by omega, by omega⟩ rfl _ _).1, normD,
        if_pos ⟨hp, by omega⟩]
    · rw [if_neg hp, if_neg (show ¬ (166 ≤ k ∧ k ≤ 175) by omega)]
      by_cases hg0 : gBits k = 0
      · rw [if_pos hg0, if_pos hg0, normD_of_lt _ _ (by omega) hg0]
      · rw [if_neg hg0, if_neg hg0, (packG_facts _ _ _).1, normD, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos ⟨by omega, hg0⟩]
  · by_cases he : k=176
    · subst he
      rw [digC, if_neg (by decide), if_neg (by decide), if_pos rfl, encoded_tail,
        vOfB_sigBC s (hg.resolve_left (by decide)), xOfB_sigBC, normD, if_neg (by decide), if_pos rfl]
      congr 1
      unfold xField vField
      have hq := Nat.mod_lt (rhoN s / 2 ^ 128) (show 0 < 2 ^ 3 by positivity)
      generalize rhoN s / 2 ^ 128 % 2 ^ 3 = q at *
      generalize ((sigDigests s).getD 176 0).toNat = x
      have h70 : x % 2 ^ 66 = x % 2 ^ 16 + 2 ^ 16 * (x / 2 ^ 16 % 2 ^ 50) := by
        rw [show (2:Nat) ^ 66 = 2 ^ 16 * 2 ^ 50 by norm_num, Nat.mod_mul]
      have hm : x % 2 ^ 99 = x % 2 ^ 66 + 2 ^ 66 * (x / 2 ^ 66 % 2 ^ 33) := by
        rw [show (2:Nat) ^ 99 = 2 ^ 66 * 2 ^ 33 by norm_num, Nat.mod_mul]
      have h29 := Nat.mod_lt (x / 2 ^ 66) (show 0 < 2 ^ 33 by positivity)
      rw [hm, h70, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h29]
      ring
    · have hg' : ¬ (166 ≤ k-1 ∧ k-1 ≤ 175) := by omega
      have he' : ¬ (k-1 < 176) := by omega
      have h0' : k - 1 ≠ 0 := by omega
      by_cases hg : gBits (k-1) = 0
      · rw [digC, if_neg h0, if_neg hlt, if_neg he, if_pos hg, cDig_sigBC s (k-1) (by omega),
          encList_getD s _ (by omega), if_neg h0', if_neg hg', if_pos hg, getD_eraseIdx, if_neg he',
          show k-1+1=k by omega, normD, if_neg (by omega), if_neg he, if_neg (fun h => h.2 hg), if_neg (by omega)]
      · rw [digC, if_neg h0, if_neg hlt, if_neg he, if_neg hg, cDig_sigBC s (k-1) (by omega),
          encList_getD s _ (by omega), if_neg h0', if_neg hg', if_neg hg, (packG_facts _ _ _).1, getD_eraseIdx,
          if_neg he', show k-1+1=k by omega, normD, if_neg (by omega), if_neg he, if_pos ⟨by omega, hg⟩]

/-- R6 (F4), Y5: an honest hint survives the codec (`h ≤ 7934 < 2^13`, so the 13-bit cut is the identity). -/
theorem policyHints_sigDecC_sigBC (s : SharedSignature) (hr : RhoHintOK s) :
    (sigDecC (sigBC s)).policyHints = BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13) := by
  change BitVec.ofNat 16 (hintOfN (nOfB (sigBC s))) = _
  have hn := rhoN_lt s hr
  rw [nOfB_sigBC_of s hr, hintOfN, if_pos hn]
  obtain ⟨-, ht, hp⟩ := hr
  have hle := packH_le_7934 _ ht
  rw [hp] at hle
  unfold rhoN
  rw [Nat.mul_add_mod_of_lt ht, hp,
    Nat.mod_eq_of_lt (show s.policyHints.toNat < 2 ^ 13 by rw [show (2:Nat) ^ 13 = 8192 by norm_num]; omega)]

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (getD_append_left' getD_append_right' getD_ofFn')
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem clearTop_of_topBits (g : Nat) (hg : g ≤ 128) (d : Digest) (h : topBits g d = 0) : clearTop g d = d := by
  apply BitVec.eq_of_toNat_eq
  unfold clearTop
  unfold topBits at h
  have hlt : d.toNat < 2 ^ (128 - g) := by
    rcases Nat.lt_or_ge d.toNat (2 ^ (128 - g)) with h' | h'
    · exact h'
    · exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.div_pos h' (by positivity)))
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt d.isLt]

/-- E8 (P1): below the top path the normal form only clears ground slots, which `GroundClear` keeps clear. -/
theorem normD_forest (s : SharedSignature) (hg : GroundClear s) (k : Nat) (hk : k < 166) :
    normD k ((sigDigests s).getD k 0) = (sigDigests s).getD k 0 := by
  by_cases h0 : gBits k = 0
  · exact normD_of_lt _ _ hk h0
  · unfold normD
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hk, h0⟩]
    apply clearTop_of_topBits _ (by have := gBits_le k; omega)
    have := hg k h0
    rwa [getD_eraseIdx, if_pos (by omega)] at this

theorem forest_sigDecC_sigBC (s : SharedSignature) (hg : GroundClear s) :
    (sigDecC (sigBC s)).forest=s.forest := by
  have hp : (sigDecC (sigBC s)).forest.pairs=s.forest.pairs := by
    funext p
    have h1 : ((sigDecC (sigBC s)).forest.pairs p).firstValues=(s.forest.pairs p).firstValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),normD_forest s hg _ (by omega),sigDigests_pair s p i.val (by omega),pairList_firstValue]
    have h2 : ((sigDecC (sigBC s)).forest.pairs p).firstPath=(s.forest.pairs p).firstPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+6+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),normD_forest s hg _ (by omega),show 1+25*p.val+6+i.val=1+25*p.val+(6+i.val) by omega,
        sigDigests_pair s p (6+i.val) (by omega),pairList_firstPath]
    have h3 : ((sigDecC (sigBC s)).forest.pairs p).secondValues=(s.forest.pairs p).secondValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+12+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),normD_forest s hg _ (by omega),show 1+25*p.val+12+i.val=1+25*p.val+(12+i.val) by omega,
        sigDigests_pair s p (12+i.val) (by omega),pairList_secondValue]
    have h4 : ((sigDecC (sigBC s)).forest.pairs p).secondPath=(s.forest.pairs p).secondPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+18+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),normD_forest s hg _ (by omega),show 1+25*p.val+18+i.val=1+25*p.val+(18+i.val) by omega,
        sigDigests_pair s p (18+i.val) (by omega),pairList_secondPath]
    cases h : (sigDecC (sigBC s)).forest.pairs p
    cases h' : s.forest.pairs p
    simp only [h,h'] at h1 h2 h3 h4
    cases h1;cases h2;cases h3;cases h4;rfl
  have hs : (sigDecC (sigBC s)).forest.singleton=s.forest.singleton := by
    have h1 : (sigDecC (sigBC s)).forest.singleton.values=s.forest.singleton.values := by
      funext i
      change digC (sigBC s) (101+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),normD_forest s hg _ (by omega),sigDigests_singleton s i.val (by omega),singletonList,
        getD_append_left' (by simp),getD_ofFn']
    have h2 : (sigDecC (sigBC s)).forest.singleton.path=s.forest.singleton.path := by
      funext i
      change digC (sigBC s) (107+i.val)=_
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),normD_forest s hg _ (by omega),show 107+i.val=101+(6+i.val) by omega,
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

theorem normD_of_out (k : Nat) (d : Digest) (hk : (k < 166 ∧ gBits k = 0) ∨ (176 < k ∧ gBits (k - 1) = 0)) :
    normD k d = d := by
  unfold normD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by rintro ⟨h1, h2⟩; rcases hk with hk | hk <;> [omega; exact h2 hk.2]),
    if_neg (by rintro ⟨h1, h2⟩; rcases hk with hk | hk <;> [exact h2 hk.2; omega])]

/-- R6 (F4): the codec round trip, on clear ground slots and an honest rho/hint range (`RhoHintOK`). -/
theorem sigDecC_sigBC (s : SharedSignature) (hg : GroundClear s) (hr0 : RhoHintOK s) :
    sigDecC (sigBC s) = normalizeV6 s := by
  have hr : (sigDecC (sigBC s)).rho=s.rho := by
    change digC (sigBC s) 0=s.rho
    rw [digC_sigBC s 0 (by decide) (Or.inl (by decide)) (Or.inr hr0),normD_of_lt _ _ (by decide) rfl,sigDigests_rho]
  have hh := policyHints_sigDecC_sigBC s hr0
  have hf := forest_sigDecC_sigBC s hg
  have hl : (sigDecC (sigBC s)).layers=(normalizeV6 s).layers := by
    funext lay
    have hli : 114≤layIdx lay := by fin_cases lay <;> decide
    have hc : layIdx lay+chainCount lay≤325 := by fin_cases lay <;> decide
    have hp : layIdx lay+chainCount lay+height lay≤325 := by fin_cases lay <;> decide
    have hv : ((sigDecC (sigBC s)).layers lay).values=((normalizeV6 s).layers lay).values := by
      funext i
      change digC (sigBC s) (layIdx lay+i.val)=(s.layers lay).values i
      have hn : (layIdx lay+i.val < 166 ∧ gBits (layIdx lay+i.val) = 0) ∨
          (176 < layIdx lay+i.val ∧ gBits (layIdx lay+i.val-1) = 0) := by
        have h1 : (114 ≤ layIdx lay+i.val ∧ layIdx lay+i.val < 166) ∨ (176 < layIdx lay+i.val ∧
            (layIdx lay+i.val-1 < 222 ∨ (225 < layIdx lay+i.val-1 ∧ layIdx lay+i.val-1 < 271) ∨
              (274 < layIdx lay+i.val-1 ∧ layIdx lay+i.val-1 < 320) ∨ 323 < layIdx lay+i.val-1)) := by
          fin_cases lay <;> simp [layIdx,chainCount] at * <;> omega
        rcases h1 with h | ⟨h, h'⟩
        · exact Or.inl ⟨h.2, gBits_eq_zero _ (by simp [gKeys]; omega)⟩
        · exact Or.inr ⟨h, gBits_eq_zero _ (by simp [gKeys]; omega)⟩
      rw [digC_sigBC s _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),normD_of_out _ _ hn,sigDigests_layValue]
    have hpath : ((sigDecC (sigBC s)).layers lay).path=((normalizeV6 s).layers lay).path := by
      funext i
      change digC (sigBC s) (layIdx lay+chainCount lay+i.val) =
        normD (layIdx lay + chainCount lay + i.val) ((s.layers lay).path i)
      rw [digC_sigBC s _ (by omega) (Or.inr hg) (Or.inl (by omega)), show layIdx lay+chainCount lay+i.val=layIdx lay+(chainCount lay+i.val) by omega,
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
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 2 (by norm_num) (cDig b 169)
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
      | (rw [o3, show topZeroBits 3 = 1 from rfl]; norm_num at *; omega)
      | (rw [o4, show topZeroBits 4 = 2 from rfl]; norm_num at *; omega)
      | (rw [o5, show topZeroBits 5 = 3 from rfl]; norm_num at *; omega)
      | (rw [o6, show topZeroBits 6 = 4 from rfl]; norm_num at *; omega)
      | (rw [o7, show topZeroBits 7 = 5 from rfl]; norm_num at *; omega)
      | (rw [o8, show topZeroBits 8 = 6 from rfl]; norm_num at *; omega)
      | (rw [o9, show topZeroBits 9 = 7 from rfl]; norm_num at *; omega)
      | (rw [o10, show topZeroBits 10 = 8 from rfl]; norm_num at *; omega)

/-- R6 (F4): X is 36 bits. -/
theorem xOfB_lt36 (b : CBytes) : xOfB b < 2 ^ 36 := by
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 2 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 3 (by norm_num) (cDig b 170); have t6 := topBits_lt 4 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 5 (by norm_num) (cDig b 172); have t8 := topBits_lt 6 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 7 (by norm_num) (cDig b 174); have t10 := topBits_lt 8 (by norm_num) (cDig b 175)
  unfold xOfB
  norm_num at *
  omega

theorem xOfB_lt (b : CBytes) : xOfB b < 2 ^ 37 := lt_trans (xOfB_lt36 b) (by norm_num)

theorem gBits_ne_zero (k : Nat) (h : gBits k ≠ 0) :
    k = 225 ∨ k = 224 ∨ k = 223 ∨ k = 222 ∨ k = 274 ∨ k = 273 ∨ k = 272 ∨ k = 271 ∨ k = 323 ∨ k = 322 ∨ k = 321 ∨ k = 320 ∨ k = 11 ∨ k = 23 ∨ k = 36 ∨ k = 48 ∨ k = 61 ∨ k = 73 ∨ k = 86 ∨ k = 98 ∨ k = 111 ∨
      k = 10 ∨ k = 22 ∨ k = 35 ∨ k = 47 := by
  have := gBits_mem k h
  simpa only [gKeys, List.mem_cons, List.not_mem_nil, or_false] using this

theorem vOfB_digit (b : CBytes) (k : Nat) (hk : gBits k ≠ 0) :
    vOfB b / 2 ^ gOff k % 2 ^ gBits k = topBits (gBits k) (cDig b k) := by
  have t0 := topBits_lt 4 (by norm_num) (cDig b 225)
  have t1 := topBits_lt 3 (by norm_num) (cDig b 224)
  have t2 := topBits_lt 2 (by norm_num) (cDig b 223)
  have t3 := topBits_lt 1 (by norm_num) (cDig b 222)
  have t4 := topBits_lt 4 (by norm_num) (cDig b 274)
  have t5 := topBits_lt 3 (by norm_num) (cDig b 273)
  have t6 := topBits_lt 2 (by norm_num) (cDig b 272)
  have t7 := topBits_lt 1 (by norm_num) (cDig b 271)
  have t8 := topBits_lt 4 (by norm_num) (cDig b 323)
  have t9 := topBits_lt 3 (by norm_num) (cDig b 322)
  have t10 := topBits_lt 2 (by norm_num) (cDig b 321)
  have t11 := topBits_lt 1 (by norm_num) (cDig b 320)
  have t12 := topBits_lt 1 (by norm_num) (cDig b 11)
  have t13 := topBits_lt 1 (by norm_num) (cDig b 23)
  have t14 := topBits_lt 2 (by norm_num) (cDig b 36)
  have t15 := topBits_lt 2 (by norm_num) (cDig b 48)
  have t16 := topBits_lt 2 (by norm_num) (cDig b 61)
  have t17 := topBits_lt 2 (by norm_num) (cDig b 73)
  have t18 := topBits_lt 2 (by norm_num) (cDig b 86)
  have t19 := topBits_lt 2 (by norm_num) (cDig b 98)
  have t20 := topBits_lt 2 (by norm_num) (cDig b 111)
  have t21 := topBits_lt 1 (by norm_num) (cDig b 10)
  have t22 := topBits_lt 1 (by norm_num) (cDig b 22)
  have t23 := topBits_lt 1 (by norm_num) (cDig b 35)
  have t24 := topBits_lt 1 (by norm_num) (cDig b 47)
  unfold vOfB
  rcases gBits_ne_zero k hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [gBits, gOff, Nat.reducePow] at * <;> omega

/-- Y5: V is 50 bits. -/
theorem vOfB_lt (b : CBytes) : vOfB b < 2 ^ 50 := by
  have t0 := topBits_lt 4 (by norm_num) (cDig b 225)
  have t1 := topBits_lt 3 (by norm_num) (cDig b 224)
  have t2 := topBits_lt 2 (by norm_num) (cDig b 223)
  have t3 := topBits_lt 1 (by norm_num) (cDig b 222)
  have t4 := topBits_lt 4 (by norm_num) (cDig b 274)
  have t5 := topBits_lt 3 (by norm_num) (cDig b 273)
  have t6 := topBits_lt 2 (by norm_num) (cDig b 272)
  have t7 := topBits_lt 1 (by norm_num) (cDig b 271)
  have t8 := topBits_lt 4 (by norm_num) (cDig b 323)
  have t9 := topBits_lt 3 (by norm_num) (cDig b 322)
  have t10 := topBits_lt 2 (by norm_num) (cDig b 321)
  have t11 := topBits_lt 1 (by norm_num) (cDig b 320)
  have t12 := topBits_lt 1 (by norm_num) (cDig b 11)
  have t13 := topBits_lt 1 (by norm_num) (cDig b 23)
  have t14 := topBits_lt 2 (by norm_num) (cDig b 36)
  have t15 := topBits_lt 2 (by norm_num) (cDig b 48)
  have t16 := topBits_lt 2 (by norm_num) (cDig b 61)
  have t17 := topBits_lt 2 (by norm_num) (cDig b 73)
  have t18 := topBits_lt 2 (by norm_num) (cDig b 86)
  have t19 := topBits_lt 2 (by norm_num) (cDig b 98)
  have t20 := topBits_lt 2 (by norm_num) (cDig b 111)
  have t21 := topBits_lt 1 (by norm_num) (cDig b 10)
  have t22 := topBits_lt 1 (by norm_num) (cDig b 22)
  have t23 := topBits_lt 1 (by norm_num) (cDig b 35)
  have t24 := topBits_lt 1 (by norm_num) (cDig b 47)
  unfold vOfB
  simp only [Nat.reducePow] at *
  omega

/-- N7g (B): the decoded top sibling: tail (24 bits) + V (bits 24..69) + X bits 0..28 (bits 70..98). -/
theorem digC_176_toNat (b : CBytes) : (digC b 176).toNat =
    b.toNat / 2 ^ (128 * 324) % 2 ^ 16 + vOfB b * 2 ^ 16 + xOfB b % 2 ^ 33 * 2 ^ 66 := by
  rw [digC, if_neg (by decide), if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 16 by positivity)
  have h2 := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 33 by positivity)
  have h3 := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 16 = t at *
  generalize xOfB b % 2 ^ 33 = x at *
  generalize vOfB b = v at *
  simp only [Nat.reducePow] at *
  omega

theorem vField_sigDecC (b : CBytes) : vField (sigDecC b) = vOfB b := by
  unfold vField
  rw [sigDigests_sigDecC b 176 (by decide), digC_176_toNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 16 by positivity)
  have h3 := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 16 = t at *
  generalize xOfB b % 2 ^ 33 = x at *
  generalize vOfB b = v at *
  simp only [Nat.reducePow] at *
  omega

/-- R6 (F4): the compact field is below `2^131` (slot 0 plus 7 X bits). -/
theorem nOfB_lt_pow131 (b : CBytes) : nOfB b < 2 ^ 131 := by
  have h0 := (cDig b 0).isLt
  have hx := xOfB_lt36 b
  unfold nOfB
  generalize (cDig b 0).toNat = c at *
  generalize xOfB b = x at *
  simp only [Nat.reducePow] at *
  omega

/-- N7g: the decoded hint word fits 16 bits (`packH ≤ 7934`; non-canonical `8192 + N % 360 < 13596`). -/
theorem hintOfN_lt (n : Nat) : hintOfN n < 2 ^ 16 := by
  have := Nat.mod_lt n (show 0 < 360 by decide)
  unfold hintOfN
  split_ifs
  · have := packH_le_7934 _ this; omega
  · omega

theorem hintT_hintOfN (n : Nat) : hintT (hintOfN n) = n % 360 := by
  have hm := Nat.mod_lt n (show 0 < 360 by decide)
  unfold hintOfN
  split_ifs
  · exact hintT_packH _ hm
  · unfold hintT; rw [if_neg (by omega)]; omega

/-- R6 (F4) / N7g: the decoded signature's field `rho * 360 + hintT h` is the compact field `N` (canonical or not). -/
theorem rhoN_sigDecC (b : CBytes) : rhoN (sigDecC b) = nOfB b := by
  have hn := nOfB_lt_pow131 b
  unfold rhoN
  change (BitVec.ofNat 128 (nOfB b / 360)).toNat * 360 + hintT (BitVec.ofNat 16 (hintOfN (nOfB b))).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hintOfN_lt _), hintT_hintOfN]
  generalize nOfB b = n at *
  have hq : n / 360 < 2 ^ 128 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    exact lt_of_lt_of_le hn (by norm_num)
  rw [Nat.mod_eq_of_lt hq, Nat.mul_comm]
  exact Nat.div_add_mod n 360

theorem xField_sigDecC (b : CBytes) : xField (sigDecC b) = xOfB b := by
  have hx := xOfB_lt36 b
  have h0 := (cDig b 0).isLt
  unfold xField
  rw [sigDigests_sigDecC b 176 (by decide), digC_176_toNat, rhoN_sigDecC]
  unfold nOfB
  have ht := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 16 by positivity)
  have hv := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 16 = t at *
  generalize vOfB b = v at *
  generalize (cDig b 0).toNat = c at *
  generalize xOfB b = x at *
  simp only [Nat.reducePow] at *
  omega

/-- R6 (F1, F4): canonical compact bytes (`N < R * 360`; DEC rejects the rest) decode to an honest-range signature
(`rho = N / 360 < R`, hint digits in range by `packH_range`). -/
theorem rhoHintOK_sigDecC (b : CBytes) (hc : nOfB b < R * 360) : RhoHintOK (sigDecC b) := by
  have hm := Nat.mod_lt (nOfB b) (show 0 < 360 by decide)
  have hp : (sigDecC b).policyHints.toNat = packH (nOfB b % 360) := by
    change (BitVec.ofNat 16 (hintOfN (nOfB b))).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hintOfN_lt _), hintOfN, if_pos hc]
  have hr : (sigDecC b).rho.toNat = nOfB b / 360 := by
    change (BitVec.ofNat 128 (nOfB b / 360)).toNat = _
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have := nOfB_lt_pow131 b
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    exact lt_of_lt_of_le this (by norm_num)
  unfold RhoHintOK
  refine ⟨?_, ?_⟩
  · rw [hr, Nat.div_lt_iff_lt_mul (by norm_num)]; exact hc
  · rw [hp]; exact hintOK_packH _ hm

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

/-- R6 (F4): every compact byte string is the encoding of its decoding (canonical or not). -/
theorem sigBC_sigDecC (b : CBytes) : sigBC (sigDecC b)=b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigBC_toNat]
  have hD : digNat (encList (sigDecC b))=b.toNat%2^(128*324) := by
    apply digNat_eq_of_digits
    · rw [encList_length];exact Nat.mod_lt _ (by positivity)
    · intro k hk
      rw [encList_length] at hk
      rw [mod_digit _ 324 k hk, encList_getD _ k hk]
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos rfl, BitVec.toNat_ofNat, Nat.mod_mod, rhoN_sigDecC, nOfB, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (cDig b 0).isLt, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      rw [if_neg hk0, getD_eraseIdx]
      by_cases hp : 166 ≤ k ∧ k ≤ 175
      · rw [if_pos hp, if_pos (by omega), sigDigests_sigDecC b k (by omega), xField_sigDecC]
        have hj : 1 ≤ k - 165 ∧ k - 165 ≤ 10 := by omega
        have hdig := xOfB_digit b (k - 165) hj.1 hj.2
        rw [show 165 + (k - 165) = k by omega] at hdig
        have hc : digC b k = clearTop (topZeroBits (k - 165)) (cDig b k) := by
          rw [digC, if_neg hk0, if_pos (by omega), if_pos (by omega)]
        rw [hc, packD_clear _ hj _ _ hdig, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      · rw [if_neg hp]
        by_cases hlt : k < 176
        · have hk166 : k < 166 := by omega
          by_cases hg : gBits k = 0
          · rw [if_pos hg, if_pos hlt, sigDigests_sigDecC b k (by omega), digC, if_neg hk0, if_pos hlt,
              if_neg (show ¬ (166 ≤ k) by omega), if_pos hg, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
          · rw [if_neg hg, if_pos hlt, sigDigests_sigDecC b k (by omega), digC, if_neg hk0, if_pos hlt,
              if_neg (show ¬ (166 ≤ k) by omega), if_neg hg, vField_sigDecC, packG_clear k _ _ (vOfB_digit b k hg),
              cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
        · by_cases hg : gBits k = 0
          · rw [if_pos hg, if_neg hlt, sigDigests_sigDecC b (k+1) (by omega), digC, if_neg (by omega),
              if_neg (show ¬ (k+1 < 176) by omega), if_neg (show ¬ (k+1 = 176) by omega), show k+1-1=k by omega,
              if_pos hg, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
          · rw [if_neg hg, if_neg hlt, sigDigests_sigDecC b (k+1) (by omega), digC, if_neg (by omega),
              if_neg (show ¬ (k+1 < 176) by omega), if_neg (show ¬ (k+1 = 176) by omega), show k+1-1=k by omega,
              if_neg hg, vField_sigDecC, packG_clear k _ _ (vOfB_digit b k hg), cDig, BitVec.extractLsb'_toNat,
              Nat.shiftRight_eq_div_pow]
  have hT : ((sigDigests (sigDecC b)).getD 176 0).toNat%2^16=b.toNat/2^(128*324)%2^16 := by
    rw [sigDigests_sigDecC b 176 (by decide), digC_176_toNat]
    rw [show b.toNat / 2 ^ (128 * 324) % 2 ^ 16 + vOfB b * 2 ^ 16 + xOfB b % 2 ^ 33 * 2 ^ 66 =
      b.toNat / 2 ^ (128 * 324) % 2 ^ 16 + (vOfB b + xOfB b % 2 ^ 33 * 2 ^ 50) * 2 ^ 16 by ring,
      Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [hD,hT]
  have hb : b.toNat / 2 ^ (128 * 324) < 2 ^ 16 := by
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
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 99 ≤ 108)),
      show c % 2 ^ 20 * 2 ^ 108 % 2 ^ 99 = 0 from
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

/-- The compact bytes ignore the brute-forced top sibling bits 108..127 (unconditional; U16b: proved directly, the
round trip now needs clear ground slots). -/
theorem sigBC_fillTopSignature (sig : SharedSignature) (c : Nat) :
    sigBC (fillTopSignature sig c) = sigBC sig := by
  have h176 : 176 < (sigDigests sig).length := by rw [sigDigests_length]; decide
  have hd : (sigDigests sig).getD 176 0 = (sig.layers 0).path ClaudeWCT.WCT9.topJ := by
    have := sigDigests_layPath sig 0 11 (by decide)
    exact this
  have hx : ∀ x : Nat, ∀ y : Nat, (x % 2 ^ 108 + y % 2 ^ 20 * 2 ^ 108) % 2 ^ 99 = x % 2 ^ 99 := by
    intro x y
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 99 ≤ 108)),
      show y % 2 ^ 20 * 2 ^ 108 % 2 ^ 99 = 0 from
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]
  have hm : ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat % 2 ^ 99 =
      ((sigDigests sig).getD 176 0).toNat % 2 ^ 99 := by
    rw [sigDigests_fill, List.getD_eq_getElem _ _ (by rw [List.length_set]; exact h176), List.getElem_set_self,
      ClaudeWCT.WCT9.setTop_toNat, hx, hd]
  have ev : ∀ x : Nat, x / 2 ^ 16 % 2 ^ 50 = x % 2 ^ 99 % 2 ^ 66 / 2 ^ 16 := fun x => by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 66 ≤ 99)), ← Nat.mod_mul_right_div_self,
      show (2:Nat) ^ 16 * 2 ^ 50 = 2 ^ 66 by norm_num]
  have ex : ∀ x : Nat, x / 2 ^ 66 % 2 ^ 33 = x % 2 ^ 99 / 2 ^ 66 := fun x => by
    rw [← Nat.mod_mul_right_div_self, show (2:Nat) ^ 66 * 2 ^ 33 = 2 ^ 99 by norm_num]
  have et : ∀ x : Nat, x % 2 ^ 16 = x % 2 ^ 99 % 2 ^ 16 := fun x => by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 16 ≤ 99))]
  have hn : rhoN (fillTopSignature sig c) = rhoN sig := rfl
  have hv : vField (fillTopSignature sig c) = vField sig := by
    unfold vField
    rw [ev ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat, ev ((sigDigests sig).getD 176 0).toNat, hm]
  have hxf : xField (fillTopSignature sig c) = xField sig := by
    unfold xField
    rw [ex ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat, ex ((sigDigests sig).getD 176 0).toNat, hm, hn]
  have ht : ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat % 2 ^ 16 =
      ((sigDigests sig).getD 176 0).toNat % 2 ^ 16 := by
    rw [et ((sigDigests (fillTopSignature sig c)).getD 176 0).toNat, et ((sigDigests sig).getD 176 0).toNat, hm]
  have he : (sigDigests (fillTopSignature sig c)).eraseIdx 176 = (sigDigests sig).eraseIdx 176 := by
    rw [sigDigests_fill, List.eraseIdx_set_eq]
  unfold sigBC encList
  rw [he, hv, hxf, ht, hn]


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
    have hg165 : gBits (165 + j.val) = 0 := gBits_eq_zero _ (by simp [gKeys]; omega)
    unfold normD normPathD clearTop
    rw [show 165 + j.val - 165 = j.val by omega, hg165]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [if_neg h0]
    have hg := gBits_lowerPath lay j h0
    have := layIdx_ge lay h0
    unfold normD normLowerPathD clearTop
    rw [if_neg (by omega), if_neg (by omega), hg]
    by_cases hz : lowerPathBits lay j.val = 0
    · rw [if_neg (fun h => h.2 hz), if_neg (by omega), if_pos hz]
    · rw [if_pos ⟨by omega, hz⟩, if_neg hz]

/-- E8 (P1): the FTS ground slots (the level-4 auth siblings, compact `< 166`) of `s` have clear top bits. -/
def FtsSlotsClear (s : SharedSignature) : Prop :=
  ∀ k, k < 166 → gBits k ≠ 0 → topBits (gBits k) ((sigDigests s).getD k 0) = 0

/-- E8 (P1): FTS width of coordinate `c`'s level-4 sibling (1 on coordinates 0, 1; 2 on 2..8). -/
def ftsSlotBits (c : Nat) : Nat := if c ≤ 1 then 1 else 2
/-- Y5: FTS width of coordinate `c`'s level-5 sibling (heap 16..31): 1 on coordinates 0..3. -/
def ftsSlotBits16 (c : Nat) : Nat := if c < 4 then 1 else 0

/-- E8 (P1): the FTS slots are clear when every opened level-4 auth sibling (heap 8..15) has its top bits clear. -/
theorem ftsSlotsClear_of_path (s : SharedSignature)
    (hp : ∀ p : Fin 4, topBits (ftsSlotBits (2 * p.val)) ((s.forest.pairs p).firstPath 4) = 0 ∧
      topBits (ftsSlotBits (2 * p.val + 1)) ((s.forest.pairs p).secondPath 4) = 0)
    (hs : topBits (ftsSlotBits 8) (s.forest.singleton.path 4) = 0)
    (hp16 : ∀ p : Fin 2, topBits 1 ((s.forest.pairs ⟨p.val, by have := p.isLt; omega⟩).firstPath 3) = 0 ∧
      topBits 1 ((s.forest.pairs ⟨p.val, by have := p.isLt; omega⟩).secondPath 3) = 0) : FtsSlotsClear s := by
  have hf : ∀ p : Fin 4, topBits (gBits (1 + 25 * p.val + 10)) ((sigDigests s).getD (1 + 25 * p.val + 10) 0) = 0 ∧
      topBits (gBits (1 + 25 * p.val + 22)) ((sigDigests s).getD (1 + 25 * p.val + 22) 0) = 0 := by
    intro p
    rw [show 1 + 25 * p.val + 10 = 1 + 25 * p.val + (6 + 4) by omega, sigDigests_pair s p (6 + 4) (by omega),
      pairList_firstPath _ ⟨4, by decide⟩, show 1 + 25 * p.val + 22 = 1 + 25 * p.val + (18 + 4) by omega,
      sigDigests_pair s p (18 + 4) (by omega), pairList_secondPath _ ⟨4, by decide⟩]
    have := hp p
    fin_cases p <;> exact this
  have h111 : topBits (gBits 111) ((sigDigests s).getD 111 0) = 0 := by
    rw [show (111 : Nat) = 101 + (6 + 4) by rfl, sigDigests_singleton s (6 + 4) (by omega), singletonList,
      SigGolfCandidate.T3M.getD_append_right' (by simp), List.length_ofFn, show 6 + 4 - 6 = 4 by rfl,
      SigGolfCandidate.T3M.getD_ofFn']
    exact hs
  have h16 : ∀ p : Fin 2, topBits (gBits (1 + 25 * p.val + 9)) ((sigDigests s).getD (1 + 25 * p.val + 9) 0) = 0 ∧
      topBits (gBits (1 + 25 * p.val + 21)) ((sigDigests s).getD (1 + 25 * p.val + 21) 0) = 0 := by
    intro p
    rw [show 1 + 25 * p.val + 9 = 1 + 25 * (⟨p.val, by have := p.isLt; omega⟩ : Fin 4).val + (6 + 3) by rfl,
      sigDigests_pair s ⟨p.val, by have := p.isLt; omega⟩ (6 + 3) (by omega), pairList_firstPath _ ⟨3, by decide⟩,
      show 1 + 25 * p.val + 21 = 1 + 25 * (⟨p.val, by have := p.isLt; omega⟩ : Fin 4).val + (18 + 3) by rfl,
      sigDigests_pair s ⟨p.val, by have := p.isLt; omega⟩ (18 + 3) (by omega), pairList_secondPath _ ⟨3, by decide⟩]
    have := hp16 p
    fin_cases p <;> exact this
  intro k hk hg
  rcases gBits_ne_zero k hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> first | (exfalso; omega) | skip
  · exact (hf 0).1
  · exact (hf 0).2
  · exact (hf 1).1
  · exact (hf 1).2
  · exact (hf 2).1
  · exact (hf 2).2
  · exact (hf 3).1
  · exact (hf 3).2
  · exact h111
  · exact (h16 0).1
  · exact (h16 0).2
  · exact (h16 1).1
  · exact (h16 1).2

/-- E8 (P1), Y5: `FtsPathOK` (the opened level-4 and level-5 FTS siblings pass their zero tests) clears the FTS
slots. -/
theorem ftsSlotsClear_of_ftsPathOK (s : SharedSignature) (h : FtsPathOK s) : FtsSlotsClear s := by
  have key : ∀ c (d : SigGolfCandidate.T3.Digest), ClaudeWCT.WCT9.ftsZeroOk c 8 d = true → topBits (ftsSlotBits c) d = 0 := by
    intro c d hd
    unfold ClaudeWCT.WCT9.ftsZeroOk ClaudeWCT.WCT9.ftsZeroBits at hd
    rw [if_pos (show 8 ≤ 8 ∧ 8 < 16 by decide)] at hd
    unfold topBits ftsSlotBits
    simpa using hd
  have key16 : ∀ c (d : SigGolfCandidate.T3.Digest), c < 4 → ClaudeWCT.WCT9.ftsZeroOk c 16 d = true →
      topBits 1 d = 0 := by
    intro c d hc hd
    unfold ClaudeWCT.WCT9.ftsZeroOk ClaudeWCT.WCT9.ftsZeroBits at hd
    rw [if_neg (show ¬ (8 ≤ 16 ∧ 16 < 16) by decide), if_pos (show 16 ≤ 16 ∧ 16 < 32 ∧ c < 4 from ⟨le_rfl, by decide, hc⟩)] at hd
    unfold topBits
    simpa using hd
  exact ftsSlotsClear_of_path s (fun p => ⟨key _ _ (h.1 p).1, key _ _ (h.1 p).2⟩) (key _ _ h.2.1)
    (fun p => ⟨key16 _ _ (by omega) (h.2.2 p).1, key16 _ _ (by omega) (h.2.2 p).2⟩)

/-- U16b: `LowerPathOK` signatures (E8: whose FTS slots are clear) have clear ground slots. -/
theorem groundClear_of_lowerPathOK (s : SharedSignature) (h : LowerPathOK s) (hf : FtsSlotsClear s) :
    GroundClear s := by
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
  by_cases hlo : k < 166
  · have := hf k hlo hk
    rwa [getD_eraseIdx, if_pos (by omega)]
  rcases gBits_ne_zero k hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> try (exfalso; omega)
  · exact key 1 ⟨6, by decide⟩ (by decide)
  · exact key 1 ⟨5, by decide⟩ (by decide)
  · exact key 1 ⟨4, by decide⟩ (by decide)
  · exact key 1 ⟨3, by decide⟩ (by decide)
  · exact key 2 ⟨5, by decide⟩ (by decide)
  · exact key 2 ⟨4, by decide⟩ (by decide)
  · exact key 2 ⟨3, by decide⟩ (by decide)
  · exact key 2 ⟨2, by decide⟩ (by decide)
  · exact key 3 ⟨5, by decide⟩ (by decide)
  · exact key 3 ⟨4, by decide⟩ (by decide)
  · exact key 3 ⟨3, by decide⟩ (by decide)
  · exact key 3 ⟨2, by decide⟩ (by decide)

/-- img-v6 codec round trip in the form used by the final pipeline (U16b: on clear ground slots, e.g. `LowerPathOK`). -/
theorem sigDecC_sigBC_normTop (s : SharedSignature) (hg : GroundClear s) (hr : RhoHintOK s) :
    sigDecC (sigBC s) = normTop s :=
  (sigDecC_sigBC s hg hr).trans (normalizeV6_eq_normTop s)

/-- U16b / R6: the compact encoder is injective up to the normal form `normTop` (on clear ground slots and an honest
rho/hint range). -/
theorem sigBC_injective_normTop (s t : SharedSignature) (hs : GroundClear s) (ht : GroundClear t)
    (hrs : RhoHintOK s) (hrt : RhoHintOK t) (h : sigBC s = sigBC t) : normTop s = normTop t := by
  rw [← sigDecC_sigBC_normTop s hs hrs, h, sigDecC_sigBC_normTop t ht hrt]

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
`xOfB b / 2^16` at `0x66000`. `fill_sigDecC`: the decoded signature has its brute-forced field (top sibling bits
111..127) clear. The `inflatedRead_*` lemmas read the slot layout back without letting the kernel unfold `digC` against
`inflatedRead` (that comparison blows up on T51's `digC`). -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

/-- E11: the decoded top sibling (digest 176) is below `2^101` (bits 101..107 zero-test, 108..127 filled by expand). -/
theorem digC_176_lt (b : CBytes) : (digC b 176).toNat < 2 ^ 101 := by
  rw [digC_176_toNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 16 by positivity)
  have h2 := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 33 by positivity)
  have h3 := vOfB_lt b
  generalize b.toNat / 2 ^ (128 * 324) % 2 ^ 16 = t at *
  generalize xOfB b % 2 ^ 33 = x at *
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
        change (digC b (layIdx 0 + chainCount 0 + j.val)).toNat % 2 ^ 108 + 0 % 2 ^ 20 * 2 ^ 108 =
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

/-- N7g: the decoded policy hints: `packH (N % 360)` for canonical `N`, `8192 + N % 360` otherwise (`hintOfN`). -/
theorem policyHints_sigDecC_toNat (b : CBytes) : (sigDecC b).policyHints.toNat = hintOfN (nOfB b) := by
  change (BitVec.ofNat 16 (hintOfN (nOfB b))).toNat = _
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (hintOfN_lt _)

/-- N7g: canonical compact bytes decode to a 13-bit hint (`packH ≤ 7934`). -/
theorem policyHints_sigDecC_lt (b : CBytes) (hc : nOfB b < R * 360) : (sigDecC b).policyHints.toNat < 2 ^ 13 := by
  rw [policyHints_sigDecC_toNat, hintOfN, if_pos hc]
  have := packH_le_7934 _ (Nat.mod_lt (nOfB b) (show 0 < 360 by decide))
  rw [show (2:Nat) ^ 13 = 8192 by norm_num]
  omega

/-- N7g (canonical check): the expand spec's hint test (`policyHints ≥ 8192 → none`) fires exactly on non-canonical
compact bytes `N ≥ R * 360 = 2^131 - 1044`, where DEC branches to word 354. -/
theorem policyHints_sigDecC_ge_iff (b : CBytes) :
    8192 ≤ (sigDecC b).policyHints.toNat ↔ R * 360 ≤ nOfB b := by
  rw [policyHints_sigDecC_toNat, hintOfN]
  have := packH_le_7934 _ (Nat.mod_lt (nOfB b) (show 0 < 360 by decide))
  split_ifs with h <;> omega

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

namespace ClaudeWCT.W9.T3M.SharedCodec
open OracleComp OracleSpec SigGolfCandidate.T3

/-- R6 (F4): `List.getD` returns a member of the list or the default. -/
theorem getD_mem_or_default (l : List Nat) (r d : Nat) : l.getD r d ∈ l ∨ l.getD r d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[r]? with
  | none => right; rfl
  | some x => left; exact List.mem_of_getElem? h

/-- Y5: the signer's hint `529 f1 + 23 f2 + f3` from admissible floors (`threshold 1 r1 < 15`,
`threshold 2 r2 < 23`, `threshold 3 r3 < 23`) is in the alphabet (`HintOK`; every table value is checked). -/
theorem hints_ok_table : ∀ r1 : Fin 55, ∀ r2 : Fin 41, ∀ r3 : Fin 23,
    HintOK (529 * ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 r1.val + 23 * ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 r2.val +
      ClaudeWCT.WCT9.CanonicalPolicy.threshold 3 r3.val) := by decide +kernel

theorem threshold_lt_ranges (lay r : Nat) (hl : lay = 1 ∨ lay = 2 ∨ lay = 3)
    (h : ClaudeWCT.WCT9.CanonicalPolicy.threshold lay r < 23) :
    r < (if lay = 1 then 55 else if lay = 2 then 41 else 23) := by
  unfold ClaudeWCT.WCT9.CanonicalPolicy.threshold at h
  rcases hl with rfl | rfl | rfl
  · simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true] at h ⊢
    by_contra hr
    rw [List.getD_eq_default _ _ (by simp [ClaudeWCT.WCT9.CanonicalPolicy.lowerOneThresholds]; omega)] at h
    omega
  · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false, if_true] at h ⊢
    by_contra hr
    rw [List.getD_eq_default _ _ (by simp [ClaudeWCT.WCT9.CanonicalPolicy.lowerTwoThresholds]; omega)] at h
    omega
  · simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide,
      if_false, true_and] at h ⊢
    split_ifs at h <;> omega

/-- R6 (F4): every signature produced by `signFromOutput` from a reduced nonce (`rho < R`) is `RhoHintOK`. -/
theorem rhoHintOK_signFromOutput (answers : SigGolfCandidate.T3.Correctness.Answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (hrho : rho.toNat < R)
    (he : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output)
      = some w) :
    RhoHintOK w.signature := by
  obtain ⟨result, hres, hr, hh, -⟩ :=
    SigGolfCandidate.Research.SharedForest.signFromOutput_components answers cache rho counter output w he
  have F := SigGolfCandidate.Research.SharedForest.searchPreparedLayers_some answers cache _ _ _ result hres
  have r1 := threshold_lt_ranges 1 _ (by decide) (lt_of_lt_of_le F.floor1_lt (by decide))
  have r2 := threshold_lt_ranges 2 _ (by decide) F.floor2_lt
  have r3 := threshold_lt_ranges 3 _ (by decide) F.floor3_lt
  simp only [if_true, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide,
    if_false] at r1 r2 r3
  refine ⟨by rw [hr]; exact hrho, ?_⟩
  rw [hh, F.hints_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have h1 := F.floor1_lt; have h2 := F.floor2_lt; have h3 := F.floor3_lt; omega)]
  exact hints_ok_table ⟨_, r1⟩ ⟨_, r2⟩ ⟨_, r3⟩

/-- R6 (F4): honest `signPayload` output is `RhoHintOK` (`rho = rhoMod _ < R`, admissible floors). -/
theorem rhoHintOK_signPayload (answers : SigGolfCandidate.T3.Correctness.Answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) (sig : SharedSignature)
    (he : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload cache message) = some sig) :
    RhoHintOK sig := by
  obtain ⟨counter, output, w, -, hw, rfl⟩ :=
    SigGolfCandidate.Research.SharedForest.signPayload_components answers cache message sig he
  refine rhoHintOK_signFromOutput answers cache _ counter output w ?_ hw
  simp only [privateNonce, evalWithAnswerFn_bind, evalWithAnswerFn_pure, rhoMod_toNat]
  exact rhoMod_lt _

/-- R6 (F4): every honest signature (`SharedForest.sign`) is `RhoHintOK`; feed this to the codec round trip
(`sigDecC_sigBC_normTop`, `digC_sigBC`, `sigBC_injective_normTop`). -/
theorem rhoHintOK_sign (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : SharedSignature)
    (he : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.sign cache message) = some sig) :
    RhoHintOK sig := by
  unfold SigGolfCandidate.Research.SharedForest.sign at he
  simp only [evalWithAnswerFn_bind] at he
  split_ifs at he with htag
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
  · exact rhoHintOK_signPayload answers cache message sig he

end ClaudeWCT.W9.T3M.SharedCodec
end
