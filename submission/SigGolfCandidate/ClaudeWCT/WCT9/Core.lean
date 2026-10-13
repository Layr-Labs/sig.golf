import SigGolfCandidate.T3.Core
import SigGolfCandidate.T3.Nonbinary.LowerLayout
import SigGolfCandidate.ClaudeWCT.WCT9.Codebook
import SigGolfCandidate.ClaudeWCT.Arith.GF128

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def coordinates : Nat := 9
def children : Nat := 128
def chains : Nat := 6
def gateShift : Nat := 242
def gateBits : Nat := 14
def gateLimit : Nat := 1353
def fieldBits : Nat := 10
def fieldLimit : Nat := 563
def jointCap : Nat := 775
abbrev Coord := Fin 9
abbrev Child := Fin 128
abbrev Rank := Fin 563
def wctHeader (tag lay tree position index : Nat) : BitVec 128 :=
  BitVec.ofNat 128 (1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 +
    (tree / 2 ^ 32 % 256) * 2 ^ 24 + position % 2 ^ 32 * 2 ^ 32 +
    tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96)
def indexShift : Nat := 33
def digestIndex (output : HashOutput) : Nat := output.toNat / 2 ^ 33 % 2 ^ 31
theorem digestIndex_lt (output : HashOutput) : digestIndex output < 2 ^ 31 := Nat.mod_lt _ (by decide)
def childBase (k : Nat) : Nat := [0,64,85,121,128,149,185,192,213].getD k 0
def fieldBase (k : Nat) : Nat := [7,71,92,107,135,156,171,199,220].getD k 0
def child (output : HashOutput) (coord : Coord) : Child :=
  ⟨output.toNat / 2 ^ childBase coord.val % 128, Nat.mod_lt _ (by decide)⟩
def field (output : HashOutput) (coord : Coord) : Nat :=
  output.toNat / 2 ^ fieldBase coord.val % 2 ^ 10
def rank (output : HashOutput) (coord : Coord) : Rank :=
  ⟨field output coord % 563, Nat.mod_lt _ (by decide)⟩
def admissible (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 242 % 2 ^ 14 < 1353) &&
    (List.range 9).all (fun coord =>
      decide (output.toNat / 2 ^ fieldBase coord % 2 ^ 10 < 563))
/-- C1 (FTS Merkle half-swap): `4 + skips`, where `skips` (0, 1 or 2, by `c % 32`) counts the child program's
elided `a2` loads; the child program costs `27 - skips` instructions. -/
def childSaveTable : List Nat :=
  [4,5,5,5,5,6,6,5,5,6,6,6,6,6,6,5,5,6,6,6,5,6,6,5,5,6,6,5,5,5,5,4,4,5,5,5,5,6,6,5,5,6,6,6,6,6,6,5,5,6,6,6,5,6,6,5,5,6,6,5,5,5,5,4,4,5,5,5,5,6,6,5,5,6,6,6,6,6,6,5,5,6,6,6,5,6,6,5,5,6,6,5,5,5,5,4,4,5,5,5,5,6,6,5,5,6,6,6,6,6,6,5,5,6,6,6,5,6,6,5,5,6,6,5,5,5,5,4]
def maxChildSave : Nat := 6
def childSave (c : Nat) : Nat := childSaveTable.getD (c % 128) 0
def childExtra (c : Child) : Nat := maxChildSave - childSave c.val
theorem childSaveTable_le : ∀ i, i < 128 → childSaveTable.getD i 0 ≤ maxChildSave := by decide
theorem childSave_le (c : Nat) : childSave c ≤ maxChildSave :=
  childSaveTable_le (c % 128) (Nat.mod_lt _ (by decide))
theorem childSave_ge (c : Nat) : 4 ≤ childSave c := by
  have h : ∀ i, i < 128 → 4 ≤ childSaveTable.getD i 0 := by decide
  exact h (c % 128) (Nat.mod_lt _ (by decide))
theorem childExtra_add (c : Child) : childExtra c + childSave c.val = maxChildSave := by
  have := childSave_le c.val
  unfold childExtra; omega
def coordCost (output : HashOutput) (coord : Coord) : Nat :=
  routineCost (rank output coord) + childExtra (child output coord)
def jointCost (output : HashOutput) : Nat :=
  ((List.finRange 9).map fun coord => coordCost output coord).sum
def capOk (output : HashOutput) : Bool := decide (jointCost output ≤ jointCap)
def producerAdmissible (output : HashOutput) : Bool := admissible output && capOk output
def digestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if producerAdmissible output then return some (BitVec.ofNat 32 counter, output)
      digestSearch rho message (counter + 1) fuel
def ftsChainLow (index coord selected chain step : Nat) : Nat :=
  0x80 + chain % 8 * 2 ^ 2 + step % 4 * 2 ^ 8 + coord % 16 * 2 ^ 16 + selected % 128 * 2 ^ 20 +
    index % 2 ^ 31 * 2 ^ 27
def ftsChainHeaderP (index coord selected chain step : Nat) (high : BitVec 64) : BitVec 128 :=
  high ++ BitVec.ofNat 64 (ftsChainLow index coord selected chain step)
def ftsChainHeader (index coord selected chain step : Nat) : BitVec 128 :=
  ftsChainHeaderP index coord selected chain step 0
def chainInput (index coord selected chain step : Nat) (value : Digest) : HashInput :=
  zero16 ++ bytesLE 16 (ftsChainHeader index coord selected chain step) ++
    zero16 ++ bytesLE 16 value
def chain (index coord selected i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInput index coord selected i step value)) value
/-- C1 (FTS Merkle half-swap): the FTS heaps whose value is the HIGH 16 bytes of their hash output: the top pair
(heaps 2 and 3, nested FTS r1-1) and every even heap `16..255`, i.e. the left inputs of the four packed fold windows,
including the child leaves `128 + c` with `c` even. Every other FTS heap uses the low half. -/
def ftsHighHeap (heap : Nat) : Bool := decide (heap < 4) || (decide (16 ≤ heap) && decide (heap % 2 = 0))
/-- C1: the used half of the hash output of FTS heap `heap`. -/
def ftsHalf (heap : Nat) (output : HashOutput) : Digest :=
  if ftsHighHeap heap then output.extractLsb' 128 128 else output.extractLsb' 0 128
/-- C1: the value of FTS heap `heap` hashed from `input`: the high half on `ftsHighHeap` heaps, else the low half. -/
def ftsHash (heap : Nat) (input : HashInput) : M Digest :=
  if ftsHighHeap heap then do pure ((← publicHash input).extractLsb' 128 128) else shortHash input
def ftsLeafLow (index coord selected : Nat) : Nat :=
  1 + 6 * 2 ^ 8 + coord % 16 * 2 ^ 16 + selected % 128 * 2 ^ 20 + index % 2 ^ 31 * 2 ^ 27
def ftsLeafHeader (index coord selected : Nat) : BitVec 128 :=
  0#64 ++ BitVec.ofNat 64 (ftsLeafLow index coord selected)
/-- FTS child leaf (campaign T8): `end0 | header | zero16 | end1..end5` (128 bytes, two blocks). The zero slot
after the header is a witness pad in the padded verifier; the honest value is zero. -/
def leafHash (index coord selected : Nat) (ends : List Digest) : M Digest :=
  shortHash (bytesLE 16 (ends.getD 0 0) ++
    bytesLE 16 (ftsLeafHeader index coord selected) ++ zero16 ++ (ends.drop 1).flatMap (bytesLE 16))
/-- Padded FTS leaf (campaign T8): the leaf with an arbitrary 16-byte value in the pad slot (nested FTS r1-1: the
previous coordinate's left top value). -/
def leafInputP (index coord selected : Nat) (pad : Digest) (ends : List Digest) : HashInput :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (ftsLeafHeader index coord selected) ++ bytesLE 16 pad ++
    (ends.drop 1).flatMap (bytesLE 16)
/-- C1: the leaf of child `selected` is FTS heap `128 + selected`, so it is the high half when `selected` is even. -/
def leafHashP (index coord selected : Nat) (pad : Digest) (ends : List Digest) : M Digest :=
  ftsHash (128 + selected) (leafInputP index coord selected pad ends)
theorem bytesLE_zero16 : bytesLE 16 (0 : Digest) = zero16 := by decide
def seedHalf (seeds : Digest × Digest) (q : Nat) : Digest := if q % 2 = 0 then seeds.1 else seeds.2
def packedSecret (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest) : M (Digest × Digest) :=
  if q % 2 = 0 then do
    let seeds ← pairQuery (q / 2)
    pure (seeds.1, seeds.2)
  else pure (carry, carry)
def ftsOrdinal (child chain : Nat) : Nat := 6 * child + chain
def ftsSeedHeader (coord index pair : Nat) : BitVec 128 := header 8 coord index 0 pair
def ftsSeedPair (index coord pair : Nat) : M (Digest × Digest) := privatePair 8 coord index 0 pair
def buildChild (index coord selected : Nat) (word : Rank) (carry : Digest) :
    M ((Digest × List Digest) × Digest) := do
  let state ← (List.finRange 6).foldlM
    (fun (state : List Digest × List Digest × Digest) i => do
      let (secret, carry) ← packedSecret (ftsSeedPair index coord) (ftsOrdinal selected i.val) state.2.2
      let deficit := wordDigit word i
      let value ← chain index coord selected i.val 0 (4 - deficit) secret
      let last ← chain index coord selected i.val (4 - deficit) deficit value
      pure (state.1 ++ [last], state.2.1 ++ [value], carry)) ([], [], carry)
  let root ← leafHash index coord selected state.1
  pure ((root, state.2.1), state.2.2)
def nodeLayer (coord : Nat) : Nat := 4 + coord
def wctNodeHeader (coord index heap : Nat) : BitVec 128 := nodeTweak 3 (nodeLayer coord) index heap
/-- FTS node at heap `heap` with a zero pad; C1: the used half follows `ftsHighHeap heap`. -/
def wctNodeHash (coord index heap : Nat) (left right : Digest) : M Digest :=
  ftsHash heap (bytesLE 16 left ++ bytesLE 16 (wctNodeHeader coord index heap) ++ zero16 ++ bytesLE 16 right)
/-- High half of a public hash. -/
def highHash (input : HashInput) : M Digest := do
  pure ((← publicHash input).extractLsb' 128 128)
/-! ### C2 + C3 (FULL): lower-tree half-swap, packed lower node word, witness pads, chain-0 high half
The legacy `T3` definitions (`nodeTweak`, `nodeHash`, `leafInput`, `leafHash`, `chain`, `rowTweak`) keep their text;
the current scheme uses the definitions below.
* Lower trees (layers 1..3): a left child (even heap; the leaves of even index included) is the HIGH 16 bytes of its
  hash output, a right child the low 16 bytes (`lowerHigh`). The top tree (layer 0) and the FTS keep their rules.
* Lower node tweak: one marked word `hyperWord (lay - 1) tree + lowerK + heap` (byte0 `128 + heap`, byte1 7); its
  high word is a witness pad (honest 0).
* Leaf tweak high words (all layers) and the top leaf's leading 16 bytes are witness pads (honest 0); the encoding
  row tweak's high word is a witness pad (honest 1).
* Lower chain 0's last step (step 6) keeps the HIGH half of its output (`chainHigh`). -/
def lowerK : Nat := 1407
/-- Packed lower node word (`lay` = layer - 1, as in `hyperWord`). For heaps `2..127` the low 16 bits are
`0x0780 + heap` (no carry: `hyperWord`'s low 16 bits are `0x0201`). -/
def lowerNodeWord (lay tree heap : Nat) : BitVec 64 := hyperWord lay tree + BitVec.ofNat 64 (lowerK + heap)
/-- C2 node tweak of lower layer `lay` (1..3) with the honest high word 0. -/
def lowerTweak (lay tree heap : Nat) : BitVec 128 := 0#64 ++ lowerNodeWord (lay - 1) tree heap
/-- Merkle node tweak of the current scheme: the top tree keeps `nodeTweak 3 0`, the lower trees use `lowerTweak`. -/
def merkleTweak (lay tree heap : Nat) : BitVec 128 :=
  if lay = 0 then nodeTweak 3 0 tree heap else lowerTweak lay tree heap
/-- The used half of a hash output. -/
def halfOf (high : Bool) (output : HashOutput) : Digest :=
  if high then output.extractLsb' 128 128 else output.extractLsb' 0 128
/-- A hash whose used half is selected by `high`. -/
def halfHash (high : Bool) (input : HashInput) : M Digest := if high then highHash input else shortHash input
/-- C2: heap `heap` of layer `lay` uses the high half (lower layers, even heap). -/
def lowerHigh (lay heap : Nat) : Bool := decide (1 ≤ lay ∧ lay < 4) && decide (heap % 2 = 0)
def lowerHalf (lay heap : Nat) (output : HashOutput) : Digest := halfOf (lowerHigh lay heap) output
def lowerHash (lay heap : Nat) (input : HashInput) : M Digest := halfHash (lowerHigh lay heap) input
/-- C3: the last step (step 6) of chain 0 of a lower layer keeps the high half. -/
def chainHigh (lay : Layer) (i step : Nat) : Bool := decide (lay ≠ 0) && decide (i = 0) && decide (step = 6)
/-- WOTS chain of the current scheme (`T3.chain` with the chain-0 high half). -/
def chainW (lay : Layer) (tree leaf i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => halfHash (chainHigh lay i step) (SigGolfCandidate.T3.chainInput lay tree leaf i step value))
    value
/-- Leaf tweak with the witness high word `hi` (honest 0). -/
def leafTweakW (lay : Layer) (tree leaf : Nat) (hi : BitVec 64) : BitVec 128 :=
  hi ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)
/-- Verifier leaf input: the top leaf has the witness pad `pad` in its leading block, a lower leaf starts with chain
0's end (`pad` unused); the tweak high word is `hi`. `leafInputW_zero`: pads 0 give `T3.leafInput`. -/
def leafInputW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) : HashInput :=
  if lay = 0 then bytesLE 16 pad ++ bytesLE 16 (leafTweakW lay tree leaf hi) ++ ends.flatMap (bytesLE 16)
  else bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (leafTweakW lay tree leaf hi) ++ (ends.drop 1).flatMap (bytesLE 16)
/-- Leaf hash of the current scheme (half by leaf index; the top uses the low half). -/
def leafHashW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) : M Digest :=
  lowerHash lay.val leaf (leafInputW lay tree leaf pad hi ends)
/-- Honest leaf hash of the current scheme. -/
def lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) : M Digest := leafHashW lay tree leaf 0 0 ends
/-- Verifier fold input of a lower node (`lay` 1..3): witness high tweak word `hp` and pad `pad` (honest 0, 0). -/
def lowerNodeInputP (lay tree heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (hp ++ lowerNodeWord (lay - 1) tree heap) ++ bytesLE 16 pad ++ bytesLE 16 right
def lowerNodeHashP (lay tree heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : M Digest :=
  lowerHash lay heap (lowerNodeInputP lay tree heap left hp pad right)
/-- Honest node input of the current scheme (all layers): `left | merkleTweak | 0 | right`. -/
def merkleNodeInput (lay tree heap : Nat) (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (merkleTweak lay tree heap) ++ zero16 ++ bytesLE 16 right
/-- Honest node hash of the current scheme (all layers; the top is `T3.nodeHash 3 0`, `lowerNodeHash_top`). -/
def lowerNodeHash (lay tree heap : Nat) (left right : Digest) : M Digest :=
  lowerHash lay heap (merkleNodeInput lay tree heap left right)
/-- `T3.buildLevel 3` with `lowerNodeHash`. -/
def lowerLevel (lay tree h level : Nat) (nodes : List Digest) : M (List Digest) :=
  (List.range (nodes.length / 2)).mapM fun i =>
    lowerNodeHash lay tree (2 ^ (h-level) + i) (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)
/-- `T3.buildLevels 3` with `lowerLevel` (all levels, root included). -/
def lowerLevels (lay tree h : Nat) (leaves : List Digest) : M (List (List Digest)) :=
  (List.range' 1 h).foldlM (fun levels level => do
    let nodes ← lowerLevel lay tree h level (levels.getD (level-1) [])
    pure (levels ++ [nodes])) [leaves]
theorem halfHash_eq (high : Bool) (input : HashInput) :
    halfHash high input = publicHash input >>= fun a => pure (halfOf high a) := by
  unfold halfHash halfOf highHash shortHash
  cases high <;> rfl
@[simp] theorem halfHash_false (input : HashInput) : halfHash false input = shortHash input := rfl
@[simp] theorem halfHash_true (input : HashInput) : halfHash true input = highHash input := rfl
@[simp] theorem halfOf_false (output : HashOutput) : halfOf false output = output.extractLsb' 0 128 := rfl
@[simp] theorem halfOf_true (output : HashOutput) : halfOf true output = output.extractLsb' 128 128 := rfl
theorem lowerHash_eq (lay heap : Nat) (input : HashInput) :
    lowerHash lay heap input = publicHash input >>= fun a => pure (lowerHalf lay heap a) :=
  halfHash_eq _ _
theorem lowerHigh_iff (lay heap : Nat) : lowerHigh lay heap = true ↔ (1 ≤ lay ∧ lay < 4) ∧ heap % 2 = 0 := by
  simp [lowerHigh]
@[simp] theorem lowerHigh_top (heap : Nat) : lowerHigh 0 heap = false := by simp [lowerHigh]
theorem lowerHigh_heap {lay e x : Nat} (he : 1 ≤ e) : lowerHigh lay (2 ^ e + x) = lowerHigh lay x := by
  have : 2 ^ e % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ]; simp
  unfold lowerHigh
  rw [show (2 ^ e + x) % 2 = x % 2 by omega]
@[simp] theorem chainHigh_top (i step : Nat) : chainHigh 0 i step = false := by simp [chainHigh]
theorem chainHigh_eq_false {lay : Layer} {i step : Nat} (h : lay = 0 ∨ i ≠ 0 ∨ step ≠ 6) :
    chainHigh lay i step = false := by
  simp only [chainHigh]; rcases h with h | h | h <;> simp [h]
theorem chainHigh_eq_true {lay : Layer} {i step : Nat} :
    chainHigh lay i step = true ↔ lay ≠ 0 ∧ i = 0 ∧ step = 6 := by
  simp [chainHigh, and_assoc]
theorem foldlM_congr_of_mem {α β : Type} {m : Type → Type} [Monad m] (f g : β → α → m β) :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldlM f init = l.foldlM g init
  | [], _, _ => rfl
  | x :: xs, init, h => by
      simp only [List.foldlM_cons]
      rw [h x List.mem_cons_self]
      congr 1; funext b
      exact foldlM_congr_of_mem f g xs b (fun y hy => h y (List.mem_cons_of_mem _ hy))
/-- `chainW` is `T3.chain` when no step of the run keeps the high half. -/
theorem chainW_of_low {lay : Layer} {i start count : Nat}
    (h : ∀ step, start ≤ step → step < start + count → chainHigh lay i step = false)
    (tree leaf : Nat) (value : Digest) :
    chainW lay tree leaf i start count value = SigGolfCandidate.T3.chain lay tree leaf i start count value := by
  unfold chainW SigGolfCandidate.T3.chain
  apply foldlM_congr_of_mem
  intro step hs b
  rw [List.mem_range'_1] at hs
  rw [h step hs.1 hs.2]; rfl
theorem chainW_top (tree leaf i start count : Nat) (value : Digest) :
    chainW 0 tree leaf i start count value = SigGolfCandidate.T3.chain 0 tree leaf i start count value :=
  chainW_of_low (fun _ _ _ => chainHigh_top _ _) tree leaf value
theorem chainW_ne_zero {lay : Layer} {i : Nat} (hi : i ≠ 0) (tree leaf start count : Nat) (value : Digest) :
    chainW lay tree leaf i start count value = SigGolfCandidate.T3.chain lay tree leaf i start count value :=
  chainW_of_low (fun _ _ _ => chainHigh_eq_false (Or.inr (Or.inl hi))) tree leaf value
theorem chainW_add (lay : Layer) (tree leaf i start a b : Nat) (value : Digest) :
    chainW lay tree leaf i start (a + b) value =
      (chainW lay tree leaf i start a value >>= chainW lay tree leaf i (start + a) b) := by
  unfold chainW
  rw [← List.range'_append_1, List.foldlM_append]
theorem leafInputW_zero (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafInputW lay tree leaf 0 0 ends = SigGolfCandidate.T3.leafInput lay tree leaf ends := by
  unfold leafInputW leafTweakW SigGolfCandidate.T3.leafInput leafTweak
  split
  · rw [show bytesLE 16 (0 : Digest) = zero16 by decide]; rfl
  · rfl
theorem lowerLeafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    lowerLeafHash lay tree leaf ends = lowerHash lay.val leaf (SigGolfCandidate.T3.leafInput lay tree leaf ends) := by
  unfold lowerLeafHash leafHashW; rw [leafInputW_zero]
theorem lowerLeafHash_top (tree leaf : Nat) (ends : List Digest) :
    lowerLeafHash 0 tree leaf ends = SigGolfCandidate.T3.leafHash 0 tree leaf ends := by
  rw [lowerLeafHash_eq]; unfold lowerHash; rw [show (0 : Layer).val = 0 from rfl, lowerHigh_top]; rfl
theorem leafHashW_top (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    leafHashW 0 tree leaf pad hi ends = shortHash (leafInputW 0 tree leaf pad hi ends) := by
  unfold leafHashW lowerHash; rw [show (0 : Layer).val = 0 from rfl, lowerHigh_top]; rfl
theorem lowerTweak_low (lay tree heap : Nat) :
    (lowerTweak lay tree heap).extractLsb' 0 64 = hyperWord (lay - 1) tree + BitVec.ofNat 64 (lowerK + heap) := by
  unfold lowerTweak lowerNodeWord; exact BitVec.extractLsb'_append_eq_right
theorem lowerTweak_high (lay tree heap : Nat) : (lowerTweak lay tree heap).extractLsb' 64 64 = 0 := by
  unfold lowerTweak; exact BitVec.extractLsb'_append_eq_left
@[simp] theorem merkleTweak_top (tree heap : Nat) : merkleTweak 0 tree heap = nodeTweak 3 0 tree heap := by
  simp [merkleTweak]
theorem merkleTweak_lower {lay : Nat} (h : lay ≠ 0) (tree heap : Nat) :
    merkleTweak lay tree heap = lowerTweak lay tree heap := by
  simp [merkleTweak, h]
theorem lowerNodeInputP_zero {lay : Nat} (h : lay ≠ 0) (tree heap : Nat) (left right : Digest) :
    lowerNodeInputP lay tree heap left 0 0 right = merkleNodeInput lay tree heap left right := by
  unfold lowerNodeInputP merkleNodeInput
  rw [merkleTweak_lower h, show bytesLE 16 (0 : Digest) = zero16 by decide]; rfl
theorem lowerNodeHash_eqP {lay : Nat} (h : lay ≠ 0) (tree heap : Nat) (left right : Digest) :
    lowerNodeHash lay tree heap left right = lowerNodeHashP lay tree heap left 0 0 right := by
  unfold lowerNodeHash lowerNodeHashP; rw [lowerNodeInputP_zero h]
theorem lowerNodeHash_top (tree heap : Nat) (left right : Digest) :
    lowerNodeHash 0 tree heap left right = nodeHash 3 0 tree heap left right := by
  unfold lowerNodeHash lowerHash merkleNodeInput; rw [lowerHigh_top, merkleTweak_top]; rfl
theorem lowerLevel_top (tree h level : Nat) (nodes : List Digest) :
    lowerLevel 0 tree h level nodes = buildLevel 3 0 tree h level nodes := by
  unfold lowerLevel buildLevel; simp only [lowerNodeHash_top]
theorem lowerLevels_top (tree h : Nat) (leaves : List Digest) :
    lowerLevels 0 tree h leaves = buildLevels 3 0 tree h leaves := by
  unfold lowerLevels buildLevels; simp only [lowerLevel_top]
/-- Nested FTS (r1-1): input of a top node (heap 2 or 3) of an FTS coordinate, with the previous coordinate's
right top value in the pad slot. -/
def wctTopInput (coord index heap : Nat) (left pad right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (wctNodeHeader coord index heap) ++ bytesLE 16 pad ++ bytesLE 16 right
/-- Nested FTS (r1-1): the top values (heaps 2 and 3) are the HIGH half of their node hash. -/
def wctTopHash (coord index heap : Nat) (left pad right : Digest) : M Digest :=
  highHash (wctTopInput coord index heap left pad right)
theorem ftsHash_eq (heap : Nat) (input : HashInput) :
    ftsHash heap input = if ftsHighHeap heap then highHash input else shortHash input := rfl
theorem ftsHash_of_high {heap : Nat} (h : ftsHighHeap heap = true) (input : HashInput) :
    ftsHash heap input = highHash input := by
  rw [ftsHash_eq, if_pos h]
theorem ftsHash_of_low {heap : Nat} (h : ftsHighHeap heap = false) (input : HashInput) :
    ftsHash heap input = shortHash input := by
  rw [ftsHash_eq, if_neg (by simp [h])]
theorem ftsHalf_of_high {heap : Nat} (h : ftsHighHeap heap = true) (output : HashOutput) :
    ftsHalf heap output = output.extractLsb' 128 128 := by
  simp [ftsHalf, h]
theorem ftsHalf_of_low {heap : Nat} (h : ftsHighHeap heap = false) (output : HashOutput) :
    ftsHalf heap output = output.extractLsb' 0 128 := by
  simp [ftsHalf, h]
theorem ftsHighHeap_top {heap : Nat} (h : heap < 4) : ftsHighHeap heap = true := by
  simp [ftsHighHeap, h]
theorem ftsHighHeap_mid {heap : Nat} (h4 : 4 ≤ heap) (h16 : heap < 16) : ftsHighHeap heap = false := by
  simp [ftsHighHeap]; omega
theorem ftsHighHeap_odd {heap : Nat} (h4 : 4 ≤ heap) (h : heap % 2 = 1) : ftsHighHeap heap = false := by
  simp [ftsHighHeap]; omega
theorem ftsHighHeap_even {heap : Nat} (h16 : 16 ≤ heap) (h : heap % 2 = 0) : ftsHighHeap heap = true := by
  simp [ftsHighHeap]; omega
theorem wctTopHash_eq_ftsHash {heap : Nat} (h : heap < 4) (coord index : Nat) (left pad right : Digest) :
    wctTopHash coord index heap left pad right = ftsHash heap (wctTopInput coord index heap left pad right) :=
  (ftsHash_of_high (ftsHighHeap_top h) _).symm
/-- Heap of an FTS coordinate. Heaps `4..127` are node hashes with a zero pad (C1: high half on even heaps `>= 16`,
low half otherwise); heaps 2 and 3 are `wctTopHash` with pad `padR` (nested FTS r1-1). -/
def wctHeapNode (coord index heap : Nat) (padR left right : Digest) : M Digest :=
  if heap < 4 then wctTopHash coord index heap left padR right else wctNodeHash coord index heap left right
def heapBuild (index coord : Nat) (padR : Digest) (leaves : List Digest) : M (Array Digest) :=
  (List.range' 2 126).reverse.foldlM (fun nodes heap => do
    let value ← wctHeapNode coord index heap padR (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
    pure (nodes.set! heap value)) ((List.replicate 128 (0 : Digest) ++ leaves).toArray)
def heapLevels (heap : Array Digest) : List (List Digest) :=
  (List.range 7).map fun level =>
    (List.range (2 ^ (7 - level))).map fun i => heap.getD (2 ^ (7 - level) + i) 0
def buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range 128).foldlM
    (fun (state : List Digest × List Digest × Digest) j => do
      let ((root, values), carry) ← buildChild index coord.val j word state.2.2
      pure (state.1 ++ [root], (if j = selected.val then values else state.2.1), carry)) ([], [], 0)
  let nodes ← heapBuild index coord.val 0 state.1
  pure (heapLevels nodes, state.2.1)
/-! ### Arithmetic seeds (stage3 F8): FTS seeds from a degree-53 GF(2^128) family per coordinate.
The 54 coefficients are the halves of `ftsSeedPair index coord j`, `j < 27`, low half first; the seed of chain
`chain` of child `child` is `familyEval coefs (ftsPoint child chain)`. Used by `signPayload` and by `Rev3.sign`
(through `signPayloadWith`). -/
def ftsCoefPairs : Nat := 27
def ftsCoefs (index coord : Nat) : M (List Digest) :=
  (List.range ftsCoefPairs).foldlM (fun acc j => do
    let p ← ftsSeedPair index coord j
    pure (acc ++ [p.1, p.2])) []
def ftsPoint (child chain : Nat) : Nat := ftsOrdinal child chain + 1
def ftsFamilySeed (coefs : List Digest) (child chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval coefs (ftsPoint child chain)
def buildChildF (index coord selected : Nat) (word : Rank) (coefs : List Digest) (padL : Digest) :
    M (Digest × List Digest) := do
  let state ← (List.finRange 6).foldlM
    (fun (state : List Digest × List Digest) i => do
      let secret := ftsFamilySeed coefs selected i.val
      let deficit := wordDigit word i
      let value ← chain index coord selected i.val 0 (4 - deficit) secret
      let last ← chain index coord selected i.val (4 - deficit) deficit value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  let root ← leafHashP index coord selected padL state.1
  pure (root, state.2)
/-- One FTS coordinate (nested FTS r1-1): `prev` is the previous coordinate's top pair `(L, R)`; every leaf
carries `L` in its pad slot and the two top nodes carry `R` in their pad slot. -/
def buildCoordinateF (index : Nat) (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    M (List (List Digest) × List Digest) := do
  let coefs ← ftsCoefs index coord.val
  let state ← (List.range 128).foldlM
    (fun (state : List Digest × List Digest) j => do
      let (root, values) ← buildChildF index coord.val j word coefs prev.1
      pure (state.1 ++ [root], (if j = selected.val then values else state.2))) ([], [])
  let nodes ← heapBuild index coord.val prev.2 state.1
  pure (heapLevels nodes, state.2)
/-- Nested FTS (r1-1): the pads of coordinate 0 in the honest scheme. -/
def ftsStart : Digest × Digest := (0, 0)
/-- Nested FTS (r1-1): the pads of the next coordinate, i.e. the last top pair (or `start` before coordinate 0). -/
def prevPair (start : Digest × Digest) (pairs : List (Digest × Digest)) : Digest × Digest := pairs.getLastD start
def forestInput (index : Nat) (pairs : List (Digest × Digest)) : HashInput :=
  zero16 ++ bytesLE 16 (header 15 0 index 0 0) ++
    pairs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)
def forestPk (index : Nat) (pairs : List (Digest × Digest)) : M Digest :=
  shortHash (forestInput index pairs)
inductive LayerMsg where
  | forest (root : Digest)
  | pair (left right : Digest)
  deriving DecidableEq
def pairEncodingInputP (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (rowTweak up tree leaf) ++ bytesLE 4 counter ++ bytesLE 12 pad ++
    bytesLE 16 right
/-- C2/C3 (FULL): the encoding input with the row tweak's high word `hi` a witness pad (honest 1,
`pairEncodingInputH_one`). -/
def pairEncodingInputH (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (hi : BitVec 64) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (hi ++ hyperWord up.val (tree * 2 ^ height up + leaf)) ++ bytesLE 4 counter ++
    bytesLE 12 pad ++ bytesLE 16 right
theorem pairEncodingInputH_one (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) : pairEncodingInputH up tree leaf left right counter pad 1 =
      pairEncodingInputP up tree leaf left right counter pad := rfl
/-- The encoding row tweak with the witness high word `hi` (`rowTweakW_one`: honest 1 is `T3.rowTweak`). -/
def rowTweakW (up : Layer) (tree leaf : Nat) (hi : BitVec 64) : BitVec 128 :=
  hi ++ hyperWord up.val (tree * 2 ^ height up + leaf)
theorem rowTweakW_one (up : Layer) (tree leaf : Nat) : rowTweakW up tree leaf 1 = rowTweak up tree leaf := rfl
theorem pairEncodingInputH_eq (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (hi : BitVec 64) : pairEncodingInputH up tree leaf left right counter pad hi =
      bytesLE 16 left ++ bytesLE 16 (rowTweakW up tree leaf hi) ++ bytesLE 4 counter ++ bytesLE 12 pad ++
        bytesLE 16 right := rfl
def layerEncodingInput (lay : Layer) (tree leaf : Nat) : LayerMsg → BitVec 32 → HashInput
  | .forest root, counter => encodingInput lay tree leaf root counter
  | .pair left right, counter => pairEncodingInputP lay tree leaf left right counter 0
/-- A zero-step chain whose leaf slot survives earlier 32-byte HASH writes. -/
def safeZeroCopy (lay : Layer) (digits : List Nat) (i : Nat) : Prop :=
  digits.getD i 0 = maxDigit lay i ∧
    (i = 0 ∨ (lay ≠ 0 ∧ i = 1) ∨
      (0 < i ∧ i % 3 ≠ 0 ∧ digits.getD (i-1) 0 = maxDigit lay (i-1)))
instance (lay : Layer) (digits : List Nat) (i : Nat) : Decidable (safeZeroCopy lay digits i) := by
  unfold safeZeroCopy
  infer_instance

def savedCopies (lay : Layer) (digits : List Nat) : Nat :=
  ((List.range (chainCount lay)).filter fun i => decide (safeZeroCopy lay digits i)).length

def topDispatchPenalty (digits : List Nat) : Nat :=
  ((List.range 17).filter fun q => decide
    (q ≠ 9 ∧ q < 13 ∧ digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3)).length

def dispatchPenalty (lay : Layer) (digits : List Nat) : Nat :=
  if lay = 0 then topDispatchPenalty digits else 0

theorem safeZeroCopy_digit {lay : Layer} {digits : List Nat} {i : Nat}
    (h : safeZeroCopy lay digits i) : digits.getD i 0 = maxDigit lay i := h.1

theorem safeZeroCopy_first (lay : Layer) (digits : List Nat) :
    safeZeroCopy lay digits 0 ↔ digits.getD 0 0 = maxDigit lay 0 := by
  simp [safeZeroCopy]

theorem safeZeroCopy_second_lower {lay : Layer} (hl : lay ≠ 0) (digits : List Nat) :
    safeZeroCopy lay digits 1 ↔ digits.getD 1 0 = maxDigit lay 1 := by
  simp [safeZeroCopy, hl]

def producerFloor (lay : Layer) : Nat := ![21, 10, 9, 9] lay
def wordCredit (lay : Layer) (digits : List Nat) : Nat :=
  ((List.range (chainCount lay)).filter fun i => digits.getD i 0 + 1 = maxDigit lay i).length
/-- Producer-only restriction; includes the checksum and leaves the broad decoder unchanged. -/
def producerZeroBound (lay : Layer) (digits : List Nat) : Prop :=
  lay = 0 ∨ (digits.filter (· = 0)).length ≤ 5
instance (lay : Layer) (digits : List Nat) : Decidable (producerZeroBound lay digits) := by
  unfold producerZeroBound; infer_instance
/-- Two stride-512 columns need rank five; the other stride-1024 columns need rank three. -/
def producerRankFloor (i : Nat) : Nat := if i = 1 ∨ i = 8 then 5 else 3
/-- Producer-only table-address safety for the mixed-stride dispatch. -/
def producerRankBound (lay : Layer) (answer : Digest) : Prop :=
  lay = 0 ∨ ∀ i : Fin 14, producerRankFloor i.val ≤ lowerWord answer / 2^(9*i.val) % 512
instance (lay : Layer) (answer : Digest) : Decidable (producerRankBound lay answer) := by
  unfold producerRankBound; infer_instance
def producerDecode (lay : Layer) (answer : Digest) : Option (List Nat) :=
  match decode lay answer with
  | some digits => if producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits ∧ producerZeroBound lay digits ∧ producerRankBound lay answer then some digits else none
  | none => none
def lowerSearchLimit : Nat := 2 ^ 21
def searchLimit (lay : Layer) : Nat := if lay = 0 then counterLimit else lowerSearchLimit
/-- The verifier accepts every 32-bit counter: its window is the whole `BitVec 32` range, so the layer check
never rejects. The signer still searches `searchLimit`. -/
def verifyWindow : Nat := 2 ^ 32
theorem ctr_not_ge_verifyWindow (c : BitVec 32) : ¬c.toNat ≥ verifyWindow := by
  unfold verifyWindow; exact Nat.not_le.mpr c.isLt
/-- The top layer selects the low half when its high bit is set. Lower layers
select it when both reserved bits are set; otherwise the high half is selected. -/
def encodingAnswer (lay : Layer) (answer : HashOutput) : Digest :=
  if lay = 0 then TopDualHalf.select answer else DualHalf.select answer

def encodingHash (lay : Layer) (input : HashInput) : M Digest :=
  encodingAnswer lay <$> publicHash input

theorem encodingHash_top (input : HashInput) :
    encodingHash 0 input = TopDualHalf.select <$> publicHash input := rfl

theorem encodingAnswer_lower_low (lay : Layer) (hl : lay ≠ 0) (answer : HashOutput)
    (hspare : lowerSpare (answer.extractLsb' 0 128)) :
    encodingAnswer lay answer = answer.extractLsb' 0 128 := by
  simp [encodingAnswer, hl, DualHalf.select, DualHalf.selectPair, hspare]

theorem encodingAnswer_lower_high (lay : Layer) (hl : lay ≠ 0) (answer : HashOutput)
    (hspare : ¬lowerSpare (answer.extractLsb' 0 128)) :
    encodingAnswer lay answer = answer.extractLsb' 128 128 := by
  simp [encodingAnswer, hl, DualHalf.select, DualHalf.selectPair, hspare]

theorem encodingHash_congr (lay : Layer) {x y : HashInput} (h : pad64 x = pad64 y) :
    encodingHash lay x = encodingHash lay y := by
  unfold encodingHash publicHash
  rw [h]

theorem encodingHash_bind {β : Type} (lay : Layer) (input : HashInput) (f : Digest → M β) :
    encodingHash lay input >>= f = publicHash input >>= fun a => f (encodingAnswer lay a) := by
  unfold encodingHash
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

def layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    Nat → M (Option (BitVec 32 × List Nat))
  | 0 => pure none
  | fuel + 1 => do
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
      match producerDecode lay answer with
      | none => layerCounterSearch lay tree leaf msg (counter + 1) fuel
      | some digits => pure (some (BitVec.ofNat 32 counter, digits))
def lowerOrdinal (lay : Layer) (leaf chain : Nat) : Nat := chainCount lay * leaf + chain
def lowerSeedHeader (lay : Layer) (tree pair : Nat) : BitVec 128 := header 0 lay.val tree pair 0
def lowerSeedPair (lay : Layer) (tree pair : Nat) : M (Digest × Digest) := privatePair 0 lay.val tree pair 0
def buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    M ((Digest × List Digest) × Digest) := do
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest × Digest) i => do
      let (seed, carry) ← packedSecret (lowerSeedPair lay tree) (lowerOrdinal lay leaf i) state.2.2
      let digit := digits.getD i 0
      let value ← SigGolfCandidate.T3.chain lay tree leaf i 0 digit seed
      let last ← SigGolfCandidate.T3.chain lay tree leaf i digit (maxDigit lay i - digit) value
      pure (state.1 ++ [last], state.2.1 ++ [value], carry)) ([], [], carry)
  let root ← SigGolfCandidate.T3.leafHash lay tree leaf state.1
  pure ((root, state.2.1), state.2.2)
/-- Levels `0..h-1` of a lower tree (C2: halves by `lowerLevel`; the tag argument is kept for the callers' text). -/
def buildLevelsBelow (_tag lay tree h : Nat) (leaves : List Digest) : M (List (List Digest)) :=
  (List.range' 1 (h - 1)).foldlM (fun levels level => do
    let nodes ← lowerLevel lay tree h level (levels.getD (level - 1) [])
    pure (levels ++ [nodes])) [leaves]
/-! ### B4 lower arithmetic seeds: a degree-7 GF(2^128) family per leaf.
Coefficient `j` of leaf `leaf` has ordinal `8 * leaf + j`; the even coefficient count
uses four private pairs per leaf without a carry. The producer reveals at most five seeds.
The seed of chain `i` is `familyEval coefs (lowerPoint i)`, `lowerPoint i = i + 1`. -/
def lowerCoefCount : Nat := 8
def lowerCoefOrdinal (leaf j : Nat) : Nat := lowerCoefCount * leaf + j
def lowerPoint (chain : Nat) : Nat := chain + 1
def lowerCoefs (lay : Layer) (tree leaf : Nat) (carry : Digest) : M (List Digest × Digest) :=
  (List.range lowerCoefCount).foldlM (fun (state : List Digest × Digest) j => do
    let (coef, carry) ← packedSecret (lowerSeedPair lay tree) (lowerCoefOrdinal leaf j) state.2
    pure (state.1 ++ [coef], carry)) ([], carry)
def lowerFamilySeed (coefs : List Digest) (chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval coefs (lowerPoint chain)
def buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    M ((Digest × List Digest) × Digest) := do
  let (coefs, carry) ← lowerCoefs lay tree leaf carry
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let value ← chainW lay tree leaf i 0 digit (lowerFamilySeed coefs i)
      let last ← chainW lay tree leaf i digit (maxDigit lay i - digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  let root ← lowerLeafHash lay tree leaf state.1
  pure ((root, state.2), carry)
/-- Lower tree of layer `lay ≥ 1` (stage B: leaves built by `buildLeafPF`, the family carry threaded across leaves).
`buildLeafP` (per-chain packed seeds) is kept for the machine proofs of the pre-stage-B sign image. -/
def buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × Digest) leaf => do
      let ((root, values), carry) ← buildLeafPF lay tree leaf (if leaf = selected then digits else []) state.2.2
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), carry)) ([], [], 0)
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure (levels, state.2.1)
def topLevel (lay : Layer) : Fin (height lay) :=
  ⟨height lay - 1, by fin_cases lay <;> decide⟩
def topPair (lay : Layer) (levels : List (List Digest)) : Digest × Digest :=
  ((levels.getD (height lay - 1) []).getD 0 0, (levels.getD (height lay - 1) []).getD 1 0)
def signLayersBC (cache : Cache) (index : Nat) : Nat → LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreeP lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := topPair lay levels
        let some previous ← signLayersBC cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))
structure Opening where
  values : Fin 6 → Digest
  path : Fin 7 → Digest
structure Signature where
  rho : Digest
  openings : Coord → Opening
  layers : (lay : Layer) → LayerSignature lay
structure Witness where
  signature : Signature
  digestCounter : BitVec 32
  counters : Layer → BitVec 32
def toT3Signature (sig : Signature) : SigGolfCandidate.T3.Signature :=
  ⟨sig.rho, fun _ => 0, fun _ => 0, sig.layers⟩
def toT3Witness (w : Witness) : SigGolfCandidate.T3.Witness :=
  ⟨toT3Signature w.signature, w.digestCounter, w.counters⟩
def recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (Digest × Digest) := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainW lay tree leaf i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)
  let value ← lowerLeafHash lay tree leaf ends
  let top ← (List.finRange (height lay - 1)).foldlM (fun value j => do
    let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    lowerNodeHash lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2) value
  let other := (sig.layers lay).path (topLevel lay)
  pure (if leaf / 2 ^ (height lay - 1) % 2 = 0 then (top, other) else (other, top))
/-- Lower dispatch is defined only at ranks allocated in the absolute-address table. -/
def lowerRankGood (answer : Digest) : Prop :=
  ∀ i : Fin 14, producerRankFloor i.val ≤ lowerWord answer / 2 ^ (9 * i.val) % 512
instance (answer : Digest) : Decidable (lowerRankGood answer) := by
  unfold lowerRankGood
  infer_instance
def lowerFirstBad (answer : Digest) : Nat :=
  ((List.range 14).find? (fun i => decide
    (lowerWord answer / 2 ^ (9 * i) % 512 < producerRankFloor i))).getD 14
def lowerGuardedRun {α : Type} (run : Nat → M Digest) (finish : M α) (answer : Digest) : M (Option α) :=
  if lowerRankGood answer then some <$> finish
  else do
    let _ ← (List.range (3 * lowerFirstBad answer)).mapM run
    pure none
def recoverLayerPairGuard (sig : Signature) (index : Nat) (lay : Layer) (answer : Digest)
    (digits : List Nat) : M (Option (Digest × Digest)) :=
  lowerGuardedRun
    (fun i => chainW lay (route index lay).2 (route index lay).1 i
      (digits.getD i 0) (maxDigit lay i - digits.getD i 0) ((sig.layers lay).values ⟨i % chainCount lay,
        Nat.mod_lt _ (by fin_cases lay <;> decide)⟩))
    (recoverLayerPair sig index lay digits) answer
def topGroupBad (answer : Digest) (i : Nat) : Bool :=
  decide (i % 3 = 0 ∧ i < 51 ∧ 125 ≤ topCode answer / 2 ^ (7 * (i / 3)) % 128)
def topDecodeStep (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest)
    (state : Option (List Digest)) (i : Fin (chainCount 0)) : M (Option (List Digest)) := do
  let some ends := state | pure none
  if topGroupBad answer i.val then return none
  let value ← run i ((dataDigits 0 answer).getD i.val 0)
  pure (some (ends ++ [value]))
def topDecodeRun (run : Fin (chainCount 0) → Nat → M Digest) (finish : List Digest → M Digest)
    (answer : Digest) : M (Option Digest) := do
  if answer.toNat ≥ 2 ^ encodedBits 0 then return none
  let some ends ← (List.finRange (chainCount 0)).foldlM (topDecodeStep run answer) (some []) | pure none
  if (dataDigits 0 answer).sum ≠ target 0 then return none
  some <$> finish ends
def verifyTop (sig : Signature) (index : Nat) (answer : Digest) : M (Option Digest) :=
  let leaf := (route index 0).1
  let tree := (route index 0).2
  topDecodeRun
    (fun i digit => SigGolfCandidate.T3.chain 0 tree leaf i.val digit (maxDigit 0 i.val - digit)
      ((sig.layers 0).values i))
    (fun ends => do
      let value ← SigGolfCandidate.T3.leafHash 0 tree leaf ends
      (List.finRange (height 0)).foldlM (fun value j => do
        let other := (sig.layers 0).path j
        let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        nodeHash 3 (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2)
        value)
    answer
def expandLayersBC (sig : Signature) (index : Nat) :
    Nat → LayerMsg → M (Option (Digest × List (BitVec 32)))
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits) ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay) | pure none
      if n = 0 then
        let root ← recoverLayer (toT3Signature sig) index lay digits
        pure (some (root, [counter]))
      else
        let pair ← recoverLayerPair sig index lay digits
        let some (root, counters) ← expandLayersBC sig index n (.pair pair.1 pair.2) | pure none
        pure (some (root, counters ++ [counter]))
def verifyLayersBC (w : Witness) (index : Nat) : Nat → LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg counter)
      if n = 0 then verifyTop w.signature index answer
      else do
        let some digits := decode lay answer | pure none
        let some pair ← recoverLayerPairGuard w.signature index lay answer digits | pure none
        verifyLayersBC w index n (.pair pair.1 pair.2)
def signPayload (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_, output) ← digestSearch rho message 0 attemptLimit | pure none
  let index := digestIndex output
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List (Digest × Digest)) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinateF index coord selected (rank output coord) (prevPair ftsStart state.2)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening],
        state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])) ([], [])
  let top := prevPair ftsStart state.2
  let some layers ← signLayersBC cache index 4 (.pair top.1 top.2) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
def sign (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message
def serializeOpening (opened : Opening) : HashInput :=
  (List.ofFn opened.values).flatMap (bytesLE 16) ++
    (List.ofFn opened.path).flatMap (bytesLE 16)
def serialize (sig : Signature) : HashInput :=
  bytesLE 16 sig.rho ++ (List.ofFn sig.openings).flatMap serializeOpening ++
    (List.ofFn fun lay => serializeLayer (sig.layers lay)).flatten
def recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput) (coord : Coord)
    (prev : Digest × Digest) : M (Digest × Digest) := do
  let selected := child output coord
  let word := rank output coord
  let ends ← (List.finRange 6).mapM fun i =>
    let deficit := wordDigit word i
    chain index coord.val selected.val i.val (4 - deficit) deficit ((sig.openings coord).values i)
  let root ← leafHashP index coord.val selected.val prev.1 ends
  let value ← (List.finRange 5).foldlM
    (fun value level => do
      let other := (sig.openings coord).path (Fin.castLE (by decide) level)
      let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      wctNodeHash coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1))
        pair.1 pair.2) root
  let other5 := (sig.openings coord).path 5
  let pair5 := if selected.val / 2 ^ 5 % 2 = 0 then (value, other5) else (other5, value)
  let top ← wctTopHash coord.val index (2 + selected.val / 2 ^ 6) pair5.1 prev.2 pair5.2
  let other := (sig.openings coord).path 6
  pure (if selected.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
/-- Nested FTS (r1-1): run the coordinates in order, each with the previous top pair as pads; return the last pair
(the L3 message). -/
def recoverFtsFrom (start : Digest × Digest) (sig : Signature) (index : Nat) (output : HashOutput) :
    M (Digest × Digest) := do
  let pairs ← (List.finRange 9).foldlM (fun (pairs : List (Digest × Digest)) coord => do
    let pair ← recoverCoordinate sig index output coord (prevPair start pairs)
    pure (pairs ++ [pair])) []
  pure (prevPair start pairs)
def recoverFts (sig : Signature) (index : Nat) (output : HashOutput) : M (Digest × Digest) :=
  recoverFtsFrom ftsStart sig index output
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := digestIndex output
  let top ← recoverFts sig index output
  let some (root, counters) ← expandLayersBC sig index 4 (.pair top.1 top.2) | pure none
  if root ≠ pk then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !admissible output then return false
  let index := digestIndex output
  let top ← recoverFts w.signature index output
  let some root ← verifyLayersBC w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def keygen := SigGolfCandidate.T3.keygen
end ClaudeWCT.WCT9
