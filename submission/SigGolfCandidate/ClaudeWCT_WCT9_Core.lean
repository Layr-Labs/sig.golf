import SigGolfCandidate.T3_Core
import SigGolfCandidate.T3_Nonbinary_LowerLayout
import SigGolfCandidate.ClaudeWCT_WCT9_Codebook
import SigGolfCandidate.ClaudeWCT_Arith_GF128

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
def jointCap : Nat := 789
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
/-- Nested FTS (r1-1): one less saved instruction on the 54 children whose level-4 fold reused `a2`. -/
def childSaveTable : List Nat :=
  [0,2,2,3,2,4,4,4,2,4,4,5,3,5,5,5,0,2,2,4,1,3,3,4,1,3,3,4,2,4,4,4,0,2,2,3,1,3,3,4,1,3,3,5,2,5,5,5,1,3,3,4,2,4,4,4,2,4,4,4,3,4,4,4,0,2,2,3,2,4,4,4,2,4,4,5,3,5,5,5,0,2,2,4,1,3,3,4,1,3,3,4,2,4,4,4,0,2,2,3,1,3,3,4,1,3,3,5,2,5,5,5,1,3,3,4,2,4,4,4,2,4,4,4,3,4,4,4]
def maxChildSave : Nat := 5
def childSave (c : Nat) : Nat := childSaveTable.getD (c % 128) 0
def childExtra (c : Child) : Nat := maxChildSave - childSave c.val
theorem childSaveTable_le : ∀ i, i < 128 → childSaveTable.getD i 0 ≤ maxChildSave := by decide
theorem childSave_le (c : Nat) : childSave c ≤ maxChildSave :=
  childSaveTable_le (c % 128) (Nat.mod_lt _ (by decide))
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
/-- FTS chain word. C4: coordinate nibble `coord + 1` (every FTS word is `≥ 2 ^ 16`, above every top label). -/
def ftsChainLow (index coord selected chain step : Nat) : Nat :=
  0x80 + chain % 8 * 2 ^ 2 + step % 4 * 2 ^ 8 + (coord + 1) % 16 * 2 ^ 16 + selected % 128 * 2 ^ 20 +
    index % 2 ^ 31 * 2 ^ 27
def ftsChainHeaderP (index coord selected chain step : Nat) (high : BitVec 64) : BitVec 128 :=
  high ++ BitVec.ofNat 64 (ftsChainLow index coord selected chain step)
def ftsChainHeader (index coord selected chain step : Nat) : BitVec 128 :=
  ftsChainHeaderP index coord selected chain step 0
def chainInput (index coord selected chain step : Nat) (value : Digest) : HashInput :=
  zero16 ++ bytesLE 16 (ftsChainHeader index coord selected chain step) ++
    zero16 ++ bytesLE 16 value
/-- Witness stack (charge 86): FTS chains 1 and 3 are value-first ("G") chains (`value | header | 0 | 0`); their
interior steps (`step < 3`) keep the HIGH half, the terminal step 3 the low half. -/
def ftsIsG (i : Nat) : Bool := decide (i = 1) || decide (i = 3)
def ftsChainHigh (i step : Nat) : Bool := ftsIsG i && decide (step < 3)
/-- FTS step input of the paired scheme: `chainInput` (F) or `value | header | 0 | 0` (G). -/
def ftsChainInputW (index coord selected i step : Nat) (value : Digest) : HashInput :=
  if ftsIsG i then bytesLE 16 value ++ bytesLE 16 (ftsChainHeader index coord selected i step) ++ zero16 ++ zero16
  else chainInput index coord selected i step value
/-- FTS chain (witness stack: G chains 1, 3 through `ftsChainInputW`/`ftsChainHigh`). -/
def chain (index coord selected i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => projHash (ftsChainHigh i step) (ftsChainInputW index coord selected i step value)) value
/-- FTS leaf word. C4: coordinate nibble `coord + 1`. -/
def ftsLeafLow (index coord selected : Nat) : Nat :=
  1 + 6 * 2 ^ 8 + (coord + 1) % 16 * 2 ^ 16 + selected % 128 * 2 ^ 20 + index % 2 ^ 31 * 2 ^ 27
theorem ftsChainLow_ge {coord : Nat} (hc : coord < 15) (index selected chain step : Nat) :
    2 ^ 16 ≤ ftsChainLow index coord selected chain step := by
  unfold ftsChainLow; rw [Nat.mod_eq_of_lt (show coord + 1 < 16 by omega)]; omega
theorem ftsLeafLow_ge {coord : Nat} (hc : coord < 15) (index selected : Nat) :
    2 ^ 16 ≤ ftsLeafLow index coord selected := by
  unfold ftsLeafLow; rw [Nat.mod_eq_of_lt (show coord + 1 < 16 by omega)]; omega
def ftsLeafHeader (index coord selected : Nat) : BitVec 128 :=
  0#64 ++ BitVec.ofNat 64 (ftsLeafLow index coord selected)
/-- FTS child leaf (campaign T8): `end0 | header | zero16 | end1..end5` (128 bytes, two blocks). The zero slot
after the header is a witness pad in the padded verifier; the honest value is zero. -/
def leafHash (index coord selected : Nat) (ends : List Digest) : M Digest :=
  shortHash (bytesLE 16 (ends.getD 0 0) ++
    bytesLE 16 (ftsLeafHeader index coord selected) ++ zero16 ++ (ends.drop 1).flatMap (bytesLE 16))
/-- Padded FTS leaf (campaign T8): the leaf with an arbitrary 16-byte value in the pad slot (the padded verifier's
witness pad; `leafHashP_zero`: the honest pad 0 gives `leafHash`). -/
def leafInputP (index coord selected : Nat) (pad : Digest) (ends : List Digest) : HashInput :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (ftsLeafHeader index coord selected) ++ bytesLE 16 pad ++
    (ends.drop 1).flatMap (bytesLE 16)
def leafHashP (index coord selected : Nat) (pad : Digest) (ends : List Digest) : M Digest :=
  shortHash (leafInputP index coord selected pad ends)
theorem bytesLE_zero16 : bytesLE 16 (0 : Digest) = zero16 := by decide
theorem leafHashP_zero (index coord selected : Nat) (ends : List Digest) :
    leafHashP index coord selected 0 ends = leafHash index coord selected ends := by
  unfold leafHashP leafInputP leafHash
  rw [bytesLE_zero16]
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
def wctNodeHash (coord index heap : Nat) (left right : Digest) : M Digest :=
  nodeHash 3 (nodeLayer coord) index heap left right
/-- C4 keeps the low half for every FTS node (`nodeLayer coord ≠ 0`). -/
theorem wctNodeHash_eq_short (coord index heap : Nat) (left right : Digest) :
    wctNodeHash coord index heap left right =
      shortHash (bytesLE 16 left ++ bytesLE 16 (wctNodeHeader coord index heap) ++ zero16 ++ bytesLE 16 right) := by
  unfold wctNodeHash nodeHash
  rw [nodeHalfHigh_of_ne (by simp [nodeLayer]), projHash_false]
  rfl
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
/-- Merkle node tweak of the current scheme: the top tree keeps `nodeTweak 3 0` (C4: the one-word label
`0#64 ++ topNodeWord heap`), the lower trees use `lowerTweak`. -/
def merkleTweak (lay tree heap : Nat) : BitVec 128 :=
  if lay = 0 then nodeTweak 3 0 tree heap else lowerTweak lay tree heap
/-- C4: the verifier-written label word of a fold window of layer `lay`: the heap on the top tree, the packed lower node
word on the lower trees. `merkleTweak lay tree heap = 0#64 ++ merkleWord lay tree heap` (`merkleTweak_eq_word`). -/
def merkleWord (lay tree heap : Nat) : BitVec 64 :=
  if lay = 0 then BitVec.ofNat 64 (topNodeWord heap) else lowerNodeWord (lay - 1) tree heap
/-- The used half of a hash output. -/
def halfOf (high : Bool) (output : HashOutput) : Digest :=
  if high then output.extractLsb' 128 128 else output.extractLsb' 0 128
/-- A hash whose used half is selected by `high`. -/
def halfHash (high : Bool) (input : HashInput) : M Digest := if high then highHash input else shortHash input
/-- C2 + C4: heap `heap` of layer `lay` uses the high half (top and lower layers, even heap; the root, heap 1, is
odd). -/
def lowerHigh (lay heap : Nat) : Bool := decide (lay < 4) && decide (heap % 2 = 0)
def lowerHalf (lay heap : Nat) (output : HashOutput) : Digest := halfOf (lowerHigh lay heap) output
def lowerHash (lay heap : Nat) (input : HashInput) : M Digest := halfHash (lowerHigh lay heap) input
/-- Pairing stage 1: the odd chains of the lower layers (1..3) are value-first ("G") chains: their step input is
`value | header | 0 | 0` (header still at bytes 16..32) and every interior step (step < 6) keeps the HIGH half.
Witness stack (charge 86): the even top chains `0, 2, .., 50` (T51) are G chains too (`T3.topIsG`). -/
def isG (lay : Layer) (i : Nat) : Bool :=
  decide (lay ≠ 0) && decide (i % 2 = 1) || decide (lay = 0) && SigGolfCandidate.T3.topIsG i
/-- C3: the last step (step 6) of chain 0 of a lower layer keeps the high half. Pairing stage 1: so does every
interior step (step < 6) of a G chain (`isG`). Witness stack: on the top, every interior step
(`step + 1 < maxDigit 0 i`) of a G chain (`T3.topChainHigh`). -/
def chainHigh (lay : Layer) (i step : Nat) : Bool :=
  decide (lay ≠ 0) && (decide (i = 0) && decide (step = 6) || decide (i % 2 = 1) && decide (step < 6)) ||
    decide (lay = 0) && SigGolfCandidate.T3.topChainHigh i step
/-- Honest chain step input of the current scheme: `T3.chainInput` (F format) or, for a G chain,
`value | header | 0 | 0`. -/
def chainInputW (lay : Layer) (tree leaf i step : Nat) (value : Digest) : HashInput :=
  if isG lay i then bytesLE 16 value ++ bytesLE 16 (SigGolfCandidate.T3.chainHeader lay tree leaf i step) ++
    zero16 ++ zero16
  else SigGolfCandidate.T3.chainInput lay tree leaf i step value
/-- WOTS chain of the current scheme (`T3.chain` with the chain-0 high half and the G chains). -/
def chainW (lay : Layer) (tree leaf i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => halfHash (chainHigh lay i step) (chainInputW lay tree leaf i step value))
    value
/-- Leaf tweak with the witness high word `hi` (honest 0). -/
def leafTweakW (lay : Layer) (tree leaf : Nat) (hi : BitVec 64) : BitVec 128 :=
  hi ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)
/-- Verifier leaf input: every leaf starts with chain 0's end, then the tweak (high word `hi`), then the other ends.
Campaign T51 ("endpad"): the top leaf has the lower shape too (`end_0 | tweak | end_1..end_50`), so the witness pad
`pad` (#938: the top leaf's leading block) is unused on every layer. `leafInputW_zero`: `hi = 0` gives
`T3.leafInput`. -/
def leafInputW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) : HashInput :=
  if lay = 0 then bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (leafTweakW lay tree leaf hi) ++
    (ends.drop 1).flatMap (bytesLE 16)
  else bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (leafTweakW lay tree leaf hi) ++ (ends.drop 1).flatMap (bytesLE 16)
/-- Leaf hash of the current scheme (half by leaf index on every layer; C4: the top included). -/
def leafHashW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) : M Digest :=
  lowerHash lay.val leaf (leafInputW lay tree leaf pad hi ends)
/-- Honest leaf hash of the current scheme. -/
def lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) : M Digest := leafHashW lay tree leaf 0 0 ends
/-- Verifier fold input of a node of layer `lay` (C4: the top included, label `merkleWord`): witness high tweak word
`hp` and pad `pad` (honest 0, 0). -/
def lowerNodeInputP (lay tree heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (hp ++ merkleWord lay tree heap) ++ bytesLE 16 pad ++ bytesLE 16 right
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
theorem lowerHigh_iff (lay heap : Nat) : lowerHigh lay heap = true ↔ lay < 4 ∧ heap % 2 = 0 := by
  simp [lowerHigh]
/-- C4: the top tree uses the high half for even heaps (left children) too. -/
theorem lowerHigh_top (heap : Nat) : lowerHigh 0 heap = decide (heap % 2 = 0) := by simp [lowerHigh]
theorem lowerHigh_top_odd {heap : Nat} (h : heap % 2 = 1) : lowerHigh 0 heap = false := by
  simp [lowerHigh, h]
theorem lowerHigh_top_even {heap : Nat} (h : heap % 2 = 0) : lowerHigh 0 heap = true := by
  simp [lowerHigh, h]
@[simp] theorem lowerHigh_one (lay : Nat) : lowerHigh lay 1 = false := by simp [lowerHigh]
/-- C4: `WCT9.halfHash` is `T3.projHash` (the legacy top tree's half selection). -/
theorem halfHash_eq_projHash (high : Bool) (input : HashInput) : halfHash high input = projHash high input := by
  cases high <;> rfl
theorem halfOf_eq_projHalf (high : Bool) (output : HashOutput) : halfOf high output = projHalf high output := by
  cases high <;> rfl
theorem lowerHigh_top_eq_nodeHalfHigh (heap : Nat) : lowerHigh 0 heap = nodeHalfHigh 3 0 heap := by
  rw [lowerHigh_top, nodeHalfHigh_top]
theorem lowerHigh_top_eq_leafHalfHigh (leaf : Nat) : lowerHigh (0 : Layer).val leaf = leafHalfHigh 0 leaf := by
  rw [show (0 : Layer).val = 0 from rfl, lowerHigh_top, leafHalfHigh_top]
theorem lowerHigh_heap {lay e x : Nat} (he : 1 ≤ e) : lowerHigh lay (2 ^ e + x) = lowerHigh lay x := by
  have : 2 ^ e % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ]; simp
  unfold lowerHigh
  rw [show (2 ^ e + x) % 2 = x % 2 by omega]
/-- Witness stack: the top chains follow `T3.topChainHigh` / `T3.topIsG`. -/
theorem chainHigh_top_eq (i step : Nat) : chainHigh 0 i step = SigGolfCandidate.T3.topChainHigh i step := by
  simp [chainHigh]
theorem isG_top_eq (i : Nat) : isG 0 i = SigGolfCandidate.T3.topIsG i := by simp [isG]
theorem isG_lower {lay : Layer} (hl : lay ≠ 0) (i : Nat) : isG lay i = decide (i % 2 = 1) := by simp [isG, hl]
theorem chainHigh_lower {lay : Layer} (hl : lay ≠ 0) (i step : Nat) :
    chainHigh lay i step = (decide (i = 0) && decide (step = 6) || decide (i % 2 = 1) && decide (step < 6)) := by
  simp [chainHigh, hl]
theorem topIsG_eq_true {i : Nat} : SigGolfCandidate.T3.topIsG i = true ↔ i % 2 = 0 ∧ i ≤ 50 := by
  simp [SigGolfCandidate.T3.topIsG]
theorem topChainHigh_eq_true {i step : Nat} :
    SigGolfCandidate.T3.topChainHigh i step = true ↔ (i % 2 = 0 ∧ i ≤ 50) ∧ (step + 1 < maxDigit 0 i ∨ i = 0) := by
  simp [SigGolfCandidate.T3.topChainHigh, SigGolfCandidate.T3.topIsG]
theorem topChainHigh_of_F {i step : Nat} (h : SigGolfCandidate.T3.topIsG i = false) :
    SigGolfCandidate.T3.topChainHigh i step = false := by
  simp [SigGolfCandidate.T3.topChainHigh, h]
theorem isG_eq_true {lay : Layer} {i : Nat} :
    isG lay i = true ↔ lay ≠ 0 ∧ i % 2 = 1 ∨ lay = 0 ∧ i % 2 = 0 ∧ i ≤ 50 := by
  simp [isG, SigGolfCandidate.T3.topIsG]
/-- Lower-layer form of `isG_eq_true` (the stage-1 statement). -/
theorem isG_eq_true_lower {lay : Layer} {i : Nat} (hl : lay ≠ 0) : isG lay i = true ↔ i % 2 = 1 := by
  simp [isG, hl]
theorem isG_eq_false {lay : Layer} {i : Nat}
    (h : lay ≠ 0 ∧ i % 2 = 0 ∨ lay = 0 ∧ (i % 2 = 1 ∨ 50 < i)) : isG lay i = false := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [isG, h1, h2]
  · subst h1; simp only [isG, SigGolfCandidate.T3.topIsG]; rcases h2 with h2 | h2 <;> simp <;> omega
theorem isG_zero {lay : Layer} (hl : lay ≠ 0) : isG lay 0 = false := isG_eq_false (Or.inl ⟨hl, rfl⟩)
theorem chainHigh_eq_false {lay : Layer} {i step : Nat}
    (h : lay ≠ 0 ∧ ¬ (i = 0 ∧ step = 6) ∧ ¬ (i % 2 = 1 ∧ step < 6) ∨
      lay = 0 ∧ SigGolfCandidate.T3.topChainHigh i step = false) :
    chainHigh lay i step = false := by
  rcases h with ⟨hl, h1, h2⟩ | ⟨hl, h⟩
  · rw [chainHigh_lower hl]
    simp only [Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · by_cases hi : i = 0 <;> simp_all
    · by_cases hi : i % 2 = 1 <;> simp_all
  · subst hl; rw [chainHigh_top_eq, h]
/-- An F chain (`isG = false`) keeps the low half except on C3's step 6 of chain 0. -/
theorem chainHigh_eq_false_F {lay : Layer} {i step : Nat} (hG : isG lay i = false) (h : i ≠ 0 ∨ step ≠ 6) :
    chainHigh lay i step = false := by
  by_cases hl : lay = 0
  · subst hl; rw [isG_top_eq] at hG
    exact chainHigh_eq_false (Or.inr ⟨rfl, topChainHigh_of_F hG⟩)
  · have : i % 2 = 0 := by simp [isG, hl] at hG; omega
    exact chainHigh_eq_false (Or.inl ⟨hl, by omega, by omega⟩)
/-- The terminal step (step 6) of a chain other than chain 0 keeps the low half. -/
theorem chainHigh_six {lay : Layer} {i : Nat} (hi : i ≠ 0) : chainHigh lay i 6 = false := by
  by_cases hl : lay = 0
  · subst hl
    refine chainHigh_eq_false (Or.inr ⟨rfl, ?_⟩)
    simp only [SigGolfCandidate.T3.topChainHigh, Bool.and_eq_false_iff, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    refine Or.inr ⟨?_, hi⟩
    unfold SigGolfCandidate.T3.maxDigit
    rw [if_pos rfl]; split_ifs <;> omega
  · exact chainHigh_eq_false (Or.inl ⟨hl, by omega, by omega⟩)
theorem chainHigh_eq_true {lay : Layer} {i step : Nat} :
    chainHigh lay i step = true ↔ lay ≠ 0 ∧ (i = 0 ∧ step = 6 ∨ i % 2 = 1 ∧ step < 6) ∨
      lay = 0 ∧ (i % 2 = 0 ∧ i ≤ 50) ∧ (step + 1 < maxDigit 0 i ∨ i = 0) := by
  simp [chainHigh, SigGolfCandidate.T3.topChainHigh, SigGolfCandidate.T3.topIsG]
/-- On an F chain the high steps are exactly C3's. -/
theorem chainHigh_eq_true_F {lay : Layer} {i step : Nat} (hG : isG lay i = false) :
    chainHigh lay i step = true ↔ lay ≠ 0 ∧ i = 0 ∧ step = 6 := by
  rw [chainHigh_eq_true]
  constructor
  · rintro (⟨hl, h | h⟩ | ⟨hl, h, -⟩)
    · exact ⟨hl, h⟩
    · exact absurd (isG_eq_true.mpr (Or.inl ⟨hl, h.1⟩)) (by simp [hG])
    · exact absurd (isG_eq_true.mpr (Or.inr ⟨hl, h⟩)) (by simp [hG])
  · rintro ⟨hl, h⟩; exact Or.inl ⟨hl, Or.inl h⟩
theorem chainInputW_F {lay : Layer} {i : Nat} (hG : isG lay i = false) (tree leaf step : Nat) (value : Digest) :
    chainInputW lay tree leaf i step value = SigGolfCandidate.T3.chainInput lay tree leaf i step value := by
  simp [chainInputW, hG]
/-- Witness stack: the top step input is `T3.topChainInput` (tree 0). -/
theorem chainInputW_top_eq (leaf i step : Nat) (value : Digest) :
    chainInputW 0 0 leaf i step value = SigGolfCandidate.T3.topChainInput leaf i step value := by
  unfold chainInputW SigGolfCandidate.T3.topChainInput; rw [isG_top_eq]
theorem chainInputW_G {lay : Layer} {i : Nat} (hG : isG lay i = true) (tree leaf step : Nat) (value : Digest) :
    chainInputW lay tree leaf i step value = bytesLE 16 value ++
      bytesLE 16 (SigGolfCandidate.T3.chainHeader lay tree leaf i step) ++ zero16 ++ zero16 := by
  simp [chainInputW, hG]
theorem chainInputW_length (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    (chainInputW lay tree leaf i step value).length = 64 := by
  unfold chainInputW SigGolfCandidate.T3.chainInput
  split <;> simp [SphincsSecurity.bytesLE_length, zero16]
theorem chainInputW_padded (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    pad64 (chainInputW lay tree leaf i step value) = chainInputW lay tree leaf i step value := by
  simp [pad64, chainInputW_length]
theorem chainInputW_header (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    ((chainInputW lay tree leaf i step value).drop 16).take 16 =
      bytesLE 16 (SigGolfCandidate.T3.chainHeader lay tree leaf i step) := by
  unfold chainInputW SigGolfCandidate.T3.chainInput
  split <;> simp [zero16, List.append_assoc, SphincsSecurity.bytesLE_length]
theorem foldlM_congr_of_mem {α β : Type} {m : Type → Type} [Monad m] (f g : β → α → m β) :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldlM f init = l.foldlM g init
  | [], _, _ => rfl
  | x :: xs, init, h => by
      simp only [List.foldlM_cons]
      rw [h x List.mem_cons_self]
      congr 1; funext b
      exact foldlM_congr_of_mem f g xs b (fun y hy => h y (List.mem_cons_of_mem _ hy))
/-- `chainW` is `T3.chain` when no step of the run keeps the high half. -/
theorem chainW_of_low {lay : Layer} {i start count : Nat} (hG : isG lay i = false)
    (h : ∀ step, start ≤ step → step < start + count → chainHigh lay i step = false)
    (tree leaf : Nat) (value : Digest) :
    chainW lay tree leaf i start count value = SigGolfCandidate.T3.chain lay tree leaf i start count value := by
  unfold chainW SigGolfCandidate.T3.chain
  apply foldlM_congr_of_mem
  intro step hs b
  rw [List.mem_range'_1] at hs
  rw [h step hs.1 hs.2, chainInputW_F hG]; rfl
/-- Witness stack: the top chain of the current scheme is `T3.topChain` (tree 0). -/
theorem chainW_top_eq (leaf i start count : Nat) (value : Digest) :
    chainW 0 0 leaf i start count value = SigGolfCandidate.T3.topChain leaf i start count value := by
  unfold chainW SigGolfCandidate.T3.topChain
  apply foldlM_congr_of_mem
  intro step _ b
  rw [chainHigh_top_eq, chainInputW_top_eq, halfHash_eq_projHash]
/-- A top F chain (odd, or `> 50`) is `T3.chain`. -/
theorem chainW_top_F {i : Nat} (hG : SigGolfCandidate.T3.topIsG i = false) (tree leaf start count : Nat)
    (value : Digest) :
    chainW 0 tree leaf i start count value = SigGolfCandidate.T3.chain 0 tree leaf i start count value :=
  chainW_of_low (by rw [isG_top_eq, hG]) (fun _ _ _ => by rw [chainHigh_top_eq, topChainHigh_of_F hG])
    tree leaf value
/-- An F chain other than chain 0 is `T3.chain`. -/
theorem chainW_ne_zero {lay : Layer} {i : Nat} (hi : i ≠ 0) (hG : isG lay i = false)
    (tree leaf start count : Nat) (value : Digest) :
    chainW lay tree leaf i start count value = SigGolfCandidate.T3.chain lay tree leaf i start count value :=
  chainW_of_low hG (fun _ _ _ => chainHigh_eq_false_F hG (Or.inl hi)) tree leaf value
theorem chainW_add (lay : Layer) (tree leaf i start a b : Nat) (value : Digest) :
    chainW lay tree leaf i start (a + b) value =
      (chainW lay tree leaf i start a value >>= chainW lay tree leaf i (start + a) b) := by
  unfold chainW
  rw [← List.range'_append_1, List.foldlM_append]
/-! #### Witness stack: FTS G chains -/
theorem ftsIsG_eq_true {i : Nat} : ftsIsG i = true ↔ i = 1 ∨ i = 3 := by simp [ftsIsG]
theorem ftsChainHigh_eq_true {i step : Nat} : ftsChainHigh i step = true ↔ (i = 1 ∨ i = 3) ∧ step < 3 := by
  simp [ftsChainHigh, ftsIsG]
theorem ftsChainHigh_of_F {i step : Nat} (h : ftsIsG i = false) : ftsChainHigh i step = false := by
  simp [ftsChainHigh, h]
theorem ftsChainHigh_three (i : Nat) : ftsChainHigh i 3 = false := by simp [ftsChainHigh]
theorem ftsChainInputW_F {i : Nat} (hG : ftsIsG i = false) (index coord selected step : Nat) (value : Digest) :
    ftsChainInputW index coord selected i step value = chainInput index coord selected i step value := by
  simp [ftsChainInputW, hG]
theorem ftsChainInputW_G {i : Nat} (hG : ftsIsG i = true) (index coord selected step : Nat) (value : Digest) :
    ftsChainInputW index coord selected i step value = bytesLE 16 value ++
      bytesLE 16 (ftsChainHeader index coord selected i step) ++ zero16 ++ zero16 := by
  simp [ftsChainInputW, hG]
theorem ftsChainInputW_length (index coord selected i step : Nat) (value : Digest) :
    (ftsChainInputW index coord selected i step value).length = 64 := by
  unfold ftsChainInputW chainInput
  split <;> simp [SphincsSecurity.bytesLE_length, zero16]
theorem ftsChainInputW_padded (index coord selected i step : Nat) (value : Digest) :
    pad64 (ftsChainInputW index coord selected i step value) = ftsChainInputW index coord selected i step value := by
  simp [pad64, ftsChainInputW_length]
/-- An FTS F chain (`ftsIsG = false`, chains 0, 2, 4, 5) is the stage-1 short-hash chain. -/
theorem chain_F {i : Nat} (hG : ftsIsG i = false) (index coord selected start count : Nat) (value : Digest) :
    chain index coord selected i start count value =
      (List.range' start count).foldlM
        (fun value step => shortHash (chainInput index coord selected i step value)) value := by
  unfold chain
  apply foldlM_congr_of_mem
  intro step _ b
  rw [ftsChainHigh_of_F hG, ftsChainInputW_F hG]; rfl
theorem chain_add (index coord selected i start a b : Nat) (value : Digest) :
    chain index coord selected i start (a + b) value =
      (chain index coord selected i start a value >>= chain index coord selected i (start + a) b) := by
  unfold chain
  rw [← List.range'_append_1, List.foldlM_append]
theorem leafInputW_zero (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafInputW lay tree leaf 0 0 ends = SigGolfCandidate.T3.leafInput lay tree leaf ends := by
  unfold leafInputW leafTweakW SigGolfCandidate.T3.leafInput leafTweak
  split
  · rfl
  · rfl
theorem lowerLeafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    lowerLeafHash lay tree leaf ends = lowerHash lay.val leaf (SigGolfCandidate.T3.leafInput lay tree leaf ends) := by
  unfold lowerLeafHash leafHashW; rw [leafInputW_zero]
theorem lowerLeafHash_top (tree leaf : Nat) (ends : List Digest) :
    lowerLeafHash 0 tree leaf ends = SigGolfCandidate.T3.leafHash 0 tree leaf ends := by
  rw [lowerLeafHash_eq]; unfold lowerHash SigGolfCandidate.T3.leafHash
  rw [lowerHigh_top_eq_leafHalfHigh, halfHash_eq_projHash]
/-- C4: the top leaf keeps the high half for an even leaf index. -/
theorem leafHashW_top (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    leafHashW 0 tree leaf pad hi ends = halfHash (decide (leaf % 2 = 0)) (leafInputW 0 tree leaf pad hi ends) := by
  unfold leafHashW lowerHash; rw [show (0 : Layer).val = 0 from rfl, lowerHigh_top]
theorem lowerTweak_low (lay tree heap : Nat) :
    (lowerTweak lay tree heap).extractLsb' 0 64 = hyperWord (lay - 1) tree + BitVec.ofNat 64 (lowerK + heap) := by
  unfold lowerTweak lowerNodeWord; exact BitVec.extractLsb'_append_eq_right
theorem lowerTweak_high (lay tree heap : Nat) : (lowerTweak lay tree heap).extractLsb' 64 64 = 0 := by
  unfold lowerTweak; exact BitVec.extractLsb'_append_eq_left
@[simp] theorem merkleTweak_top (tree heap : Nat) : merkleTweak 0 tree heap = nodeTweak 3 0 tree heap := by
  simp [merkleTweak]
@[simp] theorem merkleWord_top (tree heap : Nat) : merkleWord 0 tree heap = BitVec.ofNat 64 (topNodeWord heap) := by
  simp [merkleWord]
theorem merkleWord_lower {lay : Nat} (h : lay ≠ 0) (tree heap : Nat) :
    merkleWord lay tree heap = lowerNodeWord (lay - 1) tree heap := by
  simp [merkleWord, h]
theorem merkleTweak_eq_word (lay tree heap : Nat) : merkleTweak lay tree heap = 0#64 ++ merkleWord lay tree heap := by
  unfold merkleTweak merkleWord
  split
  · simp [nodeTweak]
  · rfl
/-- C4: the low word of a top node tweak is the label `topNodeWord heap`. -/
theorem merkleTweak_top_low (tree heap : Nat) :
    (merkleTweak 0 tree heap).extractLsb' 0 64 = BitVec.ofNat 64 (topNodeWord heap) := by
  rw [merkleTweak_eq_word, merkleWord_top]; exact BitVec.extractLsb'_append_eq_right
theorem merkleTweak_top_high (tree heap : Nat) : (merkleTweak 0 tree heap).extractLsb' 64 64 = 0 := by
  rw [merkleTweak_eq_word]; exact BitVec.extractLsb'_append_eq_left
/-- C4: the top fold input (one-word label `topNodeWord heap`, witness high word `hp`, witness pad `pad`). -/
theorem lowerNodeInputP_top (tree heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) :
    lowerNodeInputP 0 tree heap left hp pad right = bytesLE 16 left ++
      bytesLE 16 (hp ++ BitVec.ofNat 64 (topNodeWord heap)) ++ bytesLE 16 pad ++ bytesLE 16 right := by
  unfold lowerNodeInputP; rw [merkleWord_top]
theorem merkleTweak_lower {lay : Nat} (h : lay ≠ 0) (tree heap : Nat) :
    merkleTweak lay tree heap = lowerTweak lay tree heap := by
  simp [merkleTweak, h]
/-- C4: zero pads give the honest node input on every layer (the top included). -/
theorem lowerNodeInputP_zero' (lay tree heap : Nat) (left right : Digest) :
    lowerNodeInputP lay tree heap left 0 0 right = merkleNodeInput lay tree heap left right := by
  unfold lowerNodeInputP merkleNodeInput
  rw [merkleTweak_eq_word, show bytesLE 16 (0 : Digest) = zero16 by decide]
  try rfl
theorem lowerNodeInputP_zero {lay : Nat} (_h : lay ≠ 0) (tree heap : Nat) (left right : Digest) :
    lowerNodeInputP lay tree heap left 0 0 right = merkleNodeInput lay tree heap left right :=
  lowerNodeInputP_zero' lay tree heap left right
theorem lowerNodeHash_eqP' (lay tree heap : Nat) (left right : Digest) :
    lowerNodeHash lay tree heap left right = lowerNodeHashP lay tree heap left 0 0 right := by
  unfold lowerNodeHash lowerNodeHashP; rw [lowerNodeInputP_zero']
theorem lowerNodeHash_eqP {lay : Nat} (_h : lay ≠ 0) (tree heap : Nat) (left right : Digest) :
    lowerNodeHash lay tree heap left right = lowerNodeHashP lay tree heap left 0 0 right :=
  lowerNodeHash_eqP' lay tree heap left right
/-- C4: the honest top fold of the current scheme is the legacy `T3.nodeHash 3 0` (both in C4 form). -/
theorem lowerNodeHash_top (tree heap : Nat) (left right : Digest) :
    lowerNodeHash 0 tree heap left right = nodeHash 3 0 tree heap left right := by
  unfold lowerNodeHash lowerHash merkleNodeInput nodeHash
  rw [lowerHigh_top_eq_nodeHalfHigh, merkleTweak_top, halfHash_eq_projHash]
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
/-- Heap of an FTS coordinate. Heaps `4..127` are low-half node hashes with a zero pad; heaps 2 and 3 are
`wctTopHash` with pad `padR` (nested FTS r1-1). -/
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
/-! ### C1 (FTS Merkle half-swap) for the paired forest
`ftsHighHeap heap`: the FTS heaps whose value is the HIGH 16 bytes of their hash output, i.e. every even heap
`16..255` (the left inputs of the four packed fold windows, including the leaves `128 + p` of even physical
children `p`) and, as on the unpaired line, the top pair `heap < 4`. The paired forest
(`SigGolfCandidate.Research.SharedForest`) applies this rule to its leaves and to its packed nodes (heaps
`8..127`); its heaps `2..7` keep their own halves (`sharedOuterHash`, `sharedNode`). A leaf's half is fixed by its
heap `128 + physical`, while its header keeps the raw child (rotated on B/C coordinates), so the C1 leaf takes the
heap explicitly (`leafHashH`). The legacy unpaired definitions (`leafHashP`, `wctNodeHash`, `buildChildF`) are
unchanged; they describe the retained reference images. -/
def ftsHighHeap (heap : Nat) : Bool := decide (heap < 4) || (decide (16 ≤ heap) && decide (heap % 2 = 0))
/-- C1: the used half of the hash output of FTS heap `heap`. -/
def ftsHalf (heap : Nat) (output : HashOutput) : Digest :=
  if ftsHighHeap heap then output.extractLsb' 128 128 else output.extractLsb' 0 128
/-- C1: the value of FTS heap `heap` hashed from `input`: the high half on `ftsHighHeap` heaps, else the low half. -/
def ftsHash (heap : Nat) (input : HashInput) : M Digest :=
  if ftsHighHeap heap then highHash input else shortHash input
/-- C1: the padded FTS leaf of raw child `selected` placed at heap `heap` (`128 + physical`). -/
def leafHashH (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) : M Digest :=
  ftsHash heap (leafInputP index coord selected pad ends)
/-- C1: FTS node at heap `heap` with a zero pad; the used half follows `ftsHighHeap heap`. -/
def wctNodeHashH (coord index heap : Nat) (left right : Digest) : M Digest :=
  ftsHash heap (bytesLE 16 left ++ bytesLE 16 (wctNodeHeader coord index heap) ++ zero16 ++ bytesLE 16 right)
/-- C1: `buildChildF` with the leaf of heap `heap` (`leafHashH`). -/
def buildChildH (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (padL : Digest) :
    M (Digest × List Digest) := do
  let state ← (List.finRange 6).foldlM
    (fun (state : List Digest × List Digest) i => do
      let secret := ftsFamilySeed coefs selected i.val
      let deficit := wordDigit word i
      let value ← chain index coord selected i.val 0 (4 - deficit) secret
      let last ← chain index coord selected i.val (4 - deficit) deficit value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  let root ← leafHashH heap index coord selected padL state.1
  pure (root, state.2)
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
/-- C1: on the packed heaps `4..255` the high half is used exactly on even heaps `≥ 16`. -/
theorem ftsHighHeap_iff {heap : Nat} (h4 : 4 ≤ heap) :
    ftsHighHeap heap = true ↔ 16 ≤ heap ∧ heap % 2 = 0 := by
  simp [ftsHighHeap]; omega
theorem leafHashH_eq (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    leafHashH heap index coord selected pad ends = ftsHash heap (leafInputP index coord selected pad ends) := rfl
/-- On a low-half heap the C1 leaf is the legacy padded leaf. -/
theorem leafHashH_of_low {heap : Nat} (h : ftsHighHeap heap = false) (index coord selected : Nat) (pad : Digest)
    (ends : List Digest) : leafHashH heap index coord selected pad ends = leafHashP index coord selected pad ends := by
  rw [leafHashH_eq, ftsHash_of_low h]
  rfl
/-- On a low-half heap the C1 node is the legacy node hash. -/
theorem wctNodeHashH_of_low {heap : Nat} (h : ftsHighHeap heap = false) (coord index : Nat) (left right : Digest) :
    wctNodeHashH coord index heap left right = wctNodeHash coord index heap left right := by
  unfold wctNodeHashH
  rw [ftsHash_of_low h, wctNodeHash_eq_short]
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
/-- A zero-step chain whose leaf slot survives earlier 32-byte HASH writes. Campaign T51: the top checksum chain 50
is never safe (the r7 pair's chain 49 is safe iff `d48 = d49 = 6`; chain 48 never, `48 % 3 = 0`). -/
def safeZeroCopy (lay : Layer) (digits : List Nat) (i : Nat) : Prop :=
  digits.getD i 0 = maxDigit lay i ∧
    (i = 0 ∨ (lay ≠ 0 ∧ i = 1) ∨
      (0 < i ∧ i % 3 ≠ 0 ∧ ¬(lay = 0 ∧ i = 50) ∧ digits.getD (i-1) 0 = maxDigit lay (i-1)))
instance (lay : Layer) (digits : List Nat) (i : Nat) : Decidable (safeZeroCopy lay digits i) := by
  unfold safeZeroCopy
  infer_instance

def savedCopies (lay : Layer) (digits : List Nat) : Nat :=
  ((List.range (chainCount lay)).filter fun i => decide (safeZeroCopy lay digits i)).length

/-- Campaign T51: #938's penalised r5 rows that survive (q = 10, 11, 12) cost one cycle when their digit sum is below
3; the r6 groups, the r7 pair and the checksum carry no penalty. -/
def topDispatchPenalty (digits : List Nat) : Nat :=
  ((List.range 17).filter fun q => decide
    ((q = 10 ∨ q = 11 ∨ q = 12) ∧
      digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3)).length

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
/-- Top-bytes layer: the canonical producer caps the zero digits on every layer (T51: top 7 of 51, the checksum
included = 31 family coefficients / 4 leaves; lower 5 of 42). The legacy `producerZeroBound` (top unrestricted) is
kept for the legacy producer. -/
def producerZeroCap (lay : Layer) : Nat := if lay = 0 then 7 else 5
def canonicalZeroBound (lay : Layer) (digits : List Nat) : Prop :=
  (digits.filter (· = 0)).length ≤ producerZeroCap lay
instance (lay : Layer) (digits : List Nat) : Decidable (canonicalZeroBound lay digits) := by
  unfold canonicalZeroBound; infer_instance
theorem canonicalZeroBound_lower {lay : Layer} (hl : lay ≠ 0) (digits : List Nat) :
    canonicalZeroBound lay digits ↔ producerZeroBound lay digits := by
  simp [canonicalZeroBound, producerZeroBound, producerZeroCap, hl]
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
/-- The smallest lower-layer window (L1, L2). -/
def lowerSearchLimit : Nat := 2 ^ 21
/-- Top counter window 2^20 (top-bytes layer). The legacy `T3.counterLimit` (2^22, the legacy T3 scheme and the
presampling key space) is unchanged; the canonical searches use `searchLimit`. -/
def topSearchLimit : Nat := 2 ^ 20
/-- Per-layer counter windows of the shipped images (opus-crumbs img-v4 check `t1 = ((s0 + 3) >> 1) << 20`, which also
enforces the top limit): top 2^20, L1/L2 2^21, L3 3·2^20. -/
def searchLimit (lay : Layer) : Nat := (lay.val + 3) / 2 * 2 ^ 20
/-- The verifier accepts every 32-bit counter: its window is the whole `BitVec 32` range, so the layer check
never rejects. The signer still searches `searchLimit`. -/
def verifyWindow : Nat := 2 ^ 32
theorem ctr_not_ge_verifyWindow (c : BitVec 32) : ¬c.toNat ≥ verifyWindow := by
  unfold verifyWindow; exact Nat.not_le.mpr c.isLt
/-! ### Canonical policy core (configuration (1)+(2), "e7b" top head)
Defined before the encoding selector because the top producer choice uses the canonical top predicate.
* `totalCredit` = 69 (credit pool), `topFloor` = 14 (every top search uses it; RC938: pool 74 -> 77, floor 19 -> 22;
  T51 on RC: pool 69, floor 14, pool - floor = 55 as before).
* Path-aware credit: `credit lay low digits = reward + bonus·[low] - dispatchPenalty` where `low` = the
  LOW half of the 256-bit answer was selected (`lowSelected`); bonus 4 on lower layers, 2 on the top layer
  (the d6b head reads the hint first: honest LOW costs 4 cycles, HIGH 6). -/
namespace CanonicalPolicy
/-- The credit pool every canonical path must reach. -/
def totalCredit : Nat := 69
/-- The (fixed) top credit floor (on the path-aware credit). -/
def topFloor : Nat := 14
/-- All three lower layers use digit sum 201. Layer 1's existing broad decoder
has the same lower digit layout and this exact target. -/
def normalLayer (lay : Layer) : Layer := if lay = 0 then 0 else 1
def decode (lay : Layer) (answer : Digest) : Option (List Nat) :=
  SigGolfCandidate.T3.decode (normalLayer lay) answer
/-- Word reward (credited instructions) of a decoded word, independent of the selected half. -/
def reward (lay : Layer) (digits : List Nat) : Nat :=
  wordCredit lay digits + 4 * savedCopies lay digits
/-- Path bonus: a lower layer whose LOW half was selected saves 4 verify cycles, the top layer 2 (d6b head). -/
def pathBonus (lay : Layer) (low : Bool) : Nat := if low = true then (if lay = 0 then 2 else 4) else 0
/-- Path-aware reward. -/
def pathReward (lay : Layer) (low : Bool) (digits : List Nat) : Nat :=
  reward lay digits + pathBonus lay low
/-- Path-aware credit ("ec"). -/
def credit (lay : Layer) (low : Bool) (digits : List Nat) : Nat :=
  pathReward lay low digits - dispatchPenalty lay digits
def nextResidual (residual : Nat) (lay : Layer) (low : Bool) (digits : List Nat) : Nat :=
  residual - credit lay low digits
/-- The canonical producer predicate at floor `floor` for a word selected through half `low`. -/
def producerDecodeAt (lay : Layer) (floor : Nat) (low : Bool) (answer : Digest) : Option (List Nat) :=
  match decode lay answer with
  | some digits =>
      if floor + dispatchPenalty lay digits ≤ pathReward lay low digits ∧
          canonicalZeroBound lay digits ∧ producerRankBound lay answer then some digits
      else none
  | none => none
theorem pathBonus_top (low : Bool) : pathBonus 0 low = if low then 2 else 0 := by
  cases low <;> simp [pathBonus]
theorem pathBonus_lower {lay : Layer} (hl : lay ≠ 0) (low : Bool) :
    pathBonus lay low = if low then 4 else 0 := by
  cases low <;> simp [pathBonus, hl]
@[simp] theorem pathBonus_false (lay : Layer) : pathBonus lay false = 0 := by simp [pathBonus]
theorem pathBonus_le (lay : Layer) (low : Bool) : pathBonus lay low ≤ 4 := by
  unfold pathBonus; split_ifs <;> omega
theorem pathReward_top (low : Bool) (digits : List Nat) :
    pathReward 0 low digits = reward 0 digits + (if low then 2 else 0) := by
  simp [pathReward, pathBonus_top]
theorem credit_top (low : Bool) (digits : List Nat) :
    credit 0 low digits = reward 0 digits + (if low then 2 else 0) - dispatchPenalty 0 digits := by
  simp [credit, pathReward_top]
/-- Lower layers carry no dispatch penalty. -/
theorem credit_lower {lay : Layer} (hl : lay ≠ 0) (low : Bool) (digits : List Nat) :
    credit lay low digits = reward lay digits + (if low then 4 else 0) := by
  simp [credit, pathReward, pathBonus_lower hl, dispatchPenalty, hl]
end CanonicalPolicy

/-- The canonical top producer predicate on the LOW half (with the LOW path bonus); the producer chooses LOW when
it holds or LOW is forced, else HIGH (whose acceptance is then decided at `low = false`). -/
def topGood (word : Digest) : Prop :=
  (CanonicalPolicy.producerDecodeAt 0 CanonicalPolicy.topFloor true word).isSome = true
instance : DecidablePred topGood := fun word => by unfold topGood; infer_instance

/-- Canonical producer choice: LOW when it passes the top producer predicate or is forced
(`TopChoice.blocked`: bits 126, 127 of LOW both zero), else HIGH. -/
def topChooseLow (answer : HashOutput) : Bool :=
  decide (topGood (answer.extractLsb' 0 128) ∨ TopChoice.blocked (answer.extractLsb' 0 128))

/-- The producer's canonical word. The top layer uses the restricted choice; lower layers retain the
reserved-bit rule (`DualHalf.select`). -/
def encodingAnswer (lay : Layer) (answer : HashOutput) : Digest :=
  if lay = 0 then TopChoice.choose topGood answer else DualHalf.select answer

/-- Whether the producer's canonical word is the LOW half of the answer. -/
def lowSelected (lay : Layer) (answer : HashOutput) : Bool :=
  if lay = 0 then topChooseLow answer else decide (lowerSpare (answer.extractLsb' 0 128))

/-- The honest witness hint (top layer only): request HIGH exactly when the producer chose it. Stored in the
witness byte at rel 22312 as `16` (HIGH) or `0`; it adds no signature bytes. -/
def encodingHigh (lay : Layer) (answer : HashOutput) : Bool :=
  if lay = 0 then !topChooseLow answer else false

/-- Verifier selection for an arbitrary witness hint `high` (top only; HIGH is refused when LOW is forced).
Lower layers ignore the hint. -/
def verificationAnswer (lay : Layer) (high : Bool) (answer : HashOutput) : Digest :=
  if lay = 0 then TopChoice.read high answer else DualHalf.select answer

/-- The verifier's cheap path (`true` = LOW path). Top (e7b head, hint read first): the hint bit clear (cost 4);
a set hint costs 7 whichever half is then read. Lower layers: LOW is selected iff it is spare. -/
def verificationLow (lay : Layer) (high : Bool) (answer : HashOutput) : Bool :=
  if lay = 0 then !high else decide (lowerSpare (answer.extractLsb' 0 128))

def verificationHash (lay : Layer) (high : Bool) (input : HashInput) : M Digest :=
  verificationAnswer lay high <$> publicHash input

theorem encodingAnswer_top (answer : HashOutput) :
    encodingAnswer 0 answer = TopChoice.choose topGood answer := rfl
theorem encodingAnswer_top_eq (answer : HashOutput) :
    encodingAnswer 0 answer = if topChooseLow answer then answer.extractLsb' 0 128 else answer.extractLsb' 128 128 := by
  simp only [encodingAnswer, if_true, TopChoice.choose, topChooseLow, TopChoice.lowHalf, TopChoice.highHalf]
  split_ifs <;> simp_all
theorem encodingAnswer_lower (lay : Layer) (hl : lay ≠ 0) (answer : HashOutput) :
    encodingAnswer lay answer = DualHalf.select answer := by simp [encodingAnswer, hl]

/-- The expander's canonical hint selects exactly the signer's word. -/
theorem verificationAnswer_honest (lay : Layer) (answer : HashOutput) :
    verificationAnswer lay (encodingHigh lay answer) answer = encodingAnswer lay answer := by
  by_cases hl : lay = 0
  · subst hl; simp only [verificationAnswer, encodingHigh, encodingAnswer, if_true]
    exact TopChoice.read_chooseHigh topGood answer
  · simp [verificationAnswer, encodingAnswer, hl]
theorem verificationLow_honest (lay : Layer) (answer : HashOutput) :
    verificationLow lay (encodingHigh lay answer) answer = lowSelected lay answer := by
  by_cases hl : lay = 0
  · subst hl; simp only [verificationLow, encodingHigh, lowSelected, if_true, Bool.not_not]
  · simp [verificationLow, lowSelected, hl]
/-- The honest top hint is the negated selected half. -/
theorem encodingHigh_top (answer : HashOutput) : encodingHigh 0 answer = !lowSelected 0 answer := rfl
theorem verificationAnswer_lower (lay : Layer) (hl : lay ≠ 0) (high : Bool) (answer : HashOutput) :
    verificationAnswer lay high answer = encodingAnswer lay answer := by
  simp [verificationAnswer, encodingAnswer, hl]
theorem verificationLow_lower (lay : Layer) (hl : lay ≠ 0) (high : Bool) (answer : HashOutput) :
    verificationLow lay high answer = lowSelected lay answer := by
  simp [verificationLow, lowSelected, hl]
theorem verificationAnswer_eq_lower (lay : Layer) (hl : lay ≠ 0) (high : Bool) (answer : HashOutput) :
    verificationAnswer lay high answer =
      if verificationLow lay high answer then answer.extractLsb' 0 128 else answer.extractLsb' 128 128 := by
  simp only [verificationAnswer, verificationLow, hl, if_false, DualHalf.select, DualHalf.selectPair]
  by_cases hs : lowerSpare (answer.extractLsb' 0 128) <;> simp [hs]
theorem encodingAnswer_eq (lay : Layer) (answer : HashOutput) :
    encodingAnswer lay answer =
      if lowSelected lay answer then answer.extractLsb' 0 128 else answer.extractLsb' 128 128 := by
  by_cases hl : lay = 0
  · subst hl
    simpa [lowSelected] using encodingAnswer_top_eq answer
  · rw [← verificationAnswer_lower lay hl false, ← verificationLow_lower lay hl false]
    exact verificationAnswer_eq_lower lay hl false answer

def encodingHash (lay : Layer) (input : HashInput) : M Digest :=
  encodingAnswer lay <$> publicHash input

theorem encodingHash_top (input : HashInput) :
    encodingHash 0 input = TopChoice.choose topGood <$> publicHash input := rfl

theorem verificationHash_lower (lay : Layer) (hl : lay ≠ 0) (high : Bool) (input : HashInput) :
    verificationHash lay high input = encodingHash lay input := by
  unfold verificationHash encodingHash
  congr 1
  funext answer
  exact verificationAnswer_lower lay hl high answer

theorem verificationHash_bind {β : Type} (lay : Layer) (high : Bool) (input : HashInput) (f : Digest → M β) :
    verificationHash lay high input >>= f = publicHash input >>= fun a => f (verificationAnswer lay high a) := by
  unfold verificationHash
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

theorem verificationHash_congr (lay : Layer) (high : Bool) {x y : HashInput} (h : pad64 x = pad64 y) :
    verificationHash lay high x = verificationHash lay high y := by
  unfold verificationHash publicHash
  rw [h]

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
/-! ### v6 seed families (r3-lean-seedfam; opus-crumbs PORT v6 A)
`famGrp lay` consecutive leaves share one family `famOf lay leaf = leaf / famGrp lay`; family `f` owns the coefficient
ordinals `famBase lay · f + j`, `j < famSize lay f` (the last family of a tree is short), the packed halves (low half
first) of `lowerSeedPair lay tree (ordinal / 2)`. The seed of chain `i` of leaf `leaf` is the family evaluated at
`famPoint lay leaf i = (leaf % famGrp lay) · famStride lay + i + 1` (address slots `chainCount ≤ i < 58` of a lower
leaf use a separate junk region above `famGrp · famStride`; the scheme never computes them).
Lower (v6): families of 7 leaves, base 38, size `5 · min 7 (2^height − 7 f) + 3`, stride 43; the base is even, so
family `f` reads exactly the pairs `19 f + j`, `j < ⌈famSize / 2⌉` (no carry). Top: one family per leaf (24
coefficients … ) — v6 top: families of 4 leaves, 39 coefficients (`T3.topCoefCount`, carry-packed), points
`(leaf % 4) · 64 + i + 1` (= `T3.topPoint`). -/
def famGrp (lay : Layer) : Nat := if lay = 0 then 4 else 7
def famBase (lay : Layer) : Nat := if lay = 0 then SigGolfCandidate.T3.topCoefCount else 38
def famSize (lay : Layer) (f : Nat) : Nat :=
  if lay = 0 then SigGolfCandidate.T3.topCoefCount else 5 * min 7 (2 ^ height lay - 7 * f) + 3
def famStride (lay : Layer) : Nat := if lay = 0 then 64 else 43
def famOf (lay : Layer) (leaf : Nat) : Nat := leaf / famGrp lay
def famPoint (lay : Layer) (leaf i : Nat) : Nat :=
  if lay = 0 ∨ i < chainCount lay then (leaf % famGrp lay) * famStride lay + i + 1
  else famGrp lay * famStride lay + (leaf % famGrp lay) * (58 - chainCount lay) + (i - chainCount lay) + 1
def famOrdinal (lay : Layer) (leaf j : Nat) : Nat := famBase lay * famOf lay leaf + j
/-- Private pairs read by lower family `f`. -/
def famPairs (lay : Layer) (f : Nat) : Nat := (famSize lay f + 1) / 2
def lowerPoint (chain : Nat) : Nat := chain + 1
/-- The coefficients of lower family `f`: the pairs `famBase · f / 2 + j`, `j < famPairs`, low half first. -/
def lowerFamCoefs (lay : Layer) (tree f : Nat) : M (List Digest) := do
  let acc ← (List.range (famPairs lay f)).foldlM (fun (acc : List Digest) j => do
    let p ← lowerSeedPair lay tree (famBase lay * f / 2 + j)
    pure (acc ++ [p.1, p.2])) []
  pure (acc.take (famSize lay f))
/-- Coefficient state of leaf `leaf`: the family is read at its first leaf (`leaf % famGrp = 0`) and kept for the
other members. Returns the coefficients and the state for the next leaf. -/
def lowerCoefs (lay : Layer) (tree leaf : Nat) (carry : List Digest) : M (List Digest × List Digest) :=
  if leaf % famGrp lay = 0 then do
    let coefs ← lowerFamCoefs lay tree (famOf lay leaf)
    pure (coefs, coefs)
  else pure (carry, carry)
def lowerFamilySeed (coefs : List Digest) (lay : Layer) (leaf chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval coefs (famPoint lay leaf chain)
def buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : List Digest) :
    M ((Digest × List Digest) × List Digest) := do
  let (coefs, carry) ← lowerCoefs lay tree leaf carry
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let value ← chainW lay tree leaf i 0 digit (lowerFamilySeed coefs lay leaf i)
      let last ← chainW lay tree leaf i digit (maxDigit lay i - digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  let root ← lowerLeafHash lay tree leaf state.1
  pure ((root, state.2), carry)
/-- Lower tree of layer `lay ≥ 1` (v6: leaves built by `buildLeafPF`, the family coefficients threaded across leaves).
`buildLeafP` (per-chain packed seeds) is kept for the machine proofs of the pre-stage-B sign image. -/
def buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × List Digest) leaf => do
      let ((root, values), carry) ← buildLeafPF lay tree leaf (if leaf = selected then digits else []) state.2.2
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), carry)) ([], [], [])
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
/-- Campaign T51: range check of the top group whose first chain is `3 g` (r6 groups `g ≤ 8`: `r6Valid`; r5 groups
`9 ≤ g ≤ 15`: rank below 125; `g = 16` is the r7 pair at chains 48, 49: rank below 49). -/
def topGroupValid (answer : Digest) (g : Nat) : Bool :=
  if g < 9 then r6Valid answer g else if g < 16 then decide (r5Rank answer g < 125) else decide (r7Rank answer < 49)
/-- Campaign T51: the checksum digit `target 0 - sum` lies in `[0, 5]`. -/
def topChecksumOk (answer : Digest) : Bool :=
  decide ((dataDigits 0 answer).sum ≤ target 0 ∧ target 0 - (dataDigits 0 answer).sum < 6)
/-- Campaign T51: digit of top chain `i` as the verifier runs it (data digits 0..49, then the checksum). -/
def topRunDigit (answer : Digest) (i : Nat) : Nat :=
  if i < 50 then (dataDigits 0 answer).getD i 0 else target 0 - (dataDigits 0 answer).sum
/-- Campaign T51 verifier order (dispatch in chain order): a group's range check at its first chain (`i % 3 = 0`,
`i < 50`; the r7 pair at chain 48), the checksum range check before chain 50. -/
def topGroupBad (answer : Digest) (i : Nat) : Bool :=
  decide (i % 3 = 0 ∧ i < 50 ∧ topGroupValid answer (i / 3) = false) ||
    decide (i = 50 ∧ topChecksumOk answer = false)
def topDecodeStep (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest)
    (state : Option (List Digest)) (i : Fin (chainCount 0)) : M (Option (List Digest)) := do
  let some ends := state | pure none
  if topGroupBad answer i.val then return none
  let value ← run i (topRunDigit answer i.val)
  pure (some (ends ++ [value]))
/-- Campaign T51: every check is in `topDecodeStep` (no spare bit, no final sum check: the checksum digit is derived). -/
def topDecodeRun (run : Fin (chainCount 0) → Nat → M Digest) (finish : List Digest → M Digest)
    (answer : Digest) : M (Option Digest) := do
  if answer.toNat ≥ 2 ^ encodedBits 0 then return none
  let some ends ← (List.finRange (chainCount 0)).foldlM (topDecodeStep run answer) (some []) | pure none
  some <$> finish ends
def verifyTop (sig : Signature) (index : Nat) (answer : Digest) : M (Option Digest) :=
  let leaf := (route index 0).1
  let tree := (route index 0).2
  topDecodeRun
    (fun i digit => SigGolfCandidate.T3.layChain 0 tree leaf i.val digit (maxDigit 0 i.val - digit)
      ((sig.layers 0).values i))
    (fun ends => do
      let value ← SigGolfCandidate.T3.leafHash 0 tree leaf ends
      (List.finRange (height 0)).foldlM (fun value j => do
        let other := (sig.layers 0).path j
        let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        nodeHash 3 (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2)
        value)
    answer
/-- Top-bytes layer: the verifier's top path reads the node nonces of heights 1..11 from the witness pads
(`nonces.getD j 0` for the node at height `j + 1`); the root (height 12) has a zero pad. -/
def verifyTopN (sig : Signature) (nonces : List Nat) (index : Nat) (answer : Digest) : M (Option Digest) :=
  let leaf := (route index 0).1
  let tree := (route index 0).2
  topDecodeRun
    (fun i digit => SigGolfCandidate.T3.layChain 0 tree leaf i.val digit (maxDigit 0 i.val - digit)
      ((sig.layers 0).values i))
    (fun ends => do
      let value ← SigGolfCandidate.T3.leafHash 0 tree leaf ends
      (List.finRange (height 0)).foldlM (fun value j => do
        let other := (sig.layers 0).path j
        let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        let heap := 2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)
        if j.val < 11 then topNodeHashN heap (nonces.getD j.val 0) pair.1 pair.2
        else nodeHash 3 (0 : Layer).val tree heap pair.1 pair.2)
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

/-! Canonical ancestor-only policy for the paired-forest construction (configuration (1)+(2)).
A lower leaf's threshold depends only on the path-aware credits of its canonical ancestors. -/
namespace ClaudeWCT.WCT9.CanonicalPolicy
open OracleComp OracleSpec SigGolfCandidate.T3

/-- The paired gate needs this larger finite search window for simultaneous
completeness over every256-bit message. It does not change the moment model. -/
def ftsSearchLimit : Nat := 2 ^ 21

/-- Layer-1 floors by residual `r ≤ 55` (= 69 - 14 on T51; img-v6 / opus-crumbs PORT v6). -/
def lowerOneThresholds : List Nat :=
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   1,2,3,4,5,6,7,8,8,9,10,11,11,12,13,13,14,15]

/-- Layer-2 floors by residual `r ≤ 40` (img-v6). -/
def lowerTwoThresholds : List Nat :=
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,12,13,14,15,15,16,17,18,19]

/-- Largest lower floor (L3 floors reach 21; policy hints use the mixed radix 484 / 22 / 1, bound 7744). -/
def lowerFloorMax : Nat := 21

/-- Out-of-range lower residuals deliberately have an impossible threshold. -/
def threshold (stage residual : Nat) : Nat :=
  if stage = 0 then topFloor
  else if stage = 1 then lowerOneThresholds.getD residual 301
  else if stage = 2 then lowerTwoThresholds.getD residual 301
  else if stage = 3 ∧ residual ≤ 21 then residual
  else 301

/-- Producer decode of a complete 256-bit answer: the canonically selected word's digits and the selected
half (`true` = LOW). -/
def producerDecodeOut (lay : Layer) (floor : Nat) (answer : HashOutput) : Option (List Nat × Bool) :=
  (producerDecodeAt lay floor (lowSelected lay answer) (encodingAnswer lay answer)).map
    fun digits => (digits, lowSelected lay answer)

/-- Canonical counter search; returns the counter, the digits and the selected half (`true` = LOW). -/
def layerCounterSearchAt (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg)
    (counter : Nat) : Nat → M (Option (BitVec 32 × List Nat × Bool))
  | 0 => pure none
  | fuel + 1 => do
      let answer ← publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
      match producerDecodeOut lay floor answer with
      | none => layerCounterSearchAt lay floor tree leaf msg (counter + 1) fuel
      | some found => pure (some (BitVec.ofNat 32 counter, found))

theorem normalLayer_target (lay : Layer) :
    target (normalLayer lay) = if lay = 0 then 152 else 201 := by
  by_cases h : lay = 0 <;> simp [normalLayer, h, target]

theorem producerDecodeAt_spec {lay : Layer} {floor : Nat} {low : Bool} {answer : Digest} {digits : List Nat}
    (h : producerDecodeAt lay floor low answer = some digits) :
    decode lay answer = some digits ∧ floor + dispatchPenalty lay digits ≤ pathReward lay low digits ∧
      canonicalZeroBound lay digits ∧ producerRankBound lay answer := by
  unfold producerDecodeAt at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact ⟨rfl, hc⟩

theorem producerDecodeAt_credit {lay : Layer} {floor : Nat} {low : Bool} {answer : Digest} {digits : List Nat}
    (h : producerDecodeAt lay floor low answer = some digits) : floor ≤ credit lay low digits := by
  have hc := (producerDecodeAt_spec h).2.1
  unfold credit
  omega

theorem producerDecodeOut_spec {lay : Layer} {floor : Nat} {answer : HashOutput} {digits : List Nat} {low : Bool}
    (h : producerDecodeOut lay floor answer = some (digits, low)) :
    low = lowSelected lay answer ∧
      producerDecodeAt lay floor low (encodingAnswer lay answer) = some digits := by
  unfold producerDecodeOut at h
  cases hd : producerDecodeAt lay floor (lowSelected lay answer) (encodingAnswer lay answer) with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hd⟩

theorem producerDecodeOut_credit {lay : Layer} {floor : Nat} {answer : HashOutput} {digits : List Nat}
    {low : Bool} (h : producerDecodeOut lay floor answer = some (digits, low)) : floor ≤ credit lay low digits :=
  producerDecodeAt_credit (producerDecodeOut_spec h).2

theorem threshold_top (residual : Nat) : threshold 0 residual = 14 := by
  simp [threshold, topFloor]

theorem nextResidual_le (residual : Nat) (lay : Layer) (low : Bool) (digits : List Nat) :
    nextResidual residual lay low digits ≤ residual := Nat.sub_le _ _

theorem residual_composition (residual : Nat) (lay₁ lay₂ : Layer) (low₁ low₂ : Bool)
    (digits₁ digits₂ : List Nat) :
    nextResidual (nextResidual residual lay₁ low₁ digits₁) lay₂ low₂ digits₂ =
      residual - (credit lay₁ low₁ digits₁ + credit lay₂ low₂ digits₂) := by
  simp [nextResidual, Nat.sub_sub]

theorem threshold_zero : threshold 1 0 = 0 ∧ threshold 2 0 = 0 ∧ threshold 3 0 = 0 := by
  decide

end ClaudeWCT.WCT9.CanonicalPolicy

namespace ClaudeWCT.WCT9.CanonicalPolicy
open SigGolfCandidate.T3
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem lower_one_progress : ∀ r : Fin 56,
    threshold 1 r.val ≤ 19 ∧ r.val - threshold 1 r.val < 41 := by decide +kernel

/-- img-v6: every L1 floor is below 16 (the hint's leading digit `f1 ≤ 15`). -/
theorem lower_one_floor_lt : ∀ r : Fin 56, threshold 1 r.val < 16 := by decide +kernel

theorem lower_two_progress : ∀ r : Fin 41,
    threshold 2 r.val ≤ 19 ∧ r.val - threshold 2 r.val < 22 := by decide +kernel

theorem lower_three_progress (r : Nat) (hr : r < 22) :
    threshold 3 r = r := by simp [threshold, show r ≤ 21 by omega]

theorem accepted_top_residual {answer : Digest} {low : Bool} {digits : List Nat}
    (h : producerDecodeAt 0 14 low answer = some digits) : nextResidual 69 0 low digits < 56 := by
  have hc := producerDecodeAt_credit h
  unfold nextResidual
  omega

theorem accepted_one_residual (r : Fin 56) {answer : Digest} {low : Bool} {digits : List Nat}
    (h : producerDecodeAt 1 (threshold 1 r.val) low answer = some digits) :
    nextResidual r.val 1 low digits < 41 := by
  have hc := producerDecodeAt_credit h
  have hp := (lower_one_progress r).2
  unfold nextResidual
  omega

theorem accepted_two_residual (r : Fin 41) {answer : Digest} {low : Bool} {digits : List Nat}
    (h : producerDecodeAt 2 (threshold 2 r.val) low answer = some digits) :
    nextResidual r.val 2 low digits < 22 := by
  have hc := producerDecodeAt_credit h
  have hp := (lower_two_progress r).2
  unfold nextResidual
  omega

theorem accepted_three_residual (r : Fin 22) {answer : Digest} {low : Bool} {digits : List Nat}
    (h : producerDecodeAt 3 (threshold 3 r.val) low answer = some digits) :
    nextResidual r.val 3 low digits = 0 := by
  have hc := producerDecodeAt_credit h
  rw [lower_three_progress r.val r.isLt] at hc
  exact Nat.sub_eq_zero_of_le hc

end ClaudeWCT.WCT9.CanonicalPolicy
