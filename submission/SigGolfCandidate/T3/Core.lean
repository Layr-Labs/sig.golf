import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.HashOutputSplit
import SigGolfCandidate.T3.Rev
import SigGolfCandidate.T3.FullCache.MacDefs
import SigGolfCandidate.ClaudeWCT.Arith.GF128

namespace SigGolfCandidate.T3
open OracleComp OracleSpec
open SphincsSecurity (bytesLE)
abbrev Digest := BitVec 128
abbrev Message := BitVec 256
abbrev HashOutput := BitVec 256
abbrev HashInput := List UInt8
abbrev HashSpec := HashInput →ₒ HashOutput
abbrev Layer := Fin 4
abbrev Region := Fin 131040 → UInt8
abbrev Coordinate := BitVec 128 ⊕ (Message ⊕ Region)
abbrev Spec := SphincsSecurity.OracleWorld + (Coordinate →ₒ HashOutput)
abbrev M := OracleComp Spec
def height (lay : Layer) : Nat := ![12, 7, 6, 6] lay
/-- Campaign R6: the top WOTS has 52 chains (24 radix-6, 27 radix-5, one radix-8 checksum). -/
def chainCount (lay : Layer) : Nat := ![52, 43, 43, 43] lay
/-- Data digits read from the encoding word; the last chain of every layer is a checksum (R6: top chain 51). -/
def dataCount (lay : Layer) : Nat := if lay = 0 then 51 else 42
/-- Bits per chain digit: every chain, top included, has at most 8 positions, so 3. -/
def width (_lay : Layer) (_i : Nat) : Nat := 3
/-- Largest digit of chain `i`. Campaign R6: top chains 0..23 are radix 6 (8 triples), 24..50 radix 5 (9 triples),
chain 51 is the radix-8 checksum; every lower chain is radix 8. -/
def maxDigit (lay : Layer) (i : Nat) : Nat :=
  if lay = 0 then (if i < 24 then 5 else if i < 51 then 4 else 7) else 7
/-- Digit-sum targets: top 153 (R6, restricted top choice), lower layers 201/202/202. -/
def target (lay : Layer) : Nat := ![153, 201, 202, 202] lay
/-- Encoding values are below `2 ^ encodedBits lay`: no range bound on any layer. The R6 top word uses bits 0..126;
its spare bit 127 must be 0 (`topRanksValid`). -/
def encodedBits (_lay : Layer) : Nat := 128
/-- Sum of the largest digits of a layer: top 24·5 + 27·4 + 7 = 235, lower 43·7 = 301. -/
def capacity (lay : Layer) : Nat := if lay = 0 then 235 else 301
def attemptLimit : Nat := 2 ^ 20
def counterLimit : Nat := 2 ^ 22
def coordinates : Nat := 7
def bucketBits : Nat := 4
def childHeight : Nat := 7
def openings : Nat := 21
def authCapacity : Nat := 115
def zero16 : HashInput := List.replicate 16 0
def packedNodeTag (tag : Nat) : Prop := tag % 256 = 3 ∨ tag % 256 = 9 ∨ tag % 256 = 10
instance (tag : Nat) : Decidable (packedNodeTag tag) := inferInstanceAs
  (Decidable (tag % 256 = 3 ∨ tag % 256 = 9 ∨ tag % 256 = 10))
def revNodeTag (tag : Nat) : Prop := tag % 256 = 9 ∨ tag % 256 = 10
instance (tag : Nat) : Decidable (revNodeTag tag) := inferInstanceAs
  (Decidable (tag % 256 = 9 ∨ tag % 256 = 10))
def nodeWord (tag position index : Nat) : Nat :=
  if revNodeTag tag then
    Rev.revBits 64 ((if tag % 256 = 9 then index % 2^32 ^^^ 2048 else index % 2^32) + position % 2^32 * 2^32)
  else index % 2^32 + position % 2^32 * 2^32
theorem nodeWord_lt (tag position index : Nat) : nodeWord tag position index < 2^64 := by
  unfold nodeWord
  have hp := Nat.mod_lt position (show 0 < 2^32 by decide)
  have hi := Nat.mod_lt index (show 0 < 2^32 by decide)
  split_ifs
  · exact Rev.revBits_lt 64 _
  · exact Rev.revBits_lt 64 _
  · norm_num only at hp hi ⊢; omega
theorem nodeWord_normal (tag position index : Nat) :
    nodeWord (tag % 256) (position % 2^32) (index % 2^32) = nodeWord tag position index := by
  simp only [nodeWord, revNodeTag, Nat.mod_mod]
  rfl
theorem nodeWord_normal' (tag position index : Nat) :
    nodeWord (tag % 256) (position % 4294967296) (index % 4294967296) = nodeWord tag position index :=
  nodeWord_normal tag position index
theorem nodeWord_inj {tag position index position' index' : Nat} (hp : position < 2^32) (hi : index < 2^32)
    (hp' : position' < 2^32) (hi' : index' < 2^32)
    (h : nodeWord tag position index = nodeWord tag position' index') : position = position' ∧ index = index' := by
  unfold nodeWord at h
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hp', Nat.mod_eq_of_lt hi'] at h
  have hx : ∀ v, v < 2^32 → v ^^^ 2048 < 2^32 := fun v hv => Nat.xor_lt_two_pow hv (by decide)
  have hxi := hx index hi
  have hxi' := hx index' hi'
  split_ifs at h with hr h9
  · have h2 := Rev.revBits_inj (by omega) (by omega) h
    have hpp : position = position' := by omega
    refine ⟨hpp, ?_⟩
    have hxx : index ^^^ 2048 = index' ^^^ 2048 := by omega
    have := congrArg (· ^^^ 2048) hxx
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
  · have h2 := Rev.revBits_inj (by omega) (by omega) h
    omega
  · omega
def header (tag lay tree position index : Nat) : BitVec 128 :=
  BitVec.ofNat 128 (1 + tag % 256 * 2^8 + lay % 256 * 2^16 +
    (tree / 2^32 % 256) * 2^24 +
    if packedNodeTag tag then tree % 2^32 * 2^32 + nodeWord tag position index * 2^64
    else position % 2^32 * 2^32 + tree % 2^32 * 2^64 + index % 2^32 * 2^96)
def pad64 (input : HashInput) : HashInput :=
  input ++ List.replicate ((64 - input.length % 64) % 64) 0
def privateInput (secret : BitVec 256) (coordinate : Coordinate) : HashInput :=
  let payload := match coordinate with
    | .inl tweak => (tweak, [])
    | .inr (.inl message) => (header 7 0 0 0 0, bytesLE 32 message)
    | .inr (.inr region) => (header 14 0 0 0 0, List.ofFn region)
  pad64 (bytesLE 16 (secret.extractLsb' 0 128) ++ bytesLE 16 payload.1 ++
    bytesLE 16 (secret.extractLsb' 128 128) ++ zero16 ++ payload.2)
def publicHash (input : HashInput) : M HashOutput := Spec.query (.inl (.inr (pad64 input)))
def privateHash (coordinate : Coordinate) : M HashOutput := Spec.query (.inr coordinate)
def shortHash (input : HashInput) : M Digest := do
  pure ((← publicHash input).extractLsb' 0 128)
/-! ### C4: top-tree spill-down (adapted from b3cc11b's campaign S2 `projHalf`/`projHash`/`topNodeWord`)
A 32-byte answer has two 16-byte halves. In the TOP tree (`lay = 0`, tag 3) a node of even heap (a left child; the root,
heap 1, is odd) and a leaf of even index keep the HIGH half (bytes 16..32) of their answer; every other node and leaf
keeps the low half. The lower trees (L1..L3) keep this legacy text (their current scheme is `WCT9.lowerNodeHash`). -/
def projHalf (high : Bool) (output : HashOutput) : Digest :=
  bif high then output.extractLsb' 128 128 else output.extractLsb' 0 128
/-- Hash and keep the half selected by `high` (`projHash false = shortHash`). -/
def projHash (high : Bool) (input : HashInput) : M Digest := do
  pure (projHalf high (← publicHash input))
theorem projHalf_false (output : HashOutput) : projHalf false output = output.extractLsb' 0 128 := rfl
theorem projHalf_true (output : HashOutput) : projHalf true output = output.extractLsb' 128 128 := rfl
@[simp] theorem projHash_false (input : HashInput) : projHash false input = shortHash input := rfl
/-- C4: the half of a node hash: high only for an even heap of the top tree (tag 3, `lay = 0`). -/
def nodeHalfHigh (tag lay heap : Nat) : Bool := decide (tag = 3 ∧ lay = 0 ∧ heap % 2 = 0)
/-- C4: the half of a leaf hash: high only for a top leaf of even index. -/
def leafHalfHigh (lay : Layer) (leaf : Nat) : Bool := decide (lay.val = 0 ∧ leaf % 2 = 0)
theorem nodeHalfHigh_top (heap : Nat) : nodeHalfHigh 3 0 heap = decide (heap % 2 = 0) := by
  simp [nodeHalfHigh]
theorem nodeHalfHigh_of_ne {tag lay : Nat} (h : ¬ (tag = 3 ∧ lay = 0)) (heap : Nat) : nodeHalfHigh tag lay heap = false := by
  simp only [nodeHalfHigh, decide_eq_false_iff_not]; exact fun h' => h ⟨h'.1, h'.2.1⟩
theorem leafHalfHigh_top (leaf : Nat) : leafHalfHigh 0 leaf = decide (leaf % 2 = 0) := by
  simp [leafHalfHigh]
theorem leafHalfHigh_lower {lay : Layer} (h : lay ≠ 0) (leaf : Nat) : leafHalfHigh lay leaf = false := by
  simp only [leafHalfHigh, decide_eq_false_iff_not]
  exact fun h' => h (Fin.ext h'.1)
/-- C4 top fold word: the heap itself for the real heaps `1..4095` (`topNodeWord_eq`); always in `[1, 4096)`, so it
is never the digest word 0, never an FTS word (`≥ 2 ^ 16`) and never a lower word (type byte 193). -/
def topNodeWord (heap : Nat) : Nat := (heap - 1) % 4095 + 1
def privatePair (tag lay tree position index : Nat) : M (Digest × Digest) := do
  let output ← privateHash (.inl (header tag lay tree position index))
  pure (output.extractLsb' 0 128, output.extractLsb' 128 128)
def privateMacKey : M SiggolfT3Mac4.MacKey := do
  let k0 ← privateHash (.inl (header 14 0 0 0 0))
  let k1 ← privateHash (.inl (header 14 0 0 0 1))
  pure (fun i => if i = 0 then k0 else k1)
def privateMac (region : Region) : M HashOutput := do
  let key ← privateMacKey
  pure (SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag key (List.ofFn region)))
def privateNonce (message : Message) : M Digest := do
  pure ((← privateHash (.inr (.inl message))).extractLsb' 0 128)
def pairedMask (level pair : Nat) : M (Digest × Digest) := privatePair 13 0 0 level pair
def mask (level index : Nat) : M Digest := do
  let pair ← pairedMask level (index/2)
  pure (if index%2=0 then pair.1 else pair.2)
def realHandler (secret : BitVec 256) : QueryImpl Spec (OracleComp SphincsSecurity.OracleWorld)
  | .inl input => liftM (SphincsSecurity.OracleWorld.query input)
  | .inr coordinate => liftM (SphincsSecurity.OracleWorld.query (.inr (privateInput secret coordinate)))
def realize {α : Type} (secret : BitVec 256) (program : M α) :
    OracleComp SphincsSecurity.OracleWorld α := simulateQ (realHandler secret) program
def chainHeaderLow (lay : Layer) (tree leaf i step : Nat) : BitVec 64 :=
  let tr := tree % 2^31
  let lf := leaf % 4096
  let routed := (tr * 2 ^ height lay + lf) % 2^32
  let extra := tr / 2^(32-height lay) + (lf / 2^height lay) * 2^(height lay-1)
  BitVec.ofNat 64 (128 + i % 64 + step % 8 * 2^8 + routed * 2^16 +
    lay.val * 2^48 + 193 * 2^56 +
    extra % 2 * 2^6 + extra / 2 % 32 * 2^11 + extra / 64 * 2^50)
def chainHeaderSpill (tree leaf i step : Nat) : Nat :=
  tree % 2^40 / 2^31 + (leaf % 2^32 / 4096) * 2^9 +
    (i % 2^24 / 64) * 2^29 + (step % 256 / 8) * 2^47
def chainHeaderFlaggedLow (lay : Layer) (tree leaf i step : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((chainHeaderLow lay tree leaf i step).toNat +
    (if chainHeaderSpill tree leaf i step = 0 then 0 else 1) * 2^55)
def chainHeader (lay : Layer) (tree leaf i step : Nat) : BitVec 128 :=
  BitVec.ofNat 64 (chainHeaderSpill tree leaf i step) ++ chainHeaderFlaggedLow lay tree leaf i step
def chainInput (lay : Layer) (tree leaf i step : Nat) (value : Digest) : HashInput :=
  zero16 ++ bytesLE 16 (chainHeader lay tree leaf i step) ++ zero16 ++ bytesLE 16 value
def chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInput lay tree leaf i step value)) value
def hyperWord (lay routed : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (1 + 2 * 2 ^ 8 + routed % 2 ^ 32 * 2 ^ 16 + lay % 256 * 2 ^ 48 + 193 * 2 ^ 56)
def leafTweak (lay : Layer) (tree leaf : Nat) : BitVec 128 :=
  0#64 ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)
def rowTweak (lay : Layer) (tree leaf : Nat) : BitVec 128 :=
  1#64 ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)
/-- FTS node word of the two-word labels. C4: coordinate nibble `coord + 1` (every FTS word is `≥ 2 ^ 16`). -/
def ftsNodeWord (coord index : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (1 + 6 * 2 ^ 8 + (coord + 1) % 16 * 2 ^ 16 + index % 2 ^ 31 * 2 ^ 27)
/-- Packed FTS node word (heaps `8..127`, the four lower child levels): the heap is folded into the low word
(`ftsNodeWord - heap`, byte0 `257 - heap >= 130`, byte1 `5`), so the header is marked and its high word is
ignored by `canonicalHeader` (honest value 0). C4: coordinate nibble `coord + 1`. -/
def ftsNodeWordH (coord index heap : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (1537 - heap + (coord + 1) % 16 * 2 ^ 16 + index % 2 ^ 31 * 2 ^ 27)
/-- Node tweaks. C4: the top tree (`lay = 0`) has the one-word label `topNodeWord heap` (= heap) whose high word is a
witness pad (honest 0); the legacy lower branch (`lay` 1..3) keeps its text. -/
def nodeTweak (tag lay tree heap : Nat) : BitVec 128 :=
  if tag = 3 ∧ lay < 4 then
    (if lay = 0 then 0#64 ++ BitVec.ofNat 64 (topNodeWord heap) else BitVec.ofNat 64 heap ++ hyperWord (lay - 1) tree)
  else if tag = 3 ∧ lay < 13 then
    (if 8 ≤ heap ∧ heap < 128 then 0#64 ++ ftsNodeWordH (lay - 4) tree heap
     else BitVec.ofNat 64 heap ++ ftsNodeWord (lay - 4) tree)
  else header tag lay tree 0 heap
/-- Leaf input. Campaign R6: the top leaf is `0^16 | tweak | 0^32 | end_0..end_51` (896 bytes, 14 blocks); the
32 bytes after the tweak are a witness pad of the verifier (`WCT9.leafInputWG`), honest 0. -/
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  if lay = 0 then zero16 ++ bytesLE 16 (leafTweak lay tree leaf) ++ zero16 ++ zero16 ++ ends.flatMap (bytesLE 16)
  else bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (leafTweak lay tree leaf) ++ (ends.drop 1).flatMap (bytesLE 16)
/-- Leaf hash. C4: a top leaf of even index keeps the high half (`leafHalfHigh`). -/
def leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) : M Digest :=
  projHash (leafHalfHigh lay leaf) (leafInput lay tree leaf ends)
def buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool := false) : M (Digest × List Digest) := do
  let state ← (List.range ((chainCount lay + 1) / 2)).foldlM
    (fun (state : List Digest × List Digest) pair => do
      let seeds ← privatePair 0 lay.val tree pair leaf
      (List.range 2).foldlM (fun (state : List Digest × List Digest) half => do
        let i := 2*pair+half
        if chainCount lay ≤ i then return state
        let seed := if half = 0 then seeds.1 else seeds.2
        let digit := digits.getD i 0
        let value ← chain lay tree leaf i 0 digit seed
        if signatureOnly then return (state.1, state.2 ++ [value])
        let last ← chain lay tree leaf i digit (maxDigit lay i - digit) value
        pure (state.1 ++ [last], state.2 ++ [value])) state) ([], [])
  if signatureOnly then return (0, state.2)
  let root ← leafHash lay tree leaf state.1
  pure (root, state.2)
/-- Node hash. C4: a top node of even heap keeps the high half (`nodeHalfHigh`). -/
def nodeHash (tag lay tree heap : Nat) (left right : Digest) : M Digest :=
  projHash (nodeHalfHigh tag lay heap)
    (bytesLE 16 left ++ bytesLE 16 (nodeTweak tag lay tree heap) ++ zero16 ++ bytesLE 16 right)
def buildLevel (tag lay tree h level : Nat) (nodes : List Digest) : M (List Digest) :=
  (List.range (nodes.length / 2)).mapM fun i =>
    nodeHash tag lay tree (2 ^ (h-level) + i) (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)
def buildLevels (tag lay tree h : Nat) (leaves : List Digest) : M (List (List Digest)) :=
  (List.range' 1 h).foldlM (fun levels level => do
    let nodes ← buildLevel tag lay tree h level (levels.getD (level-1) [])
    pure (levels ++ [nodes])) [leaves]
/-! ### Top WOTS seed family (campaign R6)
Each top leaf has 10 GF(2^128) coefficients: coefficient `j` is half `j % 2` (low half first) of the private pair
`topSeedPair (topCoefOrdinal leaf j / 2)` = `privatePair 0 0 0 (5 * leaf + j / 2) 0`. This is X1 stage B's
`lowerCoefs` shape at lay 0, tree 0 with 10 coefficients (ordinal `10 * leaf + j` through the packed halves of
`lowerSeedPair 0 0`); 10 is even, so leaf `leaf` uses exactly the pairs `5 * leaf .. 5 * leaf + 4` and no carry
crosses a leaf boundary. The seed of chain `i` is `familyEval coefs (i + 1)` (points 1..52). The producer reveals at
most 7 seeds per leaf (`WCT9.producerZeroBound`, margin 3). The per-chain top seeds (`privatePair 0 0 0 pair leaf`)
are retired; `buildLeaf`/`buildTree` remain for the T3 lower layers. -/
def topCoefCount : Nat := 10
def topCoefPairs : Nat := 5
def topCoefOrdinal (leaf j : Nat) : Nat := topCoefCount * leaf + j
def topSeedPair (pair : Nat) : M (Digest × Digest) := privatePair 0 0 0 pair 0
def topCoefs (leaf : Nat) : M (List Digest) :=
  (List.range topCoefPairs).foldlM (fun acc j => do
    let p ← topSeedPair (topCoefPairs * leaf + j)
    pure (acc ++ [p.1, p.2])) []
def topPoint (i : Nat) : Nat := i + 1
def topSeed (coefs : List Digest) (i : Nat) : Digest := ClaudeWCT.Arith.familyEval coefs (topPoint i)
/-- Top leaf (tree 0) with family seeds; `signatureOnly` returns only the signature values (`root = 0`). -/
def buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool := false) : M (Digest × List Digest) := do
  let coefs ← topCoefs leaf
  let state ← (List.range (chainCount 0)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let value ← chain 0 0 leaf i 0 digit (topSeed coefs i)
      if signatureOnly then return (state.1, state.2 ++ [value])
      let last ← chain 0 0 leaf i digit (maxDigit 0 i - digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  if signatureOnly then return (0, state.2)
  let root ← leafHash 0 0 leaf state.1
  pure (root, state.2)
/-- The top tree (keygen): all 4096 top leaves with family seeds, then the 12 node levels. -/
def buildTopTree : M (List (List Digest)) := do
  let roots ← (List.range (2 ^ height 0)).foldlM (fun (roots : List Digest) leaf => do
    let (root, _) ← buildLeafTop leaf []
    pure (roots ++ [root])) []
  buildLevels 3 0 0 (height 0) roots
def buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest) leaf => do
      let (root, values) ← buildLeaf lay tree leaf (if leaf = selected then digits else [])
      pure (state.1 ++ [root], if leaf = selected then values else state.2)) ([], [])
  let levels ← buildLevels 3 lay.val tree (height lay) state.1
  pure (levels, state.2)
structure Cache where
  tag : HashOutput
  region : Region
def cacheBytes (cache : Cache) : HashInput := bytesLE 32 cache.tag ++ List.ofFn cache.region
def maskedLevel (nodes : List Digest) (level : Nat) : M (List Digest) := do
  let pairs ← (List.range (2^(11-level))).mapM fun pair => do
    let masks ← pairedMask level pair
    pure [nodes.getD (2*pair) 0 ^^^ masks.1, nodes.getD (2*pair+1) 0 ^^^ masks.2]
  pure pairs.flatten
def keygenPayload : M (Digest × Region) := do
  let levels ← buildTopTree
  let masked ← (List.range' 0 12).mapM fun level => maskedLevel (levels.getD level []) level
  let raw := (masked.flatten.flatMap (bytesLE 16)).toArray
  pure ((levels.getD 12 []).getD 0 0, fun i => raw.getD i.val 0)
def keygen : M (Digest × Cache) := do
  let (publicKey, region) ← keygenPayload
  let tag ← privateMac region
  pure (publicKey, ⟨tag, region⟩)
def lowerShift (i : Nat) : Nat := if i < 21 then 3 * i else 64 + 3 * (i - 21)
/-! ### R6 top word (design D1c)
Bits of the 128-bit top word `v`: r6 groups `g = 0..6` in bits `8 g .. 8 g + 7`, r5 groups `q = 8..16` in bits
`7 q .. 7 q + 6` (56..118, stored flipped: `raw = 127 - rank`), r6 group 7 in bits 119..126, spare bit 127 (must
be 0). An r6 group `g` holds the chains `3 g .. 3 g + 2` as `rank = d0 + 6 d1 + 36 d2 < 216`; group 0 stores
`raw = rank + 40` (valid iff `raw ≥ 40`), groups 1..7 store `raw = rank` (valid iff `raw < 216`). An r5 group `q`
holds the chains `3 q .. 3 q + 2` as `rank = d0 + 5 d1 + 25 d2 < 125`. The checksum chain 51 is not stored: its
digit is `target 0 - sum` and must lie in `[0, 7]` (`decode`). -/
/-- R6: the flipped r5 fields (bits 56..118). -/
def topMask : Nat := 2 ^ 119 - 2 ^ 56
def topFlip (value : Digest) : Digest := value ^^^ BitVec.ofNat 128 topMask
/-- The top word with its r5 fields unflipped (r6 fields and spare bit unchanged). -/
def topCode (value : Digest) : Nat := (topFlip value).toNat
/-- Legacy (NF17) bit position of a raw radix-8 top digit; unused by the R6 top word. -/
def topRawShift (i : Nat) : Nat := if i = 53 then 119 else 122 + 3 * (i - 51)
/-- R6: bit position of r6 group `g` (groups 0..6 at `8 g`, group 7 at 119). -/
def r6Shift (g : Nat) : Nat := if g = 7 then 119 else 8 * g
/-- R6: raw 8-bit field of r6 group `g` (read through `topCode`, which leaves the r6 fields unchanged). -/
def r6Raw (value : Digest) (g : Nat) : Nat := topCode value / 2 ^ r6Shift g % 256
/-- R6: rank of r6 group `g` (group 0 is offset by 40). -/
def r6Rank (value : Digest) (g : Nat) : Nat := if g = 0 then r6Raw value 0 - 40 else r6Raw value g
/-- R6: range check of r6 group `g`. -/
def r6Valid (value : Digest) (g : Nat) : Bool :=
  if g = 0 then decide (40 ≤ r6Raw value 0) else decide (r6Raw value g < 216)
/-- R6: rank of r5 group `q` (8..16): `127 - raw` of bits `7 q .. 7 q + 6`. -/
def r5Rank (value : Digest) (q : Nat) : Nat := topCode value / 2 ^ (7 * q) % 128
/-- R6: the spare bit 127 of a top word (verify rejects 1; SEC R1; `topCode` leaves bit 127 unchanged). -/
def topSpare (value : Digest) : Nat := topCode value / 2 ^ 127 % 2
def coreDigit (lay : Layer) (value : Digest) (i : Nat) : Nat :=
  if lay = 0 then
    if i < 24 then r6Rank value (i / 3) / 6 ^ (i % 3) % 6
    else if i < 51 then r5Rank value (i / 3) / 5 ^ (i % 3) % 5
    else 0
  else value.toNat / 2 ^ lowerShift i % 8
/-- R6: spare bit 0, every r6 group in range, every r5 rank below 125. -/
def topRanksValid (value : Digest) : Bool :=
  decide (topSpare value = 0) && (List.range 8).all (r6Valid value) &&
    (List.range' 8 9).all fun q => decide (r5Rank value q < 125)
def dataDigits (lay : Layer) (value : Digest) : List Nat :=
  (List.range (dataCount lay)).map (coreDigit lay value)
def lowerSpare (value : Digest) : Prop := value.toNat / 2 ^ 63 % 2 = 1 ∧ value.toNat / 2 ^ 127 % 2 = 1
instance (value : Digest) : Decidable (lowerSpare value) :=
  inferInstanceAs (Decidable (value.toNat / 2 ^ 63 % 2 = 1 ∧ value.toNat / 2 ^ 127 % 2 = 1))
def lowerWord (value : Digest) : Nat := value.toNat % 2 ^ 63 + value.toNat / 2 ^ 64 % 2 ^ 63 * 2 ^ 63
def lowerPack (n : Nat) : Digest :=
  BitVec.ofNat 128 (n % 2 ^ 63 + 2 ^ 63 + n / 2 ^ 63 % 2 ^ 63 * 2 ^ 64 + 2 ^ 127)
def decode (lay : Layer) (value : Digest) : Option (List Nat) :=
  if value.toNat ≥ 2 ^ encodedBits lay then none else
  let digits := dataDigits lay value
  let total := digits.sum
  if lay = 0 then
    if topRanksValid value = true ∧ total ≤ target lay ∧ target lay - total < 8 then
      some (digits ++ [target lay - total])
    else none
  else if lowerSpare value ∧ total ≤ target lay ∧ target lay - total < 8 then
    some (digits ++ [target lay - total])
  else none
def creditFloor (lay : Layer) : Nat := ![7, 0, 0, 0] lay
/-- Legacy T3 top credit (R6 digits): chains whose digit is one below the maximum, the checksum included. -/
def topCredit (value : Digest) : Nat :=
  ((List.range 52).map fun i =>
    if (dataDigits 0 value ++ [target 0 - (dataDigits 0 value).sum]).getD i 0 + 1 = maxDigit 0 i then 1 else 0).sum
def encCredit (lay : Layer) (value : Digest) : Nat := if lay = 0 then topCredit value else 0
def searchDecode (lay : Layer) (value : Digest) : Option (List Nat) :=
  if encCredit lay value < creditFloor lay then none else decode lay value
/-- Top digits signed when the top counter search is exhausted (R6 at target 153): 50 threes (chains 0..49), a two
(chain 50), checksum 1 (sum 153, no zero digit; D1c word `0x40bb44891224489122818181818181a9`). -/
def dummyTop : List Nat := List.replicate 50 3 ++ [2, 1]
def encodingInput (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : BitVec 32) : HashInput :=
  bytesLE 16 message ++ bytesLE 16 (rowTweak lay tree leaf) ++ bytesLE 4 counter
def counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : Nat) :
    Nat → M (Option (BitVec 32 × List Nat))
  | 0 => pure none
  | fuel+1 => do
      let answer ← shortHash (encodingInput lay tree leaf message (BitVec.ofNat 32 counter))
      match searchDecode lay answer with
      | none => counterSearch lay tree leaf message (counter+1) fuel
      | some digits => pure (some (BitVec.ofNat 32 counter, digits))
structure Selection where
  bucket : Nat
  leaves : List Nat
  deriving DecidableEq, Repr
def selections (output : HashOutput) : List Selection :=
  (List.range 7).map fun c =>
    let number := output.toNat / 2^(31+25*c)
    ⟨number % 16, ((List.range 3).map fun j => number / 2^(4+7*j) % 128).mergeSort (· ≤ ·)⟩
def authCount (leaves : List Nat) : Nat :=
  7 + ((leaves.zip (leaves.drop 1)).map fun p => (p.1 ^^^ p.2).log2 + 1).sum - 4
def admissible (chosen : List Selection) : Bool :=
  chosen.all (fun s => decide (s.leaves.Nodup)) &&
    decide (28 + (chosen.map fun s => authCount s.leaves).sum ≤ 115)
def digestGate (output : HashOutput) : Bool := decide (output.toNat / 2^206 % 8 = 0)
def digestAdmissible (output : HashOutput) : Bool :=
  admissible (selections output) && digestGate output
def digestHeader (counter : BitVec 32) : Digest :=
  (0#32 ++ counter) ++ 0#64
def digestInput (rho : Digest) (message : Message) (counter : BitVec 32) : HashInput :=
  bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message
def digest (rho : Digest) (message : Message) (counter : BitVec 32) : M HashOutput :=
  publicHash (digestInput rho message counter)
def digestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel+1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if digestAdmissible output then return some (BitVec.ofNat 32 counter, output)
      digestSearch rho message (counter+1) fuel
def ftsLeaf (index coord leaf : Nat) (secret : Digest) : M Digest :=
  shortHash (zero16 ++ bytesLE 16 (header 9 coord index 0 leaf) ++ bytesLE 16 secret ++ zero16)
def buildFts (index coord : Nat) : M (List (List Digest) × List Digest) := do
  let state ← (List.range 1024).foldlM
    (fun (state : List Digest × List Digest) pair => do
      let (left, right) ← privatePair 8 coord index 0 pair
      let leftLeaf ← ftsLeaf index coord (2*pair) left
      let rightLeaf ← ftsLeaf index coord (2*pair+1) right
      pure (state.1 ++ [leftLeaf,rightLeaf],state.2 ++ [left,right])) ([], [])
  let levels ← buildLevels 10 coord index 11 state.1
  pure (levels,state.2)
def hasLeaf (leaves : List Nat) (level index : Nat) : Bool :=
  leaves.any fun leaf => decide (index * 2 ^ level ≤ leaf ∧ leaf < (index+1) * 2 ^ level)
def frontier (leaves : List Nat) : Nat → Nat → List (Nat × Nat)
  | 0, index => if hasLeaf leaves 0 index then [] else [(0,index)]
  | level+1, index =>
      if hasLeaf leaves (level+1) index then
        frontier leaves level (2*index) ++ frontier leaves level (2*index+1)
      else [(level+1,index)]
def forestPk (index : Nat) (roots : List Digest) : M Digest :=
  shortHash (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++
    (roots.drop 1).flatMap (bytesLE 16))
def route (index : Nat) (lay : Layer) : Nat × Nat :=
  let below := (![19,12,6,0] : Layer → Nat) lay
  (index / 2 ^ below % 2 ^ height lay, index / 2 ^ (below + height lay))
def readLE (bytes : HashInput) : Nat := bytes.foldr (fun b n => b.toNat + 256*n) 0
def readDigest (bytes : HashInput) : Digest := BitVec.ofNat 128 (readLE bytes)
def topPath (cache : Cache) (leaf : Nat) : M (List Digest) :=
  (List.range 12).mapM fun level => do
    let sibling := leaf / 2 ^ level ^^^ 1
    let offset := 16*(8192 - 2^(13-level) + sibling)
    let value := readDigest (List.ofFn fun i : Fin 16 =>
      cache.region ⟨(offset+i.val)%131040, Nat.mod_lt _ (by decide)⟩)
    let m ← mask level sibling
    pure (value ^^^ m)
def signTop (cache : Cache) (leaf : Nat) (digits : List Nat) : M (List Digest × List Digest) := do
  let (_,values) ← buildLeafTop leaf digits true
  let path ← topPath cache leaf
  pure (values,path)
abbrev Pieces := List Digest × List Digest
def signLayers (cache : Cache) (index : Nat) : Nat → Digest → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n+1, message => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf,tree) := route index lay
      let found ← counterSearch lay tree leaf message 0 counterLimit
      if n=0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_,digits) := found | pure none
        let (levels,values) ← buildTree lay tree leaf digits
        let path := (List.range (height lay)).map fun j => (levels.getD j []).getD (leaf/2^j ^^^ 1) 0
        let some previous ← signLayers cache index n ((levels.getD (height lay) []).getD 0 0) | pure none
        pure (some (previous ++ [(values,path)]))
structure LayerSignature (lay : Layer) where
  values : Fin (chainCount lay) → Digest
  path : Fin (height lay) → Digest
structure Signature where
  rho : Digest
  secrets : Fin 21 → Digest
  proof : Fin 115 → Digest
  layers : (lay : Layer) → LayerSignature lay
structure Witness where
  signature : Signature
  digestCounter : BitVec 32
  counters : Layer → BitVec 32
def piecesSignature (lay : Layer) (pieces : Pieces) : LayerSignature lay :=
  ⟨fun i => pieces.1.getD i.val 0,fun i => pieces.2.getD i.val 0⟩
def signPayload (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_,output) ← digestSearch rho message 0 attemptLimit | pure none
  let index := output.toNat % 2^31
  let chosen := selections output
  let state ← (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])
  let root ← forestPk index state.2.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)
def sign (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message
def serializeLayer {lay : Layer} (sig : LayerSignature lay) : HashInput :=
  (List.ofFn sig.values).flatMap (bytesLE 16) ++ (List.ofFn sig.path).flatMap (bytesLE 16)
def serialize (sig : Signature) : HashInput :=
  bytesLE 16 sig.rho ++ (List.ofFn sig.secrets).flatMap (bytesLE 16) ++
    (List.ofFn sig.proof).flatMap (bytesLE 16) ++
    (List.ofFn fun lay => serializeLayer (sig.layers lay)).flatten
def recoverChild (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) : Nat → Nat → Nat → M (Option (Digest × Nat))
  | level,node,used =>
      if !hasLeaf leaves level node then
        if h : used < 115 then pure (some (proof ⟨used,h⟩,used+1)) else pure none
      else match level with
      | 0 => do
          let value ← ftsLeaf index coord node (values.getD (leaves.idxOf node) 0)
          pure (some (value,used))
      | level+1 => do
          let some (left,next) ← recoverChild index coord leaves values proof level (2*node) used | pure none
          let some (right,next) ← recoverChild index coord leaves values proof level (2*node+1) next | pure none
          let value ← nodeHash 10 coord index (2^(11-(level+1))+node) left right
          pure (some (value,next))
def recoverFts (sig : Signature) (index : Nat) (chosen : List Selection) : M (Option Digest) := do
  let state ← (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots,used) := state | pure none
      let sel := chosen.getD coord ⟨0,[]⟩
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let values := (List.range 3).map (fun j => sig.secrets ⟨(coord*3+j)%21,Nat.mod_lt _ (by decide)⟩)
      let some (value,next) ← recoverChild index coord selected values sig.proof 7 sel.bucket used | pure none
      let result ← (List.range 4).foldlM
        (fun (state : Option (Digest × Nat)) j => do
          let some (value,used) := state | pure none
          if h : used < 115 then
            let other := sig.proof ⟨used,h⟩
            let pair := if sel.bucket/2^j%2=0 then (value,other) else (other,value)
            let parent ← nodeHash 10 coord index (2^(4-j-1)+sel.bucket/2^(j+1)) pair.1 pair.2
            pure (some (parent,used+1))
          else pure none) (some (value,next))
      let some (root,next) := result | pure none
      pure (some (roots ++ [root],next))) (some ([],0))
  let some (roots,used) := state | pure none
  if !(List.range (115-used)).all (fun j =>
      decide (sig.proof ⟨(used+j)%115,Nat.mod_lt _ (by decide)⟩ = 0)) then return none
  pure (some (← forestPk index roots))
def recoverLayer (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf,tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chain lay tree leaf i.val (digits.getD i.val 0)
      (maxDigit lay i.val-digits.getD i.val 0) ((sig.layers lay).values i)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := (sig.layers lay).path j
    let pair := if leaf/2^j.val%2=0 then (value,other) else (other,value)
    nodeHash 3 lay.val tree (2^(height lay-j.val-1)+leaf/2^(j.val+1)) pair.1 pair.2) value
def expandLayers (sig : Signature) (index : Nat) : Nat → Digest → M (Option (Digest × List (BitVec 32)))
  | 0,value => pure (some (value,[]))
  | n+1,value => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf,tree) := route index lay
      let some (counter,digits) ← counterSearch lay tree leaf value 0 counterLimit | pure none
      let root ← recoverLayer sig index lay digits
      let some (root,counters) ← expandLayers sig index n root | pure none
      pure (some (root,counters ++ [counter]))
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  let some (counter,output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := output.toNat%2^31
  let some root ← recoverFts sig index (selections output) | pure none
  let some (root,counters) ← expandLayers sig index 4 root | pure none
  if root ≠ pk then return none
  pure (some ⟨sig,counter,fun lay => counters.getD lay.val 0⟩)
def verifyLayers (w : Witness) (index : Nat) : Nat → Digest → M (Option Digest)
  | 0,root => pure (some root)
  | n+1,root => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf,tree) := route index lay
      let answer ← shortHash (encodingInput lay tree leaf root counter)
      let some digits := decode lay answer | pure none
      let value ← recoverLayer w.signature index lay digits
      verifyLayers w index n value
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho message w.digestCounter
  let chosen := selections output
  if !digestAdmissible output then return false
  let index := output.toNat%2^31
  let some root ← recoverFts w.signature index chosen | pure false
  let some root ← verifyLayers w index 4 root | pure false
  pure (root==pk)
end SigGolfCandidate.T3
