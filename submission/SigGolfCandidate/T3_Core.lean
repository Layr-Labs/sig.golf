import SigGolfCandidate.SphincsSecurity_Proof_Scheme_Bytes
import SigGolfCandidate.SphincsSecurity_Proof_Scheme_HashOutputSplit
import SigGolfCandidate.T3_Rev
import SigGolfCandidate.T3_FullCache_MacDefs
import SigGolfCandidate.ClaudeWCT_Arith_GF128

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
/-- Campaign T51: the top WOTS has 51 chains (27 radix-6, 21 radix-5, an r7 pair, a radix-6 checksum). -/
def chainCount (lay : Layer) : Nat := ![51, 43, 43, 43] lay
/-- Data digits read from the encoding word; the last chain of every layer is a checksum (T51: top chain 50). -/
def dataCount (lay : Layer) : Nat := if lay = 0 then 50 else 42
/-- Bits per chain digit: every chain, top included, has at most 8 positions, so 3. -/
def width (_lay : Layer) (_i : Nat) : Nat := 3
/-- Largest digit of chain `i`. Campaign T51: top chains 0..26 are radix 6 (9 triples g0..g8), 27..47 radix 5
(#938's r5 groups q9..q15), 48 and 49 radix 7 (the r7 pair), chain 50 the radix-6 checksum; every lower chain is
radix 8. -/
def maxDigit (lay : Layer) (i : Nat) : Nat :=
  if lay = 0 then (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) else 7
/-- Digit-sum targets: top 152 (T51, restricted top choice), lower layers 201/202/202. -/
def target (lay : Layer) : Nat := ![152, 201, 202, 202] lay
/-- Encoding values are below `2 ^ encodedBits lay`: no range bound on any layer. The T51 top word uses all 128 bits
(its fields partition bits 0..127; no spare bit). -/
def encodedBits (_lay : Layer) : Nat := 128
/-- Sum of the largest digits of a layer: top 27·5 + 21·4 + 2·6 + 5 = 236, lower 43·7 = 301. -/
def capacity (lay : Layer) : Nat := if lay = 0 then 236 else 301
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
/-- Leaf input. Campaign T51 ("endpad"): the top leaf is `end_0 | tweak | end_1..end_50` (832 bytes, 13 blocks), the
same shape as a lower leaf (#938: `0^16 | tweak | end_0..end_53`, 896 bytes). -/
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  if lay = 0 then bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (leafTweak lay tree leaf) ++ (ends.drop 1).flatMap (bytesLE 16)
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
/-! ### Top-bytes layer: top-tree node nonces (opus-topbytes A)
Every top node at height `h ∈ 1..11` (level `h` of `buildTopLevels`; heap `2^(12-h) + i`) is the first trial
`n < topNonceCap h` of `topNodeHashN heap n left right` whose zero bits (`topZeroOk h`) are clear; if no trial
passes, the last one (`n = topNonceCap h - 1`) is kept. The nonce is the 64-bit counter at bytes 32..39 of the node
input (bytes 40..47 stay 0); `n = 0` gives the old zero pad. Zero bits: the top `topZeroBits h` bits of the 128-bit
node value for `h ≤ 10`, bits 104..111 for `h = 11` (T51; #938: bits 98..108). The root (height 12) has no nonce.
A height with `b_h = 0` passes its first trial (nonce 0). -/
/-- Campaign T51: `b_1..b_11 = 0,0,1,1,2,3,4,5,6,7,8` (37 bits; #938 img-v6 had `b_h = h`, 66 bits). -/
def topZeroAlloc : List Nat := [0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 8]
def topZeroBits (h : Nat) : Nat := topZeroAlloc.getD h 0
/-- Trial cap `104 << b`. -/
def topNonceCap (h : Nat) : Nat := 104 * 2 ^ topZeroBits h
def topZeroOk (h : Nat) (value : Digest) : Bool :=
  if h = 11 then value.toNat / 2 ^ 104 % 2 ^ 8 == 0 else value.toNat / 2 ^ (128 - topZeroBits h) == 0
def nonceBytes (n : Nat) : HashInput := bytesLE 16 (BitVec.ofNat 128 (n % 2 ^ 64))
def topNodeInput (heap n : Nat) (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (nodeTweak 3 0 0 heap) ++ nonceBytes n ++ bytesLE 16 right
def topNodeHashN (heap n : Nat) (left right : Digest) : M Digest :=
  projHash (nodeHalfHigh 3 0 heap) (topNodeInput heap n left right)
/-- Nonce search from trial `n` with `fuel` trials left; the last trial is kept. -/
def topNonceSearch (h heap : Nat) (left right : Digest) : Nat → Nat → M (Nat × Digest)
  | 0, n => do
      let value ← topNodeHashN heap n left right
      pure (n, value)
  | fuel + 1, n => do
      let value ← topNodeHashN heap n left right
      if topZeroOk h value then pure (n, value) else topNonceSearch h heap left right fuel (n + 1)
/-- The canonical top node at height `h` (`1 ≤ h ≤ 11`): nonce and value. -/
def topNodeAt (h heap : Nat) (left right : Digest) : M (Nat × Digest) :=
  topNonceSearch h heap left right (topNonceCap h - 1) 0
def buildTopLevel (level : Nat) (nodes : List Digest) : M (List Digest) :=
  (List.range (nodes.length / 2)).mapM fun i =>
    if level = 12 then nodeHash 3 0 0 (2 ^ (12 - level) + i) (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)
    else Prod.snd <$> topNodeAt level (2 ^ (12 - level) + i) (nodes.getD (2*i) 0) (nodes.getD (2*i+1) 0)
def buildTopLevels (leaves : List Digest) : M (List (List Digest)) :=
  (List.range' 1 12).foldlM (fun levels level => do
    let nodes ← buildTopLevel level (levels.getD (level-1) [])
    pure (levels ++ [nodes])) [leaves]
/-! ### Top WOTS seed families (families of 4 leaves, carry-packed; T51: 31 coefficients, #938 img-v6: 39)
Top leaf `leaf` belongs to the family `f = leaf / 4`, whose 31 GF(2^128) coefficients are the ordinals
`topCoefOrdinal leaf j = 31 f + j` (`j < 31`); ordinal `o` is half `o % 2` (low half first) of the private pair
`topSeedPair (o / 2)` = `privatePair 0 0 0 (o / 2) 0` (= `WCT9.lowerSeedPair 0 0 (o / 2)`). 31 is odd, so an odd
family starts with the high half of the pair whose low half ends the previous (even) family: the carry.
* Signer form `topCoefs leaf`: the 16 pairs `31 f / 2 + j` (`j < 16`), flattened, then `drop (f % 2)`, `take 31`.
* Keygen form `topCoefsK f carry`: the pairs `31 f / 2 + j` for `j ∈ [f % 2, 16)` (first pair `(31 f + f % 2) / 2`,
  `16 - f % 2` queries) appended to `[]` (even `f`) or `[carry]` (odd `f`); returns the 31 coefficients and the
  carry slot (`acc.getD 31 0`: ordinal `31 (f + 1)` for even `f`), as the keygen machine's `ktop` does.
31 = zero cap 7 x 4 leaves + 3: the producer reveals at most 7 seeds of a leaf (`WCT9.producerZeroCap 0`).
The seed of chain `i` of leaf `leaf` is `familyEval coefs (topPoint leaf i)`, `topPoint leaf i = (leaf % 4) · 64 + i + 1`
(`≤ 3 · 64 + 51 = 243`). The pre-T8D per-chain top seeds (`privatePair 0 0 0 pair leaf`) are retired;
`buildLeaf`/`buildTree` remain for the T3 lower layers. -/
def topCoefCount : Nat := 31
def topCoefPairs : Nat := 16
def topCoefOrdinal (leaf j : Nat) : Nat := topCoefCount * (leaf / 4) + j
def topSeedPair (pair : Nat) : M (Digest × Digest) := privatePair 0 0 0 pair 0
/-- The pairs `first + j`, `j ∈ [start, topCoefPairs)`, appended low half first to `init`. -/
def topPairsFrom (first start : Nat) (init : List Digest) : M (List Digest) :=
  (List.range' start (topCoefPairs - start)).foldlM (fun acc j => do
    let p ← topSeedPair (first + j)
    pure (acc ++ [p.1, p.2])) init
/-- Signer form: the 31 coefficients of top leaf `leaf`'s family, recomputed from 16 pairs. -/
def topCoefs (leaf : Nat) : M (List Digest) := do
  let acc ← topPairsFrom (topCoefCount * (leaf / 4) / 2) 0 []
  pure ((acc.drop (leaf / 4 % 2)).take topCoefCount)
/-- Keygen form (family `f`, carry from family `f - 1`): the 31 coefficients and the next carry. -/
def topCoefsK (f : Nat) (carry : Digest) : M (List Digest × Digest) := do
  let acc ← topPairsFrom (topCoefCount * f / 2) (f % 2) (if f % 2 = 0 then [] else [carry])
  pure (acc.take topCoefCount, acc.getD topCoefCount 0)
def topPoint (leaf i : Nat) : Nat := leaf % 4 * 64 + i + 1
def topSeed (coefs : List Digest) (leaf i : Nat) : Digest := ClaudeWCT.Arith.familyEval coefs (topPoint leaf i)
/-! ### Witness stack (opus-wstack, charge 86): top chain pairing
The even top chains `0, 2, .., 50` are value-first ("G") chains: their step input is `value | header | 0 | 0` and every
interior step (`step + 1 < maxDigit 0 i`) keeps the HIGH half; the terminal step keeps the low half. Their F partners
are `1, 3, .., 49`; T51's chain 50 is a G chain without an F partner.
Campaign T51: chain 0 keeps the HIGH half on EVERY step, its terminal step included (its end `end_0` precedes the
leaf tweak in the endpad leaf; the verifier writes its terminal answer at the leaf slot - 16, like a lower chain 0). -/
def topIsG (i : Nat) : Bool := decide (i % 2 = 0) && decide (i ≤ 50)
def topChainHigh (i step : Nat) : Bool := topIsG i && (decide (step + 1 < maxDigit 0 i) || decide (i = 0))
def topChainInput (leaf i step : Nat) (value : Digest) : HashInput :=
  if topIsG i then bytesLE 16 value ++ bytesLE 16 (chainHeader 0 0 leaf i step) ++ zero16 ++ zero16
  else chainInput 0 0 leaf i step value
/-- Top WOTS chain (tree 0) of the paired scheme. -/
def topChain (leaf i start count : Nat) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => projHash (topChainHigh i step) (topChainInput leaf i step value)) value
/-- Witness stack: the WOTS chain of layer `lay` in the T3 scheme text (`topChain` on the top tree, tree 0;
`chain` below). -/
def layChain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) : M Digest :=
  if lay = 0 then topChain leaf i start count value else chain lay tree leaf i start count value
theorem layChain_top (tree leaf i start count : Nat) (value : Digest) :
    layChain 0 tree leaf i start count value = topChain leaf i start count value := by
  unfold layChain; rw [if_pos rfl]
theorem layChain_lower {lay : Layer} (h : lay ≠ 0) (tree leaf i start count : Nat) (value : Digest) :
    layChain lay tree leaf i start count value = chain lay tree leaf i start count value := by
  unfold layChain; rw [if_neg h]
theorem topChain_add (leaf i start a b : Nat) (value : Digest) :
    topChain leaf i start (a + b) value =
      (topChain leaf i start a value >>= topChain leaf i (start + a) b) := by
  unfold topChain
  rw [← List.range'_append_1, List.foldlM_append]
theorem layChain_add (lay : Layer) (tree leaf i start a b : Nat) (value : Digest) :
    layChain lay tree leaf i start (a + b) value =
      (layChain lay tree leaf i start a value >>= layChain lay tree leaf i (start + a) b) := by
  unfold layChain
  split
  · exact topChain_add leaf i start a b value
  · unfold chain; rw [← List.range'_append_1, List.foldlM_append]
/-- Top leaf (tree 0) with the family coefficients `coefs`; `signatureOnly` returns only the signature values
(`root = 0`). -/
def buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool := false) :
    M (Digest × List Digest) := do
  let state ← (List.range (chainCount 0)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let value ← topChain leaf i 0 digit (topSeed coefs leaf i)
      if signatureOnly then return (state.1, state.2 ++ [value])
      let last ← topChain leaf i digit (maxDigit 0 i - digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  if signatureOnly then return (0, state.2)
  let root ← leafHash 0 0 leaf state.1
  pure (root, state.2)
/-- Top leaf (tree 0) with family seeds (signer form of the coefficients). -/
def buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool := false) : M (Digest × List Digest) := do
  let coefs ← topCoefs leaf
  buildLeafTopC leaf coefs digits signatureOnly
/-- Keygen coefficient state `(coefficients, carry)` for top leaf `leaf`: refreshed (`topCoefsK`) at a family start
(`leaf % 4 = 0`), kept otherwise. -/
def topFamilyCoefs (leaf : Nat) (cc : List Digest × Digest) : M (List Digest × Digest) :=
  if leaf % 4 = 0 then topCoefsK (leaf / 4) cc.2 else pure cc
/-- One keygen top leaf: the family coefficients (`topFamilyCoefs`), then the leaf with those coefficients.
State: (roots, coefficients, carry). -/
def topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) :
    M (List Digest × List Digest × Digest) := do
  let cc ← topFamilyCoefs leaf st.2
  let r ← buildLeafTopC leaf cc.1 []
  pure (st.1 ++ [r.1], cc)
/-- The top tree (keygen): all 4096 top leaves with family seeds, then the 12 node levels. -/
def buildTopTree : M (List (List Digest)) := do
  let st ← (List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0)
  buildTopLevels st.1
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
/-! ### T51 top word
Fields of the 128-bit top word `v` (they partition bits 0..127; no spare bit):
* r6 groups `g0..g6` in bits `8 g .. 8 g + 7`, `g7` in 112..119, `g8` in 120..127 (chains `3 g .. 3 g + 2`,
  `rank = d0 + 6 d1 + 36 d2 < 216`); `g0` stores `raw = rank + 40` (valid iff `raw ≥ 40`), `g1..g8` store
  `raw = rank` (valid iff `raw < 216`);
* the r7 pair (chains 48, 49) in bits 56..62, stored flipped (`rank = 127 - raw7 = d48 + 7 d49 < 49`);
* #938's r5 groups `q9..q15` in bits `7 q .. 7 q + 6` (63..111), stored flipped (`rank = 127 - raw7 < 125`,
  chains `3 q .. 3 q + 2`, `rank = d0 + 5 d1 + 25 d2`).
The checksum chain 50 is not stored: its digit is `target 0 - sum` and must lie in `[0, 5]` (`decode`). -/
/-- T51: the flipped 7-bit fields (r7 pair and r5 groups, bits 56..111). -/
def topMask : Nat := 2 ^ 112 - 2 ^ 56
def topFlip (value : Digest) : Digest := value ^^^ BitVec.ofNat 128 topMask
/-- The top word with its 7-bit fields unflipped (the r6 fields unchanged). -/
def topCode (value : Digest) : Nat := (topFlip value).toNat
/-- Legacy (NF17) bit position of a raw radix-8 top digit; unused by the T51 top word. -/
def topRawShift (i : Nat) : Nat := if i = 53 then 119 else 122 + 3 * (i - 51)
/-- T51: bit position of r6 group `g` (`g0..g6` at `8 g`, `g7` at 112, `g8` at 120). -/
def r6Shift (g : Nat) : Nat := if g < 7 then 8 * g else 112 + 8 * (g - 7)
/-- T51: raw 8-bit field of r6 group `g` (read through `topCode`, which leaves the r6 fields unchanged). -/
def r6Raw (value : Digest) (g : Nat) : Nat := topCode value / 2 ^ r6Shift g % 256
/-- T51: rank of r6 group `g` (group 0 is offset by 40). -/
def r6Rank (value : Digest) (g : Nat) : Nat := if g = 0 then r6Raw value 0 - 40 else r6Raw value g
/-- T51: range check of r6 group `g`. -/
def r6Valid (value : Digest) (g : Nat) : Bool :=
  if g = 0 then decide (40 ≤ r6Raw value 0) else decide (r6Raw value g < 216)
/-- T51: rank of r5 group `q` (9..15): `127 - raw` of bits `7 q .. 7 q + 6`. -/
def r5Rank (value : Digest) (q : Nat) : Nat := topCode value / 2 ^ (7 * q) % 128
/-- T51: rank of the r7 pair: `127 - raw` of bits 56..62 (`d48 + 7 d49`). -/
def r7Rank (value : Digest) : Nat := topCode value / 2 ^ 56 % 128
def coreDigit (lay : Layer) (value : Digest) (i : Nat) : Nat :=
  if lay = 0 then
    if i < 27 then r6Rank value (i / 3) / 6 ^ (i % 3) % 6
    else if i < 48 then r5Rank value (i / 3) / 5 ^ (i % 3) % 5
    else if i < 50 then r7Rank value / 7 ^ (i - 48) % 7
    else 0
  else value.toNat / 2 ^ lowerShift i % 8
/-- T51: every r6 group in range, every r5 rank below 125, the r7 rank below 49. -/
def topRanksValid (value : Digest) : Bool :=
  (List.range 9).all (r6Valid value) && (List.range' 9 7).all (fun q => decide (r5Rank value q < 125)) &&
    decide (r7Rank value < 49)
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
    if topRanksValid value = true ∧ total ≤ target lay ∧ target lay - total < 6 then
      some (digits ++ [target lay - total])
    else none
  else if lowerSpare value ∧ total ≤ target lay ∧ target lay - total < 8 then
    some (digits ++ [target lay - total])
  else none
def creditFloor (lay : Layer) : Nat := ![7, 0, 0, 0] lay
/-- Legacy T3 top credit (T51 digits): chains whose digit is one below the maximum, the checksum included. -/
def topCredit (value : Digest) : Nat :=
  ((List.range 51).map fun i =>
    if (dataDigits 0 value ++ [target 0 - (dataDigits 0 value).sum]).getD i 0 + 1 = maxDigit 0 i then 1 else 0).sum
def encCredit (lay : Layer) (value : Digest) : Nat := if lay = 0 then topCredit value else 0
def searchDecode (lay : Layer) (value : Digest) : Option (List Nat) :=
  if encCredit lay value < creditFloor lay then none else decode lay value
/-- Top digits signed when the top counter search is exhausted (T51 at target 152): 50 threes (chains 0..49), checksum 2
(sum 152, no zero digit; word `0x818144891224489167818181818181a9`). -/
def dummyTop : List Nat := List.replicate 50 3 ++ [2]
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
    layChain lay tree leaf i.val (digits.getD i.val 0)
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
