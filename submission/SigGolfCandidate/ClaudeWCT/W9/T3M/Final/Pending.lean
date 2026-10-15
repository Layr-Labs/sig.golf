import SigGolfCandidate.ClaudeWCT.Bank.WCTRev3
import SigGolfCandidate.ClaudeWCT.Bank.WCTHonest
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Moment
import SigGolfCandidate.ClaudeWCT.WCT9.QueriesWots
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.ExpansionBudget
import SigGolfCandidate.ClaudeWCT.W9.T3M.Submission
import SigGolfCandidate.T3M.Verify.HashOk
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodecC
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.SecurityP

section
namespace ClaudeWCT.W9.T3.SourceReplay
open OracleComp OracleSpec
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_mapM
  hashOnly_foldlM hashOnly_shortHash hashOnly_privatePair hashOnly_nodeHash fixedAnswers fixed_replay)
open ClaudeWCT.WCT9 (Signature Witness)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[aesop safe apply] theorem hashOnly_chain (index coord selected i start count : Nat) (value : Digest) :
    HashOnly (ClaudeWCT.WCT9.chain index coord selected i start count value) := by
  unfold ClaudeWCT.WCT9.chain; hashes
@[aesop safe apply] theorem hashOnly_leafHash (index coord selected : Nat) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash; hashes
@[aesop safe apply] theorem hashOnly_forestPk (index : Nat) (pairs : List (Digest × Digest)) :
    HashOnly (ClaudeWCT.WCT9.forestPk index pairs) := by
  unfold ClaudeWCT.WCT9.forestPk; hashes
@[aesop safe apply] theorem hashOnly_ite' {α : Type} {c : Prop} [Decidable c] {p q : M α}
    (hp : HashOnly p) (hq : HashOnly q) : HashOnly (if c then p else q) := by
  split
  · exact hp
  · exact hq
@[aesop safe apply] theorem hashOnly_ftsSeedPair (index coord pair : Nat) :
    HashOnly (ClaudeWCT.WCT9.ftsSeedPair index coord pair) := by
  unfold ClaudeWCT.WCT9.ftsSeedPair; exact hashOnly_privatePair _ _ _ _ _
@[aesop safe apply] theorem hashOnly_lowerSeedPair (lay : Layer) (tree pair : Nat) :
    HashOnly (ClaudeWCT.WCT9.lowerSeedPair lay tree pair) := by
  unfold ClaudeWCT.WCT9.lowerSeedPair; exact hashOnly_privatePair _ _ _ _ _
theorem hashOnly_packedSecret (pairQuery : Nat → M (Digest × Digest)) (h : ∀ p, HashOnly (pairQuery p))
    (q : Nat) (carry : Digest) : HashOnly (ClaudeWCT.WCT9.packedSecret pairQuery q carry) := by
  unfold ClaudeWCT.WCT9.packedSecret
  split
  · exact hashOnly_bind (h _) fun _ => hashOnly_pure _
  · exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_packedSecret_fts (index coord q : Nat) (carry : Digest) :
    HashOnly (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.ftsSeedPair index coord) q carry) :=
  hashOnly_packedSecret _ (hashOnly_ftsSeedPair index coord) q carry
@[aesop safe apply] theorem hashOnly_packedSecret_lower (lay : Layer) (tree q : Nat) (carry : Digest) :
    HashOnly (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.lowerSeedPair lay tree) q carry) :=
  hashOnly_packedSecret _ (hashOnly_lowerSeedPair lay tree) q carry
@[aesop safe apply] theorem hashOnly_ftsCoefs (index coord : Nat) :
    HashOnly (ClaudeWCT.WCT9.ftsCoefs index coord) := by
  unfold ClaudeWCT.WCT9.ftsCoefs
  exact hashOnly_foldlM _ _ (fun acc j =>
    hashOnly_bind (hashOnly_ftsSeedPair index coord j) fun _ => hashOnly_pure _) _
@[aesop safe apply] theorem hashOnly_leafHashP (index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHashP index coord selected pad ends) := by
  unfold ClaudeWCT.WCT9.leafHashP; exact SigGolfCandidate.T3.SourceReplay.hashOnly_shortHash _
@[aesop safe apply] theorem hashOnly_buildChildF (index coord selected : Nat) (word : ClaudeWCT.WCT9.Rank)
    (coefs : List Digest) (padL : Digest) :
    HashOnly (ClaudeWCT.WCT9.buildChildF index coord selected word coefs padL) := by
  unfold ClaudeWCT.WCT9.buildChildF
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · exact hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (hashOnly_leafHashP _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_wctNodeHash (coord index heap : Nat) (left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctNodeHash coord index heap left right) := by
  unfold ClaudeWCT.WCT9.wctNodeHash; exact hashOnly_nodeHash _ _ _ _ _ _
@[aesop safe apply] theorem hashOnly_wctTopHash (coord index heap : Nat) (left pad right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctTopHash coord index heap left pad right) := by
  unfold ClaudeWCT.WCT9.wctTopHash ClaudeWCT.WCT9.highHash
  exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_publicHash _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_wctHeapNode (coord index heap : Nat) (padR left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctHeapNode coord index heap padR left right) := by
  unfold ClaudeWCT.WCT9.wctHeapNode
  exact hashOnly_ite' (hashOnly_wctTopHash _ _ _ _ _ _) (hashOnly_wctNodeHash _ _ _ _ _)
@[aesop safe apply] theorem hashOnly_heapBuild (index coord : Nat) (padR : Digest) (leaves : List Digest) :
    HashOnly (ClaudeWCT.WCT9.heapBuild index coord padR leaves) := by
  unfold ClaudeWCT.WCT9.heapBuild
  exact hashOnly_foldlM _ _ (fun nodes heap =>
    hashOnly_bind (hashOnly_wctHeapNode coord index heap padR _ _) fun _ => hashOnly_pure _) _
@[aesop safe apply] theorem hashOnly_buildCoordinateF (index : Nat) (coord : ClaudeWCT.WCT9.Coord)
    (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) (prev : Digest × Digest) :
    HashOnly (ClaudeWCT.WCT9.buildCoordinateF index coord selected word prev) := by
  unfold ClaudeWCT.WCT9.buildCoordinateF
  refine hashOnly_bind (hashOnly_ftsCoefs index coord.val) fun coefs => ?_
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state j => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildChildF index coord.val j word _ prev.1) fun r => ?_
    rcases r with ⟨root, values⟩
    exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_heapBuild index coord.val prev.2 state.1) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (carry : Digest) : HashOnly (ClaudeWCT.WCT9.buildLeafP lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafP
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_packedSecret_lower _ _ _ _) fun r => ?_
    rcases r with ⟨seed, carry'⟩
    exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (carry : Digest) : HashOnly (ClaudeWCT.WCT9.buildLeafPF lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafPF
  refine hashOnly_bind ?_ fun cc => ?_
  · unfold ClaudeWCT.WCT9.lowerCoefs
    refine hashOnly_foldlM _ _ (fun state j => ?_) _
    refine hashOnly_bind (hashOnly_packedSecret_lower _ _ _ _) fun r => ?_
    rcases r with ⟨coef, carry'⟩
    exact hashOnly_pure _
  rcases cc with ⟨coefs, carry'⟩
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_buildLevelsBelow (tag lay tree h : Nat) (leaves : List Digest) :
    HashOnly (ClaudeWCT.WCT9.buildLevelsBelow tag lay tree h leaves) := by
  unfold ClaudeWCT.WCT9.buildLevelsBelow; hashes
@[aesop safe apply] theorem hashOnly_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.buildTreeP lay tree selected digits) := by
  unfold ClaudeWCT.WCT9.buildTreeP
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state leaf => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildLeafPF lay tree leaf _ _) fun r => ?_
    rcases r with ⟨⟨root, values⟩, carry⟩
    exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_buildLevelsBelow _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.digestSearch; hashes
@[aesop safe apply] theorem hashOnly_openingStep (index : Nat) (output : HashOutput)
    (state : List ClaudeWCT.WCT9.Opening × List (Digest × Digest)) (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.openingStep index output state coord) := by
  unfold ClaudeWCT.WCT9.openingStep; hashes
@[aesop safe apply] theorem hashOnly_forestRows (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows; hashes
@[aesop safe apply] theorem hashOnly_signForest (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest; hashes
@[aesop safe apply] theorem hashOnly_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput)
    (coord : ClaudeWCT.WCT9.Coord) (prev : Digest × Digest) :
    HashOnly (ClaudeWCT.WCT9.recoverCoordinate sig index output coord prev) := by
  unfold ClaudeWCT.WCT9.recoverCoordinate; hashes
@[aesop safe apply] theorem hashOnly_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.recoverFts sig index output) := by
  unfold ClaudeWCT.WCT9.recoverFts ClaudeWCT.WCT9.recoverFtsFrom; hashes
@[aesop safe apply] theorem hashOnly_encodingHash (lay : Layer) (input : HashInput) :
    HashOnly (ClaudeWCT.WCT9.encodingHash lay input) := by
  exact (ClaudeWCT.WCT9.allQueries_encodingHash_iff lay input _).mpr (hashOnly_shortHash input)
@[aesop safe apply] theorem hashOnly_layerCounterSearch (lay : Layer) (tree leaf : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
@[aesop safe apply] theorem hashOnly_signLayersBC (cache : Cache) (index n : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) :
    HashOnly (ClaudeWCT.WCT9.signLayersBC cache index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.signLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.signLayersBC; hashes
@[aesop safe apply] theorem hashOnly_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer)
    (digits : List Nat) : HashOnly (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair; hashes
@[aesop safe apply] theorem hashOnly_expandLayersBC (sig : Signature) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.expandLayersBC sig index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
@[aesop safe apply] theorem hashOnly_verifyTop (sig : Signature) (index : Nat) (answer : Digest) :
    HashOnly (ClaudeWCT.WCT9.verifyTop sig index answer) := by
  unfold ClaudeWCT.WCT9.verifyTop
  exact ClaudeWCT.W9.T3M.allQ_topDecodeRun _ _ _
    (fun _ _ => SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun _ =>
        hashOnly_foldlM _ _ (fun _ _ => hashOnly_nodeHash _ _ _ _ _ _) _
@[aesop safe apply] theorem hashOnly_recoverLayerPairGuard (sig : Signature) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.recoverLayerPairGuard sig index lay answer digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPairGuard ClaudeWCT.WCT9.lowerGuardedRun
  hashes
@[aesop safe apply] theorem hashOnly_verifyLayersBC (w : Witness) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.verifyLayersBC w index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
@[aesop safe apply] theorem hashOnly_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signPayloadWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signPayloadWith; hashes
@[aesop safe apply] theorem hashOnly_signWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signWith; hashes
@[aesop safe apply] theorem hashOnly_expandWith (limit : Nat) (message : Message) (pk : Digest)
    (sig : Signature) : HashOnly (ClaudeWCT.WCT9.expandWith limit message pk sig) := by
  unfold ClaudeWCT.WCT9.expandWith; hashes
@[aesop safe apply] theorem hashOnly_verifyWith (limit : Nat) (message : Message) (pk : Digest)
    (w : Witness) : HashOnly (ClaudeWCT.WCT9.verifyWith limit message pk w) := by
  unfold ClaudeWCT.WCT9.verifyWith; hashes
@[aesop safe apply] theorem hashOnly_signPayload (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.signPayload cache message) :=
  hashOnly_signPayloadWith _ cache message
@[aesop safe apply] theorem hashOnly_sign (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.sign cache message) :=
  hashOnly_signWith _ cache message
theorem hashOnly_topFold (sig : Signature) (index : Nat) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.topFold sig index digits) := by
  unfold ClaudeWCT.WCT9.topFold ClaudeWCT.WCT9.topEnds
  refine hashOnly_bind (hashOnly_mapM _ _ fun i => SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _)
    fun ends => ?_
  refine hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun value => ?_
  exact hashOnly_foldlM _ _ (fun v j => by unfold ClaudeWCT.WCT9.topStep; exact hashOnly_nodeHash _ _ _ _ _ _) _
theorem hashOnly_topNode (index : Nat) (v o : Digest) : HashOnly (ClaudeWCT.WCT9.topNode index v o) := by
  unfold ClaudeWCT.WCT9.topNode; exact hashOnly_nodeHash _ _ _ _ _ _
theorem hashOnly_expandLayersT (sig : Signature) (index : Nat) (o : Digest) (n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.expandLayersT sig index o n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.expandLayersT; exact hashOnly_pure _
  | succ n ih =>
    unfold ClaudeWCT.WCT9.expandLayersT
    refine hashOnly_bind (hashOnly_layerCounterSearch _ _ _ _ _ _) fun r => ?_
    rcases r with _ | ⟨counter, digits⟩
    · exact hashOnly_pure _
    · exact hashOnly_ite' (hashOnly_bind (hashOnly_topFold _ _ _) fun _ =>
          hashOnly_bind (hashOnly_topNode _ _ _) fun _ => hashOnly_pure _)
        (hashOnly_bind (hashOnly_recoverLayerPair _ _ _ _) fun _ => hashOnly_bind (ih _) fun r => by
          rcases r with _ | ⟨v, root, cs⟩ <;> exact hashOnly_pure _)
theorem hashOnly_searchTop (index : Nat) (v sib pk : Digest) (fuel c : Nat) :
    HashOnly (ClaudeWCT.WCT9.searchTop index v sib pk fuel c) := by
  induction fuel generalizing c with
  | zero => unfold ClaudeWCT.WCT9.searchTop; exact hashOnly_pure _
  | succ fuel ih =>
    unfold ClaudeWCT.WCT9.searchTop
    exact hashOnly_bind (hashOnly_topNode _ _ _) fun _ => hashOnly_ite' (hashOnly_pure _) (ih _)
theorem hashOnly_expandS (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (ClaudeWCT.WCT9.expandS limit message pk sig) := by
  unfold ClaudeWCT.WCT9.expandS
  refine hashOnly_bind (hashOnly_digestSearch _ _ _ _) fun r => ?_
  rcases r with _ | ⟨counter, output⟩
  · exact hashOnly_pure _
  refine hashOnly_bind (hashOnly_recoverFts _ _ _) fun root => ?_
  refine hashOnly_bind (hashOnly_expandLayersT _ _ _ _ _) fun r => ?_
  rcases r with _ | ⟨v, root', cs⟩
  · exact hashOnly_pure _
  refine hashOnly_ite' (hashOnly_pure _) (hashOnly_bind (hashOnly_searchTop _ _ _ _ _ _) fun r => ?_)
  rcases r with _ | c <;> exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (ClaudeWCT.WCT9.Rev3.expand message pk sig) := by
  unfold ClaudeWCT.WCT9.Rev3.expand
  exact hashOnly_map _ (hashOnly_expandS _ message pk sig)
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
    HashOnly (ClaudeWCT.WCT9.Rev3.verify message pk w) :=
  hashOnly_verifyWith _ message pk w
theorem sign_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (cache : Cache) (message : Message) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.sign cache message)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.sign cache message)) :=
  fixed_replay secret hash _ (hashOnly_sign cache message)
theorem expand_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (sig : Signature) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.expand message pk sig)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.expand message pk sig)) :=
  fixed_replay secret hash _ (hashOnly_expand message pk sig)
theorem verify_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (w : Witness) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.verify message pk w)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.verify message pk w)) :=
  fixed_replay secret hash _ (hashOnly_verify message pk w)
end ClaudeWCT.W9.T3.SourceReplay
end
section
namespace ClaudeWCT.W9.T3.NonceSampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev NonceOutputs := Message → HashOutput
abbrev SearchOutputs := SearchKey → HashOutput
abbrev QueryKey := Message ⊕ SearchKey
@[irreducible] noncomputable def nonceSampler : SampleableType NonceOutputs :=
  Derivation.outputSampler Message
@[irreducible] noncomputable def combinedSampler : SampleableType (QueryKey → HashOutput) :=
  Derivation.outputSampler QueryKey
noncomputable local instance : SampleableType NonceOutputs := nonceSampler
noncomputable local instance : SampleableType SearchOutputs := Presampling.tableSampler
noncomputable local instance : SampleableType (QueryKey → HashOutput) := combinedSampler
def nonceInputs (secret : BitVec 256) (message : Message) : HashInput :=
  privateInput secret (.inr (.inl message))
theorem nonceInputs_injective (secret : BitVec 256) : Function.Injective (nonceInputs secret) := by
  intro a b he
  exact Sum.inl.inj (Sum.inr.inj (privateInput_injective secret he))
theorem nonceInputs_length (secret : BitVec 256) (message : Message) :
    (nonceInputs secret message).length = 128 := by
  simp only [nonceInputs, privateInput_nonce, List.length_append, SphincsSecurity.bytesLE_length,
    zero16, List.length_replicate]
theorem nonceInputs_ne_searchQuery (secret : BitVec 256) (message : Message) (key : SearchKey) :
    nonceInputs secret message ≠ searchQuery key := by
  intro he
  have hl := congrArg List.length he
  rw [nonceInputs_length, searchQuery_length] at hl
  omega
def combinedInputs (secret : BitVec 256) : QueryKey → HashInput :=
  Sum.elim (nonceInputs secret) searchQuery
theorem combinedInputs_injective (secret : BitVec 256) : Function.Injective (combinedInputs secret) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (nonceInputs_injective secret he)
    | inr b => exact False.elim (nonceInputs_ne_searchQuery secret a b he)
  | inr a =>
    cases b with
    | inl b => exact False.elim (nonceInputs_ne_searchQuery secret b a he.symm)
    | inr b => exact congrArg Sum.inr (searchQuery_injective he)
noncomputable def preparedCache (secret : BitVec 256)
    (nonceOutputs : NonceOutputs) (searchOutputs : SearchOutputs) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ (combinedInputs secret) (Sum.elim nonceOutputs searchOutputs)
theorem preparedCache_nonce (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (message : Message) :
    preparedCache secret nonceOutputs searchOutputs (nonceInputs secret message) = some (nonceOutputs message) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inl message)
theorem preparedCache_search (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (key : SearchKey) :
    preparedCache secret nonceOutputs searchOutputs (searchQuery key) = some (searchOutputs key) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inr key)
theorem combined_uniform :
    𝒮[($ᵗ (QueryKey → HashOutput) : ProbComp _)] =
    𝒮[do
      let nonces ← ($ᵗ NonceOutputs : ProbComp _)
      let searches ← ($ᵗ SearchOutputs : ProbComp _)
      pure (Sum.elim nonces searches)] := by
  classical
  let : Fintype SearchOutputs := @Pi.instFintype SearchKey (fun _ => HashOutput)
    (Classical.decEq SearchKey) inferInstance (fun _ => inferInstance)
  let : Fintype NonceOutputs := @Pi.instFintype Message (fun _ => HashOutput)
    (Classical.decEq Message) inferInstance (fun _ => inferInstance)
  let split : (QueryKey → HashOutput) ≃ NonceOutputs × SearchOutputs :=
    Equiv.sumArrowEquivProdArrow Message SearchKey HashOutput
  have he := evalSPMF_map_bijective_uniform_cross
    (α := NonceOutputs × SearchOutputs) (β := QueryKey → HashOutput) split.symm split.symm.bijective
  have hp := evalDist_independent_uniform_pair (α := NonceOutputs) (β := SearchOutputs)
  rw [evalSPMF_map, ← hp] at he
  simpa only [evalSPMF_bind, evalSPMF_pure, map_bind, map_pure, split,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk] using he.symm
theorem presample_combined {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (QueryKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (cacheTable ∅ (combinedInputs secret) outputs)] := by
  let : SampleableType (QueryKey → SphincsSecurity.HashOutput) := combinedSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (QueryKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec))
        (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret)))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput)
      (combinedInputs secret) (combinedInputs_injective secret) ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let nonceOutputs ← ($ᵗ NonceOutputs : ProbComp _)
      let searchOutputs ← ($ᵗ SearchOutputs : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (preparedCache secret nonceOutputs searchOutputs)] := by
  rw [presample_combined, evalSPMF_bind, combined_uniform]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  rfl
end ClaudeWCT.W9.T3.NonceSampling
end
section
namespace ClaudeWCT.W9.T3.Completeness
open OracleComp OracleSpec ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_foldlM hashOnly_keygen
  fixedAnswers fixed_replay)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand hashOnly_verify)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true
theorem honestProgram_true (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceed answers) :
    evalWithAnswerFn answers (honestProgram message) = true := by
  obtain ⟨sig, witness, hs, he, hv⟩ := Correctness.honest_signing_complete_of_searches answers hgood message
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
theorem honestProgram_true_for (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceedFor answers message) :
    evalWithAnswerFn answers (honestProgram message) = true := by
  obtain ⟨sig, witness, hs, he, hv⟩ := Correctness.signing_complete_for_of_searches answers
    (evalWithAnswerFn answers keygen) (SigGolfCandidate.T3.Correctness.keygen_correct answers) message hgood
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
theorem hashOnly_honestProgram (message : Message) : HashOnly (honestProgram message) := by
  unfold honestProgram
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (hashOnly_sign keys.2 message)
  intro sig
  cases sig with
  | none => exact hashOnly_pure false
  | some sig =>
    apply hashOnly_bind (hashOnly_expand message keys.1 sig)
    intro witness
    cases witness with
    | none => exact hashOnly_pure false
    | some witness => exact hashOnly_verify message keys.1 witness
theorem hashOnly_everyMessageProgram : HashOnly everyMessageProgram := by
  apply hashOnly_foldlM
  intro accepted message
  exact hashOnly_bind (hashOnly_honestProgram message) fun _ => hashOnly_pure _
theorem everyMessageProgram_true (answers : SigGolfCandidate.T3.Correctness.Answers)
    (hall : ∀ message, evalWithAnswerFn answers (honestProgram message) = true) :
    evalWithAnswerFn answers everyMessageProgram = true := by
  have hf : ∀ messages : List Message, ∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted) = accepted := by
    intro messages
    induction messages with
    | nil => intro accepted; rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hall, Bool.and_true]
      exact ih accepted
  exact hf _ true
theorem everyMessageProgram_true_of_complete (answers : SigGolfCandidate.T3.Correctness.Answers)
    (hcomplete : Correctness.SigningComplete answers (evalWithAnswerFn answers keygen)) :
    evalWithAnswerFn answers everyMessageProgram = true := by
  apply everyMessageProgram_true
  intro message
  obtain ⟨sig, witness, hs, he, hv⟩ := hcomplete message
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
noncomputable local instance : SampleableType (SearchKey → HashOutput) :=
  Presampling.tableSampler
theorem failure_le_bad_table (secret : BitVec 256) (program : M Bool)
    (good : (SearchKey → HashOutput) → Prop)
    (hzero : ∀ outputs, good outputs →
      Pr[fun value => value = false |
        (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
          (Presampling.preparedCache outputs)] = 0) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] ≤
    Pr[fun outputs => ¬good outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value = false))
    (Presampling.presample_source secret program)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_probEvent
  intro outputs _ hgood
  exact hzero outputs (not_not.mp hgood)
theorem prepared_failure_zero (secret : BitVec 256) (program : M Bool)
    (outputs : SearchKey → HashOutput)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      (Presampling.preparedCache outputs).AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program) = (pure true : ProbComp Bool)) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (Presampling.preparedCache outputs)] = 0 :=
  SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret program _ hgood
theorem honest_prepared_failure_zero (secret : BitVec 256) (message : Message)
    (outputs : SearchKey → HashOutput) (hgood : Budgets.tableGoodFor message outputs) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run'
        (Presampling.preparedCache outputs)] = 0 := by
  refine prepared_failure_zero secret (honestProgram message) outputs ?_
  intro hash hagree
  have hsrc : Correctness.SearchesSucceedFor (fixedAnswers secret hash) message := by
    apply Budgets.tableGoodFor_searchesSucceedFor message outputs _ hgood
    intro key
    change hash (searchQuery key) = outputs key
    exact hagree (Presampling.preparedCache_apply outputs key)
  exact (fixed_replay secret hash _ (hashOnly_honestProgram message)).trans
    (congrArg (pure : Bool → ProbComp Bool) (honestProgram_true_for _ message hsrc))
theorem honest_failure_small_of_acceptance (secret : BitVec 256) (message : Message)
    (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (ClaudeWCT.W9.T3.Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 298 := by
  exact (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans
    (Budgets.tableGoodFor_failure_small_of_acceptance message p hp hp1 haccept)
theorem honest_failure_small (secret : BitVec 256) (message : Message) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 298 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_small message)
theorem honest_failure_128 (secret : BitVec 256) (message : Message) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 128 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_128 message)
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler
theorem everyMessage_prepared_failure_zero (secret : BitVec 256)
    (nonces : NonceSampling.NonceOutputs) (outputs : NonceSampling.SearchOutputs)
    (hgood : Budgets.tableGoodForNonces nonces outputs) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run'
        (NonceSampling.preparedCache secret nonces outputs)] = 0 := by
  refine SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret everyMessageProgram _ ?_
  intro hash hagree
  have hsearch : Budgets.SearchAgreement outputs (fixedAnswers secret hash) := by
    intro key
    change hash (searchQuery key) = outputs key
    exact hagree (NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : Budgets.NonceAgreement nonces (fixedAnswers secret hash) := by
    intro message
    have h := hagree (NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) h
  have hcomplete := Budgets.tableGoodForNonces_signingComplete nonces outputs
    (fixedAnswers secret hash) hgood hsearch hnonce
  exact (fixed_replay secret hash _ hashOnly_everyMessageProgram).trans
    (congrArg (pure : Bool → ProbComp Bool) (everyMessageProgram_true_of_complete _ hcomplete))
theorem everyMessage_failure_small (secret : BitVec 256) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
        1 / (2 : ENNReal) ^ 193 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value = false))
    (NonceSampling.presample_source secret everyMessageProgram)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent
    (p := fun outputs => ¬Budgets.tableGoodForNonces nonces outputs)
    (fun outputs _ hgood => everyMessage_prepared_failure_zero secret nonces outputs (not_not.mp hgood))).trans
    (Budgets.tableGoodForNonces_failure_small nonces)
theorem source_completeness (secret : BitVec 256) :
    1 - 1 / (2 : ENNReal) ^ 128 ≤
      Pr[= true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] := by
  have hf := everyMessage_failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  have hsmall : 1 / (2 : ENNReal) ^ 193 ≤ 1 / (2 : ENNReal) ^ 128 := by norm_num
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero, tsub_zero]
  exact tsub_le_tsub_left (hf.trans hsmall) 1
end ClaudeWCT.W9.T3.Completeness
end
section
namespace ClaudeWCT.W9.T3.Freshness
open OracleComp OracleSpec
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery SearchQ SearchHdr RowHdr searchQ_ne header_not_search
  hasTag_not_search hasTag_privatePair)
open ClaudeWCT.WCT9 (FtsQuery FtsInput FtsSeed)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem ftsChain_not_search (index coord selected t step : Nat) :
    ¬ SearchHdr (ClaudeWCT.WCT9.ftsChainHeader index coord selected t step) := by
  have := ClaudeWCT.WCT9.ftsChainHeaderP_tweakMarker index coord selected t step 0
  unfold SearchHdr RowHdr ClaudeWCT.WCT9.ftsChainHeader; omega
theorem ftsLeaf_not_search (index coord selected : Nat) :
    ¬ SearchHdr (ClaudeWCT.WCT9.ftsLeafHeader index coord selected) := by
  unfold SearchHdr RowHdr
  rw [ClaudeWCT.WCT9.ftsLeafHeader_tweakMarker, ClaudeWCT.WCT9.ftsLeafHeader_tweakTag]; omega
theorem ftsNode_not_search {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    ¬ SearchHdr (ClaudeWCT.WCT9.wctNodeHeader coord index heap) := by
  unfold SearchHdr RowHdr
  rw [ClaudeWCT.WCT9.wctNodeHeader_tweakMarker, ClaudeWCT.WCT9.wctNodeHeader_tweakTag hk]
  by_cases hn : SigGolfCandidate.T3.FtsNew heap
  · rw [if_pos ⟨hk, hn⟩, if_pos hn]; obtain ⟨_, _⟩ := hn; omega
  · rw [if_neg (fun h => hn h.2), if_neg hn]; omega
theorem avoidsQuery_of_fts (secret : BitVec 256) (target : HashInput)
    (ht : SearchQ target) (index : Nat) (q : Spec.Domain)
    (hq : FtsQuery index q) : avoidsQuery secret target q := by
  rcases q with (coin | input) | (tweak | other)
  · exact hq.elim
  · rcases ClaudeWCT.WCT9.FtsInput.hdrBlock (show FtsInput index input from hq) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨coord, selected, -, -, hblock⟩ | ⟨coord, heap, hk, -, -, hblock⟩ | hblock
    · exact searchQ_ne hblock (ftsChain_not_search index coord selected t step) ht
    · exact searchQ_ne hblock (ftsLeaf_not_search index coord selected) ht
    · exact searchQ_ne hblock (ftsNode_not_search hk index heap) ht
    · exact searchQ_ne hblock (header_not_search 15 0 index 0 0 (by decide)) ht
  · obtain ⟨coord, pair, -, -, rfl⟩ := (show FtsSeed index tweak from hq)
    exact hasTag_not_search (hasTag_privatePair secret 8 coord index 0 pair) (by decide) ht
  · exact hq.elim
theorem avoids_signForest (secret : BitVec 256) (target : HashInput)
    (ht : SearchQ target) (index : Nat) (output : HashOutput) :
    Avoids secret target (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (ClaudeWCT.WCT9.signForest_queries index output)
    (fun q hq => avoidsQuery_of_fts secret target ht index q hq)
theorem sourceFreshness (secret : BitVec 256) : Budgets.SourceFreshness secret where
  forest := by
    intro index output cache hc result hr
    exact ClaudeWCT.W9.T3.PairRows.preserves_pairBelow secret _
      (fun target ht => avoids_signForest secret target ht.searchQ index output)
      4 cache hc result hr
end ClaudeWCT.W9.T3.Freshness
end
section
namespace ClaudeWCT.W9.T3.BudgetClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V)
open ClaudeWCT.W9.T3.Budgets (V_sign_of_freshness_for realized_sign_exponential_budget_of_freshness_for)
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (AllSearchesFreshBC)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem V_sign_le_signingMoment (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ ClaudeWCT.W9.T3.Budgets.signingMoment :=
  V_sign_of_freshness_for secret (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) _
    (fun index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_signForest index output⟩) cache message rcache hc
theorem V_sign_le_two (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_le_signingMoment secret cache message rcache hc).trans ClaudeWCT.W9.T3.Budgets.signingMoment_le_two
theorem realized_sign_exponential_budget (secret : BitVec 256) (cache : Cache)
    (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 :=
  realized_sign_exponential_budget_of_freshness_for secret
    (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) (by norm_num)
    (fun index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_signForest index output⟩) cache message rcache hc
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (sign keys.2 message)
theorem honestSignCount_realize (secret : BitVec 256) (message : Message) :
    realize secret (honestSignCount message) = (do
      let keys ← realize secret keygen
      Cost.World.countBlocks (realize secret (sign keys.2 message))) := by
  rw [honestSignCount, Cost.realize_bind]
  congr 1
  funext keys
  exact Cost.realize_count secret _
theorem honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2 := by
  rw [honestSignCount, SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h := V_sign_le_two secret keys.1.2 message keys.2
    (ClaudeWCT.W9.T3.PairRows.keygen_fresh_from_empty_bc secret keys hkeys)
  simpa only [V, signingZ_pow] using h
theorem realized_honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue ((simulateQ SphincsSecurity.romImpl (do
      let keys ← realize secret keygen
      Cost.World.countBlocks (realize secret (sign keys.2 message)))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  rw [← honestSignCount_realize secret message, StateT.run'_eq, expectedValue_map]
  exact honest_sign_exponential_budget secret message
theorem uniform_message_sign_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestSignCount message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_sign_exponential_budget secret message
end ClaudeWCT.W9.T3.BudgetClosure
end
section
namespace ClaudeWCT.W9.T3.ExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun)
open SigGolfCandidate.T3.Cost (countBlocks)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts eval_joint_cost_le)
open SigGolfCandidate.T3.SourceReplay (hashOnly_pure hashOnly_bind hashOnly_keygen)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
theorem joint_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.1 : ℝ) / 131072)) ≤ 2 := by
  refine le_trans ?_ (ClaudeWCT.W9.T3.BudgetClosure.honest_sign_exponential_budget secret message)
  simp only [honestJointCounts, jointCounts, ClaudeWCT.W9.T3.BudgetClosure.honestSignCount,
    SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig, signCost⟩, rcache⟩
  cases sig with
  | none => simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
  | some sig =>
    simp only [SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
theorem hashOnly_honestJointCounts (message : Message) :
    SigGolfCandidate.T3.SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact hashOnly_pure _
  | some sig =>
    apply hashOnly_bind
      (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_expand message keys.1 sig))
    intro expanded
    exact hashOnly_pure _
theorem joint_cost_le (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message) :
    (evalWithAnswerFn answers (honestJointCounts message)).2 ≤
      8 * (evalWithAnswerFn answers (honestJointCounts message)).1 := by
  exact eval_joint_cost_le (κ := Digest × Cache) (σ := Signature) (ω := Option Witness) answers keygen
    (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
    (ClaudeWCT.W9.T3.ExpansionBudget.expand_cost_le_eight_sign answers message)
theorem support_joint_cost_le (secret : BitVec 256) (message : Message)
    (result : (Nat × Nat) × RCache)
    (hr : result ∈ support (roRun secret (honestJointCounts message) ∅)) :
    result.1.2 ≤ 8 * result.1.1 := by
  obtain ⟨hash, _, heval⟩ := SigGolfCandidate.T3.CountedReplay.support_replay secret _
    (hashOnly_honestJointCounts message) ∅ result hr
  rw [heval]
  exact joint_cost_le _ message
theorem honest_expand_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2 := by
  refine le_trans ?_ (joint_sign_exponential_budget secret message)
  apply expectedValue_mono_of_support
  intro result hr
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (result.1.2 : ℝ) ≤ 8 * (result.1.1 : ℝ) := by
    exact_mod_cast support_joint_cost_le secret message result hr
  linarith
theorem uniform_message_expand_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestJointCounts message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 1048576)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_expand_exponential_budget secret message
end ClaudeWCT.W9.T3.ExpansionClosure
end
section
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (keygen Cache Digest realize)
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open ClaudeWCT.W9.T3M (Images submission)
def verifyCycleBound : Nat := 6997
def claimedC : Nat := 7094
def DigestCapOk (hash : Hash) (m : Message) (w : Bytes 24828) : Prop :=
  ∀ N, evalWithAnswerFn hash (mrealize 0 (digestP m w)) = some N → WCT9.capOk N = true
variable (I : Images)
def KeygenRunCounts : Prop := ∀ sk : SecretKey,
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .keygen sk =
    (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$> countBoth (mrealize sk keygen)
def KeygenRunWith : Prop := ∀ (hash : Hash) (sk : SecretKey),
  (submission I).runWith hash .keygen sk =
    ⟨some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
      cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2), true, 483274415, 983040, 1036288⟩
def SignRefines : Prop := ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .sign (sk, cache, m) =
    (fun p => (p.1.map sigBC, p.2.1, p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))
def SignTerminates : Prop := ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  ((submission I).runWith hash .sign (sk, cache, m)).finished = true ∧
    ((submission I).runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT
def ExpandRefines : Prop := ∀ (m : Message) (pk : PublicKey) (s : Bytes 5310),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .expand (m, pk, s) =
    (fun p => (p.1.map (fun x => witEnc x.1 x.2), p.2.1, p.2.2)) <$>
      countBoth (mrealize 0 (expandN m pk (sigDecC s)))
def ExpandTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5310),
  ((submission I).runWith hash .expand (m, pk, s)).finished = true ∧
    ((submission I).runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT
def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 24828),
  (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 24828),
  ((submission I).runWith hash .verify (m, pk, w)).finished = true ∧
    ((submission I).runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT
def VerifyAcceptCycles : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 24828),
  SigGolfCandidate.T3M.Verify.HashOk hash → DigestCapOk hash m w →
  ((submission I).runWith hash .verify (m, pk, w)).value.isSome = true →
    ((submission I).runWith hash .verify (m, pk, w)).cycles ≤ verifyCycleBound
structure Pending : Prop where
  admissible : (submission I).Admissible
  keygen_run_counts : KeygenRunCounts I
  keygen_runWith : KeygenRunWith I
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I
def SourceCompleteness : Prop := ∀ secret : BitVec 256,
  1 - 1 / (2 : ℝ≥0∞) ^ 128 ≤
    Pr[= true | (simulateQ SphincsSecurity.romImpl
      (realize secret ClaudeWCT.W9.T3.Completeness.everyMessageProgram)).run' ∅]
def SignMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2
def ExpandMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2
structure SourceFacts : Prop where
  source_completeness : SourceCompleteness
  honest_sign_exponential_budget : SignMoment
  honest_expand_exponential_budget : ExpandMoment
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ (cache : Cache) (message : SigGolfCandidate.T3.Message),
    AllQueriesSatisfy (sign cache message) isHash
  hashOnly_expand : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (sig : Signature),
    AllQueriesSatisfy (expand message pk sig) isHash
  hashOnly_verify : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (w : Witness),
    AllQueriesSatisfy (verify message pk w) isHash
  securityP : SecurityP
end ClaudeWCT.W9.T3M.Final
end


namespace ClaudeWCT.W9.T3.Freshness.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery SearchQ searchQ_ne)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The shared forest adds padded heaps4..7; all remaining query domains are unchanged. -/
def FtsQuery (index : Nat) (query : Query) : Prop :=
  ClaudeWCT.WCT9.FtsQuery index query ∨
    ∃ (coord heap : Nat) (left pad right : Digest), coord<9 ∧ 2≤heap ∧ heap<8 ∧
      query=.inl (.inr (pad64 (wctTopInput coord index heap left pad right)))

theorem lift_bound {index : Nat} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound (ClaudeWCT.WCT9.FtsQuery index) Post k oa) : Bound (FtsQuery index) Post k oa :=
  h.mono (fun _ hq => Or.inl hq) (fun _ hp => hp)

theorem avoidsQuery (secret : BitVec 256) (target : HashInput) (ht : SearchQ target)
    (index : Nat) (query : Query) (hq : FtsQuery index query) :
    SigGolfCandidate.T3.Freshness.avoidsQuery secret target query := by
  rcases hq with hlegacy|⟨coord,heap,left,pad,right,hcoord,_,_,rfl⟩
  · exact Freshness.avoidsQuery_of_fts secret target ht index query hlegacy
  · have hblock : SigGolfCandidate.T3M.Extract.hdrBlock
        (pad64 (wctTopInput coord index heap left pad right)) = bytesLE 16 (wctNodeHeader coord index heap) := by
      unfold wctTopInput
      rw [List.append_assoc (bytesLE 16 left ++ _),
        hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
    exact searchQ_ne hblock (Freshness.ftsNode_not_search hcoord index heap) ht

theorem bound_sharedOuterHash (coord index heap : Nat) (left right : Digest)
    (hc : coord<9) (hl : 2≤heap) (hh : heap<4) :
    Bound (FtsQuery index) (fun _ => True) 1 (sharedOuterHash coord index heap left right) := by
  have hq : FtsQuery index (.inl (.inr (pad64 (wctTopInput coord index heap left 0 right)))) :=
    Or.inr ⟨coord,heap,left,0,right,hc,hl,by omega,rfl⟩
  unfold sharedOuterHash
  split
  · exact bound_shortHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])
  · exact bound_highHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])

theorem bound_sharedNode (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot)
    (left right : Digest) (hc : coord<9) (hl : 2≤heap) (hh : heap<128) :
    Bound (FtsQuery index) (fun _ => True) 1 (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact bound_sharedOuterHash coord index heap left right hc hl (by assumption)
  · split
    · have hq : FtsQuery index (.inl (.inr
          (pad64 (wctTopInput coord index heap left (pads (heap/2-2)).2 right)))) :=
        Or.inr ⟨coord,heap,left,(pads (heap/2-2)).2,right,hc,hl,by assumption,rfl⟩
      split
      · exact bound_highHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])
      · exact bound_shortHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])
    · exact lift_bound (ftsBound_nodeHash index coord heap left right hc hl hh)

theorem bound_sharedHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) (hc : coord<9) :
    Bound (FtsQuery index) (fun _ => True) (if first then 124 else 126)
      (sharedHeap first index coord pads leaves) := by
  unfold sharedHeap
  refine (Bound.foldlM_list (P := FtsQuery index)
    (List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse
    (fun (nodes : Array Digest) heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2*heap) 0) (nodes.getD (2*heap+1) 0)
      pure (nodes.set! heap value)) (fun _ _ => True) (fun _ => 1) _
    trivial (fun i hi nodes _ => ?_)).mono_k (by simp)
  have hmem := List.getElem_mem hi
  rw [List.mem_reverse, List.mem_range'] at hmem
  have hb : 2≤((List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse[i]'hi) ∧
      ((List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse[i]'hi)<128 := by
    cases first <;> simp only [Bool.false_eq_true,↓reduceIte] at hmem ⊢ <;> omega
  exact (bound_sharedNode first coord index _ pads _ _ hc hb.1 hb.2).bind' (l:=0)
    (fun value _ => .pure (nodes.set! _ value) 0 trivial) (by omega)

theorem bound_buildSharedCoordinate (first : Bool) (index coord : Nat)
    (hcoord : coord<9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    Bound (FtsQuery index) (fun _ => True) (if first then 3479 else 3481)
      (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  refine (lift_bound (ftsBound_ftsCoefs index coord hcoord)).bind'
    (l:=3328+if first then 124 else 126) (fun coefs _ => ?_) ?_
  · refine (Bound.foldlM_range_le 128 _ (fun _ _ => True) (fun _ => 26) ([],[])
      trivial (fun j hj state _ => ?_) (fun _ _ => trivial) (by simp)).bind'
      (l:=if first then 124 else 126) (fun state _ => ?_) le_rfl
    · refine (lift_bound (ftsBound_buildChildF index coord (rawChild first j) word coefs
        (pads (j/64)).1 hcoord (rawChild_lt first j hj))).bind' (l:=0)
        (fun child _ => .pure _ 0 trivial) (by simp [ClaudeWCT.WCT9.childCost])
    · exact (bound_sharedHeap first index coord pads state.1 hcoord).bind' (l:=0)
        (fun nodes _ => .pure (nodes,state.2) 0 trivial) (by omega)
  · cases first <;> decide

theorem bound_buildPair (index pair : Nat) (hpair : pair<4) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    Bound (FtsQuery index) (fun _ => True) 6960 (buildPair index pair s aWord bWord prev) := by
  unfold buildPair
  refine (bound_buildSharedCoordinate true index (2*pair) (by omega)
    (firstChild s) aWord (fun _ => prev)).bind' (l:=3481) (fun a _ => ?_) (by decide)
  exact (bound_buildSharedCoordinate false index (2*pair+1) (by omega)
    (secondChild s) bWord (nodesPair a.1)).bind' (l:=0)
    (fun b _ => .pure _ 0 trivial) (by decide)

theorem bound_buildSingleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    Bound (FtsQuery index) (fun _ => True) 3481 (buildSingleton index selected word prev) := by
  unfold buildSingleton
  exact (bound_buildSharedCoordinate false index 8 (by decide) selected word (fun _ => prev)).bind'
    (l:=0) (fun built _ => .pure _ 0 trivial) (by decide)

theorem bound_buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Bound (FtsQuery index) (fun _ => True) 31321 (buildForest index selected words) := by
  unfold buildForest
  refine (Bound.foldlM_list (P:=FtsQuery index) (List.finRange 4) _ (fun _ _ => True)
    (fun _ => 6960) ([],ftsStart) trivial (fun i hi state _ => ?_)).bind'
    (l:=3481) (fun state _ => ?_) (by simp)
  · exact (bound_buildPair index _ ((List.finRange 4)[i]'hi).isLt _ _ _ state.2).bind'
      (l:=0) (fun built _ => .pure _ 0 trivial) (by decide)
  · exact (bound_buildSingleton index selected.singleton words.singleton state.2).bind'
      (l:=0) (fun last _ => .pure _ 0 trivial) (by decide)

theorem buildForest_queries (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (buildForest index selected words) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (bound_buildForest index selected words)

theorem avoids_buildForest (secret : BitVec 256) (target : HashInput)
    (ht : SearchQ target) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Avoids secret target (buildForest index selected words) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (buildForest_queries index selected words)
    (fun query hq => avoidsQuery secret target ht index query hq)

#print axioms buildForest_queries
#print axioms avoids_buildForest
end ClaudeWCT.W9.T3.Freshness.Paired

namespace SigGolfCandidate.Research.SharedSigningBudget
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Freshness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.PairRows
open ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Shared forest queries leave every WOTS encoding row fresh. -/
theorem buildForest_preserves_rows (secret : BitVec 256) (index stage : Nat)
    (selected : ForestSelection) (words : ForestWords) (cache : RCache)
    (hfresh : RowsFreshFrom stage cache)
    (result : (ForestOpening × PairRoot) × RCache)
    (hr : result ∈ support (roRun secret (buildForest index selected words) cache)) :
    RowsFreshFrom stage result.2 := by
  intro lay hl tree leaf left right counter hc
  rw [preserves secret _ _ (ClaudeWCT.W9.T3.Freshness.Paired.avoids_buildForest secret _
    (rowQ_pairTrial ..).searchQ index selected words) cache result hr]
  exact hfresh lay hl tree leaf left right counter hc

/-- Fixed forest/root preparation and the certified canonical searches compose. -/
theorem V_signFromOutput_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (signFromOutput cache rho counter output) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^112636 * ((initialBound : ENNReal)/scale) := by
  have h := V_signFromOutput_fixed secret SigGolfCandidate.T3.Budgets.signingZ
    (SigGolfCandidate.T3.Budgets.signingZ^169 * ((initialBound : ENNReal)/scale))
    (SigGolfCandidate.Budget.one_le_zOf _) cache rho counter output rcache ?_
  · simpa only [← mul_assoc, ← pow_add] using h
  · intro forest hforest prepared hprepared
    exact V_searchPreparedLayers_certified secret cache (digestIndex output) prepared.1 forest.1.2 prepared.2
      (prepareRoots_preserves_rows secret (digestIndex output) 0 forest.2
        (buildForest_preserves_rows secret (digestIndex output) 0 _ _ rcache hfresh forest hforest)
        prepared hprepared)
end SigGolfCandidate.Research.SharedSigningBudget


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

theorem sharedDigestSearch_eq_run (rho : Digest) (message : Message) (counter fuel : Nat) :
    sharedDigestSearch rho message counter fuel=DigestGeneric.run digestAccepted rho message counter fuel := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih => simp only [sharedDigestSearch,DigestGeneric.run,ih]

theorem sharedDigestSearch_table_failure (outputsFallback : Answers) (rho : Digest) (message : Message) :
    Pr[fun outputs => evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs outputsFallback)
      (sharedDigestSearch rho message 0 digestAttemptLimit)=none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤1/(2:ENNReal)^400 := by
  simp_rw [sharedDigestSearch_eq_run]
  rw [DigestGeneric.run_table_failure _ _ (by rfl)]
  exact DigestGeneric.failure_power_400 _ ClaudeWCT.Bank.Paired.digestAccepted_acceptance_lower

#print axioms sharedDigestSearch_table_failure
end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Budgets (zeroAnswers)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

def TableGoodForNonces (nonces : Message → Digest) (outputs : SearchKey → HashOutput) : Prop :=
  (∀ message, evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)
    (sharedDigestSearch (nonces message) message 0 digestAttemptLimit)≠none) ∧
  ContextGood (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)

theorem not_tableGoodForNonces (nonces : Message → Digest) (outputs : SearchKey → HashOutput) :
    ¬TableGoodForNonces nonces outputs ↔
    (∃ message, evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)
      (sharedDigestSearch (nonces message) message 0 digestAttemptLimit)=none) ∨
    (∃ context, ContextFailed context (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)) := by
  classical
  simp only [TableGoodForNonces,ContextGood,not_and_or,not_forall,ne_eq,not_not]

theorem tableGoodForNonces_failure (nonces : Message → Digest) :
    Pr[fun outputs => ¬TableGoodForNonces nonces outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤1/(2:ENNReal)^138 := by
  simp_rw [not_tableGoodForNonces]
  exact all_search_failure_small ($ᵗ (SearchKey → HashOutput) : ProbComp _)
    (fun message outputs => evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)
      (sharedDigestSearch (nonces message) message 0 digestAttemptLimit)=none)
    (fun context outputs => ContextFailed context (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers))
    (by simp [Message,Fintype.card_bitVec])
    (fun message => sharedDigestSearch_table_failure zeroAnswers (nonces message) message)
    context_table_failure

#print axioms tableGoodForNonces_failure
end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem sharedDigestSearch_none_agreement (outputs : SearchKey → HashOutput) (answers fallback : Answers)
    (hagree : ClaudeWCT.W9.T3.Budgets.SearchAgreement outputs answers) (rho : Digest) (message : Message) :
    evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit)=none ↔
      evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs fallback)
        (sharedDigestSearch rho message 0 digestAttemptLimit)=none := by
  simp_rw [sharedDigestSearch_eq_run]
  exact (DigestGeneric.run_none_agreement _ _ (by rfl) outputs answers hagree rho message).trans
    (DigestGeneric.run_none_table _ _ (by rfl) outputs fallback rho message).symm

#print axioms sharedDigestSearch_none_agreement
end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Budgets (zeroAnswers)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem tableGoodForNonces_signing (outputs : SearchKey → HashOutput) (answers : Answers)
    (nonces : Message → Digest) (hgood : TableGoodForNonces nonces outputs)
    (hagree : ClaudeWCT.W9.T3.Budgets.SearchAgreement outputs answers)
    (hnonce : ∀ message, evalWithAnswerFn answers (privateNonce message)=nonces message) :
    SigningComplete answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 := by
  have hcontext : ContextGood answers :=
    (contextGood_agreement outputs answers zeroAnswers hagree).mpr hgood.2
  have hc := (SigGolfCandidate.T3.Correctness.keygen_correct answers).2.2
  have hm : (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.tag=
      evalWithAnswerFn answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) := hc
  intro message
  apply sign_complete answers hcontext _ message hm.symm
  intro hd
  rw [hnonce message] at hd
  exact hgood.1 message ((sharedDigestSearch_none_agreement outputs answers zeroAnswers hagree _ _).mp hd)

#print axioms tableGoodForNonces_signing
end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.SourceReplay
open ClaudeWCT.W9.T3.SourceReplay
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[aesop safe apply] theorem hashOnly_sharedOuterHash (coord index heap : Nat) (left right : Digest) :
    HashOnly (sharedOuterHash coord index heap left right) := by
  unfold sharedOuterHash
  split
  · exact hashOnly_shortHash _
  · unfold highHash
    exact hashOnly_bind (hashOnly_publicHash _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_sharedNode (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    HashOnly (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact hashOnly_sharedOuterHash _ _ _ _ _
  · split
    · split
      · unfold highHash
        exact hashOnly_bind (hashOnly_publicHash _) fun _ => hashOnly_pure _
      · exact hashOnly_shortHash _
    · exact hashOnly_wctNodeHash _ _ _ _ _
@[aesop safe apply] theorem hashOnly_recoverSharedInner (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    HashOnly (recoverSharedInner first index coord selected word values path prev) := by
  unfold recoverSharedInner
  refine hashOnly_bind (hashOnly_mapM _ _ (fun _ => ClaudeWCT.W9.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _)) fun _ => ?_
  refine hashOnly_bind (hashOnly_leafHashP _ _ _ _ _) fun _ => ?_
  exact hashOnly_foldlM _ _ (fun _ _ => hashOnly_sharedNode _ _ _ _ _ _ _) _
@[aesop safe apply] theorem hashOnly_recoverPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : HashOnly (recoverPair index pair s aWord bWord opened prev) := by
  unfold recoverPair
  refine hashOnly_bind (hashOnly_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  refine hashOnly_bind (hashOnly_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact hashOnly_bind (hashOnly_sharedOuterHash _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : HashOnly (recoverSingleton index selected word opened prev) := by
  unfold recoverSingleton
  refine hashOnly_bind (hashOnly_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact hashOnly_bind (hashOnly_sharedOuterHash _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : HashOnly (recoverForest index selected words opened) := by
  unfold recoverForest
  exact hashOnly_bind (hashOnly_foldlM _ _ (fun _ _ => hashOnly_recoverPair _ _ _ _ _ _ _) _) fun _ =>
    hashOnly_recoverSingleton _ _ _ _ _
@[aesop safe apply] theorem hashOnly_layerCounterSearchAt (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (counter fuel : Nat) :
    HashOnly (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold CanonicalPolicy.layerCounterSearchAt; exact hashOnly_pure _
  | succ fuel ih =>
    unfold CanonicalPolicy.layerCounterSearchAt
    refine hashOnly_bind (hashOnly_encodingHash _ _) fun result => ?_
    split
    · exact ih _
    · exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_recoverHintedLayers (sig : Signature) (index : Nat) (other : Digest)
    (n : Nat) (msg : LayerMsg) : HashOnly (recoverHintedLayers sig index other n msg) := by
  induction n generalizing msg with
  | zero => unfold recoverHintedLayers; exact hashOnly_pure _
  | succ n ih =>
    unfold recoverHintedLayers
    refine hashOnly_bind (hashOnly_layerCounterSearchAt _ _ _ _ _ _ _) fun result => ?_
    rcases result with _ | ⟨counter,digits⟩
    · exact hashOnly_pure _
    · dsimp only
      split
      · exact hashOnly_bind (hashOnly_topFold _ _ _) fun _ =>
          hashOnly_bind (hashOnly_topNode _ _ _) fun _ => hashOnly_pure _
      · refine hashOnly_bind (hashOnly_recoverLayerPair _ _ _ _) fun pair => ?_
        refine hashOnly_bind (ih _) fun previous => ?_
        cases previous <;> exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_sharedDigestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    HashOnly (sharedDigestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold sharedDigestSearch; exact hashOnly_pure _
  | succ fuel ih =>
    unfold sharedDigestSearch
    refine hashOnly_bind (hashOnly_digest _ _ _) fun output => ?_
    split
    · exact hashOnly_pure _
    · exact ih _
@[aesop safe apply] theorem hashOnly_signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (signPayload cache message) := by
  rw [ClaudeWCT.Bank.Paired.signPayload_factor]
  refine hashOnly_bind (hashOnly_privateNonce _) fun rho => ?_
  refine hashOnly_bind (hashOnly_sharedDigestSearch _ _ _ _) fun found => ?_
  rcases found with _ | ⟨counter,output⟩
  · exact hashOnly_pure _
  · exact ClaudeWCT.Bank.Paired.payHashOnly cache rho output
@[aesop safe apply] theorem hashOnly_sign (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (sign cache message) := by
  unfold sign
  refine hashOnly_bind (hashOnly_privateMac _) fun _ => ?_
  split
  · exact hashOnly_pure _
  · exact hashOnly_signPayload _ _
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (expand message pk sig) := by
  unfold expand
  split
  · exact hashOnly_pure _
  · refine hashOnly_bind (hashOnly_sharedDigestSearch _ _ _ _) fun found => ?_
    rcases found with _ | ⟨counter,output⟩
    · exact hashOnly_pure _
    · refine hashOnly_bind (hashOnly_recoverForest _ _ _ _) fun forest => ?_
      refine hashOnly_bind (hashOnly_recoverHintedLayers _ _ _ _ _) fun layers => ?_
      cases layers
      · exact hashOnly_pure _
      · dsimp only
        split
        · exact hashOnly_pure _
        · split
          · exact hashOnly_pure _
          · refine hashOnly_bind (hashOnly_searchTop _ _ _ _ _ _) fun found => ?_
            cases found <;> exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_verifyLayers (w : Witness) (index n : Nat) (msg : LayerMsg) :
    HashOnly (verifyLayers w index n msg) := by
  induction n generalizing msg with
  | zero => unfold verifyLayers; exact hashOnly_pure _
  | succ n ih =>
    unfold verifyLayers
    dsimp only
    split
    · exact hashOnly_pure _
    · refine hashOnly_bind (hashOnly_encodingHash _ _) fun answer => ?_
      split
      · exact hashOnly_verifyTop _ _ _
      · split
        · refine hashOnly_bind (hashOnly_recoverLayerPairGuard _ _ _ _ _) fun found => ?_
          cases found
          · exact hashOnly_pure _
          · exact ih _
        · exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
    HashOnly (verify message pk w) := by
  unfold verify
  split
  · exact hashOnly_pure _
  · refine hashOnly_bind (hashOnly_digest _ _ _) fun output => ?_
    split
    · exact hashOnly_pure _
    · refine hashOnly_bind (hashOnly_recoverForest _ _ _ _) fun forest => ?_
      refine hashOnly_bind (hashOnly_verifyLayers _ _ _ _) fun root => ?_
      cases root <;> exact hashOnly_pure _
#print axioms hashOnly_expand
#print axioms hashOnly_verify
end SigGolfCandidate.Research.SharedForest

namespace ClaudeWCT.W9.T3.Completeness.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler

noncomputable def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness

noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true

theorem honestProgram_true (answers : Answers) (message : Message)
    (hcomplete : SigningComplete answers (evalWithAnswerFn answers keygen).2) :
    evalWithAnswerFn answers (honestProgram message)=true := by
  obtain ⟨sig,hs⟩ := hcomplete message
  have hc := keygen_correct answers
  obtain ⟨w,he,hv⟩ := sign_expands answers _ hc.2.1 message sig hs
  rw [←hc.1] at he hv
  simp only [honestProgram,evalWithAnswerFn_bind,hs,he,hv]

theorem hashOnly_honestProgram (message : Message) : HashOnly (honestProgram message) := by
  unfold honestProgram
  refine hashOnly_bind hashOnly_keygen fun keys => ?_
  refine hashOnly_bind (SigGolfCandidate.Research.SharedForest.hashOnly_sign keys.2 message) fun sig => ?_
  cases sig
  · exact hashOnly_pure _
  · refine hashOnly_bind (SigGolfCandidate.Research.SharedForest.hashOnly_expand _ _ _) fun witness => ?_
    cases witness
    · exact hashOnly_pure _
    · exact SigGolfCandidate.Research.SharedForest.hashOnly_verify _ _ _

theorem hashOnly_everyMessageProgram : HashOnly everyMessageProgram :=
  hashOnly_foldlM _ _ (fun _ message => hashOnly_bind (hashOnly_honestProgram message) fun _ => hashOnly_pure _) _

theorem everyMessageProgram_true_of_complete (answers : Answers)
    (hcomplete : SigningComplete answers (evalWithAnswerFn answers keygen).2) :
    evalWithAnswerFn answers everyMessageProgram=true := by
  have hall := fun message => honestProgram_true answers message hcomplete
  have hf : ∀ messages : List Message, ∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted)=accepted := by
    intro messages
    induction messages with
    | nil => intro accepted; rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons,evalWithAnswerFn_bind,evalWithAnswerFn_pure,hall,Bool.and_true]
      exact ih accepted
  exact hf _ true

theorem everyMessage_prepared_failure_zero (secret : BitVec 256)
    (nonces : NonceSampling.NonceOutputs) (outputs : NonceSampling.SearchOutputs)
    (hgood : TableGoodForNonces (fun message => (nonces message).extractLsb' 0 128) outputs) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run'
        (NonceSampling.preparedCache secret nonces outputs)]=0 := by
  refine SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret everyMessageProgram _ ?_
  intro hash hagree
  have hsearch : Budgets.SearchAgreement outputs (fixedAnswers secret hash) := by
    intro key
    change hash (searchQuery key)=outputs key
    exact hagree (NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : ∀ message, evalWithAnswerFn (fixedAnswers secret hash) (privateNonce message)=
      (nonces message).extractLsb' 0 128 := by
    intro message
    have h := hagree (NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) h
  have hcomplete := tableGoodForNonces_signing outputs (fixedAnswers secret hash)
    (fun message => (nonces message).extractLsb' 0 128) hgood hsearch hnonce
  exact (fixed_replay secret hash _ hashOnly_everyMessageProgram).trans
    (congrArg (pure : Bool → ProbComp Bool) (everyMessageProgram_true_of_complete _ hcomplete))

theorem everyMessage_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅]≤
        1/(2:ENNReal)^138 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false))
    (NonceSampling.presample_source secret everyMessageProgram)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent
    (p:=fun outputs => ¬TableGoodForNonces (fun message => (nonces message).extractLsb' 0 128) outputs)
    (fun outputs _ hgood => everyMessage_prepared_failure_zero secret nonces outputs (not_not.mp hgood))).trans ?_
  exact tableGoodForNonces_failure _

theorem source_completeness (secret : BitVec 256) :
    1-1/(2:ENNReal)^128≤
      Pr[=true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] := by
  have hf := everyMessage_failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  have hsmall : 1/(2:ENNReal)^138≤1/(2:ENNReal)^128 := by norm_num
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero,tsub_zero]
  exact tsub_le_tsub_left (hf.trans hsmall) 1
#print axioms source_completeness
end ClaudeWCT.W9.T3.Completeness.Paired


namespace SigGolfCandidate.Research.SharedSigningBudget
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.PairRows
open ClaudeWCT.Numerics.CanonicalCompression
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def digestMoment : ENNReal := (ftsBound:ENNReal)/scale
noncomputable def postMoment : ENNReal := signingZ^112636*((initialBound:ENNReal)/scale)
noncomputable def payloadMoment : ENNReal := signingZ^2*(digestMoment*postMoment)
noncomputable def signingMoment : ENNReal := signingZ^2*payloadMoment

theorem digestMoment_ge_one : 1 ≤ digestMoment := by
  apply (ENNReal.toReal_le_toReal (by simp) (by unfold digestMoment scale; finiteness)).mp
  norm_num [digestMoment,ENNReal.toReal_div,ftsBound,scale]

theorem postMoment_ge_one : 1 ≤ postMoment := by
  apply one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
  apply (ENNReal.toReal_le_toReal (by simp) (by unfold scale; finiteness)).mp
  norm_num [ENNReal.toReal_div,initialBound,scale]

theorem payloadMoment_ge_one : 1 ≤ payloadMoment :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    (one_le_mul digestMoment_ge_one postMoment_ge_one)

theorem digest_moment_step : signingZ*
    (SphincsSecurity.Completeness.failMass (DigestGeneric.decoder digestAccepted)*digestMoment+
      (1-SphincsSecurity.Completeness.failMass (DigestGeneric.decoder digestAccepted))) ≤ digestMoment := by
  have hfail : SphincsSecurity.Completeness.failMass (DigestGeneric.decoder digestAccepted)=
      1-(ftsNum:ENNReal)/ftsDen := by
    rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept,
      DigestGeneric.decoder_acceptance,ClaudeWCT.Bank.Paired.digestAccepted_acceptance_exact]
  rw [hfail]
  exact (mul_le_mul' signing_z_ratio le_rfl).trans fts_ratio_step

theorem V_sharedDigestSearch (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel≤2^32) (cache : RCache)
    (hfresh : ∀ c, counter≤c → c<2^32 → cache (digestTrial rho message c)=none) :
    V secret signingZ (sharedDigestSearch rho message counter fuel) cache ≤ digestMoment := by
  rw [sharedDigestSearch_eq_run]
  exact DigestGeneric.V_run digestAccepted secret signingZ digestMoment digestMoment_ge_one rho message
    digest_moment_step fuel counter hlimit cache hfresh

theorem V_signPayload_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache) :
    V secret signingZ (SharedForest.signPayload cache message) rcache ≤ payloadMoment := by
  apply V_signPayload_fixed secret signingZ digestMoment postMoment
    (SigGolfCandidate.Budget.one_le_zOf _) postMoment_ge_one cache message rcache
  · intro nonce hn
    have hnonce := privateNonce_preserves_fresh secret message rcache hfresh nonce hn
    exact V_sharedDigestSearch secret nonce.1 message _ _
      (by have := ClaudeWCT.WCT9.digestAttemptLimit_le; omega) nonce.2
      (fun c _ hc => hnonce.1 _ _ _ hc)
  · intro nonce hn found hd counter output he
    have hnonce := privateNonce_preserves_fresh secret message rcache hfresh nonce hn
    have hrows : RowsFreshFrom 0 nonce.2 := fun lay _ => hnonce.2 lay lay.isLt
    rw [sharedDigestSearch_eq_run] at hd
    exact V_signFromOutput_certified secret cache nonce.1 counter output found.2
      (DigestGeneric.run_preserves_rows digestAccepted secret 0 nonce.1 message 0
        ClaudeWCT.WCT9.digestAttemptLimit nonce.2 hrows found hd)

theorem V_sign_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache) :
    V secret signingZ (SharedForest.sign cache message) rcache ≤ signingMoment := by
  apply V_sign_fixed secret signingZ payloadMoment (SigGolfCandidate.Budget.one_le_zOf _)
    payloadMoment_ge_one cache message rcache
  intro checked hc _
  exact V_signPayload_certified secret cache message checked.2
    (privateMac_preserves_fresh secret cache.region rcache hfresh checked hc)

theorem signingMoment_eq : signingMoment =
    signingZ^112640*(((ftsBound:ENNReal)/scale)*((initialBound:ENNReal)/scale)) := by
  unfold signingMoment payloadMoment digestMoment postMoment
  rw [show 112640=2+2+112636 by decide,pow_add,pow_add]
  ac_rfl

theorem signingMoment_le_two : signingMoment ≤ 2 := by
  rw [signingMoment_eq]
  have hz := ENNReal.toReal_mono (by unfold zDen; finiteness) signing_z_ratio
  rw [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast] at hz
  apply (ENNReal.toReal_le_toReal (by unfold signingZ SigGolfCandidate.Budget.zOf scale; finiteness)
    (by simp)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  have hfixed : signingZ.toReal^112640≤(fixedBound:ℝ)/scale :=
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hz _).trans fixed_ratio_bound
  calc
    _ ≤ ((fixedBound:ℝ)/scale)*(((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale)) := by gcongr
    _ ≤ 2 := envelope_ratio_le_two

theorem V_sign_le_two (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache) :
    V secret signingZ (SharedForest.sign cache message) rcache ≤ 2 :=
  (V_sign_certified secret cache message rcache hfresh).trans signingMoment_le_two

def honestSignCount (message : Message) : M (Option SharedForest.Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (SharedForest.sign keys.2 message)

theorem honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result => (2:ENNReal)^((result.1.2:ℝ)/131072)) ≤ 2 := by
  rw [honestSignCount,SigGolfCandidate.T3.Sampling.roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h := V_sign_le_two secret keys.1.2 message keys.2
    (keygen_fresh_from_empty_bc secret keys hkeys)
  simpa only [V,signingZ_pow] using h
#print axioms honest_sign_exponential_budget
end SigGolfCandidate.Research.SharedSigningBudget

section
namespace SigGolfCandidate.Research.SharedExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun)
open SigGolfCandidate.T3.Cost (countBlocks)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts eval_joint_cost_le)
open SigGolfCandidate.T3.SourceReplay (hashOnly_pure hashOnly_bind hashOnly_keygen)
open SigGolfCandidate.Research.SharedForest (hashOnly_sign hashOnly_expand)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
theorem joint_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.1 : ℝ) / 131072)) ≤ 2 := by
  refine le_trans ?_ (SigGolfCandidate.Research.SharedSigningBudget.honest_sign_exponential_budget secret message)
  simp only [honestJointCounts, jointCounts, SigGolfCandidate.Research.SharedSigningBudget.honestSignCount,
    SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig, signCost⟩, rcache⟩
  cases sig with
  | none => simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
  | some sig =>
    simp only [SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
theorem hashOnly_honestJointCounts (message : Message) :
    SigGolfCandidate.T3.SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact hashOnly_pure _
  | some sig =>
    apply hashOnly_bind
      (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_expand message keys.1 sig))
    intro expanded
    exact hashOnly_pure _
theorem joint_cost_le (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message) :
    (evalWithAnswerFn answers (honestJointCounts message)).2 ≤
      8 * (evalWithAnswerFn answers (honestJointCounts message)).1 := by
  exact eval_joint_cost_le (κ := Digest × SigGolfCandidate.T3.Cache) (σ := Signature) (ω := Option Witness) answers keygen
    (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
    (SigGolfCandidate.Research.SharedForest.expand_cost_le_eight_sign answers message)
theorem support_joint_cost_le (secret : BitVec 256) (message : Message)
    (result : (Nat × Nat) × RCache)
    (hr : result ∈ support (roRun secret (honestJointCounts message) ∅)) :
    result.1.2 ≤ 8 * result.1.1 := by
  obtain ⟨hash, _, heval⟩ := SigGolfCandidate.T3.CountedReplay.support_replay secret _
    (hashOnly_honestJointCounts message) ∅ result hr
  rw [heval]
  exact joint_cost_le _ message
theorem honest_expand_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2 := by
  refine le_trans ?_ (joint_sign_exponential_budget secret message)
  apply expectedValue_mono_of_support
  intro result hr
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (result.1.2 : ℝ) ≤ 8 * (result.1.1 : ℝ) := by
    exact_mod_cast support_joint_cost_le secret message result hr
  linarith
theorem uniform_message_expand_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestJointCounts message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 1048576)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_expand_exponential_budget secret message
#print axioms honest_expand_exponential_budget
end SigGolfCandidate.Research.SharedExpansionClosure
end

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (M Spec Cache Digest keygen)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand)
open ClaudeWCT.W9.T3M.Paired (submission expandN expandB verifyP witEnc)
open ClaudeWCT.W9.T3M.SharedCodec (sigBC sigDecC)

abbrev submission := ClaudeWCT.W9.T3M.Paired.submission
abbrev sigBC := ClaudeWCT.W9.T3M.SharedCodec.sigBC
abbrev sigDecC := ClaudeWCT.W9.T3M.SharedCodec.sigDecC
abbrev expandN := ClaudeWCT.W9.T3M.Paired.expandN
abbrev expandB := ClaudeWCT.W9.T3M.Paired.expandB
abbrev verifyP := ClaudeWCT.W9.T3M.Paired.verifyP
abbrev witEnc := ClaudeWCT.W9.T3M.Paired.witEnc

 def verifyCycleBound : Nat := 6950
 def claimedC : Nat := 7047
 def DigestCapOk (hash : Hash) (m : Message) (w : Bytes 24828) : Prop :=
  SigGolfCandidate.Research.SharedForest.jointAccountingCost
    (hash (SigGolfCandidate.T3M.toQ (SigGolfCandidate.T3.pad64
      (SigGolfCandidate.T3.digestInput (wrho w) m (wdc w)))))≤788
 variable (I : Images)
 def KeygenRunCounts : Prop := ∀ sk : SecretKey,
  (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> (submission I).run .keygen sk=
    (fun p => (some ((p.1.1 : PublicKey),cacheB p.1.2),p.2.1,p.2.2)) <$> countBoth (mrealize sk keygen)
 def KeygenRunWith : Prop := ∀ (hash : Hash) (sk : SecretKey),
  (submission I).runWith hash .keygen sk=
    ⟨some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
      cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2),true,483274415,983040,1036288⟩
 def SignRefines : Prop := ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> (submission I).run .sign (sk,cache,m)=
    (fun p => (p.1.map sigBC,p.2.1,p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))
 def SignTerminates : Prop := ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  ((submission I).runWith hash .sign (sk,cache,m)).finished=true ∧
    ((submission I).runWith hash .sign (sk,cache,m)).cycles<CYCLE_LIMIT
 def ExpandRefines : Prop := ∀ (m : Message) (pk : PublicKey) (s : Bytes 5248),
  (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> (submission I).run .expand (m,pk,s)=
    (fun p => (p.1.map (fun x => witEnc x.1 x.2),p.2.1,p.2.2)) <$>
      countBoth (mrealize 0 (expandN m pk (sigDecC s)))
 def ExpandTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5248),
  ((submission I).runWith hash .expand (m,pk,s)).finished=true ∧
    ((submission I).runWith hash .expand (m,pk,s)).cycles<CYCLE_LIMIT
 def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 24828),
  (fun r => (r.value,r.hashCalls)) <$> (submission I).run .verify (m,pk,w)=
    (fun p => (if p.1 then some () else none,p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
 def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 24828),
  ((submission I).runWith hash .verify (m,pk,w)).finished=true ∧
    ((submission I).runWith hash .verify (m,pk,w)).cycles<CYCLE_LIMIT
 def VerifyAcceptCycles : Prop := ∀ (floors : SigGolfCandidate.T3.Layer→Nat),
  SigGolfCandidate.T3M.Verify.CreditFloors floors →
  ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 24828),
  SigGolfCandidate.T3M.Verify.HashOkBy floors hash → DigestCapOk hash m w →
  ((submission I).runWith hash .verify (m,pk,w)).value.isSome=true →
    ((submission I).runWith hash .verify (m,pk,w)).cycles≤verifyCycleBound
 structure Pending : Prop where
  admissible : (submission I).Admissible
  keygen_run_counts : KeygenRunCounts I
  keygen_runWith : KeygenRunWith I
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I

end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (M Spec Cache Digest keygen)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand verify)
 def SourceCompleteness : Prop := ∀ secret : BitVec 256,
  1-1/(2:ENNReal)^128≤Pr[=true | (simulateQ SphincsSecurity.romImpl
    (SigGolfCandidate.T3.realize secret ClaudeWCT.W9.T3.Completeness.Paired.everyMessageProgram)).run' ∅]
 def SignMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
    (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount message) ∅)
    (fun result => (2:ENNReal)^((result.1.2:ℝ)/131072))≤2
 def ExpandMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
    (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts message) ∅)
    (fun result => (2:ENNReal)^((result.1.2:ℝ)/1048576))≤2
 structure SourceFacts : Prop where
  source_completeness : SourceCompleteness
  honest_sign_exponential_budget : SignMoment
  honest_expand_exponential_budget : ExpandMoment
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ cache message, AllQueriesSatisfy (sign cache message) isHash
  hashOnly_expand : ∀ message pk sig, AllQueriesSatisfy (expand message pk sig) isHash
  hashOnly_verify : ∀ message pk witness, AllQueriesSatisfy (verify message pk witness) isHash
  securityP : SecurityP
end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 (Cache Digest)
open SigGolfCandidate.T3M (isHash isPublic)
open SigGolfCandidate.Research.SharedForest (Signature Witness)

structure SourceQueriesData (p0 : Prop) (p1 : Prop) (p2 : Prop) (p3 : Prop) (p4 : Prop) (p5 : Prop) (p6 : Prop) (p7 : Prop) (p8 : Prop) (p9 : Prop) : Prop where
  good_sign : p0
  good_expand : p1
  good_verify : p2
  good_expandN : p3
  good_verifyP : p4
  public_expandN : p5
  public_expandB : p6
  public_verifyP : p7
  hashOnly_expandB : p8
  hashOnly_verifyP : p9

abbrev SourceQueries : Prop := SourceQueriesData
  (∀(cache : Cache)(message : SigGolfCandidate.T3.Message),
AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.sign cache message) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.expand message pk sig) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : Witness),
AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.verify message pk w) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandN message pk sig) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : WBytes),
AllQueriesSatisfy (verifyP message pk w) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandN message pk sig) isPublic)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandB message pk sig) isPublic)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : WBytes),
AllQueriesSatisfy (verifyP message pk w) isPublic)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandB message pk sig) isHash)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : WBytes),
AllQueriesSatisfy (verifyP message pk w) isHash)
end ClaudeWCT.W9.T3M.Final.Paired
