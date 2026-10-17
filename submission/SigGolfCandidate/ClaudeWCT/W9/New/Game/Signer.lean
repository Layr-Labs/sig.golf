import SigGolfCandidate.Research.V7Composed198Gate
import SigGolfCandidate.ClaudeWCT.WCT9.Queries
import SigGolfCandidate.T3.FullCache.PayloadSeparation
import SigGolfCandidate.T3.FullCache.SourcePrelude

section


namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (PubGood allQ_pure allQ_bind allQ_foldlM allQ_mapM allQ_mono pubGood_shortHash
  pubGood_nodeHash)
open SphincsSecurity (bytesLE_length)
def LowerSeedQ (lay : Layer) (tree : Nat) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inr (.inl tweak) => ∃ pair, tweak = lowerSeedHeader lay tree pair
  | _ => False
def LowerQuery (lay : Layer) (tree : Nat) (q : SigGolfCandidate.T3.Spec.Domain) : Prop :=
  PubGood q ∨ LowerSeedQ lay tree q
section
variable (lay : Layer) (tree : Nat)
theorem lowerQuery_chain (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.chain lay tree leaf i start count value) (LowerQuery lay tree) :=
  allQ_mono (allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [SigGolfCandidate.T3.chainInput, bytesLE_length, zero16])) _)
    (fun _ h => Or.inl h)
theorem lowerQuery_leafHash (leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) (LowerQuery lay tree) :=
  allQ_mono (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) (fun _ h => Or.inl h)
theorem pubGood_halfHash (high : Bool) (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (halfHash high input) PubGood := by
  rw [halfHash_eq]
  exact allQ_bind (SigGolfCandidate.T3M.pubGood_publicHash input h) fun _ => allQ_pure _
/-- C3: the chains of the current scheme (`chainW`). -/
theorem lowerQuery_chainW (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chainW lay tree leaf i start count value) (LowerQuery lay tree) :=
  allQ_mono (allQ_foldlM _ _ (fun _ _ => pubGood_halfHash _ _
    (by rw [chainInputW_length]; omega)) _) (fun _ h => Or.inl h)
/-- C2: the leaf hash of the current scheme (`lowerLeafHash`). -/
theorem lowerQuery_lowerLeafHash (leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (lowerLeafHash lay tree leaf ends) (LowerQuery lay tree) := by
  rw [lowerLeafHash_eq]
  exact allQ_mono (pubGood_halfHash _ _ (by rw [SigGolfCandidate.T3.leafInput_length]; split_ifs <;> omega))
    (fun _ h => Or.inl h)
/-- C2: a level of a lower tree of the current scheme (`lowerLevel`). -/
theorem lowerQuery_lowerLevel (h level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (lowerLevel lay.val tree h level nodes) (LowerQuery lay tree) := by
  unfold lowerLevel
  refine allQ_mono (allQ_mapM _ _ fun _ => ?_) (fun _ h => Or.inl h)
  unfold lowerNodeHash lowerHash
  exact pubGood_halfHash _ _ (by simp [merkleNodeInput, bytesLE_length, zero16])
theorem lowerQuery_buildLevels (h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 3 lay.val tree h leaves) (LowerQuery lay tree) := by
  unfold buildLevels
  refine allQ_foldlM _ _ (fun levels level => allQ_bind ?_ fun _ => allQ_pure _) _
  unfold buildLevel
  exact allQ_mono (allQ_mapM _ _ fun _ => pubGood_nodeHash _ _ _ _ _ _) (fun _ h => Or.inl h)
theorem lowerQuery_buildLevelsBelow (h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevelsBelow 3 lay.val tree h leaves) (LowerQuery lay tree) := by
  unfold buildLevelsBelow
  exact allQ_foldlM _ _ (fun levels level =>
    allQ_bind (lowerQuery_lowerLevel lay tree _ _ _) fun _ => allQ_pure _) _
theorem lowerQuery_seedPair (pair : Nat) :
    AllQueriesSatisfy (lowerSeedPair lay tree pair) (LowerQuery lay tree) := by
  unfold lowerSeedPair privatePair privateHash
  refine allQ_bind ?_ fun _ => allQ_pure _
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨Or.inr ⟨pair, rfl⟩, fun _ => allQueriesSatisfy_pure _ _⟩
theorem lowerQuery_packedSecret (q : Nat) (carry : Digest) :
    AllQueriesSatisfy (packedSecret (lowerSeedPair lay tree) q carry) (LowerQuery lay tree) := by
  unfold packedSecret
  split
  · exact allQ_bind (lowerQuery_seedPair lay tree _) fun _ => allQ_pure _
  · exact allQ_pure _
theorem lowerQuery_buildLeafP (leaf : Nat) (digits : List Nat) (carry : Digest) :
    AllQueriesSatisfy (buildLeafP lay tree leaf digits carry) (LowerQuery lay tree) := by
  unfold buildLeafP
  refine allQ_bind (allQ_foldlM _ _ (fun state i => ?_) _) fun _ =>
    allQ_bind (lowerQuery_leafHash lay tree leaf _) fun _ => allQ_pure _
  refine allQ_bind (lowerQuery_packedSecret lay tree _ _) fun sc => ?_
  exact allQ_bind (lowerQuery_chain lay tree _ _ _ _ _) fun _ =>
    allQ_bind (lowerQuery_chain lay tree _ _ _ _ _) fun _ => allQ_pure _
theorem lowerQuery_lowerCoefs (leaf : Nat) (carry : Digest) :
    AllQueriesSatisfy (lowerCoefs lay tree leaf carry) (LowerQuery lay tree) := by
  unfold lowerCoefs
  exact allQ_foldlM _ _ (fun state j => allQ_bind (lowerQuery_packedSecret lay tree _ _) fun _ => allQ_pure _) _
theorem lowerQuery_buildLeafPF (leaf : Nat) (digits : List Nat) (carry : Digest) :
    AllQueriesSatisfy (buildLeafPF lay tree leaf digits carry) (LowerQuery lay tree) := by
  unfold buildLeafPF
  refine allQ_bind (lowerQuery_lowerCoefs lay tree leaf carry) fun cc => ?_
  refine allQ_bind (allQ_foldlM _ _ (fun state i => ?_) _) fun _ =>
    allQ_bind (lowerQuery_lowerLeafHash lay tree leaf _) fun _ => allQ_pure _
  exact allQ_bind (lowerQuery_chainW lay tree _ _ _ _ _) fun _ =>
    allQ_bind (lowerQuery_chainW lay tree _ _ _ _ _) fun _ => allQ_pure _
theorem lowerQuery_buildTreeP (selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTreeP lay tree selected digits) (LowerQuery lay tree) := by
  unfold buildTreeP
  refine allQ_bind (allQ_foldlM _ _ (fun state leaf => ?_) _) fun _ =>
    allQ_bind (lowerQuery_buildLevelsBelow lay tree _ _) fun _ => allQ_pure _
  exact allQ_bind (lowerQuery_buildLeafPF lay tree _ _ _) fun _ => allQ_pure _
end
theorem lowerSeedQ_separated {lay : Layer} (hlay : lay ≠ 0) (tree : Nat) {tweak : BitVec 128}
    (h : LowerSeedQ lay tree (.inr (.inl tweak))) :
    (∀ coord index pair, tweak ≠ ftsSeedHeader coord index pair) ∧
      (∀ tree' position idx, tweak ≠ header 0 0 tree' position idx) ∧
      (∀ tag lay' tree' position idx, tag % 256 ≠ 0 → tweak ≠ header tag lay' tree' position idx) := by
  obtain ⟨pair, rfl⟩ := h
  exact ⟨fun coord index pair' he => ftsSeedHeader_ne_lowerSeedHeader coord index pair' lay tree pair he.symm,
    fun tree' position idx => lowerSeedHeader_ne_top lay hlay tree pair tree' position idx,
    fun tag lay' tree' position idx ht => lowerSeedHeader_ne_tag lay tree pair tag lay' tree' position idx ht⟩
end ClaudeWCT.WCT9
end

section




namespace ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec SigGolfCandidate.T3
abbrev Signature : Type := ClaudeWCT.WCT9.Signature
abbrev signPayload : SigGolfCandidate.T3.Cache → Message → M (Option Signature) :=
  ClaudeWCT.WCT9.Rev3.signPayload
abbrev sign : SigGolfCandidate.T3.Cache → Message → M (Option Signature) :=
  ClaudeWCT.WCT9.Rev3.sign
theorem sign_eq (cache : SigGolfCandidate.T3.Cache) (message : Message) : sign cache message = (do
    let tag ← privateMac cache.region
    if tag ≠ cache.tag then return none
    signPayload cache message) := rfl
namespace Signer
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening)
open SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section allowed
variable (P : SigGolfCandidate.T3.Spec.Domain → Prop) (hpublic : ∀ input, P (.inl (.inr input)))
  (hseed : ∀ lay tree position index, P (.inr (.inl (header 8 lay tree position index))))
include hpublic in
theorem shortHash_allowed (input : HashInput) : AllQueriesSatisfy (shortHash input) P := by
  unfold shortHash publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem highHash_allowed (input : HashInput) : AllQueriesSatisfy (WCT9.highHash input) P := by
  unfold WCT9.highHash publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
    fun _ => SourceQueries.pure_allowed P _
include hseed in
theorem seed_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 8 lay tree position index) P := by
  unfold privatePair privateHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hseed _ _ _ _))
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem chain_allowed (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) P := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed P _ _ (fun _ _ => shortHash_allowed P hpublic _) _
include hpublic in
theorem leafHash_allowed (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) P := by
  unfold WCT9.leafHash
  exact shortHash_allowed P hpublic _
include hseed in
theorem ftsCoefs_allowed (index coord : Nat) : AllQueriesSatisfy (WCT9.ftsCoefs index coord) P := by
  unfold WCT9.ftsCoefs
  apply SourceQueries.foldlM_allowed P
  intro acc j
  exact SourceQueries.bind_allowed P (by unfold WCT9.ftsSeedPair; exact seed_allowed P hseed _ _ _ _)
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem buildChildF_allowed (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (WCT9.buildChildF index coord selected word coefs pad) P := by
  unfold WCT9.buildChildF
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state i
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (by unfold WCT9.leafHashP; exact shortHash_allowed P hpublic _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) P := by
  unfold nodeHash
  exact shortHash_allowed P hpublic _
include hpublic in
/-- C1: an FTS hash (either half) makes one public query. -/
theorem ftsHash_allowed (heap : Nat) (input : HashInput) : AllQueriesSatisfy (WCT9.ftsHash heap input) P := by
  rw [WCT9.ftsHash_eq]
  split
  · exact highHash_allowed P hpublic _
  · exact shortHash_allowed P hpublic _
include hpublic in
theorem nodeHashH_allowed (coord index heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (WCT9.wctNodeHashH coord index heap left right) P := by
  unfold WCT9.wctNodeHashH
  exact ftsHash_allowed P hpublic _ _
include hpublic in
/-- C1: the paired child of heap `heap` makes only public queries. -/
theorem buildChildH_allowed (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (WCT9.buildChildH heap index coord selected word coefs pad) P := by
  unfold WCT9.buildChildH
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state i
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (by unfold WCT9.leafHashH; exact ftsHash_allowed P hpublic _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
/-- C1: every paired node (either half) makes one public query. -/
theorem sharedNode_allowed (first : Bool) (coord index heap : Nat)
    (pads : Nat → SigGolfCandidate.Research.SharedForest.PairRoot) (left right : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.sharedNode first coord index heap pads left right) P := by
  unfold SigGolfCandidate.Research.SharedForest.sharedNode SigGolfCandidate.Research.SharedForest.sharedOuterHash
  split
  · split
    · exact shortHash_allowed P hpublic _
    · exact highHash_allowed P hpublic _
  · split
    · split
      · exact highHash_allowed P hpublic _
      · exact shortHash_allowed P hpublic _
    · exact nodeHashH_allowed P hpublic _ _ _ _ _
include hpublic in
theorem heapBuild_allowed (index coord : Nat) (padR : Digest) (leaves : List Digest) :
    AllQueriesSatisfy (WCT9.heapBuild index coord padR leaves) P := by
  unfold WCT9.heapBuild
  apply SourceQueries.foldlM_allowed P
  intro nodes heap
  refine SourceQueries.bind_allowed P ?_ fun _ => SourceQueries.pure_allowed P _
  unfold WCT9.wctHeapNode
  split
  · unfold WCT9.wctTopHash; exact highHash_allowed P hpublic _
  · unfold WCT9.wctNodeHash; exact nodeHash_allowed P hpublic _ _ _ _ _ _
include hpublic hseed in
theorem buildCoordinateF_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    AllQueriesSatisfy (WCT9.buildCoordinateF index coord selected word prev) P := by
  unfold WCT9.buildCoordinateF
  apply SourceQueries.bind_allowed P (ftsCoefs_allowed P hseed _ _)
  intro coefs
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state j
    apply SourceQueries.bind_allowed P (buildChildF_allowed P hpublic _ _ _ _ _ _)
    rintro ⟨root, values⟩
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (heapBuild_allowed P hpublic _ _ _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem forestPk_allowed (index : Nat) (pairs : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index pairs) P := by
  unfold WCT9.forestPk
  exact shortHash_allowed P hpublic _
omit hseed in
theorem layerCounterSearch_allowed'
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
    (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.layerCounterSearch lay tree leaf msg counter fuel) P := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed P _
  | succ fuel ih =>
      unfold WCT9.layerCounterSearch
      apply SourceQueries.bind_allowed P (henc _ _ _ _ _)
      intro answer
      split
      · exact ih _
      · exact SourceQueries.pure_allowed P _
include hpublic in
theorem layerCounterSearch_allowed (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.layerCounterSearch lay tree leaf msg counter fuel) P :=
  layerCounterSearch_allowed' P (fun _ _ _ _ _ => shortHash_allowed P hpublic _) lay tree leaf msg counter fuel
omit hseed in
theorem signLayersBC_allowed' (cache : SigGolfCandidate.T3.Cache)
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
    (hbuild : ∀ lay tree selected digits, AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P)
    (htop : ∀ leaf digits, AllQueriesSatisfy (signTop cache leaf digits) P) (index n : Nat) (msg : WCT9.LayerMsg) :
    AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P := by
  induction n generalizing msg with
  | zero => exact SourceQueries.pure_allowed P _
  | succ n ih =>
      unfold WCT9.signLayersBC
      apply SourceQueries.bind_allowed P (layerCounterSearch_allowed' P henc _ _ _ _ _ _)
      intro found
      split
      · exact SourceQueries.bind_allowed P (htop _ _) fun _ => SourceQueries.pure_allowed P _
      · split
        · apply SourceQueries.bind_allowed P (hbuild _ _ _ _)
          rintro ⟨levels, values⟩
          apply SourceQueries.bind_allowed P (ih _)
          intro previous
          split
          · exact SourceQueries.pure_allowed P _
          · exact SourceQueries.pure_allowed P _
        · exact SourceQueries.pure_allowed P _
include hpublic in
theorem signLayersBC_allowed (cache : SigGolfCandidate.T3.Cache)
    (hbuild : ∀ lay tree selected digits, AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P)
    (htop : ∀ leaf digits, AllQueriesSatisfy (signTop cache leaf digits) P) (index n : Nat) (msg : WCT9.LayerMsg) :
    AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P :=
  signLayersBC_allowed' P cache (fun _ _ _ _ _ => shortHash_allowed P hpublic _) hbuild htop index n msg
include hpublic in
theorem digestSearch_allowed (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.digestSearch rho message counter fuel) P := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed P _
  | succ fuel ih =>
      unfold WCT9.digestSearch digest publicHash
      apply SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
      intro output
      split
      · exact SourceQueries.pure_allowed P _
      · exact ih _
include hpublic hseed in
theorem signPayloadWith_allowed (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hnonce : P (.inr (.inr (.inl message))))
    (hlayers : ∀ index n msg, AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P) :
    AllQueriesSatisfy (WCT9.signPayloadWith limit cache message) P := by
  unfold WCT9.signPayloadWith privateNonce privateHash
  apply SourceQueries.bind_allowed P
  · exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr hnonce)
      fun _ => SourceQueries.pure_allowed P _
  intro rho
  apply SourceQueries.bind_allowed P (digestSearch_allowed P hpublic _ _ _ _)
  intro found
  split
  · apply SourceQueries.bind_allowed P
    · apply SourceQueries.foldlM_allowed P
      intro state coord
      exact SourceQueries.bind_allowed P (buildCoordinateF_allowed P hpublic hseed _ _ _ _ _)
        fun _ => SourceQueries.pure_allowed P _
    · intro state
      apply SourceQueries.bind_allowed P (hlayers _ _ _)
      intro layers
      split
      · exact SourceQueries.pure_allowed P _
      · exact SourceQueries.pure_allowed P _
  · exact SourceQueries.pure_allowed P _
end allowed
/-! C2/C3 (FULL): the lower trees of the current scheme hash with `chainW`, `lowerLeafHash` and `lowerLevel`. Their
queries are those of `T3.chain` and `T3.leafHash` (same inputs, another half of the output); a lower node's query
needs its heap below `2 ^ height lay` (the packed node word's marker), which the honest tree shape guarantees. -/
theorem halfHash_allowed_of_short (P : SigGolfCandidate.T3.Spec.Domain → Prop) (high : Bool) {input : HashInput}
    (h : AllQueriesSatisfy (shortHash input) P) : AllQueriesSatisfy (WCT9.halfHash high input) P := by
  unfold shortHash publicHash at h
  have hq : P (.inl (.inr (pad64 input))) := ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1
  rw [WCT9.halfHash_eq]
  unfold publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr hq) fun _ => SourceQueries.pure_allowed P _
theorem chainW_allowed_of_chain (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hstep : ∀ (lay : Layer) tree leaf i step value,
      AllQueriesSatisfy (shortHash (WCT9.chainInputW lay tree leaf i step value)) P)
    (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chainW lay tree leaf i start count value) P := by
  unfold WCT9.chainW
  exact SourceQueries.foldlM_allowed P _ _ (fun v step => halfHash_allowed_of_short P _ (hstep lay tree leaf i step v)) _
theorem lowerLeafHash_allowed_of_leafHash (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hleaf : ∀ (lay : Layer) tree leaf ends, AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) P)
    (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.lowerLeafHash lay tree leaf ends) P := by
  rw [WCT9.lowerLeafHash_eq]
  exact halfHash_allowed_of_short P _ (hleaf lay tree leaf ends)
/-- A lower node hash only queries a public input. -/
theorem lowerNodeHash_allowed_of_public (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hpublic : ∀ input, P (.inl (.inr input))) (lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (WCT9.lowerNodeHash lay tree heap left right) P := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  exact halfHash_allowed_of_short P _ (shortHash_allowed P hpublic _)
theorem allQ_bind_supp {α β : Type} {P : SigGolfCandidate.T3.Spec.Domain → Prop} {p : M α} {f : α → M β}
    (hp : AllQueriesSatisfy p P) (hf : ∀ a ∈ support p, AllQueriesSatisfy (f a) P) :
    AllQueriesSatisfy (p >>= f) P := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact hf a (by simp)
  | query_bind t mx ih =>
    rw [bind_assoc]
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    refine ⟨hp.1, fun u => ih u (hp.2 u) fun a ha => hf a ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩
theorem mapM_allowed_mem {α β : Type} {P : SigGolfCandidate.T3.Spec.Domain → Prop} (f : α → M β) :
    ∀ (items : List α), (∀ a ∈ items, AllQueriesSatisfy (f a) P) → AllQueriesSatisfy (items.mapM f) P
  | [], _ => by simp
  | a :: items, h => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (h a List.mem_cons_self) fun _ =>
      allQueriesSatisfy_bind (mapM_allowed_mem f items fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ =>
        allQueriesSatisfy_pure _ _
theorem mapM_support_length {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [mapM_support_length f xs zs hzs]
/-- A fold over `List.range' s n` with a step-indexed invariant on the reachable states. -/
theorem foldlM_range'_inv {α : Type} {P : SigGolfCandidate.T3.Spec.Domain → Prop} (I : Nat → α → Prop)
    (f : α → Nat → M α) :
    ∀ (n s : Nat) (init : α), I s init →
      (∀ k a, s ≤ k → k < s + n → I k a →
        AllQueriesSatisfy (f a k) P ∧ ∀ x ∈ support (f a k), I (k + 1) x) →
      AllQueriesSatisfy ((List.range' s n).foldlM f init) P ∧
        ∀ x ∈ support ((List.range' s n).foldlM f init), I (s + n) x
  | 0, s, init, h0, _ => ⟨by simp, by simpa using h0⟩
  | n + 1, s, init, h0, hs => by
    rw [List.range'_succ, List.foldlM_cons]
    obtain ⟨hq, hsup⟩ := hs s init (le_refl _) (by omega) h0
    have ih : ∀ a ∈ support (f init s), AllQueriesSatisfy ((List.range' (s + 1) n).foldlM f a) P ∧
        ∀ x ∈ support ((List.range' (s + 1) n).foldlM f a), I (s + 1 + n) x := fun a ha =>
      foldlM_range'_inv I f n (s + 1) a (hsup a ha) (fun k b h1 h2 h3 => hs k b (by omega) (by omega) h3)
    refine ⟨allQ_bind_supp hq fun a ha => (ih a ha).1, fun x hx => ?_⟩
    rw [mem_support_bind_iff] at hx
    obtain ⟨a, ha, hx⟩ := hx
    have := (ih a ha).2 x hx
    rwa [show s + 1 + n = s + (n + 1) by omega] at this
/-- A fold whose every step appends one element to the first component. -/
theorem foldlM_support_fst_length {α β γ : Type} (items : List β) (f : List γ × α → β → M (List γ × α))
    (hf : ∀ s b, ∀ x ∈ support (f s b), x.1.length = s.1.length + 1) :
    ∀ init, ∀ x ∈ support (items.foldlM f init), x.1.length = init.1.length + items.length := by
  induction items with
  | nil => intro init x hx; simp only [List.foldlM_nil, support_pure, Set.mem_singleton_iff] at hx; subst hx; simp
  | cons b items ih =>
    intro init x hx
    rw [List.foldlM_cons, mem_support_bind_iff] at hx
    obtain ⟨a, ha, hx⟩ := hx
    rw [ih a x hx, hf init b a ha, List.length_cons]
    omega
theorem height_le_seven {lay : Layer} (h0 : lay.val ≠ 0) : height lay ≤ 7 := by
  fin_cases lay <;> simp_all [height]
theorem lowerLevel_allowed (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hnode : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
      AllQueriesSatisfy (WCT9.lowerNodeHash lay.val tree heap left right) P)
    (lay : Layer) (tree level : Nat) (nodes : List Digest) (h1 : 1 ≤ level) (h2 : level < height lay)
    (hn : nodes.length = 2 ^ (height lay - (level - 1))) :
    AllQueriesSatisfy (WCT9.lowerLevel lay.val tree (height lay) level nodes) P := by
  unfold WCT9.lowerLevel
  refine mapM_allowed_mem _ _ fun i hi => hnode lay tree _ _ _ ?_
  rw [List.mem_range, hn, show height lay - (level - 1) = (height lay - level) + 1 by omega, pow_succ,
    Nat.mul_div_cancel _ (by decide)] at hi
  have hle : 2 ^ (height lay - level) * 2 ≤ 2 ^ height lay := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega
theorem buildLevelsBelow_allowed (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hnode : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
      AllQueriesSatisfy (WCT9.lowerNodeHash lay.val tree heap left right) P)
    (lay : Layer) (tree : Nat) (leaves : List Digest) (hlen : leaves.length = 2 ^ height lay) :
    AllQueriesSatisfy (WCT9.buildLevelsBelow 3 lay.val tree (height lay) leaves) P := by
  unfold WCT9.buildLevelsBelow
  refine (foldlM_range'_inv (P := P)
    (fun k (levels : List (List Digest)) =>
      levels.length = k ∧ (levels.getD (k - 1) []).length = 2 ^ (height lay - (k - 1))) _
    (height lay - 1) 1 [leaves] ⟨rfl, by simpa using hlen⟩ ?_).1
  rintro k levels hk1 hk2 ⟨hl, hg⟩
  have hk : k < height lay := by omega
  refine ⟨SourceQueries.bind_allowed P (lowerLevel_allowed P hnode lay tree k _ hk1 hk hg) fun _ =>
    SourceQueries.pure_allowed P _, fun x hx => ?_⟩
  rw [mem_support_bind_iff] at hx
  obtain ⟨nodes, hnodes, hx⟩ := hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  have hnl := mapM_support_length _ _ _ hnodes
  rw [List.length_range, hg, show height lay - (k - 1) = (height lay - k) + 1 by omega, pow_succ,
    Nat.mul_div_cancel _ (by decide)] at hnl
  refine ⟨by simp [hl], ?_⟩
  rw [show k + 1 - 1 = k by omega, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hl, hnl]
theorem buildTreeP_allowed' (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hchain : ∀ (lay : Layer) tree leaf i step value,
      AllQueriesSatisfy (shortHash (WCT9.chainInputW lay tree leaf i step value)) P)
    (hleaf : ∀ (lay : Layer) tree leaf ends, AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) P)
    (hnode : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
      AllQueriesSatisfy (WCT9.lowerNodeHash lay.val tree heap left right) P)
    (hseed : ∀ (lay : Layer) tree pair, AllQueriesSatisfy (WCT9.lowerSeedPair lay tree pair) P)
    (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P := by
  have hpf : ∀ leaf digits carry, AllQueriesSatisfy (WCT9.buildLeafPF lay tree leaf digits carry) P := by
    intro leaf digits carry
    unfold WCT9.buildLeafPF
    refine SourceQueries.bind_allowed P ?_ fun cc => ?_
    · unfold WCT9.lowerCoefs
      refine SourceQueries.foldlM_allowed P _ _ (fun state j => ?_) _
      refine SourceQueries.bind_allowed P ?_ fun _ => SourceQueries.pure_allowed P _
      unfold WCT9.packedSecret
      split
      · exact SourceQueries.bind_allowed P (hseed _ _ _) fun _ => SourceQueries.pure_allowed P _
      · exact SourceQueries.pure_allowed P _
    refine SourceQueries.bind_allowed P (SourceQueries.foldlM_allowed P _ _ (fun state i => ?_) _) fun _ =>
      SourceQueries.bind_allowed P (lowerLeafHash_allowed_of_leafHash P hleaf _ _ _ _) fun _ =>
        SourceQueries.pure_allowed P _
    exact SourceQueries.bind_allowed P (chainW_allowed_of_chain P hchain _ _ _ _ _ _ _) fun _ =>
      SourceQueries.bind_allowed P (chainW_allowed_of_chain P hchain _ _ _ _ _ _ _) fun _ =>
        SourceQueries.pure_allowed P _
  unfold WCT9.buildTreeP
  refine allQ_bind_supp (SourceQueries.foldlM_allowed P _ _ (fun state leaf =>
    SourceQueries.bind_allowed P (hpf _ _ _) fun _ => SourceQueries.pure_allowed P _) _) fun state hstate => ?_
  have hlen : state.1.length = 2 ^ height lay := by
    have := foldlM_support_fst_length _ _ (fun s b x hx => by
      rw [mem_support_bind_iff] at hx
      obtain ⟨⟨⟨root, values⟩, carry⟩, -, hx⟩ := hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp) _ state hstate
    simpa using this
  exact SourceQueries.bind_allowed P (buildLevelsBelow_allowed P hnode lay tree _ hlen) fun _ =>
    SourceQueries.pure_allowed P _
theorem buildTreeP_allowed (P : SigGolfCandidate.T3.Spec.Domain → Prop) (hpublic : ∀ input, P (.inl (.inr input)))
    (hlower : ∀ (lay : Layer) tree pair, P (.inr (.inl (WCT9.lowerSeedHeader lay tree pair))))
    (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P := by
  refine SigGolfCandidate.T3M.allQ_mono (WCT9.lowerQuery_buildTreeP lay tree selected digits) fun q hq => ?_
  rcases hq with ⟨hp, -⟩ | hs
  · rcases q with (n | input) | c
    · exact hp.elim
    · exact hpublic input
    · exact hp.elim
  · rcases q with (n | input) | (tweak | rest)
    · exact hs.elim
    · exact hs.elim
    · obtain ⟨pair, rfl⟩ := hs
      exact hlower lay tree pair
    · exact hs.elim
theorem signPayloadWith_nonMac (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (WCT9.signPayloadWith limit cache message) SiggolfT3Mac4.Source.NonMac :=
  signPayloadWith_allowed _ (fun _ => trivial)
    (fun lay tree position index => ⟨SiggolfT3Mac4.Source.non_mac_tweak 8 lay tree position index (by decide) 0,
      SiggolfT3Mac4.Source.non_mac_tweak 8 lay tree position index (by decide) 1⟩)
    limit cache message (SiggolfT3Mac4.Source.nonce_coordinate_other message)
    (fun index n msg => signLayersBC_allowed _ (fun _ => trivial) cache
      (buildTreeP_allowed _ (fun _ => trivial) (fun lay tree pair =>
        ⟨SiggolfT3Mac4.Source.non_mac_tweak 0 lay.val tree pair 0 (by decide) 0,
          SiggolfT3Mac4.Source.non_mac_tweak 0 lay.val tree pair 0 (by decide) 1⟩))
      (SiggolfT3Mac4.Source.Payload.signTop_allowed cache) index n msg)
theorem signPayload_nonMac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) SiggolfT3Mac4.Source.NonMac :=
  signPayloadWith_nonMac _ cache message
theorem signPayloadWith_hashOnly (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SourceReplay.HashOnly (WCT9.signPayloadWith limit cache message) :=
  signPayloadWith_allowed _ (fun _ => trivial) (fun _ _ _ _ => trivial) limit cache message trivial
    (fun index n msg => signLayersBC_allowed _ (fun _ => trivial) cache
      (buildTreeP_allowed _ (fun _ => trivial) (fun _ _ _ => trivial))
      (SourceQueries.signTop_allowed SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) cache)
      index n msg)
theorem signPayload_hashOnly (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SourceReplay.HashOnly (signPayload cache message) :=
  signPayloadWith_hashOnly _ cache message
theorem signPayloadWith_avoids (protectedMessage : Message) (limit : Nat) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (hne : message ≠ protectedMessage) :
    NonceFreshness.Avoids protectedMessage (WCT9.signPayloadWith limit cache message) :=
  signPayloadWith_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
    (fun _ _ _ _ => by simp [NonceFreshness.nonceQuery]) limit cache message
    (by simpa [NonceFreshness.nonceQuery] using hne)
    (fun index n msg => signLayersBC_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery]) cache
      (buildTreeP_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
        (fun _ _ _ => by simp [NonceFreshness.nonceQuery]))
      (NonceFreshness.avoids_signTop protectedMessage cache)
      index n msg)
theorem signPayload_avoids (protectedMessage : Message) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hne : message ≠ protectedMessage) : NonceFreshness.Avoids protectedMessage (signPayload cache message) :=
  signPayloadWith_avoids protectedMessage _ cache message hne
theorem sign_hashOnly (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SourceReplay.HashOnly (sign cache message) := by
  rw [sign_eq]
  apply SourceQueries.bind_allowed SourceReplay.IsHash
    (SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) _)
  intro tag
  split_ifs
  · exact SourceQueries.pure_allowed _ _
  · exact signPayload_hashOnly cache message
theorem sign_avoids (protectedMessage : Message) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hne : message ≠ protectedMessage) : NonceFreshness.Avoids protectedMessage (sign cache message) := by
  rw [sign_eq]
  apply NonceFreshness.avoids_bind protectedMessage (NonceFreshness.avoids_privateMac protectedMessage _)
  intro tag
  split_ifs
  · exact NonceFreshness.avoids_pure _ _
  · exact signPayload_avoids protectedMessage cache message hne
end Signer
end ClaudeWCT.W9.T3.Security
end

namespace ClaudeWCT.W9.T3.Security.SharedQueries
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Stage 2 (C2/C3, #866): the lower trees hash with `chainW`, `lowerLeafHash` (same inputs as `T3.chain` /
`T3.leafHash`, another half of the output; `Signer.halfHash_allowed_of_short`) and `lowerNodeHash`, whose query
needs the honest heap bound `heap < 2 ^ height lay` (the packed node word's marker). -/
structure TailAllowed (Q : SigGolfCandidate.T3.Spec.Domain → Prop) : Prop where
  chainStep : ∀ lay tree leaf i step value,
    AllQueriesSatisfy (shortHash (SigGolfCandidate.T3.chainInput lay tree leaf i step value)) Q
  /-- Pairing stage 1: the chain steps of the current scheme (G chains included). -/
  chainStepW : ∀ lay tree leaf i step value,
    AllQueriesSatisfy (shortHash (WCT9.chainInputW lay tree leaf i step value)) Q
  leaf : ∀ lay tree leaf ends, AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) Q
  node : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
    AllQueriesSatisfy (lowerNodeHash lay.val tree heap left right) Q
  seed : ∀ lay tree pair, AllQueriesSatisfy (lowerSeedPair lay tree pair) Q
  encoding : ∀ lay tree leaf msg counter,
    AllQueriesSatisfy (encodingHash lay (layerEncodingInput lay tree leaf msg counter)) Q
  top : ∀ cache leaf digits, AllQueriesSatisfy (signTop cache leaf digits) Q

section
variable (Q : SigGolfCandidate.T3.Spec.Domain → Prop) (hQ : TailAllowed Q)
include hQ

theorem chain_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.chain lay tree leaf i start count value) Q := by
  unfold SigGolfCandidate.T3.chain
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ => hQ.chainStep ..) _

theorem chainW_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chainW lay tree leaf i start count value) Q := by
  unfold chainW
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ =>
    Signer.halfHash_allowed_of_short Q _ (hQ.chainStepW ..)) _

theorem lowerLeafHash_allowed (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (lowerLeafHash lay tree leaf ends) Q :=
  Signer.lowerLeafHash_allowed_of_leafHash Q hQ.leaf lay tree leaf ends

theorem lowerCoefs_allowed (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    AllQueriesSatisfy (lowerCoefs lay tree leaf carry) Q := by
  unfold lowerCoefs
  apply SourceQueries.foldlM_allowed Q
  intro state j
  refine SourceQueries.bind_allowed Q ?_ fun _ => SourceQueries.pure_allowed Q _
  unfold packedSecret
  split
  · exact SourceQueries.bind_allowed Q (hQ.seed ..) fun _ => SourceQueries.pure_allowed Q _
  · exact SourceQueries.pure_allowed Q _

theorem buildLeafPF_allowed (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    AllQueriesSatisfy (buildLeafPF lay tree leaf digits carry) Q := by
  unfold buildLeafPF
  refine SourceQueries.bind_allowed Q (lowerCoefs_allowed Q hQ ..) fun _ => ?_
  refine SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _ (fun state i => ?_) _) fun _ =>
    SourceQueries.bind_allowed Q (lowerLeafHash_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _
  exact SourceQueries.bind_allowed Q (chainW_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (chainW_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem chainPrefixes_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chainPrefixes lay tree leaf i start count value) Q := by
  induction count generalizing start value with
  | zero => exact SourceQueries.pure_allowed Q _
  | succ count ih =>
    unfold chainPrefixes
    exact SourceQueries.bind_allowed Q (Signer.halfHash_allowed_of_short Q _ (hQ.chainStepW ..)) fun _ =>
      SourceQueries.bind_allowed Q (ih ..) fun _ => SourceQueries.pure_allowed Q _

theorem buildLeafPrefixes_allowed (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    AllQueriesSatisfy (buildLeafPrefixes lay tree leaf carry) Q := by
  unfold buildLeafPrefixes
  exact SourceQueries.bind_allowed Q (lowerCoefs_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (SourceQueries.mapM_allowed Q _ _
      (fun _ => chainPrefixes_allowed Q hQ ..)) fun _ =>
      SourceQueries.bind_allowed Q (lowerLeafHash_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem buildTreePrefixes_allowed (lay : Layer) (tree selected : Nat) :
    AllQueriesSatisfy (buildTreePrefixes lay tree selected) Q := by
  unfold buildTreePrefixes
  refine Signer.allQ_bind_supp (SourceQueries.foldlM_allowed Q _ _ (fun state leaf => ?_) _)
    fun state hstate => ?_
  · dsimp only
    split
    · refine SourceQueries.bind_allowed Q (buildLeafPrefixes_allowed Q hQ ..) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      exact SourceQueries.pure_allowed Q _
    · refine SourceQueries.bind_allowed Q (buildLeafPF_allowed Q hQ ..) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      simp only [pure_bind]
      exact SourceQueries.pure_allowed Q _
  · -- C2: the lower levels need the honest leaf count (heap bound of `lowerNodeHash`), as in
    -- `Signer.buildTreeP_allowed'`.
    have hlen : state.1.length = 2 ^ height lay := by
      have := Signer.foldlM_support_fst_length _ _ (fun s b x hx => by
        dsimp only at hx
        split at hx
        all_goals
          try simp only [pure_bind] at hx
          rw [mem_support_bind_iff] at hx
          obtain ⟨⟨⟨root, values⟩, carry⟩, -, hx⟩ := hx
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx
          simp) _ state hstate
      simpa using this
    exact SourceQueries.bind_allowed Q (Signer.buildLevelsBelow_allowed Q hQ.node lay tree _ hlen) fun _ =>
      SourceQueries.pure_allowed Q _

theorem prepareRoots_allowed (index : Nat) : AllQueriesSatisfy (prepareRoots index) Q := by
  unfold prepareRoots
  exact SourceQueries.bind_allowed Q (buildTreePrefixes_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (buildTreePrefixes_allowed Q hQ ..) fun _ =>
      SourceQueries.bind_allowed Q (buildTreePrefixes_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem layerCounterSearchAt_allowed (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) Q := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed Q _
  | succ fuel ih =>
    unfold CanonicalPolicy.layerCounterSearchAt
    apply SourceQueries.bind_allowed Q (hQ.encoding ..)
    intro answer
    split
    · exact ih _
    · exact SourceQueries.pure_allowed Q _

theorem searchPreparedLayers_allowed (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) :
    AllQueriesSatisfy (searchPreparedLayers cache index prepared forest) Q := by
  unfold searchPreparedLayers
  apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
  intro found
  rcases found with _ | ⟨counter0,digits0⟩
  · exact SourceQueries.pure_allowed Q _
  · dsimp only
    split
    · exact SourceQueries.pure_allowed Q _
    · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
      intro found
      rcases found with _ | ⟨counter1,digits1⟩
      · exact SourceQueries.pure_allowed Q _
      · dsimp only
        split
        · exact SourceQueries.pure_allowed Q _
        · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
          intro found
          rcases found with _ | ⟨counter2,digits2⟩
          · exact SourceQueries.pure_allowed Q _
          · dsimp only
            split
            · exact SourceQueries.pure_allowed Q _
            · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
              intro found
              rcases found with _ | ⟨counter3,digits3⟩
              · exact SourceQueries.pure_allowed Q _
              · exact SourceQueries.bind_allowed Q (hQ.top ..) fun _ => SourceQueries.pure_allowed Q _

theorem signFromOutput_allowed
    (hforest : ∀ index selected words, AllQueriesSatisfy (buildForest index selected words) Q)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    AllQueriesSatisfy (signFromOutput cache rho counter output) Q := by
  unfold signFromOutput
  apply SourceQueries.bind_allowed Q (hforest ..)
  intro forest
  apply SourceQueries.bind_allowed Q (prepareRoots_allowed Q hQ ..)
  intro prepared
  apply SourceQueries.bind_allowed Q (searchPreparedLayers_allowed Q hQ ..)
  intro layers
  cases layers <;> exact SourceQueries.pure_allowed Q _
end

#print axioms prepareRoots_allowed
#print axioms searchPreparedLayers_allowed
#print axioms signFromOutput_allowed
end ClaudeWCT.W9.T3.Security.SharedQueries
