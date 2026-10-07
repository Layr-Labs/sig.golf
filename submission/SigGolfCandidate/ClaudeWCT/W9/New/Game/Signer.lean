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
theorem lowerQuery_buildLevels (h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 3 lay.val tree h leaves) (LowerQuery lay tree) := by
  unfold buildLevels
  refine allQ_foldlM _ _ (fun levels level => allQ_bind ?_ fun _ => allQ_pure _) _
  unfold buildLevel
  exact allQ_mono (allQ_mapM _ _ fun _ => pubGood_nodeHash _ _ _ _ _ _) (fun _ h => Or.inl h)
theorem lowerQuery_buildLevelsBelow (h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevelsBelow 3 lay.val tree h leaves) (LowerQuery lay tree) := by
  unfold buildLevelsBelow
  refine allQ_foldlM _ _ (fun levels level => allQ_bind ?_ fun _ => allQ_pure _) _
  unfold buildLevel
  exact allQ_mono (allQ_mapM _ _ fun _ => pubGood_nodeHash _ _ _ _ _ _) (fun _ h => Or.inl h)
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
theorem lowerQuery_buildTreeP (selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTreeP lay tree selected digits) (LowerQuery lay tree) := by
  unfold buildTreeP
  refine allQ_bind (allQ_foldlM _ _ (fun state leaf => ?_) _) fun _ =>
    allQ_bind (lowerQuery_buildLevelsBelow lay tree _ _) fun _ => allQ_pure _
  exact allQ_bind (lowerQuery_buildLeafP lay tree _ _ _) fun _ => allQ_pure _
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
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening buildChild buildCoordinate)
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
theorem packedSecret_allowed (index coord q : Nat) (carry : Digest) :
    AllQueriesSatisfy (WCT9.packedSecret (WCT9.ftsSeedPair index coord) q carry) P := by
  unfold WCT9.packedSecret
  split
  · exact SourceQueries.bind_allowed P (by unfold WCT9.ftsSeedPair; exact seed_allowed P hseed _ _ _ _)
      fun _ => SourceQueries.pure_allowed P _
  · exact SourceQueries.pure_allowed P _
include hpublic hseed in
theorem buildChild_allowed (index coord selected : Nat) (word : Rank) (carry : Digest) :
    AllQueriesSatisfy (buildChild index coord selected word carry) P := by
  unfold buildChild
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state i
    apply SourceQueries.bind_allowed P (packedSecret_allowed P hseed _ _ _ _)
    rintro ⟨secret, carry'⟩
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (leafHash_allowed P hpublic _ _ _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) P := by
  unfold nodeHash
  exact shortHash_allowed P hpublic _
include hpublic in
theorem heapBuild_allowed (index coord : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (WCT9.heapBuild index coord leaves) P := by
  unfold WCT9.heapBuild
  apply SourceQueries.foldlM_allowed P
  intro nodes heap
  exact SourceQueries.bind_allowed P (by unfold WCT9.wctNodeHash; exact nodeHash_allowed P hpublic _ _ _ _ _ _)
    fun _ => SourceQueries.pure_allowed P _
include hpublic hseed in
theorem buildCoordinate_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinate index coord selected word) P := by
  unfold buildCoordinate
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state j
    apply SourceQueries.bind_allowed P (buildChild_allowed P hpublic hseed _ _ _ _ _)
    rintro ⟨⟨root, values⟩, carry⟩
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (heapBuild_allowed P hpublic _ _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem forestPk_allowed (index : Nat) (pairs : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index pairs) P := by
  unfold WCT9.forestPk
  exact shortHash_allowed P hpublic _
omit hseed in
theorem layerCounterSearch_allowed'
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (shortHash (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
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
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (shortHash (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
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
      exact SourceQueries.bind_allowed P (buildCoordinate_allowed P hpublic hseed _ _ _ _)
        fun _ => SourceQueries.pure_allowed P _
    · intro state
      apply SourceQueries.bind_allowed P (forestPk_allowed P hpublic _ _)
      intro root
      apply SourceQueries.bind_allowed P (hlayers _ _ _)
      intro layers
      split
      · exact SourceQueries.pure_allowed P _
      · exact SourceQueries.pure_allowed P _
  · exact SourceQueries.pure_allowed P _
end allowed
theorem buildTreeP_allowed' (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hchain : ∀ (lay : Layer) tree leaf i start count value,
      AllQueriesSatisfy (SigGolfCandidate.T3.chain lay tree leaf i start count value) P)
    (hleaf : ∀ (lay : Layer) tree leaf ends, AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) P)
    (hlevel : ∀ (lay : Layer) tree h level nodes, AllQueriesSatisfy (buildLevel 3 lay.val tree h level nodes) P)
    (hseed : ∀ (lay : Layer) tree pair, AllQueriesSatisfy (WCT9.lowerSeedPair lay tree pair) P)
    (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P := by
  unfold WCT9.buildTreeP
  refine SourceQueries.bind_allowed P (SourceQueries.foldlM_allowed P _ _ (fun state leaf => ?_) _) fun _ =>
    SourceQueries.bind_allowed P ?_ fun _ => SourceQueries.pure_allowed P _
  swap
  · unfold WCT9.buildLevelsBelow
    exact SourceQueries.foldlM_allowed P _ _ (fun _ _ =>
      SourceQueries.bind_allowed P (hlevel _ _ _ _ _) fun _ => SourceQueries.pure_allowed P _) _
  refine SourceQueries.bind_allowed P ?_ fun _ => SourceQueries.pure_allowed P _
  unfold WCT9.buildLeafP
  refine SourceQueries.bind_allowed P (SourceQueries.foldlM_allowed P _ _ (fun state i => ?_) _) fun _ =>
    SourceQueries.bind_allowed P (hleaf _ _ _ _) fun _ => SourceQueries.pure_allowed P _
  refine SourceQueries.bind_allowed P ?_ fun sc => ?_
  · unfold WCT9.packedSecret
    split
    · exact SourceQueries.bind_allowed P (hseed _ _ _) fun _ => SourceQueries.pure_allowed P _
    · exact SourceQueries.pure_allowed P _
  · exact SourceQueries.bind_allowed P (hchain _ _ _ _ _ _ _) fun _ =>
      SourceQueries.bind_allowed P (hchain _ _ _ _ _ _ _) fun _ => SourceQueries.pure_allowed P _
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
