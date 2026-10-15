import SigGolfCandidate.T3.Secc.SeccSufSigned

namespace SigGolfCandidate.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind queried_shortHash)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_seccSufRoute : DecidableEq T3.Cache := Classical.decEq _
attribute [local irreducible] buildFts buildTree
theorem digestInput_length (rho : Digest) (m : Message) (c : BitVec 32) : (digestInput rho m c).length = 64 := by
  simp [digestInput, SphincsSecurity.bytesLE_length]
theorem pad64_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) = digestInput rho m c := by
  simp [pad64, digestInput_length]
theorem digestInput_injective {rho rho' : Digest} {m m' : Message} {c c' : BitVec 32}
    (h : pad64 (digestInput rho m c) = pad64 (digestInput rho' m' c')) : rho = rho' ∧ c = c' ∧ m = m' := by
  rw [pad64_digestInput, pad64_digestInput] at h
  obtain ⟨hr, hm, hc⟩ := SigGolfCandidate.T3.digestInput_injective h
  exact ⟨hr, hc, hm⟩
theorem queried_digest (answers : Correctness.Answers) (rho : Digest) (m : Message) (c : BitVec 32) :
    queried answers (digest rho m c) = [.inl (.inr (pad64 (digestInput rho m c)))] := rfl
def hdrTag (input : HashInput) : Nat :=
  if 128 ≤ ((Extract.hdrBlock input).getD 0 0).toNat then 1
  else ((Extract.hdrBlock input).getD 1 0).toNat
theorem hdrBlock_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    Extract.hdrBlock (pad64 (digestInput rho m c)) = SphincsSecurity.bytesLE 16 (digestHeader c) := by
  rw [pad64_digestInput]
  exact Extract.hdrBlock_prefix _ _ _
def hdrMarker (input : HashInput) : Nat := ((Extract.hdrBlock input).getD 0 0).toNat
theorem hdrMarker_eq {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock input = SphincsSecurity.bytesLE 16 hdr) : hdrMarker input = tweakMarker hdr := by
  unfold hdrMarker
  rw [h, bytesLE16_first_toNat]
  rfl
theorem hdrMarker_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    hdrMarker (pad64 (digestInput rho m c)) = 0 := by
  rw [hdrMarker_eq (hdrBlock_digestInput rho m c), digestHeader_marker]
def NotDigestQ : T3.Spec.Domain → Prop
  | .inl (.inr input) => hdrMarker input ≠ 0
  | _ => True
theorem shortHash_ok_marker {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 hdr) (hm : tweakMarker hdr ≠ 0) :
    AllQueriesSatisfy (shortHash input) NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (show hdrMarker (pad64 input) ≠ 0 by rw [hdrMarker_eq h]; exact hm)
  · intro _; exact SourceQueries.pure_allowed _ _
theorem shortHash_ok {input : HashInput} {tag lay tree position index : Nat}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 (header tag lay tree position index))
    (_ht : tag % 256 ≠ 0) : AllQueriesSatisfy (shortHash input) NotDigestQ :=
  shortHash_ok_marker h (by rw [header_marker]; decide)
theorem privatePair_ok (tag lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair tag lay tree position index) NotDigestQ :=
  SourceQueries.privatePair_allowed NotDigestQ (fun _ => trivial) tag lay tree position index
theorem mask_ok (level index : Nat) : AllQueriesSatisfy (mask level index) NotDigestQ :=
  SourceQueries.mask_allowed NotDigestQ (fun _ => trivial) level index
theorem chain_ok (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NotDigestQ := by
  unfold chain
  apply SourceQueries.foldlM_allowed NotDigestQ
  intro v step
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change hdrMarker (pad64 (chainInput lay tree leaf i step v)) ≠ 0
    rw [chainInput_padded]
    unfold hdrMarker Extract.hdrBlock
    rw [chainInput_header, bytesLE16_first_toNat]
    have := chainHeader_firstByte lay tree leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem leafHash_ok (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDigestQ :=
  shortHash_ok_marker (Extract.hdrBlock_leafInput _ _ _ _) (by rw [leafTweak_marker]; decide)
theorem nodeHash_ok (tag lay tree heap : Nat) (left right : Digest) (_ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDigestQ := by
  rw [nodeHash_eq_shortHash]
  exact shortHash_ok_marker (by rw [pad64_nodeInputP]; exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _)
    (nodeTweak_marker_ne_zero _ _ _ _)
theorem nodeHash3_ok (lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash 3 lay tree heap left right) NotDigestQ :=
  nodeHash_ok 3 lay tree heap left right (by decide)
theorem ftsLeaf_ok (index coord leaf : Nat) (secret : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf secret) NotDigestQ := by
  rw [ftsLeaf_eq_shortHash]
  exact shortHash_ok (tag := 9) (by rw [pad64_ftsLeafInputP]; exact BSuf.hdrBlock_ftsLeafInputP _ _ _ _ _ _)
    (by decide)
theorem forestPk_ok (index : Nat) (roots : List Digest) : AllQueriesSatisfy (forestPk index roots) NotDigestQ := by
  rw [Extract.forestPk_eq_shortHash]
  exact shortHash_ok (tag := 11) (Extract.hdrBlock_listInput _ _ _) (by decide)
theorem encoding_ok (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : BitVec 32) :
    AllQueriesSatisfy (shortHash (encodingInput lay tree leaf message counter)) NotDigestQ :=
  shortHash_ok_marker (by
    rw [Extract.hdrBlock_pad64 _ (by simp [encodingInput, SphincsSecurity.bytesLE_length])]
    exact Extract.hdrBlock_prefix _ _ _) (by rw [rowTweak_marker]; decide)
theorem counterSearch_ok (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter, AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) NotDigestQ := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter
      unfold counterSearch
      apply SourceQueries.bind_allowed _ (encoding_ok _ _ _ _ _)
      intro answer
      split
      · exact ih _
      · exact SourceQueries.pure_allowed _ _
theorem buildLevel_ok (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NotDigestQ := by
  unfold buildLevel
  exact SourceQueries.mapM_allowed NotDigestQ _ _ fun _ => nodeHash_ok _ _ _ _ _ _ ht
theorem buildLevels_ok (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NotDigestQ := by
  unfold buildLevels
  exact SourceQueries.foldlM_allowed NotDigestQ _ _ (fun _ _ =>
    SourceQueries.bind_allowed _ (buildLevel_ok _ _ _ _ _ _ ht) fun _ => SourceQueries.pure_allowed _ _) _
theorem buildLevels3_ok (lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 3 lay tree h leaves) NotDigestQ := buildLevels_ok 3 lay tree h leaves (by decide)
theorem buildLevels10_ok (lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 10 lay tree h leaves) NotDigestQ := buildLevels_ok 10 lay tree h leaves (by decide)
section aesopShape
attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed SourceQueries.map_allowed
  SourceQueries.foldlM_allowed SourceQueries.mapM_allowed privatePair_ok mask_ok chain_ok leafHash_ok nodeHash3_ok
  ftsLeaf_ok forestPk_ok counterSearch_ok buildLevels3_ok buildLevels10_ok
theorem buildLeaf_ok (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NotDigestQ := by
  unfold buildLeaf; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildLeaf_ok
theorem buildTree_ok (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NotDigestQ := by
  unfold buildTree; aesop (config := { maxRuleApplications := 1000 })
theorem buildFts_ok (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) NotDigestQ := by
  unfold buildFts; aesop (config := { maxRuleApplications := 1000 })
theorem topPath_ok (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDigestQ := by
  unfold topPath; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildTree_ok buildFts_ok topPath_ok
theorem topCoefs_ok (leaf : Nat) : AllQueriesSatisfy (topCoefs leaf) NotDigestQ := by
  unfold topCoefs topSeedPair; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topCoefs_ok
theorem buildLeafTop_ok (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTop leaf digits signatureOnly) NotDigestQ := by
  unfold buildLeafTop; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildLeafTop_ok
theorem buildTopTree_ok : AllQueriesSatisfy buildTopTree NotDigestQ := by
  unfold buildTopTree
  exact SourceQueries.bind_allowed _ (SourceQueries.foldlM_allowed NotDigestQ _ _ (fun _ _ =>
    SourceQueries.bind_allowed _ (buildLeafTop_ok _ _ _) fun _ => SourceQueries.pure_allowed _ _) _)
    fun _ => buildLevels3_ok _ _ _ _
theorem signTop_ok (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NotDigestQ := by
  unfold signTop; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] signTop_ok
theorem signLayers_ok (cache : T3.Cache) (index n : Nat) (message : Digest) :
    AllQueriesSatisfy (signLayers cache index n message) NotDigestQ := by
  induction n generalizing message with
  | zero => unfold signLayers; aesop (config := { maxRuleApplications := 1000 })
  | succ n ih => unfold signLayers; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] signLayers_ok
theorem forestRows_ok (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (Correctness.forestRows index chosen) NotDigestQ := by
  unfold Correctness.forestRows; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] forestRows_ok
theorem payloadAfterDigest_ok (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payloadAfterDigest cache rho output) NotDigestQ := by
  rw [SigningRecords.payloadAfterDigest_forestRows]; aesop (config := { maxRuleApplications := 1000 })
end aesopShape
theorem allQ_queried {α : Type} (answers : Correctness.Answers) (P : T3.Spec.Domain → Prop) (program : M α)
    (h : AllQueriesSatisfy program P) : ∀ q ∈ queried answers program, P q := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      intro q hq
      rw [SecurityExtraction.queried_query_bind] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hi
      · exact ih _ (hn _) q hq
theorem queried_privateMac (answers : Correctness.Answers) (region : Region) :
    queried answers (privateMac region) =
      [.inr (.inl (header 14 0 0 0 0)), .inr (.inl (header 14 0 0 0 1))] := rfl
theorem queried_privateNonce (answers : Correctness.Answers) (m : Message) :
    queried answers (privateNonce m) = [.inr (.inr (.inl m))] := rfl
end SigGolfCandidate.T3.Security.BPB
