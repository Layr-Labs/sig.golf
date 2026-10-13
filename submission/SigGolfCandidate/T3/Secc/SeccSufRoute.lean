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
theorem hdrBlock_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    Extract.hdrBlock (pad64 (digestInput rho m c)) = SphincsSecurity.bytesLE 16 (digestHeader c) := by
  rw [pad64_digestInput]
  exact Extract.hdrBlock_prefix _ _ _
/-- First header byte (the pre-S1 marker). -/
def hdrByte0 (input : HashInput) : Nat := ((Extract.hdrBlock input).getD 0 0).toNat
/-- Campaign S1: the low header word (bytes 16..24 of the input). The digest is the only query whose low header
word is zero (`digestHeader_lowNat`, `nodeTweak_low_ne_zero`); byte0 alone no longer separates it, because a top
fold label `topNodeWord heap` may have byte0 = 0. -/
def hdrMarker (input : HashInput) : Nat := readLE ((Extract.hdrBlock input).take 8)
theorem hdrMarker_eq {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock input = SphincsSecurity.bytesLE 16 hdr) : hdrMarker input = tweakLow hdr := by
  unfold hdrMarker tweakLow
  rw [h]
  have hs := T3M.readLE_append ((SphincsSecurity.bytesLE 16 hdr).take 8) ((SphincsSecurity.bytesLE 16 hdr).drop 8)
  rw [List.take_append_drop, T3M.readLE_bytesLE 16 hdr] at hs
  have hl : ((SphincsSecurity.bytesLE 16 hdr).take 8).length = 8 := by simp [SphincsSecurity.bytesLE_length]
  have hlt := T3M.readLE_lt ((SphincsSecurity.bytesLE 16 hdr).take 8)
  rw [hl] at hs hlt
  omega
theorem hdrMarker_ne_zero_of_byte0 {input : HashInput} (h : hdrByte0 input ≠ 0) : hdrMarker input ≠ 0 := by
  unfold hdrMarker
  intro h0
  have hd := T3M.readLE_div_mod ((Extract.hdrBlock input).take 8) 0
  rw [h0] at hd
  apply h
  unfold hdrByte0
  have : ((Extract.hdrBlock input).take 8).getD 0 0 = (Extract.hdrBlock input).getD 0 0 := by
    cases Extract.hdrBlock input <;> rfl
  rw [← this, ← hd]
  rfl
theorem hdrMarker_ne_zero {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock input = SphincsSecurity.bytesLE 16 hdr) (hm : tweakMarker hdr ≠ 0) :
    hdrMarker input ≠ 0 := by
  rw [hdrMarker_eq h]
  unfold tweakMarker at hm
  unfold tweakLow
  omega
theorem hdrMarker_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    hdrMarker (pad64 (digestInput rho m c)) = 0 := by
  rw [hdrMarker_eq (hdrBlock_digestInput rho m c), digestHeader_lowNat]
def NotDigestQ : T3.Spec.Domain → Prop
  | .inl (.inr input) => hdrMarker input ≠ 0
  | _ => True
theorem projHash_ok_marker (high : Bool) {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 hdr) (hm : tweakLow hdr ≠ 0) :
    AllQueriesSatisfy (projHash high input) NotDigestQ := by
  unfold projHash publicHash
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (show hdrMarker (pad64 input) ≠ 0 by rw [hdrMarker_eq h]; exact hm)
  · intro _; exact SourceQueries.pure_allowed _ _
theorem shortHash_ok_marker {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 hdr) (hm : tweakMarker hdr ≠ 0) :
    AllQueriesSatisfy (shortHash input) NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (hdrMarker_ne_zero h hm)
  · intro _; exact SourceQueries.pure_allowed _ _
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
  unfold projHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change hdrMarker (pad64 (chainInput lay tree leaf i step v)) ≠ 0
    rw [chainInput_padded]
    apply hdrMarker_ne_zero_of_byte0
    unfold hdrByte0 Extract.hdrBlock
    rw [chainInput_header, bytesLE16_first_toNat]
    have := chainHeader_firstByte lay tree leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem leafHash_ok (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDigestQ :=
  projHash_ok_marker _ (Extract.hdrBlock_leafInput _ _ _ _) (by
    have h := leafTweak_marker lay tree leaf
    unfold tweakMarker at h; unfold tweakLow; omega)
theorem nodeHash_ok (tag lay tree heap : Nat) (left right : Digest) (_ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDigestQ := by
  rw [nodeHash_eq_projHash]
  exact projHash_ok_marker _ (by rw [pad64_nodeInputP]; exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _)
    (nodeTweak_low_ne_zero _ _ _ _)
theorem encoding_ok (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : BitVec 32) :
    AllQueriesSatisfy (shortHash (encodingInput lay tree leaf message counter)) NotDigestQ :=
  shortHash_ok_marker (by
    rw [Extract.hdrBlock_pad64 _ (by simp [encodingInput, SphincsSecurity.bytesLE_length])]
    exact Extract.hdrBlock_prefix _ _ _) (by rw [rowTweak_marker]; decide)
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
section aesopShape
attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed SourceQueries.map_allowed
  SourceQueries.foldlM_allowed SourceQueries.mapM_allowed privatePair_ok mask_ok chain_ok leafHash_ok
  buildLevels3_ok
theorem topPath_ok (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDigestQ := by
  unfold topPath; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topPath_ok
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
