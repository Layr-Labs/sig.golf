import SigGolfCandidate.T3_Secc_PairGuessLazyFree
import SigGolfCandidate.ClaudeWCT_W9_New_Game_Signer
import SigGolfCandidate.ClaudeWCT_Bank_GameInvL
import SigGolfCandidate.ClaudeWCT_Bank_WCTHonest

section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening wctHeader buildChildF buildCoordinateF)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem wct_digestSearch_public {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.producer = WCT9.producerAdmissible) (rho : Digest) (message : Message) :
    ∀ fuel counter, WCT9.digestSearch rho message counter fuel = S.search rho message counter fuel := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [WCT9.digestSearch, FtsBankSpec.search, searchLoop]
      simp only [Sampling.publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, Sampling.publicHandler,
        digest, publicHash, Sampling.digestTrial, FtsBankSpec.decode, hadm]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_pure, map_pure, ih, FtsBankSpec.search, Sampling.publicProgram]
def payAfterDigest (cache : T3.Cache) (rho : Digest) (output : HashOutput) : M (Option WCT9.Signature) := do
  let index := WCT9.digestIndex output
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List (Digest × Digest)) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinateF index coord selected (rank output coord)
        (WCT9.prevPair WCT9.ftsStart state.2)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening],
        state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])) ([], [])
  let top := WCT9.prevPair WCT9.ftsStart state.2
  let some layers ← WCT9.signLayersBC cache index 4 (.pair top.1 top.2) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
theorem signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 attemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem payloadRecord_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.producer = WCT9.producerAdmissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayload cache message := by
  rw [signPayload_factor]
  unfold FtsBankSpec.payloadRecord FtsBankSpec.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
section avoids
variable (m : Message)
theorem avoids_chain (index coord selected i start count : Nat) (value : Digest) :
    NonceFreshness.Avoids m (WCT9.chain index coord selected i start count value) := by
  unfold WCT9.chain
  exact NonceFreshness.avoids_foldlM m _ _ (fun _ _ => NonceFreshness.avoids_projHash m _ _) _
theorem avoids_leafHash (index coord selected : Nat) (ends : List Digest) :
    NonceFreshness.Avoids m (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_forestPk (index : Nat) (roots : List (Digest × Digest)) :
    NonceFreshness.Avoids m (WCT9.forestPk index roots) := by
  unfold WCT9.forestPk
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_buildChildF (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    NonceFreshness.Avoids m (buildChildF index coord selected word coefs pad) :=
  W9.T3.Security.Signer.buildChildF_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
    index coord selected word coefs pad
theorem avoids_ftsCoefs (index coord : Nat) : NonceFreshness.Avoids m (WCT9.ftsCoefs index coord) :=
  W9.T3.Security.Signer.ftsCoefs_allowed _ (fun _ _ _ _ => by simp [NonceFreshness.nonceQuery]) index coord
theorem avoids_buildCoordinateF (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    NonceFreshness.Avoids m (buildCoordinateF index coord selected word prev) :=
  W9.T3.Security.Signer.buildCoordinateF_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
    (fun _ _ _ _ => by simp [NonceFreshness.nonceQuery]) index coord selected word prev
theorem avoids_signLayersBC (cache : T3.Cache) (index n : Nat) (msg : WCT9.LayerMsg) :
    NonceFreshness.Avoids m (WCT9.signLayersBC cache index n msg) :=
  W9.T3.Security.Signer.signLayersBC_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery]) cache
    (W9.T3.Security.Signer.buildTreeP_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
      (fun _ _ _ => by simp [NonceFreshness.nonceQuery]))
    (NonceFreshness.avoids_signTop m cache) index n msg
end avoids
theorem wct_payAvoids : PayAvoids payAfterDigest := by
  intro m cache rho output
  unfold payAfterDigest
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state coord
    exact NonceFreshness.avoids_bind m (avoids_buildCoordinateF m _ _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
  · intro state
    apply NonceFreshness.avoids_bind m (avoids_signLayersBC m _ _ _ _)
    intro layers
    split
    · exact NonceFreshness.avoids_pure m _
    · exact NonceFreshness.avoids_pure m _
theorem wctHeader_value_lt (tag lay tree position index : Nat) :
    1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
      position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 < 2 ^ 128 := by
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem wctHeader_toNat (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat =
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
        position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wctHeader_value_lt _ _ _ _ _)]
theorem wctHeader_byte1 (tag lay tree position index : Nat) :
    ((bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0).toNat = tag % 256 := by
  have h : (bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0 =
      ⟨(wctHeader tag lay tree position index).extractLsb' 8 8⟩ := rfl
  rw [h]
  show ((wctHeader tag lay tree position index).extractLsb' 8 8).toNat = tag % 256
  rw [BitVec.extractLsb'_toNat, wctHeader_toNat, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  generalize tag % 256 = a at *
  generalize lay % 256 = b at *
  generalize tree / 2 ^ 32 % 256 = c at *
  generalize position % 2 ^ 32 = d at *
  generalize tree % 2 ^ 32 = e at *
  generalize index % 2 ^ 32 = f at *
  norm_num at h4 h5 h6 ⊢
  omega
theorem wctHeader_byte0 (tag lay tree position index : Nat) :
    ((bytesLE 16 (wctHeader tag lay tree position index)).getD 0 0).toNat = 1 := by
  rw [bytesLE16_first_toNat, wctHeader_toNat]
  omega
theorem hdrBlock_pad64_prefix (a h rest : HashInput) (ha : a.length = 16) (hh : h.length = 16) :
    T3M.Extract.hdrBlock (pad64 (a ++ h ++ rest)) = h := by
  rw [T3M.Extract.hdrBlock_pad64 _ (by simp [ha, hh]; omega)]
  unfold T3M.Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hh]
theorem shortHash_wct_ok (a rest : HashInput) (tag lay tree position index : Nat) (ha : a.length = 16)
    (_ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (shortHash (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) BPB.NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0
    rw [hdrBlock_pad64_prefix _ _ _ ha (bytesLE_length _ _), wctHeader_byte0]
    decide
  · intro _; exact SourceQueries.pure_allowed _ _
/-- Witness stack: FTS chain step in either format (G chains 1, 3: `value | header | 0 | 0`). -/
theorem chainInput_ok (index coord selected i step : Nat) (high : Bool) (value : Digest) :
    AllQueriesSatisfy (projHash high (WCT9.ftsChainInputW index coord selected i step value)) BPB.NotDigestQ := by
  unfold projHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (WCT9.ftsChainInputW index coord selected i step value)) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0 WCT9.ftsChainInputW
    split
    · rw [List.append_assoc (bytesLE 16 value ++ _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)
        (bytesLE_length _ _), bytesLE16_first_toNat, WCT9.ftsChainHeader_toNat, WCT9.ftsChainLow_byte0]
      omega
    · unfold WCT9.chainInput
      rw [List.append_assoc (zero16 ++ _), hdrBlock_pad64_prefix _ _ _ (by simp [zero16]) (bytesLE_length _ _),
        bytesLE16_first_toNat, WCT9.ftsChainHeader_toNat, WCT9.ftsChainLow_byte0]
      omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem chain_ok (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) BPB.NotDigestQ := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed BPB.NotDigestQ _ _ (fun v step => chainInput_ok _ _ _ _ _ _ _) _
theorem leafHash_ok (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) BPB.NotDigestQ := by
  unfold WCT9.leafHash shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.ftsLeafHeader index coord selected) ++
      zero16 ++ (ends.drop 1).flatMap (bytesLE 16))) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0
    rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _) (bytesLE_length _ _), bytesLE16_first_toNat,
      WCT9.ftsLeafHeader_firstByte]
    decide
  · intro _; exact SourceQueries.pure_allowed _ _
theorem leafHashP_ok (index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashP index coord selected pad ends) BPB.NotDigestQ := by
  unfold WCT9.leafHashP WCT9.leafInputP shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.ftsLeafHeader index coord selected) ++
      bytesLE 16 pad ++ (ends.drop 1).flatMap (bytesLE 16))) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0
    rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _) (bytesLE_length _ _), bytesLE16_first_toNat,
      WCT9.ftsLeafHeader_firstByte]
    decide
  · intro _; exact SourceQueries.pure_allowed _ _
theorem topHash_ok (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (WCT9.wctTopHash coord index heap left pad right) BPB.NotDigestQ :=
  WCT9.allQ_highHash_of_shortHash _ (BPB.shortHash_ok_marker
    (show T3M.Extract.hdrBlock (pad64 (WCT9.wctTopInput coord index heap left pad right)) =
        SphincsSecurity.bytesLE 16 (nodeTweak 3 (WCT9.nodeLayer coord) index heap) by
      change T3M.Extract.hdrBlock (pad64 (T3M.SecurityInputs.nodeInputP 3 (WCT9.nodeLayer coord) index heap
        left pad right)) = _
      rw [T3M.SecurityInputs.pad64_nodeInputP]; exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _)
    (nodeTweak_marker_ne_zero (by unfold WCT9.nodeLayer; omega) _ _))
theorem forest_header_plain (index : Nat) : header 15 0 index 0 0 = wctHeader 15 0 index 0 0 := by
  unfold wctHeader header
  rw [if_neg (by decide)]
  simp only [Nat.add_assoc]
theorem forestPk_ok (index : Nat) (roots : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index roots) BPB.NotDigestQ := by
  unfold WCT9.forestPk WCT9.forestInput
  rw [forest_header_plain]
  exact shortHash_wct_ok _ _ 15 _ _ _ _ (by simp [zero16]) (by decide)
theorem hdrBlock_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    T3M.Extract.hdrBlock (pad64 (WCT9.pairEncodingInputP lay tree leaf left right counter pad)) =
      SphincsSecurity.bytesLE 16 (rowTweak lay tree leaf) := by
  have hl : (WCT9.pairEncodingInputP lay tree leaf left right counter pad).length = 64 := by
    simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
  rw [T3M.Extract.hdrBlock_pad64 _ (by omega)]
  unfold WCT9.pairEncodingInputP
  rw [List.append_assoc, List.append_assoc]
  exact T3M.Extract.hdrBlock_prefix _ _ _
theorem layerEncoding_ok (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) BPB.NotDigestQ := by
  cases msg with
  | forest root => exact BPB.encoding_ok lay tree leaf root counter
  | pair left right =>
      exact BPB.shortHash_ok_marker (hdrBlock_pairEncodingInputP lay tree leaf left right counter 0)
        (by rw [rowTweak_marker]; decide)
theorem buildChildF_ok (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (buildChildF index coord selected word coefs pad) BPB.NotDigestQ := by
  unfold buildChildF
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state i
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed _ _
  · intro state
    exact SourceQueries.bind_allowed _ (leafHashP_ok _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
/-- C1: the FTS leaf of heap `heap` (either hash half) makes the legacy padded leaf's single query. -/
theorem leafHashH_ok (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashH heap index coord selected pad ends) BPB.NotDigestQ := by
  rw [WCT9.leafHashH_eq]
  exact WCT9.allQ_ftsHash_of_shortHash heap _ (leafHashP_ok index coord selected pad ends)
/-- C1: `buildChildF_ok` for the heap-indexed child `buildChildH`. -/
theorem buildChildH_ok (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (WCT9.buildChildH heap index coord selected word coefs pad) BPB.NotDigestQ := by
  unfold WCT9.buildChildH
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state i
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed _ _
  · intro state
    exact SourceQueries.bind_allowed _ (leafHashH_ok _ _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
theorem ftsCoefs_ok (index coord : Nat) : AllQueriesSatisfy (WCT9.ftsCoefs index coord) BPB.NotDigestQ := by
  unfold WCT9.ftsCoefs
  apply SourceQueries.foldlM_allowed
  intro acc j
  exact SourceQueries.bind_allowed _ (BPB.privatePair_ok _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
theorem buildCoordinateF_ok (index : Nat) (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    AllQueriesSatisfy (buildCoordinateF index coord selected word prev) BPB.NotDigestQ := by
  unfold buildCoordinateF
  apply SourceQueries.bind_allowed _ (ftsCoefs_ok _ _)
  intro coefs
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state j
    exact SourceQueries.bind_allowed _ (buildChildF_ok _ _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed
    · unfold WCT9.heapBuild
      apply SourceQueries.foldlM_allowed
      intro nodes heap
      refine SourceQueries.bind_allowed _ ?_ fun _ => SourceQueries.pure_allowed _ _
      unfold WCT9.wctHeapNode
      split
      · exact topHash_ok _ _ _ _ _ _
      · exact BPB.nodeHash_ok 3 _ _ _ _ _ (by decide)
    · intro _
      exact SourceQueries.pure_allowed _ _
/-- C2 (FULL): a lower node query of the honest tree shape (heap below `2 ^ height lay`) is no digest query: the
packed node word's marker is `128 + heap`. -/
theorem lowerNodeHash_notDigest (lay : Layer) (tree heap : Nat) (left right : Digest) (hh : heap < 2 ^ height lay) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerNodeHash lay.val tree heap left right)
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  by_cases h0 : lay.val = 0
  · rw [h0, ClaudeWCT.WCT9.lowerNodeHash_top]
    exact SigGolfCandidate.T3.Security.BPB.nodeHash_ok _ _ _ _ _ _ (by decide)
  · have h7 : heap < 128 := lt_of_lt_of_le hh
      ((Nat.pow_le_pow_right (by decide) (ClaudeWCT.W9.T3.Security.Signer.height_le_seven h0)).trans (by norm_num))
    unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash
    refine ClaudeWCT.W9.T3.Security.Signer.halfHash_allowed_of_short _ _
      (SigGolfCandidate.T3.Security.BPB.shortHash_ok_marker
        (hdr := ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ?_ ?_)
    · unfold ClaudeWCT.WCT9.merkleNodeInput
      rw [List.append_assoc (SphincsSecurity.bytesLE 16 left ++
          SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap)),
        SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [SphincsSecurity.bytesLE_length, zero16]),
        SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
    · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]
      unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
      rw [SigGolfCandidate.T3.append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat,
        SigGolfCandidate.T3.hyperWord_toNat]
      omega
open SigGolfCandidate.T3.Security.BPB SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs in
/-- Pairing stage 1: a chain step of the current scheme (either format) is not a digest query. -/
theorem chainStepW_ok_rev3 (lay : SigGolfCandidate.T3.Layer) (tree leaf i step : Nat) (v : SigGolfCandidate.T3.Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.shortHash (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  unfold SigGolfCandidate.T3.shortHash SigGolfCandidate.T3.publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change hdrMarker (SigGolfCandidate.T3.pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v)) ≠ 0
    rw [ClaudeWCT.WCT9.chainInputW_padded]
    apply hdrMarker_ne_zero_of_byte0
    unfold hdrByte0 Extract.hdrBlock
    rw [ClaudeWCT.WCT9.chainInputW_header, bytesLE16_first_toNat]
    have := SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem wct_payNotDigest : PayNotDigest payAfterDigest := by
  intro cache rho output
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinateF_ok _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed _ (W9.T3.Security.Signer.signLayersBC_allowed' _ _ layerEncoding_ok
      (W9.T3.Security.Signer.buildTreeP_allowed' _ chainStepW_ok_rev3 BPB.leafHash_ok
        (fun lay _ _ _ _ hh => lowerNodeHash_notDigest lay _ _ _ _ hh)
        (fun _ _ _ => BPB.privatePair_ok _ _ _ _ _)) (BPB.signTop_ok _) _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end ClaudeWCT.Bank.WCT
end
section
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_exists_admissible : ∃ x, digestAdmissible x = true := by
  obtain ⟨x, hx⟩ := CaseC.admissibleSet_nonempty
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩
theorem bpors_acceptance_eq :
    Pr[fun x : HashOutput => digestAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) CaseC.admInd := by
  unfold CaseC.admInd
  rw [expectedValue_ite_one]
theorem bpors_one_le_score (X : List HashOutput) (N : HashOutput) (hadm : digestAdmissible N = true)
    (hcov : ∀ c, CaseC.CoordCovered X N c) : 1 ≤ CaseC.score X N := by
  unfold digestAdmissible at hadm
  rw [Bool.and_eq_true] at hadm
  exact CaseC.one_le_score X N (CaseC.outLeaves_injective N hadm.1) hadm.2 hcov
theorem bpors_finiteAverage (g : BPORS.History.Proposal → ENNReal) :
    BPORS.finiteAverage g = ∑ p, (Fintype.card BPORS.History.Proposal : ENNReal)⁻¹ * g p := by
  unfold BPORS.finiteAverage
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _
theorem bpors_law_sum : ∑ _p : BPORS.History.Proposal, (Fintype.card BPORS.History.Proposal : ENNReal)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
noncomputable def bporsSpec : FtsBankSpec BPORS.History.Proposal where
  admissible := digestAdmissible
  producer := digestAdmissible
  exists_producer := bpors_exists_admissible
  acceptance_le := bpors_acceptance_eq ▸ CaseC.expected_admInd_tight
  proposal := CaseC.label
  law := fun _ => (Fintype.card BPORS.History.Proposal : ENNReal)⁻¹
  law_sum := bpors_law_sum
  accepted_proposal g := by
    rw [Sampling.digest_acceptanceProbability, ← bpors_finiteAverage]
    exact accepted_samplingData g
  score := CaseC.score
  covered X N := ∀ c, CaseC.CoordCovered X N c
  one_le_score := bpors_one_le_score
  score_append_mono := CaseC.score_append_mono
  price := BPORS.History.fullPrice
  average_score := CaseC.average_score
  horizon := BPORS.Numeric.proposalLength
  excessRate := 11324 / 100000000
  excess_le := (ClaudeWCT.Numerics.Law.lawAvg_uniform _ _).le.trans CaseC.excess_three_quarters
theorem bpors_decode : bporsSpec.decode = Sampling.digestDecode := rfl
theorem bpors_acceptance : bporsSpec.acceptance = acceptanceProbability := Sampling.digest_acceptanceProbability
theorem bpors_freshPrice (w : HashOutput → ENNReal) :
    bporsSpec.freshPrice w = Sampling.WeightedSelection.freshPrice w := by
  unfold FtsBankSpec.freshPrice Sampling.WeightedSelection.freshPrice
  rw [bpors_acceptance]
  rfl
theorem bpors_search (rho : Digest) (m : Message) (counter fuel : Nat) :
    bporsSpec.search rho m counter fuel = digestSearch rho m counter fuel :=
  (Sampling.digestSearch_public rho m fuel counter).symm
theorem bpors_admissibleSet : bporsSpec.admissibleSet = CaseC.admissibleSet := by
  ext x
  simp [FtsBankSpec.admissibleSet, CaseC.admissibleSet, bporsSpec]
theorem bpors_accepted : bporsSpec.accepted = CaseC.accepted := by
  unfold FtsBankSpec.accepted CaseC.accepted
  congr 1
theorem bpors_forecast : bporsSpec.forecast = CaseC.forecast := by
  funext R X N
  unfold FtsBankSpec.forecast CaseC.forecast
  rw [bpors_accepted]
  rfl
theorem bpors_excessForecast : bporsSpec.excessForecast = CaseC.excessForecast := by
  funext R X
  unfold FtsBankSpec.excessForecast CaseC.excessForecast
  exact ClaudeWCT.Numerics.Law.lawAvg_uniform _ _
theorem bpors_ledger : bporsSpec.ledger = CaseC.ledger := by
  funext R targets X slack
  unfold FtsBankSpec.ledger CaseC.ledger
  rw [bpors_forecast, bpors_excessForecast]
theorem bpors_corePotential : bporsSpec.corePotential = CaseC.corePotential := by
  funext b
  unfold FtsBankSpec.corePotential CaseC.corePotential
  rw [bpors_ledger]
  rfl
theorem bpors_Reuse : bporsSpec.Reuse = CaseC.Reuse := rfl
theorem bpors_admissibleEntry : bporsSpec.admissibleEntry = CaseC.admissibleEntry := by
  funext cache input
  unfold FtsBankSpec.admissibleEntry CaseC.admissibleEntry
  cases cache input <;> simp [bporsSpec]
theorem bpors_reuseMass : bporsSpec.reuseMass = CaseC.reuseMass := by
  funext cache m
  unfold FtsBankSpec.reuseMass CaseC.reuseMass
  rw [bpors_admissibleEntry]
theorem bpors_admInd : bporsSpec.admInd = CaseC.admInd := by
  funext a
  simp [FtsBankSpec.admInd, CaseC.admInd, bporsSpec]
theorem bpors_recordForNonce (cache : T3.Cache) (rho : Digest) (m : Message) :
    bporsSpec.recordForNonce payloadAfterDigest cache rho m = payloadRecordForNonce cache rho m := by
  unfold FtsBankSpec.recordForNonce payloadRecordForNonce
  rw [bpors_search]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem bpors_record (published : T3.Cache) (request : Request) :
    bporsSpec.authenticatedRecord payloadAfterDigest published request =
      FullGame.authenticatedRecord published request := by
  unfold FtsBankSpec.authenticatedRecord FullGame.authenticatedRecord
  apply bind_congr
  intro tag
  by_cases h : request.cache = published
  · simp only [h, if_true]
    unfold FtsBankSpec.payloadRecord payloadRecord
    apply bind_congr
    intro rho
    exact bpors_recordForNonce _ rho _
  · simp only [h, if_false]
theorem t3_core_sign (b : CaseC.BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + CaseC.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if CaseC.Reuse cache rho m then CaseC.corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => CaseC.corePotential (b.expose C' (result.1.map Prod.snd)))) ≤ CaseC.corePotential b := by
  have h := bporsSpec.core_sign b cache m C' (by rw [bpors_reuseMass]; exact hC) secret fuel hfuel
  simp only [bpors_corePotential, bpors_Reuse, bpors_search] at h
  exact h
theorem t3_core_birth (b : CaseC.BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + CaseC.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => CaseC.corePotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      CaseC.corePotential b + (CaseC.theta + 1 / 64) / 2 ^ 128 := by
  have h := bporsSpec.core_birth b s hs C' (by rw [bpors_admInd]; exact hC)
  simp only [bpors_corePotential] at h
  exact h
theorem t3_core_initial (budget : Nat) :
    CaseC.corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have h := bporsSpec.core_initial budget
  rw [bpors_corePotential] at h
  exact h
theorem t3_core_win (b : CaseC.BankCore) (halive : ¬BPORS.Numeric.proposalLength < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, admissible (selections N) = true ∧ digestGate N = true ∧
      CaseC.CoveredBy b.exposures N) :
    1 ≤ CaseC.corePotential b := by
  rw [← bpors_corePotential]
  apply bporsSpec.core_win b halive
  rcases h with h | ⟨N, hN, hadm, hgate, hcov⟩
  · exact Or.inl h
  · refine Or.inr ⟨N, hN, ?_, ?_⟩
    · change digestAdmissible N = true
      unfold digestAdmissible
      rw [Bool.and_eq_true]
      exact ⟨hadm, hgate⟩
    · exact fun c => CaseC.coordCovered_of_opened b.exposures N c fun j => hcov _ (CaseC.opened_mem N c j)
theorem t3_fresh_signing_kernel (published : T3.Cache) (m : Message) (state : LazyPrivate.State)
    (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Signature × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P : ENNReal) (hP : Sampling.WeightedSelection.freshPrice w ≤ P)
    (hF : ∀ result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state),
      F result ≤ if CaseC.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P w) :
    expectedValue (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state) F ≤
      P + CaseC.reuseMass state.2 m := by
  have h := bporsSpec.fresh_signing_kernel payloadAfterDigest published m state hfresh F w P
    (by rw [bpors_freshPrice]; exact hP) (by rw [bpors_record]; exact hF)
  rw [bpors_record, bpors_reuseMass] at h
  exact h
theorem bpors_payNotDigest : PayNotDigest payloadAfterDigest := BPB.payloadAfterDigest_ok
theorem bpors_source (published : T3.Cache) :
    bporsSpec.source payloadAfterDigest published = MonitoredPrivate.interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request =>
      change Prod.fst <$> bporsSpec.authenticatedRecord payloadAfterDigest published request =
        FullGame.authenticatedSign published request
      rw [bpors_record, FullGame.authenticatedRecord_erasure]
end ClaudeWCT.Bank.BPORSRegression
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression2 : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_payAvoids : PayAvoids payloadAfterDigest := by
  intro m cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(NonceFreshness.avoids_pure m), (NonceFreshness.avoids_bind m), (NonceFreshness.avoids_map m),
      (NonceFreshness.avoids_foldlM m), (NonceFreshness.avoids_mapM m), (NonceFreshness.avoids_buildFts m),
      (NonceFreshness.avoids_forestPk m), (NonceFreshness.avoids_signLayers m)])
theorem bpors_recordedExperiment (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget =
      bporsSpec.recordedExperiment payloadAfterDigest (CreationGame.rest adversary) := by
  rw [CreationGame.padded_trace_eq, FtsBankSpec.recordedExperiment, map_bind]
  apply bind_congr
  intro generated
  have ht := (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_erasure
    (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [QueryRecorded.proposal_execution_erasure] at ht
  rw [bpors_source]
  exact ht
theorem bpors_birthWeight (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    birthWeight (Sig := Signature) budget input state.2 =
      (CreationGame.classWeight CaseC.IsDigestInput budget input state : ENNReal) := by
  rcases input with (n | x) | request
  · simp [birthWeight, CreationGame.classWeight]
  · simp only [birthWeight, CreationGame.classWeight]
    by_cases h : CaseC.Birth budget x state.2
    · have h' : state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none :=
        ⟨h.2.2, h.1, h.2.1⟩
      rw [if_pos h, if_pos h', Nat.cast_one]
    · have h' : ¬(state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none) :=
        fun h' => h ⟨h'.2.1, h'.2.2, h'.1⟩
      rw [if_neg h, if_neg h', Nat.cast_zero]
  · simp [birthWeight, CreationGame.classWeight]
theorem bpors_expectedBirths (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    bporsSpec.expectedBirths payloadAfterDigest (CreationGame.rest adversary) budget =
      CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget := by
  unfold FtsBankSpec.expectedBirths CreationGame.expectedBirths
  congr 1
  funext generated
  have ht := BPORS.Adaptive.Creation.expectedCharges_project
    (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
    (bporsSpec.recordedImpl payloadAfterDigest generated.1.2) Prod.snd
    (fun input st => by
      rw [(QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_query_erasure,
        QueryRecorded.proposal_query_erasure, ← bpors_source]
      rfl)
    (birthWeight budget) (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [← ht]
  congr 1
  funext input state
  exact bpors_birthWeight budget input state
theorem t3_bank_potential_le (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    expectedValue (bporsSpec.bankExperiment payloadAfterDigest (CreationGame.rest adversary) budget)
        (fun r => bporsSpec.potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget +
        (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  rw [← bpors_expectedBirths adversary budget hbudget]
  exact bporsSpec.bank_potential_le payloadAfterDigest bpors_payNotDigest bpors_payAvoids
    (CreationGame.rest adversary) budget
end ClaudeWCT.Bank.BPORSRegression
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctBank : DecidableEq T3.Cache := Classical.decEq _
variable (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
noncomputable def authenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.signPayload request.cache request.message else pure none
theorem wct_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpec' horizon rate hexc).authenticatedRecord payAfterDigest published request =
      authenticatedSign published request := by
  unfold FtsBankSpec.authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure _ rfl _ _
  · rfl
theorem wct_source_sign (published : T3.Cache) (request : Request) :
    (wctSpec' horizon rate hexc).source payAfterDigest published (.inr request) =
      authenticatedSign published request :=
  wct_record_erasure horizon rate hexc published request
noncomputable def interactionSource (published : T3.Cache) : QueryImpl (Interaction' WCT9.Signature) M
  | .inl input => forwardWorld input
  | .inr request => authenticatedSign published request
theorem wct_source (published : T3.Cache) :
    (wctSpec' horizon rate hexc).source payAfterDigest published = interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact wct_source_sign horizon rate hexc published request
theorem wct_recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) :
    (wctSpec' horizon rate hexc).recordedExperiment payAfterDigest rest = (do
      let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
      (liftM (QueryRecorded.run (simulateQ (interactionSource generated.1.2) (rest generated.1.1 generated.1.2))
        generated.2) : PMF _)) := by
  unfold FtsBankSpec.recordedExperiment
  simp only [wct_source]
theorem wct_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpec' horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpec' horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec' horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec' horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wct_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpec' horizon rate hexc).potential budget st :=
  (wctSpec' horizon rate hexc).potential_win budget st halive hcount h
theorem wct_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpec' horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpec' horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpec' horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec' horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec' horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
end ClaudeWCT.Bank.WCT
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening buildChildF buildCoordinateF)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section allowed
variable (Q : T3.Spec.Domain → Prop) (hpublic : ∀ input, Q (.inl (.inr input)))
  (hpair : ∀ tweak, Q (.inr (.inl tweak))) (hnonce : ∀ message, Q (.inr (.inr (.inl message))))
include hpublic in
theorem chain_allowed (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) Q := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ => SourceQueries.projHash_allowed Q hpublic _ _) _
include hpublic in
theorem buildChildF_allowed (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (buildChildF index coord selected word coefs pad) Q :=
  W9.T3.Security.Signer.buildChildF_allowed Q hpublic index coord selected word coefs pad
include hpublic hpair in
theorem buildCoordinateF_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    AllQueriesSatisfy (buildCoordinateF index coord selected word prev) Q :=
  W9.T3.Security.Signer.buildCoordinateF_allowed Q hpublic (fun _ _ _ _ => hpair _) index coord selected word prev
include hpublic hpair hnonce in
theorem payAfterDigest_allowed (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payAfterDigest cache rho output) Q := by
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinateF_allowed Q hpublic hpair _ _ _ _ _)
      fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed _ (W9.T3.Security.Signer.signLayersBC_allowed Q hpublic _
      (W9.T3.Security.Signer.buildTreeP_allowed Q hpublic (fun _ _ _ => hpair _))
      (SourceQueries.signTop_allowed Q hpublic hpair hnonce _) _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end allowed
theorem wct_payHashOnly : PayHashOnly payAfterDigest :=
  payAfterDigest_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
theorem wct_payRho : PayRho payAfterDigest WCT9.Signature.rho := by
  intro A cache rho output σ h
  unfold payAfterDigest at h
  simp only [evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl
variable (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
theorem wct_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpec' horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpec' horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpec' horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
end ClaudeWCT.Bank.WCT
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bpors_payHashOnly : PayHashOnly payloadAfterDigest := by
  intro cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(SourceQueries.pure_allowed Security.SourceReplay.IsHash),
      (SourceQueries.bind_allowed Security.SourceReplay.IsHash),
      (SourceQueries.foldlM_allowed Security.SourceReplay.IsHash),
      (SourceQueries.map_allowed Security.SourceReplay.IsHash),
      (SourceQueries.buildFts_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.forestPk_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.signLayers_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial))])
theorem bpors_payRho : PayRho payloadAfterDigest Signature.rho :=
  CaseC.eval_payloadAfterDigest_rho
end ClaudeWCT.Bank.BPORSRegression
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctRev3 : DecidableEq T3.Cache := Classical.decEq _
theorem signPayloadWith_factor (limit : Nat) (cache : T3.Cache) (message : Message) :
    WCT9.signPayloadWith limit cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 limit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayloadWith
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem rev3_signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.Rev3.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 WCT9.digestAttemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) :=
  signPayloadWith_factor WCT9.digestAttemptLimit cache message
theorem payloadRecordL_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
    (hadm : S.producer = WCT9.producerAdmissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayloadWith S.limit cache message := by
  rw [signPayloadWith_factor]
  unfold FtsBankSpecL.payloadRecord FtsBankSpecL.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S.toFtsBankSpec hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
noncomputable def wctSpecL (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    FtsBankSpecL WProposal :=
  (wctSpec' horizon rate hexc).atLimit WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le
variable (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate)
@[simp] theorem wctSpecL_limit : (wctSpecL horizon rate hexc).limit = WCT9.digestAttemptLimit := rfl
theorem wctSpecL_admissible : (wctSpecL horizon rate hexc).admissible = WCT9.admissible := rfl
theorem wctSpecL_producer : (wctSpecL horizon rate hexc).producer = WCT9.producerAdmissible := rfl
theorem wctSpecL_law : (wctSpecL horizon rate hexc).law = honestLaw := rfl
@[simp] theorem wctSpecL_horizon : (wctSpecL horizon rate hexc).horizon = horizon := rfl
noncomputable def rev3AuthenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.Rev3.signPayload request.cache request.message else pure none
theorem wctL_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpecL horizon rate hexc).authenticatedRecord payAfterDigest published request =
      rev3AuthenticatedSign published request := by
  unfold FtsBankSpecL.authenticatedRecord rev3AuthenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecordL_erasure _ rfl _ _
  · rfl
theorem excess_of_excessBound (h : ExcessBound horizon rate) :
    ClaudeWCT.Numerics.Law.lawAvg (wctSpecL horizon rate hexc).law (wctSpecL horizon rate hexc).horizon
      (fun W : List WProposal => (wctSpecL horizon rate hexc).price W - 1023 / 1024) ≤ rate := h
theorem wctL_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpecL horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wctL_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpecL horizon rate hexc).potential budget st :=
  (wctSpecL horizon rate hexc).potential_win budget st halive hcount h
theorem wctL_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpecL horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpecL horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
theorem wctL_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpecL horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpecL horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
theorem wctL_search (rho : Digest) (m : Message) :
    (wctSpecL horizon rate hexc).search rho m 0 (wctSpecL horizon rate hexc).limit =
      WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit :=
  (wct_digestSearch_public (wctSpecL horizon rate hexc).toFtsBankSpec rfl rho m _ 0).symm
end ClaudeWCT.Bank.WCT
end

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable def bankSpec : FtsBankSpecL Proposal :=
  lawSpec.atLimit ClaudeWCT.WCT9.digestAttemptLimit (by decide +kernel)

theorem digestSearch_public (rho : Digest) (message : Message) :
    ∀ fuel counter, SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message counter fuel =
      lawSpec.search rho message counter fuel := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [SigGolfCandidate.Research.SharedForest.sharedDigestSearch, FtsBankSpec.search, searchLoop]
      simp only [Sampling.publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, Sampling.publicHandler,
        digest, publicHash, Sampling.digestTrial, FtsBankSpec.decode,
        show lawSpec.producer = producer from rfl, producer_source]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_pure, map_pure, ih, FtsBankSpec.search, Sampling.publicProgram]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def payAfterDigest (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (output : HashOutput) :
    M (Option SharedForest.Signature) :=
  Option.map SharedForest.Witness.signature <$> SharedForest.signFromOutput cache rho 0 output

theorem signature_counter (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) :
    Option.map SharedForest.Witness.signature <$> SharedForest.signFromOutput cache rho counter output =
      payAfterDigest cache rho output := by
  unfold payAfterDigest SharedForest.signFromOutput
  simp only [map_bind]
  apply bind_congr
  intro forest
  apply bind_congr
  intro prepared
  apply bind_congr
  intro layers
  cases layers <;> rfl

theorem signPayload_factor (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SharedForest.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← SharedForest.sharedDigestSearch rho message 0 ClaudeWCT.WCT9.digestAttemptLimit
      match found with
      | none => pure none
      | some (_,output) => payAfterDigest cache rho output) := by
  unfold SharedForest.signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  cases found with
  | none => rfl
  | some found =>
      rcases found with ⟨counter,output⟩
      dsimp only
      rw [← signature_counter cache rho counter output]
      simp only [map_eq_bind_pure_comp]
      apply bind_congr
      intro witness
      cases witness <;> rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure ForestAllowed (Q : SigGolfCandidate.T3.Spec.Domain → Prop) : Prop where
  coefs : ∀ index coord, AllQueriesSatisfy (ftsCoefs index coord) Q
  child : ∀ heap index coord selected word coefs pad,
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs pad) Q
  node : ∀ first coord index heap pads left right,
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) Q

section
variable (Q : SigGolfCandidate.T3.Spec.Domain → Prop) (hQ : ForestAllowed Q)
include hQ

theorem sharedHeap_allowed (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) : AllQueriesSatisfy (sharedHeap first index coord pads leaves) Q := by
  unfold sharedHeap
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ =>
    SourceQueries.bind_allowed Q (hQ.node ..) fun _ => SourceQueries.pure_allowed Q _) _

theorem sharedCoordinate_allowed (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (buildSharedCoordinate first index coord selected word pads) Q := by
  unfold buildSharedCoordinate
  exact SourceQueries.bind_allowed Q (hQ.coefs ..) fun _ =>
    SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _
      (fun _ _ => SourceQueries.bind_allowed Q (hQ.child ..) fun _ => SourceQueries.pure_allowed Q _) _) fun _ =>
      SourceQueries.bind_allowed Q (sharedHeap_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem pair_allowed (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) : AllQueriesSatisfy (buildPair index pair s aWord bWord prev) Q := by
  unfold buildPair
  exact SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem singleton_allowed (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    AllQueriesSatisfy (buildSingleton index selected word prev) Q := by
  unfold buildSingleton
  exact SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem forest_allowed (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (buildForest index selected words) Q := by
  unfold buildForest
  exact SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _
    (fun _ _ => SourceQueries.bind_allowed Q (pair_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _) _) fun _ =>
    SourceQueries.bind_allowed Q (singleton_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _
end

section
variable (Q : SigGolfCandidate.T3.Spec.Domain → Prop)
  (hpublic : ∀ input, Q (.inl (.inr input)))
  (hpair : ∀ tweak, Q (.inr (.inl tweak)))
  (htop : ∀ cache leaf digits, AllQueriesSatisfy (signTop cache leaf digits) Q)

include hpublic hpair htop in
theorem tail_public : SharedQueries.TailAllowed Q where
  chainStep := fun _ _ _ _ _ _ => SourceQueries.shortHash_allowed Q hpublic _
  chainStepW := fun _ _ _ _ _ _ => SourceQueries.shortHash_allowed Q hpublic _
  leaf := fun _ _ _ _ => SourceQueries.shortHash_allowed Q hpublic _
  node := fun _ _ _ _ _ _ => W9.T3.Security.Signer.lowerNodeHash_allowed_of_public Q hpublic _ _ _ _ _
  seed := fun _ _ _ => SourceQueries.privatePair_allowed Q hpair _ _ _ _ _
  encoding := fun lay _ _ msg _ => by
    cases msg <;> exact SourceQueries.shortHash_allowed Q hpublic _
  top := htop

include hpublic hpair in
theorem forest_public : ForestAllowed Q where
  coefs := fun _ _ => W9.T3.Security.Signer.ftsCoefs_allowed Q (fun _ _ _ _ => hpair _) _ _
  child := W9.T3.Security.Signer.buildChildH_allowed Q hpublic
  node := W9.T3.Security.Signer.sharedNode_allowed Q hpublic
end

theorem pay_allowed (Q : SigGolfCandidate.T3.Spec.Domain → Prop)
    (htail : SharedQueries.TailAllowed Q) (hforest : ForestAllowed Q)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payAfterDigest cache rho output) Q :=
  SourceQueries.map_allowed Q _ (SharedQueries.signFromOutput_allowed Q htail
    (forest_allowed Q hforest) cache rho 0 output)

theorem payHashOnly : PayHashOnly payAfterDigest :=
  pay_allowed _ (tail_public _ (fun _ => trivial) (fun _ => trivial)
    (SourceQueries.signTop_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)))
    (forest_public _ (fun _ => trivial) (fun _ => trivial))

theorem payAvoids : PayAvoids payAfterDigest := by
  intro message
  apply pay_allowed
  · exact tail_public _ (fun _ => by simp [NonceFreshness.nonceQuery])
      (fun _ => by simp [NonceFreshness.nonceQuery]) (NonceFreshness.avoids_signTop message)
  · exact forest_public _ (fun _ => by simp [NonceFreshness.nonceQuery])
      (fun _ => by simp [NonceFreshness.nonceQuery])

theorem tail_notDigest : SharedQueries.TailAllowed BPB.NotDigestQ where
  chainStep := fun lay tree leaf i step value => by
    unfold shortHash publicHash
    apply SourceQueries.bind_allowed
    · apply (allQueriesSatisfy_query_iff _ _).mpr
      change BPB.hdrMarker (pad64 (SigGolfCandidate.T3.chainInput lay tree leaf i step value)) ≠ 0
      rw [chainInput_padded]
      apply BPB.hdrMarker_ne_zero_of_byte0
      unfold BPB.hdrByte0 SigGolfCandidate.T3M.Extract.hdrBlock
      rw [chainInput_header, bytesLE16_first_toNat]
      have := chainHeader_firstByte lay tree leaf i step
      omega
    · intro _; exact SourceQueries.pure_allowed _ _
  chainStepW := ClaudeWCT.Bank.WCT.chainStepW_ok_rev3
  leaf := BPB.leafHash_ok
  node := fun lay _ _ _ _ hh => ClaudeWCT.Bank.WCT.lowerNodeHash_notDigest lay _ _ _ _ hh
  seed := fun _ _ _ => BPB.privatePair_ok _ _ _ _ _
  encoding := WCT.layerEncoding_ok
  top := BPB.signTop_ok

theorem topInput_notDigest (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (shortHash (wctTopInput coord index heap left pad right)) BPB.NotDigestQ :=
  BPB.shortHash_ok_marker
    (show SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (wctTopInput coord index heap left pad right)) =
      SphincsSecurity.bytesLE 16 (nodeTweak 3 (nodeLayer coord) index heap) by
      change SigGolfCandidate.T3M.Extract.hdrBlock
        (pad64 (SigGolfCandidate.T3M.SecurityInputs.nodeInputP 3 (nodeLayer coord) index heap left pad right)) = _
      rw [SigGolfCandidate.T3M.SecurityInputs.pad64_nodeInputP]
      exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _)
    (nodeTweak_marker_ne_zero (by simp [nodeLayer]) _ _)

theorem forest_notDigest : ForestAllowed BPB.NotDigestQ where
  coefs := WCT.ftsCoefs_ok
  child := WCT.buildChildH_ok
  node := fun first coord index heap pads left right => by
    unfold sharedNode sharedOuterHash
    split
    · split
      · exact topInput_notDigest ..
      · exact allQ_highHash_of_shortHash _ (topInput_notDigest ..)
    · split
      · split
        · exact allQ_highHash_of_shortHash _ (topInput_notDigest ..)
        · exact topInput_notDigest ..
      · exact ClaudeWCT.WCT9.allQ_ftsHash_of_shortHash heap (ClaudeWCT.WCT9.nodeInput coord index heap left right)
          (BPB.nodeHash_ok 3 (ClaudeWCT.WCT9.nodeLayer coord) index heap left right (by decide))

theorem payNotDigest : PayNotDigest payAfterDigest :=
  pay_allowed _ tail_notDigest forest_notDigest

theorem payRho : PayRho payAfterDigest SigGolfCandidate.Research.SharedForest.Signature.rho := by
  intro A cache rho output sig h
  unfold payAfterDigest signFromOutput at h
  simp only [SigGolfCandidate.T3M.eval_map, evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.FtsBankSpecL
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

theorem payloadRecord_factor {P Sig : Type} [Fintype P] [SampleableType P]
    (S : FtsBankSpecL P) (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option Sig))
    (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord pay cache message = (do
      let rho ← privateNonce message
      let found ← S.search rho message 0 S.limit
      match found with
      | none => pure none
      | some (_,output) => pay cache rho output) := by
  unfold FtsBankSpecL.payloadRecord FtsBankSpecL.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind,map_pure]
    exact bind_pure _

end ClaudeWCT.Bank.FtsBankSpecL

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem payloadRecord_erasure (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    Prod.fst <$> bankSpec.payloadRecord payAfterDigest cache message =
      SharedForest.signPayload cache message := by
  rw [FtsBankSpecL.payloadRecord_factor, signPayload_factor]
  apply bind_congr
  intro rho
  rw [digestSearch_public]
  rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_pairedBank : DecidableEq T3.Cache := Classical.decEq _

noncomputable def authenticatedSign (published : T3.Cache) (request : Request) :
    M (Option SharedForest.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then SharedForest.signPayload request.cache request.message else pure none

theorem record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> bankSpec.authenticatedRecord payAfterDigest published request =
      authenticatedSign published request := by
  unfold FtsBankSpecL.authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure _ _
  · rfl

noncomputable def recordedSource (published : T3.Cache) : QueryImpl (Interaction' SharedForest.Signature) M
  | .inl input => forwardWorld input
  | .inr request => authenticatedSign published request

theorem source_erasure (published : T3.Cache) :
    bankSpec.source payAfterDigest published = recordedSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact record_erasure published request

theorem recordedExperiment_erasure
    (rest : Digest → T3.Cache → OracleComp (Interaction' SharedForest.Signature) Bool) :
    bankSpec.recordedExperiment payAfterDigest rest = (do
      let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
      (liftM (QueryRecorded.run (simulateQ (recordedSource generated.1.2)
        (rest generated.1.1 generated.1.2)) generated.2) : PMF _)) := by
  unfold FtsBankSpecL.recordedExperiment
  simp_rw [source_erasure]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def NotNonce : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inr (.inr (.inl _))=>False
  | _=>True

theorem notDN_of_marker_notNonce (q : SigGolfCandidate.T3.Spec.Domain)
    (hmark : BPB.NotDigestQ q) (hnonce : NotNonce q) : BPair.NotDN q := by
  rcases q with (n|x)|(tweak|(m|region))
  · trivial
  · intro hx
    obtain ⟨rho,m,c,rfl⟩:=BPair.mem_digestInputs.mp hx
    exact hmark (BPB.hdrMarker_digestInput rho m c)
  · trivial
  · exact hnonce.elim
  · trivial

theorem allQ_notDN {α : Type} (program : M α)
    (hmark : AllQueriesSatisfy program BPB.NotDigestQ)
    (hnonce : AllQueriesSatisfy program NotNonce) : AllQueriesSatisfy program BPair.NotDN := by
  induction program using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind q next ih =>
      obtain ⟨hm,hms⟩:=(allQueriesSatisfy_query_bind_iff _ _ _).mp hmark
      obtain ⟨hn,hns⟩:=(allQueriesSatisfy_query_bind_iff _ _ _).mp hnonce
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr
        ⟨notDN_of_marker_notNonce q hm hn,fun a=>ih a (hms a) (hns a)⟩

theorem forest_notNonce : ForestAllowed NotNonce :=
  forest_public NotNonce (fun _=>trivial) (fun _=>trivial)

theorem forest_notDN : ForestAllowed BPair.NotDN where
  coefs := fun index coord=>allQ_notDN _ (forest_notDigest.coefs index coord) (forest_notNonce.coefs index coord)
  child := fun heap index coord selected word coefs pad=>allQ_notDN _
    (forest_notDigest.child heap index coord selected word coefs pad)
    (forest_notNonce.child heap index coord selected word coefs pad)
  node := fun first coord index heap pads left right=>allQ_notDN _
    (forest_notDigest.node first coord index heap pads left right) (forest_notNonce.node first coord index heap pads left right)

theorem buildForest_notDN (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (buildForest index selected words) BPair.NotDN :=
  forest_allowed BPair.NotDN forest_notDN index selected words

end ClaudeWCT.Bank.Paired
