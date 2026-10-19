import SigGolfCandidate.ClaudeWCT_Bank_WCTRev3
import SigGolfCandidate.ClaudeWCT_W9_T3M_Extract_Wct
import SigGolfCandidate.Research_V7Composed198Gate
import SigGolfCandidate.ClaudeWCT_W9_New_CanonTable_ChainTable
import SigGolfCandidate.ClaudeWCT_WCT9_Codebook
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_CaseCSplit
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_ExpandLink_Link

section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
/-- Private cells holding FTS family coefficients (campaign X1: the hidden FTS secrets). -/
def IsSeedPair (c : Coordinate) : Prop :=
  ∃ cf : CanonGraph.WctCoef, c = .inl (WCT9.ftsSeedHeader cf.2.1.val cf.1.val (cf.2.2.val / 2))
def WFree : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr x) => Guess.decodeProbe x = none
  | .inr c => ¬IsSeedPair c
theorem not_isSeedPair_header {t l tr p ix : Nat} (ht : t % 256 ≠ 8) : ¬IsSeedPair (.inl (header t l tr p ix)) := by
  rintro ⟨a, ha⟩
  exact SigGolfCandidate.T3.QuerySpace.header_ne_of_tag (by omega) (Sum.inl.inj ha)
theorem hdrBlock_pad64_prefix (a : Digest) (h : BitVec 128) (rest : HashInput) :
    Guess.hdrBlock (pad64 (bytesLE 16 a ++ bytesLE 16 h ++ rest)) = bytesLE 16 h := by
  unfold Guess.hdrBlock pad64
  rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length _ _), List.take_left' (bytesLE_length _ _)]
theorem decodeProbe_prefix (a : Digest) {h : BitVec 128} (rest : HashInput) (ht : h.toNat % 256 < 128) :
    Guess.decodeProbe (pad64 (bytesLE 16 a ++ bytesLE 16 h ++ rest)) = none :=
  Guess.decodeProbe_of_hdrBlock (hdrBlock_pad64_prefix a h rest) ht
theorem firstByte_header (t l tr p ix : Nat) : (header t l tr p ix).toNat % 256 < 128 := by
  rw [header_firstByte]; decide
theorem eval_query' (A : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    evalWithAnswerFn A (liftM (SigGolfCandidate.T3.Spec.query input)) = A input :=
  simulateQ_spec_query A input
theorem eval_congr_allowed {P : SigGolfCandidate.T3.Spec.Domain → Prop} {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program P) {A A' : Answers} (h : ∀ q, P q → A q = A' q) :
    evalWithAnswerFn A program = evalWithAnswerFn A' program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_query', eval_query', h input hi]
      exact ih _ (hn _)
section Free
open SourceQueries
theorem zero16_eq : zero16 = bytesLE 16 (0 : Digest) := by decide
theorem shortHash_free (a : Digest) {h : BitVec 128} (rest : HashInput) (ht : h.toNat % 256 < 128) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 h ++ rest)) WFree := by
  unfold shortHash publicHash
  exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr (decodeProbe_prefix a rest ht))
    fun _ => pure_allowed _ _
/-- C4 (adapted from b3cc11b's `decodeProbe_of_hdrBlock_low`): a header whose low word is below `2 ^ 16` is never an
FTS chain probe, because every FTS chain word is at least `2 ^ 16` (coordinate nibble `coord + 1`). -/
theorem decodeProbe_of_hdrBlock_low {x : HashInput} {h : BitVec 128} (hx : Guess.hdrBlock x = bytesLE 16 h)
    (ht : h.toNat % 2 ^ 64 < 2 ^ 16) : Guess.decodeProbe x = none := by
  rw [Guess.decodeProbe_eq_none]
  intro a p c he
  rw [he, Guess.hdrBlock_probeInput] at hx
  have hh := bytesLE_injective hx
  have hb := WCT9.ftsChainLow_ge (show a.2.1.val < 15 by have := a.2.1.isLt; omega)
    a.1.val a.2.2.1.val a.2.2.2.val p.val
  have hl := WCT9.ftsChainLow_lt a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p.val
  rw [← hh, WCT9.ftsChainHeader_toNat, Nat.mod_eq_of_lt (by omega)] at ht
  omega
/-- C4: a header is probe-safe when its byte0 is below 128, its byte1 is at least 4, or (top fold labels) its low word
is below `2 ^ 16`. -/
theorem shortHash_free' (a : Digest) {h : BitVec 128} (rest : HashInput)
    (ht : h.toNat % 256 < 128 ∨ 4 ≤ h.toNat / 256 % 256 ∨ h.toNat % 2 ^ 64 < 2 ^ 16) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 h ++ rest)) WFree := by
  rcases ht with ht | ht | ht
  · exact shortHash_free a rest ht
  · unfold shortHash publicHash
    exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr
      (Guess.decodeProbe_of_hdrBlock_tag (hdrBlock_pad64_prefix a h rest) ht)) fun _ => pure_allowed _ _
  · unfold shortHash publicHash
    exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr
      (decodeProbe_of_hdrBlock_low (hdrBlock_pad64_prefix a h rest) ht)) fun _ => pure_allowed _ _
/-- C4: `shortHash_free'` for a hash keeping either half. -/
theorem projHash_free' (high : Bool) (a : Digest) {h : BitVec 128} (rest : HashInput)
    (ht : h.toNat % 256 < 128 ∨ 4 ≤ h.toNat / 256 % 256 ∨ h.toNat % 2 ^ 64 < 2 ^ 16) :
    AllQueriesSatisfy (projHash high (bytesLE 16 a ++ bytesLE 16 h ++ rest)) WFree := by
  have hs := shortHash_free' a rest ht
  unfold shortHash publicHash at hs
  have hq := ((allQueriesSatisfy_query_bind_iff _ _ _).mp hs).1
  unfold projHash publicHash
  exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr hq) fun _ => pure_allowed _ _
/-- C4 (b3cc11b's `nodeTweak_probe_safeS`): every node tweak is probe-safe; the top labels by their low word
`topNodeWord heap < 4096`. -/
theorem nodeTweak_probe_safeS (tag lay tree heap : Nat) :
    (nodeTweak tag lay tree heap).toNat % 256 < 128 ∨ 4 ≤ (nodeTweak tag lay tree heap).toNat / 256 % 256 ∨
      (nodeTweak tag lay tree heap).toNat % 2 ^ 64 < 2 ^ 16 := by
  by_cases ht : tag = 3 ∧ lay = 0
  · obtain ⟨rfl, rfl⟩ := ht
    right; right
    have hl := nodeTweak_top_low tree heap
    have := topNodeWord_lt heap
    unfold tweakLow at hl
    omega
  · have := nodeTweak_probe_safe ht tree heap
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
theorem shortHash_header_free (a : Digest) (t l tr p ix : Nat) (rest : HashInput) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) WFree :=
  shortHash_free a rest (firstByte_header t l tr p ix)
theorem privatePair_free {t : Nat} (l tr p ix : Nat) (ht : t % 256 ≠ 8) :
    AllQueriesSatisfy (privatePair t l tr p ix) WFree := by
  unfold privatePair privateHash
  exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr (not_isSeedPair_header ht))
    fun _ => pure_allowed _ _
theorem privateNonce_free (message : Message) : AllQueriesSatisfy (privateNonce message) WFree := by
  unfold privateNonce privateHash
  refine bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr ?_) fun _ => pure_allowed _ _
  rintro ⟨a, ha⟩
  cases ha
theorem privateMac_free (region : Region) : AllQueriesSatisfy (privateMac region) WFree := by
  have hquery (i : Nat) : AllQueriesSatisfy (privateHash (.inl (header 14 0 0 0 i))) WFree := by
    exact (allQueriesSatisfy_query_iff _ _).mpr (not_isSeedPair_header (by decide : 14 % 256 ≠ 8))
  unfold privateMac privateMacKey
  apply bind_allowed WFree
  · exact bind_allowed WFree (hquery 0) (fun _ => bind_allowed WFree (hquery 1) (fun _ => pure_allowed _ _))
  · intro key; exact pure_allowed _ _
theorem chainStep_free (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (chainInput lay tree leaf i step value)) WFree := by
  unfold shortHash publicHash
  apply bind_allowed WFree
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change Guess.decodeProbe (pad64 (chainInput lay tree leaf i step value)) = none
    rw [Guess.decodeProbe_eq_none, chainInput_padded]
    intro a p c he
    have hx := congrArg Guess.hdrBlock he
    rw [Guess.hdrBlock_probeInput] at hx
    change ((chainInput lay tree leaf i step value).drop 16).take 16 = _ at hx
    rw [chainInput_header] at hx
    exact WCT9.ftsChainHeaderP_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _ (bytesLE_injective hx).symm
  · intro _; exact pure_allowed _ _
theorem chainStepW_free (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) WFree := by
  unfold shortHash publicHash
  apply bind_allowed WFree
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change Guess.decodeProbe (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) = none
    rw [Guess.decodeProbe_eq_none, ClaudeWCT.WCT9.chainInputW_padded]
    intro a p c he
    have hx := congrArg Guess.hdrBlock he
    rw [Guess.hdrBlock_probeInput] at hx
    change ((ClaudeWCT.WCT9.chainInputW lay tree leaf i step value).drop 16).take 16 = _ at hx
    rw [ClaudeWCT.WCT9.chainInputW_header] at hx
    exact WCT9.ftsChainHeaderP_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _ (bytesLE_injective hx).symm
  · intro _; exact pure_allowed _ _
theorem chain_free (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) WFree := by
  unfold chain
  exact foldlM_allowed WFree _ _ (fun v step => chainStep_free lay tree leaf i step v) value
/-- Witness stack: the top chain is `chainW 0 0` (G for even i ≤ 52). -/
theorem topChain_free (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (topChain leaf i start count value) WFree := by
  rw [← WCT9.chainW_top_eq]
  exact Signer.chainW_allowed_of_chain WFree chainStepW_free _ _ _ _ _ _ _
theorem leafHash_free (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) WFree := by
  unfold leafHash projHash publicHash
  apply bind_allowed WFree
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change Guess.decodeProbe (pad64 (leafInput lay tree leaf ends)) = none
    exact Guess.decodeProbe_of_hdrBlock (ClaudeWCT.W9.T3M.Extract.hdrBlock_leafInput lay tree leaf ends)
      (by have := leafTweak_marker lay tree leaf; unfold tweakMarker at this; omega)
  · intro _; exact pure_allowed _ _
theorem nodeHash_free (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) WFree := by
  unfold nodeHash
  rw [List.append_assoc]
  exact projHash_free' _ _ _ (nodeTweak_probe_safeS tag lay tree heap)
theorem mask_free (level index : Nat) : AllQueriesSatisfy (mask level index) WFree := by
  unfold mask pairedMask
  exact bind_allowed WFree (privatePair_free _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem buildLeaf_free (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) WFree := by
  unfold buildLeaf
  apply bind_allowed WFree
  · apply foldlM_allowed WFree
    intro state pair
    apply bind_allowed WFree (privatePair_free _ _ _ _ (by decide))
    intro seeds
    apply foldlM_allowed WFree
    intro state half
    dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed WFree (chain_free _ _ _ _ _ _ _)
      intro value
      split
      · exact pure_allowed _ _
      · exact bind_allowed WFree (chain_free _ _ _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed WFree (leafHash_free _ _ _ _) fun _ => pure_allowed _ _
theorem buildLevel_free (tag lay tree h level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) WFree := by
  unfold buildLevel
  exact mapM_allowed WFree _ _ fun _ => nodeHash_free _ _ _ _ _ _
theorem buildLevels_free (tag lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) WFree := by
  unfold buildLevels
  exact foldlM_allowed WFree _ _ (fun levels level =>
    bind_allowed WFree (buildLevel_free _ _ _ _ _ _) fun _ => pure_allowed _ _) _
theorem buildTree_free (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) WFree := by
  unfold buildTree
  apply bind_allowed WFree
  · exact foldlM_allowed WFree _ _ (fun state leaf =>
      bind_allowed WFree (buildLeaf_free _ _ _ _ _) fun _ => pure_allowed _ _) _
  · intro state
    exact bind_allowed WFree (buildLevels_free _ _ _ _ _) fun _ => pure_allowed _ _
theorem packedSecret_free (lay : Layer) (tree q : Nat) (carry : Digest) :
    AllQueriesSatisfy (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry) WFree := by
  unfold WCT9.packedSecret WCT9.lowerSeedPair
  split
  · exact bind_allowed WFree (privatePair_free _ _ _ _ (by decide)) fun _ => pure_allowed _ _
  · exact pure_allowed _ _
theorem buildLeafP_free (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    AllQueriesSatisfy (WCT9.buildLeafP lay tree leaf digits carry) WFree := by
  unfold WCT9.buildLeafP
  apply bind_allowed WFree
  · apply foldlM_allowed WFree
    intro state i
    apply bind_allowed WFree (packedSecret_free _ _ _ _)
    intro sc
    exact bind_allowed WFree (chain_free _ _ _ _ _ _ _) fun _ =>
      bind_allowed WFree (chain_free _ _ _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    exact bind_allowed WFree (leafHash_free _ _ _ _) fun _ => pure_allowed _ _
/-- C2 (FULL): a lower-tree node hash (packed node word: marked, byte1 7) is never an FTS probe. -/
theorem lowerNodeHash_free (lay : Layer) (tree heap : Nat) (left right : Digest) (hh : heap < 2 ^ height lay) :
    AllQueriesSatisfy (WCT9.lowerNodeHash lay.val tree heap left right) WFree := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  apply Signer.halfHash_allowed_of_short
  unfold WCT9.merkleNodeInput
  rw [List.append_assoc]
  apply shortHash_free'
  by_cases h0 : lay.val = 0
  · rw [h0, WCT9.merkleTweak_top]; exact nodeTweak_probe_safeS 3 0 tree heap
  · rw [WCT9.merkleTweak_lower h0]
    right; left
    have h7 : height lay ≤ 7 := by fin_cases lay <;> simp_all [height]
    have h128 : heap < 128 := lt_of_lt_of_le hh (le_trans (Nat.pow_le_pow_right (by decide) h7) (by norm_num))
    have := WCT9.lowerTweak_tag h128 lay.val tree
    unfold tweakTag at this
    omega
theorem lowerSeedPair_free (lay : Layer) (tree pair : Nat) :
    AllQueriesSatisfy (WCT9.lowerSeedPair lay tree pair) WFree := by
  unfold WCT9.lowerSeedPair
  exact privatePair_free _ _ _ _ (by decide)
theorem buildTreeP_free (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) WFree :=
  Signer.buildTreeP_allowed' WFree chainStepW_free leafHash_free (fun lay tree heap left right hh =>
    lowerNodeHash_free lay tree heap left right hh) lowerSeedPair_free lay tree selected digits
theorem maskedLevel_free (nodes : List Digest) (level : Nat) :
    AllQueriesSatisfy (maskedLevel nodes level) WFree := by
  unfold maskedLevel pairedMask
  apply bind_allowed WFree
  · exact mapM_allowed WFree _ _ (fun pair => bind_allowed WFree (privatePair_free _ _ _ _ (by decide))
      (fun _ => pure_allowed _ _))
  · intro _; exact pure_allowed _ _
/-- img-v6 top family coefficients (r3-lean-nonsec port): pairs from `topPairsFrom`. -/
theorem topPairsFrom_free (first start : Nat) (init : List Digest) :
    AllQueriesSatisfy (topPairsFrom first start init) WFree := by
  unfold topPairsFrom topSeedPair
  exact foldlM_allowed WFree _ _ (fun _ _ => bind_allowed WFree (privatePair_free _ _ _ _ (by decide))
    fun _ => pure_allowed _ _) _
theorem buildLeafTopC_free (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTopC leaf coefs digits signatureOnly) WFree := by
  unfold buildLeafTopC
  apply bind_allowed WFree
  · apply foldlM_allowed WFree
    intro state i
    apply bind_allowed WFree (topChain_free _ _ _ _ _)
    intro value
    split
    · exact pure_allowed _ _
    · exact bind_allowed WFree (topChain_free _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed WFree (leafHash_free _ _ _ _) fun _ => pure_allowed _ _
/-- Top-nonce layer: a keygen nonce trial is a node input with the top node tweak. -/
theorem topNodeHashN_free (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeHashN heap n left right) WFree := by
  unfold topNodeHashN topNodeInput
  rw [List.append_assoc]
  exact projHash_free' _ _ _ (nodeTweak_probe_safeS 3 0 0 heap)
theorem topNonceSearch_free (h heap : Nat) (left right : Digest) :
    ∀ fuel n, AllQueriesSatisfy (topNonceSearch h heap left right fuel n) WFree
  | 0, n => by
      unfold topNonceSearch
      exact bind_allowed WFree (topNodeHashN_free _ _ _ _) fun _ => pure_allowed _ _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine bind_allowed WFree (topNodeHashN_free _ _ _ _) fun _ => ?_
      split
      · exact pure_allowed _ _
      · exact topNonceSearch_free h heap left right fuel (n + 1)
theorem buildTopLevels_free (leaves : List Digest) : AllQueriesSatisfy (buildTopLevels leaves) WFree := by
  unfold buildTopLevels
  refine foldlM_allowed WFree _ _ (fun levels level => bind_allowed WFree ?_ fun _ => pure_allowed _ _) _
  unfold buildTopLevel
  refine mapM_allowed WFree _ _ fun i => ?_
  split
  · exact nodeHash_free _ _ _ _ _ _
  · unfold topNodeAt
    rw [map_eq_bind_pure_comp]
    exact bind_allowed WFree (topNonceSearch_free _ _ _ _ _ _) fun _ => pure_allowed _ _
theorem buildLeafTop_free (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTop leaf digits signatureOnly) WFree := by
  unfold buildLeafTop
  apply bind_allowed WFree
  · unfold topCoefs
    exact bind_allowed WFree (topPairsFrom_free _ _ _) fun _ => pure_allowed _ _
  · intro coefs
    apply bind_allowed WFree
    · apply foldlM_allowed WFree
      intro state i
      apply bind_allowed WFree (topChain_free _ _ _ _ _)
      intro value
      split
      · exact pure_allowed _ _
      · exact bind_allowed WFree (topChain_free _ _ _ _ _) fun _ => pure_allowed _ _
    · intro state
      split
      · exact pure_allowed _ _
      · exact bind_allowed WFree (leafHash_free _ _ _ _) fun _ => pure_allowed _ _
theorem buildTopTree_free : AllQueriesSatisfy buildTopTree WFree := by
  unfold buildTopTree
  apply bind_allowed WFree
  · refine foldlM_allowed WFree _ _ (fun st leaf => ?_) _
    unfold topTreeStep topFamilyCoefs
    apply bind_allowed WFree
    · split
      · unfold topCoefsK
        exact bind_allowed WFree (topPairsFrom_free _ _ _) fun _ => pure_allowed _ _
      · exact pure_allowed _ _
    · intro cc
      exact bind_allowed WFree (buildLeafTopC_free _ _ _ _) fun _ => pure_allowed _ _
  · intro roots
    exact buildTopLevels_free _
theorem keygenPayload_free : AllQueriesSatisfy keygenPayload WFree := by
  unfold keygenPayload
  apply bind_allowed WFree buildTopTree_free
  intro built
  apply bind_allowed WFree
  · exact mapM_allowed WFree _ _ (fun level => maskedLevel_free _ _)
  · intro _
    exact pure_allowed _ _
theorem keygen_free : AllQueriesSatisfy keygen WFree := by
  unfold keygen
  apply bind_allowed WFree keygenPayload_free
  intro generated
  exact bind_allowed WFree (privateMac_free _) fun _ => pure_allowed _ _
theorem counterSearch_free (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) WFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold counterSearch
      apply bind_allowed WFree
      · unfold encodingInput
        exact shortHash_free _ _ (by have := rowTweak_marker lay tree leaf; unfold tweakMarker at this; omega)
      · intro answer
        split
        · exact ih _
        · exact pure_allowed _ _
theorem digest_free (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) WFree := by
  unfold digest publicHash digestInput
  exact (allQueriesSatisfy_query_iff _ _).mpr
    (decodeProbe_prefix _ _ (by rw [digestHeader_firstByte]; decide))
theorem wctDigestSearch_free (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.digestSearch rho message counter fuel) WFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold WCT9.digestSearch
      apply bind_allowed WFree (digest_free _ _ _)
      intro output
      split
      · exact pure_allowed _ _
      · exact ih _
theorem topPath_free (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) WFree := by
  unfold topPath
  exact mapM_allowed WFree _ _ fun level =>
    bind_allowed WFree (mask_free _ _) fun _ => pure_allowed _ _
theorem signTop_free (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) WFree := by
  unfold signTop
  exact bind_allowed WFree (buildLeafTop_free _ _ _) fun _ =>
    bind_allowed WFree (topPath_free _ _) fun _ => pure_allowed _ _
/-- img-v6: the counter search queries the encoding row through `publicHash`. -/
theorem layerEncodingPublic_free (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    AllQueriesSatisfy (publicHash (WCT9.layerEncodingInput lay tree leaf msg counter)) WFree := by
  unfold publicHash
  apply (allQueriesSatisfy_query_iff _ _).mpr
  change Guess.decodeProbe (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) = none
  exact Guess.decodeProbe_of_hdrBlock (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInput lay tree leaf msg counter)
    (by have := rowTweak_marker lay tree leaf; unfold tweakMarker at this; omega)
theorem layerEncoding_free (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) WFree := by
  rw [ClaudeWCT.WCT9.allQueries_encodingHash_iff]
  unfold shortHash publicHash
  apply bind_allowed WFree
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change Guess.decodeProbe (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) = none
    exact Guess.decodeProbe_of_hdrBlock (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInput lay tree leaf msg counter)
      (by have := rowTweak_marker lay tree leaf; unfold tweakMarker at this; omega)
  · intro _; exact pure_allowed _ _
theorem signLayersBC_free (cache : SigGolfCandidate.T3.Cache) (index n : Nat) (msg : WCT9.LayerMsg) :
    AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) WFree :=
  Signer.signLayersBC_allowed' WFree cache layerEncoding_free buildTreeP_free (signTop_free cache) index n msg
theorem wctLeafHash_free (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) WFree := by
  unfold WCT9.leafHash
  exact shortHash_free _ _ (by rw [WCT9.ftsLeafHeader_firstByte]; decide)
theorem wctForestPk_free (index : Nat) (pairs : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index pairs) WFree := by
  unfold WCT9.forestPk WCT9.forestInput
  rw [zero16_eq]
  exact shortHash_header_free _ _ _ _ _ _ _
theorem wctLeafHashP_free (index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashP index coord selected pad ends) WFree := by
  unfold WCT9.leafHashP WCT9.leafInputP
  rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _) (bytesLE 16 pad)]
  exact shortHash_free _ _ (by rw [WCT9.ftsLeafHeader_firstByte]; decide)
theorem highHash_free' (a : Digest) {h : BitVec 128} (rest : HashInput)
    (ht : h.toNat % 256 < 128 ∨ 4 ≤ h.toNat / 256 % 256) :
    AllQueriesSatisfy (WCT9.highHash (bytesLE 16 a ++ bytesLE 16 h ++ rest)) WFree := by
  unfold WCT9.highHash publicHash
  rcases ht with ht | ht
  · exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr (decodeProbe_prefix a rest ht))
      fun _ => pure_allowed _ _
  · exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr
      (Guess.decodeProbe_of_hdrBlock_tag (hdrBlock_pad64_prefix a h rest) ht)) fun _ => pure_allowed _ _
/-- C1: the paired leaf of heap `heap` (either half) makes only a free query. -/
theorem wctLeafHashH_free (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashH heap index coord selected pad ends) WFree := by
  unfold WCT9.leafHashH WCT9.leafInputP
  rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _) (bytesLE 16 pad), WCT9.ftsHash_eq]
  split
  · exact highHash_free' _ _ (Or.inl (by rw [WCT9.ftsLeafHeader_firstByte]; decide))
  · exact shortHash_free _ _ (by rw [WCT9.ftsLeafHeader_firstByte]; decide)
theorem wctTopHash_free (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (WCT9.wctTopHash coord index heap left pad right) WFree := by
  unfold WCT9.wctTopHash WCT9.wctTopInput WCT9.wctNodeHeader
  rw [List.append_assoc (bytesLE 16 left ++ bytesLE 16 _) (bytesLE 16 pad)]
  exact highHash_free' _ _ (nodeTweak_probe_safe (by unfold WCT9.nodeLayer; omega) index heap)
theorem wctHeapNode_free (coord index heap : Nat) (padR left right : Digest) :
    AllQueriesSatisfy (WCT9.wctHeapNode coord index heap padR left right) WFree := by
  unfold WCT9.wctHeapNode
  split
  · exact wctTopHash_free _ _ _ _ _ _
  · exact nodeHash_free _ _ _ _ _ _
theorem heapBuild_free (index coord : Nat) (padR : Digest) (leaves : List Digest) :
    AllQueriesSatisfy (WCT9.heapBuild index coord padR leaves) WFree := by
  unfold WCT9.heapBuild
  exact foldlM_allowed WFree _ _ (fun nodes heap =>
    bind_allowed WFree (wctHeapNode_free _ _ _ _ _ _) fun _ => pure_allowed _ _) _
end Free
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
open ClaudeWCT.W9.T3.Security.CanonGraph
theorem splitEquiv_symm_secret (s : Secrets) (o : OtherHalves) (i : SecretIndex) :
    splitEquiv.symm (s, o) (secretCoordinate i) = s i := by
  have h := splitEquiv_fst (splitEquiv.symm (s, o))
  rw [Equiv.apply_symm_apply] at h
  exact (congrFun h i).symm
theorem splitEquiv_snd (t : ChainGraph.HalfTable) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range secretCoordinate) : (splitEquiv t).2 ⟨h, hh⟩ = t h := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.Set.sumCompl]
  rfl
theorem splitEquiv_symm_other (s : Secrets) (o : OtherHalves) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range secretCoordinate) : splitEquiv.symm (s, o) h = o ⟨h, hh⟩ := by
  have e := splitEquiv_snd (splitEquiv.symm (s, o)) h hh
  rw [Equiv.apply_symm_apply] at e
  exact e.symm
theorem privateEquiv_symm_apply (s : Secrets) (o : OtherHalves) (c : Coordinate) :
    privateEquiv.symm (s, o) c =
      ChainGraph.joinOutput (splitEquiv.symm (s, o) (c, 0)) (splitEquiv.symm (s, o) (c, 1)) :=
  rfl
theorem private_free (g g' : CanonTable.HiddenF) (c : Coordinate) (hc : ¬IsSeedPair c) :
    privateEquiv.symm (CanonTable.worldSecrets ω.secrets g.1, ω.other) c =
      privateEquiv.symm (CanonTable.worldSecrets ω.secrets g'.1, ω.other) c := by
  have hhalf : ∀ h : Fin 2, splitEquiv.symm (CanonTable.worldSecrets ω.secrets g.1, ω.other) (c, h) =
      splitEquiv.symm (CanonTable.worldSecrets ω.secrets g'.1, ω.other) (c, h) := by
    intro h
    by_cases hr : (c, h) ∈ Set.range secretCoordinate
    · obtain ⟨i, hi⟩ := hr
      rw [← hi, splitEquiv_symm_secret, splitEquiv_symm_secret]
      cases i with
      | inl a => rw [CanonTable.worldSecrets_inl, CanonTable.worldSecrets_inl]
      | inr a =>
          exfalso
          apply hc
          exact ⟨a, (congrArg Prod.fst hi).symm⟩
    · rw [splitEquiv_symm_other _ _ _ hr, splitEquiv_symm_other _ _ _ hr]
  rw [privateEquiv_symm_apply, privateEquiv_symm_apply, hhalf 0, hhalf 1]
theorem answers_free (g g' : CanonTable.HiddenF) (q : SigGolfCandidate.T3.Spec.Domain) (hq : WFree q) :
    CanonTable.worldAnswers hU ω g q = CanonTable.worldAnswers hU ω g' q := by
  rcases q with (n | x) | c
  · rfl
  · exact (CanonTable.chainTable hU ω).answers_public g g' x hq
  · exact private_free ω g g' c hq
theorem eval_free (g g' : CanonTable.HiddenF) {α : Type} {program : M α} (hp : AllQueriesSatisfy program WFree) :
    evalWithAnswerFn (CanonTable.worldAnswers hU ω g) program =
      evalWithAnswerFn (CanonTable.worldAnswers hU ω g') program :=
  eval_congr_allowed hp (answers_free hU ω g g')
end Table
end ClaudeWCT.W9.T3.Security.WPair
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def outIndex (output : HashOutput) : Nat := WCT9.digestIndex output
def revealedCoords (output : HashOutput) : List Guess.GCoord :=
  (List.finRange 9).flatMap fun k => (List.finRange 6).filterMap fun t =>
    if h : 1 ≤ Guess.deficit output k t then
      some (Guess.chainOf output k t, ⟨4 - Guess.deficit output k t, by omega⟩)
    else none
theorem mem_revealedCoords {output : HashOutput} {c : Guess.GCoord} :
    c ∈ revealedCoords output ↔ ∃ (k : Fin 9) (t : Fin 6), 1 ≤ Guess.deficit output k t ∧
      c.1 = Guess.chainOf output k t ∧ c.2.val = 4 - Guess.deficit output k t := by
  unfold revealedCoords
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨k, t, ht⟩
    split_ifs at ht with h
    · cases ht
      exact ⟨k, t, h, rfl, rfl⟩
  · rintro ⟨k, t, h, h1, h2⟩
    refine ⟨k, t, ?_⟩
    rw [dif_pos h]
    obtain ⟨a, ⟨p, hp⟩⟩ := c
    simp only at h1 h2
    subst h1 h2
    rfl
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable local instance instDecidableEqCache_g6Signer : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable abbrev wA (g : CanonTable.HiddenF) : Answers := CanonTable.worldAnswers hU ω g
def addrOf (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) (j : Fin 128) (t : Fin 6) : Guess.ChainAddr :=
  (⟨index, hindex⟩, k, j, t)
theorem wctChainValue_eq (A : Answers) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) (j : Fin 128)
    (word : WCT9.Rank) (t : Fin 6) :
    WCT9.chainValue A index k.val j.val word t = Guess.chainValue A (addrOf index hindex k j t) (4 - WCT9.wordDigit word t) :=
  rfl
theorem chainEnd_eq (A : Answers) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) (j : Fin 128) (t : Fin 6) :
    WCT9.chainEnd A index k.val j.val t = Guess.chainValue A (addrOf index hindex k j t) 4 :=
  rfl
theorem chainValue_world (g : CanonTable.HiddenF) (a : Guess.ChainAddr) (p : Nat) (hp : p ≤ 4) :
    Guess.chainValue (wA hU ω g) a p = (CanonTable.chainTable hU ω).walkVal g a p :=
  (CanonTable.chainTable hU ω).chainValue_answers g a p hp
theorem walkVal_three (g g' : CanonTable.HiddenF) (a : Guess.ChainAddr) :
    (CanonTable.chainTable hU ω).walkVal g a 4 = (CanonTable.chainTable hU ω).walkVal g' a 4 := by
  simp [Guess.ChainTable.walkVal]
theorem chainEnd_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9)
    (j : Fin 128) (t : Fin 6) :
    WCT9.chainEnd (wA hU ω g) index k.val j.val t = WCT9.chainEnd (wA hU ω g') index k.val j.val t := by
  rw [chainEnd_eq _ index hindex, chainEnd_eq _ index hindex, chainValue_world hU ω g _ 4 le_rfl,
    chainValue_world hU ω g' _ 4 le_rfl, walkVal_three]
theorem childRoot_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9)
    (j : Nat) (hj : j < 128) (pad : Digest) :
    WCT9.childRoot (wA hU ω g) index k.val j pad = WCT9.childRoot (wA hU ω g') index k.val j pad := by
  unfold WCT9.childRoot
  have he : (fun t : Fin 6 => WCT9.chainEnd (wA hU ω g) index k.val j t) =
      (fun t : Fin 6 => WCT9.chainEnd (wA hU ω g') index k.val j t) := by
    funext t
    exact chainEnd_world hU ω g g' index hindex k ⟨j, hj⟩ t
  rw [he]
  exact eval_free hU ω g g' (wctLeafHashP_free _ _ _ _ _)
/-- C1: the paired leaf of heap `heap` does not read the hidden part of the world. -/
theorem childRootH_world (g g' : CanonTable.HiddenF) (heap index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9)
    (j : Nat) (hj : j < 128) (pad : Digest) :
    WCT9.childRootH (wA hU ω g) heap index k.val j pad = WCT9.childRootH (wA hU ω g') heap index k.val j pad := by
  unfold WCT9.childRootH
  have he : (fun t : Fin 6 => WCT9.chainEnd (wA hU ω g) index k.val j t) =
      (fun t : Fin 6 => WCT9.chainEnd (wA hU ω g') index k.val j t) := by
    funext t
    exact chainEnd_world hU ω g g' index hindex k ⟨j, hj⟩ t
  rw [he]
  exact eval_free hU ω g g' (wctLeafHashH_free _ _ _ _ _ _)
theorem coordLeavesWith_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9)
    (pad : Digest) :
    WCT9.coordLeavesWith (wA hU ω g) index k.val pad = WCT9.coordLeavesWith (wA hU ω g') index k.val pad := by
  unfold WCT9.coordLeavesWith
  exact congrArg List.ofFn (funext fun j : Fin 128 => childRoot_world hU ω g g' index hindex k j.val j.isLt pad)
theorem coordNodesWith_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9)
    (prev : Digest × Digest) :
    WCT9.coordNodesWith (wA hU ω g) index k.val prev = WCT9.coordNodesWith (wA hU ω g') index k.val prev := by
  unfold WCT9.coordNodesWith
  rw [coordLeavesWith_world hU ω g g' index hindex k]
  exact eval_free hU ω g g' (heapBuild_free _ _ _ _)
theorem ftsPrev_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) (c : Nat) (hc : c ≤ 9) :
    WCT9.ftsPrev (wA hU ω g) index c = WCT9.ftsPrev (wA hU ω g') index c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    show WCT9.coordPairWith (wA hU ω g) index c (WCT9.ftsPrev (wA hU ω g) index c) =
      WCT9.coordPairWith (wA hU ω g') index c (WCT9.ftsPrev (wA hU ω g') index c)
    rw [ih (by omega)]
    unfold WCT9.coordPairWith
    rw [coordNodesWith_world hU ω g g' index hindex ⟨c, by omega⟩]
theorem coordNodes_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) :
    WCT9.coordNodes (wA hU ω g) index k = WCT9.coordNodes (wA hU ω g') index k := by
  unfold WCT9.coordNodes
  rw [ftsPrev_world hU ω g g' index hindex k.val (by omega)]
  exact coordNodesWith_world hU ω g g' index hindex k _
theorem coordinatePair_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) :
    WCT9.coordinatePair (wA hU ω g) index = WCT9.coordinatePair (wA hU ω g') index := by
  funext k
  unfold WCT9.coordinatePair
  rw [coordNodes_world hU ω g g' index hindex k]
theorem honestForest_world (g g' : CanonTable.HiddenF) (index : Nat) (hindex : index < 2 ^ 31) :
    WCT9.honestTop (wA hU ω g) index = WCT9.honestTop (wA hU ω g') index := by
  unfold WCT9.honestTop
  exact ftsPrev_world hU ω g g' index hindex 9 le_rfl
theorem outIndex_lt (output : HashOutput) : outIndex output < 2 ^ 31 := Nat.mod_lt _ (by positivity)
theorem chainOf_eq_addrOf (output : HashOutput) (k : Fin 9) (t : Fin 6) :
    Guess.chainOf output k t = addrOf (outIndex output) (outIndex_lt output) k (WCT9.child output k) t := rfl
theorem expectedOpening_world (g g' : CanonTable.HiddenF) (output : HashOutput)
    (h : ∀ c ∈ revealedCoords output, Guess.Fam.phi g.1 g.2 c = Guess.Fam.phi g'.1 g'.2 c) (k : Fin 9) :
    WCT9.expectedOpening (wA hU ω g) (outIndex output) output k =
      WCT9.expectedOpening (wA hU ω g') (outIndex output) output k := by
  unfold WCT9.expectedOpening
  rw [WCT9.buildCoordinateF_result, WCT9.buildCoordinateF_result,
    coordNodes_world hU ω g g' (outIndex output) (outIndex_lt output) k]
  congr 3
  funext t
  rw [wctChainValue_eq _ _ (outIndex_lt output), wctChainValue_eq _ _ (outIndex_lt output),
    chainValue_world hU ω g _ _ (by omega), chainValue_world hU ω g' _ _ (by omega)]
  unfold Guess.ChainTable.walkVal
  by_cases hd : 1 ≤ WCT9.wordDigit (WCT9.rank output k) t
  · have hlt : 4 - WCT9.wordDigit (WCT9.rank output k) t < 4 := by omega
    rw [dif_pos hlt, dif_pos hlt]
    apply h
    rw [mem_revealedCoords]
    exact ⟨k, t, hd, rfl, rfl⟩
  · have hlt : ¬4 - WCT9.wordDigit (WCT9.rank output k) t < 4 := by omega
    rw [dif_neg hlt, dif_neg hlt]
noncomputable def signerCore (published : SigGolfCandidate.T3.Cache) (request : Request) :
    Option (Digest × HashOutput × List Pieces) :=
  if request.cache = published then
    match evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch (evalWithAnswerFn (wA hU ω 0)
        (privateNonce request.message)) request.message 0 WCT9.digestAttemptLimit) with
    | none => none
    | some (_, output) =>
        match evalWithAnswerFn (wA hU ω 0) (WCT9.signLayersBC request.cache (WCT9.digestIndex output) 4
            (.pair (WCT9.honestTop (wA hU ω 0) (WCT9.digestIndex output)).1 (WCT9.honestTop (wA hU ω 0) (WCT9.digestIndex output)).2)) with
        | none => none
        | some pieces => some (evalWithAnswerFn (wA hU ω 0) (privateNonce request.message), output, pieces)
  else none
def assembleWith (A : Answers) (core : Digest × HashOutput × List Pieces) : Signature :=
  WCT9.assembledSignature core.1 (List.ofFn (WCT9.expectedOpening A (outIndex core.2.1) core.2.1)) core.2.2
theorem eval_privateMac_bind (A : Answers) (region : Region) {β : Type} (next : M β) :
    evalWithAnswerFn A (privateMac region >>= fun _ => next) = evalWithAnswerFn A next := by
  rw [evalWithAnswerFn_bind]
theorem sign_answers (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) =
      (signerCore hU ω published request).map (assembleWith (wA hU ω g)) := by
  unfold FullGame.authenticatedSign signerCore
  rw [eval_privateMac_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    change evalWithAnswerFn (wA hU ω g) (WCT9.Rev3.signPayload request.cache request.message) = _
    rw [WCT9.Rev3.signPayload_eq, evalWithAnswerFn_bind, eval_free hU ω g 0 (privateNonce_free _),
      evalWithAnswerFn_bind, eval_free hU ω g 0 (wctDigestSearch_free _ _ _ _)]
    generalize evalWithAnswerFn (wA hU ω 0) (privateNonce request.message) = rho
    cases evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) with
    | none => rfl
    | some found =>
        obtain ⟨ctr, output⟩ := found
        simp only
        rw [evalWithAnswerFn_bind, WCT9.eval_signForest, evalWithAnswerFn_bind]
        simp only
        rw [honestForest_world hU ω g 0 (WCT9.digestIndex output) (outIndex_lt output),
          eval_free hU ω g 0 (signLayersBC_free _ _ _ _)]
        cases evalWithAnswerFn (wA hU ω 0) (WCT9.signLayersBC request.cache (WCT9.digestIndex output) 4
          (.pair (WCT9.honestTop (wA hU ω 0) (WCT9.digestIndex output)).1 (WCT9.honestTop (wA hU ω 0) (WCT9.digestIndex output)).2)) with
        | none => rfl
        | some pieces => rfl
  · rw [if_neg hc, if_neg hc]
    rfl
noncomputable def openedFor (published : SigGolfCandidate.T3.Cache) (request : Request) : List Guess.GCoord :=
  match signerCore hU ω published request with
  | none => []
  | some core => revealedCoords core.2.1
theorem map_assemble_congr {A A' : Answers} (o : Option (Digest × HashOutput × List Pieces))
    (h : ∀ core, o = some core → assembleWith A core = assembleWith A' core) :
    o.map (assembleWith A) = o.map (assembleWith A') := by
  cases o with
  | none => exact (Option.map_none _).trans (Option.map_none _).symm
  | some core => exact (Option.map_some _ _).trans ((congrArg some (h core rfl)).trans (Option.map_some _ _).symm)
theorem sign_local (g g' : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (h : ∀ c ∈ openedFor hU ω published request, Guess.Fam.phi g.1 g.2 c = Guess.Fam.phi g'.1 g'.2 c) :
    evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) =
      evalWithAnswerFn (wA hU ω g') (FullGame.authenticatedSign published request) := by
  rw [sign_answers, sign_answers]
  apply map_assemble_congr
  intro core hcore
  unfold openedFor at h
  rw [hcore] at h
  exact congrArg (fun l => WCT9.assembledSignature core.1 l core.2.2)
    (congrArg List.ofFn (funext fun k => expectedOpening_world hU ω g g' core.2.1 h k))
theorem signerCore_search {published : SigGolfCandidate.T3.Cache} {request : Request}
    {core : Digest × HashOutput × List Pieces} (h : signerCore hU ω published request = some core) :
    ∃ ctr, evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch core.1 request.message 0 WCT9.digestAttemptLimit) =
      some (ctr, core.2.1) := by
  unfold signerCore at h
  split_ifs at h
  split at h
  · cases h
  · rename_i ctr output hfound
    split at h
    · cases h
    · cases h
      exact ⟨ctr, hfound⟩
theorem signedOutput_world (g : CanonTable.HiddenF) {published : SigGolfCandidate.T3.Cache} {request : Request}
    {core : Digest × HashOutput × List Pieces} (h : signerCore hU ω published request = some core) :
    CaseC.signedOutput (wA hU ω g) request.message (assembleWith (wA hU ω g) core) = some core.2.1 := by
  obtain ⟨ctr, hs⟩ := signerCore_search hU ω h
  unfold CaseC.signedOutput assembleWith
  rw [WCT9.assembledSignature_rho, eval_free hU ω g 0 (wctDigestSearch_free _ _ _ _), hs]
  rfl
theorem sign_opened (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (c : Guess.GCoord) (hc : c ∈ openedFor hU ω published request) :
    ∃ signature output, evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) = some signature ∧
      CaseC.signedOutput (wA hU ω g) request.message signature = some output ∧ c ∈ revealedCoords output := by
  unfold openedFor at hc
  cases hcore : signerCore hU ω published request with
  | none => rw [hcore] at hc; cases hc
  | some core =>
      rw [hcore] at hc
      refine ⟨assembleWith (wA hU ω g) core, core.2.1, ?_, signedOutput_world hU ω g hcore, hc⟩
      rw [sign_answers, hcore]
      rfl
theorem ftsPoint_child_injective (j : Fin 128) : Function.Injective fun t : Fin 6 => WCT9.ftsPoint j.val t.val :=
  fun t t' h => (Guess.Fam.ftsPoint_inj (j := j) (j' := j) h).2
/-- Coefficients whose seeds at the 6 chains of child `j` are `v` (the name is kept from the 7-chain code). -/
noncomputable def interp7 (v : Fin 6 → Digest) (j : Fin 128) : Guess.Fam.Coefs :=
  Classical.choose (ClaudeWCT.Arith.familyEval_surjective (n := 54) (t := 6) (by decide)
    (fun t => WCT9.ftsPoint j.val t.val) (ftsPoint_child_injective j) (fun t => Guess.Fam.ftsPoint_lt j t) v)
theorem interp7_spec (v : Fin 6 → Digest) (j : Fin 128) (t : Fin 6) :
    ClaudeWCT.Arith.familyEval (List.ofFn (interp7 v j)) (WCT9.ftsPoint j.val t.val) = v t :=
  congrFun (Classical.choose_spec (ClaudeWCT.Arith.familyEval_surjective (n := 54) (t := 6) (by decide)
    (fun t => WCT9.ftsPoint j.val t.val) (ftsPoint_child_injective j) (fun t => Guess.Fam.ftsPoint_lt j t) v)) t
/-- A hidden value whose table agrees with `v` on the coordinates revealed by `output`. -/
noncomputable def liftH (v : Guess.GCoord → Digest) (output : HashOutput) : CanonTable.HiddenF :=
  (fun f => if f.1.val = outIndex output then
      interp7 (fun t => v ((f.1, f.2, WCT9.child output f.2, t), 0)) (WCT9.child output f.2) else 0,
    fun l => v (l.1, l.2.succ))
theorem phi_liftH (v : Guess.GCoord → Digest) (output : HashOutput) (c : Guess.GCoord)
    (hc : c ∈ revealedCoords output) : Guess.Fam.phi (liftH v output).1 (liftH v output).2 c = v c := by
  obtain ⟨k, t, -, h1, h2⟩ := mem_revealedCoords.mp hc
  obtain ⟨a, q⟩ := c
  simp only at h1 h2
  subst h1
  by_cases hq : q = 0
  · subst hq
    rw [Guess.Fam.phi_seed]
    have hidx : (Guess.Fam.famOf (Guess.chainOf output k t)).1.val = outIndex output := rfl
    simp only [liftH, Guess.Fam.seedK, hidx, if_true]
    exact interp7_spec _ _ t
  · rw [Guess.Fam.phi_label' _ _ (Guess.chainOf output k t, q) hq]
    simp only [liftH, Fin.succ_pred]
/-- The hidden value used by the world's signer for the disclosed values `v`. -/
noncomputable def liftFor (published : SigGolfCandidate.T3.Cache) (request : Request) (v : Guess.GCoord → Digest) :
    CanonTable.HiddenF :=
  match signerCore hU ω published request with
  | none => 0
  | some core => liftH v core.2.1
theorem phi_liftFor (published : SigGolfCandidate.T3.Cache) (request : Request) (v : Guess.GCoord → Digest)
    (c : Guess.GCoord) (hc : c ∈ openedFor hU ω published request) :
    Guess.Fam.phi (liftFor hU ω published request v).1 (liftFor hU ω published request v).2 c = v c := by
  unfold liftFor
  unfold openedFor at hc
  cases hcore : signerCore hU ω published request with
  | none => rw [hcore] at hc; cases hc
  | some core =>
      rw [hcore] at hc
      exact phi_liftH v core.2.1 c hc
end World
end ClaudeWCT.W9.T3.Security.WPair
end
section
namespace ClaudeWCT.Guess
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.SecretGuessObservation
set_option backward.isDefEq.respectTransparency false
variable {E Memory : Type}
def CovMono (Cov : List E → ChainAddr → ℕ → Prop) : Prop :=
  (∀ l1 l2 a p, Cov l1 a p → Cov (l1 ++ l2) a p) ∧ (∀ l1 l2 a p, Cov l2 a p → Cov (l1 ++ l2) a p)
structure WTracks {H : Type} (T : ChainTable H) (g : H) (Cov : List E → ChainAddr → ℕ → Prop)
    (before after : State GCoord Digest Memory) (log : List E) (entries : List (HashInput × HashOutput)) : Prop where
  probes : after.probes ≤ before.probes + entries.length
  prefixTracks : PrefixTracks (Cov log) before after
  queried : ∀ c ans, (honestProbe (T.answers g) c, ans) ∈ entries → c ∈ after.retired
namespace WTracks
variable {H : Type} {T : ChainTable H} {g : H} {Cov : List E → ChainAddr → ℕ → Prop}
theorem refl (state : State GCoord Digest Memory) : WTracks T g Cov state state [] [] :=
  ⟨by simp, PrefixTracks.refl _ _, fun _ _ h => by cases h⟩
theorem trans (hc : CovMono Cov) {s1 s2 s3 : State GCoord Digest Memory} {l1 l2 : List E}
    {e1 e2 : List (HashInput × HashOutput)} (first : WTracks T g Cov s1 s2 l1 e1)
    (second : WTracks T g Cov s2 s3 l2 e2) : WTracks T g Cov s1 s3 (l1 ++ l2) (e1 ++ e2) := by
  refine ⟨?_, ?_, ?_⟩
  · have := first.probes
    have := second.probes
    simp only [List.length_append]
    omega
  · refine (first.prefixTracks.trans second.prefixTracks).mono ?_
    rintro a p (h | h)
    · exact hc.1 l1 l2 a p h
    · exact hc.2 l1 l2 a p h
  · intro c ans h
    rcases List.mem_append.mp h with h | h
    · exact second.prefixTracks.retired (first.queried c ans h)
    · exact second.queried c ans h
theorem coin {before after : State GCoord Digest Memory} (hg : before.guesses = after.guesses)
    (hr : before.retired = after.retired) (hp : after.probes = before.probes) :
    WTracks T g Cov before after [] [] := by
  refine ⟨by simp [hp], ⟨hg ▸ Finset.Subset.refl _, hr ▸ Finset.Subset.refl _, ?_⟩, fun _ _ h => by cases h⟩
  intro a p h
  left
  rw [hr]
  exact h
theorem of_prefix_false {before after : State GCoord Digest Memory} {log : List E}
    {entries : List (HashInput × HashOutput)} (hp : after.probes ≤ before.probes + entries.length)
    (ht : PrefixTracks (fun _ _ => False) before after)
    (hq : ∀ c ans, (honestProbe (T.answers g) c, ans) ∈ entries → c ∈ after.retired) :
    WTracks T g Cov before after log entries :=
  ⟨hp, ht.mono fun _ _ h => h.elim, hq⟩
theorem hashW {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
    (environment : Environment auxSpec GCoord Digest Memory) (x : HashInput) (state : State GCoord Digest Memory)
    (result : HashOutput × State GCoord Digest Memory)
    (hr : fixedRun environment (T.view g) (T.hashW (auxSpec := auxSpec) x) state result ≠ 0) :
    result.1 = T.answers g (.inl (.inr x)) ∧ WTracks T g Cov state result.2 [] [(x, result.1)] := by
  obtain ⟨h1, h2, h3, h4⟩ := T.fixedRun_hashW environment g x state result hr
  refine ⟨h1, of_prefix_false (by simpa using h3) h2 ?_⟩
  intro c ans h
  rw [List.mem_singleton] at h
  exact h4 c (congrArg Prod.fst h).symm
theorem disclose {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
    (environment : Environment auxSpec GCoord Digest Memory) (cs : List GCoord) (entry : E)
    (hcs : ∀ c ∈ cs, Cov [entry] c.1 c.2.val) (hpos : ∀ l a p p', p ≤ p' → Cov l a p → Cov l a p')
    (state : State GCoord Digest Memory) (result : List Digest × State GCoord Digest Memory)
    (hr : fixedRun environment (T.view g) (discloseAll (auxSpec := auxSpec) cs) state result ≠ 0) :
    result.1 = cs.map (T.view g) ∧ WTracks T g Cov state result.2 [entry] [] := by
  obtain ⟨h1, h2, -, h4⟩ := fixedRun_discloseAll environment (T.view g) cs state result hr
  refine ⟨h1, ⟨by simp [h2], h4.mono ?_, fun _ _ h => by cases h⟩⟩
  rintro a p ⟨c, hc, rfl, hle⟩
  exact hpos _ _ _ _ hle (hcs c hc)
theorem guess {init final : State GCoord Digest Memory} {log : List E} {entries : List (HashInput × HashOutput)}
    (h : WTracks T g Cov init final log entries) (hinit : init.retired = ∅) (c : GCoord)
    (hcov : ¬Cov log c.1 c.2.val) (hentry : ∃ ans, (honestProbe (T.answers g) c, ans) ∈ entries) :
    PrefixIn final.guesses c.1 c.2.val := by
  obtain ⟨ans, he⟩ := hentry
  exact prefixIn_guesses_of_tracks h.prefixTracks hinit (prefixIn_of_mem (h.queried c ans he)) hcov
theorem pair {init final : State GCoord Digest Memory} {log : List E} {entries : List (HashInput × HashOutput)}
    (h : WTracks T g Cov init final log entries) (hinit : init.retired = ∅) (c c' : GCoord) (hne : c.1 ≠ c'.1)
    (hc : ¬Cov log c.1 c.2.val ∧ ∃ ans, (honestProbe (T.answers g) c, ans) ∈ entries)
    (hc' : ¬Cov log c'.1 c'.2.val ∧ ∃ ans, (honestProbe (T.answers g) c', ans) ∈ entries) :
    2 ≤ final.guesses.card :=
  two_le_card_of_prefixIn hne (h.guess hinit c hc.1 hc.2) (h.guess hinit c' hc'.1 hc'.2)
theorem one {init final : State GCoord Digest Memory} {log : List E} {entries : List (HashInput × HashOutput)}
    (h : WTracks T g Cov init final log entries) (hinit : init.retired = ∅) (c : GCoord)
    (hc : ¬Cov log c.1 c.2.val ∧ ∃ ans, (honestProbe (T.answers g) c, ans) ∈ entries) :
    final.guesses.Nonempty :=
  nonempty_of_prefixIn (h.guess hinit c hc.1 hc.2)
end WTracks
end ClaudeWCT.Guess
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
abbrev WSpec := SecretGuessObservation.World unifSpec Guess.GCoord Digest
abbrev WState := SecretGuessObservation.State Guess.GCoord Digest PUnit
noncomputable def coinImpl : QueryImpl unifSpec ProbComp := fun n => liftM (unifSpec.query n)
noncomputable def env : SecretGuessObservation.Environment unifSpec Guess.GCoord Digest PUnit :=
  SecretGuessObservation.environment coinImpl
def init : WState := SecretGuessObservation.initialState PUnit.unit
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp
def overwrite (positions : List Guess.GCoord) (values : List Digest) (c : Guess.GCoord) : Digest :=
  ((positions.zip values).find? (fun pv => decide (pv.1 = c))).elim 0 Prod.snd
theorem overwrite_map (g : Guess.GCoord → Digest) (positions : List Guess.GCoord) (c : Guess.GCoord)
    (hc : c ∈ positions) : overwrite positions (positions.map g) c = g c := by
  induction positions with
  | nil => cases hc
  | cons first rest ih =>
      unfold overwrite
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      by_cases he : first = c
      · subst he
        simp
      · simp only [he, decide_false]
        exact ih (by simpa [Ne.symm he] using List.mem_cons.mp hc |>.resolve_left (Ne.symm he))
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable def hashW (x : HashInput) : OracleComp WSpec HashOutput :=
  (CanonTable.chainTable hU ω).hashW (auxSpec := unifSpec) x
noncomputable def signW (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp WSpec (Option Signature) := do
  let positions := openedFor hU ω published request
  let values ← Guess.discloseAll (auxSpec := unifSpec) (V := Digest) positions
  pure (evalWithAnswerFn (wA hU ω (liftFor hU ω published request (overwrite positions values)))
    (FullGame.authenticatedSign published request))
noncomputable def interactionW (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → OracleComp WSpec (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signW hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
noncomputable def programW {β : Type} : M β → OracleComp WSpec (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))
noncomputable def worldGame (adversary : AdversaryP) :
    OracleComp WSpec (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen
  let interaction ← interactionW hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programW hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
end World
noncomputable def interactionT (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → ProbComp (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let rest ← next (T (.inl (.inr x)))
          pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)
      | .inr request => do
          let rest ← next (evalWithAnswerFn T (FullGame.authenticatedSign published request))
          pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ :: rest.2.1,
            rest.2.2))
noncomputable def pairRun (T : Answers) (adversary : AdversaryP) :
    ProbComp (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn T SigGolfCandidate.T3.keygen
  let interaction ← interactionT T generated.2 (adversary generated.1 generated.2)
  let verdict := GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1)
  pure (evalWithAnswerFn T verdict, interaction.2.1,
    interaction.2.2 ++ Wots.entriesOf T (SourceReplay.queried T verdict))
section Couple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable abbrev fixedW (g : CanonTable.HiddenF) : QueryImpl WSpec ProbComp :=
  SecretGuessObservation.fixedAnswers coinImpl (Guess.Fam.phi g.1 g.2)
theorem keygen_answers (g : CanonTable.HiddenF) :
    evalWithAnswerFn (wA hU ω g) SigGolfCandidate.T3.keygen = evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen :=
  eval_free hU ω g 0 keygen_free
theorem fixed_hashW (g : CanonTable.HiddenF) (x : HashInput) :
    simulateQ (fixedW g) (hashW hU ω x) = pure (wA hU ω g (.inl (.inr x))) :=
  (CanonTable.chainTable hU ω).fixed_hashW coinImpl g x
theorem fixed_signW (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (fixedW g) (signW hU ω published request) =
      pure (evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request)) := by
  unfold signW
  rw [simulateQ_bind, Guess.fixed_discloseAll, pure_bind, simulateQ_pure]
  congr 1
  apply sign_local
  intro c hc
  rw [phi_liftFor hU ω published request _ c hc]
  exact overwrite_map (Guess.Fam.phi g.1 g.2) _ c hc
theorem interactionW_pure (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionW hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionW_coin (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1))) >>= fun coin =>
        interactionW hU ω published (next coin)) := rfl
theorem interactionW_public (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => interactionW hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionW_request (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signW hU ω published request >>= fun signature => interactionW hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programW_pure {β : Type} (value : β) : programW hU ω (pure value : M β) = pure (value, []) := rfl
theorem programW_public {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programW hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => programW hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem interactionT_pure (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionT T published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionT_coin (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin => interactionT T published (next coin)) :=
  rfl
theorem interactionT_public (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (interactionT T published (next (T (.inl (.inr x)))) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)) := rfl
theorem interactionT_request (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (interactionT T published (next (evalWithAnswerFn T (FullGame.authenticatedSign published request))) >>=
        fun rest => pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ ::
          rest.2.1, rest.2.2)) := rfl
theorem fixed_interactionW (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (fixedW g) (interactionW hU ω published program) = interactionT (wA hU ω g) published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionW_pure, interactionT_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin, interactionT_coin, simulateQ_bind, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [interactionW_public, interactionT_public, simulateQ_bind, fixed_hashW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [interactionW_request, interactionT_request, simulateQ_bind, fixed_signW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
theorem fixed_programW (g : CanonTable.HiddenF) {β : Type} (program : M β) (hp : PublicVerdict.Only program) :
    simulateQ (fixedW g) (programW hU ω program) =
      pure (evalWithAnswerFn (wA hU ω g) program,
        Wots.entriesOf (wA hU ω g) (SourceReplay.queried (wA hU ω g) program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [programW_pure, simulateQ_pure]; rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact hi.elim
      · rw [programW_public, simulateQ_bind, fixed_hashW, pure_bind, simulateQ_bind, ih _ (hn _), pure_bind,
          simulateQ_pure, SourceReplay.queried_query_bind, evalWithAnswerFn_bind, eval_query']
        rfl
      · exact hi.elim
theorem simulate_worldGame (g : CanonTable.HiddenF) (adversary : AdversaryP) :
    simulateQ (fixedW g) (worldGame hU ω adversary) = pairRun (wA hU ω g) adversary := by
  unfold worldGame pairRun
  rw [← keygen_answers hU ω g]
  rw [simulateQ_bind, fixed_interactionW]
  apply bind_congr
  intro interaction
  rw [simulateQ_bind, fixed_programW _ _ _ _ (PaddedGame.verdict_public _ _), pure_bind, simulateQ_pure]
theorem fixed_worldGame (g : CanonTable.HiddenF) (adversary : AdversaryP) :
    Prod.fst <$> SecretGuessObservation.fixedRun env (Guess.Fam.phi g.1 g.2) (worldGame hU ω adversary) init =
      𝒮[pairRun (wA hU ω g) adversary] := by
  rw [env, SecretGuessObservation.fixedRun_projection, simulate_worldGame]
end Couple
section Tracking
open SecretGuessObservation (runWith fixedRun fixedImpl afterTrial afterDisclosure)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
def Cov (A : Answers) (log : QueryLog Requests) (a : Guess.ChainAddr) (p : Nat) : Prop := Disclosed A log a p
theorem cov_mono (A : Answers) : Guess.CovMono (Cov A) :=
  ⟨fun l1 l2 a p h => Disclosed.mono_log (fun e he => List.mem_append_left _ he) h,
    fun l1 l2 a p h => Disclosed.mono_log (fun e he => List.mem_append_right _ he) h⟩
abbrev Tracks (g : CanonTable.HiddenF) (before after : WState) (log : QueryLog Requests)
    (entries : List Wots.Entry) : Prop :=
  Guess.WTracks (CanonTable.chainTable hU ω) g (Cov (wA hU ω g)) before after log entries
theorem Tracks.trans' {g : CanonTable.HiddenF} {s1 s2 s3 : WState} {l1 l2 : QueryLog Requests}
    {e1 e2 : List Wots.Entry} (first : Tracks hU ω g s1 s2 l1 e1) (second : Tracks hU ω g s2 s3 l2 e2) :
    Tracks hU ω g s1 s3 (l1 ++ l2) (e1 ++ e2) :=
  Guess.WTracks.trans (cov_mono _) first second
theorem fixedRun_bind_nonzero {First Result : Type} (g : CanonTable.HiddenF) (first : OracleComp WSpec First)
    (next : First → OracleComp WSpec Result) (state : WState) (result : Result × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (first >>= next) state result ≠ 0) :
    ∃ middle, fixedRun env (Guess.Fam.phi g.1 g.2) first state middle ≠ 0 ∧ fixedRun env (Guess.Fam.phi g.1 g.2) (next middle.1) middle.2 result ≠ 0 :=
  Guess.fixedRun_bind_nonzero' env (Guess.Fam.phi g.1 g.2) first next state result hr
theorem fixedRun_pure_nonzero {Result : Type} (g : CanonTable.HiddenF) (value : Result) (state : WState)
    (result : Result × WState) (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (pure value) state result ≠ 0) : result = (value, state) :=
  Guess.fixedRun_pure_nonzero' env (Guess.Fam.phi g.1 g.2) value state result hr
theorem fixed_coin_tracks (g : CanonTable.HiddenF) (n : Nat) (state : WState) (result : Fin (n + 1) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (liftM (WSpec.query (.inl n))) state result ≠ 0) : Tracks hU ω g state result.2 [] [] := by
  unfold fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [fixedImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  exact Guess.WTracks.refl state
theorem fixed_hashW_tracks (g : CanonTable.HiddenF) (x : HashInput) (state : WState) (result : HashOutput × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (hashW hU ω x) state result ≠ 0) :
    result.1 = wA hU ω g (.inl (.inr x)) ∧ Tracks hU ω g state result.2 [] [(x, result.1)] :=
  Guess.WTracks.hashW (T := CanonTable.chainTable hU ω) (g := g) env x state result hr
theorem fixed_signW_tracks (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (state : WState) (result : Option Signature × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (signW hU ω published request) state result ≠ 0) :
    result.1 = evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) ∧
      Tracks hU ω g state result.2 [⟨request, result.1⟩] [] := by
  unfold signW at hr
  obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
  have h := fixedRun_pure_nonzero g _ _ result hr
  subst h
  have hsig : evalWithAnswerFn (wA hU ω (liftFor hU ω published request
        (overwrite (openedFor hU ω published request) middle.1)))
      (FullGame.authenticatedSign published request) =
      evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) := by
    have h1 := (Guess.fixedRun_discloseAll env (Guess.Fam.phi g.1 g.2) (openedFor hU ω published request) state
      middle hm).1
    rw [h1]
    exact sign_local hU ω _ _ published request fun c hc => by
      rw [phi_liftFor hU ω published request _ c hc]
      exact overwrite_map (Guess.Fam.phi g.1 g.2) _ c hc
  refine ⟨hsig, ?_⟩
  have hcov : ∀ c ∈ openedFor hU ω published request,
      Cov (wA hU ω g) [⟨request, evalWithAnswerFn (wA hU ω (liftFor hU ω published request
        (overwrite (openedFor hU ω published request) middle.1)))
        (FullGame.authenticatedSign published request)⟩] c.1 c.2.val := by
    intro c hc
    rw [hsig]
    obtain ⟨signature, output, hs, ho, hrev⟩ := sign_opened hU ω g published request c hc
    obtain ⟨k, t, hu, h1, h2⟩ := mem_revealedCoords.mp hrev
    refine ⟨output, mem_loggedOutputs.mpr ⟨_, List.mem_singleton_self _, signature, hs, ho⟩, ?_, ?_, ?_⟩
    · rw [h1]; rfl
    · rw [h1]; rfl
    · rw [h1, h2]; exact le_rfl
  exact (Guess.WTracks.disclose env (openedFor hU ω published request) _ hcov
    (fun l a p p' hpp' hc => Disclosed.mono_pos hpp' hc) state middle hm).2
theorem interactionW_tracks (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (state : WState)
    (result : (α × QueryLog Requests × List Wots.Entry) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (interactionW hU ω published program) state result ≠ 0) :
    Tracks hU ω g state result.2 result.1.2.1 result.1.2.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [interactionW_pure] at hr
      have h := fixedRun_pure_nonzero g _ state result hr
      subst h
      exact Guess.WTracks.refl state
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        have h := Tracks.trans' hU ω (fixed_coin_tracks hU ω g n state middle hm) (ih middle.1 middle.2 result hr)
        simpa only [List.nil_append] using h
      · rw [interactionW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_hashW_tracks hU ω g x state middle hm).2 (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · rw [interactionW_request] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_signW_tracks hU ω g published request state middle hm).2
          (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
theorem programW_tracks (g : CanonTable.HiddenF) {β : Type} (program : M β) (hp : PublicVerdict.Only program)
    (state : WState) (result : (β × List Wots.Entry) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (programW hU ω program) state result ≠ 0) :
    Tracks hU ω g state result.2 [] result.1.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [programW_pure] at hr
      have h := fixedRun_pure_nonzero g _ state result hr
      subst h
      exact Guess.WTracks.refl state
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact hi.elim
      · rw [programW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_hashW_tracks hU ω g x state middle hm).2
          (ih middle.1 (hn _) middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · exact hi.elim
theorem worldGame_tracking (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (result : (Bool × QueryLog Requests × List Wots.Entry) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (worldGame hU ω adversary) init result ≠ 0) :
    result.2.probes ≤ result.1.2.2.length ∧
      ∀ c, GuessedIn (wA hU ω g) result.1.2.1 result.1.2.2 c → Guess.PrefixIn result.2.guesses c.1 c.2.val := by
  unfold worldGame at hr
  obtain ⟨interaction, hi, hr⟩ := fixedRun_bind_nonzero g _ _ init result hr
  obtain ⟨verdict, hv, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
  have h := fixedRun_pure_nonzero g _ _ result hr
  subst h
  have t := Tracks.trans' hU ω (interactionW_tracks hU ω g _ _ init interaction hi)
    (programW_tracks hU ω g _ (PaddedGame.verdict_public _ _) _ verdict hv)
  rw [List.append_nil] at t
  refine ⟨by simpa [init, SecretGuessObservation.initialState] using t.probes, ?_⟩
  intro c hc
  exact t.guess (by simp [init, SecretGuessObservation.initialState]) c hc.1 hc.2
/-- FTS overflow in a signing log: more than 50 distinct signed outputs share an index (campaign X1). -/
def OverflowIn (A : Answers) (log : QueryLog Requests) : Prop :=
  ∃ i : Nat, 50 < ((loggedOutputs A log).toFinset.filter fun out => WCT9.digestIndex out = i).card
theorem rank_three_card_le (w : WCT9.Rank) :
    ((Finset.univ : Finset (Fin 6)).filter fun t => WCT9.wordDigit w t = 4).card ≤ 1 :=
  WCT9.f8_seedDisclosures_card_le _
/-- Without overflow in the log, the engine never flags `Bad`: retired-but-unguessed seeds were disclosed by at most
50 signatures per index, at most two seeds per signature and family (campaign T8: at most one, the digit-4 chain). -/
theorem worldGame_noBad (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (result : (Bool × QueryLog Requests × List Wots.Entry) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (worldGame hU ω adversary) init result ≠ 0)
    (hno : ¬OverflowIn (wA hU ω g) result.1.2.1) : ¬Guess.Fam.Bad result.2 := by
  unfold worldGame at hr
  obtain ⟨interaction, hi, hr⟩ := fixedRun_bind_nonzero g _ _ init result hr
  obtain ⟨verdict, hv, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
  have h := fixedRun_pure_nonzero g _ _ result hr
  subst h
  have t := Tracks.trans' hU ω (interactionW_tracks hU ω g _ _ init interaction hi)
    (programW_tracks hU ω g _ (PaddedGame.verdict_public _ _) _ verdict hv)
  rw [List.append_nil] at t
  rintro ⟨f, hf⟩
  have hf' : 51 < (Guess.Fam.freeRetired verdict.2 f).card := hf
  have hno' : ¬OverflowIn (wA hU ω g) interaction.1.2.1 := hno
  set X := loggedOutputs (wA hU ω g) interaction.1.2.1
  have hcount : ((X.toFinset.filter fun out => WCT9.digestIndex out = f.1.val)).card ≤ 50 := by
    by_contra hc
    exact hno' ⟨f.1.val, Nat.lt_of_not_le hc⟩
  let S : Finset (Fin 128 × Fin 6) := (X.toFinset.filter fun out => WCT9.digestIndex out = f.1.val).biUnion
    fun out => ((Finset.univ : Finset (Fin 6)).filter fun t => WCT9.wordDigit (WCT9.rank out f.2) t = 4).image
      fun t => (WCT9.child out f.2, t)
  have hsub : Guess.Fam.freeRetired verdict.2 f ⊆ S := by
    intro p hp
    rw [Guess.Fam.mem_freeRetired] at hp
    obtain ⟨hret, hng⟩ := hp
    rcases t.prefixTracks.origin (Guess.Fam.member f p.1 p.2) 0 (Guess.prefixIn_of_mem hret) with h0 | h0 | h0
    · simp [init, SecretGuessObservation.initialState, Guess.not_prefixIn_empty] at h0
    · obtain ⟨q, hq, hm⟩ := h0
      have : q = 0 := Fin.ext (by omega)
      subst this
      exact absurd hm hng
    · obtain ⟨out, hout, h1, h2, h3⟩ := h0
      have hd := WCT9.wordDigit_le_four (WCT9.rank out f.2) p.2
      simp only [S, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset, Finset.mem_image, Finset.mem_univ,
        true_and]
      refine ⟨out, ⟨hout, h1⟩, p.2, ?_, ?_⟩
      · change 4 - WCT9.wordDigit (WCT9.rank out f.2) p.2 ≤ 0 at h3
        omega
      · exact Prod.ext h2 rfl
  have hS : S.card ≤ 50 := by
    refine Finset.card_biUnion_le.trans ?_
    calc (∑ out ∈ X.toFinset.filter (fun out => WCT9.digestIndex out = f.1.val),
          (((Finset.univ : Finset (Fin 6)).filter fun t => WCT9.wordDigit (WCT9.rank out f.2) t = 4).image
            fun t => (WCT9.child out f.2, t)).card)
        ≤ ∑ out ∈ X.toFinset.filter (fun out => WCT9.digestIndex out = f.1.val), 1 :=
          Finset.sum_le_sum fun out _ => Finset.card_image_le.trans (rank_three_card_le _)
      _ ≤ 50 := by rw [Finset.sum_const, smul_eq_mul]; omega
  have := Finset.card_le_card hsub
  omega
end Tracking
end ClaudeWCT.W9.T3.Security.WPair
end

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open SourceQueries
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem lowTop_free (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (shortHash (WCT9.wctTopInput coord index heap left pad right)) WFree := by
  unfold WCT9.wctTopInput WCT9.wctNodeHeader
  rw [List.append_assoc (SphincsSecurity.bytesLE 16 left ++ SphincsSecurity.bytesLE 16 _)
    (SphincsSecurity.bytesLE 16 pad)]
  exact shortHash_free' _ _ (nodeTweak_probe_safeS 3 (WCT9.nodeLayer coord) index heap)

theorem sharedOuterHash_free (coord index heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (sharedOuterHash coord index heap left right) WFree := by
  unfold sharedOuterHash
  split
  · exact lowTop_free _ _ _ _ _ _
  · exact wctTopHash_free _ _ _ _ _ _

/-- C1: a packed node (either half) makes only a free query. -/
theorem nodeHashH_free (coord index heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (WCT9.wctNodeHashH coord index heap left right) WFree := by
  have he : WCT9.wctNodeHashH coord index heap left right =
      WCT9.ftsHash heap (WCT9.wctTopInput coord index heap left 0 right) := by
    unfold WCT9.wctNodeHashH WCT9.wctTopInput
    rw [WCT9.bytesLE_zero16]
  rw [he, WCT9.ftsHash_eq]
  split
  · exact wctTopHash_free coord index heap left 0 right
  · exact lowTop_free coord index heap left 0 right

theorem sharedNode_free (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot)
    (left right : Digest) : AllQueriesSatisfy (sharedNode first coord index heap pads left right) WFree := by
  unfold sharedNode
  split
  · exact sharedOuterHash_free _ _ _ _ _
  · split
    · split
      · exact wctTopHash_free _ _ _ _ _ _
      · exact lowTop_free _ _ _ _ _ _
    · exact nodeHashH_free _ _ _ _ _

theorem sharedHeap_free (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) (leaves : List Digest) :
    AllQueriesSatisfy (sharedHeap first index coord pads leaves) WFree := by
  unfold sharedHeap
  exact foldlM_allowed WFree _ _ (fun nodes heap =>
    bind_allowed WFree (sharedNode_free _ _ _ _ _ _ _) fun _ => pure_allowed _ _) _

theorem rawChild_lt (first : Bool) (physical : Nat) (hphysical : physical < 128) :
    rawChild first physical < 128 := by
  cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

theorem sharedLeaves_world (hidden hidden' : CanonTable.HiddenF) (first : Bool)
    (index : Nat) (hindex : index < 2 ^ 31) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedLeaves (wA hU ω hidden) first index coord.val pads =
      sharedLeaves (wA hU ω hidden') first index coord.val pads := by
  unfold sharedLeaves
  apply congrArg List.ofFn
  funext physical
  exact childRootH_world hU ω hidden hidden' (128 + physical.val) index hindex coord (rawChild first physical.val)
    (rawChild_lt first physical.val physical.isLt) _

theorem sharedNodes_world (hidden hidden' : CanonTable.HiddenF) (first : Bool)
    (index : Nat) (hindex : index < 2 ^ 31) (coord : Fin 9) (pads : Nat → PairRoot) :
    sharedNodes (wA hU ω hidden) first index coord.val pads =
      sharedNodes (wA hU ω hidden') first index coord.val pads := by
  unfold sharedNodes
  rw [sharedLeaves_world hU ω hidden hidden' first index hindex coord]
  exact eval_free hU ω hidden hidden' (sharedHeap_free _ _ _ _ _)

theorem firstNodes_world (hidden hidden' : CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) (pair : Fin 4) (prev : PairRoot) :
    firstNodes (wA hU ω hidden) index pair.val prev = firstNodes (wA hU ω hidden') index pair.val prev := by
  exact sharedNodes_world hU ω hidden hidden' true index hindex
    ⟨2 * pair.val, by have := pair.isLt; omega⟩ (fun _ => prev)

theorem secondNodes_world (hidden hidden' : CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) (pair : Fin 4) (prev : PairRoot) :
    secondNodes (wA hU ω hidden) index pair.val prev = secondNodes (wA hU ω hidden') index pair.val prev := by
  unfold secondNodes
  rw [firstNodes_world hU ω hidden hidden' index hindex pair]
  exact sharedNodes_world hU ω hidden hidden' false index hindex
    ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ _

theorem expectedPairRoot_world (hidden hidden' : CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) (pair : Fin 4) (prev : PairRoot) :
    expectedPairRoot (wA hU ω hidden) index pair.val prev =
      expectedPairRoot (wA hU ω hidden') index pair.val prev := by
  unfold expectedPairRoot
  rw [secondNodes_world hU ω hidden hidden' index hindex pair]

end ClaudeWCT.W9.T3.Security.WPair.Paired


namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
theorem forestCommitment_world (hidden hidden' : CanonTable.HiddenF) (index : Nat)
    (hindex : index < 2 ^ 31) :
    forestCommitment (wA hU ω hidden) index = forestCommitment (wA hU ω hidden') index := by
  have hpair (pair : Nat) (hp : pair < 4) (prev : PairRoot) :=
    expectedPairRoot_world hU ω hidden hidden' index hindex ⟨pair, hp⟩ prev
  dsimp only [forestCommitment]
  rw [hpair 0 (by decide), hpair 1 (by decide), hpair 2 (by decide), hpair 3 (by decide),
    sharedNodes_world hU ω hidden hidden' false index hindex ⟨8, by decide⟩]
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def chainOf (output : HashOutput) (coord : Fin 9) (chain : Fin 6) : Guess.ChainAddr :=
  (⟨digestIndex output, digestIndex_lt output⟩, coord, rawChildFromOutput output coord, chain)

theorem chainOf_injective (output : HashOutput) {coord coord' : Fin 9} {chain chain' : Fin 6}
    (h : chainOf output coord chain = chainOf output coord' chain') : coord = coord' ∧ chain = chain' := by
  simp only [chainOf, Prod.mk.injEq] at h
  exact ⟨h.2.1, h.2.2.2⟩

def deficit (output : HashOutput) (coord : Fin 9) (chain : Fin 6) : Nat :=
  wordDigit (forestRank output coord.val) chain

theorem deficit_le (output : HashOutput) (coord : Fin 9) (chain : Fin 6) :
    deficit output coord chain ≤ 4 := wordDigit_le_four _ _

theorem deficit_sum (output : HashOutput) (coord : Fin 9) :
    ∑ chain, deficit output coord chain = 7 := wordStep_count _

def revealedCoords (output : HashOutput) : List Guess.GCoord :=
  (List.finRange 9).flatMap fun coord => (List.finRange 6).filterMap fun chain =>
    if h : 1 ≤ deficit output coord chain then
      some (chainOf output coord chain, ⟨4 - deficit output coord chain, by omega⟩)
    else none

theorem mem_revealedCoords {output : HashOutput} {cell : Guess.GCoord} :
    cell ∈ revealedCoords output ↔ ∃ (coord : Fin 9) (chain : Fin 6), 1 ≤ deficit output coord chain ∧
      cell.1 = chainOf output coord chain ∧ cell.2.val = 4 - deficit output coord chain := by
  unfold revealedCoords
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨coord, chain, hc⟩
    split_ifs at hc with h
    · cases hc
      exact ⟨coord, chain, h, rfl, rfl⟩
  · rintro ⟨coord, chain, h, h1, h2⟩
    refine ⟨coord, chain, ?_⟩
    rw [dif_pos h]
    congr 1
    exact Prod.ext h1.symm (Fin.ext h2.symm)

noncomputable def liftH (values : Guess.GCoord → Digest) (output : HashOutput) : CanonTable.HiddenF :=
  (fun family => if family.1.val = outIndex output then
      interp7 (fun chain => values ((family.1, family.2, rawChildFromOutput output family.2, chain), 0))
        (rawChildFromOutput output family.2) else 0,
    fun label => values (label.1, label.2.succ))

theorem phi_liftH (values : Guess.GCoord → Digest) (output : HashOutput) (cell : Guess.GCoord)
    (hc : cell ∈ revealedCoords output) : Guess.Fam.phi (liftH values output).1 (liftH values output).2 cell = values cell := by
  obtain ⟨coord, chain, _, h1, h2⟩ := mem_revealedCoords.mp hc
  obtain ⟨addr, position⟩ := cell
  simp only at h1 h2
  subst h1
  by_cases hp : position = 0
  · subst hp
    rw [Guess.Fam.phi_seed]
    have hindex : (Guess.Fam.famOf (chainOf output coord chain)).1.val = outIndex output := rfl
    simp only [liftH, Guess.Fam.seedK, hindex, if_true]
    exact interp7_spec _ _ chain
  · rw [Guess.Fam.phi_label' _ _ (chainOf output coord chain, position) hp]
    simp only [liftH, Fin.succ_pred]

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem selectedChain_world (hidden hidden' : CanonTable.HiddenF) (output : HashOutput)
    (h : ∀ cell ∈ revealedCoords output, Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell)
    (coord : Fin 9) (chain : Fin 6) :
    WCT9.chainValue (wA hU omega hidden) (digestIndex output) coord.val
        (rawChildFromOutput output coord).val (forestRank output coord.val) chain =
      WCT9.chainValue (wA hU omega hidden') (digestIndex output) coord.val
        (rawChildFromOutput output coord).val (forestRank output coord.val) chain := by
  rw [wctChainValue_eq _ _ (digestIndex_lt output), wctChainValue_eq _ _ (digestIndex_lt output),
    chainValue_world hU omega hidden _ _ (by omega), chainValue_world hU omega hidden' _ _ (by omega)]
  unfold Guess.ChainTable.walkVal
  by_cases hd : 1 ≤ deficit output coord chain
  · have hp : 4 - wordDigit (forestRank output coord.val) chain < 4 := by change 4 - deficit output coord chain < 4; omega
    rw [dif_pos hp, dif_pos hp]
    apply h
    exact mem_revealedCoords.mpr ⟨coord, chain, hd, rfl, rfl⟩
  · have hp : ¬4 - wordDigit (forestRank output coord.val) chain < 4 := by change ¬4 - deficit output coord chain < 4; omega
    rw [dif_neg hp, dif_neg hp]
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem rawFirst_output (output : HashOutput) (pair : Fin 4) :
    rawChild true (firstChild ((forestSelectionFromOutput output).pairs pair)).val =
      (rawChildFromOutput output ⟨2 * pair.val, by have := pair.isLt; omega⟩).val := by
  rw [← physicalFromOutput_first]
  have hf : firstCoord (2 * pair.val) = true := by fin_cases pair <;> rfl
  simp only [physicalChildFromOutput, hf]
  exact raw_physical_child _ _ (rawChildFromOutput output _).isLt

theorem rawSecond_output (output : HashOutput) (pair : Fin 4) :
    rawChild false (secondChild ((forestSelectionFromOutput output).pairs pair)).val =
      (rawChildFromOutput output ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩).val := by
  rw [← physicalFromOutput_second]
  have hf : firstCoord (2 * pair.val + 1) = false := by fin_cases pair <;> rfl
  simp only [physicalChildFromOutput, hf]
  exact raw_physical_child _ _ (rawChildFromOutput output _).isLt

theorem rawSingleton_output (output : HashOutput) :
    rawChild false (forestSelectionFromOutput output).singleton.val =
      (rawChildFromOutput output 8).val := by
  rw [← physicalFromOutput_singleton]
  exact raw_physical_child _ _ (rawChildFromOutput output 8).isLt

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem expectedPairOpening_world (hidden hidden' : CanonTable.HiddenF) (output : HashOutput)
    (h : ∀ cell ∈ revealedCoords output, Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell)
    (pair : Fin 4) (prev : PairRoot) :
    expectedPairOpening (wA hU omega hidden) (digestIndex output) pair.val
        ((forestSelectionFromOutput output).pairs pair)
        ((forestWordsFromOutput output).first pair) ((forestWordsFromOutput output).second pair) prev =
      expectedPairOpening (wA hU omega hidden') (digestIndex output) pair.val
        ((forestSelectionFromOutput output).pairs pair)
        ((forestWordsFromOutput output).first pair) ((forestWordsFromOutput output).second pair) prev := by
  have ha := selectedChain_world hU omega hidden hidden' output h
    ⟨2 * pair.val, by have := pair.isLt; omega⟩
  have hb := selectedChain_world hU omega hidden hidden' output h
    ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩
  unfold expectedPairOpening
  rw [rawFirst_output, rawSecond_output,
    firstNodes_world hU omega hidden hidden' (digestIndex output) (digestIndex_lt output) pair,
    secondNodes_world hU omega hidden hidden' (digestIndex output) (digestIndex_lt output) pair]
  congr 2 <;> funext i
  · exact congrArg (fun values => (List.ofFn values).getD i.val 0) (funext ha)
  · exact congrArg (fun values => (List.ofFn values).getD i.val 0) (funext hb)

theorem buildPair_world (hidden hidden' : CanonTable.HiddenF) (output : HashOutput)
    (h : ∀ cell ∈ revealedCoords output, Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell)
    (pair : Fin 4) (prev : PairRoot) :
    evalWithAnswerFn (wA hU omega hidden) (buildPair (digestIndex output) pair.val
        ((forestSelectionFromOutput output).pairs pair)
        ((forestWordsFromOutput output).first pair) ((forestWordsFromOutput output).second pair) prev) =
      evalWithAnswerFn (wA hU omega hidden') (buildPair (digestIndex output) pair.val
        ((forestSelectionFromOutput output).pairs pair)
        ((forestWordsFromOutput output).first pair) ((forestWordsFromOutput output).second pair) prev) := by
  rw [buildPair_result, buildPair_result, expectedPairOpening_world hU omega hidden hidden' output h,
    expectedPairRoot_world hU omega hidden hidden' (digestIndex output) (digestIndex_lt output) pair]

theorem buildSingleton_world (hidden hidden' : CanonTable.HiddenF) (output : HashOutput)
    (h : ∀ cell ∈ revealedCoords output, Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell)
    (prev : PairRoot) :
    evalWithAnswerFn (wA hU omega hidden) (buildSingleton (digestIndex output)
        (forestSelectionFromOutput output).singleton (forestWordsFromOutput output).singleton prev) =
      evalWithAnswerFn (wA hU omega hidden') (buildSingleton (digestIndex output)
        (forestSelectionFromOutput output).singleton (forestWordsFromOutput output).singleton prev) := by
  simp only [buildSingleton, evalWithAnswerFn_bind, buildSharedCoordinate_result, evalWithAnswerFn_pure]
  rw [rawSingleton_output,
    sharedNodes_world hU omega hidden hidden' false (digestIndex output) (digestIndex_lt output) ⟨8, by decide⟩]
  have hv := funext (selectedChain_world hU omega hidden hidden' output h 8)
  have hv' : (fun i : Fin 6 => (List.ofFn (fun chain : Fin 6 =>
      WCT9.chainValue (wA hU omega hidden) (digestIndex output) 8
        (rawChildFromOutput output 8).val (forestRank output 8) chain)).getD i.val 0) =
      (fun i : Fin 6 => (List.ofFn (fun chain : Fin 6 =>
      WCT9.chainValue (wA hU omega hidden') (digestIndex output) 8
        (rawChildFromOutput output 8).val (forestRank output 8) chain)).getD i.val 0) := by
    funext i
    exact congrArg (fun values => (List.ofFn values).getD i.val 0) hv
  exact congrArg (fun values =>
    ((⟨values,
      fun i => authAt (sharedNodes (wA hU omega hidden') false (digestIndex output) 8 (fun _ => prev))
        (forestSelectionFromOutput output).singleton.val i.val⟩ : SingletonOpening),
      ((sharedNodes (wA hU omega hidden') false (digestIndex output) 8 (fun _ => prev)).getD 2 0,
       (sharedNodes (wA hU omega hidden') false (digestIndex output) 8 (fun _ => prev)).getD 3 0))) hv'

theorem buildForest_world (hidden hidden' : CanonTable.HiddenF) (output : HashOutput)
    (h : ∀ cell ∈ revealedCoords output, Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell) :
    evalWithAnswerFn (wA hU omega hidden) (buildForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output)) =
      evalWithAnswerFn (wA hU omega hidden') (buildForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output)) := by
  have hfour : List.finRange 4 = [0,1,2,3] := by decide
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  simp only [buildPair_world hU omega hidden hidden' output h,
    buildSingleton_world hU omega hidden hidden' output h]
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def ChainCovered (X : List HashOutput) (a : Guess.ChainAddr) (p : Nat) : Prop :=
  ∃ out ∈ X, WCT9.digestIndex out = a.1.val ∧ rawChildFromOutput out a.2.1 = a.2.2.1 ∧ 4 - wordDigit (forestRank out a.2.1.val) a.2.2.2 ≤ p
def SlotCovered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) : Prop :=
  ∃ out ∈ X, WCT9.digestIndex out = WCT9.digestIndex N ∧ rawChildFromOutput out k = rawChildFromOutput N k ∧
    deficit N k t ≤ wordDigit (forestRank out k.val) t
theorem ChainCovered.mono_pos {X : List HashOutput} {a : Guess.ChainAddr} {p p' : Nat} (h : p ≤ p')
    (hc : ChainCovered X a p) : ChainCovered X a p' := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, hout, h1, h2, h3.trans h⟩
theorem ChainCovered.mono_log {X Y : List HashOutput} {a : Guess.ChainAddr} {p : Nat} (h : ∀ x ∈ X, x ∈ Y)
    (hc : ChainCovered X a p) : ChainCovered Y a p := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, h out hout, h1, h2, h3⟩
theorem slotCovered_iff_chainCovered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCovered X N k t ↔ ChainCovered X (chainOf N k t) (4 - deficit N k t) := by
  have hu := deficit_le N k t
  constructor
  · rintro ⟨out, hout, h1, h2, h3⟩
    exact ⟨out, hout, h1, h2, by simp only [chainOf]; omega⟩
  · rintro ⟨out, hout, h1, h2, h3⟩
    have hd := wordDigit_le_four (forestRank out k.val) t
    exact ⟨out, hout, h1, h2, by simp only [chainOf] at h3; omega⟩
theorem slotCovered_iff_covered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCovered X N k t ↔
      Guess.Covered (fun k d => ∃ out ∈ X, WCT9.digestIndex out = WCT9.digestIndex N ∧ rawChildFromOutput out k = rawChildFromOutput N k ∧
        d = fun t => wordDigit (forestRank out k.val) t) (deficit N) k t := by
  constructor
  · rintro ⟨out, hout, h1, h2, h3⟩
    exact ⟨_, ⟨out, hout, h1, h2, rfl⟩, h3⟩
  · rintro ⟨d, ⟨out, hout, h1, h2, rfl⟩, h3⟩
    exact ⟨out, hout, h1, h2, h3⟩
theorem caseC_slots (X : List HashOutput) (N : HashOutput) :
    (∀ k t, SlotCovered X N k t) ∨
      (∃ k t, 1 ≤ deficit N k t ∧ ¬ChainCovered X (chainOf N k t) (4 - deficit N k t) ∧
        ∀ k' t', (k', t') ≠ (k, t) → SlotCovered X N k' t') ∨
      (∃ k t k' t', (k, t) ≠ (k', t') ∧
        1 ≤ deficit N k t ∧ ¬ChainCovered X (chainOf N k t) (4 - deficit N k t) ∧
        1 ≤ deficit N k' t' ∧ ¬ChainCovered X (chainOf N k' t') (4 - deficit N k' t')) := by
  have h := Guess.three_way (fun k d => ∃ out ∈ X, WCT9.digestIndex out = WCT9.digestIndex N ∧
      rawChildFromOutput out k = rawChildFromOutput N k ∧ d = fun t => wordDigit (forestRank out k.val) t) (deficit N) (s := 7) (w := 4)
    (deficit_sum N) (deficit_le N) (by decide)
  simp only [← slotCovered_iff_covered, slotCovered_iff_chainCovered] at h
  rcases h with h | ⟨k, t, h1, h2, h3⟩ | ⟨k, t, k', t', hne, h1, h2, h3, h4⟩
  · exact Or.inl fun k t => (slotCovered_iff_chainCovered X N k t).mpr (h k t)
  · exact Or.inr (Or.inl ⟨k, t, h2, h1, fun k' t' hne => (slotCovered_iff_chainCovered X N k' t').mpr (h3 k' t' hne)⟩)
  · exact Or.inr (Or.inr ⟨k, t, k', t', hne, h2, h1, h4, h3⟩)
theorem chainOf_ne {N : HashOutput} {k k' : Fin 9} {t t' : Fin 6} (h : (k, t) ≠ (k', t')) :
    chainOf N k t ≠ chainOf N k' t' := by
  intro he
  obtain ⟨rfl, rfl⟩ := chainOf_injective N he
  exact h rfl

end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable def disclosedSeeds (outputs : List HashOutput) (family : Guess.Fam.FamIdx) :
    Finset (Fin 128 × Fin 6) :=
  (outputs.toFinset.filter fun output => digestIndex output = family.1.val).biUnion fun output =>
    ((Finset.univ : Finset (Fin 6)).filter fun chain => wordDigit (forestRank output family.2.val) chain = 4).image
      (fun chain => (rawChildFromOutput output family.2, chain))

theorem disclosedSeeds_card (outputs : List HashOutput) (family : Guess.Fam.FamIdx) :
    (disclosedSeeds outputs family).card ≤
      (outputs.toFinset.filter fun output => digestIndex output = family.1.val).card := by
  classical
  unfold disclosedSeeds
  apply le_trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ _output ∈ outputs.toFinset.filter (fun output => digestIndex output = family.1.val), 1 := by
      apply Finset.sum_le_sum
      intro output _
      exact Finset.card_image_le.trans (f8_seedDisclosures_card_le _)
    _ = _ := by simp

theorem seed_covered_mem (outputs : List HashOutput) (family : Guess.Fam.FamIdx)
    (child : Fin 128) (chain : Fin 6)
    (h : ChainCovered outputs (Guess.Fam.member family child chain) 0) :
    (child, chain) ∈ disclosedSeeds outputs family := by
  classical
  obtain ⟨output, hout, hindex, hchild, hstep⟩ := h
  have hd := wordDigit_le_four (forestRank output family.2.val) chain
  have heq : wordDigit (forestRank output family.2.val) chain = 4 := by
    change 4 - wordDigit (forestRank output family.2.val) chain ≤ 0 at hstep
    omega
  simp only [disclosedSeeds, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset,
    Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨output, ⟨hout, hindex⟩, chain, heq, Prod.ext hchild rfl⟩
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.SourceQueries
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem chainPrefixes_free (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chainPrefixes lay tree leaf i start count value) WFree := by
  induction count generalizing start value with
  | zero => exact pure_allowed _ _
  | succ count ih =>
      -- C3 (#866): a prefix step keeps the half `chainHigh lay i start` (same query as the short hash).
      exact bind_allowed WFree (Signer.halfHash_allowed_of_short WFree _ (chainStepW_free _ _ _ _ _ _)) fun next =>
        bind_allowed WFree (ih _ next) fun _ => pure_allowed _ _

theorem lowerCoefs_free (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    AllQueriesSatisfy (lowerCoefs lay tree leaf carry) WFree := by
  unfold lowerCoefs lowerFamCoefs
  split
  · exact bind_allowed WFree (bind_allowed WFree (foldlM_allowed WFree _ _ (fun acc j =>
      bind_allowed WFree (lowerSeedPair_free _ _ _) fun _ => pure_allowed _ _) _) fun _ => pure_allowed _ _)
      fun _ => pure_allowed _ _
  · exact pure_allowed _ _

theorem buildLeafPrefixes_free (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    AllQueriesSatisfy (buildLeafPrefixes lay tree leaf carry) WFree := by
  unfold buildLeafPrefixes
  exact bind_allowed WFree (lowerCoefs_free _ _ _ _) fun _ =>
    bind_allowed WFree (mapM_allowed WFree _ _ (fun _ => chainPrefixes_free _ _ _ _ _ _ _)) fun _ =>
      bind_allowed WFree (Signer.lowerLeafHash_allowed_of_leafHash WFree leafHash_free _ _ _ _) fun _ =>
        pure_allowed _ _

/-- C2/C3 (#866): `WCT9.buildLeafPF` hashes with `chainW` and `lowerLeafHash` (the legacy `buildLeafPF_free` was
removed with #866; this is its paired-section replacement). -/
theorem buildLeafPF_free (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : List Digest) :
    AllQueriesSatisfy (WCT9.buildLeafPF lay tree leaf digits carry) WFree := by
  unfold WCT9.buildLeafPF
  apply bind_allowed WFree
  · exact lowerCoefs_free _ _ _ _
  · intro cc
    apply bind_allowed WFree
    · apply foldlM_allowed WFree
      intro state i
      exact bind_allowed WFree (Signer.chainW_allowed_of_chain WFree chainStepW_free _ _ _ _ _ _ _) fun _ =>
        bind_allowed WFree (Signer.chainW_allowed_of_chain WFree chainStepW_free _ _ _ _ _ _ _) fun _ =>
          pure_allowed _ _
    · intro state
      exact bind_allowed WFree (Signer.lowerLeafHash_allowed_of_leafHash WFree leafHash_free _ _ _ _) fun _ =>
        pure_allowed _ _

/-- C2 (#866): the lower levels use `lowerNodeHash`, whose query needs the honest heap bound, so the leaf count of
the fold is carried as in `Signer.buildTreeP_allowed'`. -/
theorem buildTreePrefixes_free (lay : Layer) (tree selected : Nat) :
    AllQueriesSatisfy (buildTreePrefixes lay tree selected) WFree := by
  unfold buildTreePrefixes
  refine Signer.allQ_bind_supp (foldlM_allowed WFree _ _ (fun state leaf => ?_) _) fun state hstate => ?_
  · split
    · exact bind_allowed WFree (buildLeafPrefixes_free _ _ _ _) fun _ => pure_allowed _ _
    · exact bind_allowed WFree (buildLeafPF_free _ _ _ _ _) fun _ => pure_allowed _ _
  · have hlen : state.1.length = 2 ^ height lay := by
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
    exact bind_allowed WFree (Signer.buildLevelsBelow_allowed WFree
      (fun lay tree heap left right hh => lowerNodeHash_free lay tree heap left right hh) lay tree _ hlen)
      fun _ => pure_allowed _ _

theorem prepareRoots_free (index : Nat) : AllQueriesSatisfy (prepareRoots index) WFree := by
  unfold prepareRoots
  exact bind_allowed WFree (buildTreePrefixes_free _ _ _) fun _ =>
    bind_allowed WFree (buildTreePrefixes_free _ _ _) fun _ =>
      bind_allowed WFree (buildTreePrefixes_free _ _ _) fun _ => pure_allowed _ _

theorem canonicalSearch_free (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) WFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold CanonicalPolicy.layerCounterSearchAt
      apply bind_allowed WFree (layerEncodingPublic_free _ _ _ _ _)
      intro answer
      split
      · exact ih _
      · exact pure_allowed _ _

theorem searchPreparedLayers_free (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) :
    AllQueriesSatisfy (searchPreparedLayers cache index prepared forest) WFree := by
  unfold searchPreparedLayers
  apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
  rintro (_ | ⟨c0, d0⟩)
  · exact pure_allowed _ _
  · dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
      rintro (_ | ⟨c1, d1⟩)
      · exact pure_allowed _ _
      · dsimp only
        split
        · exact pure_allowed _ _
        · apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
          rintro (_ | ⟨c2, d2⟩)
          · exact pure_allowed _ _
          · dsimp only
            split
            · exact pure_allowed _ _
            · apply bind_allowed WFree (canonicalSearch_free _ _ _ _ _ _ _)
              rintro (_ | ⟨c3, d3⟩)
              · exact pure_allowed _ _
              · exact bind_allowed WFree (signTop_free _ _ _) fun _ => pure_allowed _ _

theorem sharedDigestSearch_free (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (sharedDigestSearch rho message counter fuel) WFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold sharedDigestSearch
      exact bind_allowed WFree (digest_free _ _ _) fun _ => by
        split
        · exact pure_allowed _ _
        · exact ih _
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

noncomputable def signerCore (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    Option (Digest × HashOutput × CanonicalLayers) :=
  let answers := wA hU omega 0
  let rho := evalWithAnswerFn answers (privateNonce message)
  match evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none => none
  | some (_, output) =>
      match evalWithAnswerFn answers (searchPreparedLayers cache (digestIndex output)
          (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
          (forestCommitment answers (digestIndex output))) with
      | none => none
      | some layers => some (rho, output, layers)

attribute [local irreducible] signerCore

def assembleWith (answers : Answers) (core : Digest × HashOutput × CanonicalLayers) :
    SigGolfCandidate.Research.SharedForest.Signature :=
  ⟨core.1, core.2.2.policyHints,
    (evalWithAnswerFn answers (buildForest (digestIndex core.2.1)
      (forestSelectionFromOutput core.2.1) (forestWordsFromOutput core.2.1))).1,
    fun lay => piecesSignature lay (core.2.2.pieces.getD lay.val ([], []))⟩

theorem signFromOutput_answers (hidden : CanonTable.HiddenF) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    evalWithAnswerFn (wA hU omega hidden) (signFromOutput cache rho counter output) =
      (evalWithAnswerFn (wA hU omega 0) (searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn (wA hU omega 0) (prepareRoots (digestIndex output)))
        (forestCommitment (wA hU omega 0) (digestIndex output)))).map
        (fun layers => (⟨assembleWith (wA hU omega hidden) (rho, output, layers), counter,
          fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true), []⟩ :
            SigGolfCandidate.Research.SharedForest.Witness)) := by
  simp only [signFromOutput, evalWithAnswerFn_bind]
  rw [buildForest_commitment, eval_free hU omega hidden 0 (prepareRoots_free _),
    forestCommitment_world hU omega hidden 0 (digestIndex output) (digestIndex_lt output),
    eval_free hU omega hidden 0 (searchPreparedLayers_free _ _ _ _)]
  cases evalWithAnswerFn (wA hU omega 0) (searchPreparedLayers cache (digestIndex output)
      (evalWithAnswerFn (wA hU omega 0) (prepareRoots (digestIndex output)))
      (forestCommitment (wA hU omega 0) (digestIndex output))) <;> rfl

theorem signPayload_answers (hidden : CanonTable.HiddenF) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    evalWithAnswerFn (wA hU omega hidden) (SigGolfCandidate.Research.SharedForest.signPayload cache message) =
      (signerCore hU omega cache message).map (assembleWith (wA hU omega hidden)) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload signerCore
  rw [evalWithAnswerFn_bind, eval_free hU omega hidden 0 (privateNonce_free _),
    evalWithAnswerFn_bind, eval_free hU omega hidden 0 (sharedDigestSearch_free _ _ _ _)]
  dsimp only
  cases hs : evalWithAnswerFn (wA hU omega 0) (sharedDigestSearch
      (evalWithAnswerFn (wA hU omega 0) (privateNonce message)) message 0 digestAttemptLimit) with
  | none => simp only [hs, evalWithAnswerFn_pure, Option.map_none]
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hs, evalWithAnswerFn_bind, signFromOutput_answers]
      cases evalWithAnswerFn (wA hU omega 0) (searchPreparedLayers cache (digestIndex output)
          (evalWithAnswerFn (wA hU omega 0) (prepareRoots (digestIndex output)))
          (forestCommitment (wA hU omega 0) (digestIndex output))) <;> rfl

noncomputable def openedFor (cache : SigGolfCandidate.T3.Cache) (message : Message) : List Guess.GCoord :=
  match signerCore hU omega cache message with
  | none => []
  | some core => revealedCoords core.2.1

theorem assembleWith_local (hidden hidden' : CanonTable.HiddenF)
    (core : Digest × HashOutput × CanonicalLayers)
    (h : ∀ cell ∈ revealedCoords core.2.1,
      Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell) :
    assembleWith (wA hU omega hidden) core = assembleWith (wA hU omega hidden') core := by
  exact congrArg (fun forest => (⟨core.1, core.2.2.policyHints, forest,
    fun lay => piecesSignature lay (core.2.2.pieces.getD lay.val ([], []))⟩ :
      SigGolfCandidate.Research.SharedForest.Signature))
    (congrArg Prod.fst (buildForest_world hU omega hidden hidden' core.2.1 h))

theorem assembleOption_local (hidden hidden' : CanonTable.HiddenF)
    (coreOption : Option (Digest × HashOutput × CanonicalLayers))
    (h : ∀ cell ∈ (match coreOption with | none => [] | some core => revealedCoords core.2.1),
      Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell) :
    coreOption.map (assembleWith (wA hU omega hidden)) =
      coreOption.map (assembleWith (wA hU omega hidden')) := by
  cases coreOption with
  | none => exact (Option.map_none _).trans (Option.map_none _).symm
  | some core =>
      exact (Option.map_some _ _).trans
        ((congrArg some (assembleWith_local hU omega hidden hidden' core h)).trans
          (Option.map_some _ _).symm)

theorem signPayload_local (hidden hidden' : CanonTable.HiddenF) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (h : ∀ cell ∈ openedFor hU omega cache message,
      Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell) :
    evalWithAnswerFn (wA hU omega hidden) (SigGolfCandidate.Research.SharedForest.signPayload cache message) =
      evalWithAnswerFn (wA hU omega hidden') (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  exact (signPayload_answers hU omega hidden cache message).trans
    ((assembleOption_local hU omega hidden hidden' (signerCore hU omega cache message) h).trans
      (signPayload_answers hU omega hidden' cache message).symm)

noncomputable def liftFor (cache : SigGolfCandidate.T3.Cache) (message : Message) (values : Guess.GCoord → Digest) :
    CanonTable.HiddenF :=
  match signerCore hU omega cache message with
  | none => 0
  | some core => liftH values core.2.1

theorem phi_liftFor (cache : SigGolfCandidate.T3.Cache) (message : Message) (values : Guess.GCoord → Digest)
    (cell : Guess.GCoord) (hc : cell ∈ openedFor hU omega cache message) :
    Guess.Fam.phi (liftFor hU omega cache message values).1 (liftFor hU omega cache message values).2 cell = values cell := by
  unfold liftFor
  unfold openedFor at hc
  cases hs : signerCore hU omega cache message with
  | none => rw [hs] at hc; cases hc
  | some core => rw [hs] at hc; exact phi_liftH values core.2.1 cell hc
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

noncomputable def authenticatedSign (published : SigGolfCandidate.T3.Cache) (request : Request) :
    M (Option SigGolfCandidate.Research.SharedForest.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then SigGolfCandidate.Research.SharedForest.signPayload request.cache request.message
  else pure none

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

noncomputable def openedForRequest (published : SigGolfCandidate.T3.Cache) (request : Request) : List Guess.GCoord :=
  if request.cache = published then openedFor hU omega request.cache request.message else []

noncomputable def liftForRequest (published : SigGolfCandidate.T3.Cache) (request : Request)
    (values : Guess.GCoord → Digest) : CanonTable.HiddenF :=
  if request.cache = published then liftFor hU omega request.cache request.message values else 0

theorem authenticatedSign_local (hidden hidden' : CanonTable.HiddenF)
    (published : SigGolfCandidate.T3.Cache) (request : Request)
    (h : ∀ cell ∈ openedForRequest hU omega published request,
      Guess.Fam.phi hidden.1 hidden.2 cell = Guess.Fam.phi hidden'.1 hidden'.2 cell) :
    evalWithAnswerFn (wA hU omega hidden) (authenticatedSign published request) =
      evalWithAnswerFn (wA hU omega hidden') (authenticatedSign published request) := by
  unfold authenticatedSign
  rw [eval_privateMac_bind, eval_privateMac_bind]
  by_cases hc : request.cache = published
  · simp only [openedForRequest, if_pos hc] at h ⊢
    exact signPayload_local hU omega hidden hidden' request.cache request.message h
  · simp only [if_neg hc]
    rfl

theorem phi_liftForRequest (published : SigGolfCandidate.T3.Cache) (request : Request)
    (values : Guess.GCoord → Digest) (cell : Guess.GCoord)
    (hc : cell ∈ openedForRequest hU omega published request) :
    Guess.Fam.phi (liftForRequest hU omega published request values).1
      (liftForRequest hU omega published request values).2 cell = values cell := by
  by_cases hcache : request.cache = published
  · simp only [liftForRequest, if_pos hcache]
    exact phi_liftFor hU omega request.cache request.message values cell
      (by simpa only [openedForRequest, if_pos hcache] using hc)
  · simp only [openedForRequest, if_neg hcache, List.not_mem_nil] at hc

noncomputable def signW (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp WSpec (Option SigGolfCandidate.Research.SharedForest.Signature) := do
  let positions := openedForRequest hU omega published request
  let values ← Guess.discloseAll (auxSpec := unifSpec) (V := Digest) positions
  pure (evalWithAnswerFn (wA hU omega
    (liftForRequest hU omega published request (overwrite positions values)))
    (authenticatedSign published request))

theorem fixed_signW (hidden : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (fixedW hidden) (signW hU omega published request) =
      pure (evalWithAnswerFn (wA hU omega hidden) (authenticatedSign published request)) := by
  unfold signW
  rw [simulateQ_bind, Guess.fixed_discloseAll, pure_bind, simulateQ_pure]
  congr 1
  apply authenticatedSign_local
  intro cell hc
  rw [phi_liftForRequest hU omega published request _ cell hc]
  exact overwrite_map (Guess.Fam.phi hidden.1 hidden.2) _ cell hc
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Requests := Request →ₒ Option SigGolfCandidate.Research.SharedForest.Signature
abbrev Interaction := OracleWorld + Requests

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)

noncomputable def interactionW (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp Interaction α → OracleComp WSpec (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signW hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
noncomputable def interactionT (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp Interaction α → ProbComp (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let rest ← next (T (.inl (.inr x)))
          pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)
      | .inr request => do
          let rest ← next (evalWithAnswerFn T (authenticatedSign published request))
          pure (rest.1, ⟨request, evalWithAnswerFn T (authenticatedSign published request)⟩ :: rest.2.1,
            rest.2.2))
theorem interactionW_pure (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionW hU ω published (pure value : OracleComp Interaction α) = pure (value, [], []) := rfl
theorem interactionW_coin (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp Interaction α) :
    interactionW hU ω published (liftM (Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1))) >>= fun coin =>
        interactionW hU ω published (next coin)) := rfl
theorem interactionW_public (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp Interaction α) :
    interactionW hU ω published (liftM (Interaction.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => interactionW hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionW_request (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp Interaction α) :
    interactionW hU ω published (liftM (Interaction.query (.inr request)) >>= next) =
      (signW hU ω published request >>= fun signature => interactionW hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem interactionT_pure (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionT T published (pure value : OracleComp Interaction α) = pure (value, [], []) := rfl
theorem interactionT_coin (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp Interaction α) :
    interactionT T published (liftM (Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin => interactionT T published (next coin)) :=
  rfl
theorem interactionT_public (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp Interaction α) :
    interactionT T published (liftM (Interaction.query (.inl (.inr x))) >>= next) =
      (interactionT T published (next (T (.inl (.inr x)))) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)) := rfl
theorem interactionT_request (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp Interaction α) :
    interactionT T published (liftM (Interaction.query (.inr request)) >>= next) =
      (interactionT T published (next (evalWithAnswerFn T (authenticatedSign published request))) >>=
        fun rest => pure (rest.1, ⟨request, evalWithAnswerFn T (authenticatedSign published request)⟩ ::
          rest.2.1, rest.2.2)) := rfl
theorem fixed_interactionW (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp Interaction α) :
    simulateQ (fixedW g) (interactionW hU ω published program) = interactionT (wA hU ω g) published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionW_pure, interactionT_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin, interactionT_coin, simulateQ_bind, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [interactionW_public, interactionT_public, simulateQ_bind, fixed_hashW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [interactionW_request, interactionT_request, simulateQ_bind, fixed_signW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

noncomputable def signedOutput (answers : Answers) (message : Message)
    (signature : SigGolfCandidate.Research.SharedForest.Signature) : Option HashOutput :=
  (evalWithAnswerFn answers (sharedDigestSearch signature.rho message 0 digestAttemptLimit)).map Prod.snd

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (omega : CanonTable.Omega U)

theorem signerCore_search {cache : SigGolfCandidate.T3.Cache} {message : Message}
    {core : Digest × HashOutput × CanonicalLayers} (h : signerCore hU omega cache message = some core) :
    ∃ counter, evalWithAnswerFn (wA hU omega 0) (sharedDigestSearch core.1 message 0 digestAttemptLimit) =
      some (counter, core.2.1) := by
  unfold signerCore at h
  dsimp only at h
  split at h
  · cases h
  · rename_i counter output hfound
    split at h
    · cases h
    · cases h
      exact ⟨counter, hfound⟩

theorem signedOutput_world (hidden : CanonTable.HiddenF) {cache : SigGolfCandidate.T3.Cache}
    {message : Message} {core : Digest × HashOutput × CanonicalLayers}
    (h : signerCore hU omega cache message = some core) :
    signedOutput (wA hU omega hidden) message (assembleWith (wA hU omega hidden) core) = some core.2.1 := by
  obtain ⟨counter, hs⟩ := signerCore_search hU omega h
  change (evalWithAnswerFn (wA hU omega hidden)
    (sharedDigestSearch core.1 message 0 digestAttemptLimit)).map Prod.snd = _
  rw [eval_free hU omega hidden 0 (sharedDigestSearch_free _ _ _ _), hs]
  rfl

theorem signPayload_opened (hidden : CanonTable.HiddenF) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (cell : Guess.GCoord) (hc : cell ∈ openedFor hU omega cache message) :
    ∃ signature output,
      evalWithAnswerFn (wA hU omega hidden) (SigGolfCandidate.Research.SharedForest.signPayload cache message) = some signature ∧
      signedOutput (wA hU omega hidden) message signature = some output ∧ cell ∈ revealedCoords output := by
  unfold openedFor at hc
  cases hcore : signerCore hU omega cache message with
  | none => rw [hcore] at hc; cases hc
  | some core =>
      rw [hcore] at hc
      refine ⟨assembleWith (wA hU omega hidden) core, core.2.1, ?_,
        signedOutput_world hU omega hidden hcore, hc⟩
      exact (signPayload_answers hU omega hidden cache message).trans
        ((congrArg (Option.map (assembleWith (wA hU omega hidden))) hcore).trans (Option.map_some _ _))

theorem authenticatedSign_opened (hidden : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (cell : Guess.GCoord) (hc : cell ∈ openedForRequest hU omega published request) :
    ∃ signature output, evalWithAnswerFn (wA hU omega hidden) (authenticatedSign published request) = some signature ∧
      signedOutput (wA hU omega hidden) request.message signature = some output ∧ cell ∈ revealedCoords output := by
  by_cases he : request.cache = published
  · have hm : cell ∈ openedFor hU omega request.cache request.message := by
      simpa only [openedForRequest, if_pos he] using hc
    obtain ⟨signature, output, hsign, hout, hcell⟩ := signPayload_opened hU omega hidden _ _ cell hm
    refine ⟨signature, output, ?_, hout, hcell⟩
    simpa only [authenticatedSign, eval_privateMac_bind, if_pos he] using hsign
  · simp only [openedForRequest, if_neg he, List.not_mem_nil] at hc
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.SecretGuessObservation (runWith fixedRun fixedImpl afterTrial afterDisclosure)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def loggedOutputs (answers : Correctness.Answers) (log : QueryLog Paired.Requests) : List HashOutput :=
  log.filterMap fun entry => entry.2.bind fun signature => Paired.signedOutput answers entry.1.message signature
theorem mem_loggedOutputs {answers : Correctness.Answers} {log : QueryLog Paired.Requests} {out : HashOutput} :
    out ∈ loggedOutputs answers log ↔ ∃ entry ∈ log, ∃ signature, entry.2 = some signature ∧
      Paired.signedOutput answers entry.1.message signature = some out := by
  unfold loggedOutputs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨entry, he, hb⟩
    cases hs : entry.2 with
    | none => rw [hs] at hb; cases hb
    | some signature =>
        rw [hs] at hb
        exact ⟨entry, he, signature, hs, hb⟩
  · rintro ⟨entry, he, signature, hs, ho⟩
    exact ⟨entry, he, by rw [hs]; exact ho⟩
def Disclosed (answers : Correctness.Answers) (log : QueryLog Paired.Requests) (a : Guess.ChainAddr) (p : Nat) : Prop :=
  Paired.ChainCovered (loggedOutputs answers log) a p
def GuessedIn (answers : Correctness.Answers) (log : QueryLog Paired.Requests) (entries : List Wots.Entry)
    (c : Guess.GCoord) : Prop :=
  ¬Disclosed answers log c.1 c.2.val ∧ ∃ answer, (Guess.honestProbe answers c, answer) ∈ entries
theorem Disclosed.mono_pos {answers : Correctness.Answers} {log : QueryLog Paired.Requests} {a : Guess.ChainAddr}
    {p p' : Nat} (h : p ≤ p') (hd : Disclosed answers log a p) : Disclosed answers log a p' :=
  Paired.ChainCovered.mono_pos h hd
theorem loggedOutputs_mono {answers : Correctness.Answers} {log log' : QueryLog Paired.Requests}
    (h : ∀ entry ∈ log, entry ∈ log') : ∀ out ∈ loggedOutputs answers log, out ∈ loggedOutputs answers log' := by
  intro out hout
  obtain ⟨entry, he, signature, hs, ho⟩ := mem_loggedOutputs.mp hout
  exact mem_loggedOutputs.mpr ⟨entry, h entry he, signature, hs, ho⟩
theorem Disclosed.mono_log {answers : Correctness.Answers} {log log' : QueryLog Paired.Requests} {a : Guess.ChainAddr}
    {p : Nat} (h : ∀ entry ∈ log, entry ∈ log') (hd : Disclosed answers log a p) : Disclosed answers log' a p :=
  Paired.ChainCovered.mono_log (loggedOutputs_mono h) hd

variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
def Cov (A : Answers) (log : QueryLog Paired.Requests) (a : Guess.ChainAddr) (p : Nat) : Prop := Disclosed A log a p
theorem cov_mono (A : Answers) : Guess.CovMono (Cov A) :=
  ⟨fun l1 l2 a p h => Disclosed.mono_log (fun e he => List.mem_append_left _ he) h,
    fun l1 l2 a p h => Disclosed.mono_log (fun e he => List.mem_append_right _ he) h⟩
abbrev Tracks (g : CanonTable.HiddenF) (before after : WState) (log : QueryLog Paired.Requests)
    (entries : List Wots.Entry) : Prop :=
  Guess.WTracks (CanonTable.chainTable hU ω) g (Cov (wA hU ω g)) before after log entries
theorem Tracks.trans' {g : CanonTable.HiddenF} {s1 s2 s3 : WState} {l1 l2 : QueryLog Paired.Requests}
    {e1 e2 : List Wots.Entry} (first : Tracks hU ω g s1 s2 l1 e1) (second : Tracks hU ω g s2 s3 l2 e2) :
    Tracks hU ω g s1 s3 (l1 ++ l2) (e1 ++ e2) :=
  Guess.WTracks.trans (cov_mono _) first second
theorem fixedRun_bind_nonzero {First Result : Type} (g : CanonTable.HiddenF) (first : OracleComp WSpec First)
    (next : First → OracleComp WSpec Result) (state : WState) (result : Result × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (first >>= next) state result ≠ 0) :
    ∃ middle, fixedRun env (Guess.Fam.phi g.1 g.2) first state middle ≠ 0 ∧ fixedRun env (Guess.Fam.phi g.1 g.2) (next middle.1) middle.2 result ≠ 0 :=
  Guess.fixedRun_bind_nonzero' env (Guess.Fam.phi g.1 g.2) first next state result hr
theorem fixedRun_pure_nonzero {Result : Type} (g : CanonTable.HiddenF) (value : Result) (state : WState)
    (result : Result × WState) (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (pure value) state result ≠ 0) : result = (value, state) :=
  Guess.fixedRun_pure_nonzero' env (Guess.Fam.phi g.1 g.2) value state result hr
theorem fixed_coin_tracks (g : CanonTable.HiddenF) (n : Nat) (state : WState) (result : Fin (n + 1) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (liftM (WSpec.query (.inl n))) state result ≠ 0) : Tracks hU ω g state result.2 [] [] := by
  unfold fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [fixedImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  exact Guess.WTracks.refl state
theorem fixed_hashW_tracks (g : CanonTable.HiddenF) (x : HashInput) (state : WState) (result : HashOutput × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (hashW hU ω x) state result ≠ 0) :
    result.1 = wA hU ω g (.inl (.inr x)) ∧ Tracks hU ω g state result.2 [] [(x, result.1)] :=
  Guess.WTracks.hashW (T := CanonTable.chainTable hU ω) (g := g) env x state result hr
theorem fixed_signW_tracks (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (state : WState) (result : Option SigGolfCandidate.Research.SharedForest.Signature × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (signW hU ω published request) state result ≠ 0) :
    result.1 = evalWithAnswerFn (wA hU ω g) (Paired.authenticatedSign published request) ∧
      Tracks hU ω g state result.2 [⟨request, result.1⟩] [] := by
  unfold signW at hr
  obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
  have h := fixedRun_pure_nonzero g _ _ result hr
  subst h
  have hsig : evalWithAnswerFn (wA hU ω (liftForRequest hU ω published request
        (overwrite (openedForRequest hU ω published request) middle.1)))
      (Paired.authenticatedSign published request) =
      evalWithAnswerFn (wA hU ω g) (Paired.authenticatedSign published request) := by
    have h1 := (Guess.fixedRun_discloseAll env (Guess.Fam.phi g.1 g.2) (openedForRequest hU ω published request) state
      middle hm).1
    rw [h1]
    exact authenticatedSign_local hU ω _ _ published request fun c hc => by
      rw [phi_liftForRequest hU ω published request _ c hc]
      exact overwrite_map (Guess.Fam.phi g.1 g.2) _ c hc
  refine ⟨hsig, ?_⟩
  have hcov : ∀ c ∈ openedForRequest hU ω published request,
      Cov (wA hU ω g) [⟨request, evalWithAnswerFn (wA hU ω (liftForRequest hU ω published request
        (overwrite (openedForRequest hU ω published request) middle.1)))
        (Paired.authenticatedSign published request)⟩] c.1 c.2.val := by
    intro c hc
    rw [hsig]
    obtain ⟨signature, output, hs, ho, hrev⟩ := authenticatedSign_opened hU ω g published request c hc
    obtain ⟨k, t, hu, h1, h2⟩ := mem_revealedCoords.mp hrev
    refine ⟨output, mem_loggedOutputs.mpr ⟨_, List.mem_singleton_self _, signature, hs, ho⟩, ?_, ?_, ?_⟩
    · rw [h1]; rfl
    · rw [h1]; rfl
    · rw [h1, h2]; exact le_rfl
  exact (Guess.WTracks.disclose env (openedForRequest hU ω published request) _ hcov
    (fun l a p p' hpp' hc => Disclosed.mono_pos hpp' hc) state middle hm).2
theorem interactionW_tracks (g : CanonTable.HiddenF) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp Paired.Interaction α) (state : WState)
    (result : (α × QueryLog Paired.Requests × List Wots.Entry) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (interactionW hU ω published program) state result ≠ 0) :
    Tracks hU ω g state result.2 result.1.2.1 result.1.2.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [interactionW_pure] at hr
      have h := fixedRun_pure_nonzero g _ state result hr
      subst h
      exact Guess.WTracks.refl state
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        have h := Tracks.trans' hU ω (fixed_coin_tracks hU ω g n state middle hm) (ih middle.1 middle.2 result hr)
        simpa only [List.nil_append] using h
      · rw [interactionW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_hashW_tracks hU ω g x state middle hm).2 (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · rw [interactionW_request] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_signW_tracks hU ω g published request state middle hm).2
          (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
theorem programW_tracks (g : CanonTable.HiddenF) {β : Type} (program : M β) (hp : PublicVerdict.Only program)
    (state : WState) (result : (β × List Wots.Entry) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (programW hU ω program) state result ≠ 0) :
    Tracks hU ω g state result.2 [] result.1.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [programW_pure] at hr
      have h := fixedRun_pure_nonzero g _ state result hr
      subst h
      exact Guess.WTracks.refl state
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact hi.elim
      · rw [programW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_hashW_tracks hU ω g x state middle hm).2
          (ih middle.1 (hn _) middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · exact hi.elim

def OverflowIn (A : Answers) (log : QueryLog Paired.Requests) : Prop :=
  ∃ i : Nat, 50 < ((loggedOutputs A log).toFinset.filter fun out => WCT9.digestIndex out = i).card

theorem tracked_noBad (g : CanonTable.HiddenF) (state : WState)
    (log : QueryLog Paired.Requests) (entries : List Wots.Entry)
    (ht : Tracks hU ω g init state log entries)
    (hno : ¬OverflowIn (wA hU ω g) log) : ¬Guess.Fam.Bad state := by
  rintro ⟨family, hbad⟩
  have hbad' : 51 < (Guess.Fam.freeRetired state family).card := hbad
  have hcount : (((loggedOutputs (wA hU ω g) log).toFinset.filter
      fun output => WCT9.digestIndex output = family.1.val)).card ≤ 50 := by
    by_contra hc
    exact hno ⟨family.1.val, Nat.lt_of_not_le hc⟩
  have hsub : Guess.Fam.freeRetired state family ⊆
      disclosedSeeds (loggedOutputs (wA hU ω g) log) family := by
    intro point hp
    rw [Guess.Fam.mem_freeRetired] at hp
    obtain ⟨hret, hng⟩ := hp
    rcases ht.prefixTracks.origin (Guess.Fam.member family point.1 point.2) 0
        (Guess.prefixIn_of_mem hret) with h0 | h0 | h0
    · simp [init, SecretGuessObservation.initialState, Guess.not_prefixIn_empty] at h0
    · obtain ⟨q, hq, hm⟩ := h0
      have heq : q = 0 := Fin.ext (by omega)
      subst heq
      exact absurd hm hng
    · exact seed_covered_mem _ family point.1 point.2 h0
  have hcard := (Finset.card_le_card hsub).trans (disclosedSeeds_card _ family)
  omega

theorem tracked_guessed (g : CanonTable.HiddenF) (state : WState)
    (log : QueryLog Paired.Requests) (entries : List Wots.Entry)
    (ht : Tracks hU ω g init state log entries) (cell : Guess.GCoord)
    (hg : GuessedIn (wA hU ω g) log entries cell) : state.guesses.Nonempty := by
  apply Guess.nonempty_of_prefixIn
  exact ht.guess (by simp [init, SecretGuessObservation.initialState]) cell hg.1 hg.2

noncomputable def experimentW {α β : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp Paired.Interaction α) (finish : (α × QueryLog Paired.Requests) → M β) :
    OracleComp WSpec (β × QueryLog Paired.Requests × List Wots.Entry) := do
  let interaction ← interactionW hU ω published program
  let result ← WPair.programW hU ω (finish (interaction.1, interaction.2.1))
  pure (result.1, interaction.2.1, interaction.2.2 ++ result.2)

theorem experimentW_tracks (g : CanonTable.HiddenF) {α β : Type}
    (published : SigGolfCandidate.T3.Cache) (program : OracleComp Paired.Interaction α)
    (finish : (α × QueryLog Paired.Requests) → M β) (hfinish : ∀ result, PublicVerdict.Only (finish result))
    (state : WState) (result : (β × QueryLog Paired.Requests × List Wots.Entry) × WState)
    (hr : fixedRun env (Guess.Fam.phi g.1 g.2) (experimentW hU ω published program finish) state result ≠ 0) :
    Tracks hU ω g state result.2 result.1.2.1 result.1.2.2 := by
  unfold experimentW at hr
  obtain ⟨interaction, hi, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
  obtain ⟨verdict, hv, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
  have he := fixedRun_pure_nonzero g _ _ result hr
  subst he
  have ht := Tracks.trans' hU ω (interactionW_tracks hU ω g published program state interaction hi)
    (programW_tracks hU ω g _ (hfinish _) _ verdict hv)
  simpa only [List.append_nil] using ht
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M W9Machine
open SigGolfCandidate.T3M.SecurityExtraction
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem honestProbe_slot (answers : Answers) (output : HashOutput) (k : Fin 9) (t : Fin 6) (p : Fin 4) :
    Guess.honestProbe answers (chainOf output k t,p) =
      Extract.Paired.honestInput answers (.wctChain (digestIndex output) k.val
        (rawChildFromOutput output k).val t.val p.val) := by
  rw [Extract.Paired.honestInput_wctChain]
  rfl

/-- The actual padded forest trace contains every nonempty canonical chain start
unless extraction has already found a collision. -/
theorem forest_active_probe (answers : Answers) (w : SharedV3.WBytes) (output : HashOutput)
    (reaches : evalWithAnswerFn answers (SharedV3.forest w (digestIndex output)
      (rawChildFromOutput output) (fun k => embed (forestRank output k.val)))=
        forestCommitment answers (digestIndex output)) :
    Extract.Paired.HitIn answers (queried answers (SharedV3.forest w (digestIndex output)
      (rawChildFromOutput output) (fun k => embed (forestRank output k.val)))) ∨
    ∀ (k : Fin 9) (t : Fin 6) (p : Fin 4), p.val=4-deficit output k t →
      (.inl (.inr (Guess.honestProbe answers (chainOf output k t,p))) : Spec.Domain) ∈
        queried answers (SharedV3.forest w (digestIndex output) (rawChildFromOutput output)
          (fun k => embed (forestRank output k.val))) := by
  rcases Extract.Paired.forest_extract_active answers w (digestIndex output)
    (rawChildFromOutput output) (fun k => embed (forestRank output k.val)) (digestIndex_lt output)
    (Extract.Paired.branchCompatible_output output) reaches with hh|⟨_,hp⟩
  · exact Or.inl hh
  · right
    intro k t p he
    have hd : 0<digit (embed (forestRank output k.val)) t := by
      change 0<deficit output k t
      have := p.isLt
      omega
    have h := hp k t hd
    rw [honestProbe_slot]
    have hpos : p.val=4-digit (embed (forestRank output k.val)) t := he
    rw [hpos]
    exact h

/-- A missing covered slot becomes a concrete undisclosed public probe; the
caller supplies only membership of forest queries in the recorded public trace. -/
theorem forest_uncovered_probe (answers : Answers) (w : SharedV3.WBytes) (output : HashOutput)
    (X : List HashOutput) (entries : List Wots.Entry)
    (reaches : evalWithAnswerFn answers (SharedV3.forest w (digestIndex output)
      (rawChildFromOutput output) (fun k => embed (forestRank output k.val)))=
        forestCommitment answers (digestIndex output))
    (hentries : ∀ input, (.inl (.inr input) : Spec.Domain) ∈
      queried answers (SharedV3.forest w (digestIndex output) (rawChildFromOutput output)
        (fun k => embed (forestRank output k.val))) → ∃ answer, (input,answer)∈entries) :
    Extract.Paired.HitIn answers (queried answers (SharedV3.forest w (digestIndex output)
      (rawChildFromOutput output) (fun k => embed (forestRank output k.val)))) ∨
    (∀ k t, SlotCovered X output k t) ∨
    ∃ c : Guess.GCoord, ¬ChainCovered X c.1 c.2.val ∧
      ∃ answer, (Guess.honestProbe answers c,answer)∈entries := by
  rcases forest_active_probe answers w output reaches with hh|hp
  · exact Or.inl hh
  right
  have make (k : Fin 9) (t : Fin 6) (ha : 1≤deficit output k t)
      (hu : ¬ChainCovered X (chainOf output k t) (4-deficit output k t)) :
      ∃ c : Guess.GCoord, ¬ChainCovered X c.1 c.2.val ∧
        ∃ answer, (Guess.honestProbe answers c,answer)∈entries := by
    let p : Fin 4 := ⟨4-deficit output k t,by omega⟩
    exact ⟨(chainOf output k t,p),hu,hentries _ (hp k t p rfl)⟩
  rcases caseC_slots X output with covered|⟨k,t,ha,hu,_⟩|⟨k,t,_,_,_,ha,hu,_⟩
  · exact Or.inl covered
  · exact Or.inr (make k t ha hu)
  · exact Or.inr (make k t ha hu)

#print axioms forest_uncovered_probe
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M W9Machine
open SigGolfCandidate.T3M.SecurityExtraction
set_option backward.isDefEq.respectTransparency false

theorem forest_log_split (answers : Answers) (w : SharedV3.WBytes) (output : HashOutput)
    (log : QueryLog Paired.Requests) (entries : List Wots.Entry)
    (reaches : evalWithAnswerFn answers (SharedV3.forest w (digestIndex output)
      (rawChildFromOutput output) (fun k => embed (forestRank output k.val)))=
        forestCommitment answers (digestIndex output))
    (hentries : ∀ input, (.inl (.inr input) : Spec.Domain) ∈
      queried answers (SharedV3.forest w (digestIndex output) (rawChildFromOutput output)
        (fun k => embed (forestRank output k.val))) → ∃ answer, (input,answer)∈entries) :
    Extract.Paired.HitIn answers (queried answers (SharedV3.forest w (digestIndex output)
      (rawChildFromOutput output) (fun k => embed (forestRank output k.val)))) ∨
    (∀ k t, SlotCovered (loggedOutputs answers log) output k t) ∨
    ∃ c, GuessedIn answers log entries c :=
  forest_uncovered_probe answers w output (loggedOutputs answers log) entries reaches hentries

#print axioms forest_log_split
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem payload_rho (answers : Correctness.Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (signature : SigGolfCandidate.Research.SharedForest.Signature)
    (h : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload cache message) =
      some signature) : signature.rho = evalWithAnswerFn answers (privateNonce message) := by
  rw [ClaudeWCT.Bank.Paired.signPayload_factor, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at h
  generalize evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 ClaudeWCT.WCT9.digestAttemptLimit) = found at h
  rcases found with _ | ⟨counter, output⟩
  · simp at h
  · exact ClaudeWCT.Bank.Paired.payRho answers cache _ output signature h

theorem eval_authenticatedSign (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) : evalWithAnswerFn answers (authenticatedSign published request) =
      if request.cache = published then
        evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload request.cache request.message)
      else none := by
  unfold authenticatedSign
  rw [evalWithAnswerFn_bind]
  split <;> rfl

end ClaudeWCT.W9.T3.Security.WPair.Paired
