import SigGolfCandidate.T3_Secc_PairGuessLazyDefs
set_option Elab.async false

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def NotDN : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr x) => x ∉ digestInputs
  | .inr (.inl _) => True
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr _)) => True
theorem not_digest_of_marker {x : HashInput} {h : Digest} (hx : Extract.hdrBlock x = bytesLE 16 h)
    (hm : tweakMarker h ≠ 0) : x ∉ digestInputs := by
  intro hmem
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hmem
  rw [Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hx
  unfold digestInput at hx
  have h2 : bytesLE 16 (digestHeader ctr) = bytesLE 16 h :=
    (Extract.hdrBlock_prefix rho (digestHeader ctr) (bytesLE 32 m)).symm.trans hx
  exact hm (by rw [← bytesLE_injective h2, digestHeader_marker])
/-- C4: the digest is the only query with low header word 0 (top fold labels may have byte0 = 0). -/
theorem not_digest_of_low {x : HashInput} {h : Digest} (hx : Extract.hdrBlock x = bytesLE 16 h)
    (hm : tweakLow h ≠ 0) : x ∉ digestInputs := by
  intro hmem
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hmem
  rw [Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hx
  unfold digestInput at hx
  have h2 : bytesLE 16 (digestHeader ctr) = bytesLE 16 h :=
    (Extract.hdrBlock_prefix rho (digestHeader ctr) (bytesLE 32 m)).symm.trans hx
  exact hm (by rw [← bytesLE_injective h2, digestHeader_lowNat])
section DN
open SourceQueries
theorem privatePair_dn (t l tr p ix : Nat) : AllQueriesSatisfy (privatePair t l tr p ix) NotDN := by
  unfold privatePair privateHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr trivial) fun _ => pure_allowed _ _
theorem privateMac_dn (region : Region) : AllQueriesSatisfy (privateMac region) NotDN := by
  exact privateMac_allowed NotDN (fun _ => trivial) region
theorem chainStep_dn (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (chainInput lay tree leaf i step value)) NotDN := by
  unfold shortHash publicHash
  apply bind_allowed NotDN
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    intro hm
    obtain ⟨rho, m, ctr, he⟩ := mem_digestInputs.mp hm
    have hh := congrArg Extract.hdrBlock he
    rw [chainInput_padded, Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hh
    change ((chainInput lay tree leaf i step value).drop 16).take 16 = _ at hh
    rw [chainInput_header] at hh
    unfold digestInput at hh
    rw [Extract.hdrBlock_prefix] at hh
    exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hh)
  · intro _; exact pure_allowed _ _
/-- Witness stack: the top chain step (G or F input) carries the chain header in bytes `16..32`. -/
theorem topChainStep_dn (leaf i step : Nat) (high : Bool) (value : Digest) :
    AllQueriesSatisfy (projHash high (topChainInput leaf i step value)) NotDN := by
  unfold projHash publicHash
  apply bind_allowed NotDN
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    intro hm
    obtain ⟨rho, m, ctr, he⟩ := mem_digestInputs.mp hm
    have hh := congrArg Extract.hdrBlock he
    have hpad : pad64 (topChainInput leaf i step value) = topChainInput leaf i step value := by
      unfold topChainInput; split
      · simp [pad64, SphincsSecurity.bytesLE_length, zero16]
      · exact chainInput_padded _ _ _ _ _ _
    have hhdr : ((topChainInput leaf i step value).drop 16).take 16 =
        SphincsSecurity.bytesLE 16 (chainHeader 0 0 leaf i step) := by
      unfold topChainInput; split
      · simp [zero16, List.append_assoc, SphincsSecurity.bytesLE_length]
      · exact chainInput_header _ _ _ _ _ _
    rw [hpad, Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hh
    change ((topChainInput leaf i step value).drop 16).take 16 = _ at hh
    rw [hhdr] at hh
    unfold digestInput at hh
    rw [Extract.hdrBlock_prefix] at hh
    exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hh)
  · intro _; exact pure_allowed _ _
theorem topChain_dn (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (topChain leaf i start count value) NotDN := by
  unfold topChain
  exact foldlM_allowed NotDN _ _ (fun v step => topChainStep_dn leaf i step _ v) value
theorem chain_dn (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NotDN := by
  unfold chain
  exact foldlM_allowed NotDN _ _ (fun v step => chainStep_dn lay tree leaf i step v) value
theorem leafHash_dn (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDN := by
  unfold leafHash projHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_marker (Extract.hdrBlock_leafInput lay tree leaf ends) (by rw [leafTweak_marker]; decide)))
    fun _ => pure_allowed _ _
theorem nodeHash_dn {tag : Nat} (lay tree heap : Nat) (left right : Digest) (_ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDN := by
  rw [nodeHash_eq_projHash]
  unfold projHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_low (by rw [pad64_nodeInputP, nodeInputP]; exact Extract.hdrBlock_block4 _ _ _ _)
      (nodeTweak_low_ne_zero _ _ _ _)))
    fun _ => pure_allowed _ _
theorem mask_dn (level index : Nat) : AllQueriesSatisfy (mask level index) NotDN := by
  unfold mask pairedMask
  exact bind_allowed NotDN (privatePair_dn _ _ _ _ _) fun _ => pure_allowed _ _
theorem buildLeaf_dn (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NotDN := by
  unfold buildLeaf
  apply bind_allowed NotDN
  · apply foldlM_allowed NotDN
    intro state pair
    apply bind_allowed NotDN (privatePair_dn _ _ _ _ _)
    intro seeds
    apply foldlM_allowed NotDN
    intro state half
    dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed NotDN (chain_dn _ _ _ _ _ _ _)
      intro value
      split
      · exact pure_allowed _ _
      · exact bind_allowed NotDN (chain_dn _ _ _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed NotDN (leafHash_dn _ _ _ _) fun _ => pure_allowed _ _
theorem buildLevel_dn {tag : Nat} (lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NotDN := by
  unfold buildLevel
  exact mapM_allowed NotDN _ _ fun _ => nodeHash_dn _ _ _ _ _ ht
theorem buildLevels_dn {tag : Nat} (lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NotDN := by
  unfold buildLevels
  exact foldlM_allowed NotDN _ _ (fun levels level =>
    bind_allowed NotDN (buildLevel_dn _ _ _ _ _ ht) fun _ => pure_allowed _ _) _
theorem buildTree_dn (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NotDN := by
  unfold buildTree
  apply bind_allowed NotDN
  · exact foldlM_allowed NotDN _ _ (fun state leaf =>
      bind_allowed NotDN (buildLeaf_dn _ _ _ _ _) fun _ => pure_allowed _ _) _
  · intro state
    exact bind_allowed NotDN (buildLevels_dn _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem maskedLevel_dn (nodes : List Digest) (level : Nat) :
    AllQueriesSatisfy (maskedLevel nodes level) NotDN := by
  unfold maskedLevel pairedMask
  apply bind_allowed NotDN
  · exact mapM_allowed NotDN _ _ (fun pair => bind_allowed NotDN (privatePair_dn _ _ _ _ _) (fun _ => pure_allowed _ _))
  · intro _; exact pure_allowed _ _
theorem topPairsFrom_dn (first start : Nat) (init : List Digest) :
    AllQueriesSatisfy (topPairsFrom first start init) NotDN := by
  unfold topPairsFrom topSeedPair
  exact foldlM_allowed NotDN _ _ (fun _ _ => bind_allowed NotDN (privatePair_dn _ _ _ _ _)
    fun _ => pure_allowed _ _) _
theorem buildLeafTopC_dn (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTopC leaf coefs digits signatureOnly) NotDN := by
  unfold buildLeafTopC
  apply bind_allowed NotDN
  · apply foldlM_allowed NotDN
    intro state i
    apply bind_allowed NotDN (topChain_dn _ _ _ _ _)
    intro value
    split
    · exact pure_allowed _ _
    · exact bind_allowed NotDN (topChain_dn _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed NotDN (leafHash_dn _ _ _ _) fun _ => pure_allowed _ _
theorem buildLeafTop_dn (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTop leaf digits signatureOnly) NotDN := by
  unfold buildLeafTop topCoefs
  exact bind_allowed NotDN (bind_allowed NotDN (topPairsFrom_dn _ _ _) fun _ => pure_allowed _ _)
    fun _ => buildLeafTopC_dn _ _ _ _
theorem topTreeStep_dn (st : List Digest × List Digest × Digest) (leaf : Nat) :
    AllQueriesSatisfy (topTreeStep st leaf) NotDN := by
  unfold topTreeStep topFamilyCoefs
  apply bind_allowed NotDN
  · split
    · unfold topCoefsK
      exact bind_allowed NotDN (topPairsFrom_dn _ _ _) fun _ => pure_allowed _ _
    · exact pure_allowed _ _
  · intro cc
    exact bind_allowed NotDN (buildLeafTopC_dn _ _ _ _) fun _ => pure_allowed _ _
/-- Top nonce trials: the node tweak sits in bytes `16..32` (nonce in `32..48`). -/
theorem topNodeHashN_dn (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeHashN heap n left right) NotDN := by
  unfold topNodeHashN projHash publicHash
  refine bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_low (h := nodeTweak 3 0 0 heap) ?_ (nodeTweak_low_ne_zero _ _ _ _))) fun _ => pure_allowed _ _
  rw [Extract.hdrBlock_pad64 _ (by simp [topNodeInput, nonceBytes, bytesLE_length])]
  unfold topNodeInput
  rw [List.append_assoc]
  exact Extract.hdrBlock_prefix _ _ _
theorem topNonceSearch_dn (h heap : Nat) (left right : Digest) :
    ∀ fuel n, AllQueriesSatisfy (topNonceSearch h heap left right fuel n) NotDN
  | 0, n => by
      unfold topNonceSearch
      exact bind_allowed NotDN (topNodeHashN_dn _ _ _ _) fun _ => pure_allowed _ _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine bind_allowed NotDN (topNodeHashN_dn _ _ _ _) fun _ => ?_
      split
      · exact pure_allowed _ _
      · exact topNonceSearch_dn h heap left right fuel (n + 1)
theorem buildTopLevels_dn (leaves : List Digest) : AllQueriesSatisfy (buildTopLevels leaves) NotDN := by
  unfold buildTopLevels
  refine foldlM_allowed NotDN _ _ (fun levels level => bind_allowed NotDN ?_ fun _ => pure_allowed _ _) _
  unfold buildTopLevel
  refine mapM_allowed NotDN _ _ fun i => ?_
  split
  · exact nodeHash_dn _ _ _ _ _ (by decide)
  · unfold topNodeAt
    exact map_allowed NotDN _ (topNonceSearch_dn _ _ _ _ _ _)
theorem buildTopTree_dn : AllQueriesSatisfy buildTopTree NotDN := by
  unfold buildTopTree
  exact bind_allowed NotDN (foldlM_allowed NotDN _ _ topTreeStep_dn _) fun _ => buildTopLevels_dn _
theorem keygenPayload_dn : AllQueriesSatisfy keygenPayload NotDN := by
  unfold keygenPayload
  apply bind_allowed NotDN buildTopTree_dn
  intro built
  apply bind_allowed NotDN
  · exact mapM_allowed NotDN _ _ (fun level => maskedLevel_dn _ _)
  · intro _
    exact pure_allowed _ _
theorem keygen_dn : AllQueriesSatisfy keygen NotDN := by
  unfold keygen
  apply bind_allowed NotDN keygenPayload_dn
  intro generated
  exact bind_allowed NotDN (privateMac_dn _) fun _ => pure_allowed _ _
theorem topPath_dn (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDN := by
  unfold topPath
  exact mapM_allowed NotDN _ _ fun level =>
    bind_allowed NotDN (mask_dn _ _) fun _ => pure_allowed _ _
theorem signTop_dn (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NotDN := by
  unfold signTop
  exact bind_allowed NotDN (buildLeafTop_dn _ _ _) fun _ =>
    bind_allowed NotDN (topPath_dn _ _) fun _ => pure_allowed _ _
end DN
def nonceHalf (m : Message) : ChainGraph.HalfCoordinate := (.inr (.inl m), 0)
theorem nonceHalf_not_secret (m : Message) : nonceHalf m ∉ Set.range CanonGraph.secretCoordinate := by
  rintro ⟨i, hi⟩
  have h1 := congrArg Prod.fst hi
  cases i with
  | inl a => cases h1
  | inr f => cases h1
def nonceOther (m : Message) : CanonGraph.OtherHalf := ⟨nonceHalf m, nonceHalf_not_secret m⟩
section Rest
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyFree : DecidableEq T3.Cache := Classical.decEq _
noncomputable def digestOf (ω : Omega U) : digestInputs → HashOutput := fun x => finiteHashAnswer ∅ U ω.residual x.val
def nonceOf (ω : Omega U) : Message → Digest := fun m => ω.other (nonceOther m)
end Rest
end SigGolfCandidate.T3.Security.BPair
