import SigGolfCandidate.T3.Secc.PairGuessLazyDefs

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
theorem not_digest_of_hdr {x : HashInput} {t l tr p ix : Nat} (hx : Extract.hdrBlock x = bytesLE 16 (header t l tr p ix))
    (_ht : t % 256 ≠ 12) : x ∉ digestInputs :=
  not_digest_of_marker hx (by rw [header_marker]; decide)
theorem not_digest_prefix (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 12) :
    pad64 (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest) ∉ digestInputs := by
  refine not_digest_of_hdr (t := t) (l := l) (tr := tr) (p := p) (ix := ix) ?_ ht
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega)]
  exact Extract.hdrBlock_prefix _ _ _
theorem probeInput_not_digest (f : FtsCoord) (c : Digest) : probeInput f c ∉ digestInputs :=
  not_digest_of_hdr (hdrBlock_probeInput f c) (by decide)
section DN
open SourceQueries
theorem shortHash_dn (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 12) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) NotDN := by
  unfold shortHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr (not_digest_prefix a l tr p ix rest ht))
    fun _ => pure_allowed _ _
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
theorem chain_dn (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NotDN := by
  unfold chain
  exact foldlM_allowed NotDN _ _ (fun v step => chainStep_dn lay tree leaf i step v) value
theorem leafHash_dn (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDN := by
  unfold leafHash shortHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_marker (Extract.hdrBlock_leafInput lay tree leaf ends) (by rw [leafTweak_marker]; decide)))
    fun _ => pure_allowed _ _
theorem nodeHash_dn {tag : Nat} (lay tree heap : Nat) (left right : Digest) (_ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDN := by
  rw [nodeHash_eq_shortHash]
  unfold shortHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_marker (by rw [pad64_nodeInputP, nodeInputP]; exact Extract.hdrBlock_block4 _ _ _ _)
      (nodeTweak_marker_ne_zero _ _ _ _)))
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
theorem keygenPayload_dn : AllQueriesSatisfy keygenPayload NotDN := by
  unfold keygenPayload
  apply bind_allowed NotDN (buildTree_dn _ _ _ _)
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
theorem forestPk_dn (index : Nat) (roots : List Digest) : AllQueriesSatisfy (forestPk index roots) NotDN := by
  unfold forestPk
  exact shortHash_dn _ _ _ _ _ _ (by decide)
theorem topPath_dn (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDN := by
  unfold topPath
  exact mapM_allowed NotDN _ _ fun level =>
    bind_allowed NotDN (mask_dn _ _) fun _ => pure_allowed _ _
theorem signTop_dn (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NotDN := by
  unfold signTop
  exact bind_allowed NotDN (buildLeaf_dn _ _ _ _ _) fun _ =>
    bind_allowed NotDN (topPath_dn _ _) fun _ => pure_allowed _ _
theorem ftsLeaf_dn (index coord leaf : Nat) (secret : Digest) : AllQueriesSatisfy (ftsLeaf index coord leaf secret) NotDN := by
  unfold ftsLeaf
  rw [zero16_eq]
  exact shortHash_dn 0 _ _ _ _ _ (by decide)
theorem buildFts_dn (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) NotDN := by
  unfold buildFts
  apply bind_allowed NotDN
  · apply foldlM_allowed NotDN
    intro state pair
    apply bind_allowed NotDN (privatePair_dn _ _ _ _ _)
    intro seeds
    obtain ⟨left, right⟩ := seeds
    exact bind_allowed NotDN (ftsLeaf_dn _ _ _ _) fun _ =>
      bind_allowed NotDN (ftsLeaf_dn _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    exact bind_allowed NotDN (buildLevels_dn _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem signForest_dn (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (Correctness.signForest index chosen) NotDN := by
  unfold Correctness.signForest
  apply foldlM_allowed NotDN
  intro state coord
  apply bind_allowed NotDN (buildFts_dn _ _)
  intro built
  obtain ⟨levels, secrets⟩ := built
  exact pure_allowed _ _
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
def SameRest (ω₁ ω₂ : Omega U) : Prop :=
  ω₁.seeds = ω₂.seeds ∧ ω₁.labels = ω₂.labels ∧
    (∀ x : U, x.val ∉ digestInputs → ω₁.residual x = ω₂.residual x) ∧
    (∀ h : CanonGraph.OtherHalf, (∀ m, h ≠ nonceOther m) → ω₁.other h = ω₂.other h)
theorem secrets_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (fts : FtsCoord → Digest) :
    ω₁.secrets fts = ω₂.secrets fts := by
  funext i
  cases i with
  | inl a => exact congrFun h.1 a
  | inr p => rfl
theorem private_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (fts : FtsCoord → Digest) (c : Coordinate)
    (hc : ∀ m, c ≠ .inr (.inl m)) :
    CanonGraph.privateEquiv.symm (ω₁.secrets fts, ω₁.other) c = CanonGraph.privateEquiv.symm (ω₂.secrets fts, ω₂.other) c := by
  have hhalf : ∀ k : Fin 2, CanonGraph.splitEquiv.symm (ω₁.secrets fts, ω₁.other) (c, k) =
      CanonGraph.splitEquiv.symm (ω₂.secrets fts, ω₂.other) (c, k) := by
    intro k
    by_cases hr : (c, k) ∈ Set.range CanonGraph.secretCoordinate
    · obtain ⟨i, hi⟩ := hr
      rw [← hi, splitEquiv_symm_secret, splitEquiv_symm_secret, secrets_sameRest h fts]
    · rw [splitEquiv_symm_other _ _ _ hr, splitEquiv_symm_other _ _ _ hr]
      apply h.2.2.2
      intro m he
      have := congrArg (fun o : CanonGraph.OtherHalf => o.1.1) he
      exact hc m this
  rw [privateEquiv_symm_apply, privateEquiv_symm_apply, hhalf 0, hhalf 1]
theorem residual_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (x : HashInput) (hx : x ∉ digestInputs) :
    finiteHashAnswer ∅ U ω₁.residual x = finiteHashAnswer ∅ U ω₂.residual x := by
  by_cases hxU : x ∈ U
  · rw [finiteHashAnswer_none ∅ U _ _ hxU rfl, finiteHashAnswer_none ∅ U _ _ hxU rfl]
    exact h.2.2.1 ⟨x, hxU⟩ hx
  · simp only [finiteHashAnswer, dif_neg hxU]
end Rest
end SigGolfCandidate.T3.Security.BPair
