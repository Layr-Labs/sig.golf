import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableProducts
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableObservationErasure
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsContactTrace
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTracePotential

section



section
namespace SphincsSecurity.OtsCode
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def decodingDigests (words : Finset Encoding) : Finset Digest :=
  Finset.univ.filter fun digest => ∃ word ∈ words, decode digest = some word
theorem mem_decodingDigests {words : Finset Encoding} {digest : Digest} :
    digest ∈ decodingDigests words ↔ ∃ word ∈ words, decode digest = some word := by
  simp only [decodingDigests, Finset.mem_filter, Finset.mem_univ, true_and]
theorem decodingDigests_card_le (words : Finset Encoding) : (decodingDigests words).card ≤ words.card := by
  apply Finset.card_le_card_of_injOn (fun digest => (decode digest).getD defaultWord)
  · intro digest hd
    obtain ⟨word, hw, hdecode⟩ := mem_decodingDigests.mp hd
    simpa only [hdecode, Option.getD_some, Finset.mem_coe] using hw
  · intro left hl right hr he
    obtain ⟨leftWord, _, hleft⟩ := mem_decodingDigests.mp hl
    obtain ⟨rightWord, _, hright⟩ := mem_decodingDigests.mp hr
    simp only [hleft, hright, Option.getD_some] at he
    exact decode_some_injective hleft (by rw [he]; exact hright)
theorem decodingDigests_uniform_le (words : Finset Encoding) :
    Pr[fun output : HashOutput => truncateHash output ∈ decodingDigests words | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (words.card : ENNReal) / Fintype.card Digest := by
  rw [probEvent_uniform_truncateHash_mem]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (decodingDigests_card_le words)) _
end SphincsSecurity.OtsCode
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
def FreshEncodingSupport (reference : Encoding) (allowed : Finset HashOutput) : Prop :=
  allowed = Finset.univ ∨ ∀ output ∈ allowed, decodeEncodingOutput output = none ∨ decodeEncodingOutput output = some reference
theorem firstSuccess_allowed_fresh {n : Nat} (index : Fin n) (reference : Encoding) (coordinate : Fin n) :
    FreshEncodingSupport reference (FirstSuccessTable.allowed decodeEncodingOutput index reference coordinate) := by
  unfold FirstSuccessTable.allowed
  split_ifs with hlt heq
  · exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
  · exact Or.inr fun output ho => Or.inr ((FirstSuccessTable.mem_fiber _ _ _).mp ho)
  · exact Or.inl rfl
theorem freshEncodingSupport_probability_le (reference : Encoding) (targets : Finset Encoding) (href : reference ∉ targets)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests targets | PMF.uniformOfFinset allowed ha] ≤
      (targets.card : ENNReal) / Fintype.card Digest := by
  rcases hallowed with rfl | hrestricted
  · have h := OtsCode.decodingDigests_uniform_le targets
    simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply,
      Finset.mem_univ, if_true, Finset.card_univ] using h
  · have hzero : Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests targets |
        PMF.uniformOfFinset allowed ha] = 0 := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro output
      by_cases hm : output ∈ allowed
      · have hn : truncateHash output ∉ OtsCode.decodingDigests targets := by
          intro hd
          obtain ⟨word, hw, hdecode⟩ := OtsCode.mem_decodingDigests.mp hd
          change decodeEncodingOutput output = some word at hdecode
          rcases hrestricted output hm with hi | hr
          · rw [hi] at hdecode
            contradiction
          · have he : reference = word := Option.some.inj (hr.symm.trans hdecode)
            exact href (he ▸ hw)
        exact if_neg hn
      · simp only [PMF.uniformOfFinset_apply, if_neg hm, ite_self]
    rw [hzero]
    exact zero_le
theorem freshEncodingSupport_neighbor_le (reference : Encoding) (lowered : ChainIndex)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests (OtsCode.unitNeighbors reference lowered) |
      PMF.uniformOfFinset allowed ha] ≤ (OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  have href : reference ∉ OtsCode.unitNeighbors reference lowered := by
    intro h
    exact (OtsCode.mem_unitNeighbors.mp h).ne rfl
  exact (freshEncodingSupport_probability_le reference _ href allowed ha hallowed).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (OtsCode.unitNeighbors_card_le reference lowered)) _)
theorem freshEncodingSupport_all_neighbors_le (reference : Encoding)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ OtsCode.decodingDigests (OtsCode.allUnitNeighbors reference) |
      PMF.uniformOfFinset allowed ha] ≤ (OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  have href : reference ∉ OtsCode.allUnitNeighbors reference := by
    intro h
    obtain ⟨lowered, ht⟩ := OtsCode.mem_allUnitNeighbors.mp h
    exact ht.ne rfl
  exact (freshEncodingSupport_probability_le reference _ href allowed ha hallowed).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (OtsCode.allUnitNeighbors_card_le reference)) _)
end SphincsSecurity.Concrete
end
end

section





section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def encodingSelectionRows (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  match selection with
  | none => fun _ => FirstSuccessTable.invalid decodeEncodingOutput
  | some (index, word) => FirstSuccessTable.allowed decodeEncodingOutput index word
noncomputable def encodingSelectionAllowed (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  if ∀ coordinate, (encodingSelectionRows selection coordinate).Nonempty then encodingSelectionRows selection
  else fun _ => Finset.univ
theorem encodingSelectionAllowed_nonempty (selection : ReferenceSelection) :
    ∀ coordinate, (encodingSelectionAllowed selection coordinate).Nonempty := by
  unfold encodingSelectionAllowed
  split_ifs with hrows
  · exact hrows
  · exact fun _ => Finset.univ_nonempty
theorem encodingSelectionAllowed_fresh (selection : ReferenceSelection) (dummy : Encoding) (coordinate : Fin encodingAttemptLimit) :
    FreshEncodingSupport ((selection.map Prod.snd).getD dummy) (encodingSelectionAllowed selection coordinate) := by
  unfold encodingSelectionAllowed
  split_ifs
  · cases selection with
    | none => exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
    | some selected =>
        obtain ⟨index, word⟩ := selected
        exact firstSuccess_allowed_fresh index word coordinate
  · exact Or.inl rfl
private theorem uniformTable_rows_eq {rows rows' : Fin encodingAttemptLimit → Finset HashOutput} (h : rows = rows')
    (hrows : ∀ coordinate, (rows coordinate).Nonempty) (hrows' : ∀ coordinate, (rows' coordinate).Nonempty) :
    uniformTable rows hrows = uniformTable rows' hrows' := by
  subst h
  rfl
theorem encoding_afterSelect_complete (selection : ReferenceSelection) :
    𝒮[FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection] =
      complete (encodingSelectionAllowed selection) := by
  rw [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection)]
  have hafter : FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection =
      FirstSuccessTable.constrained (encodingSelectionRows selection) := by
    cases selection with
    | none => rfl
    | some selected =>
        obtain ⟨index, word⟩ := selected
        rfl
  rw [hafter, FirstSuccessTable.constrained]
  split_ifs with hrows
  · rw [uniformTable_rows_eq (show encodingSelectionRows selection = encodingSelectionAllowed selection from
      (if_pos hrows).symm) hrows (encodingSelectionAllowed_nonempty selection)]
  · rw [FirstSuccessTable.full, uniformTable_rows_eq (show (fun _ => Finset.univ) = encodingSelectionAllowed selection from
      (if_neg hrows).symm) _ (encodingSelectionAllowed_nonempty selection)]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def encodingFamilyAllowed (selections : ReferenceFamily) (row : EncodingRow) : Finset HashOutput :=
  encodingSelectionAllowed (selections row.1) row.2
theorem encodingFamilyAllowed_nonempty (selections : ReferenceFamily) :
    ∀ row, (encodingFamilyAllowed selections row).Nonempty :=
  fun row => encodingSelectionAllowed_nonempty (selections row.1) row.2
theorem encoding_afterSelect_uniform (selection : ReferenceSelection) :
    FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection =
      uniformTable (encodingSelectionAllowed selection) (encodingSelectionAllowed_nonempty selection) := by
  apply PMF.ext
  intro table
  have h := congrArg (fun law : SPMF (Fin encodingAttemptLimit → HashOutput) => law table)
    (encoding_afterSelect_complete selection)
  simpa only [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection), PMF.evalSPMF_eq, SPMF.liftM_apply] using h
theorem encoding_family_uniform (selections : ReferenceFamily) :
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).map Function.uncurry =
        uniformTable (encodingFamilyAllowed selections) (encodingFamilyAllowed_nonempty selections) := by
  simp only [FirstSuccessFamily.afterSelect, encoding_afterSelect_uniform, uniformTable_eq_product]
  exact FinitePmfProduct.uncurry (fun position coordinate =>
    PMF.uniformOfFinset (encodingSelectionAllowed (selections position) coordinate)
      (encodingSelectionAllowed_nonempty (selections position) coordinate))
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.UniformTableSplit
open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Index Cell Answer : Type} (embed : Index → Cell) (hinj : Function.Injective embed)
theorem join_eq_iff (table : Cell → Answer) (rows : Index → Answer) (outside : Outside embed → Answer) :
    table = join embed hinj rows outside ↔ rows = table ∘ embed ∧ outside = fun cell : Outside embed => table cell.val := by
  constructor
  · intro heq
    subst table
    constructor
    · funext index
      exact (join_embed embed hinj rows outside index).symm
    · funext cell
      exact (join_outside embed hinj rows outside cell).symm
  · rintro ⟨rfl, rfl⟩
    exact (join_split embed hinj table).symm
attribute [local irreducible] join
section Mass
attribute [local instance 10000] Classical.propDecidable
theorem bind_map_join_apply (left : PMF (Index → Answer)) (right : PMF (Outside embed → Answer)) (table : Cell → Answer) :
    (left.bind fun rows => right.map (join embed hinj rows)) table =
      left (table ∘ embed) * right (fun cell => table cell.val) := by
  simp only [PMF.bind_apply, PMF.map_apply]
  rw [tsum_eq_single (table ∘ embed)]
  · rw [tsum_eq_single (fun cell : Outside embed => table cell.val)]
    · rw [if_pos (join_split embed hinj table).symm]
    · intro outside hne
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table _ outside).mp h).2)
  · intro rows hne
    have hz : (∑' outside : Outside embed → Answer,
        if table = join embed hinj rows outside then right outside else 0) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro outside
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table rows outside).mp h).1)
    rw [hz, mul_zero]
end Mass
variable [Fintype Index] [Fintype Cell] [DecidableEq Cell]
include hinj in
theorem prod_embed_mul_outside {M : Type} [CommMonoid M] (f : Cell → M) :
    (∏ index, f (embed index)) * (∏ cell : Outside embed, f cell.val) = ∏ cell, f cell := by
  letI : Fintype (Set.range embed) := Subtype.fintype (Set.range embed)
  have he : (∏ index, f (embed index)) = ∏ cell : Set.range embed, f cell.val :=
    Fintype.prod_equiv (Equiv.ofInjective embed hinj) _ _ (fun _ => rfl)
  rw [he]
  convert Fintype.prod_subtype_mul_prod_subtype (Set.range embed) f using 1
  congr 1
  exact Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
variable [DecidableEq Index] [Fintype Answer]
theorem product_join (left : Index → PMF Answer) (right : Outside embed → PMF Answer) :
    (FinitePmfProduct.law left).bind (fun rows => (FinitePmfProduct.law right).map (join embed hinj rows)) =
      FinitePmfProduct.law (join embed hinj left right) := by
  apply PMF.ext
  intro table
  rw [bind_map_join_apply]
  simp only [FinitePmfProduct.apply]
  have hp := prod_embed_mul_outside embed hinj (fun cell => join embed hinj left right cell (table cell))
  simpa only [join_embed, join_outside, Function.comp_def] using hp
variable [DecidableEq Answer]
omit [Fintype Cell] [DecidableEq Index] [Fintype Answer] [DecidableEq Answer] in
theorem join_nonempty (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    ∀ cell, (join embed hinj left right cell).Nonempty := by
  intro cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    rw [join_embed]
    exact hl index
  · change (join embed hinj left right (⟨cell, hc⟩ : Outside embed).val).Nonempty
    rw [join_outside]
    exact hr ⟨cell, hc⟩
theorem uniformTable_join (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    (uniformTable left hl).bind (fun rows => (uniformTable right hr).map (join embed hinj rows)) =
      uniformTable (join embed hinj left right) (join_nonempty embed hinj left right hl hr) := by
  simp only [uniformTable_eq_product, product_join]
  apply congrArg FinitePmfProduct.law
  funext cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    simp only [join_embed]
  · change join embed hinj _ _ (⟨cell, hc⟩ : Outside embed).val = _
    rw [join_outside]
    have hrow := join_outside embed hinj left right (⟨cell, hc⟩ : Outside embed)
    simp only [hrow]
end SphincsSecurity.Concrete.UniformTableSplit
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs UniformTableSplit.join
noncomputable def referenceEncodingAllowed (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : canonicalEncodingInputs parameter → Finset HashOutput :=
  UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
    (encodingFamilyAllowed selections) (fun _ => Finset.univ)
theorem referenceEncodingAllowed_nonempty (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : ∀ cell, (referenceEncodingAllowed parameter messages selections cell).Nonempty :=
  UniformTableSplit.join_nonempty _ _ _ _ (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)
noncomputable def referenceEncodingPrior (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : PMF (canonicalEncodingInputs parameter → HashOutput) :=
  (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
    (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside (referenceFamilyCell parameter messages) → HashOutput)).map
      (UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
        (Function.uncurry rows)))
theorem referenceEncodingPrior_uniform (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    referenceEncodingPrior parameter messages selections =
      uniformTable (referenceEncodingAllowed parameter messages selections)
        (referenceEncodingAllowed_nonempty parameter messages selections) := by
  have h := UniformTableSplit.uniformTable_join (referenceFamilyCell parameter messages)
    (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => Finset.univ)
    (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)
  rw [uniformTable_univ, ← encoding_family_uniform selections, PMF.bind_map] at h
  exact h
theorem referenceEncodingPrior_complete (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    𝒮[referenceEncodingPrior parameter messages selections] = complete (referenceEncodingAllowed parameter messages selections) := by
  rw [referenceEncodingPrior_uniform, complete_of_nonempty _ (referenceEncodingAllowed_nonempty parameter messages selections)]
theorem referenceEncodingAllowed_fresh (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (cell : canonicalEncodingInputs parameter)
    (position : EncodingPosition) (hposition : AtEncodingPosition parameter cell.val position) :
    FreshEncodingSupport (referenceFamilyWords selections dummy position.lay position.tree position.leafIdx)
      (referenceEncodingAllowed parameter messages selections cell) := by
  by_cases hc : cell ∈ Set.range (referenceFamilyCell parameter messages)
  · obtain ⟨row, rfl⟩ := hc
    have hp := atEncodingPosition_unique hposition
      (show AtEncodingPosition parameter (referenceFamilyCell parameter messages row).val row.1 from ⟨_, rfl⟩)
    subst position
    rw [referenceEncodingAllowed, UniformTableSplit.join_embed]
    exact encodingSelectionAllowed_fresh (selections row.1) (dummy row.1.lay row.1.tree row.1.leafIdx) row.2
  · have hrow := UniformTableSplit.join_outside (referenceFamilyCell parameter messages)
      (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => (Finset.univ : Finset HashOutput))
      (⟨cell, hc⟩ : UniformTableSplit.Outside (referenceFamilyCell parameter messages))
    exact Or.inl hrow
end SphincsSecurity.Concrete
end
end

section







section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs frontierTreeNode referenceEncodingSearch boundaryEval publicDigestLoop
def AgreeOutsideEncoding (parameter : PublicParameter) (f g : QueryImpl HashSpec Id) : Prop :=
  ∀ input, input ∉ canonicalEncodingInputs parameter → f input = g input
theorem AgreeOutsideEncoding.domain {parameter : PublicParameter} {f g : QueryImpl HashSpec Id}
    (h : AgreeOutsideEncoding parameter f g) (domain : HashDomain)
    (htag : (hashDomainFields domain).tag ≠ 4#8) (payload : HashInput) :
    f (tweakableHashInput parameter domain payload) = g (tweakableHashInput parameter domain payload) := by
  apply h
  intro hinput
  rw [canonicalEncodingInputs] at hinput
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hinput
  obtain ⟨position, pair, heq⟩ := hinput
  exact htag (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain
    (.encoding position.lay position.tree position.leafIdx) payload _ heq.symm)
namespace AgreeOutsideEncoding
variable {parameter : PublicParameter} {f g : QueryImpl HashSpec Id}
  (h : AgreeOutsideEncoding parameter f g)
include h
theorem frontierTreeNode (lay : Layer) (tree : TreeIndex) (words : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (Concrete.frontierTreeNode parameter lay tree words frontier level nodeIdx) =
      evalWithAnswerFn g (Concrete.frontierTreeNode parameter lay tree words frontier level nodeIdx) := by
  apply eval_frontierTreeNode_congr
  · intro leaf chainIdx step _ input
    exact congrArg truncateHash (h.domain (.chain lay tree leaf chainIdx step) (by simp only [hashDomainFields, tweakFields]; decide) (digestBytes input))
  · intro leaf payload
    exact congrArg truncateHash (h.domain (.leaf lay tree leaf) (by simp only [hashDomainFields, tweakFields]; decide) payload)
  · intro level nodeIdx payload
    exact congrArg truncateHash (h.domain (.node lay tree level nodeIdx) (by simp only [hashDomainFields, tweakFields]; decide) payload)
theorem frontierTreePath (lay : Layer) (tree : TreeIndex) (words : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (Concrete.frontierTreePath parameter lay tree words frontier leaf) =
      evalWithAnswerFn g (Concrete.frontierTreePath parameter lay tree words frontier leaf) := by
  simp only [Concrete.frontierTreePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs
  · exact h.frontierTreeNode _ _ _ _ _ _
  · rfl
theorem ftsNode (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (Concrete.ftsNode parameter index tree secret level nodeIdx) =
      evalWithAnswerFn g (Concrete.ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      simp only [ftsNode_zero_eq, ftsLeafHash, eval_tweakableHash]
      exact congrArg truncateHash (h.domain (.ftsLeaf index tree _) (by simp only [hashDomainFields, tweakFields]; decide) _)
  | succ level ih =>
      simp only [ftsNode_succ_eq, evalWithAnswerFn_bind, ih, eval_tweakableHash]
      exact congrArg truncateHash (h.domain (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx)) (by simp only [hashDomainFields, tweakFields]; decide) _)
theorem ftsOpen (index : Index) (leaves : IndexGroup → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (Concrete.ftsOpen parameter index leaves secret) =
      evalWithAnswerFn g (Concrete.ftsOpen parameter index leaves secret) := by
  rw [eval_ftsOpen, eval_ftsOpen]
  exact congrArg (honestFts leaves (secret porsTree)) (funext fun level => funext fun nodeIdx =>
    h.ftsNode _ _ _ _ _)
theorem publicDigestLoop (root : Digest) (message : Message) (attempts : Nat) :
    fixedBoundaryRun parameter f (Concrete.publicDigestLoop parameter root message attempts) =
      fixedBoundaryRun parameter g (Concrete.publicDigestLoop parameter root message attempts) := by
  have hattempt (randomness : Randomness) :
      boundaryEval parameter f (publicSignAttempt parameter root message randomness) =
        boundaryEval parameter g (publicSignAttempt parameter root message randomness) := by
    have hinput := h.domain .message (by simp only [hashDomainFields, tweakFields]; decide) (messageDigestPayload root message randomness)
    simp [publicSignAttempt, messageDigest, oracleHash, boundaryEval, QueryImpl.withTrace_apply, hinput]
  induction attempts with
  | zero => simp only [Concrete.publicDigestLoop, fixedBoundaryRun_pure]
  | succ attempts ih =>
      rw [Concrete.publicDigestLoop]
      apply fixedBoundaryRun_bind_congr
      · exact fixedBoundaryRun_lift_prob_eq parameter f g sampleRandomness
      · intro randomness
        apply fixedBoundaryRun_bind_congr
        · rw [fixedBoundaryRun_lift_hash, fixedBoundaryRun_lift_hash, hattempt]
        · intro attempt
          cases attempt with
          | none => exact ih
          | some selected => rfl
theorem frontierSignLayer (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (index : Index) (lay : Layer)
    (hsearch : frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) :
    Concrete.frontierSignLayer parameter f ftsSecret words frontier index lay =
      Concrete.frontierSignLayer parameter g ftsSecret words frontier index lay := by
  simp only [Concrete.frontierSignLayer, hsearch, h.frontierTreePath]
theorem frontierSignAfterDigest (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Concrete.frontierSignAfterDigest parameter f ftsSecret words frontier randomness index leaves =
      Concrete.frontierSignAfterDigest parameter g ftsSecret words frontier randomness index leaves := by
  simp only [Concrete.frontierSignAfterDigest, h.frontierSignLayer ftsSecret words frontier _ _ (hsearch _ _),
    h.ftsOpen]
theorem frontierSigningRun (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) (message : Message) :
    Concrete.frontierSigningRun parameter root f ftsSecret words frontier message =
      Concrete.frontierSigningRun parameter root g ftsSecret words frontier message := by
  simp only [Concrete.frontierSigningRun, frontierSigningRecord, h.publicDigestLoop,
    h.frontierSignAfterDigest ftsSecret words frontier hsearch]
theorem frontierRoot (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    Concrete.frontierRoot parameter f words frontier = Concrete.frontierRoot parameter g words frontier :=
  h.frontierTreeNode _ _ _ _ _ _
end AgreeOutsideEncoding
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs frontierSigningRun frontierRoot
theorem joinEncodingTable_agrees_outside (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (left right : canonicalEncodingInputs parameter → HashOutput)
    (outside : NonencodingRows parameter inputs hencoding) :
    AgreeOutsideEncoding parameter
      (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding left outside))
      (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding right outside)) := by
  intro input hnot
  by_cases hin : input ∈ inputs
  · rw [finiteHashAnswer_none ∅ inputs _ _ hin (by simp), finiteHashAnswer_none ∅ inputs _ _ hin (by simp)]
    let cell : UniformTableSplit.Outside (encodingInputCell parameter inputs hencoding) :=
      ⟨⟨input, hin⟩, UniformTableSplit.inclusion_not_range hencoding ⟨input, hin⟩ hnot⟩
    exact (UniformTableSplit.join_outside _ _ left outside cell).trans
      (UniformTableSplit.join_outside _ _ right outside cell).symm
  · simp only [finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]
theorem frontierLayerSearch_eq_referenceSelection (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (selections : ReferenceFamily)
    (hselected : referenceTableSelection key f = selections) (index : Index) (lay : Layer) :
    frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay =
      referenceSelectionResult (selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) := by
  rw [frontierLayerSearch, eval_frontierLayerMessage key f words frontier hfrontier,
    ← canonicalEncodingSearch_at,
    ← referenceSelectionResult_eq_search key f ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩, hselected]
namespace CausalFrontierProgram
theorem game_eq_of_encoding (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) (h : AgreeOutsideEncoding parameter f g)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) :
    game parameter f ftsSecret words frontier adversary = game parameter g ftsSecret words frontier adversary := by
  have hsign (root : Digest) (message : Message) :
      frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier message =
        frontierSigningRun parameter root (maskOtsPrefixes parameter words g) ftsSecret words frontier message := by
    rw [← frontierSigningRun_eq_of_agree parameter words f _ (maskOtsPrefixes_agrees parameter words f),
      ← frontierSigningRun_eq_of_agree parameter words g _ (maskOtsPrefixes_agrees parameter words g)]
    exact h.frontierSigningRun root ftsSecret words frontier hsearch message
  have himpl (root : Digest) : adversaryImpl parameter root f ftsSecret words frontier =
      adversaryImpl parameter root g ftsSecret words frontier := by
    funext input
    cases input with
    | inl input => rfl
    | inr message => simp only [adversaryImpl_signing, hsign]
  rw [game, game,
    ← frontierRoot_eq_of_agree parameter words f _ (maskOtsPrefixes_agrees parameter words f),
    ← frontierRoot_eq_of_agree parameter words g _ (maskOtsPrefixes_agrees parameter words g),
    h.frontierRoot words frontier]
  simp only [gameRest, adversaryRun, himpl]
end CausalFrontierProgram
theorem joinedEncoding_isSigningFrontier (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (outside : NonencodingRows key.parameter inputs hencoding) (words : OtsReferenceWords) :
    IsSigningFrontier key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
      words (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
        (nonencodingAnswer key.parameter inputs hencoding outside)) words) := by
  have hfrontier := canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret
    (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) words key.root key.top
  rw [canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph] at hfrontier
  rw [hfrontier]
  exact isSigningFrontier_canonical key _ words
theorem joinedEncoding_program_eq (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (left right : canonicalEncodingInputs key.parameter → HashOutput)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (hleft : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding left outside)) = selections)
    (hright : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding right outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let words := referenceFamilyWords selections dummy
    let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) words
    CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding left outside))
        key.ftsSecret words frontier adversary =
      CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding right outside))
        key.ftsSecret words frontier adversary := by
  dsimp only
  apply CausalFrontierProgram.game_eq_of_encoding
  · exact joinEncodingTable_agrees_outside _ _ _ _ _ _
  · intro index lay
    rw [frontierLayerSearch_eq_referenceSelection key _ _ _
      (joinedEncoding_isSigningFrontier key inputs hencoding hgraph left outside _) selections hleft,
      frontierLayerSearch_eq_referenceSelection key _ _ _
      (joinedEncoding_isSigningFrontier key inputs hencoding hgraph right outside _) selections hright]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
noncomputable def referenceRecordedRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain) :=
  let words := referenceFamilyWords selections dummy
  simulateQ (fixedHashWorld f) (QueryCap.recorded (CausalFrontierProgram.game key.parameter f key.ftsSecret words
    (canonicalGraphFrontier key.otsSecret labels words) adversary))
theorem referenceRecordedRest_erased (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.fst <$> referenceRecordedRest key f labels selections dummy adversary =
      referenceFamilyFrontierRest key f labels selections dummy adversary := by
  rw [referenceRecordedRest, ← simulateQ_map, QueryCap.recorded_forget, CausalFrontierProgram.fixed_game,
    referenceFamilyFrontierRest, causalFrontierGame_eq]
abbrev ReferenceRecordedResult := PublicParameter × ReferenceFamily × ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
def ReferenceRecordedResult.erase (result : ReferenceRecordedResult) : ReferenceFamily × (Bool × SigningBoundaryTrace) :=
  (result.2.1, result.2.2.1)
noncomputable def referenceRecordedGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF ReferenceRecordedResult := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩
  let reference ← 𝒮[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒮[referenceRecordedRest key f
    (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (parameter, reference.1, result)
theorem referenceRecordedGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceRecordedResult.erase <$> referenceRecordedGame inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  unfold referenceRecordedGame referenceFamilyGame
  simp only [map_bind, map_pure, ReferenceRecordedResult.erase]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒮[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  rw [← referenceRecordedRest_erased, evalSPMF_map, bind_map_left]
theorem referenceRecordedGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) : result.2.2.1.2.hashCalls ≤ q := by
  apply referenceFamilyGame_hashCalls_le dummy adversary q hbound result.erase
  rw [← referenceRecordedGame_erased, support_map]
  exact ⟨result, hresult, rfl⟩
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
abbrev FrontierObserver (Result : Type) := PublicParameter → OtsReferenceWords → OtsFrontierValues →
  OracleComp OracleWorld (Bool × SigningBoundaryTrace) → OracleComp OracleWorld Result
noncomputable def referenceInstrumentedRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (oracle : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Result :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret labels words
  simulateQ (fixedHashWorld oracle) (observer key.parameter words frontier
    (CausalFrontierProgram.game key.parameter oracle key.ftsSecret words frontier adversary))
abbrev InstrumentedResult (Result : Type) := PublicParameter × ReferenceFamily × Result
noncomputable def referenceInstrumentedGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩
  let reference ← 𝒮[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let oracle := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒮[referenceInstrumentedRest observer key oracle
    (canonicalGraphLabels parameter otsSecret ftsSecret oracle) reference.1 dummy adversary]
  pure (parameter, reference.1, result)
theorem referenceInstrumentedRest_erased {Result : Type} (observer : FrontierObserver Result)
    (erase : Result → Bool × SigningBoundaryTrace)
    (herase : ∀ parameter words frontier computation, erase <$> observer parameter words frontier computation = computation)
    (key : SecretKey) (oracle : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    erase <$> referenceInstrumentedRest observer key oracle labels selections dummy adversary =
      referenceFamilyFrontierRest key oracle labels selections dummy adversary := by
  rw [referenceInstrumentedRest, ← simulateQ_map, herase, CausalFrontierProgram.fixed_game,
    referenceFamilyFrontierRest, causalFrontierGame_eq]
theorem referenceInstrumentedGame_erased {Result : Type} (observer : FrontierObserver Result)
    (erase : Result → Bool × SigningBoundaryTrace)
    (herase : ∀ parameter words frontier computation, erase <$> observer parameter words frontier computation = computation)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => (result.2.1, erase result.2.2)) <$> referenceInstrumentedGame observer inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  unfold referenceInstrumentedGame referenceFamilyGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒮[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  rw [← referenceInstrumentedRest_erased observer erase herase, evalSPMF_map, bind_map_left]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
noncomputable def referenceEncodingRepresentative (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily) :
    canonicalEncodingInputs key.parameter → HashOutput :=
  if h : ∃ encoding, referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections
  then Classical.choose h else fun _ => 0
theorem referenceEncodingRepresentative_selected (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (referenceEncodingRepresentative key inputs hencoding outside selections) outside)) = selections := by
  have hex : ∃ encoding, referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections :=
    ⟨encoding, hselected⟩
  rw [referenceEncodingRepresentative, dif_pos hex]
  exact Classical.choose_spec hex
noncomputable def referenceEncodingProgram (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (dummy : OtsReferenceWords) (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) words
  CausalFrontierProgram.game key.parameter
    (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (referenceEncodingRepresentative key inputs hencoding outside selections) outside)) key.ftsSecret words frontier adversary
theorem referenceEncodingProgram_selected (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let words := referenceFamilyWords selections dummy
    let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) words
    CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
        key.ftsSecret words frontier adversary =
      referenceEncodingProgram key inputs hencoding outside selections dummy adversary :=
  joinedEncoding_program_eq key inputs hencoding hgraph encoding _ outside selections hselected
    (referenceEncodingRepresentative_selected key inputs hencoding outside selections encoding hselected) dummy adversary
noncomputable def referenceEncodingRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Result :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) words
  simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)))
    (observer key.parameter words frontier (referenceEncodingProgram key inputs hencoding outside selections dummy adversary))
theorem referenceEncodingRest_selected {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let oracle := finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)
    referenceInstrumentedRest observer key oracle (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret oracle)
        selections dummy adversary =
      referenceEncodingRest observer key inputs hencoding outside selections encoding dummy adversary := by
  dsimp only
  rw [referenceInstrumentedRest, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  rw [referenceEncodingProgram_selected key inputs hencoding hgraph outside selections encoding hselected]
  rfl
theorem referenceEncodingRest_table {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (selections : ReferenceFamily)
    (table : inputs → HashOutput) (hselected : referenceTableSelection key (finiteHashAnswer ∅ inputs table) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceInstrumentedRest observer key (finiteHashAnswer ∅ inputs table)
        (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret (finiteHashAnswer ∅ inputs table)) selections dummy adversary =
      referenceEncodingRest observer key inputs hencoding (fun cell => table cell.val) selections
        (table ∘ encodingInputCell key.parameter inputs hencoding) dummy adversary := by
  have hjoin : joinEncodingTable key.parameter inputs hencoding (table ∘ encodingInputCell key.parameter inputs hencoding)
      (fun cell => table cell.val) = table := UniformTableSplit.join_split _ _ table
  have hs : referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (table ∘ encodingInputCell key.parameter inputs hencoding) (fun cell => table cell.val))) = selections := by
    rw [hjoin]
    exact hselected
  have h := referenceEncodingRest_selected observer key inputs hencoding hgraph (fun cell => table cell.val) selections
    (table ∘ encodingInputCell key.parameter inputs hencoding) hs dummy adversary
  simpa only [hjoin] using h
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.EncodingObservation
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs Finset.univ
abbrev World (parameter : PublicParameter) :=
  OracleWorld + UniformTableObservation.TableSpec (canonicalEncodingInputs parameter) HashOutput
noncomputable def translate (parameter : PublicParameter) : QueryImpl OracleWorld (OracleComp (World parameter))
  | .inl input => liftM ((World parameter).query (.inl (.inl input)))
  | .inr input =>
      if h : input ∈ canonicalEncodingInputs parameter then liftM ((World parameter).query (.inr ⟨input, h⟩))
      else liftM ((World parameter).query (.inl (.inr input)))
noncomputable def auxiliary (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl OracleWorld SPMF := fun input => 𝒮[fixedHashWorld (nonencodingAnswer parameter inputs hencoding outside) input]
theorem fixed_translate (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (input : OracleWorld.Domain) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary parameter inputs hencoding outside) encoding) (translate parameter input) =
      𝒮[fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside)) input] := by
  cases input with
  | inl input =>
      simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary, fixedHashWorld]
  | inr input =>
      by_cases hc : input ∈ canonicalEncodingInputs parameter
      · have hrow : finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside) input = encoding ⟨input, hc⟩ := by
          rw [finiteHashAnswer_none ∅ inputs _ _ (hencoding hc) (by simp)]
          exact UniformTableSplit.join_embed (encodingInputCell parameter inputs hencoding)
            (encodingInputCell_injective parameter inputs hencoding) encoding outside ⟨input, hc⟩
        simp only [translate, dif_pos hc, simulateQ_spec_query, UniformTableObservation.fixedImpl, fixedHashWorld,
          evalSPMF_pure, hrow]
      · have hrow := joinEncodingTable_agrees_outside parameter inputs hencoding encoding (fun _ => 0) outside input hc
        simp only [translate, dif_neg hc, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary, fixedHashWorld,
          evalSPMF_pure, hrow, nonencodingAnswer]
theorem fixed_run {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (computation : OracleComp OracleWorld Result) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary parameter inputs hencoding outside) encoding)
        (simulateQ (translate parameter) computation) =
      𝒮[simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside))) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih, fixed_translate]
noncomputable def lazyRun {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    SPMF (Result × (canonicalEncodingInputs parameter → Finset HashOutput)) :=
  UniformTableObservation.lazyRun (auxiliary parameter inputs hencoding outside) (simulateQ (translate parameter) computation) allowed
theorem lazyRun_original {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (ha : ∀ cell, (allowed cell).Nonempty) :
    (complete allowed >>= fun encoding =>
      𝒮[simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside))) computation]) =
        Prod.fst <$> lazyRun parameter inputs hencoding outside computation allowed := by
  have h := UniformTableObservation.run_marginal (auxiliary parameter inputs hencoding outside)
    (simulateQ (translate parameter) computation) allowed ha
  simpa only [fixed_run, lazyRun] using h
end SphincsSecurity.Concrete.EncodingObservation
end
end

section









section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def SigningBoundaryTrace.nonmessageCalls (trace : SigningBoundaryTrace) : Nat :=
  trace.toList.countP Option.isNone
theorem SigningBoundaryTrace.nonmessageCalls_mul (first second : SigningBoundaryTrace) :
    (first * second).nonmessageCalls = first.nonmessageCalls + second.nonmessageCalls := by
  simp only [SigningBoundaryTrace.nonmessageCalls, FreeMonoid.toList_mul, List.countP_append]
theorem SigningBoundaryTrace.partition (trace : SigningBoundaryTrace) :
    trace.nonmessageCalls + trace.messageCalls.length = trace.hashCalls := by
  unfold SigningBoundaryTrace.nonmessageCalls SigningBoundaryTrace.messageCalls SigningBoundaryTrace.hashCalls
  generalize trace.toList = records
  induction records with
  | nil => rfl
  | cons entry records ih =>
      cases entry <;> simp_all <;> omega
namespace CausalFrontierProgram
def NonmessageHash (parameter : PublicParameter) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => ¬FtsProbeSimulation.MessageHashInput parameter input
noncomputable instance (parameter : PublicParameter) : DecidablePred (NonmessageHash parameter) := Classical.decPred _
noncomputable def nonmessageTraceCharge (parameter : PublicParameter) : TraceCharge parameter where
  selected := NonmessageHash parameter
  decidable := inferInstance
  cost := SigningBoundaryTrace.nonmessageCalls
  cost_mul := SigningBoundaryTrace.nonmessageCalls_mul
  uniform := by intro input; exact not_false
  step := by
    intro input answer
    cases input with
    | inl input => simp [NonmessageHash, signingBoundaryTrace, SigningBoundaryTrace.nonmessageCalls]
    | inr input =>
        by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input <;>
          simp [NonmessageHash, signingBoundaryTrace, SigningBoundaryTrace.nonmessageCalls, hmessage]
theorem game_nonmessage_recorded_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (QueryCap.recorded (game parameter external ftsSecret words frontier adversary))) :
    QueryCap.calls (NonmessageHash parameter) result.2 + result.1.2.messageCalls.length ≤ result.1.2.hashCalls := by
  have h := QueryCap.recorded_calls_le (NonmessageHash parameter) _ (fun result => result.2.nonmessageCalls)
    (TraceCharge.game_counted_le (nonmessageTraceCharge parameter) external ftsSecret words frontier adversary) result hresult
  exact (Nat.add_le_add_right h _).trans_eq (SigningBoundaryTrace.partition result.1.2)
end CausalFrontierProgram
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete.QueryClass
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def EncodingHash (parameter : PublicParameter) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => ∃ position, AtEncodingPosition parameter input position
def OtherHash (parameter : PublicParameter) (words : OtsReferenceWords) (input : OracleWorld.Domain) : Prop :=
  CausalFrontierProgram.NonmessageHash parameter input ∧ ¬EncodingHash parameter input ∧
    ∀ address, ¬(OtsPrefix.atAddress parameter words address).Selects input
noncomputable instance (parameter : PublicParameter) : DecidablePred (EncodingHash parameter) := Classical.decPred _
noncomputable instance (parameter : PublicParameter) (words : OtsReferenceWords) : DecidablePred (OtherHash parameter words) :=
  Classical.decPred _
theorem encoding_nonmessage (parameter : PublicParameter) (input : OracleWorld.Domain) (hencoding : EncodingHash parameter input) :
    CausalFrontierProgram.NonmessageHash parameter input := by
  cases input with
  | inl input => exact False.elim hencoding
  | inr input =>
      obtain ⟨position, payload, hinput⟩ := hencoding
      rintro ⟨message, hmessage⟩
      have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) (hinput.symm.trans hmessage.symm)).1
      simp only [EncodingPosition.domain, reduceCtorEq] at hdomain
theorem prefix_nonmessage (segment : OtsPrefix) (input : OracleWorld.Domain) (hprefix : segment.Selects input) :
    CausalFrontierProgram.NonmessageHash segment.parameter input := by
  cases input with
  | inl input => exact False.elim hprefix
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hprefix
      have hinput := (segment.parse_some_iff input query).mp hquery
      rintro ⟨message, hmessage⟩
      have hdomain := (tweakableHashInput_injective segment.parameter (by trivial) (by trivial)
        (hinput.symm.trans hmessage.symm)).1
      simp only [reduceCtorEq] at hdomain
theorem prefix_not_encoding (segment : OtsPrefix) (input : OracleWorld.Domain) (hprefix : segment.Selects input) :
    ¬EncodingHash segment.parameter input := by
  cases input with
  | inl input => exact False.elim hprefix
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hprefix
      have hinput := (segment.parse_some_iff input query).mp hquery
      rintro ⟨position, hencoding⟩
      exact hencoding.not_atPosition (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1))
        ⟨digestBytes query.2, hinput⟩
theorem allocation_step (parameter : PublicParameter) (words : OtsReferenceWords) (input : OracleWorld.Domain) :
    (∑ address : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words address).Selects input then 1 else 0) +
        (if EncodingHash parameter input then 1 else 0) + (if OtherHash parameter words input then 1 else 0) =
      if CausalFrontierProgram.NonmessageHash parameter input then 1 else 0 := by
  classical
  by_cases hprefix : ∃ address, (OtsPrefix.atAddress parameter words address).Selects input
  · obtain ⟨address, haddress⟩ := hprefix
    have hsum : (∑ other : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words other).Selects input then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single address]
      · exact if_pos haddress
      · intro other _ hne
        exact if_neg (fun hother => hne (OtsPrefix.atAddress_selects_unique parameter words other address input hother haddress))
      · simp
    have hn := prefix_nonmessage _ input haddress
    have he := prefix_not_encoding _ input haddress
    have ho : ¬OtherHash parameter words input := fun h => h.2.2 address haddress
    simp only [hsum, if_neg he, if_neg ho, if_pos hn, Nat.add_zero]
  · have hnone : ∀ address, ¬(OtsPrefix.atAddress parameter words address).Selects input := by simpa using hprefix
    have hsum : (∑ address : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words address).Selects input then 1 else 0) = 0 := by
      simp only [hnone, if_false, Finset.sum_const_zero]
    rw [hsum, Nat.zero_add]
    by_cases he : EncodingHash parameter input
    · have hn := encoding_nonmessage parameter input he
      simp only [he, hn, OtherHash, not_true_eq_false, and_false, false_and, if_true, if_false, Nat.add_zero]
    · by_cases hn : CausalFrontierProgram.NonmessageHash parameter input <;>
        simp [he, hn, OtherHash, hnone]
theorem allocation_calls (parameter : PublicParameter) (words : OtsReferenceWords) (inputs : List OracleWorld.Domain) :
    (∑ address : OtsPrefix.ChainAddress, QueryCap.calls (OtsPrefix.atAddress parameter words address).Selects inputs) +
        QueryCap.calls (EncodingHash parameter) inputs + QueryCap.calls (OtherHash parameter words) inputs =
      QueryCap.calls (CausalFrontierProgram.NonmessageHash parameter) inputs := by
  induction inputs with
  | nil => simp only [QueryCap.calls_nil, Finset.sum_const_zero, Nat.add_zero]
  | cons input inputs ih =>
      simp only [QueryCap.calls_cons, Finset.sum_add_distrib]
      have h := allocation_step parameter words input
      omega
end SphincsSecurity.Concrete.QueryClass
end
section
namespace SphincsSecurity.OtsCode
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
def backwardWeight (reference candidate : Encoding) : Nat :=
  ∑ index : ChainIndex, ((reference index).val - (candidate index).val)
private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h
private theorem single_of_sum_one (f : ChainIndex → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, ?_⟩
  intro other hne
  have hpair := two_terms_le_sum f hne
  omega
theorem unitNeighbor_of_backwardWeight_one {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate) (hweight : backwardWeight reference candidate = 1) :
    ∃ lowered, UnitNeighborAt reference candidate lowered := by
  obtain ⟨lowered, hlower, hothers⟩ := single_of_sum_one (fun index => (reference index).val - (candidate index).val) hweight
  refine ⟨lowered, hreference, hcandidate, ?_, fun index hne => ?_⟩
  · omega
  · have hdown := hothers index hne
    omega
theorem eq_of_backwardWeight_zero {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate) (hweight : backwardWeight reference candidate = 0) :
    reference = candidate := by
  apply eq_of_le_of_valid hreference hcandidate
  intro index
  have hle : (reference index).val - (candidate index).val ≤ backwardWeight reference candidate := by
    unfold backwardWeight
    exact Finset.single_le_sum (f := fun index : ChainIndex => (reference index).val - (candidate index).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  omega
theorem backwardWeight_two_witness {reference candidate : Encoding} (hweight : 2 ≤ backwardWeight reference candidate) :
    (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  by_cases hlarge : ∃ index, (candidate index).val + 2 ≤ (reference index).val
  · exact Or.inl hlarge
  have hnonzero : ∃ index, (candidate index).val < (reference index).val := by
    by_contra hnone
    push Not at hnone
    have hz : backwardWeight reference candidate = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Nat.sub_eq_zero_of_le (hnone index)
    omega
  obtain ⟨left, hl⟩ := hnonzero
  by_cases hother : ∃ right, left ≠ right ∧ (candidate right).val < (reference right).val
  · obtain ⟨right, hne, hr⟩ := hother
    exact Or.inr ⟨left, right, hne, hl, hr⟩
  · have hzero : ∀ index, index ≠ left → (reference index).val - (candidate index).val = 0 := by
      intro index hne
      have hn : ¬(candidate index).val < (reference index).val := fun hi => hother ⟨index, hne.symm, hi⟩
      omega
    have hsum : backwardWeight reference candidate = (reference left).val - (candidate left).val := by
      apply Finset.sum_eq_single left
      · intro index _ hne
        exact hzero index hne
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    have hn := not_exists.mp hlarge left
    omega
theorem valid_encoding_classification {reference candidate : Encoding} (hreference : Valid reference) (hcandidate : Valid candidate) :
    reference = candidate ∨ (∃ lowered, UnitNeighborAt reference candidate lowered) ∨
      (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  by_cases hzero : backwardWeight reference candidate = 0
  · exact Or.inl (eq_of_backwardWeight_zero hreference hcandidate hzero)
  by_cases hone : backwardWeight reference candidate = 1
  · exact Or.inr (Or.inl (unitNeighbor_of_backwardWeight_one hreference hcandidate hone))
  exact Or.inr (Or.inr (backwardWeight_two_witness (by omega)))
end SphincsSecurity.OtsCode
end
section
namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ OtsContactTrace.contacts canonicalEncodingInputs
def EntryMarker (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (entry : HashInput × HashOutput) : Prop :=
  AtEncodingPosition parameter entry.1 ⟨address.1, address.2.1, address.2.2.1⟩ ∧
    entry.1 ∈ canonicalEncodingInputs parameter ∧
    ∃ candidate, decodeEncodingOutput entry.2 = some candidate ∧
      OtsCode.UnitNeighborAt (words address.1 address.2.1 address.2.2.1) candidate address.2.2.2
theorem entryMarker_encoding_iff (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (message : Digest) (counter : Counter) (output : HashOutput) :
    EntryMarker parameter words address
      (tweakableHashInput parameter (.encoding address.1 address.2.1 address.2.2.1)
        (digestBytes message ++ counterBytes counter), output) ↔
      ∃ candidate, decodeEncodingOutput output = some candidate ∧
        OtsCode.UnitNeighborAt (words address.1 address.2.1 address.2.2.1) candidate address.2.2.2 := by
  have hcounter : counter.toNat < 2 ^ counterBits := counter.isLt
  have hin := encodingRetryInput_mem_canonicalEncodingInputs_wide parameter
    ⟨address.1, address.2.1, address.2.2.1⟩ message ⟨counter.toNat, hcounter⟩
  simp only [encodingRetryInput, BitVec.ofNat_toNat] at hin
  exact and_iff_right ⟨_, rfl⟩ |>.trans (and_iff_right hin)
def Seen (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (trace : OtsContactTrace.Trace) : Prop := ∃ entry ∈ trace.toList, EntryMarker parameter words address entry
theorem entryMarker_unique (parameter : PublicParameter) (words : OtsReferenceWords) (entry : HashInput × HashOutput)
    (left right : OtsPrefix.ChainAddress) (hleft : EntryMarker parameter words left entry) (hright : EntryMarker parameter words right entry) :
    left = right := by
  rcases left with ⟨leftLay, leftTree, leftLeaf, leftChain⟩
  rcases right with ⟨rightLay, rightTree, rightLeaf, rightChain⟩
  obtain ⟨hl, _, leftWord, hdecodeLeft, hneighborLeft⟩ := hleft
  obtain ⟨hr, _, rightWord, hdecodeRight, hneighborRight⟩ := hright
  have hp := atEncodingPosition_unique hl hr
  simp only [EncodingPosition.mk.injEq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  have hw : leftWord = rightWord := Option.some.inj (hdecodeLeft.symm.trans hdecodeRight)
  subst rightWord
  have hc := hneighborLeft.lowered_unique hneighborRight
  cases hc
  rfl
theorem entryMarker_not_contact (parameter : PublicParameter) (words : OtsReferenceWords) (address other : OtsPrefix.ChainAddress)
    (endpoint : Digest) (entry : HashInput × HashOutput) (hm : EntryMarker parameter words address entry) :
    ¬OtsContactTrace.EntryContact (OtsPrefix.atAddress parameter words other) endpoint entry := by
  intro hc
  exact QueryClass.prefix_not_encoding (OtsPrefix.atAddress parameter words other) (.inr entry.1)
    (OtsContactTrace.entryContact_selects _ endpoint entry hc) ⟨_, hm.1⟩
theorem seen_one (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) :
    ¬Seen parameter words address 1 := by simp [Seen]
theorem seen_of (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) (entry : HashInput × HashOutput) :
    Seen parameter words address (FreeMonoid.of entry) ↔ EntryMarker parameter words address entry := by simp [Seen]
theorem seen_mul (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) (before after : OtsContactTrace.Trace) :
    Seen parameter words address (before * after) ↔ Seen parameter words address before ∨ Seen parameter words address after := by
  simp only [Seen, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]
noncomputable def markers (parameter : PublicParameter) (words : OtsReferenceWords) (trace : OtsContactTrace.Trace) :
    Finset OtsPrefix.ChainAddress := Finset.univ.filter fun address => Seen parameter words address trace
theorem mem_markers (parameter : PublicParameter) (words : OtsReferenceWords) (trace : OtsContactTrace.Trace) (address : OtsPrefix.ChainAddress) :
    address ∈ markers parameter words trace ↔ Seen parameter words address trace := by
  simp only [markers, Finset.mem_filter, Finset.mem_univ, true_and]
theorem markers_one (parameter : PublicParameter) (words : OtsReferenceWords) : markers parameter words 1 = ∅ := by
  ext address
  simp only [mem_markers, seen_one, Finset.notMem_empty]
theorem markers_mul (parameter : PublicParameter) (words : OtsReferenceWords) (before after : OtsContactTrace.Trace) :
    markers parameter words (before * after) = markers parameter words before ∪ markers parameter words after := by
  ext address
  simp only [mem_markers, seen_mul, Finset.mem_union]
attribute [local irreducible] markers
end SphincsSecurity.Concrete.OtsEncodingMarker
end
section
namespace SphincsSecurity.Concrete.EncodingObservation
open _root_.OracleComp OracleSpec UniformTableCompletion RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs Finset.univ
def TraceConsistent (parameter : PublicParameter)
    (initial : canonicalEncodingInputs parameter → Finset HashOutput) (trace : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput) : Prop :=
  (∀ cell output, (cell.val, output) ∈ trace.toList → allowed cell = {output}) ∧
    ∀ cell, (∀ output, (cell.val, output) ∉ trace.toList) → allowed cell = initial cell
theorem traceConsistent_one (parameter : PublicParameter)
    (initial : canonicalEncodingInputs parameter → Finset HashOutput) :
    TraceConsistent parameter initial 1 initial := by
  constructor
  · simp
  · intros; rfl
theorem TraceConsistent.outside {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (input : HashInput)
    (houtside : input ∉ canonicalEncodingInputs parameter) (output : HashOutput) :
    TraceConsistent parameter initial (trace * FreeMonoid.of (input, output)) allowed := by
  constructor
  · intro cell answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, _⟩
    · exact h.1 cell answer hentry
    · exact False.elim (houtside (heq ▸ cell.property))
  · intro cell hfresh
    apply h.2 cell
    intro answer hentry
    apply hfresh answer
    exact List.mem_append_left _ hentry
theorem TraceConsistent.disclose {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (output : HashOutput) (houtput : output ∈ allowed cell) :
    TraceConsistent parameter initial (trace * FreeMonoid.of (cell.val, output))
      (discloseTableValue allowed cell output) := by
  constructor
  · intro other answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, rfl⟩
    · by_cases heq : other = cell
      · subst other
        have heq : output = answer := Finset.mem_singleton.mp ((h.1 cell answer hentry) ▸ houtput)
        simp only [discloseTableValue, Function.update_self, heq]
      · rw [discloseTableValue, Function.update_of_ne heq]
        exact h.1 other answer hentry
    · have heq : other = cell := Subtype.ext heq
      subst other
      exact Function.update_self cell {answer} allowed
  · intro other hfresh
    have heq : other ≠ cell := by
      intro heq
      subst other
      exact hfresh output (List.mem_append_right _ (by simp))
    rw [discloseTableValue, Function.update_of_ne heq]
    apply h.2 other
    intro answer hentry
    exact hfresh answer (List.mem_append_left _ hentry)
noncomputable def lazyWorldImpl (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl OracleWorld (StateT (canonicalEncodingInputs parameter → Finset HashOutput) SPMF) :=
  (UniformTableObservation.lazyImpl (auxiliary parameter inputs hencoding outside)).compose (translate parameter)
theorem lazyRun_eq_simulate {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    lazyRun parameter inputs hencoding outside computation allowed =
      (simulateQ (lazyWorldImpl parameter inputs hencoding outside) computation).run allowed := by
  rw [lazyRun, UniformTableObservation.lazyRun, lazyWorldImpl, QueryImpl.simulateQ_compose]
theorem lazyRun_map {Result Next : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (f : Result → Next)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    lazyRun parameter inputs hencoding outside (f <$> computation) allowed =
      (fun result => (f result.1, result.2)) <$> lazyRun parameter inputs hencoding outside computation allowed := by
  simp only [lazyRun_eq_simulate, simulateQ_map, StateT.run_map]
theorem lazyWorldImpl_traceConsistent (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (initial allowed : canonicalEncodingInputs parameter → Finset HashOutput) (trace : OtsContactTrace.Trace)
    (h : TraceConsistent parameter initial trace allowed) (input : OracleWorld.Domain)
    (result : OracleWorld.Range input × (canonicalEncodingInputs parameter → Finset HashOutput))
    (hr : (lazyWorldImpl parameter inputs hencoding outside input).run allowed result ≠ 0) :
    TraceConsistent parameter initial (trace * hashObservationTrace input result.1) result.2 := by
  cases input with
  | inl input =>
      simp only [lazyWorldImpl, QueryImpl.compose, translate, simulateQ_spec_query,
        UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
      obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
      subst result
      simpa only [hashObservationTrace, mul_one] using h
  | inr input =>
      by_cases hc : input ∈ canonicalEncodingInputs parameter
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hc, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, ha, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        have hin : answer ∈ allowed ⟨input, hc⟩ := by
          by_contra hn
          simp only [cell_apply, if_neg hn, ne_eq, not_true_eq_false] at ha
        exact h.disclose ⟨input, hc⟩ answer hin
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_neg hc, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        exact h.outside input hc answer
theorem TraceConsistent.cached_reply {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (previous output : HashOutput) (hp : (cell.val, previous) ∈ trace.toList)
    (ho : UniformTableCompletion.cell (allowed cell) output ≠ 0) : output = previous := by
  rw [h.1 cell previous hp, cell_apply] at ho
  by_contra hn
  simp only [Finset.mem_singleton, hn, if_false, ne_eq, not_true_eq_false] at ho
theorem TraceConsistent.new_reply_probability_le {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (event : HashOutput → Prop) :
    Pr[fun output => event output ∧ (cell.val, output) ∉ trace.toList | UniformTableCompletion.cell (allowed cell)] ≤
      Pr[event | UniformTableCompletion.cell (initial cell)] := by
  by_cases hfresh : ∀ output, (cell.val, output) ∉ trace.toList
  · rw [h.2 cell hfresh]
    exact _root_.probEvent_mono (fun _ _ he => he.1)
  · obtain ⟨previous, hp⟩ := not_forall.mp hfresh
    have hp : (cell.val, previous) ∈ trace.toList := not_not.mp hp
    have hz : Pr[fun output => event output ∧ (cell.val, output) ∉ trace.toList |
        UniformTableCompletion.cell (allowed cell)] = 0 := by
      apply probEvent_eq_zero
      intro output ho he
      have heq := h.cached_reply cell previous output hp ((SPMF.mem_support_iff _ _).mp ho)
      exact he.2 (heq.symm ▸ hp)
    rw [hz]
    exact bot_le
end SphincsSecurity.Concrete.EncodingObservation
end
section
namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs
theorem entryMarker_allowed_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (cell : canonicalEncodingInputs parameter) :
    Pr[fun output : HashOutput => EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output) |
      PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
        (referenceEncodingAllowed_nonempty parameter messages selections cell)] ≤ (OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  by_cases hp : AtEncodingPosition parameter cell.val ⟨address.1, address.2.1, address.2.2.1⟩
  · refine (_root_.probEvent_mono (mx := (liftM (PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
      (referenceEncodingAllowed_nonempty parameter messages selections cell)) : SPMF HashOutput)) ?_).trans (freshEncodingSupport_neighbor_le
      (referenceFamilyWords selections dummy address.1 address.2.1 address.2.2.1) address.2.2.2 _ _
      (referenceEncodingAllowed_fresh parameter messages selections dummy cell _ hp))
    intro output _ hm
    obtain ⟨_, _, candidate, hd, hn⟩ := hm
    exact OtsCode.mem_decodingDigests.mpr ⟨candidate, OtsCode.mem_unitNeighbors.mpr hn, hd⟩
  · have he : (fun output : HashOutput => EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output)) =
        fun _ => False := by
      funext output
      apply propext
      exact ⟨fun hm => hp hm.1, False.elim⟩
    rw [he]
    simp only [probEvent_eq_tsum_ite, if_false, tsum_zero, zero_le]
theorem encodingInput_position (parameter : PublicParameter) (input : HashInput)
    (hc : input ∈ canonicalEncodingInputs parameter) : ∃ position, AtEncodingPosition parameter input position := by
  rw [canonicalEncodingInputs] at hc
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hc
  obtain ⟨position, pair, hinput⟩ := hc
  exact ⟨position, _, hinput.symm⟩
theorem entryMarker_any_allowed_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (cell : canonicalEncodingInputs parameter) :
    Pr[fun output : HashOutput => ∃ address, EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output) |
      PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
        (referenceEncodingAllowed_nonempty parameter messages selections cell)] ≤ (OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  obtain ⟨position, hp⟩ := encodingInput_position parameter cell.val cell.property
  refine (_root_.probEvent_mono (mx := (liftM (PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
      (referenceEncodingAllowed_nonempty parameter messages selections cell)) : SPMF HashOutput)) ?_).trans (freshEncodingSupport_all_neighbors_le
    (referenceFamilyWords selections dummy position.lay position.tree position.leafIdx) _ _
    (referenceEncodingAllowed_fresh parameter messages selections dummy cell position hp))
  intro output _ hm
  obtain ⟨⟨lay, tree, leaf, chain⟩, hposition, _, candidate, hd, hn⟩ := hm
  have he := atEncodingPosition_unique hposition hp
  subst position
  exact OtsCode.mem_decodingDigests.mpr ⟨candidate, OtsCode.mem_allUnitNeighbors.mpr ⟨chain, hn⟩, hd⟩
end SphincsSecurity.Concrete.OtsEncodingMarker
end
section
namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs markers
def NewMarker (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (address : OtsPrefix.ChainAddress) (entry : HashInput × HashOutput) : Prop :=
  EntryMarker parameter words address entry ∧ ¬Seen parameter words address history
theorem NewMarker.not_mem {parameter : PublicParameter} {words : OtsReferenceWords} {history : OtsContactTrace.Trace}
    {address : OtsPrefix.ChainAddress} {entry : HashInput × HashOutput}
    (h : NewMarker parameter words history address entry) : entry ∉ history.toList :=
  fun hin => h.2 ⟨entry, hin, h.1⟩
theorem newMarker_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (address : OtsPrefix.ChainAddress) (row : canonicalEncodingInputs parameter) :
    Pr[fun output => NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ (OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  refine (_root_.probEvent_mono (fun _ _ h => ⟨h.1, h.not_mem⟩)).trans
    ((hc.new_reply_probability_le row (fun output => EntryMarker parameter (referenceFamilyWords selections dummy) address
      (row.val, output))).trans ?_)
  simpa only [cell, dif_pos (referenceEncodingAllowed_nonempty parameter messages selections row), SPMF.probEvent_liftM] using
    entryMarker_allowed_le parameter messages selections dummy address row
theorem newMarker_subset_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (addresses : Finset OtsPrefix.ChainAddress) (row : canonicalEncodingInputs parameter) :
    Pr[fun output => ∃ address ∈ addresses, NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ ((OtsCode.unitNeighborBound : ENNReal) * (addresses.card : ENNReal)) / Fintype.card Digest := by
  have h := (probEvent_exists_finset_le_sum addresses (cell (allowed row))
    (fun address output => NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output))).trans
    (Finset.sum_le_sum fun address _ => newMarker_cell_le parameter messages selections dummy history allowed hc address row)
  simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
theorem newMarker_any_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (row : canonicalEncodingInputs parameter) :
    Pr[fun output => ∃ address, NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ (OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  refine (_root_.probEvent_mono (fun _ _ h => ?_)).trans
    ((hc.new_reply_probability_le row (fun output => ∃ address, EntryMarker parameter (referenceFamilyWords selections dummy) address
      (row.val, output))).trans ?_)
  · obtain ⟨address, hm⟩ := h
    exact ⟨⟨address, hm.1⟩, hm.not_mem⟩
  · simpa only [cell, dif_pos (referenceEncodingAllowed_nonempty parameter messages selections row), SPMF.probEvent_liftM] using
      entryMarker_any_allowed_le parameter messages selections dummy row
section Cardinality
local instance (priority := 11000) : DecidableEq OtsPrefix.ChainAddress := inferInstance
attribute [local instance 10000] Classical.propDecidable
theorem markers_step_card (parameter : PublicParameter) (words : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (entry : HashInput × HashOutput) :
    (markers parameter words (history * FreeMonoid.of entry)).card = (markers parameter words history).card +
      if ∃ address, NewMarker parameter words history address entry then 1 else 0 := by
  rw [markers_mul]
  by_cases hm : ∃ address, NewMarker parameter words history address entry
  · obtain ⟨address, he, hn⟩ := hm
    have hi : address ∈ markers parameter words (FreeMonoid.of entry) := (mem_markers _ _ _ _).mpr ((seen_of _ _ _ _).mpr he)
    have hs : markers parameter words (FreeMonoid.of entry) = {address} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun other ho =>
        entryMarker_unique parameter words entry other address ((seen_of _ _ _ _).mp ((mem_markers _ _ _ _).mp ho)) he⟩
    have ha : address ∉ markers parameter words history := fun hin => hn ((mem_markers _ _ _ _).mp hin)
    rw [if_pos ⟨address, he, hn⟩, hs, Finset.union_singleton, Finset.card_insert_of_notMem ha]
  · have hs : markers parameter words (FreeMonoid.of entry) ⊆ markers parameter words history := by
      intro address hi
      by_contra hn
      exact hm ⟨address, (seen_of _ _ _ _).mp ((mem_markers _ _ _ _).mp hi),
        fun hs => hn ((mem_markers _ _ _ _).mpr hs)⟩
    rw [if_neg hm, Finset.union_eq_left.mpr hs, Nat.add_zero]
end Cardinality
end SphincsSecurity.Concrete.OtsEncodingMarker
end
section
namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs markers
def QueryNewMarker (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : OracleWorld.Domain) (answer : OracleWorld.Range input) : Prop :=
  ∃ address, Seen parameter words address (history * hashObservationTrace input answer) ∧ ¬Seen parameter words address history
theorem queryNewMarker_coin (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : unifSpec.Domain) (answer : unifSpec.Range input) : ¬QueryNewMarker parameter words history (.inl input) answer := by
  simp only [QueryNewMarker, hashObservationTrace, mul_one, and_not_self, exists_false, not_false_eq_true]
theorem queryNewMarker_hash (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : HashInput) (output : HashOutput) :
    QueryNewMarker parameter words history (.inr input) output ↔ ∃ address, NewMarker parameter words history address (input, output) := by
  simp only [QueryNewMarker, hashObservationTrace, seen_mul, seen_of, or_and_right, and_not_self, false_or, NewMarker]
theorem queryNewMarker_any_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history input result.1 |
      (lazyWorldImpl parameter inputs hencoding outside input).run allowed] ≤
      ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      have hz : Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history (.inl input) result.1 |
          (lazyWorldImpl parameter inputs hencoding outside (.inl input)).run allowed] = 0 :=
        probEvent_eq_zero fun result _ => queryNewMarker_coin _ _ _ _ result.1
      rw [hz]
      exact bot_le
  | inr input =>
      by_cases hi : input ∈ canonicalEncodingInputs parameter
      · have he : QueryClass.EncodingHash parameter (.inr input) := encodingInput_position parameter input hi
        simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hi, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, probEvent_map, Function.comp_def,
          queryNewMarker_hash, if_pos he, Nat.cast_one, mul_one]
        exact newMarker_any_cell_le parameter messages selections dummy history allowed hc ⟨input, hi⟩
      · have hz : Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history (.inr input) result.1 |
            (lazyWorldImpl parameter inputs hencoding outside (.inr input)).run allowed] = 0 := by
          apply probEvent_eq_zero
          intro result _ hm
          obtain ⟨_, hm⟩ := (queryNewMarker_hash _ _ _ _ _).mp hm
          exact hi hm.1.2.1
        rw [hz]
        exact bot_le
section Potential
attribute [local instance 10000] Classical.propDecidable
theorem markers_query_potential_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorldImpl parameter inputs hencoding outside input).run allowed] *
      ((markers parameter (referenceFamilyWords selections dummy) (history * hashObservationTrace input result.1)).card : ENNReal)) ≤
      ((markers parameter (referenceFamilyWords selections dummy) history).card : ENNReal) +
        ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      simp only [hashObservationTrace, mul_one, QueryClass.EncodingHash, if_false, Nat.cast_zero,
        mul_zero, add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one
  | inr input =>
      simp only [hashObservationTrace, markers_step_card, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
      apply add_le_add (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)
      simpa only [queryNewMarker_hash, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero] using
        queryNewMarker_any_le parameter inputs hencoding outside messages selections dummy history allowed hc (.inr input)
end Potential
end SphincsSecurity.Concrete.OtsEncodingMarker
end
section
namespace SphincsSecurity.Concrete.UniformTableObservation
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
theorem lazyRun_neverFail {Coordinate Value AuxIndex Result : Type} [DecidableEq Coordinate]
    {auxSpec : OracleSpec AuxIndex} (auxiliary : QueryImpl auxSpec SPMF)
    (haux : ∀ input, NeverFail (auxiliary input))
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    NeverFail (lazyRun auxiliary computation allowed) := by
  induction computation using OracleComp.inductionOn generalizing allowed with
  | pure value => rw [lazyRun_pure]; infer_instance
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          exact ⟨haux input, fun answer _ => ih answer allowed ha⟩
      | inr coordinate =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          constructor
          · rw [cell, dif_pos (ha coordinate)]
            exact ⟨probFailure_of_liftM_PMF _⟩
          · intro answer _
            exact ih answer _ (discloseTableValue_nonempty allowed ha coordinate answer)
end SphincsSecurity.Concrete.UniformTableObservation
namespace SphincsSecurity.Concrete.EncodingObservation
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs OtsEncodingMarker.markers
theorem lazyRun_neverFail {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (ha : ∀ row, (allowed row).Nonempty) : NeverFail (lazyRun parameter inputs hencoding outside computation allowed) := by
  apply UniformTableObservation.lazyRun_neverFail _ _ _ _ ha
  intro input
  exact ⟨probFailure_eq_zero (mx := fixedHashWorld (nonencodingAnswer parameter inputs hencoding outside) input)⟩
noncomputable def encodingCalls (parameter : PublicParameter) (trace : OtsContactTrace.Trace) : Nat :=
  QueryCap.calls (QueryClass.EncodingHash parameter) (trace.toList.map fun entry => .inr entry.1)
theorem encodingCalls_one (parameter : PublicParameter) : encodingCalls parameter 1 = 0 := rfl
theorem encodingCalls_step (parameter : PublicParameter) (input : OracleWorld.Domain) (answer : OracleWorld.Range input)
    (tail : OtsContactTrace.Trace) :
    encodingCalls parameter (hashObservationTrace input answer * tail) =
      (if QueryClass.EncodingHash parameter input then 1 else 0) + encodingCalls parameter tail := by
  cases input with
  | inl input => simp only [hashObservationTrace, one_mul, QueryClass.EncodingHash, if_false, Nat.zero_add]
  | inr input =>
      simp only [encodingCalls, hashObservationTrace, FreeMonoid.toList_mul, FreeMonoid.toList_of,
        List.singleton_append, List.map_cons, QueryCap.calls_cons]
theorem markers_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (ha : ∀ row, (allowed row).Nonempty) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) (history * result.1.2)).card : ENNReal)) ≤
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) history).card : ENNReal) +
        ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
            (encodingCalls parameter result.1.2 : ENNReal) := by
  simp only [lazyRun_eq_simulate]
  apply QueryPause.traced_spmf_potential_le hashObservationTrace (lazyWorldImpl parameter inputs hencoding outside)
    (fun history allowed => TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed ∧
      ∀ row, (allowed row).Nonempty)
    _ _ (fun history _ => (OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) history).card)
    _ (encodingCalls parameter) _ (encodingCalls_one parameter) (encodingCalls_step parameter) _ computation history allowed ⟨hc, ha⟩
  · intro history allowed hi input result hr
    exact ⟨lazyWorldImpl_traceConsistent parameter inputs hencoding outside _ allowed history hi.1 input result hr,
      UniformTableObservation.lazyRun_nonempty (auxiliary parameter inputs hencoding outside) (translate parameter input)
        allowed hi.2 result hr⟩
  · intro computation history allowed hi
    rw [← lazyRun_eq_simulate]
    exact probFailure_eq_zero' (lazyRun_neverFail parameter inputs hencoding outside _ allowed hi.2)
  · intro history allowed hi input
    exact OtsEncodingMarker.markers_query_potential_le parameter inputs hencoding outside messages selections dummy history allowed hi.1 input
theorem markers_initial_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
      (referenceEncodingAllowed parameter messages selections)] *
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) result.1.2).card : ENNReal)) ≤
        ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
            (referenceEncodingAllowed parameter messages selections)] * (encodingCalls parameter result.1.2 : ENNReal) := by
  simpa only [one_mul, OtsEncodingMarker.markers_one, Finset.card_empty, Nat.cast_zero, zero_add] using
    markers_lazyRun_le parameter inputs hencoding outside messages selections dummy computation 1 _
      (traceConsistent_one parameter _) (referenceEncodingAllowed_nonempty parameter messages selections)
end SphincsSecurity.Concrete.EncodingObservation
end
end
