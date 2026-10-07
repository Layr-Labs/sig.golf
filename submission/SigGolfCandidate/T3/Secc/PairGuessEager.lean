import SigGolfCandidate.T3.Secc.PairGuessWorld
import SigGolfCandidate.T3.Secc.WotsTransportTable

section


namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def IsFtsPair (c : Coordinate) : Prop := ∃ f : FtsCoord, c = .inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2))
def FtsFree : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr x) => decodeProbe x = none
  | .inr c => ¬IsFtsPair c
theorem not_isFtsPair_header {t l tr p ix : Nat} (ht : t % 256 ≠ 8) : ¬IsFtsPair (.inl (header t l tr p ix)) := by
  rintro ⟨f, hf⟩
  exact QuerySpace.header_ne_of_tag (by omega) (Sum.inl.inj hf)
theorem decodeProbe_prefix (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 9) :
    decodeProbe (pad64 (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) = none := by
  refine decodeProbe_of_hdr (t := t) (l := l) (tr := tr) (p := p) (ix := ix) ?_ ht
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega)]
  exact Extract.hdrBlock_prefix _ _ _
theorem eval_query' (A : Answers) (input : T3.Spec.Domain) :
    evalWithAnswerFn A (liftM (T3.Spec.query input)) = A input :=
  simulateQ_spec_query A input
theorem eval_congr_allowed {P : T3.Spec.Domain → Prop} {α : Type} {program : M α}
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
theorem shortHash_free (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 9) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) FtsFree := by
  unfold shortHash publicHash
  exact bind_allowed FtsFree ((allQueriesSatisfy_query_iff _ _).mpr (decodeProbe_prefix a l tr p ix rest ht))
    fun _ => pure_allowed _ _
theorem privatePair_free {t : Nat} (l tr p ix : Nat) (ht : t % 256 ≠ 8) :
    AllQueriesSatisfy (privatePair t l tr p ix) FtsFree := by
  unfold privatePair privateHash
  exact bind_allowed FtsFree ((allQueriesSatisfy_query_iff _ _).mpr (not_isFtsPair_header ht))
    fun _ => pure_allowed _ _
theorem privateNonce_free (message : Message) : AllQueriesSatisfy (privateNonce message) FtsFree := by
  unfold privateNonce privateHash
  refine bind_allowed FtsFree ((allQueriesSatisfy_query_iff _ _).mpr ?_) fun _ => pure_allowed _ _
  rintro ⟨f, hf⟩
  cases hf
theorem privateMac_free (region : Region) : AllQueriesSatisfy (privateMac region) FtsFree := by
  have hquery (i : Nat) : AllQueriesSatisfy (privateHash (.inl (header 14 0 0 0 i))) FtsFree := by
    exact (allQueriesSatisfy_query_iff _ _).mpr (not_isFtsPair_header (by decide : 14 % 256 ≠ 8))
  unfold privateMac privateMacKey
  apply bind_allowed FtsFree
  · exact bind_allowed FtsFree (hquery 0) (fun _ => bind_allowed FtsFree (hquery 1) (fun _ => pure_allowed _ _))
  · intro key; exact pure_allowed _ _
theorem chainStep_free (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (chainInput lay tree leaf i step value)) FtsFree := by
  unfold shortHash publicHash
  apply bind_allowed FtsFree
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change decodeProbe (pad64 (chainInput lay tree leaf i step value)) = none
    rw [decodeProbe_eq_none, chainInput_padded]
    intro f c he
    have hh := congrArg Extract.hdrBlock he
    rw [hdrBlock_probeInput] at hh
    change ((chainInput lay tree leaf i step value).drop 16).take 16 = _ at hh
    rw [chainInput_header] at hh
    exact chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ (bytesLE_injective hh)
  · intro _; exact pure_allowed _ _
theorem chain_free (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) FtsFree := by
  unfold chain
  exact foldlM_allowed FtsFree _ _ (fun v step => chainStep_free lay tree leaf i step v) value
theorem mask_free (level index : Nat) : AllQueriesSatisfy (mask level index) FtsFree := by
  unfold mask pairedMask
  exact bind_allowed FtsFree (privatePair_free _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem maskedLevel_free (nodes : List Digest) (level : Nat) :
    AllQueriesSatisfy (maskedLevel nodes level) FtsFree := by
  unfold maskedLevel pairedMask
  apply bind_allowed FtsFree
  · exact mapM_allowed FtsFree _ _ (fun pair => bind_allowed FtsFree (privatePair_free _ _ _ _ (by decide)) (fun _ => pure_allowed _ _))
  · intro _; exact pure_allowed _ _
theorem forestPk_free (index : Nat) (roots : List Digest) : AllQueriesSatisfy (forestPk index roots) FtsFree := by
  unfold forestPk
  exact shortHash_free _ _ _ _ _ _ (by decide)
theorem topPath_free (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) FtsFree := by
  unfold topPath
  exact mapM_allowed FtsFree _ _ fun level =>
    bind_allowed FtsFree (mask_free _ _) fun _ => pure_allowed _ _
end Free
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
theorem splitEquiv_symm_secret (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (i : CanonGraph.SecretIndex) :
    CanonGraph.splitEquiv.symm (s, o) (CanonGraph.secretCoordinate i) = s i := by
  have h := CanonGraph.splitEquiv_fst (CanonGraph.splitEquiv.symm (s, o))
  rw [Equiv.apply_symm_apply] at h
  exact (congrFun h i).symm
theorem splitEquiv_snd (t : ChainGraph.HalfTable) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : (CanonGraph.splitEquiv t).2 ⟨h, hh⟩ = t h := by
  simp [CanonGraph.splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.Set.sumCompl]
  rfl
theorem splitEquiv_symm_other (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : CanonGraph.splitEquiv.symm (s, o) h = o ⟨h, hh⟩ := by
  have e := splitEquiv_snd (CanonGraph.splitEquiv.symm (s, o)) h hh
  rw [Equiv.apply_symm_apply] at e
  exact e.symm
theorem privateEquiv_symm_apply (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (c : Coordinate) :
    CanonGraph.privateEquiv.symm (s, o) c =
      ChainGraph.joinOutput (CanonGraph.splitEquiv.symm (s, o) (c, 0)) (CanonGraph.splitEquiv.symm (s, o) (c, 1)) :=
  rfl
theorem private_free (fts fts' : FtsCoord → Digest) (c : Coordinate) (hc : ¬IsFtsPair c) :
    CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other) c = CanonGraph.privateEquiv.symm (ω.secrets fts', ω.other) c := by
  have hhalf : ∀ h : Fin 2, CanonGraph.splitEquiv.symm (ω.secrets fts, ω.other) (c, h) =
      CanonGraph.splitEquiv.symm (ω.secrets fts', ω.other) (c, h) := by
    intro h
    by_cases hr : (c, h) ∈ Set.range CanonGraph.secretCoordinate
    · obtain ⟨i, hi⟩ := hr
      rw [← hi, splitEquiv_symm_secret, splitEquiv_symm_secret]
      cases i with
      | inl a => rfl
      | inr p =>
          exfalso
          apply hc
          refine ⟨ofLeafPos p, ?_⟩
          have := congrArg Prod.fst hi
          exact this.symm
    · rw [splitEquiv_symm_other _ _ _ hr, splitEquiv_symm_other _ _ _ hr]
  rw [privateEquiv_symm_apply, privateEquiv_symm_apply, hhalf 0, hhalf 1]
theorem secretNat_answers (fts : FtsCoord → Digest) (f : FtsCoord) :
    secretNat (Omega.answers hU ω fts) f.1.val f.2.1.val f.2.2.val = fts f := by
  have hc : CanonGraph.ftsCoordinate (toLeafPos f) =
      (.inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2)), ⟨f.2.2.val % 2, Nat.mod_lt _ (by decide)⟩) := rfl
  have hs := splitEquiv_symm_secret (ω.secrets fts) ω.other (.inr (toLeafPos f))
  change CanonGraph.splitEquiv.symm (ω.secrets fts, ω.other) (CanonGraph.ftsCoordinate (toLeafPos f)) = fts f at hs
  rw [hc] at hs
  unfold secretNat privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (if f.2.2.val % 2 = 0 then (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)
      (.inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2)))).extractLsb' 0 128
    else (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)
      (.inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2)))).extractLsb' 128 128) = fts f
  rw [privateEquiv_symm_apply, ChainGraph.joinOutput_low, ChainGraph.joinOutput_high]
  have h2 := Nat.mod_lt f.2.2.val (by decide : 0 < 2)
  split_ifs with he
  · have e : (⟨f.2.2.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext he
    rw [e] at hs
    exact hs
  · have e : (⟨f.2.2.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 :=
      Fin.ext (by change f.2.2.val % 2 = 1; omega)
    rw [e] at hs
    exact hs
theorem secretAt_answers (fts : FtsCoord → Digest) (f : FtsCoord) : secretAt (Omega.answers hU ω fts) f = fts f :=
  secretNat_answers hU ω fts f
theorem cell_ftsLeaf (s : CanonGraph.Secrets) (p : CanonGraph.FtsLeafPos) (labels : CanonGraph.Labels) :
    CanonGraph.cell s (.ftsLeaf p) labels = probeInput (ofLeafPos p) (CanonGraph.ftsOf s p) := rfl
theorem cell_seeds (s s' : CanonGraph.Secrets) (hs : CanonGraph.seedsOf s = CanonGraph.seedsOf s')
    (node : CanonGraph.Node) (hnode : ∀ p, node ≠ .ftsLeaf p) (labels : CanonGraph.Labels) :
    CanonGraph.cell s node labels = CanonGraph.cell s' node labels := by
  cases node with
  | chain p => simp only [CanonGraph.cell, hs]
  | leaf L =>
      have he : CanonGraph.endLabel s labels L = CanonGraph.endLabel s' labels L := by
        funext i
        simp only [CanonGraph.endLabel, hs]
      simp only [CanonGraph.cell, he]
  | node n => rfl
  | ftsLeaf p => exact absurd rfl (hnode p)
  | ftsNode n => rfl
  | forest i => rfl
include hU in
theorem probeInput_mem (f : FtsCoord) (c : Digest) : probeInput f c ∈ U := by
  apply hU
  have h := CanonGraph.cell_mem (fun _ => c) (.ftsLeaf (toLeafPos f)) (fun _ => 0)
  rwa [cell_ftsLeaf] at h
end Table
theorem list_ext_getD {α : Type} {l l' : List α} (d : α) (hl : l.length = l'.length)
    (h : ∀ n, n < l.length → l.getD n d = l'.getD n d) : l = l' := by
  apply List.ext_getElem hl
  intro n h1 h2
  have := h n h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
theorem levels_ext {levels levels' : List (List Digest)} (hs : Cost.LevelShape 11 11 levels)
    (hs' : Cost.LevelShape 11 11 levels')
    (h : ∀ level, level ≤ 11 → ∀ c, c < 2 ^ (11 - level) → treeValue levels level c = treeValue levels' level c) :
    levels = levels' := by
  apply list_ext_getD [] (by rw [hs.1, hs'.1])
  intro j hj
  have hj' : j ≤ 11 := by rw [hs.1] at hj; omega
  apply list_ext_getD 0 (by rw [hs.2 j hj', hs'.2 j hj'])
  intro c hc
  rw [hs.2 j hj'] at hc
  exact h j hj' c hc
section Levels
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildLevels Correctness.ftsRows
end Levels
theorem selection_bounds (output : HashOutput) (c : Nat) (hc : c < 7) :
    ((selections output).getD c ⟨0, []⟩).bucket < 16 ∧
      ∀ leaf ∈ ((selections output).getD c ⟨0, []⟩).leaves, leaf < 128 := by
  simp only [selections, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some]
  refine ⟨Nat.mod_lt _ (by decide), ?_⟩
  intro leaf hleaf
  rw [List.mem_mergeSort] at hleaf
  simp only [List.mem_map, List.mem_range] at hleaf
  obtain ⟨j, -, rfl⟩ := hleaf
  exact Nat.mod_lt _ (by decide)
def openedValues (fts : FtsCoord → Digest) (output : HashOutput) : List Digest := (openedPositions output).map fts
section Sign
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
theorem forestOpened_answers (fts : FtsCoord → Digest) (output : HashOutput) (c : Fin 7) :
    Correctness.forestOpened (Omega.answers hU ω fts) (output.toNat % 2 ^ 31) c.val
        ((selections output).getD c.val ⟨0, []⟩) =
      (((selections output).getD c.val ⟨0, []⟩).leaves.map fun leaf =>
        (outputIndex output, c, leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf)).map fts := by
  obtain ⟨hb, hl⟩ := selection_bounds output c.val c.isLt
  have hsec : ∀ s (hs : s < 2048),
      (evalWithAnswerFn (Omega.answers hU ω fts) (buildFts (output.toNat % 2 ^ 31) c.val)).2.getD s 0 =
        fts (outputIndex output, c, ⟨s, hs⟩) := by
    intro s hs
    rw [buildFts_secret _ _ _ _ hs]
    exact secretNat_answers hU ω fts (outputIndex output, c, ⟨s, hs⟩)
  unfold Correctness.forestOpened
  generalize evalWithAnswerFn (Omega.answers hU ω fts) (buildFts (output.toNat % 2 ^ 31) c.val) = X at hsec ⊢
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro leaf hleaf
  have hlt : ((selections output).getD c.val ⟨0, []⟩).bucket * 128 + leaf < 2048 := by
    have := hl leaf hleaf; omega
  rw [Function.comp_apply, Function.comp_apply, hsec _ hlt]
  have hidx : (⟨_, hlt⟩ : Fin 2048) = leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf := by
    apply Fin.ext
    simp only [leafIndex]
    exact (Nat.mod_eq_of_lt hlt).symm
  rw [hidx]
theorem forestOpenPrefix_answers (fts : FtsCoord → Digest) (output : HashOutput) :
    Correctness.forestOpenPrefix (Omega.answers hU ω fts) (output.toNat % 2 ^ 31) (selections output) 7 =
      openedValues fts output := by
  unfold Correctness.forestOpenPrefix openedValues openedPositions
  rw [List.map_flatMap, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  exact forestOpened_answers hU ω fts output c
end Sign
section Signer
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessSigner : DecidableEq T3.Cache := Classical.decEq _
noncomputable def signerRho (request : Request) : Digest :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (privateNonce request.message)
noncomputable def signerFound (request : Request) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
    (digestSearch (signerRho hU ω request) request.message 0 attemptLimit)
noncomputable def signerForest (output : HashOutput) : List Digest × List Digest × List Digest :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))
noncomputable def signerLayers (request : Request) (output : HashOutput) : Option (List Pieces) :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (signLayers request.cache (output.toNat % 2 ^ 31) 4
    (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
      (forestPk (output.toNat % 2 ^ 31) (signerForest hU ω output).2.2)))
noncomputable def signWith (published : T3.Cache) (request : Request) (opener : HashOutput → List Digest) :
    Option Signature :=
  if request.cache = published then
    match signerFound hU ω request with
    | some (_, output) =>
        match signerLayers hU ω request output with
        | some pieces => some (Correctness.assembledSignature (signerRho hU ω request)
            (opener output, (signerForest hU ω output).2.1, (signerForest hU ω output).2.2) pieces)
        | none => none
    | none => none
  else none
noncomputable def signerOpened (published : T3.Cache) (request : Request) : List FtsCoord :=
  if request.cache = published then
    match signerFound hU ω request with
    | some (_, output) =>
        match signerLayers hU ω request output with
        | some _ => openedPositions output
        | none => []
    | none => []
  else []
end Signer
end SigGolfCandidate.T3.Security.BPair
end

section



section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Couple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable abbrev fixedW (fts : FtsCoord → Digest) : QueryImpl WSpec ProbComp :=
  SecretGuessObservation.fixedAnswers coinImpl fts
theorem overwrite_map (g : FtsCoord → Digest) (positions : List FtsCoord) (f : FtsCoord) (hf : f ∈ positions) :
    overwrite positions (positions.map g) f = g f := by
  induction positions with
  | nil => cases hf
  | cons first rest ih =>
      unfold overwrite
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      by_cases he : first = f
      · subst he
        simp
      · simp only [he, decide_false]
        exact ih (by simpa [Ne.symm he] using List.mem_cons.mp hf |>.resolve_left (Ne.symm he))
theorem fixed_disclosures (fts : FtsCoord → Digest) (positions : List FtsCoord) :
    simulateQ (fixedW fts) (positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest)) =
      pure (positions.map fts) := by
  induction positions with
  | nil => rfl
  | cons first rest ih =>
      rw [List.mapM_cons, simulateQ_bind, simulateQ_spec_query]
      change (pure (fts first) >>= fun value => simulateQ (fixedW fts) (do
        let values ← rest.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest)
        pure (value :: values))) = _
      rw [pure_bind, simulateQ_bind, ih, pure_bind, simulateQ_pure, List.map_cons]
theorem interactionW_pure (published : T3.Cache) {α : Type} (value : α) :
    interactionW hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionW_coin (published : T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1))) >>= fun coin =>
        interactionW hU ω published (next coin)) := rfl
theorem interactionW_public (published : T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => interactionW hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionW_request (published : T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signW hU ω published request >>= fun signature => interactionW hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programW_pure {β : Type} (value : β) : programW hU ω (pure value : M β) = pure (value, []) := rfl
theorem programW_public {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programW hU ω (liftM (T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => programW hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem interactionT_pure (T : Answers) (published : T3.Cache) {α : Type} (value : α) :
    interactionT T published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionT_coin (T : Answers) (published : T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin => interactionT T published (next coin)) := rfl
theorem interactionT_public (T : Answers) (published : T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (interactionT T published (next (T (.inl (.inr x)))) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)) := rfl
theorem interactionT_request (T : Answers) (published : T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (interactionT T published (next (evalWithAnswerFn T (FullGame.authenticatedSign published request))) >>=
        fun rest => pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ ::
          rest.2.1, rest.2.2)) := rfl
end Couple
section Tracking
open SecretGuessObservation (runWith fixedRun fixedImpl afterTrial afterDisclosure)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
theorem disclosed_append_left (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l1 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_left _ he, rest⟩
theorem disclosed_append_right (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l2 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_right _ he, rest⟩
structure Tracks (fts : FtsCoord → Digest) (before after : WState) (log : QueryLog Requests)
    (entries : List Wots.Entry) : Prop where
  probes : after.probes ≤ before.probes + entries.length
  guesses : before.guesses ⊆ after.guesses
  retired : before.retired ⊆ after.retired
  origin : ∀ f ∈ after.retired, f ∈ before.retired ∨ f ∈ after.guesses ∨ Disclosed (Omega.answers hU ω fts) log f
  queried : ∀ f answer, (probeInput f (fts f), answer) ∈ entries → f ∈ after.retired
theorem Tracks.refl (fts : FtsCoord → Digest) (state : WState) : Tracks hU ω fts state state [] [] :=
  ⟨by simp, Finset.Subset.refl _, Finset.Subset.refl _, fun _ h => Or.inl h, fun _ _ h => by cases h⟩
theorem Tracks.trans {fts : FtsCoord → Digest} {s1 s2 s3 : WState} {l1 l2 : QueryLog Requests}
    {e1 e2 : List Wots.Entry} (first : Tracks hU ω fts s1 s2 l1 e1) (second : Tracks hU ω fts s2 s3 l2 e2) :
    Tracks hU ω fts s1 s3 (l1 ++ l2) (e1 ++ e2) := by
  refine ⟨?_, first.guesses.trans second.guesses, first.retired.trans second.retired, ?_, ?_⟩
  · have := first.probes
    have := second.probes
    simp only [List.length_append]
    omega
  · intro f hf
    rcases second.origin f hf with h | h | h
    · rcases first.origin f h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (second.guesses h))
      · exact Or.inr (Or.inr (disclosed_append_left _ _ _ _ h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (disclosed_append_right _ _ _ _ h))
  · intro f answer h
    rcases List.mem_append.mp h with h | h
    · exact second.retired (first.queried f answer h)
    · exact second.queried f answer h
theorem runWith_bind' {First Result : Type}
    (implementation : QueryImpl WSpec (StateT WState SPMF))
    (first : OracleComp WSpec First) (next : First → OracleComp WSpec Result) (state : WState) :
    runWith implementation (first >>= next) state =
      runWith implementation first state >>= fun middle => runWith implementation (next middle.1) middle.2 := by
  simp only [runWith, simulateQ_bind, StateT.run_bind]
theorem fixedRun_bind_nonzero {First Result : Type} (fts : FtsCoord → Digest) (first : OracleComp WSpec First)
    (next : First → OracleComp WSpec Result) (state : WState) (result : Result × WState)
    (hr : fixedRun env fts (first >>= next) state result ≠ 0) :
    ∃ middle, fixedRun env fts first state middle ≠ 0 ∧ fixedRun env fts (next middle.1) middle.2 result ≠ 0 := by
  unfold fixedRun at hr ⊢
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr
theorem fixedRun_pure_nonzero {Result : Type} (fts : FtsCoord → Digest) (value : Result) (state : WState)
    (result : Result × WState) (hr : fixedRun env fts (pure value) state result ≠ 0) : result = (value, state) := by
  unfold fixedRun at hr
  rw [SecretGuessObservation.runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixed_coin_tracks (fts : FtsCoord → Digest) (n : Nat) (state : WState) (result : Fin (n + 1) × WState)
    (hr : fixedRun env fts (liftM (WSpec.query (.inl n))) state result ≠ 0) : Tracks hU ω fts state result.2 [] [] := by
  unfold fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [fixedImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  exact Tracks.refl hU ω fts state
theorem fixed_disclosures_run (fts : FtsCoord → Digest) (positions : List FtsCoord) (state : WState)
    (result : List Digest × WState)
    (hr : fixedRun env fts (positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest))
      state result ≠ 0) :
    result.1 = positions.map fts ∧ result.2.probes = state.probes ∧ result.2.guesses = state.guesses ∧
      ∀ f, f ∈ result.2.retired ↔ f ∈ state.retired ∨ f ∈ positions := by
  induction positions generalizing state result with
  | nil =>
      have h := fixedRun_pure_nonzero fts _ state result hr
      subst h
      simp
  | cons first rest ih =>
      rw [List.mapM_cons] at hr
      obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero fts _ _ state result hr
      unfold fixedRun runWith at hm
      rw [simulateQ_spec_query] at hm
      simp only [fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hm
      subst hm
      obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero fts _ _ _ result hr
      have h := fixedRun_pure_nonzero fts _ _ result hr
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := ih _ tail ht
      refine ⟨by simp [h1], h2, h3, ?_⟩
      intro f
      rw [h4]
      simp only [afterDisclosure, Finset.mem_insert, List.mem_cons]
      tauto
end Tracking
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section WorldBound
open SecretGuessObservation (fixedRun lazyRun)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable def secretsLaw : SPMF (FtsCoord → Digest) := UniformTableCompletion.complete init.allowed
noncomputable def ftsRun (adversary : AdversaryP) : SPMF ((FtsCoord → Digest) × (Bool × QueryLog Requests × List Wots.Entry)) :=
  secretsLaw >>= fun fts => (fun run => (fts, run)) <$> 𝒮[pairRun (Omega.answers hU ω fts) adversary]
end WorldBound
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
theorem probEvent_bind_mono' {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (p : β → Prop) (r : γ → Prop) (h : ∀ x, Pr[p | f x] ≤ Pr[r | g x]) :
    Pr[p | mx >>= f] ≤ Pr[r | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
theorem counted_le_interactionT (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (B : α × QueryLog Requests → Nat → Prop)
    (hB : ∀ v c c', c' ≤ c → B v c → B v c') :
    Pr[fun x => B x.1 x.2 | simulateQ (Wots.Ref.fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
        (FullGame.loggedWith (FullGame.authenticatedSign published) program))] ≤
      Pr[fun r => B (r.1, r.2.1) r.2.2.length | interactionT T published program] := by
  induction program using OracleComp.inductionOn generalizing B with
  | pure value =>
      rw [FullGame.loggedWith_pure, SphincsSecurity.QueryCap.counted_pure, simulateQ_pure, interactionT_pure,
        probEvent_pure, probEvent_pure]
      exact le_rfl
  | query_bind input next ih =>
      rcases input with input | request
      · rw [FullGame.loggedWith_world]
        change Pr[fun x => B x.1 x.2 | simulateQ (Wots.Ref.fixedWorld T) (SphincsSecurity.QueryCap.counted
          Derivation.charged (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)))] ≤ _
        rw [SphincsSecurity.QueryCap.counted_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
        rcases input with n | x
        · rw [interactionT_coin]
          change Pr[_ | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= _] ≤ _
          apply probEvent_bind_mono'
          intro coin
          simp only [Derivation.charged, if_false, Nat.zero_add, Prod.mk.eta, bind_pure]
          exact ih coin B hB
        · rw [interactionT_public]
          change Pr[_ | pure (T (.inl (.inr x))) >>= _] ≤ _
          rw [pure_bind]
          simp only [Derivation.charged, if_true]
          rw [bind_pure_comp, probEvent_map, bind_pure_comp, probEvent_map]
          calc _ = Pr[fun r => B r.1 (1 + r.2) | simulateQ (Wots.Ref.fixedWorld T)
                (SphincsSecurity.QueryCap.counted Derivation.charged
                  (FullGame.loggedWith (FullGame.authenticatedSign published) (next (T (.inl (.inr x))))))] := rfl
            _ ≤ Pr[fun r => B (r.1, r.2.1) (1 + r.2.2.length) |
                interactionT T published (next (T (.inl (.inr x))))] :=
              ih (T (.inl (.inr x))) (fun v c => B v (1 + c)) (fun v c c' h hb => hB v _ _ (by omega) hb)
            _ ≤ _ := by
              apply probEvent_mono
              intro r _ hr
              simp only [Function.comp_apply, List.length_cons]
              rw [Nat.add_comm]
              exact hr
      · rw [FullGame.loggedWith_request, SphincsSecurity.QueryCap.counted_bind]
        rw [simulateQ_bind, Wots.Ref.fixedWorld_counted_hashOnly T _ (Wots.Ref.authenticatedSign_hashOnly published request),
          pure_bind]
        rw [SphincsSecurity.QueryCap.counted_map, simulateQ_bind, simulateQ_map, interactionT_request]
        simp only [simulateQ_pure, bind_map_left]
        rw [bind_pure_comp, probEvent_map, bind_pure_comp, probEvent_map]
        refine le_trans (ih _ (fun v c => B (v.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ :: v.2)
          ((SourceReplay.queried T (FullGame.authenticatedSign published request)).length + c))
          (fun v c c' h hb => hB _ _ _ (by omega) hb)) ?_
        apply probEvent_mono
        intro r _ hr
        simp only [Function.comp_apply] at hr ⊢
        exact hB _ _ _ (by omega) hr
def publicEntries (events : List FirstHit.QueryEvent) : List Wots.Entry :=
  events.filterMap fun e => match e with
    | ⟨_, .inl (.inr input), answer⟩ => some (input, answer)
    | _ => none
def PairGuess (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  ∀ generated interaction checked,
    Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
      PairGuessIn z.2 interaction.value.2 (publicEntries checked.events)
def OneGuess (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  ∀ generated interaction checked,
    Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
      OneGuessIn z.2 interaction.value.2 (publicEntries checked.events)
theorem publicEntries_pureRecord (T : Answers) {β : Type} (program : M β) (state : LazyPrivate.State) :
    publicEntries (Wots.Ref.pureRecord T program state).events = Wots.entriesOf T (SourceReplay.queried T program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [Wots.Ref.pureRecord_query_bind, SourceReplay.queried_query_bind]
      rcases input with (n | x) | c
      · exact ih _ _
      · change (x, T (.inl (.inr x))) :: publicEntries _ = (x, T (.inl (.inr x))) :: Wots.entriesOf T _
        rw [ih]
      · exact ih _ _
theorem entriesOf_length_le (T : Answers) (queries : List T3.Spec.Domain) :
    (Wots.entriesOf T queries).length ≤ queries.length := by
  unfold Wots.entriesOf
  exact List.length_filterMap_le _ _
section PerTable
variable (adversary : AdversaryP) (q : Nat) (T : Answers)
  (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
  (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
  (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
noncomputable abbrev verdictOn (value : Option ForgeryP × QueryLog Requests) : M Bool :=
  GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 value
include hshort in
theorem fixed_step (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi : interaction ∈ support (Wots.Ref.fixedInteraction adversary T))
    (hev : Wots.Ref.chargeSum (Wots.Ref.combine T interaction).events ≤ q ∧
      ∀ g i c, Wots.GameSplit adversary (Wots.Ref.combine T interaction) g i c →
        P (Wots.Ref.cut (Wots.Ref.combine T interaction).state T) i.value.2 (publicEntries c.events)) :
    Wots.Ref.chargeSum interaction.events + (SourceReplay.queried T (verdictOn T interaction.value)).length ≤ q ∧
      P T interaction.value.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T interaction.value))) := by
  have hg0val : (Wots.Ref.pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen :=
    Wots.Ref.pureRecord_value T keygen (∅, ∅)
  have hg0 : Wots.Ref.pureRecord T keygen (∅, ∅) ∈ support (Wots.Ref.fixedRecord T keygen (∅, ∅)) := by
    rw [Wots.Ref.fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
  obtain ⟨hg0rec, hag0⟩ := Wots.Ref.fixedRecord_mem_record T keygen (∅, ∅) (Wots.Ref.agrees_empty T) _ hg0
  have hi' := hi
  unfold Wots.Ref.fixedInteraction at hi'
  rw [← hg0val] at hi'
  obtain ⟨hirec, hagi⟩ := Wots.Ref.fixedRecord_mem_record T _ _ hag0 interaction hi'
  have hci : Wots.Ref.verdictRecord T interaction ∈ support (Wots.Ref.fixedRecord T (GameWith.verdict PaddedGame.checker
      (Wots.Ref.pureRecord T keygen (∅, ∅)).value.1 interaction.value) interaction.state) := by
    rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.verdict_hashOnly _ _), mem_support_pure_iff, hg0val]
    rfl
  obtain ⟨hcirec, -⟩ := Wots.Ref.fixedRecord_mem_record T _ interaction.state hagi _ hci
  have hsplit : Wots.GameSplit adversary (Wots.Ref.combine T interaction) (Wots.Ref.pureRecord T keygen (∅, ∅))
      interaction (Wots.Ref.verdictRecord T interaction) := ⟨hg0rec, hirec, hcirec, rfl⟩
  obtain ⟨hcharge, hP⟩ := hev
  have hPv := hP _ interaction _ hsplit
  have hentries : publicEntries (Wots.Ref.verdictRecord T interaction).events =
      Wots.entriesOf T (SourceReplay.queried T (verdictOn T interaction.value)) :=
    publicEntries_pureRecord T _ interaction.state
  rw [hentries] at hPv
  refine ⟨?_, hshort _ _ _ _ (Wots.Ref.cut_shortAgree _ _) hPv⟩
  have hv : Wots.Ref.chargeSum (Wots.Ref.verdictRecord T interaction).events =
      (SourceReplay.queried T (verdictOn T interaction.value)).length :=
    Wots.Ref.pureRecord_charge T _ (Wots.Ref.verdict_hashOnly _ _) interaction.state
  have hc : Wots.Ref.chargeSum (Wots.Ref.combine T interaction).events =
      Wots.Ref.chargeSum (Wots.Ref.pureRecord T keygen (∅, ∅)).events +
        (Wots.Ref.chargeSum interaction.events + Wots.Ref.chargeSum (Wots.Ref.verdictRecord T interaction).events) := by
    simp only [Wots.Ref.combine, Wots.Ref.chargeSum_append]
  omega
include hshort hmono in
theorem fixed_le_pairRun :
    Pr[fun result => Wots.Ref.chargeSum result.events ≤ q ∧
        ∀ g i c, Wots.GameSplit adversary result g i c →
          P (Wots.Ref.cut result.state T) i.value.2 (publicEntries c.events) |
      Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => run.2.2.length ≤ q ∧ P T run.2.1 run.2.2 | pairRun T adversary] := by
  rw [Wots.Ref.fixed_game_eq, probEvent_map]
  let B : Option ForgeryP × QueryLog Requests → Nat → Prop := fun value charge =>
    charge + (SourceReplay.queried T (verdictOn T value)).length ≤ q ∧
      P T value.2 (Wots.entriesOf T (SourceReplay.queried T (verdictOn T value)))
  have hB : ∀ v c c', c' ≤ c → B v c → B v c' := fun v c c' h hb => ⟨by have := hb.1; omega, hb.2⟩
  refine le_trans (probEvent_mono fun interaction hi hev =>
    (show B interaction.value (Wots.Ref.chargeSum interaction.events) from
      fixed_step adversary q T P hshort interaction hi hev)) ?_
  have hcount := Wots.Ref.fixedRecord_counted T (FullGame.loggedWith (FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (Wots.Ref.pureRecord T keygen (∅, ∅)).state
  calc _ = Pr[fun x => B x.1 x.2 | (fun result : FirstHit.Recorded (Option ForgeryP × QueryLog Requests) =>
          (result.value, Wots.Ref.chargeSum result.events)) <$> Wots.Ref.fixedInteraction adversary T] := by
        rw [probEvent_map]; rfl
    _ = Pr[fun x => B x.1 x.2 | simulateQ (Wots.Ref.fixedWorld T) (SphincsSecurity.QueryCap.counted
          Derivation.charged (FullGame.loggedWith (FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
            (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] := by
        unfold Wots.Ref.fixedInteraction
        rw [hcount]
    _ ≤ Pr[fun r => B (r.1, r.2.1) r.2.2.length | interactionT T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)] :=
        counted_le_interactionT T _ _ B hB
    _ ≤ _ := by
        unfold pairRun
        rw [bind_pure_comp, probEvent_map]
        apply probEvent_mono
        intro r _ hr
        obtain ⟨hlen, hP⟩ := hr
        refine ⟨?_, hmono _ _ _ _ (fun e he => List.mem_append_right _ he) hP⟩
        simp only [List.length_append]
        have := entriesOf_length_le T (SourceReplay.queried T (verdictOn T (r.1, r.2.1)))
        simp only [verdictOn] at this hlen ⊢
        omega
end PerTable
section Law
noncomputable local instance instFintypeCoordinate_pairGuessEager : Fintype Coordinate := coordinateFintype
attribute [local instance] Wots.Ref.instSampleableTypeFullTable_wotsTransportCompletion
  FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def completionComp' : ProbComp SeccLaw.CompletionTables :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun publicTable => pure (privateTable, publicTable)
theorem completionComp'_eq :
    (liftM completionComp' : PMF SeccLaw.CompletionTables) = PMF.uniformOfFintype SeccLaw.CompletionTables := by
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [PMF.uniformOfFintype_apply]
  have h := MonitoredPrivate.event_lift completionComp' (· = (a, b))
  rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput, PMF.probOutput_eq_apply] at h
  rw [h]
  unfold completionComp'
  change Pr[=(a, b) | (($ᵗ FullGame.FullTable : ProbComp _) >>= fun x =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun y => pure (id x, id y))] = _
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map, probOutput_uniformSample]
  rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  congr 1
  rw [← Nat.cast_mul]
  congr 1
  rw [← Fintype.card_prod]
noncomputable def recordedCompleted' (adversary : AdversaryP) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
    completionComp' >>= fun tables => pure (result, SeccLaw.completeWith result.state tables)
theorem completed_map' (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq =
      (liftM (recordedCompleted' adversary) : PMF _) := by
  unfold SeccLaw.completedExperiment recordedCompleted'
  rw [PMF.monad_map_eq_map, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have he := PaddedGame.traced_record_erasure adversary q hq
  rw [PMF.monad_map_eq_map] at he
  rw [show (PaddedGame.tracedExperiment adversary q hq).bind (fun result =>
      (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
        (QueryRecorded.recordedTrace result, SeccLaw.completeWith result.2.2.base.source.2 tables)) =
      ((PaddedGame.tracedExperiment adversary q hq).map QueryRecorded.recordedTrace).bind (fun result =>
        (PMF.uniformOfFintype SeccLaw.CompletionTables).map fun tables =>
          (result, SeccLaw.completeWith result.state tables)) from by rw [PMF.bind_map]; rfl]
  rw [he, ← completionComp'_eq, liftM_bind]
  congr 1
  funext result
  rw [← PMF.monad_map_eq_map, ← liftM_map, map_eq_bind_pure_comp]
  rfl
theorem pmf_probEvent_mono {α : Type} (p : PMF α) (A B : α → Prop) (h : ∀ x ∈ p.support, A x → B x) :
    Pr[A | p] ≤ Pr[B | p] := by
  simp only [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ p.support
  · split_ifs with ha hb
    · exact le_rfl
    · exact absurd (h x hx ha) hb
    · exact zero_le
    · exact le_rfl
  · have hz : p x = 0 := by simpa [PMF.mem_support_iff] using hx
    split_ifs <;> simp [PMF.probOutput_eq_apply, hz]
theorem shared_le_recorded (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (E : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ E (QueryRecorded.recordedTrace z.1) z.2 |
        SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => Wots.Ref.chargeSum pair.1.events ≤ q ∧ E pair.1 pair.2 | recordedCompleted' adversary] := by
  calc _ ≤ Pr[fun z => Wots.Ref.chargeSum (QueryRecorded.recordedTrace z.1).events ≤ q ∧
        E (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] := by
        apply pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, he⟩ := hev
        have hr := (SeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨?_, he⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => Wots.Ref.chargeSum pair.1.events ≤ q ∧ E pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [completed_map', MonitoredPrivate.event_lift]
theorem restrict_uniform' {β : Type} (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V)
    (k : SeccLaw.PublicTable → ProbComp β) :
    𝒮[($ᵗ (V → HashOutput) : ProbComp _) >>= fun table =>
        k (table ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub)] =
      𝒮[($ᵗ SeccLaw.PublicTable : ProbComp _) >>= k] := by
  rw [FiniteRowSplit.public_table_bind SeccLaw.publicUniverse V hsub]
  apply evalSPMF_bind_congr'
  intro chainTable
  have hc : ∀ extra, (FiniteRowSplit.publicTableEquiv SeccLaw.publicUniverse V hsub).symm (chainTable, extra) ∘
      FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub = chainTable := by
    intro extra
    rw [← FiniteRowSplit.publicTableEquiv_rows, Equiv.apply_symm_apply]
  simp only [hc]
  exact evalSPMF_bind_const_neverFails _ (by simp) _
theorem completeWith_eq_cut' (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : V → HashOutput) :
    SeccLaw.completeWith state (privateTable, publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) =
      Wots.Ref.cut state (Wots.Ref.fillAnswers V state privateTable publicTable) := by
  funext query
  rcases query with (n | x) | c
  · rfl
  · change (state.2 x).getD (SeccLaw.publicFill (publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) x) =
      (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then
        (state.2 x).getD (SphincsSecurity.Concrete.finiteHashAnswer ∅ V publicTable x) else (0 : HashOutput))
    cases hx : state.2 x with
    | some v =>
        simp only [Option.getD_some, Option.isSome_some, or_true, if_true]
    | none =>
        rw [Option.getD_none, Option.getD_none]
        unfold SeccLaw.publicFill
        by_cases hu : x ∈ SeccLaw.publicUniverse
        · rw [dif_pos hu, if_pos (Or.inl hu), SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x (hsub hu) rfl,
            Function.comp_apply]
          rfl
        · rw [dif_neg hu, if_neg (fun h => h.elim hu (fun h' => by simp at h'))]
  · rfl
theorem referenceInputs_universe' (adversary : AdversaryP) :
    SeccLaw.publicUniverse ⊆ Wots.referenceInputs adversary :=
  Finset.subset_union_left
theorem referenceInputs_inputsIn' (adversary : AdversaryP) :
    Wots.Ref.InputsIn (Wots.referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) :=
  fun privateTable _ => (ChainGraph.program_subset_recordedInputs _ privateTable).trans Finset.subset_union_right
theorem recorded_eq_eager' (adversary : AdversaryP) (E : FirstHit.Recorded Bool → Answers → Prop) :
    Pr[fun pair => E pair.1 pair.2 | recordedCompleted' adversary] =
      Pr[fun pair => E pair.1 (Wots.Ref.cut pair.1.state pair.2) |
        Wots.Ref.eagerSide (Wots.referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] := by
  have hlaw : 𝒮[recordedCompleted' adversary] =
      𝒮[(fun pair : FirstHit.Recorded Bool × Answers => (pair.1, Wots.Ref.cut pair.1.state pair.2)) <$>
        (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) >>= fun result =>
          ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
            ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
              pure (result, Wots.Ref.fillAnswers (Wots.referenceInputs adversary) result.state privateTable
                publicTable))] := by
    unfold recordedCompleted' completionComp'
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
    apply evalSPMF_bind_congr'
    intro result
    apply evalSPMF_bind_congr'
    intro privateTable
    rw [← restrict_uniform' (Wots.referenceInputs adversary) (referenceInputs_universe' adversary)]
    apply evalSPMF_bind_congr'
    intro publicTable
    rw [completeWith_eq_cut']
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_map]
  have hc := Wots.Ref.record_completion (Wots.referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary)
    (∅, ∅) (referenceInputs_inputsIn' adversary)
  exact probEvent_congr' (fun _ _ => Iff.rfl) hc
noncomputable def pairExperiment (adversary : AdversaryP) : ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun (run : Bool × QueryLog Requests × List Wots.Entry) =>
          (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable, run.2.1, run.2.2)) <$>
        pairRun (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable) adversary
theorem shared_le_pair (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries') :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
        Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (publicEntries checked.events) | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun s => s.2.2.length ≤ q ∧ P s.1 s.2.1 s.2.2 | pairExperiment adversary] := by
  refine (shared_le_recorded adversary q hq (fun rec A => ∀ g i c, Wots.GameSplit adversary rec g i c →
    P A i.value.2 (publicEntries c.events))).trans ?_
  rw [recorded_eq_eager' adversary (fun rec A => Wots.Ref.chargeSum rec.events ≤ q ∧
    ∀ g i c, Wots.GameSplit adversary rec g i c → P A i.value.2 (publicEntries c.events))]
  unfold Wots.Ref.eagerSide pairExperiment
  apply probEvent_bind_mono'
  intro privateTable
  apply probEvent_bind_mono'
  intro publicTable
  rw [probEvent_map, probEvent_map, Wots.Ref.fillAnswers_empty]
  exact fixed_le_pairRun adversary q (Wots.eagerAnswers (Wots.referenceInputs adversary) privateTable publicTable)
    P hshort hmono
end Law
end SigGolfCandidate.T3.Security.BPair
end
end
