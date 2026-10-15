import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingTable
import SigGolfCandidate.T3.Secc.LargeCouplingContact

section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (mix PrefixDetermined)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
theorem nonce_not_secret (m : Message) :
    (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) ∉ Set.range secretCoordinate := by
  rintro ⟨s, hs⟩
  have hp := congrArg Prod.fst hs
  cases s with
  | inl a =>
      simp only [secretCoordinate, Sum.elim_inl, seedCoordinateP] at hp
      split_ifs at hp <;> cases hp
  | inr f => cases hp
def nonceHalf (m : Message) : OtherHalf := ⟨((.inr (.inl m) : Coordinate), 0), nonce_not_secret m⟩
theorem nonceHalf_injective : Function.Injective nonceHalf := by
  intro m m' h
  have h1 := congrArg (fun x : OtherHalf => x.val.1) h
  simp only [nonceHalf] at h1
  exact Sum.inl.inj (Sum.inr.inj h1)
noncomputable def nonceOver (o : OtherHalves) (nvv : Message → Digest) : OtherHalves :=
  SphincsSecurity.Concrete.UniformTableSplit.overwrite nonceHalf nonceHalf_injective nvv o
noncomputable def privPsi (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) : FullGame.FullTable :=
  privateEquiv.symm (s, nonceOver (privateEquiv priv).2 nvv)
theorem privateEquiv_snd (t : FullGame.FullTable) (h : OtherHalf) : (privateEquiv t).2 h = ChainGraph.halves t h.val := by
  change (splitEquiv (ChainGraph.halves t)).2 h = _
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow]
  rfl
theorem halves_privPsi (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable)
    (h : ChainGraph.HalfCoordinate) (hs : h ∉ Set.range secretCoordinate) :
    ChainGraph.halves (privPsi s nvv priv) h =
      if hn : ∃ m, h = ((.inr (.inl m) : Coordinate), 0) then nvv (Classical.choose hn)
      else ChainGraph.halves priv h := by
  have h1 := privateEquiv_snd (privPsi s nvv priv) ⟨h, hs⟩
  unfold privPsi at h1
  rw [Equiv.apply_symm_apply] at h1
  change (nonceOver (privateEquiv priv).2 nvv) ⟨h, hs⟩ = _ at h1
  change ChainGraph.halves (privateEquiv.symm (s, nonceOver (privateEquiv priv).2 nvv)) (⟨h, hs⟩ : OtherHalf).val = _
  rw [← h1]
  split_ifs with hn
  · have hm := Classical.choose_spec hn
    have heq : (⟨h, hs⟩ : OtherHalf) = nonceHalf (Classical.choose hn) := Subtype.ext hm
    rw [heq]
    exact SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed _ _ _ _ _
  · rw [nonceOver, SphincsSecurity.Concrete.UniformTableSplit.overwrite_outside _ _ _ _ _ (by
      rintro ⟨m, hm⟩
      exact hn ⟨m, (congrArg Subtype.val hm).symm⟩), privateEquiv_snd]
theorem privPsi_other (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) (c : Coordinate)
    (hc : ∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) (hn : ∀ m : Message, c ≠ .inr (.inl m)) :
    privPsi s nvv priv c = priv c := by
  have hh : ∀ i : Fin 2, ChainGraph.halves (privPsi s nvv priv) (c, i) = ChainGraph.halves priv (c, i) := by
    intro i
    rw [halves_privPsi s nvv priv (c, i) (hc i), dif_neg]
    rintro ⟨m, hm⟩
    exact hn m (congrArg Prod.fst hm)
  have h0 := hh 0
  have h1 := hh 1
  simp only [ChainGraph.halves] at h0 h1
  simp only [Fin.isValue, Fin.val_zero, if_true, Fin.val_one, one_ne_zero, if_false] at h0 h1
  rw [← ChainGraph.joinOutput_parts (privPsi s nvv priv c), ← ChainGraph.joinOutput_parts (priv c), h0, h1]
theorem privPsi_nonce (s : Secrets) (nvv : Message → Digest) (priv : FullGame.FullTable) (m : Message) :
    (privPsi s nvv priv (.inr (.inl m))).extractLsb' 0 128 = nvv m := by
  have h := halves_privPsi s nvv priv _ (nonce_not_secret m)
  rw [dif_pos ⟨m, rfl⟩] at h
  have hm : Classical.choose (⟨m, rfl⟩ : ∃ m', (((.inr (.inl m) : Coordinate), (0 : Fin 2)) : ChainGraph.HalfCoordinate) =
      ((.inr (.inl m') : Coordinate), 0)) = m := by
    have := Classical.choose_spec (⟨m, rfl⟩ : ∃ m', (((.inr (.inl m) : Coordinate), (0 : Fin 2)) :
      ChainGraph.HalfCoordinate) = ((.inr (.inl m') : Coordinate), 0))
    have h1 := congrArg Prod.fst this
    exact (Sum.inl.inj (Sum.inr.inj h1)).symm
  rw [hm] at h
  simpa [ChainGraph.halves] using h
def rowPrefix (f : EncLeaf × Fin (2 ^ 22) → HashOutput) (x : EncLeaf × Fin (2 ^ 22)) : Prop :=
  x.2.val < WCT9.searchLimit x.1.1.lay ∧
    ∀ r, capSel x.1 (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt x.1) (fun c => f (x.1, c))) = some r →
      x.2 ≤ r.1
theorem select_congr_prefix (L : EncLeaf) (f g : Fin (2 ^ 22) → HashOutput)
    (h : ∀ c, c.val < WCT9.searchLimit L.1.lay →
      (∀ r, capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) f) = some r → c ≤ r.1) →
        f c = g c) :
    capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) g) =
      capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) f) := by
  cases hs : capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) f) with
  | none =>
      have hrej : ∀ c : Fin (2 ^ 22), c.val < WCT9.searchLimit L.1.lay → decodeAt L (f c) = none := by
        intro c hc
        cases hf : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) f with
        | none => exact (SphincsSecurity.Concrete.FirstSuccessTable.select_none_iff _ _).mp hf c
        | some r =>
            have hge : WCT9.searchLimit L.1.lay ≤ r.1.val := by
              by_contra hlt
              have := (capSel_eq_some (L := L)).mpr ⟨hf, by omega⟩
              rw [hs] at this
              cases this
            exact ((SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ f r.1 r.2).mp hf).2 c
              (by rw [Fin.lt_def]; omega)
      have hfg : ∀ c : Fin (2 ^ 22), c.val < WCT9.searchLimit L.1.lay → f c = g c :=
        fun c hc => h c hc (fun r hr => by rw [hs] at hr; cases hr)
      cases hg : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) g with
      | none => rfl
      | some r =>
          obtain ⟨hv, -⟩ := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ g r.1 r.2).mp hg
          by_cases hlt : r.1.val < WCT9.searchLimit L.1.lay
          · rw [← hfg r.1 hlt, hrej r.1 hlt] at hv
            cases hv
          · cases hc : capSel L (some r) with
            | none => rfl
            | some r' =>
                obtain ⟨hr', hlt'⟩ := capSel_eq_some.mp hc
                cases hr'
                exact absurd hlt' hlt
  | some r =>
      obtain ⟨hraw, hlt⟩ := capSel_eq_some.mp hs
      obtain ⟨i, v⟩ := r
      have hsome := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ f i v).mp hraw
      have hle : ∀ c, c ≤ i → f c = g c := fun c hc =>
        h c (lt_of_le_of_lt (Fin.le_def.mp hc) hlt) (fun r hr => by rw [hs] at hr; cases hr; exact hc)
      have hg : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) g = some (i, v) := by
        apply (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ g i v).mpr
        refine ⟨by rw [← hle i le_rfl]; exact hsome.1, fun j hj => ?_⟩
        rw [← hle j (le_of_lt hj)]
        exact hsome.2 j hj
      rw [hg]
      exact capSel_eq_some.mpr ⟨rfl, hlt⟩
theorem rowPrefix_determined : PrefixDetermined rowPrefix := by
  intro f g hfg x
  unfold rowPrefix
  have hsel : capSel x.1 (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt x.1) (fun c => g (x.1, c))) =
      capSel x.1 (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt x.1) (fun c => f (x.1, c))) :=
    select_congr_prefix x.1 _ _ (fun c hc hc' => hfg (x.1, c) ⟨hc, hc'⟩)
  rw [hsel]
section Public
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
noncomputable def residualPsi (labels : Labels) (rows : EncLeaf → Fin (2 ^ 22) → HashOutput) (τ : U → HashOutput) :
    U → HashOutput :=
  SphincsSecurity.Concrete.UniformTableSplit.overwrite (encCell U hE labels) (encCell_injective U hE labels)
    (mix rowPrefix (Function.uncurry rows) (fun x => τ (encCell U hE labels x))) τ
noncomputable def tablePsi (sec : Secrets) (vals : Coord → Digest) (nv : Message → Digest) (τ : U → HashOutput)
    (a : AuxData) : Answers :=
  Wots.eagerAnswers U (privPsi sec nv a.priv)
    (programmed U hU sec (routerLabels vals a) (residualPsi U hE (routerLabels vals a) a.rows τ))
theorem eagerAnswers_eq (priv : FullGame.FullTable) (pub : U → HashOutput) :
    Wots.eagerAnswers U priv pub = CanonGraph.eagerAnswers priv U pub := by
  funext q
  rcases q with (n | x) | c <;> rfl
theorem encCell_val (labels : Labels) (L : EncLeaf) (c : Fin (2 ^ 22)) :
    (encCell U hE labels (L, c)).val = Wots.encRow L.toWots (msgLabel labels L) (BitVec.ofNat 32 c.val) 0 := by
  rw [CanonEncoding.encCell_val, Wots.encRow_zero]
  rfl
theorem msgLabel_router (vals : Coord → Digest) (a : AuxData) (L : EncLeaf) :
    msgLabel (routerLabels vals a) L = msgVals vals L := by
  unfold msgLabel msgVals
  by_cases hl : L.1.lay.val < 3
  · rw [dif_pos hl, dif_pos hl]
    congr 1
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans (joinLabels_low _ _ _)
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans (joinLabels_low _ _ _)
  · rw [dif_neg hl, dif_neg hl]
    exact congrArg WCT9.LayerMsg.forest (joinLabels_low _ _ _)
theorem sel_psi (a : AuxData) (labels : Labels) (τ : U → HashOutput) (L : EncLeaf) :
    selectionsOf U hE labels (residualPsi U hE labels a.rows τ) L = a.sel L := by
  unfold selectionsOf rawSelectionsOf AuxData.sel
  apply select_congr_prefix
  intro c hc hc'
  unfold residualPsi
  rw [SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
  unfold mix
  rw [if_pos (show rowPrefix (Function.uncurry a.rows) (L, c) from ⟨hc, hc'⟩)]
  rfl
theorem rowPrefix_iff (a : AuxData) (L : EncLeaf) (c : Fin (2 ^ 22)) :
    rowPrefix (Function.uncurry a.rows) (L, c) ↔ PrefixRow a L (BitVec.ofNat 32 c.val) := by
  have hc : (BitVec.ofNat 32 c.val).toNat = c.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := c.isLt; omega)
  unfold rowPrefix PrefixRow
  rw [hc]
  rfl
end Public
section Coherence
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
theorem coherent_psi (sec : Secrets) (vals : Coord → Digest) (nv : Message → Digest) (τ : U → HashOutput)
    (a : AuxData) (hv : seedView sec = fun x => vals (.inr x)) :
    Coherent U (tablePsi U hU hE sec vals nv τ a) vals nv τ a := by
  set s : Secrets := sec with hs
  set labels := routerLabels vals a with hlabels
  set res := residualPsi U hE labels a.rows τ with hres
  set o := nonceOver (privateEquiv a.priv).2 nv with ho
  have hT : tablePsi U hU hE sec vals nv τ a = CanonGraph.eagerAnswers (privateEquiv.symm (s, o)) U
      (programmed U hU s labels res) := by
    unfold tablePsi
    rw [eagerAnswers_eq]
    rfl
  have hsec : secretsOf (tablePsi U hU hE sec vals nv τ a) = s := by
    rw [hT, secretsOf_eager, privateSecrets_symm]
  have hpubX : ∀ (X : HashInput) (hX : X ∈ U), tablePsi U hU hE sec vals nv τ a (.inl (.inr X)) =
      programmed U hU s labels res ⟨X, hX⟩ := by
    intro X hX
    rw [hT]
    exact eagerAnswers_mem _ U _ ⟨X, hX⟩
  refine ⟨?_, by rw [hsec]; exact hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    exact eager_programmed_agrees U hU s o labels res
  ·
    intro X hX hcell hpre
    rw [hpubX X hX, programmed_other U hU s labels res ⟨X, hX⟩ (fun N => by
      have := hcell N
      rw [hsec] at this
      exact this)]
    by_cases hr : (⟨X, hX⟩ : U) ∈ Set.range (encCell U hE labels)
    · obtain ⟨x, hx⟩ := hr
      rw [hres, residualPsi, ← hx, SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
      unfold mix
      rw [if_neg]
      intro hpx
      apply hpre
      obtain ⟨L, c⟩ := x
      refine ⟨L, BitVec.ofNat 32 c.val, ?_, (rowPrefix_iff a L c).mp hpx⟩
      have hv := congrArg Subtype.val hx
      rw [encCell_val, msgLabel_router] at hv
      exact hv.symm
    · rw [hres, residualPsi, SphincsSecurity.Concrete.UniformTableSplit.overwrite_outside _ _ _ _ _ hr]
  ·
    intro L ctr hp
    have hp1 : ctr.toNat < 2 ^ 22 := lt_of_lt_of_le hp.1 (WCT9.searchLimit_le L.1.lay)
    have hc : BitVec.ofNat 32 (⟨ctr.toNat, hp1⟩ : Fin (2 ^ 22)).val = ctr := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hp1; omega)
    have hX : Wots.encRow L.toWots (msgVals vals L) ctr 0 = (encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).val := by
      rw [encCell_val, msgLabel_router, hc]
    rw [hX, hpubX _ (encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).property]
    rw [programmed_other U hU s labels res _ (fun N => encodingQuery_ne_cell _ s N labels)]
    rw [hres, residualPsi, show (⟨(encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).val,
      (encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).property⟩ : U) = encCell U hE labels (L, ⟨ctr.toNat, hp1⟩) from rfl,
      SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
    unfold mix
    rw [if_pos ((rowPrefix_iff a L _).mpr (by rw [hc]; exact hp))]
    unfold prefixValue
    rw [dif_pos hp1]
    rfl
  ·
    intro L
    have hpub : ∀ x : U, tablePsi U hU hE sec vals nv τ a (.inl (.inr x.val)) =
        programmed U hU (secretsOf (tablePsi U hU hE sec vals nv τ a)) labels res x := by
      intro x
      rw [hsec]
      exact hpubX x.val x.property
    rw [referenceSearch_eq U hU hE _ labels res hpub L, sel_psi]
    cases hsel : a.sel L with
    | none => rfl
    | some r =>
        have h := (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp
          (capSel_eq_some.mp hsel).1
        obtain ⟨-, hsome⟩ := (decodeAt_eq_some L _ r.2).mp h.1
        simp only [Option.bind_some]
        rcases WCT9.producerDecode_eq_none_or L.1.lay r.2 with hn | he
        · rw [hn] at hsome
          cases hsome
        · rw [he]
  ·
    intro c hc hn
    change privPsi s nv a.priv c = a.priv c
    exact privPsi_other s nv a.priv c hc hn
  ·
    intro X hX
    change SphincsSecurity.Concrete.finiteHashAnswer ∅ U _ X = 0
    unfold SphincsSecurity.Concrete.finiteHashAnswer
    rw [dif_neg hX]
    rfl
  ·
    intro m
    exact privPsi_nonce s nv a.priv m
end Coherence
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers
open OracleComp
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open ClaudeWCT.W9.T3.Security.LargeCoupling (nonceHalf)
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable scoped instance (priority := high) samplerLabels : SampleableType Labels :=
  CanonGraph.instSampleableTypeLabels_1
noncomputable scoped instance (priority := high) samplerSecrets : SampleableType Secrets :=
  CanonGraph.instSampleableTypeSecrets
noncomputable scoped instance (priority := high) samplerOthers : SampleableType OtherHalves :=
  CanonGraph.instSampleableTypeOtherHalves
noncomputable scoped instance (priority := high) samplerLow : SampleableType LowLabels :=
  CanonGraph.instSampleableTypeLowLabels
noncomputable scoped instance (priority := high) samplerVals : SampleableType (Coord → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerWorld : SampleableType (WCoord → LargeResidual.Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerHid : SampleableType (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerJunk : SampleableType (WJunk → LargeResidual.Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRows :
    SampleableType (EncLeaf → Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRowsFlat :
    SampleableType (EncLeaf × Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) decEqNonceOutside :
    DecidableEq (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Classical.decEq _
noncomputable scoped instance (priority := high) fintypeNonceOutside :
    Fintype (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Subtype.fintype _
noncomputable scoped instance (priority := high) samplerNonceOutside :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf → Digest) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerEncOutside (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) :=
  SampleableType.ofFintype _
end ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (overwrite_bind uniform_equiv_bind uniform_join_bind uniform_prod_bind
  evalSPMF_bind_comm evalSPMF_unused uniform_mix mix)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Law
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem others_bind {R : Type} (next : OtherHalves → ProbComp R) :
    𝒮[($ᵗ OtherHalves : ProbComp _) >>= next] =
      𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        next (nonceOver (privateEquiv priv).2 nv)] := by
  rw [private_bind (fun priv => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
    next (nonceOver (privateEquiv priv).2 nv))]
  simp only [Equiv.apply_symm_apply]
  rw [evalSPMF_unused Secrets]
  unfold nonceOver
  rw [overwrite_bind nonceHalf nonceHalf_injective next]
theorem residual_bind (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) {R : Type}
    (next : (U → HashOutput) → ProbComp R) :
    𝒮[($ᵗ (U → HashOutput) : ProbComp _) >>= next] =
      𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ => next (residualPsi U hE labels rows τ)] := by
  have hj : ∀ (rows : EncLeaf → Fin (2 ^ 22) → HashOutput) (g : EncLeaf × Fin (2 ^ 22) → HashOutput)
      (out : SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput),
      residualPsi U hE labels rows
        (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels) g out) =
      SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels)
        (mix rowPrefix (Function.uncurry rows) g) out := by
    intro rows g out
    unfold residualPsi
    have hg : (fun x => SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) g out (encCell U hE labels x)) = g :=
      funext fun x => SphincsSecurity.Concrete.UniformTableSplit.join_embed _ _ _ _ x
    rw [hg, SphincsSecurity.Concrete.UniformTableSplit.overwrite_join]
  rw [evalSPMF_bind_congr' _ (fun rows => uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels)
    (fun τ => next (residualPsi U hE labels rows τ)))]
  simp only [hj]
  rw [uniform_equiv_bind (Equiv.curry (EncLeaf) (Fin (2 ^ 22)) HashOutput).symm.symm]
  simp only [Equiv.symm_symm, Equiv.curry_apply, Function.uncurry_curry]
  rw [uniform_mix rowPrefix rowPrefix_determined (fun R =>
    ($ᵗ (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) : ProbComp _) >>=
      fun out => next (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) R out))]
  rw [uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels) next]
theorem law_derived (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv => ($ᵗ LowLabels : ProbComp _) >>= fun low =>
        ($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (programmed U hU sec (joinLabels low high) (residualPsi U hE (joinLabels low high) rows τ)))] := by
  simp only [eagerAnswers_eq]
  rw [tables_bind U hU (fun priv pub => next (CanonGraph.eagerAnswers priv U pub))]
  refine (evalSPMF_bind_congr' _ fun sec => others_bind _).trans ?_
  refine evalSPMF_bind_congr' _ fun sec => evalSPMF_bind_congr' _ fun priv' => evalSPMF_bind_congr' _ fun nv => ?_
  rw [labels_bind]
  refine evalSPMF_bind_congr' _ fun low => evalSPMF_bind_congr' _ fun high => ?_
  exact residual_bind U hE (joinLabels low high) _
theorem law_target (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (programmed U hU sec (joinLabels low high) (residualPsi U hE (joinLabels low high) rows τ)))] := by
  rw [law_derived U hU hE next]
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ =>
    evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  refine evalSPMF_bind_congr' _ fun _ => ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ =>
    evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_congr' _ fun _ => evalSPMF_bind_comm _ _ _).trans ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  refine evalSPMF_bind_congr' _ fun _ => ?_
  refine (evalSPMF_bind_comm _ _ _).trans ?_
  rfl
end Law
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl lazy_aux' view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (completeRows_none_apply completeRows_none probEvent_bind_congr_eq)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Chain
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
noncomputable def initComp : ProbComp AuxData :=
  ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
      ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => pure ⟨high, rows, priv⟩
noncomputable def initLaw : PMF AuxData := liftM initComp
theorem cell_univ :
    SphincsSecurity.Concrete.UniformTableCompletion.cell
        (supp (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest))) =
      𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] := by
  rw [ClaudeWCT.W9.T3.Security.FamResidual.supp_univ]
  apply SPMF.ext
  intro x
  change _ = Pr[= x | ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)]
  rw [SphincsSecurity.Concrete.UniformTableCompletion.cell_apply, if_pos (Finset.mem_univ _), probOutput_uniformSample,
    Finset.card_univ]
section Lazy
variable {U : Finset HashInput}
theorem lazy_aux {β : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (i : AuxQuery) (k : AuxSpec.Range i → OracleComp (RWorld U) β) (s : LargeResidual.State WCoord (Cell U)) :
    lazyRun aux q (liftM ((RWorld U).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => lazyRun aux q (k v) s) := by
  exact lazy_aux' aux q i k s
theorem finish_stop {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U)))
    (P : LargeResidual.State WCoord (Cell U) → Prop) :
    Pr[fun r => r.1 = none ∧ P r.2 | X >>= finish] = Pr[fun r => r.1 = none ∧ P r.2 | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      simp only [finish, probEvent_pure, true_and]
      split_ifs <;> simp
  | some v =>
      simp only [reduceCtorEq, false_and, if_false, mul_eq_zero]
      right
      unfold finish
      simp only [probEvent_bind_eq_tsum, probEvent_pure, reduceCtorEq, false_and, if_false, mul_zero, tsum_zero]
theorem observed_avg {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : LargeResidual.State WCoord (Cell U) → Prop) :
    Pr[fun r => r.1 = none ∧ P r.2 | 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q (view x) τ program LargeResidual.initial] =
      Pr[fun r => r.1 = none ∧ P r.2 | lazyRun aux q program LargeResidual.initial] := by
  rw [← cell_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (by change (supp (fun _ : WCoord => (Finset.univ : Finset LargeResidual.Digest))).Nonempty
        rw [ClaudeWCT.W9.T3.Security.FamResidual.supp_univ]; exact Finset.univ_nonempty)
  rw [← finish_stop (lazyRun aux q program LargeResidual.initial) P, ← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  simp only [Function.comp_apply, retain, Option.map_eq_none_iff]
theorem initLaw_spmf : (liftM initLaw : SPMF AuxData) = 𝒮[initComp] := by
  apply SPMF.ext
  intro a
  rw [SPMF.liftM_apply, ← PMF.probOutput_eq_apply, ← probEvent_eq_eq_probOutput, initLaw,
    MonitoredPrivate.event_lift, probEvent_eq_eq_probOutput]
  rfl
theorem router_side (adversary : AdversaryP) (q : Nat) :
    Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial] =
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell (Wots.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q (view x) τ (routerWith (Wots.referenceInputs adversary) adversary q ⟨high, rows, priv⟩)
          LargeResidual.initial] := by
  unfold router initReq
  rw [lazy_aux]
  change Pr[_ | (liftM initLaw : SPMF AuxData) >>= _] = _
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_congr_eq
  intro high
  apply probEvent_bind_congr_eq
  intro rows
  apply probEvent_bind_congr_eq
  intro priv
  exact (observed_avg (auxLaw initLaw) q _ (fun st => st.counters.calls ≤ q)).symm
end Lazy
end Chain
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
section
namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery retain runWith_query_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (lazyRun finish observedRun run_posterior lazyImpl lazy_aux' view supp)
open SigGolfCandidate.T3.Security.LargeCoupling (probEvent_bind_le_of uniform_weight weight_self evalSPMF_uniform_inst
  uniform_equiv_bind uniform_prod_bind)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Contact
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
def RealContact (adversary : AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  ContactR adversary q x.1 x.2 ∧ NoOvR adversary x.1 x.2
theorem loggedOutputs_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (log : QueryLog Requests) :
    WPair.loggedOutputs A log = WPair.loggedOutputs T log := by
  unfold WPair.loggedOutputs CaseC.signedOutput
  congr 1
  funext entry
  congr 1
  funext σ
  rw [digestSearch_short hAT]
theorem noOvR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : AdversaryP)
    (rec : FirstHit.Recorded Bool) : NoOvR adversary rec A ↔ NoOvR adversary rec T := by
  unfold NoOvR LogNoOverflow
  simp only [loggedOutputs_short hAT]
/-- The contact event with the FTS no-overflow side condition (on the recorded trace). -/
def ContactNO (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) : Prop :=
  Contact adversary q z ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2
noncomputable def fixedNext (adversary : AdversaryP) (T : Answers) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  (fun r => (r, T)) <$> Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)
theorem contact_real_side (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[ContactNO adversary q | SeccLaw.completedExperiment adversary q hq] =
      Pr[RealContact adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.completed_eager_cut adversary q hq (fun rec A => ContactR adversary q rec A ∧ NoOvR adversary rec A)
  rw [show (ContactNO adversary q) = fun z => ContactR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
    NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 from rfl, h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => ContactR adversary q x.1 (Wots.Ref.cut x.1.state x.2) ∧
      NoOvR adversary x.1 (Wots.Ref.cut x.1.state x.2)) = RealContact adversary q := by
    funext x
    exact propext (and_congr (contactR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
      (noOvR_short (Wots.Ref.cut_shortAgree _ _) adversary x.1))
  rw [h2]
  unfold Wots.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1
/-- The secrets of a hidden object (leaf-family and FTS coefficients) and the unused junk cells. -/
noncomputable def secOf (x : ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) (jk : WJunk → LargeResidual.Digest) :
    Secrets :=
  Sum.elim
    (fun a => if hc : a.chain.val < WCT9.famCount a.layer then
        x.2 (Sum.inl ⟨(a.layer, a.tree, a.leaf), trivial⟩ : WFam)
          ⟨a.chain.val, by have := WCT9.famCount_ge a.layer; show a.chain.val < WCT9.famCount a.layer - 1 + 1; omega⟩
      else jk ⟨a, by omega⟩)
    (fun c => x.2 (Sum.inr (c.1, c.2.1) : WFam) c.2.2)
/-- The coefficient families of a secret table. -/
def famOfSec (sec : Secrets) : (f : WFam) → ClaudeWCT.W9.T3.Security.FamResidual.Coefs
    (ClaudeWCT.W9.T3.Security.FamResidual.Seeds.deg (Coord := WCoord) f)
  | .inl L => fun j => sec (.inl ⟨L.1.1, L.1.2.1, L.1.2.2,
      ⟨j.val, by
        have hj : j.val < WCT9.famCount L.1.1 - 1 + 1 := j.isLt
        have := WCT9.famCount_le L.1.1
        omega⟩⟩)
  | .inr f => fun j => sec (.inr (f.1, f.2, j))
noncomputable def worldEquiv : Secrets × ((Message → Digest) × LowLabels) ≃
    ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord × (WJunk → LargeResidual.Digest) where
  toFun p := (((Sum.elim (Sum.elim p.2.2 (fun t => p.1 (.inl t.1))) p.2.1 : WPlain → LargeResidual.Digest),
    famOfSec p.1), fun jk => p.1 (.inl jk.1))
  invFun y := (secOf y.1 y.2, fun m => y.1.1 (.inr m), fun N => y.1.1 (.inl (.inl N)))
  left_inv p := by
    obtain ⟨sec, nv, low⟩ := p
    refine Prod.ext ?_ rfl
    funext c
    rcases c with a | ⟨i, k, j⟩
    · change (if hc : a.chain.val < WCT9.famCount a.layer then
          sec (.inl ⟨a.layer, a.tree, a.leaf, ⟨a.chain.val, _⟩⟩) else sec (.inl a)) = sec (.inl a)
      split_ifs <;> rfl
    · rfl
  right_inv y := by
    obtain ⟨⟨L, K⟩, jk⟩ := y
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext c
      rcases c with (N | ⟨a, ha⟩) | m
      · rfl
      · exact ha.elim
      · rfl
    · funext f
      rcases f with ⟨⟨lay, tree, leaf⟩, hL⟩ | ⟨i, k⟩
      · funext j
        have hj : j.val < WCT9.famCount lay := by
          have h1 : j.val < WCT9.famCount lay - 1 + 1 := j.isLt
          have := WCT9.famCount_ge lay
          omega
        change (if hc : j.val < WCT9.famCount lay then
            K (Sum.inl ⟨(lay, tree, leaf), trivial⟩ : WFam) ⟨j.val, _⟩ else _) = K _ j
        rw [dif_pos hj]
      · rfl
    · funext t
      obtain ⟨a, hc⟩ := t
      show secOf (L, K) jk (.inl a) = jk ⟨a, hc⟩
      unfold secOf
      simp only [Sum.elim_inl]
      rw [dif_neg (by omega)]
theorem world_split {R : Type} (K : Secrets → (Message → Digest) → LowLabels → ProbComp R) :
    𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => K sec nv low] =
      𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        ($ᵗ (WJunk → LargeResidual.Digest) : ProbComp _) >>= fun jk =>
        K (secOf x jk) (fun m => x.1 (.inr m)) (fun N => x.1 (.inl (.inl N)))] := by
  let _ : SampleableType ((Message → Digest) × LowLabels) := SampleableType.ofFintype _
  let _ : SampleableType (Secrets × ((Message → Digest) × LowLabels)) := SampleableType.ofFintype _
  let _ : SampleableType (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord × (WJunk → LargeResidual.Digest)) :=
    SampleableType.ofFintype _
  calc _ = 𝒮[($ᵗ (Secrets × ((Message → Digest) × LowLabels)) : ProbComp _) >>= fun p => K p.1 p.2.1 p.2.2] := by
        rw [uniform_prod_bind]
        refine evalSPMF_bind_congr' _ fun sec => ?_
        rw [uniform_prod_bind]
    _ = 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord × (WJunk → LargeResidual.Digest)) : ProbComp _) >>=
          fun y => K (secOf y.1 y.2) (fun m => y.1.1 (.inr m)) (fun N => y.1.1 (.inl (.inl N)))] :=
        uniform_equiv_bind worldEquiv.symm _
    _ = _ := uniform_prod_bind _
theorem ofFn_congr_len {n m : Nat} (h : n = m) (f : Fin n → Digest) (g : Fin m → Digest)
    (hfg : ∀ i (hi : i < n), f ⟨i, hi⟩ = g ⟨i, h ▸ hi⟩) : List.ofFn f = List.ofFn g := by
  subst h
  congr 1
  funext i
  exact hfg i.val i.isLt
theorem seedView_secOf (x : ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) (jk : WJunk → LargeResidual.Digest) :
    seedView (secOf x jk) = fun s => view x (.inl (.inr s)) := by
  funext s
  rcases s with a | w
  · change seedsOf (secOf x jk) a = view x (.inl (.inr (.inl a)))
    have hs : (ClaudeWCT.W9.T3.Security.FamResidual.Seeds.split (.inl (.inr (.inl a)) : WCoord)) =
        wsplit (.inl (.inr (.inl a))) := rfl
    unfold view
    rw [hs, wsplit_addr]
    unfold seedsOf
    change ClaudeWCT.Arith.familyEval (List.ofFn (leafFamily (secOf x jk) a.layer a.tree a.leaf)) (a.chain.val + 1) =
      ClaudeWCT.Arith.familyEval (List.ofFn (x.2 (Sum.inl ⟨(a.layer, a.tree, a.leaf), trivial⟩ : WFam)))
        (WCT9.lowerPoint a.chain.val)
    have hn : WCT9.famCount a.layer = WCT9.famCount a.layer - 1 + 1 := by
      have := WCT9.famCount_ge a.layer; omega
    congr 1
    apply ofFn_congr_len hn
    intro k hk
    unfold leafFamily secOf
    simp only [Sum.elim_inl]
    rw [dif_pos hk]
  · rfl
/-- An event's probability under a bind is at most a uniform bound on the continuations. -/
theorem probEvent_bind_le_const {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (E : β → Prop) (c : ENNReal)
    (h : ∀ x, Pr[E | f x] ≤ c) : Pr[E | mx >>= f] ≤ c := by
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' x, Pr[= x | mx] * c := ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
    _ = (∑' x, Pr[= x | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
    _ = c := one_mul c
theorem contact_le_lazy (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[ContactNO adversary q | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial] := by
  have hU : canonInputs ⊆ Wots.referenceInputs adversary :=
    canonInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  have hE : encInputs ⊆ Wots.referenceInputs adversary :=
    encInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  rw [contact_real_side, router_side,
    probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun high => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun x => ?_
  refine probEvent_bind_le_const _ _ _ _ fun jk => ?_
  have hτ : ∀ (k : (Wots.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm (secOf x jk,
          nonceOver (privateEquiv priv).2 (fun m => x.1 (.inr m)))) (Wots.referenceInputs adversary)
          (programmed (Wots.referenceInputs adversary) hU (secOf x jk)
            (joinLabels (fun N => x.1 (.inl (.inl N))) high)
            (residualPsi (Wots.referenceInputs adversary) hE (joinLabels (fun N => x.1 (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c)) (fun m => view x (.inr m)) τ
          ⟨high, rows, priv⟩ := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealContact
    rw [probEvent_map]
    have h := table_contact_le adversary q hq initLaw
      (coherent_psi (Wots.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c))
        (fun m => view x (.inr m)) τ ⟨high, rows, priv⟩ (seedView_secOf x jk))
    have hlab : Sum.elim (fun c => view x (.inl c)) (fun m => view x (.inr m)) = view x := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h
end Contact
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
