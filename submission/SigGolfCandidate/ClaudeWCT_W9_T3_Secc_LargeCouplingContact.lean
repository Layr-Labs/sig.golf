import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeCouplingTable
import SigGolfCandidate.T3_Secc_LargeCouplingContact

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
section Public
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
theorem eagerAnswers_eq (priv : FullGame.FullTable) (pub : U → HashOutput) :
    Wots.eagerAnswers U priv pub = CanonGraph.eagerAnswers priv U pub := by
  funext q
  rcases q with (n | x) | c <;> rfl
end Public
section Coherence
variable (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
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
/-- The secrets of a hidden object (leaf-family and FTS coefficients) and the unused junk cells. -/
noncomputable def secOf (x : ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) (jk : WJunk → LargeResidual.Digest) :
    Secrets :=
  Sum.elim
    (fun a => if hc : a.chain.val < WCT9.famSize a.layer a.leaf.val then
        x.2 (Sum.inl ⟨(a.layer, a.tree, a.leaf), trivial⟩ : WFam)
          ⟨a.chain.val, by
            have := WCT9.famSize_pos a.layer a.leaf.val
            show a.chain.val < WCT9.famSize a.layer a.leaf.val - 1 + 1; omega⟩
      else jk ⟨a, by omega⟩)
    (fun c => x.2 (Sum.inr (c.1, c.2.1) : WFam) c.2.2)
/-- The coefficient families of a secret table. -/
def famOfSec (sec : Secrets) : (f : WFam) → ClaudeWCT.W9.T3.Security.FamResidual.Coefs
    (ClaudeWCT.W9.T3.Security.FamResidual.Seeds.deg (Coord := WCoord) f)
  | .inl L => fun j => sec (.inl ⟨L.1.1, L.1.2.1, L.1.2.2,
      ⟨j.val, by
        have hj : j.val < WCT9.famSize L.1.1 L.1.2.2.val - 1 + 1 := j.isLt
        have := WCT9.famSize_lt_58 L.1.1 L.1.2.2.val
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
    · change (if hc : a.chain.val < WCT9.famSize a.layer a.leaf.val then
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
        have hj : j.val < WCT9.famSize lay leaf.val := by
          have h1 : j.val < WCT9.famSize lay leaf.val - 1 + 1 := j.isLt
          have := WCT9.famSize_pos lay leaf.val
          omega
        change (if hc : j.val < WCT9.famSize lay leaf.val then
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
    change ClaudeWCT.Arith.familyEval (List.ofFn (leafFamily (secOf x jk) a.layer a.tree a.leaf))
        (WCT9.famPoint a.layer a.leaf.val a.chain.val) =
      ClaudeWCT.Arith.familyEval
        (List.ofFn (x.2 (Sum.inl ⟨(a.layer, a.tree, famSlot a.layer a.leaf), trivial⟩ : WFam)))
        (WCT9.famPoint a.layer a.leaf.val a.chain.val)
    have hn : WCT9.famSize a.layer (WCT9.famOf a.layer a.leaf.val) =
        WCT9.famSize a.layer (WCT9.famOf a.layer a.leaf.val) - 1 + 1 := by
      have := WCT9.famSize_pos a.layer (WCT9.famOf a.layer a.leaf.val); omega
    congr 1
    apply ofFn_congr_len hn
    intro k hk
    unfold leafFamily secOf
    simp only [Sum.elim_inl]
    split_ifs with h
    · rfl
    · exact absurd hk h
  · rfl
/-- An event's probability under a bind is at most a uniform bound on the continuations. -/
theorem probEvent_bind_le_const {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (E : β → Prop) (c : ENNReal)
    (h : ∀ x, Pr[E | f x] ≤ c) : Pr[E | mx >>= f] ≤ c := by
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' x, Pr[= x | mx] * c := ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
    _ = (∑' x, Pr[= x | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
    _ = c := one_mul c
/-- `probEvent_bind_le_of` with an additive pointwise error (top-nonce layer: `CapFail`). -/
theorem probEvent_bind_le_of_add {α β γ : Type} (mx : ProbComp α) (my : SPMF α) (f : α → ProbComp β) (g : α → SPMF γ)
    (E : β → Prop) (F : γ → Prop) (e : α → ENNReal) (hw : ∀ x, Pr[= x | mx] = Pr[= x | my])
    (h : ∀ x, Pr[E | f x] ≤ Pr[F | g x] + e x) :
    Pr[E | mx >>= f] ≤ Pr[F | my >>= g] + ∑' x, Pr[= x | mx] * e x := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← hw x, ← mul_add]
  gcongr
  exact h x
/-- `probEvent_bind_le_of` with a constant additive error. -/
theorem probEvent_bind_le_of_add_const {α β γ : Type} (mx : ProbComp α) (my : SPMF α) (f : α → ProbComp β)
    (g : α → SPMF γ) (E : β → Prop) (F : γ → Prop) (c : ENNReal) (hw : ∀ x, Pr[= x | mx] = Pr[= x | my])
    (h : ∀ x, Pr[E | f x] ≤ Pr[F | g x] + c) :
    Pr[E | mx >>= f] ≤ Pr[F | my >>= g] + c := by
  refine (probEvent_bind_le_of_add mx my f g E F (fun _ => c) hw h).trans (add_le_add le_rfl ?_)
  calc _ = (∑' x, Pr[= x | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
    _ = c := one_mul c
end Contact
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (mix PrefixDetermined)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem select_congr_prefix (L : EncLeaf) (floor : Nat) (f g : Fin (2 ^ 22) → HashOutput)
    (h : ∀ c, c.val < WCT9.searchLimit L.1.lay →
      (∀ r, capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f) = some r → c ≤ r.1) →
        f c = g c) :
    capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) g) =
      capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f) := by
  cases hs : capSel L (SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f) with
  | none =>
      have hrej : ∀ c : Fin (2 ^ 22), c.val < WCT9.searchLimit L.1.lay → decodeAt L floor (f c) = none := by
        intro c hc
        cases hf : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) f with
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
      cases hg : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) g with
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
      have hg : SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L floor) g = some (i, v) := by
        apply (SphincsSecurity.Concrete.FirstSuccessTable.select_some_iff _ g i v).mpr
        refine ⟨by rw [← hle i le_rfl]; exact hsome.1, fun j hj => ?_⟩
        rw [← hle j (le_of_lt hj)]
        exact hsome.2 j hj
      rw [hg]
      exact capSel_eq_some.mpr ⟨rfl, hlt⟩

noncomputable def rowPrefix (f : EncLeaf × Fin (2^22) → HashOutput) (x : EncLeaf × Fin (2^22)) : Prop :=
  ∃ remaining, rowsContext (Function.curry f) x.1.toWots=some remaining ∧
    x.2.val<WCT9.searchLimit x.1.1.lay ∧
    ∀ r, selectionAt (Function.curry f) x.1 remaining=some r → x.2≤r.1

theorem selectionAt_prefix_congr
    (f g : EncLeaf × Fin (2^22) → HashOutput)
    (hfg : ∀ x, rowPrefix f x → f x=g x) (L : EncLeaf) (remaining : Nat)
    (hctx : rowsContext (Function.curry f) L.toWots=some remaining) :
    selectionAt (Function.curry g) L remaining=selectionAt (Function.curry f) L remaining := by
  apply select_congr_prefix L (WCT9.CanonicalPolicy.threshold L.1.lay.val remaining)
  intro c hc hs
  exact hfg (L,c) ⟨remaining,hctx,hc,hs⟩

theorem option_bind_congr_some' {A B : Type} {o : Option A} {f g : A → Option B}
    (h : ∀ a, o = some a → f a = g a) : o.bind f = o.bind g := by
  cases o with
  | none => rfl
  | some a => exact h a rfl

theorem selectionAt_lt {rows : Rows} {L : EncLeaf} {remaining : Nat} {r : Fin (2^22) × Digest}
    (h : selectionAt rows L remaining = some r) : r.1.val < WCT9.searchLimit L.1.lay :=
  (capSel_eq_some.mp h).2

/-- Two row tables with the same selection and the same selected row give the same canonical result. -/
theorem selection_result_congr (f g : Rows) (L : EncLeaf) (remaining floor : Nat)
    (hsel : selectionAt g L remaining = selectionAt f L remaining)
    (hrow : ∀ r, selectionAt f L remaining = some r → g L r.1 = f L r.1) :
    ((selectionAt g L remaining).bind fun r => (WCT9.CanonicalPolicy.producerDecodeOut L.1.lay floor (g L r.1)).map
        fun found => (BitVec.ofNat 32 r.1.val, found)) =
      ((selectionAt f L remaining).bind fun r => (WCT9.CanonicalPolicy.producerDecodeOut L.1.lay floor (f L r.1)).map
        fun found => (BitVec.ofNat 32 r.1.val, found)) := by
  rw [hsel]
  exact option_bind_congr_some' (fun r hr => by rw [hrow r hr])

theorem rowsContext_prefix_congr
    (f g : EncLeaf × Fin (2^22) → HashOutput)
    (hfg : ∀ x, rowPrefix f x → f x=g x) (L : EncLeaf) :
    rowsContext (Function.curry g) L.toWots=rowsContext (Function.curry f) L.toWots := by
  apply Wots.CanonicalRef.context_congr_on WCT9.CanonicalPolicy.credit WotsExtract.SourceLeaf7
    (fun _ h hp => Wots.CanonicalRef.source_parent h hp) _ (source_toWots L)
  intro leaf hleaf remaining hctx
  let E := encLeafOf leaf hleaf
  have he : E.toWots=leaf := encLeafOf_toWots leaf hleaf
  have hc : rowsContext (Function.curry f) E.toWots=some remaining := by rw [he]; exact hctx
  rw [←he,searchRows_toWots,searchRows_toWots]
  exact selection_result_congr (Function.curry f) (Function.curry g) E remaining _
    (selectionAt_prefix_congr f g hfg E remaining hc)
    (fun r hsel => (hfg (E, r.1) ⟨remaining, hc, selectionAt_lt hsel,
      fun r' hr' => by rw [hsel] at hr'; cases hr'; exact le_rfl⟩).symm)

attribute [local irreducible] rowsContext selectionAt

private theorem option_bind_congr_on {A B : Type} {a b : Option A} {f g : A → Option B}
    (he : a=b) (hf : ∀x,b=some x→f x=g x) : a.bind f=b.bind g := by
  subst a
  cases hb : b with
  | none => rfl
  | some x => exact hf x hb

theorem selectionsOfRows_prefix_congr
    (f g : EncLeaf × Fin (2^22) → HashOutput)
    (hfg : ∀ x, rowPrefix f x → f x=g x) (L : EncLeaf) :
    selectionsOfRows (Function.curry g) L=selectionsOfRows (Function.curry f) L :=
  option_bind_congr_on (rowsContext_prefix_congr f g hfg L)
    (fun remaining hc => selectionAt_prefix_congr f g hfg L remaining hc)

theorem rowPrefix_determined : PrefixDetermined rowPrefix := by
  intro f g hfg x
  have hc := rowsContext_prefix_congr f g hfg x.1
  constructor
  · rintro ⟨remaining,hctx,hlimit,hs⟩
    have hctx' := hc.symm.trans hctx
    have he := selectionAt_prefix_congr f g hfg x.1 remaining hctx'
    exact ⟨remaining,hctx',hlimit,fun r hr => hs r (he.symm ▸ hr)⟩
  · rintro ⟨remaining,hctx,hlimit,hs⟩
    have he := selectionAt_prefix_congr f g hfg x.1 remaining hctx
    exact ⟨remaining,hc.trans hctx,hlimit,fun r hr => hs r (he ▸ hr)⟩

end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.CanonGraph
open SigGolfCandidate.T3.Security.LargeCoupling (uniform_equiv_bind uniform_join_bind uniform_mix mix)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType Rows := SampleableType.ofFintype _
noncomputable local instance : SampleableType (EncLeaf × Fin (2^22) → HashOutput) := SampleableType.ofFintype _
noncomputable local instance (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
noncomputable local instance (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) :=
  SampleableType.ofFintype _

noncomputable def residualPsi0 (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) (rows : Rows) (τ : U → HashOutput) : U → HashOutput :=
  SphincsSecurity.Concrete.UniformTableSplit.overwrite (encCell U hE labels) (encCell_injective U hE labels)
    (mix rowPrefix (Function.uncurry rows) (fun x => τ (encCell U hE labels x))) τ

theorem residualPsi0_prefix (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) (rows : Rows) (τ : U → HashOutput)
    (x : EncLeaf × Fin (2^22)) (hx : rowPrefix (Function.uncurry rows) x) :
    residualPsi0 U hE labels rows τ (encCell U hE labels x) = Function.uncurry rows x := by
  unfold residualPsi0
  rw [SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
  exact if_pos hx

theorem selections_residualPsi0 (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) (rows : Rows) (τ : U → HashOutput) (L : EncLeaf) :
    selectionsOfRows (fun L c => residualPsi0 U hE labels rows τ (encCell U hE labels (L,c))) L =
      selectionsOfRows rows L :=
  selectionsOfRows_prefix_congr (Function.uncurry rows)
    (fun x => residualPsi0 U hE labels rows τ (encCell U hE labels x))
    (fun x hx => (residualPsi0_prefix U hE labels rows τ x hx).symm) L

theorem residual_bind0 (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) {R : Type}
    (next : (U → HashOutput) → ProbComp R) :
    𝒮[($ᵗ (U → HashOutput) : ProbComp _) >>= next] =
      𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ => next (residualPsi0 U hE labels rows τ)] := by
  have hj : ∀ (rows : EncLeaf → Fin (2 ^ 22) → HashOutput) (g : EncLeaf × Fin (2 ^ 22) → HashOutput)
      (out : SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput),
      residualPsi0 U hE labels rows
        (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels) g out) =
      SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels)
        (mix rowPrefix (Function.uncurry rows) g) out := by
    intro rows g out
    unfold residualPsi0
    have hg : (fun x => SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) g out (encCell U hE labels x)) = g :=
      funext fun x => SphincsSecurity.Concrete.UniformTableSplit.join_embed _ _ _ _ x
    rw [hg, SphincsSecurity.Concrete.UniformTableSplit.overwrite_join]
  rw [evalSPMF_bind_congr' _ (fun rows => uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels)
    (fun τ => next (residualPsi0 U hE labels rows τ)))]
  simp only [hj]
  rw [uniform_equiv_bind (Equiv.curry (EncLeaf) (Fin (2 ^ 22)) HashOutput).symm.symm]
  simp only [Equiv.symm_symm, Equiv.curry_apply, Function.uncurry_curry]
  rw [uniform_mix rowPrefix rowPrefix_determined (fun R =>
    ($ᵗ (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) : ProbComp _) >>=
      fun out => next (SphincsSecurity.Concrete.UniformTableSplit.join (encCell U hE labels)
        (encCell_injective U hE labels) R out))]
  rw [uniform_join_bind (encCell U hE labels) (encCell_injective U hE labels) next]

#print axioms selections_residualPsi0
end ClaudeWCT.W9.T3.Security.CanonEncoding.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord seedView)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding (EncLeaf Selections Selection childIndex childIndex_treeBits)
open ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeCoupling (mix uniform_equiv_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] CanonEncoding.Paired.rowsContext CanonEncoding.Paired.selectionAt

def AuxConsistent (a : AuxData) : Prop := a.sel=selectionsOfRows a.rows

section Public
variable (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U)
noncomputable def presentTable (τ : U → HashOutput) : U → HashOutput := fun x => LargeResidual.Paired.rowPresent x.val (τ x)
noncomputable def presentTableEquiv : (U → HashOutput) ≃ (U → HashOutput) :=
  Equiv.piCongrRight fun x : U => LargeResidual.Paired.rowPresent x.val
noncomputable def residualPsi (labels : Labels) (rows : Rows) (τ : U → HashOutput) : U → HashOutput :=
  CanonEncoding.Paired.residualPsi0 U hE labels rows (presentTable U τ)
noncomputable def tablePsi (sec : Secrets) (vals : LargeResidual.Coord → Digest) (nv : Message → Digest)
    (τ : U → HashOutput) (a : AuxData) : Answers :=
  Wots.eagerAnswers U (privPsi sec nv a.priv)
    (CanonGraph.Paired.Filtered.programmed U hU sec (LargeResidual.Paired.routerLabels vals a)
      (residualPsi U hE (LargeResidual.Paired.routerLabels vals a) a.rows τ))

theorem encCell_row (labels : Labels) (L : EncLeaf) (c : Fin (2^22)) :
    (CanonEncoding.Paired.encCell U hE labels (L,c)).val = Wots.encRow L.toWots (msgLabel labels L) (BitVec.ofNat 32 c.val) 0 := by
  rw [CanonEncoding.Paired.encCell_val,Wots.encRow_zero]
  rfl

theorem paired_ftsLabel_top (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) :
    CanonGraph.Paired.ftsLabel labels index coord 6 b.val =
      Extract.Paired.proj (CanonGraph.Node.wctNode (ftsTopNode index coord b)).toPos
        (labels (.wctNode (ftsTopNode index coord b))) := by
  unfold CanonGraph.Paired.ftsLabel
  rw [if_neg (by omega)]
  unfold ftsNodeAt
  rw [dif_pos (show 6-1<6 ∧ b.val<2^(7-(6-1)-1) by have := b.isLt;omega)]
  rfl

theorem msgLabel_router (vals : LargeResidual.Coord → Digest) (a : AuxData) (L : EncLeaf) :
    msgLabel (LargeResidual.Paired.routerLabels vals a) L = LargeResidual.msgVals vals L := by
  unfold msgLabel LargeResidual.msgVals
  by_cases hl : L.1.lay.val<3
  · rw [dif_pos hl,dif_pos hl]
    congr 1
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
    · refine (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans ?_
      rw [selNode_of_cap_one (trialCap_lower (fun h => absurd (congrArg Fin.val h) (by simp [topNode])) _) rfl]
      exact CanonGraph.Paired.joinLabels_node _ _ _
  · rw [dif_neg hl,dif_neg hl]
    congr 1
    · exact (paired_ftsLabel_top _ _ _ 0).trans (CanonGraph.Paired.joinLabels_val _ _ _)
    · exact (paired_ftsLabel_top _ _ _ 1).trans (CanonGraph.Paired.joinLabels_val _ _ _)

theorem sel_psi (a : AuxData) (ha : AuxConsistent a) (labels : Labels) (τ : U → HashOutput) (L : EncLeaf) :
    selectionsOfRows (fun L c => residualPsi U hE labels a.rows τ (CanonEncoding.Paired.encCell U hE labels (L,c))) L = a.sel L :=
  (selections_residualPsi0 U hE labels a.rows (presentTable U τ) L).trans (congrFun ha.symm L)

end Public

private theorem context_prefix_iff (context : Option Nat) (select : Nat → CanonEncoding.Selection)
    (c : Fin (2^22)) (limit : Nat) :
    (∃remaining,context=some remaining ∧ c.val<limit ∧ ∀r,select remaining=some r→c≤r.1) ↔
      context.isSome ∧ c.val<limit ∧ ∀r,context.bind select=some r→c.val≤r.1.val := by
  cases context with
  | none =>
      constructor
      · rintro ⟨remaining,he,_,_⟩;cases he
      · rintro ⟨he,_,_⟩;cases he
  | some n =>
      constructor
      · rintro ⟨remaining,he,hlim,hs⟩
        have hn : n=remaining := Option.some.inj he
        subst remaining
        exact ⟨rfl,hlim,fun r hr => Fin.le_def.mp (hs r hr)⟩
      · rintro ⟨_,hlim,hs⟩
        exact ⟨n,rfl,hlim,fun r hr => Fin.le_def.mpr (hs r hr)⟩

theorem rowPrefix_iff (a : AuxData) (ha : AuxConsistent a) (L : EncLeaf) (c : Fin (2^22)) :
    CanonEncoding.Paired.rowPrefix (Function.uncurry a.rows) (L,c) ↔ LargeResidual.Paired.PrefixRow a L (BitVec.ofNat 32 c.val) := by
  have hc : (BitVec.ofNat 32 c.val).toNat=c.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := c.isLt;omega)
  unfold LargeResidual.Paired.PrefixRow
  rw [hc,ha]
  exact context_prefix_iff (rowsContext a.rows L.toWots) (selectionAt a.rows L) c (WCT9.searchLimit L.1.lay)

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord seedView)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding (EncLeaf Selections Selection childIndex childIndex_treeBits)
open ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeCoupling (mix uniform_equiv_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] CanonEncoding.Paired.rowsContext CanonEncoding.Paired.selectionAt

section Coherence
variable (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U)
theorem coherent_psi (sec : Secrets) (vals : Coord → Digest) (nv : Message → Digest) (τ : U → HashOutput)
    (a : AuxData) (ha : AuxConsistent a) (hv : seedView sec = fun x => vals (.inr x))
    (hcap : ¬ CanonGraph.CapFail (LargeResidual.Paired.routerLabels vals a)) :
    LargeResidual.Paired.Coherent U (tablePsi U hU hE sec vals nv τ a) vals nv τ a := by
  set s : Secrets := sec with hs
  set labels := LargeResidual.Paired.routerLabels vals a with hlabels
  set res := residualPsi U hE labels a.rows τ with hres
  set o := nonceOver (privateEquiv a.priv).2 nv with ho
  have hT : tablePsi U hU hE sec vals nv τ a = CanonGraph.eagerAnswers (privateEquiv.symm (s, o)) U
      (CanonGraph.Paired.Filtered.programmed U hU s labels res) := by
    unfold tablePsi
    rw [eagerAnswers_eq]
    rfl
  have hsec : secretsOf (tablePsi U hU hE sec vals nv τ a) = s := by
    rw [hT, secretsOf_eager, privateSecrets_symm]
  have hpubX : ∀ (X : HashInput) (hX : X ∈ U), tablePsi U hU hE sec vals nv τ a (.inl (.inr X)) =
      CanonGraph.Paired.Filtered.programmed U hU s labels res ⟨X, hX⟩ := by
    intro X hX
    rw [hT]
    exact eagerAnswers_mem _ U _ ⟨X, hX⟩
  refine ⟨?_, by rw [hsec]; exact hv, ?_, ?_, ?_, ?_, ?_, ?_,ha,hcap⟩
  · rw [hT]
    apply CanonGraph.Paired.Filtered.agrees_of_programmed U hU _ labels res
    intro x
    rw [secretsOf_eager,privateSecrets_symm,eagerAnswers_mem]
  ·
    intro X hX hcell hpre
    rw [hpubX X hX, CanonGraph.Paired.Filtered.programmed_other U hU s labels res ⟨X, hX⟩ (fun N hused => by
      have := hcell N hused
      rw [hsec] at this
      exact this)]
    by_cases hr : (⟨X, hX⟩ : U) ∈ Set.range (CanonEncoding.Paired.encCell U hE labels)
    · obtain ⟨x, hx⟩ := hr
      rw [hres, residualPsi, CanonEncoding.Paired.residualPsi0, ← hx, SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
      unfold mix
      rw [if_neg]
      · show LargeResidual.Paired.rowPresent (CanonEncoding.Paired.encCell U hE labels x).val (τ (CanonEncoding.Paired.encCell U hE labels x)) = _
        rw [show (CanonEncoding.Paired.encCell U hE labels x).val = X from congrArg Subtype.val hx]
      intro hpx
      apply hpre
      obtain ⟨L, c⟩ := x
      refine ⟨L, BitVec.ofNat 32 c.val, ?_, (rowPrefix_iff a ha L c).mp hpx⟩
      have hv := congrArg Subtype.val hx
      rw [encCell_row, msgLabel_router] at hv
      exact hv.symm
    · rw [hres, residualPsi, CanonEncoding.Paired.residualPsi0, SphincsSecurity.Concrete.UniformTableSplit.overwrite_outside _ _ _ _ _ hr]
      rfl
  ·
    intro L ctr hp
    have hp1 : ctr.toNat < 2 ^ 22 := lt_of_lt_of_le hp.2.1 (WCT9.searchLimit_le L.1.lay)
    have hc : BitVec.ofNat 32 (⟨ctr.toNat, hp1⟩ : Fin (2 ^ 22)).val = ctr := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hp1; omega)
    have hX : Wots.encRow L.toWots (LargeResidual.msgVals vals L) ctr 0 = (CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).val := by
      rw [encCell_row, msgLabel_router, hc]
    rw [hX, hpubX _ (CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).property]
    rw [CanonGraph.Paired.Filtered.programmed_other U hU s labels res _ (fun N _ => CanonEncoding.Paired.encodingQuery_ne_cell _ s N labels)]
    rw [hres, residualPsi, CanonEncoding.Paired.residualPsi0, show (⟨(CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).val,
      (CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩)).property⟩ : U) = CanonEncoding.Paired.encCell U hE labels (L, ⟨ctr.toNat, hp1⟩) from rfl,
      SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
    unfold mix
    rw [if_pos ((rowPrefix_iff a ha L _).mpr (by rw [hc]; exact hp))]
    unfold LargeResidual.Paired.prefixValue
    rw [dif_pos hp1]
    rfl
  ·
    intro L
    have hpub : ∀ x : U, tablePsi U hU hE sec vals nv τ a (.inl (.inr x.val)) =
        CanonGraph.Paired.Filtered.programmed U hU (secretsOf (tablePsi U hU hE sec vals nv τ a)) labels res x := by
      intro x
      rw [hsec]
      exact hpubX x.val x.property
    rw [referenceSearch_eq_filtered U hU hE _ labels res hpub L]
    rw [hres,sel_psi U hE a ha labels τ L]
    cases hsel : a.sel L with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      have hctxsel : CanonEncoding.Paired.selectionsOfRows a.rows L = some r := by
        rw [← congrFun ha L]; exact hsel
      unfold CanonEncoding.Paired.selectionsOfRows at hctxsel
      cases hctx : CanonEncoding.Paired.rowsContext a.rows L.toWots with
      | none => rw [hctx] at hctxsel; cases hctxsel
      | some remaining =>
        rw [hctx, Option.bind_some] at hctxsel
        have hcap := CanonEncoding.Paired.selectionAt_lt hctxsel
        have hpre : LargeResidual.Paired.PrefixRow a L (BitVec.ofNat 32 r.1.val) := by
          have hc : (BitVec.ofNat 32 r.1.val).toNat = r.1.val := by
            rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := r.1.isLt; omega)
          refine ⟨by rw [hctx]; rfl, by rw [hc]; exact hcap, ?_⟩
          intro r' hr'
          rw [hsel] at hr'; cases hr'
          rw [hc]
        have hrow : residualPsi U hE labels a.rows τ (CanonEncoding.Paired.encCell U hE labels (L, r.1)) =
            a.rows L r.1 := by
          rw [residualPsi, CanonEncoding.Paired.residualPsi0,
            SphincsSecurity.Concrete.UniformTableSplit.overwrite_embed]
          unfold mix
          rw [if_pos ((rowPrefix_iff a ha L r.1).mpr hpre)]
          rfl
        rw [hrow]
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
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord seedView)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding (EncLeaf Selections Selection childIndex childIndex_treeBits)
open ClaudeWCT.W9.T3.Security.CanonEncoding.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open SigGolfCandidate.T3.Security.LargeCoupling (mix uniform_equiv_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] CanonEncoding.Paired.rowsContext CanonEncoding.Paired.selectionAt

open SigGolfCandidate.T3.Security.LargeCoupling (evalSPMF_bind_comm)
noncomputable local instance : SampleableType FullGame.FullTable := CanonGraph.instSampleableTypeFullTable_canonGraph
noncomputable local instance : SampleableType (Message → Digest) := SigGolfCandidate.T3.Security.LargeCoupling.Samplers.samplerNonces
noncomputable local instance : SampleableType Rows := SampleableType.ofFintype _
noncomputable local instance : SampleableType LowLabels := CanonGraph.instSampleableTypeLowLabels
noncomputable local instance : SampleableType Labels := CanonGraph.instSampleableTypeLabels_1
noncomputable local instance : SampleableType Secrets := CanonGraph.instSampleableTypeSecrets
noncomputable local instance : SampleableType OtherHalves := CanonGraph.instSampleableTypeOtherHalves
noncomputable local instance (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _

theorem tables_bind {Result : Type} (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (privateEquiv.symm (secrets, other)) (CanonGraph.Paired.Filtered.programmed U hU secrets labels residual)] := by
  refine (CanonGraph.private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)).trans ?_
  refine evalSPMF_bind_congr' ($ᵗ Secrets : ProbComp _) fun secrets => ?_
  refine evalSPMF_bind_congr' ($ᵗ OtherHalves : ProbComp _) fun other => ?_
  exact CanonGraph.Paired.Filtered.uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)
theorem residual_bind (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) {R : Type}
    (next : (U → HashOutput) → ProbComp R) :
    𝒮[($ᵗ (U → HashOutput) : ProbComp _) >>= next] =
      𝒮[($ᵗ Rows : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ => next (residualPsi U hE labels rows τ)] := by
  rw [CanonEncoding.Paired.residual_bind0 U hE labels next]
  refine evalSPMF_bind_congr' _ fun rows => ?_
  exact uniform_equiv_bind (presentTableEquiv U)
    (fun τ => next (CanonEncoding.Paired.residualPsi0 U hE labels rows τ))
theorem law_derived (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv => ($ᵗ LowLabels : ProbComp _) >>= fun low =>
        ($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (CanonGraph.Paired.Filtered.programmed U hU sec (CanonGraph.Paired.joinLabels low high) (residualPsi U hE (CanonGraph.Paired.joinLabels low high) rows τ)))] := by
  simp only [eagerAnswers_eq]
  rw [tables_bind U hU (fun priv pub => next (CanonGraph.eagerAnswers priv U pub))]
  refine (evalSPMF_bind_congr' ($ᵗ Secrets : ProbComp _) fun (sec : Secrets) => others_bind _).trans ?_
  refine evalSPMF_bind_congr' ($ᵗ Secrets : ProbComp _) fun sec => ?_
  refine evalSPMF_bind_congr' ($ᵗ FullGame.FullTable : ProbComp _) fun priv' => ?_
  refine evalSPMF_bind_congr' ($ᵗ (Message → Digest) : ProbComp _) fun nv => ?_
  rw [CanonGraph.Paired.labels_bind]
  refine evalSPMF_bind_congr' _ fun low => evalSPMF_bind_congr' _ fun high => ?_
  exact residual_bind U hE (CanonGraph.Paired.joinLabels low high) _
theorem law_target (U : Finset HashInput) (hU : CanonGraph.Paired.canonInputs ⊆ U) (hE : encInputs ⊆ U) {R : Type}
    (next : Answers → ProbComp R) :
    𝒮[($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun pub =>
        next (Wots.eagerAnswers U priv pub)] =
      𝒮[($ᵗ LowLabels : ProbComp _) >>= fun high =>
        ($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _) >>= fun rows =>
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv' =>
        ($ᵗ Secrets : ProbComp _) >>= fun sec => ($ᵗ (Message → Digest) : ProbComp _) >>= fun nv =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => ($ᵗ (U → HashOutput) : ProbComp _) >>= fun τ =>
        next (CanonGraph.eagerAnswers (privateEquiv.symm (sec, nonceOver (privateEquiv priv').2 nv)) U
          (CanonGraph.Paired.Filtered.programmed U hU sec (CanonGraph.Paired.joinLabels low high) (residualPsi U hE (CanonGraph.Paired.joinLabels low high) rows τ)))] := by
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

noncomputable def auxOf (high : LowLabels) (rows : Rows) (priv : FullGame.FullTable) : AuxData :=
  ⟨high,rows,selectionsOfRows rows,priv⟩
theorem auxOf_consistent (high : LowLabels) (rows : Rows) (priv : FullGame.FullTable) :
    AuxConsistent (auxOf high rows priv) := rfl
noncomputable def initComp : ProbComp AuxData :=
  ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ Rows : ProbComp _) >>= fun rows =>
      ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv => pure (auxOf high rows priv)
noncomputable def initLaw : PMF AuxData := liftM initComp
theorem initLaw_spmf : (liftM initLaw : SPMF AuxData) = 𝒮[initComp] := by
  apply SPMF.ext
  intro a
  rw [SPMF.liftM_apply, ← PMF.probOutput_eq_apply, ← probEvent_eq_eq_probOutput, initLaw,
    MonitoredPrivate.event_lift, probEvent_eq_eq_probOutput]
  rfl

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord WJunk)
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
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open SigGolfCandidate.T3.Security.LargeCoupling (completeRows_none probEvent_bind_congr_eq)
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
theorem router_side (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q) LargeResidual.initial] =
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] >>= fun x =>
        𝒮[($ᵗ (Cell (Wots.PairedReference.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q (view x) τ (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q (auxOf high rows priv))
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
def RealContact (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  ContactR adversary q x.1 x.2 ∧ NoOvR adversary x.1 x.2
theorem loggedOutputs_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :
    WPair.Paired.loggedOutputs A log = WPair.Paired.loggedOutputs T log := by
  unfold WPair.Paired.loggedOutputs WPair.Paired.signedOutput
  congr 1
  funext entry
  congr 1
  funext σ
  rw [digestSearch_short hAT]
theorem noOvR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (rec : FirstHit.Recorded Bool) : NoOvR adversary rec A ↔ NoOvR adversary rec T := by
  unfold NoOvR LogNoOverflow
  simp only [loggedOutputs_short hAT]
/-- The contact event with the FTS no-overflow side condition (on the recorded trace). -/
def ContactNO (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  Contact adversary q z ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2
noncomputable def fixedNext (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers) : ProbComp (FirstHit.Recorded Bool × Answers) :=
  (fun r => (r, T)) <$> Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)
theorem contact_real_side (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] =
      Pr[RealContact adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.PairedReference.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.PairedReference.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.PairedReference.completed_eager_cut adversary q hq (fun rec A => ContactR adversary q rec A ∧ NoOvR adversary rec A)
  rw [show (ContactNO adversary q) = fun z => ContactR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
    NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 from rfl, h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => ContactR adversary q x.1 (Wots.Ref.cut x.1.state x.2) ∧
      NoOvR adversary x.1 (Wots.Ref.cut x.1.state x.2)) = RealContact adversary q := by
    funext x
    exact propext (and_congr (contactR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
      (noOvR_short (Wots.Ref.cut_shortAgree _ _) adversary x.1))
  rw [h2]
  unfold Wots.PairedReference.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord WJunk)
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
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open SigGolfCandidate.T3.Security.LargeCoupling (completeRows_none probEvent_bind_congr_eq)
/-- The `CapFail` error of the coupling, given the high halves: the probability over the hidden world that the
router labels exhaust a top trial cap. -/
noncomputable def capErr (high : LowLabels) : ENNReal :=
  ∑' x, Pr[= x | ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _)] *
    (if CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) then 1 else 0)

theorem capErr_le :
    ∑' high, Pr[= high | ($ᵗ LowLabels : ProbComp _)] * capErr high ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have e1 : ∀ high, capErr high = Pr[fun l => CanonGraph.CapFail l |
      ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] := by
    intro high
    unfold capErr
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    rw [probEvent_pure]
  have e2 : ∀ high, Pr[fun l => CanonGraph.CapFail l |
      ($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] =
      Pr[fun l => CanonGraph.CapFail l | ($ᵗ LowLabels : ProbComp _) >>= fun low =>
        (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] := by
    intro high
    have hw := world_split (fun (_ : Secrets) (_ : Message → Digest) low =>
      (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels))
    have h1 : 𝒮[($ᵗ Secrets : ProbComp _) >>= fun _ => ($ᵗ (Message → Digest) : ProbComp _) >>= fun _ =>
        ($ᵗ LowLabels : ProbComp _) >>= fun low => (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] =
        𝒮[($ᵗ LowLabels : ProbComp _) >>= fun low => (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] := by
      rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _,
        OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _]
    have h2 : 𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
        ($ᵗ (WJunk → LargeResidual.Digest) : ProbComp _) >>= fun _ =>
          (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] =
        𝒮[($ᵗ (ClaudeWCT.W9.T3.Security.FamResidual.Hid WCoord) : ProbComp _) >>= fun x =>
          (pure (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) : ProbComp Labels)] :=
      evalSPMF_bind_congr' _ fun _ => OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
    exact probEvent_congr' (fun _ _ => Iff.rfl) (h2.symm.trans (hw.symm.trans h1))
  simp only [e1, e2]
  rw [← probEvent_bind_eq_tsum]
  let _ : SampleableType Labels := SampleableType.ofFintype _
  have h3 : 𝒮[($ᵗ LowLabels : ProbComp _) >>= fun high => ($ᵗ LowLabels : ProbComp _) >>= fun low =>
      (pure (CanonGraph.Paired.joinLabels low high) : ProbComp Labels)] = 𝒮[($ᵗ Labels : ProbComp Labels)] := by
    rw [OracleComp.DeferredSampling.evalSPMF_bind_comm]
    have := CanonGraph.Paired.labels_bind (fun l => (pure l : ProbComp Labels))
    simp only [bind_pure] at this
    rw [← this]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) h3]
  have hc := CanonGraph.prob_capFail_le
  refine le_trans (le_of_eq ?_) hc
  exact probEvent_congr' (fun _ _ => Iff.rfl) (SigGolfCandidate.T3.Security.LargeCoupling.evalSPMF_uniform_inst _ _)

set_option maxHeartbeats 4000000 in
theorem contact_le_lazy (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        lazyRun (auxLaw initLaw) q (router (Wots.PairedReference.referenceInputs adversary) adversary q) LargeResidual.initial] +
        (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have hU : CanonGraph.Paired.canonInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    CanonGraph.Paired.canonInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  have hE : CanonGraph.encInputs ⊆ Wots.PairedReference.referenceInputs adversary :=
    CanonGraph.encInputs_subset_publicUniverse.trans (Wots.PairedReference.Ref.referenceInputs_universe adversary)
  rw [contact_real_side, router_side,
    probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.PairedReference.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine le_trans (probEvent_bind_le_of_add _ _ _ _ _ _ capErr (weight_self _) fun high => ?_)
    (add_le_add le_rfl capErr_le)
  refine probEvent_bind_le_of_add_const _ _ _ _ _ _ (capErr high) (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of_add_const _ _ _ _ _ _ (capErr high) (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine le_trans (probEvent_bind_le_of_add _ _ _ _ _ _
    (fun x => if CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) then 1 else 0)
    (weight_self _) fun x => ?_) (add_le_add le_rfl (le_of_eq ?_))
  swap
  · unfold capErr
    refine tsum_congr fun x => ?_
    rw [probOutput_uniformSample]
  by_cases hcf : CanonGraph.CapFail (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high)
  · rw [if_pos hcf]
    exact le_trans probEvent_le_one le_add_self
  rw [if_neg hcf, add_zero]
  refine probEvent_bind_le_const _ _ _ _ fun jk => ?_
  have hτ : ∀ (k : (Wots.PairedReference.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.PairedReference.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm (secOf x jk,
          nonceOver (privateEquiv priv).2 (fun m => x.1 (.inr m)))) (Wots.PairedReference.referenceInputs adversary)
          (CanonGraph.Paired.Filtered.programmed (Wots.PairedReference.referenceInputs adversary) hU (secOf x jk)
            (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high)
            (residualPsi (Wots.PairedReference.referenceInputs adversary) hE (CanonGraph.Paired.joinLabels (fun N => x.1 (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c)) (fun m => view x (.inr m)) τ
          (auxOf high rows priv) := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealContact
    rw [probEvent_map]
    have hcoh := coherent_psi (Wots.PairedReference.referenceInputs adversary) hU hE (secOf x jk) (fun c => view x (.inl c))
        (fun m => view x (.inr m)) τ (auxOf high rows priv) (auxOf_consistent _ _ _) (seedView_secOf x jk) hcf
    have h := table_contact_le adversary q hq initLaw hcoh
      (hcoh.source (evalWithAnswerFn _ keygen).2 (Correctness.keygen_correct _).2.1)
    have hlab : Sum.elim (fun c => view x (.inl c)) (fun m => view x (.inr m)) = view x := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
