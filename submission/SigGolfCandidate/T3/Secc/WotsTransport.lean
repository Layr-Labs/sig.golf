import SigGolfCandidate.T3.Secc.WotsTransportTable

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
noncomputable def completionComp : ProbComp SeccLaw.CompletionTables :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun publicTable => pure (privateTable, publicTable)
theorem completionComp_eq :
    (liftM completionComp : PMF SeccLaw.CompletionTables) = PMF.uniformOfFintype SeccLaw.CompletionTables := by
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [PMF.uniformOfFintype_apply, ← PMF.probOutput_eq_apply]
  have hl : Pr[= (a, b) | (liftM completionComp : PMF SeccLaw.CompletionTables)] = Pr[= (a, b) | completionComp] := by
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, MonitoredPrivate.event_lift]
  rw [hl]
  unfold completionComp
  change Pr[=(a, b) | (($ᵗ FullGame.FullTable : ProbComp _) >>= fun x =>
    ($ᵗ SeccLaw.PublicTable : ProbComp _) >>= fun y => pure (id x, id y))] = _
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map, probOutput_uniformSample]
  rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)), ← Nat.cast_mul]
  congr 2
  rw [← Fintype.card_prod]
theorem pmf_probEvent_mono {α : Type} (p : PMF α) {E F : α → Prop} (h : ∀ x ∈ p.support, E x → F x) :
    Pr[E | p] ≤ Pr[F | p] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hE : E x
    · rw [if_pos hE, if_pos (h x hx hE)]
    · rw [if_neg hE]
      exact zero_le
  · have hz' : p x = 0 := (PMF.apply_eq_zero_iff p x).mpr hx
    have hz : Pr[= x | p] = 0 := by
      rw [PMF.probOutput_eq_apply]
      exact hz'
    split_ifs <;> simp [hz, hz']
theorem restrict_uniform {β : Type} (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V)
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
    funext query
    rw [Function.comp_apply]
    exact FiniteRowSplit.publicTableEquiv_reconstruct SeccLaw.publicUniverse V hsub chainTable extra query
  simp only [hc]
  exact evalSPMF_bind_const_neverFails _ (by simp) _
theorem completeWith_eq_cut (V : Finset HashInput) (hsub : SeccLaw.publicUniverse ⊆ V) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : V → HashOutput) :
    SeccLaw.completeWith state (privateTable, publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) =
      cut state (fillAnswers V state privateTable publicTable) := by
  funext query
  rcases query with (n | x) | c
  · rfl
  · change (state.2 x).getD (SeccLaw.publicFill (publicTable ∘ FiniteRowSplit.includeRow SeccLaw.publicUniverse V hsub) x) =
      (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then
        (state.2 x).getD (SphincsSecurity.Concrete.finiteHashAnswer ∅ V publicTable x) else (0 : HashOutput))
    cases hx : state.2 x with
    | some v =>
        rw [if_pos (show x ∈ SeccLaw.publicUniverse ∨ (some v).isSome = true from Or.inr rfl),
          Option.getD_some, Option.getD_some]
    | none =>
        rw [Option.getD_none, Option.getD_none]
        unfold SeccLaw.publicFill
        by_cases hu : x ∈ SeccLaw.publicUniverse
        · rw [dif_pos hu, if_pos (Or.inl hu), SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x (hsub hu) rfl,
            Function.comp_apply]
          rfl
        · rw [dif_neg hu, if_neg (fun h => h.elim hu (fun h' => by simp at h'))]
  · rfl
end Ref
end SigGolfCandidate.T3.Security.Wots
