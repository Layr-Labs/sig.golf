import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Moment
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufSigned
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransport
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Budgets

namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots.Ref (eagerSide cut fillAnswers)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_injective searchQuery_length)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_signerCompleteBound : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_signerCompleteBound :
    SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) :=
  ClaudeWCT.W9.T3.Presampling.tableSampler
theorem signerComplete_of_searches (A : Correctness.Answers)
    (h : ClaudeWCT.W9.T3.Correctness.SearchesSucceed A) : SignerComplete A := by
  refine ⟨fun rho m => ?_, fun lay _ tree leaf msg htree hleaf => ?_⟩
  · obtain ⟨found, hf⟩ := h.1 (rho, m)
    rw [hf]
    rfl
  · have hr : tree * 2 ^ height lay + leaf < 2 ^ 32 := by
      rename_i hlay
      fin_cases lay
      · exact absurd rfl hlay
      all_goals simp only [height] at hleaf ⊢; norm_num at hleaf ⊢; omega
    obtain ⟨found, hf⟩ := ClaudeWCT.W9.T3.Correctness.encodingSearchesSucceedBC_msg A h.2 lay
      tree leaf hleaf hr msg
    change (evalWithAnswerFn A (WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay))).isSome
    rw [hf]
    rfl
theorem digestSearch_respects (rho : Digest) (m : Message) :
    ∀ fuel c, Wots.Ref.ShortRespects (WCT9.digestSearch rho m c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact Wots.Ref.ShortRespects.pure' _
  | succ fuel ih =>
      intro c
      simp only [WCT9.digestSearch, digest]
      refine Wots.Ref.ShortRespects.bind (fun A' T' hAT' => ?_) fun output => ?_
      · unfold publicHash
        change A' (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c))))) =
          T' (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))))
        refine hAT'.public _ ?_
        rw [SigGolfCandidate.T3.Security.BPB.pad64_digestInput, SigGolfCandidate.T3.Security.BPB.digestInput_length]
        unfold SeccLaw.maxInputLength
        omega
      · split
        · exact Wots.Ref.ShortRespects.pure' _
        · exact ih _
theorem signerComplete_short {A T : Correctness.Answers} (h : Wots.Ref.ShortAgree A T) (hc : SignerComplete A) :
    SignerComplete T := by
  refine ⟨fun rho m => ?_, fun lay hl tree leaf msg ht hle => ?_⟩
  · rw [← digestSearch_respects rho m WCT9.digestAttemptLimit 0 A T h]
    exact hc.1 rho m
  · rw [← Wots.Ref.layerCounterSearch_respects lay tree leaf msg 0 (WCT9.searchLimit lay) A T h]
    exact hc.2 lay hl tree leaf msg ht hle
def searchTable (A : Correctness.Answers) : SearchKey → HashOutput := fun key => A (.inl (.inr (searchQuery key)))
theorem not_tableGood_of_incomplete (A : Correctness.Answers) (h : ¬SignerComplete A) :
    ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable A) := fun hg =>
  h (signerComplete_of_searches A
    ((ClaudeWCT.W9.T3.Budgets.tableGood_iff_searchesSucceed (searchTable A) A (fun _ => rfl)).mp hg))
theorem searchQuery_mem (adversary : AdversaryP) (key : SearchKey) :
    searchQuery key ∈ Wots.referenceInputs adversary :=
  Wots.Ref.referenceInputs_universe adversary
    (SeccLaw.mem_publicUniverse _ (by rw [searchQuery_length]; decide))
theorem searchTable_cut (state : LazyPrivate.State) (F : Correctness.Answers) :
    searchTable (cut state F) = searchTable F := by
  funext key
  unfold searchTable
  exact SigGolfCandidate.T3.Security.Wots.Ref.cut_shortAgree state F _
    (show (searchQuery key).length ≤ SeccLaw.maxInputLength by rw [searchQuery_length]; decide)
theorem searchTable_fill (adversary : AdversaryP) (privateTable : FullGame.FullTable)
    (publicTable : Wots.referenceInputs adversary → HashOutput) :
    searchTable (fillAnswers (Wots.referenceInputs adversary) (∅, ∅) privateTable publicTable) =
      fun key => publicTable ⟨searchQuery key, searchQuery_mem adversary key⟩ := by
  funext key
  unfold searchTable
  rw [SigGolfCandidate.T3.Security.Wots.Ref.fillAnswers_empty]
  exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (searchQuery_mem adversary key) rfl
theorem eager_incomplete_le (adversary : AdversaryP) :
    Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable (cut pair.1.state pair.2)) |
        eagerSide (Wots.referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun outputs => ¬ClaudeWCT.W9.T3.Budgets.tableGood outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  unfold eagerSide
  refine probEvent_bind_le_of_forall_le fun privateTable _ => ?_
  refine (probEvent_bind_le_probEvent (p := fun publicTable : Wots.referenceInputs adversary → HashOutput =>
    ¬ClaudeWCT.W9.T3.Budgets.tableGood (fun key => publicTable ⟨searchQuery key, searchQuery_mem adversary key⟩))
    fun publicTable _ hgood => ?_).trans ?_
  · rw [probEvent_eq_zero_iff]
    intro pair _ hbad
    rw [support_map] at *
    obtain ⟨result, -, rfl⟩ := (Set.mem_image _ _ _).mp ‹pair ∈ _›
    apply hbad
    rw [searchTable_cut, searchTable_fill]
    exact not_not.mp hgood
  · let e : SearchKey → Wots.referenceInputs adversary := fun key => ⟨searchQuery key, searchQuery_mem adversary key⟩
    have he : Function.Injective e := fun k k' h => searchQuery_injective (congrArg Subtype.val h)
    have hlaw := evalSPMF_uniformSample_map_comp_injective (R := HashOutput) he
    have hp : Pr[fun publicTable : Wots.referenceInputs adversary → HashOutput =>
        ¬ClaudeWCT.W9.T3.Budgets.tableGood (fun key => publicTable (e key)) |
          ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] =
        Pr[fun outputs => ¬ClaudeWCT.W9.T3.Budgets.tableGood outputs |
          (do let g ← ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _); pure (g ∘ e))] := by
      rw [bind_pure_comp, probEvent_map]
      rfl
    rw [hp, probEvent_congr' (fun _ _ => Iff.rfl) hlaw]
theorem signerIncomplete_le_table (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => ¬SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun outputs => ¬ClaudeWCT.W9.T3.Budgets.tableGood outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  calc Pr[fun z => ¬SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq]
      ≤ Pr[fun z => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable z.2) |
          SeccLaw.completedExperiment adversary q hq] :=
        Wots.Ref.pmf_probEvent_mono _ fun z _ h => not_tableGood_of_incomplete z.2 h
    _ = Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable pair.2) |
          (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable pair.2) |
          Wots.Ref.recordedCompleted adversary] := by
        rw [Wots.Ref.completed_map, MonitoredPrivate.event_lift]
    _ = Pr[fun pair => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable (cut pair.1.state pair.2)) |
          eagerSide (Wots.referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] :=
        Wots.Ref.recorded_eq_eager adversary fun _ A => ¬ClaudeWCT.W9.T3.Budgets.tableGood (searchTable A)
    _ ≤ _ := eager_incomplete_le adversary
theorem signerIncomplete_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => ¬SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] ≤ 1 / (2 : ENNReal) ^ 298 := by
  refine (signerIncomplete_le_table adversary q hq).trans ?_
  refine (ClaudeWCT.W9.T3.Budgets.tableGood_failure_le _ _ ClaudeWCT.W9.T3.Budgets.digest_failure_power_900
    ClaudeWCT.W9.T3.ProducerV5.producer_failure_power).trans ?_
  have hreal : (2 : ℝ) ^ 384 * (1 / 2 ^ 900) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ 298 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num), ENNReal.ofReal_ofNat,
    SigGolfCandidate.T3.Budgets.ofReal_inv_two_pow] using hcast
end ClaudeWCT.W9.T3.Security.BPB

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_injective searchQuery_length)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

def outputs (A : Answers) : SearchKey → HashOutput := fun key => A (.inl (.inr (searchQuery key)))

theorem query_mem (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (key : SearchKey) :
    searchQuery key ∈ PairedReference.referenceInputs adversary := by
  apply Finset.mem_union_left
  exact SeccLaw.mem_publicUniverse _ (by rw[searchQuery_length];decide)

theorem outputs_eager (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (privateTable : FullGame.FullTable) (publicTable : PairedReference.referenceInputs adversary → HashOutput) :
    outputs (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)=
      fun key => publicTable ⟨searchQuery key,query_mem adversary key⟩ := by
  funext key
  exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (query_mem adversary key) rfl

theorem reference_event_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (event : (SearchKey → HashOutput) → Prop) :
    Pr[fun s => event (outputs s.answers) | PairedReference.referenceExperiment adversary q] ≤
      Pr[event | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  unfold PairedReference.referenceExperiment
  rw[MonitoredPrivate.event_lift]
  unfold PairedReference.referenceComp
  refine probEvent_bind_le_of_forall_le fun privateTable _ => ?_
  refine (probEvent_bind_le_probEvent (p:=fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
    event (fun key => publicTable ⟨searchQuery key,query_mem adversary key⟩))
    fun publicTable _ hgood => ?_).trans ?_
  · rw[probEvent_map,probEvent_eq_zero_iff]
    intro result _ hbad
    exact hgood ((congrArg event (outputs_eager adversary privateTable publicTable)).mp hbad)
  · let e : SearchKey → PairedReference.referenceInputs adversary := fun key => ⟨searchQuery key,query_mem adversary key⟩
    have he : Function.Injective e := fun k k' h => searchQuery_injective (congrArg Subtype.val h)
    have hlaw := evalSPMF_uniformSample_map_comp_injective (R:=HashOutput) he
    have hp : Pr[fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
        event (fun key => publicTable (e key)) |
        ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _)] =
        Pr[event | (do let g ← ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _); pure (g ∘ e))] := by
      rw[bind_pure_comp,probEvent_map]
      rfl
    rw[hp,probEvent_congr' (fun _ _ => Iff.rfl) hlaw]

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey)
open ClaudeWCT.W9.T3.CanonicalSearch
open SigGolfCandidate.T3.Budgets (zeroAnswers ofReal_inv_two_pow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

theorem context_failure (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ¬ContextGood s.answers | PairedReference.referenceExperiment adversary q] ≤
      1/(2:ENNReal)^139 := by
  have hpoint (A : Correctness.Answers) :
      ¬ContextGood A ↔ ∃c,ContextFailed c (Presampling.tableAnswers (outputs A) zeroAnswers) := by
    rw [contextGood_agreement (outputs A) A zeroAnswers (fun _=>rfl)]
    simp only [ContextGood,not_forall,not_not]
  calc
    _ = Pr[fun s => ∃c,ContextFailed c (Presampling.tableAnswers (outputs s.answers) zeroAnswers) |
        PairedReference.referenceExperiment adversary q] := by simp_rw[hpoint]
    _ ≤ Pr[fun output => ∃c,ContextFailed c (Presampling.tableAnswers output zeroAnswers) |
        ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := reference_event_le adversary q _
    _ ≤ (2:ENNReal)^301*(1/(2:ENNReal)^440) := context_family_failure
    _ ≤ 1/(2:ENNReal)^139 := by
      have hr:(2:ℝ)^301*(1/(2:ℝ)^440)≤1/(2:ℝ)^139 := by
        set_option exponentiation.threshold 1024 in norm_num
      have h:=ENNReal.ofReal_le_ofReal hr
      rw[ENNReal.ofReal_mul (by positivity)] at h
      simpa only [ENNReal.ofReal_pow (show 0≤(2:ℝ) by norm_num),ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using h

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_injective)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

theorem eager_event_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (event : Answers → Prop) (bad : FullGame.FullTable → (SearchKey → HashOutput) → Prop) (bound : ENNReal)
    (hbad : ∀ privateTable publicTable state,
      event (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)) →
      bad privateTable (fun key=>publicTable ⟨searchQuery key,query_mem adversary key⟩))
    (hbound : ∀ privateTable,Pr[bad privateTable | ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤bound) :
    Pr[fun x=>event (Ref.cut x.1.state x.2) | PairedReference.eagerRecorded adversary]≤bound := by
  unfold PairedReference.eagerRecorded
  rw[MonitoredPrivate.event_lift]
  refine probEvent_bind_le_of_forall_le fun privateTable _ => ?_
  refine (probEvent_bind_le_probEvent (p:=fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
    bad privateTable (fun key=>publicTable ⟨searchQuery key,query_mem adversary key⟩))
    fun publicTable _ hgood => ?_).trans ?_
  · rw[probEvent_map,probEvent_eq_zero_iff]
    intro result _ he
    exact hgood (hbad privateTable publicTable result.state he)
  · let e : SearchKey → PairedReference.referenceInputs adversary := fun key=>⟨searchQuery key,query_mem adversary key⟩
    have he : Function.Injective e:=fun k k' h=>searchQuery_injective (congrArg Subtype.val h)
    have hlaw:=evalSPMF_uniformSample_map_comp_injective (R:=HashOutput) he
    have hp : Pr[fun publicTable : PairedReference.referenceInputs adversary → HashOutput =>
        bad privateTable (fun key=>publicTable (e key)) |
        ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _)] =
        Pr[bad privateTable | (do let g ← ($ᵗ (PairedReference.referenceInputs adversary → HashOutput) : ProbComp _);pure (g ∘ e))] := by
      rw[bind_pure_comp,probEvent_map];rfl
    rw[hp,probEvent_congr' (fun _ _ => Iff.rfl) hlaw]
    exact hbound privateTable

theorem completed_event_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq:q≤2^127) (event : Answers → Prop)
    (bad : FullGame.FullTable → (SearchKey → HashOutput) → Prop) (bound : ENNReal)
    (hbad : ∀ privateTable publicTable state,
      event (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)) →
      bad privateTable (fun key=>publicTable ⟨searchQuery key,query_mem adversary key⟩))
    (hbound : ∀ privateTable,Pr[bad privateTable | ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤bound) :
    Pr[fun z=>event z.2 | PairedSeccLaw.completedExperiment adversary q hq]≤bound := by
  rw[PairedReference.completed_eager_cut adversary q hq (fun _ A=>event A)]
  exact eager_event_le adversary event bad bound hbad hbound

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_length)
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

def privateNonces (table : FullGame.FullTable) (message : Message) : Digest :=
  (table (.inr (.inl message))).extractLsb' 0 128

theorem completed_signer_failure (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>¬SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138 := by
  refine completed_event_le adversary q hq (fun A=>¬SigningComplete A (evalWithAnswerFn A keygen).2)
    (fun privateTable output=>¬TableGoodForNonces (privateNonces privateTable) output) (1/(2:ENNReal)^138) ?_ ?_
  · intro privateTable publicTable state hbad hgood
    apply hbad
    apply tableGoodForNonces_signing _ _ (privateNonces privateTable) hgood
    · intro key
      change (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable))
        (.inl (.inr (searchQuery key))) = _
      rw[(Ref.cut_shortAgree state _).public _ (by rw[searchQuery_length];decide)]
      exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (query_mem adversary key) rfl
    · intro message
      rfl
  · intro privateTable
    exact tableGoodForNonces_failure _

end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery searchQuery_length)
open ClaudeWCT.W9.T3.CanonicalSearch
open SigGolfCandidate.T3.Budgets (zeroAnswers ofReal_inv_two_pow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

theorem completed_context_failure (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun z => ¬ContextGood z.2 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      1/(2:ENNReal)^139 := by
  refine completed_event_le adversary q hq (fun A => ¬ContextGood A)
    (fun _ outputs => ∃context,ContextFailed context (Presampling.tableAnswers outputs zeroAnswers))
    (1/(2:ENNReal)^139) ?_ ?_
  · intro privateTable publicTable state hbad
    have ha : Budgets.SearchAgreement
        (fun key => publicTable ⟨searchQuery key,query_mem adversary key⟩)
        (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable)) := by
      intro key
      change (Ref.cut state (eagerAnswers (PairedReference.referenceInputs adversary) privateTable publicTable))
        (.inl (.inr (searchQuery key))) = _
      rw [(Ref.cut_shortAgree state _).public _ (by rw [searchQuery_length];decide)]
      exact SphincsSecurity.Concrete.finiteHashAnswer_none ∅ _ publicTable _ (query_mem adversary key) rfl
    rw [contextGood_agreement _ _ zeroAnswers ha] at hbad
    simpa only [ContextGood,not_forall,not_not] using hbad
  · intro _
    refine context_family_failure.trans ?_
    have hr : (2:ℝ)^301*(1/(2:ℝ)^440) ≤ 1/(2:ℝ)^139 := by
      set_option exponentiation.threshold 1024 in norm_num
    have h := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul (by positivity)] at h
    simpa only [ENNReal.ofReal_pow (show 0≤(2:ℝ) by norm_num),ENNReal.ofReal_ofNat,
      ofReal_inv_two_pow] using h
end ClaudeWCT.W9.T3.Security.Wots.PairedSearchTable
