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
  · have hl : leaf < 4096 := by
      have : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)
      omega
    obtain ⟨found, hf⟩ := ClaudeWCT.W9.T3.Correctness.encodingSearchesSucceedBC_msg A h.2 lay
      ⟨tree, by omega⟩ ⟨leaf, hl⟩ msg
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
    Pr[fun z => ¬SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] ≤ 1 / (2 : ENNReal) ^ 698 := by
  refine (signerIncomplete_le_table adversary q hq).trans ?_
  refine (ClaudeWCT.W9.T3.Budgets.tableGood_failure_le _ _ ClaudeWCT.W9.T3.Budgets.digest_failure_power_1300
    ClaudeWCT.W9.T3.ProducerV5.producer_failure_power).trans ?_
  have hreal : (2 : ℝ) ^ 384 * (1 / 2 ^ 1300) + 2 ^ 301 * (1 / 2 ^ 1000) ≤ 1 / 2 ^ 698 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num), ENNReal.ofReal_ofNat,
    SigGolfCandidate.T3.Budgets.ofReal_inv_two_pow] using hcast
end ClaudeWCT.W9.T3.Security.BPB
