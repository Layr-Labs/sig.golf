import Mathlib.Analysis.Complex.ExponentialBounds
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.EvalDist.Bool
import Mathlib.Data.BitVec
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import SigGolfCandidate.Merge001
import SigGolfCandidate.Merge007
import SigGolfCandidate.Merge009
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge027

-- ==== merged from SphincsSecurity_Proof_Fts_CertificateGame ====
section

section





section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundaryHashAtLeast signDigestLoop
theorem boundaryHashAtLeast_lift_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, BoundaryHashAtLeast parameter (liftM (computation i)) (cost i)) :
    BoundaryHashAtLeast parameter (liftM (sequenceFin computation)) (∑ i, cost i) := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact boundaryHashAtLeast_zero _ _
  | succ n ih =>
      rw [sequenceFin, liftM_bind, Fin.sum_univ_succ]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (hcost 0)
      intro head
      rw [liftM_bind, ← Nat.add_zero (∑ i : Fin n, cost i.succ)]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _ _ (fun i => hcost i.succ))
      intro tail
      exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_ftsNode (traceParameter parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    BoundaryHashAtLeast traceParameter
      (liftM (ftsNode parameter index tree secret level nodeIdx : OracleComp HashSpec Digest))
      (2 ^ (level + 1) - 1) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact boundaryHashAtLeast_tweakableHash traceParameter parameter
        (.ftsLeaf index tree (ftsLeafOfNat nodeIdx)) (digestBytes (secret (ftsLeafOfNat nodeIdx)))
  | succ level ih =>
      rw [ftsNode_succ_eq, liftM_bind]
      have hpower : 0 < 2 ^ (level + 1) := by positivity
      have hcost : 2 ^ (level + 1 + 1) - 1 = (2 ^ (level + 1) - 1) + ((2 ^ (level + 1) - 1) + 1) := by
        rw [pow_succ]
        omega
      rw [hcost]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro left
      rw [liftM_bind]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro right
      exact boundaryHashAtLeast_tweakableHash _ _ _ _
theorem boundaryHashAtLeast_buildLevels (traceParameter : PublicParameter)
    (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ level nodeIdx left right,
      BoundaryHashAtLeast traceParameter (liftM (hashNode level nodeIdx left right)) 1)
    (height : Nat) (leaves : Nat → Digest) (levels : Nat) :
    BoundaryHashAtLeast traceParameter (liftM (buildLevels hashNode height leaves levels))
      (levelsHashCost height levels) := by
  induction levels with
  | zero => exact boundaryHashAtLeast_zero _ _
  | succ levels ih =>
      rw [buildLevels, liftM_bind, levelsHashCost]
      apply boundaryHashAtLeast_bind _ _ _ _ _ ih
      intro table
      rw [buildLevel, liftM_bind, liftM_bind]
      rw [bind_assoc]
      refine BoundaryHashAtLeast.mono (a := 2 ^ (height - (levels + 1)) + 0) ?_ (by omega)
      apply boundaryHashAtLeast_bind _ _ _ _ 0
      · have h := boundaryHashAtLeast_lift_sequenceFin traceParameter
          (fun nodeIdx : Fin (2 ^ (height - (levels + 1))) =>
            hashNode (levels + 1) nodeIdx.val (table levels (2 * nodeIdx.val)) (table levels (2 * nodeIdx.val + 1)))
          (fun _ => 1) (fun _ => hhash _ _ _ _)
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using h
      · intro _
        exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_buildFtsTree_levels (traceParameter parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) :
    BoundaryHashAtLeast traceParameter
      (liftM (buildFtsTree parameter index (fun leaf => pure (secret leaf)) :
        OracleComp HashSpec _)) (2 ^ (ftsTreeHeight + 1) - 1) := by
  have hcost : 2 ^ (ftsTreeHeight + 1) - 1 = 2 ^ ftsTreeHeight + (levelsHashCost ftsTreeHeight ftsTreeHeight + 0) := by
    rw [levelsHashCost_self, pow_succ]
    have := Nat.two_pow_pos ftsTreeHeight
    omega
  rw [hcost, buildFtsTree, liftM_bind]
  apply boundaryHashAtLeast_bind _ _ _ _ _
  · have h := boundaryHashAtLeast_lift_sequenceFin traceParameter
      (fun leafIdx : FtsLeaf => (do
        let value ← (pure (secret leafIdx) : OracleComp HashSpec Digest)
        let hashed ← ftsLeafHash parameter index porsTree leafIdx.val value
        return (value, hashed)))
      (fun _ => 1) (fun leafIdx => by
        rw [pure_bind, liftM_bind, ← Nat.add_zero 1]
        apply boundaryHashAtLeast_bind _ _ _ _ _ (boundaryHashAtLeast_tweakableHash _ _ _ _)
        intro _
        exact boundaryHashAtLeast_zero _ _)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using h
  · intro leaves
    rw [liftM_bind]
    apply boundaryHashAtLeast_bind _ _ _ _ _
      (boundaryHashAtLeast_buildLevels _ _ (fun _ _ _ _ => boundaryHashAtLeast_tweakableHash _ _ _ _) _ _ _)
    intro _
    exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_buildFtsTree (traceParameter parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) :
    BoundaryHashAtLeast traceParameter
      (liftM (buildFtsTree parameter index (fun leaf => pure (secret leaf)) :
        OracleComp HashSpec _)) ftsOpenHashCost := by
  rw [ftsOpenHashCost_def]
  exact boundaryHashAtLeast_buildFtsTree_levels traceParameter parameter index secret
theorem boundaryHashAtLeast_signAttempt (parameter : PublicParameter) (key : SecretKey)
    (message : Message) (randomness : Randomness) :
    BoundaryHashAtLeast parameter (liftM (signAttempt key message randomness : OracleComp HashSpec _)) 1 := by
  unfold signAttempt messageDigest
  rw [liftM_bind, liftM_bind, bind_assoc]
  apply boundaryHashAtLeast_bind _ _ _ 1 0 (boundaryHashAtLeast_hash _ _)
  intro output
  exact boundaryHashAtLeast_zero _ _
theorem boundaryHashAtLeast_signDigestLoop_bind {α : Type} (parameter : PublicParameter)
    (key : SecretKey) (message : Message) (cost attempts : Nat)
    (next : Option (Randomness × Index × (IndexGroup → FtsLeaf)) → OracleComp OracleWorld α)
    (hnext : ∀ selected, BoundaryHashAtLeast parameter (next (some selected)) cost) :
    BoundaryHashAtLeast parameter (signDigestLoop attempts key message >>= next) (min attempts cost) := by
  induction attempts with
  | zero => exact boundaryHashAtLeast_zero _ _
  | succ attempts ih =>
      rw [signDigestLoop, bind_assoc, ← Nat.zero_add (min (attempts + 1) cost)]
      apply boundaryHashAtLeast_bind _ _ _ 0 _ (boundaryHashAtLeast_zero _ _)
      intro randomness
      rw [bind_assoc]
      apply BoundaryHashAtLeast.mono (a := 1 + min attempts cost) ?_ (by omega)
      apply boundaryHashAtLeast_bind _ _ _ 1 _ (boundaryHashAtLeast_signAttempt _ _ _ _)
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected =>
          simp only [pure_bind]
          exact BoundaryHashAtLeast.mono (hnext _) (min_le_right _ _)
theorem boundaryHashAtLeast_sign (parameter : PublicParameter) (key : SecretKey) (message : Message) :
    BoundaryHashAtLeast parameter (sign key message) ftsOpenHashCost := by
  rw [sign_eq]
  apply BoundaryHashAtLeast.mono (a := min digestAttemptLimit ftsOpenHashCost) ?_
    (le_min ftsOpenHashCost_le_digestAttemptLimit le_rfl)
  apply boundaryHashAtLeast_signDigestLoop_bind
  rintro ⟨randomness, index, leaves⟩
  show BoundaryHashAtLeast parameter (liftM (signAfterDigest key randomness index leaves :
      OracleComp HashSpec (Option Signature))) ftsOpenHashCost
  rw [signAfterDigest, signFrom, liftM_bind, ← Nat.add_zero ftsOpenHashCost]
  apply boundaryHashAtLeast_bind _ _ _ _ _ (boundaryHashAtLeast_buildFtsTree _ _ _ _)
  intro _
  exact boundaryHashAtLeast_zero _ _
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem probCompLift_support {α : Type} (computation : ProbComp α) :
    (liftM computation : PMF α).support = support computation := by
  ext value
  rw [PMF.mem_support_iff, ← PMF.probOutput_eq_apply, mem_support_iff]
  rfl
theorem originalProposalRecord_boundary (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    (originalProposalRecord key input cache).map (fun record => ((record.output, record.trace), record.cache)) =
      (liftM (boundaryRun key.parameter (expandedAdversaryImpl key input) cache) : PMF _) := by
  cases input with
  | inl world =>
      simp only [originalProposalRecord, PMF.map_comp, expandedAdversaryImpl]
      rw [boundaryRun_query]
      exact (liftM_map (m := ProbComp) (n := PMF) _ _).symm
  | inr message =>
      rw [originalProposalRecord, PMF.map_comp]
      calc
        _ = ((completedSigningRecord (signingBoundaryTrace key.parameter) key message cache).map Prod.fst).map
            signingRecordResponse := (PMF.map_comp _ _ _).symm
        _ = _ := by
          rw [completedSigningRecord_forget, ← PMF.monad_map_eq_map,
            ← liftM_map (m := ProbComp) (n := PMF), tracedSigningRun_signature]
          rfl
theorem originalProposalRecord_boundary_support (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    ((record.output, record.trace), record.cache) ∈
      support (boundaryRun key.parameter (expandedAdversaryImpl key input) cache) := by
  have hm := (PMF.mem_support_map_iff
    (fun record : ProposalExecutionRecord input => ((record.output, record.trace), record.cache))
    (originalProposalRecord key input cache) _).mpr ⟨record, hr, rfl⟩
  rwa [originalProposalRecord_boundary, probCompLift_support] at hm
theorem originalProposalRecord_query_bound {α : Type} (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (cache : QueryCache HashSpec)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) (OracleSpec.query input >>= next)) cache q) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input cache).support) :
    record.trace.hashCalls ≤ q ∧
      HashQueryBound (simulateQ (expandedAdversaryImpl key) (next record.output)) record.cache
        (q - record.trace.hashCalls) := by
  rw [simulateQ_bind, simulateQ_spec_query] at hbound
  exact boundaryRun_bind_query_bound key.parameter (expandedAdversaryImpl key input)
    (fun output => simulateQ (expandedAdversaryImpl key) (next output)) q cache hbound _
    (originalProposalRecord_boundary_support key input cache record hr)
theorem originalProposalRecord_sign_hashCalls (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord (.inr message))
    (hr : record ∈ (originalProposalRecord key (.inr message) cache).support) :
    ftsOpenHashCost ≤ record.trace.hashCalls :=
  boundaryHashAtLeast_sign key.parameter key message cache _
    (originalProposalRecord_boundary_support key (.inr message) cache record hr)
theorem targetCreationMultiplier_le_record_hashCalls (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    targetCreationMultiplier key cache input ≤ record.trace.hashCalls := by
  cases input with
  | inl world =>
      rw [originalProposalRecord_world_hashCalls key world cache record hr, targetCreationMultiplier]
      cases world with
      | inl sample => exact le_refl _
      | inr input =>
          simp only [freshWorldTargetHashCost, signingExecutionHashCost]
          split_ifs <;> norm_num
  | inr message =>
      have hmass := mul_le_mul' admissibleProbability_inv_le
        (freshDigestSelectionProbability_le_one key message cache)
      calc
        _ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by
          refine (by simpa only [targetCreationMultiplier, mul_one] using hmass : _ ≤ (2142 : ENNReal)).trans ?_
          exact_mod_cast (show 2142 ≤ 2 ^ ftsTreeHeight by decide)
        _ ≤ (ftsOpenHashCost : ENNReal) := Nat.cast_le.mpr two_pow_ftsTreeHeight_le_ftsOpenHashCost
        _ ≤ record.trace.hashCalls := Nat.cast_le.mpr (originalProposalRecord_sign_hashCalls key message cache record hr)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem certificateLengthImpl_support (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (result : (OracleWorld + SigningSpec).Range input × CertificateMonitorState)
    (hr : result ∈ ((certificateLengthImpl key budget required stopAfter input).run state).support) :
    ∃ length record, record ∈ (originalProposalRecord key input state.1).support ∧
      result = (record.output, originalProposalAdvance
        (certificateMonitorUpdate key budget required stopAfter) input state length record) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk] at hr
  split at hr
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨source, hsource, rfl⟩ := hr
    have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
    rw [recordLengthBridge_record] at hrecord
    exact ⟨source.1, source.2, hrecord, rfl⟩
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    exact ⟨0, record, hrecord, rfl⟩
theorem certificateMonitorUpdate_le_hashCalls (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input state.1).support) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).spent ≤
        state.2.spent + record.trace.hashCalls ∧
      (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass ≤
        state.2.creationMass + record.trace.hashCalls := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simp only [certificateMonitorUpdate, if_pos hactive]
    exact ⟨le_rfl, add_le_add le_rfl (targetCreationMultiplier_le_record_hashCalls key input state.1 record hr)⟩
  · simp only [certificateMonitorUpdate, if_neg hactive]
    exact ⟨Nat.le_add_right _ _, le_self_add⟩
theorem certificateLength_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : CertificateMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) computation) state.1 q) (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.spent ≤ state.2.spent + q ∧ result.2.2.creationMass ≤ state.2.creationMass + q := by
  induction computation using OracleComp.inductionOn generalizing q state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨Nat.le_add_right _ _, le_self_add⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateLengthImpl_support key budget required stopAfter input state middle hmiddle
      have hquery := originalProposalRecord_query_bound key input next q state.1 hbound record hrecord
      have hstep := certificateMonitorUpdate_le_hashCalls key budget required stopAfter input state length record hrecord
      have htail := ih record.output _ _ hquery.2 result hr
      simp only [originalProposalAdvance] at htail
      constructor
      · omega
      · calc
          _ ≤ (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass +
              (q - record.trace.hashCalls : Nat) := htail.2
          _ ≤ (state.2.creationMass + record.trace.hashCalls) + (q - record.trace.hashCalls : Nat) :=
            add_le_add hstep.2 le_rfl
          _ = state.2.creationMass + q := by
            rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hquery.1]
theorem certificateProposal_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : List Index × CertificateMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) computation) state.2.1 q) (result : α × (List Index × CertificateMonitorState))
    (hr : result ∈ ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.2.spent ≤ state.2.2.spent + q ∧
      result.2.2.2.creationMass ≤ state.2.2.creationMass + q := by
  have hprojection := simulateQ_certificateProposalImpl_length key budget required stopAfter computation state
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, hprojection] at hm
  exact certificateLength_run_cost_le key budget required stopAfter computation q state.2 hbound _ hm
end SphincsSecurity.Concrete
end
end

section








section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem expected_certificateLengthImpl_potential_le (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      certificateMonitorPotential key budget required result.2) ≤
      certificateMonitorPotential key budget required state + certificateMonitorCharge key budget required input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · have hdata := hactive
    obtain ⟨hlive, ⟨hsigned, hcache, _⟩, hvalid, hcost⟩ := hdata
    rw [certificateMonitorCharge, if_pos hactive]
    cases input with
    | inl world =>
        rw [certificateLengthImpl_world_run, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inl world) state 0 _ hactive,
          signingLogFragment, List.append_nil]
        have hcost' : signingExecutionHashCost (.inl world) ≤ budget - state.2.spent := by
          cases world <;> exact hcost
        have h := expected_originalProposalRecord_world_banked_le key nearUniformDigestReuseWeight
          (budget - state.2.spent) (signatureLimit - state.2.log.length) required
          (certificateMonitorCoverState state) state.2.bank world
          (fun record => (certificateMonitorUpdate key budget required stopAfter (.inl world) state 0 record).stopped)
          hsigned hcost'
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive] using h
    | inr message =>
        rw [certificateLengthImpl_sign_run, if_pos hactive, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inr message) state _ _ hactive,
          signingLogFragment, List.length_append, List.length_singleton]
        have hremaining : signatureLimit - (state.2.log.length + 1) + 1 = signatureLimit - state.2.log.length := by
          change state.2.log.length < signatureLimit at hvalid
          omega
        have hreuse := exactDigestReuseWeight_le_near_uniform_of_clean_cache key state.1 state.2.spent
          hcache.spent_le hcache.cache_le hcache.no_deficit message
        have h := expected_lengthBridge_sign_banked_le key nearUniformDigestReuseWeight
          (budget - state.2.spent) (signatureLimit - (state.2.log.length + 1)) required
          (certificateMonitorCoverState state) state.2.bank message
          (fun result => (certificateMonitorUpdate key budget required stopAfter (.inr message) state result.1 result.2).stopped)
          hsigned hreuse
        rw [hremaining] at h
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive] using h
  · rw [certificateMonitorCharge, if_neg hactive, add_zero, certificateLengthImpl_inactive_run key budget required stopAfter input state hactive,
      ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [certificateMonitorPotential, bankedTargetEnvelope_stopped]
    rw [ENNReal.tsum_mul_right]
    have hmass : (∑' record, Pr[= record | originalProposalRecord key input state.1]) = 1 := by
      simp only [PMF.probOutput_eq_apply, PMF.tsum_coe]
    rw [hmass, one_mul]
    exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _
theorem expected_certificateLengthImpl_of_advance_constant (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (counter : CertificateMonitorState → ENNReal) (value : ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) = value) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) = value := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split <;> rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] <;>
    simp only [hadvance, ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
theorem expected_certificateLengthImpl_creationCost (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * result.2.2.creationCost) =
      state.2.creationCost + certificateMonitorCharge key budget required input state :=
  expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
    (fun current => current.2.creationCost) _ (certificateMonitorUpdate_creationCost key budget required stopAfter input state)
theorem expected_certificateLengthImpl_creationMass (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * result.2.2.creationMass) =
      state.2.creationMass + certificateMonitorMass key budget input state :=
  expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
    (fun current => current.2.creationMass) _ (certificateMonitorUpdate_creationMass key budget required stopAfter input state)
noncomputable def expectedCertificateCharge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CertificateMonitorState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => charge input state +
      ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
        next result.1 result.2) computation
@[simp] theorem expectedCertificateCharge_pure {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (value : α) (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter charge (pure value) state = 0 := rfl
theorem expectedCertificateCharge_query_bind {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter charge (OracleSpec.query input >>= next) state =
      charge input state +
        ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
          expectedCertificateCharge key budget required stopAfter charge (next result.1) result.2 := rfl
theorem expected_certificate_accumulator {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (counter : CertificateMonitorState → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hstep : ∀ input state,
      (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) =
        counter state + charge input state)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * counter result.2) =
      counter state + expectedCertificateCharge key budget required stopAfter charge computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
      expectedCertificateCharge_pure, add_zero]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCertificateCharge_query_bind]
      simp_rw [ih, mul_add, ENNReal.tsum_add]
      rw [hstep, add_assoc]
theorem expected_certificate_creationCost {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * result.2.2.creationCost) =
      state.2.creationCost +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.creationCost)
    (certificateMonitorCharge key budget required) (expected_certificateLengthImpl_creationCost key budget required stopAfter)
    computation state
theorem expected_certificate_creationMass {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * result.2.2.creationMass) =
      state.2.creationMass + expectedCertificateCharge key budget required stopAfter (certificateMonitorMass key budget) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.creationMass)
    (certificateMonitorMass key budget) (expected_certificateLengthImpl_creationMass key budget required stopAfter)
    computation state
theorem expected_certificate_potential_le_initial_add_charge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      certificateMonitorPotential key budget required result.2) ≤
      certificateMonitorPotential key budget required state +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
      expectedCertificateCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCertificateCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
            (certificateMonitorPotential key budget required result.2 +
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2) :=
          ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)
        _ = (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
            certificateMonitorPotential key budget required result.2) +
            ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2 := by simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (certificateMonitorPotential key budget required state + certificateMonitorCharge key budget required input state) +
            ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2 :=
          add_le_add (expected_certificateLengthImpl_potential_le key budget required stopAfter input state) le_rfl
        _ = _ := by rw [add_assoc]
theorem expected_certificate_count_le_initial_add_charge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      certificateBankCount result.2.2.bank) ≤
      certificateMonitorPotential key budget required state +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state := by
  apply le_trans ?_ (expected_certificate_potential_le_initial_add_charge key budget required stopAfter computation state)
  exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)
theorem expected_certificate_count_le_creationCost {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.bank) ≤
      ∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.creationCost := by
  rw [expected_certificate_creationCost]
  have h := expected_certificate_count_le_initial_add_charge key budget required stopAfter computation
    (cache, initialCertificateMonitor spent stopped)
  rw [certificateMonitorPotential_initial key budget spent required cache stopped hnone, zero_add] at h
  simpa only [initialCertificateMonitor, zero_add] using h
theorem expected_certificateProposal_count_le_creationCost {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.2.bank) ≤
      ∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.creationCost := by
  have hmap := simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    ([], cache, initialCertificateMonitor spent stopped)
  have hcount := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank) hmap
  have hcost := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * result.2.2.creationCost) hmap
  rw [tsum_probOutput_map_mul] at hcount hcost
  simp only [Prod.map] at hcount hcost
  rw [hcount, hcost]
  exact expected_certificate_count_le_creationCost key budget spent required stopAfter computation cache stopped hnone
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop
theorem probEvent_signDigestAttemptPrefix_fresh_le_admissibility
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] ≤
      admissibleProbability := by
  rw [signDigestAttemptPrefix]
  apply probEvent_bind_le_of_forall_le
  intro randomness _
  rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
    probEvent_bind_pure_comp]
  change Pr[fun result => reference (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
      (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache] ≤ _
  by_cases href : reference (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = none
  · simp only [href, true_and]
    cases hc : cache (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) with
    | none => exact (probEvent_signAttempt_fresh_success_eq key message randomness cache hc).le
    | some output =>
        apply le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
        intro result hr hsuccess
        have hle : cache ≤ result.2 :=
          simulateQ_romImpl_cache_le (liftM (signAttempt key message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) cache result (by
              rw [simulateQ_romImpl_liftM]
              exact hr)
        exact hsuccess ((signAttempt_result_of_cached key message randomness cache result.2 result.1 output
          (hle hc) hr).trans (hinvariant randomness output href hc))
  · apply le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
    intro result _ hevent
    exact href hevent.1
theorem probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
      (simulateQ romImpl (signDigestLoop attempts key message)).run cache] ≤
      digestAttemptExpectation attempts key message cache * admissibleProbability := by
  induction attempts generalizing cache with
  | zero => simp [signDigestLoop, freshSelectedLoopView?, digestAttemptExpectation]
  | succ attempts ih =>
      rw [probEvent_signDigestLoop_fresh_recurrence, digestAttemptExpectation, add_mul, one_mul,
        ← ENNReal.tsum_mul_right]
      apply add_le_add (probEvent_signDigestAttemptPrefix_fresh_le_admissibility key message reference cache hinvariant)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
      · by_cases hnone : result.2.1 = none
        · rw [if_pos hnone, if_pos hnone, mul_assoc]
          apply mul_le_mul' le_rfl
          apply ih
          apply onlyRejectedNewMessageEntries_of_failed_attempt reference cache result.2.2 key message result.1 hinvariant
          have heq : result.2 = (none, result.2.2) := Prod.ext hnone rfl
          rw [← heq]
          exact signDigestAttemptPrefix_support_attempt key message cache result hr
        · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
      · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, le_refl]
end SphincsSecurity.Concrete
end
section
set_option autoImplicit true
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
theorem expectedQueryCharge_lift_unif_eq_zero
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp unifSpec α) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (liftM computation : OracleComp OracleWorld α) cache = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rw [liftM_bind]
      change expectedQueryCharge charge
        ((liftM (OracleWorld.query (.inl query)) : OracleComp OracleWorld _) >>= fun answer => liftM (next answer)) cache = 0
      rw [expectedQueryCharge_query_bind]
      simp only [hashQueryCharge, Sum.elim_inl, ih, mul_zero, tsum_zero, zero_add]
end SphincsSecurity
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_7 : SampleableType Randomness := Concrete.randomnessSampleableType
attribute [local irreducible] signDigestLoop signAttempt signWithView
set_option backward.isDefEq.respectTransparency false
theorem expectedQueryCharge_messageDigest_message (key : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter)
      (liftM (messageDigest key.parameter key.root message randomness : OracleComp HashSpec MessageDigest)) cache = 1 := by
  change expectedQueryCharge (messageHashCharge key.parameter)
    ((liftM (OracleWorld.query (.inr (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)))) : OracleComp OracleWorld HashOutput) >>=
      fun answer => pure (truncateMessageDigest answer)) cache = 1
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr,
    messageHashCharge, if_pos (show FtsProbeSimulation.MessageHashInput key.parameter
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) from ⟨_, rfl⟩)]
theorem expectedQueryCharge_signAttempt_message (key : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter)
      (liftM (signAttempt key message randomness : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) cache = 1 := by
  rw [signAttempt, liftM_bind, expectedQueryCharge_bind, expectedQueryCharge_messageDigest_message]
  conv_lhs =>
    arg 2
    tactic =>
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      split_ifs <;> simp
  exact add_zero 1
theorem expectedQueryCharge_signDigestLoop_message (attempts : Nat) (key : SecretKey)
    (message : Message) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter) (signDigestLoop attempts key message) cache =
      digestAttemptExpectation attempts key message cache := by
  induction attempts generalizing cache with
  | zero => simp only [signDigestLoop, expectedQueryCharge_pure, digestAttemptExpectation]
  | succ attempts ih =>
      have hsample : (simulateQ romImpl (liftM sampleRandomness)).run cache =
          (fun randomness => (randomness, cache)) <$> sampleRandomness :=
        roSim.run_liftM (hashSpec := HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) sampleRandomness cache
      rw [signDigestLoop, expectedQueryCharge_bind, expectedQueryCharge_lift_unif_eq_zero, zero_add,
        hsample, sampleRandomness_eq, tsum_probOutput_map_mul, digestAttemptExpectation,
        signDigestAttemptPrefix, tsum_probOutput_bind_mul]
      simp_rw [expectedQueryCharge_bind, expectedQueryCharge_signAttempt_message,
        mul_add, ENNReal.tsum_add, mul_one, tsum_probOutput_of_liftM_PMF]
      congr 1
      apply tsum_congr
      intro randomness
      rw [simulateQ_romImpl_liftM]
      congr 1
      rw [tsum_probOutput_bind_mul]
      apply tsum_congr
      intro result
      simp only [tsum_probOutput_pure_mul]
      cases result.1 <;> simp [ih]
theorem freshDigestSelection_mass_le_messageCharge (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    admissibleProbability⁻¹ * freshDigestSelectionProbability key message cache ≤
      expectedQueryCharge (messageHashCharge key.parameter) (signWithView key message) cache := by
  have h := probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility digestAttemptLimit key message cache cache
    (onlyRejectedNewMessageEntries_self cache key message)
  have hscaled := mul_le_mul' (le_refl admissibleProbability⁻¹) h
  have hscalar : admissibleProbability⁻¹ *
      (digestAttemptExpectation digestAttemptLimit key message cache * admissibleProbability) =
      digestAttemptExpectation digestAttemptLimit key message cache := by
    rw [mul_left_comm, ENNReal.inv_mul_cancel admissibleProbability_pos admissibleProbability_ne_top, mul_one]
  rw [hscalar] at hscaled
  apply hscaled.trans
  rw [signWithView, expectedQueryCharge_bind, expectedQueryCharge_signDigestLoop_message]
  exact le_self_add
private theorem expected_pmfLift {α : Type} (computation : ProbComp α) (weight : α → ENNReal) :
    (∑' result, Pr[= result | (liftM computation : PMF α)] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl
theorem expected_originalProposalRecord_sign_messageCalls (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (∑' record, Pr[= record | originalProposalRecord key (.inr message) cache] *
      record.trace.messageCalls.length) =
      expectedQueryCharge (messageHashCharge key.parameter) (signWithView key message) cache := by
  rw [originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  have h := congrArg (fun law : PMF (TracedSigningRecord SigningBoundaryTrace) =>
    ∑' result, Pr[= result | law] * (result.1.2.messageCalls.length : ENNReal))
    (completedSigningRecord_forget (signingBoundaryTrace key.parameter) key message cache)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, expected_pmfLift] at h
  change _ = expectedBoundaryMessageCalls key.parameter (signWithView key message) cache at h
  exact h.trans (expectedBoundaryMessageCalls_eq_queryCharge key.parameter (signWithView key message) cache)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem expected_originalProposalRecord_world_messageCalls (key : SecretKey)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' record, Pr[= record | originalProposalRecord key (.inl input) cache] *
      record.trace.messageCalls.length) = hashQueryCharge (messageHashCharge key.parameter) cache input := by
  rw [originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  simp only [signingBoundaryTrace_messageCalls key.parameter input _ cache,
    ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
theorem targetCreationMultiplier_le_expected_messageCalls (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    targetCreationMultiplier key cache input ≤
      ∑' record, Pr[= record | originalProposalRecord key input cache] * record.trace.messageCalls.length := by
  cases input with
  | inl world =>
      rw [expected_originalProposalRecord_world_messageCalls, targetCreationMultiplier]
      cases world with
      | inl sample => simp only [freshWorldTargetHashCost, Nat.cast_zero, hashQueryCharge, Sum.elim_inl, le_refl]
      | inr input =>
          by_cases hmessage : FtsProbeSimulation.MessageHashInput key.parameter input <;>
            simp [freshWorldTargetHashCost, hashQueryCharge, messageHashCharge, hmessage]
          split_ifs <;> norm_num
  | inr message =>
      rw [expected_originalProposalRecord_sign_messageCalls]
      simpa only [targetCreationMultiplier, FtsLeaf, Fintype.card_fin] using
        freshDigestSelection_mass_le_messageCharge key message cache
noncomputable def certificateMonitorMessageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then
    ∑' record, Pr[= record | originalProposalRecord key input state.1] * record.trace.messageCalls.length
  else 0
theorem certificateMonitorMass_le_messageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    certificateMonitorMass key budget input state ≤ certificateMonitorMessageCharge key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simpa only [certificateMonitorMass, certificateMonitorMessageCharge, if_pos hactive] using
      targetCreationMultiplier_le_expected_messageCalls key input state.1
  · simp only [certificateMonitorMass, certificateMonitorMessageCharge, if_neg hactive, le_refl]
theorem expected_certificateLengthImpl_of_record_function (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (counter : CertificateMonitorState → ENNReal) (weight : ProposalExecutionRecord input → ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) = weight record) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) =
      ∑' record, Pr[= record | originalProposalRecord key input state.1] * weight record := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]
    have h := congrArg (fun law : PMF (ProposalExecutionRecord input) =>
      ∑' record, Pr[= record | law] * weight record)
      (recordLengthBridge_record (originalProposalRecord key input state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
    rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
    exact h
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]
theorem expected_certificateLengthImpl_messageCalls (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      result.2.2.messageCalls) = state.2.messageCalls + certificateMonitorMessageCharge key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · rw [expected_certificateLengthImpl_of_record_function key budget required stopAfter input state
        (fun current => current.2.messageCalls)
        (fun record => (state.2.messageCalls : ENNReal) + record.trace.messageCalls.length)
        (fun length record => by simp only [originalProposalAdvance,
          certificateMonitorUpdate_messageCalls key budget required stopAfter input state length record hactive, Nat.cast_add])]
    simp only [certificateMonitorMessageCharge, if_pos hactive, mul_add, ENNReal.tsum_add,
      ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
  · rw [expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
        (fun current => current.2.messageCalls) state.2.messageCalls
        (fun length record => by simp only [originalProposalAdvance,
          certificateMonitorUpdate_inactive key budget required stopAfter input state length record hactive])]
    simp only [certificateMonitorMessageCharge, if_neg hactive, add_zero]
theorem expected_certificate_messageCalls {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      result.2.2.messageCalls) = state.2.messageCalls +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorMessageCharge key budget) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.messageCalls)
    (certificateMonitorMessageCharge key budget) (expected_certificateLengthImpl_messageCalls key budget required stopAfter)
    computation state
theorem expectedCertificateCharge_mono {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (first second : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hle : ∀ input state, first input state ≤ second input state)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter first computation state ≤
      expectedCertificateCharge key budget required stopAfter second computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedCertificateCharge_pure, le_refl]
  | query_bind input next ih =>
      rw [expectedCertificateCharge_query_bind, expectedCertificateCharge_query_bind]
      exact add_le_add (hle input state) (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2))
theorem expected_certificate_creationMass_le_messageCalls {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.creationMass) ≤
      ∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.messageCalls := by
  rw [expected_certificate_creationMass, expected_certificate_messageCalls]
  simp only [initialCertificateMonitor, Nat.cast_zero, zero_add]
  exact expectedCertificateCharge_mono key budget required stopAfter _ _
    (certificateMonitorMass_le_messageCharge key budget) computation _
theorem expected_certificateProposal_creationMass_le_messageCalls {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.creationMass) ≤
      ∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.messageCalls := by
  have hmap := simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    ([], cache, initialCertificateMonitor spent stopped)
  have hmass := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * result.2.2.creationMass) hmap
  have hcalls := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * (result.2.2.messageCalls : ENNReal)) hmap
  rw [tsum_probOutput_map_mul] at hmass hcalls
  simp only [Prod.map] at hmass hcalls
  rw [hmass, hcalls]
  exact expected_certificate_creationMass_le_messageCalls key budget spent required stopAfter computation cache stopped
end SphincsSecurity.Concrete
end
section
set_option autoImplicit true
namespace SphincsSecurity.Concrete.OtsProbeSimulation
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
theorem simulateQ_unloggedMapped_eq_expanded (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (unloggedMappedAdversaryImpl secretKey) computation =
      simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation) := by
  have hhandler : unloggedMappedAdversaryImpl secretKey = romImpl ∘ₛ expandedAdversaryImpl secretKey := by
    funext input
    exact unloggedMappedAdversaryImpl_eq_simulateQ_expanded secretKey input
  rw [hhandler, QueryImpl.simulateQ_compose]
end SphincsSecurity.Concrete.OtsProbeSimulation
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
private theorem simulateQ_romImpl_sampling_bind_run {α β : Type} (computation : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld α) >>= next)).run cache =
      computation >>= fun value => (simulateQ romImpl (next value)).run cache := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ (unifFwdImpl HashSpec) computation from QueryImpl.simulateQ_add_liftM_left _ _ computation,
    unifFwdImpl.simulateQ_run, bind_map_left]
theorem keygen_cache_message_none (generated : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hg : generated ∈ support ((simulateQ romImpl scheme.keygen).run ∅)) :
    ∀ input, FtsProbeSimulation.MessageHashInput generated.1.2.parameter input → generated.2 input = none := by
  change generated ∈ support ((simulateQ romImpl keygen).run ∅) at hg
  rw [keygen, simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨parameter, _, hg⟩ := hg
  rw [simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨otsSecret, _, hg⟩ := hg
  rw [simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨ftsSecret, _, hg⟩ := hg
  rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM, mem_support_bind_iff] at hg
  obtain ⟨root, hroot, hg⟩ := hg
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hg
  subst generated
  rintro input ⟨payload, rfl⟩
  exact keygenTable_cache_message_none parameter (otsSecret topLayer rootTree)
    root.1 root.2 hroot payload
abbrev CertificateGameResult := RetainedRestResult × (List Index × CertificateMonitorState)
noncomputable def certificateGame (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) : PMF CertificateGameResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  (simulateQ (certificateProposalImpl key budget required (stopAfter key))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped)
theorem certificateGame_cost_le (adversary : Adversary) (q : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (hbound : HasHashQueryBound scheme adversary q) (result : CertificateGameResult)
    (hr : result ∈ (certificateGame adversary q required stopAfter stopped).support) :
    result.2.2.2.spent ≤ q ∧ result.2.2.2.creationMass ≤ q := by
  rw [certificateGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hgenerated, hr⟩ := hr
  rw [probCompLift_support] at hgenerated
  have hwhole : HashQueryBound (scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2)
      ∅ q := (hasHashQueryBound_iff scheme adversary q).mp hbound
  have hkeygen := boundaryRun_bind_query_bound 0 scheme.keygen
    (fun keys => gameRest scheme adversary keys.1 keys.2) q ∅ hwhole generated hgenerated
  have hrest := hkeygen.2
  rw [OtsProbeSimulation.gameRest_eq_map_retained, hashQueryBound_map_iff] at hrest
  have hcost := certificateProposal_run_cost_le generated.1.1.2 q required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1) (q - generated.1.2.hashCalls)
    ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped) hrest result hr
  simp only [initialCertificateMonitor, zero_add] at hcost
  exact ⟨by omega, hcost.2.trans (Nat.cast_le.mpr (Nat.sub_le _ _))⟩
theorem expected_certificateGame_creationMass_le_messageCalls (adversary : Adversary)
    (budget : Nat) (required : Finset IndexGroup) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.creationMass) ≤
      ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.messageCalls := by
  rw [certificateGame, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  exact mul_le_mul' le_rfl (expected_certificateProposal_creationMass_le_messageCalls generated.1.1.2 budget
    generated.1.2.hashCalls required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1) generated.2 stopped)
theorem expected_certificateGame_count_le_creationCost (adversary : Adversary)
    (budget : Nat) (required : Finset IndexGroup) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] *
        certificateBankCount result.2.2.2.bank) ≤
      ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.creationCost := by
  rw [certificateGame, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  by_cases hg : generated ∈ (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _).support
  · have hgenerated := hg
    rw [probCompLift_support] at hgenerated
    have hkeygen : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
      rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
      exact ⟨generated, hgenerated, rfl⟩
    have hnone := keygen_cache_message_none (generated.1.1, generated.2) hkeygen
    exact mul_le_mul' le_rfl (expected_certificateProposal_count_le_creationCost generated.1.1.2 budget
      generated.1.2.hashCalls required (stopAfter generated.1.1.2)
      (retainedGameRestComputation adversary generated.1.1.1) generated.2 stopped
      hnone)
  · have hzero : Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] = 0 := by
      rw [PMF.probOutput_eq_apply]
      exact (PMF.apply_eq_zero_iff _ _).mpr hg
    rw [hzero, zero_mul, zero_mul]
end SphincsSecurity.Concrete
end
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_ProposalPrefixExponential ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem originalProposalImpl_complete {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (QueryCache HashSpec × μ)) :
    ((originalProposalImpl key spent enabled update input).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  simp only [originalProposalImpl, proposalRecordImpl, StateT.run_mk]
  by_cases hactive : originalProposalActive key spent enabled input state.2 = true
  · rw [if_pos hactive, PMF.bind_map]
    cases input with
    | inl world => simp only [originalProposalActive, Bool.false_eq_true] at hactive
    | inr message =>
        have hcache : ProposalCacheBound key state.2.1 (spent state.2) := by
          by_contra hcache
          simp [originalProposalActive, hcache] at hactive
        rw [originalRejectedProposal, dif_pos hcache]
        simpa only [cappedRecordProposalBridge, List.append_assoc, Function.comp_def] using
          complete_cappedRecordProposalBridge_prefix (PMF.uniformOfFintype Index)
            (originalProposalRecord key (.inr message) state.2.1) (fun record => record.index)
            targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one
            (originalProposalRecord_cap key message state.2.1 (spent state.2) hcache) total state.1
  · rw [if_neg hactive, PMF.bind_map]
    simp only [Function.comp_def]
    exact PMF.bind_const _ _
theorem simulateQ_originalProposalImpl_complete {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    ((simulateQ (originalProposalImpl key spent enabled update) computation).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_bind]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
      simp_rw [ih]
      exact originalProposalImpl_complete key spent enabled update total input state
noncomputable def terminalProposalPotential {α : Type} (base : PMF α) (total : Nat)
    (payoff : List α → ENNReal) (consumed : List α) : ENNReal :=
  ∑' word, Pr[= word | completeProposalWord base total consumed] * payoff word
theorem expected_originalProposalImpl_terminalPotential {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (QueryCache HashSpec × μ)) :
    (∑' result, Pr[= result | (originalProposalImpl key spent enabled update input).run state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : PMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (originalProposalImpl_complete key spent enabled update total input state)
  rw [← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul] at h
  exact h
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem simulateQ_certificateProposalImpl_complete {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (total : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState) :
    ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 :=
  simulateQ_originalProposalImpl_complete key (fun current : CertificateMonitorState => current.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter) total computation state
theorem expected_certificateProposalImpl_terminalPotential (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateProposalImpl key budget required stopAfter input).run state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 :=
  expected_originalProposalImpl_terminalPotential key (fun current : CertificateMonitorState => current.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter) total payoff input state
theorem certificateGame_complete (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateGame adversary budget required stopAfter stopped).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      independentProposalWord (PMF.uniformOfFintype Index) total := by
  rw [certificateGame, PMF.monad_bind_eq_bind, PMF.bind_bind]
  simp_rw [simulateQ_certificateProposalImpl_complete, completeProposalWord_nil]
  exact PMF.bind_const _ _
noncomputable def certificateTerminalGame (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    PMF (CertificateGameResult × List Index) :=
  (certificateGame adversary budget required stopAfter stopped).bind fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map (fun word => (result, word))
theorem certificateTerminalGame_game (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateTerminalGame adversary budget required stopAfter stopped total).map Prod.fst =
      certificateGame adversary budget required stopAfter stopped := by
  rw [certificateTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (certificateGame adversary budget required stopAfter stopped).bind (fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map (Function.const _ result)) = _
  simp only [PMF.map_const, PMF.bind_pure]
theorem certificateTerminalGame_word (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateTerminalGame adversary budget required stopAfter stopped total).map Prod.snd =
      independentProposalWord (PMF.uniformOfFintype Index) total := by
  rw [certificateTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (certificateGame adversary budget required stopAfter stopped).bind (fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map id) = _
  simp only [PMF.map_id]
  exact certificateGame_complete adversary budget required stopAfter stopped total
theorem certificateTerminalGame_cost_le (adversary : Adversary) (q : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : CertificateGameResult × List Index)
    (hr : result ∈ (certificateTerminalGame adversary q required stopAfter stopped total).support) :
    result.1.2.2.2.spent ≤ q ∧ result.1.2.2.2.creationMass ≤ q := by
  have hm := (PMF.mem_support_map_iff Prod.fst _ _).mpr ⟨result, hr, rfl⟩
  rw [certificateTerminalGame_game] at hm
  exact certificateGame_cost_le adversary q required stopAfter stopped hbound result.1 hm
theorem expected_certificateTerminalGame_mass_payoff_le (adversary : Adversary) (q : Nat)
    (required : Finset IndexGroup) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] *
        (result.1.2.2.2.creationMass * payoff result.2)) ≤
      (q : ENNReal) * ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff word := by
  have hword := congrArg (fun law : PMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (certificateTerminalGame_word adversary q required stopAfter stopped total)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at hword
  calc
    _ ≤ ∑' result, (q : ENNReal) *
        (Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] * payoff result.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hzero : Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] = 0
      · rw [hzero, zero_mul, zero_mul, mul_zero]
      · have hr : result ∈ (certificateTerminalGame adversary q required stopAfter stopped total).support := by
          simpa only [PMF.mem_support_iff, PMF.probOutput_eq_apply] using hzero
        have hmass := (certificateTerminalGame_cost_le adversary q required stopAfter stopped total hbound result hr).2
        calc
          _ ≤ Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] *
              ((q : ENNReal) * payoff result.2) := mul_le_mul' le_rfl (mul_le_mul' hmass le_rfl)
          _ = _ := by ring
    _ = _ := by rw [ENNReal.tsum_mul_left, hword]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def proposalPrefixStop : CertificateStopRule :=
  fun input state length record => decide (
    targetProposalOverhead * (state.2.log ++ signingLogFragment input record.output).length + (proposalPrefixSlack : ENNReal) <
      ((state.2.proposals + length : Nat) : ENNReal))
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
def ProposalPrefixExceptional (proposals completed : Nat) : Prop :=
  targetProposalOverhead * completed + (proposalPrefixSlack : ENNReal) < (proposals : ENNReal)
theorem proposalPrefixStop_eq_after_exception (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    proposalPrefixStop input state length record =
      decide (ProposalPrefixExceptional
        (certificateMonitorUpdate key budget required stopAfter input state length record).proposals
        (certificateMonitorUpdate key budget required stopAfter input state length record).log.length) := by
  simp only [proposalPrefixStop, ProposalPrefixExceptional, certificateMonitorUpdate, if_pos hactive,
    proposalRecordLogState]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
noncomputable def proposalTailBase : ENNReal := 1025 / 1024
noncomputable def proposalTailMoment : ENNReal := 6885376000 / 6865219987
theorem proposalBlockLength_power_moment (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (base : ENNReal) :
    (∑' length, proposalBlockLength accept hpos hle length * base ^ length) =
      accept * base / (1 - (1 - accept) * base) := by
  rw [tsum_eq_zero_add' ENNReal.summable, proposalBlockLength_zero, zero_mul, zero_add]
  simp only [proposalBlockLength_succ, pow_succ]
  calc
    _ = ∑' failures, (accept * base) * ((1 - accept) * base) ^ failures := by
      apply tsum_congr
      intro failures
      rw [mul_pow]
      ac_rfl
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]; rfl
theorem proposalTailMoment_eq : proposalTailMoment =
    targetProposalAcceptance * proposalTailBase ^ 2 / (1 - (1 - targetProposalAcceptance) * proposalTailBase ^ 2) := by
  have hrem : (1 - targetProposalAcceptance).toReal = 1 - targetProposalAcceptance.toReal := by
    rw [ENNReal.toReal_sub_of_le targetProposalAcceptance_lt_one.le (by finiteness), ENNReal.toReal_one]
  have hlt : (1 - targetProposalAcceptance) * proposalTailBase ^ 2 < 1 := by
    apply (ENNReal.toReal_lt_toReal (by unfold proposalTailBase; finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, hrem]
    norm_num [ENNReal.toReal_pow, targetProposalAcceptance, targetProposalOverhead,
      proposalTailBase, ENNReal.toReal_inv, ENNReal.toReal_div]
  have hnz : 1 - (1 - targetProposalAcceptance) * proposalTailBase ^ 2 ≠ 0 := (tsub_pos_iff_lt.mpr hlt).ne'
  have haccept : targetProposalAcceptance ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) targetProposalAcceptance_lt_one.le
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold proposalTailMoment; finiteness)
    (ENNReal.div_ne_top (ENNReal.mul_ne_top haccept (by unfold proposalTailBase; finiteness)) hnz)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hlt.le (by finiteness)]
  simp only [ENNReal.toReal_mul, hrem]
  norm_num [proposalTailMoment, ENNReal.toReal_pow, targetProposalAcceptance,
    targetProposalOverhead, proposalTailBase, ENNReal.toReal_inv, ENNReal.toReal_div]
theorem proposalTailMoment_ge_cube : proposalTailBase ^ 3 ≤ proposalTailMoment := by
  apply (ENNReal.toReal_le_toReal (by unfold proposalTailBase; finiteness) (by unfold proposalTailMoment; finiteness)).mp
  norm_num [proposalTailBase, proposalTailMoment, ENNReal.toReal_pow, ENNReal.toReal_div]
theorem proposalTailBase_one_le : 1 ≤ proposalTailBase := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold proposalTailBase; finiteness)).mp
  norm_num [proposalTailBase, ENNReal.toReal_div]
noncomputable def proposalPrefixWeight (proposals completed : Nat) : ENNReal :=
  proposalTailBase ^ (2 * proposals) * proposalTailMoment ^ (signatureLimit - completed) /
    proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack)
theorem proposalPrefixWeight_bad (proposals completed : Nat) (hcap : completed ≤ signatureLimit)
    (hbad : ProposalPrefixExceptional proposals completed) : 1 ≤ proposalPrefixWeight proposals completed := by
  have hcount : 3 * completed + 2 * proposalPrefixSlack ≤ 2 * proposals := by
    have h := (ENNReal.toReal_lt_toReal (by unfold targetProposalOverhead; finiteness) (by finiteness)).mpr hbad
    rw [ENNReal.toReal_add (by unfold targetProposalOverhead; finiteness) (by finiteness), ENNReal.toReal_mul] at h
    norm_num [targetProposalOverhead, ENNReal.toReal_div] at h
    have hc : (0 : ℝ) ≤ completed := Nat.cast_nonneg _
    have h' : (3 : ℝ) * completed + 2 * proposalPrefixSlack ≤ 2 * proposals := by linarith
    exact_mod_cast h'
  have hexp : 3 * signatureLimit + 2 * proposalPrefixSlack ≤ 2 * proposals + 3 * (signatureLimit - completed) := by omega
  have hbase : proposalTailBase ≠ 0 := by norm_num [proposalTailBase]
  have hfinite : proposalTailBase ≠ ⊤ := by unfold proposalTailBase; finiteness
  rw [proposalPrefixWeight]
  calc
    1 = proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack) /
        proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack) := (ENNReal.div_self (pow_ne_zero _ hbase) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right (calc
      _ ≤ proposalTailBase ^ (2 * proposals + 3 * (signatureLimit - completed)) :=
        pow_le_pow_right₀ proposalTailBase_one_le hexp
      _ = proposalTailBase ^ (2 * proposals) * (proposalTailBase ^ 3) ^ (signatureLimit - completed) := by simp only [pow_add, pow_mul]
      _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left₀ (by positivity) proposalTailMoment_ge_cube _)) _
theorem expected_proposalPrefixWeight (proposals completed : Nat) (hcap : completed < signatureLimit) :
    (∑' length, proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le length *
      proposalPrefixWeight (proposals + length) (completed + 1)) = proposalPrefixWeight proposals completed := by
  have hremaining : signatureLimit - completed = (signatureLimit - (completed + 1)) + 1 := by omega
  simp only [proposalPrefixWeight, Nat.mul_add]
  calc
    _ = (proposalTailBase ^ (2 * proposals) * proposalTailMoment ^ (signatureLimit - (completed + 1)) /
        proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack)) *
        ∑' length, proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le length *
          (proposalTailBase ^ 2) ^ length := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro length
      simp only [pow_add, pow_mul, div_eq_mul_inv]
      ac_rfl
    _ = _ := by
      rw [proposalBlockLength_power_moment, ← proposalTailMoment_eq, hremaining]
      simp only [pow_add, pow_one, div_eq_mul_inv]
      ac_rfl
theorem proposalPrefixWeight_initial_le : proposalPrefixWeight 0 0 ≤ proposalPrefixExceptionBound := by
  rw [proposalPrefixExceptionBound_def]
  let z : ℝ := 1025 / 1024
  let ratio : ℝ := 35184372088832 / 35184252433375
  have hz : 0 < z := by norm_num [z]
  have hr : 0 < ratio := by norm_num [ratio]
  have hlog : (signatureLimit : ℝ) * Real.log ratio - 2 * 2 ^ 23 * Real.log z ≤ -700 * Real.log 2 := by
    have hratio := Real.log_le_sub_one_of_pos hr
    have hbase := Real.one_sub_inv_le_log_of_pos hz
    have htwo := Real.log_two_lt_d9
    norm_num [ratio, z, signatureLimit] at hratio hbase ⊢
    linarith
  have hreal : (ratio * z ^ 3) ^ signatureLimit / z ^ (3 * signatureLimit + 2 * 2 ^ 23) ≤ (2 ^ 700 : ℝ)⁻¹ := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul hr.ne' (by positivity),
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_pow]
    push_cast
    nlinarith only [hlog]
  have hmoment : proposalTailMoment.toReal = ratio * z ^ 3 := by
    norm_num [proposalTailMoment, ENNReal.toReal_div, ratio, z]
  have hbase : proposalTailBase.toReal = z := by norm_num [proposalTailBase, ENNReal.toReal_div, z]
  have hfinite : proposalPrefixWeight 0 0 ≠ ⊤ := by
    unfold proposalPrefixWeight
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by unfold proposalTailBase; finiteness))
        (ENNReal.pow_ne_top (by unfold proposalTailMoment; finiteness))
    · exact pow_ne_zero _ (by norm_num [proposalTailBase])
  apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
  simpa only [proposalPrefixWeight, proposalPrefixSlack_def, Nat.mul_zero, pow_zero, one_mul, Nat.sub_zero, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, hmoment, hbase] using hreal
end SphincsSecurity.Concrete
end
end
-- ==== merged from T3_FullCache_SourcePrelude ====
section

section
namespace SigGolfCandidate.T3.BPORS.Adaptive
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
structure ProposalModel {ι : Type} (spec : OracleSpec ι) (State Label : Type) where
  Outcome : spec.Domain → Type
  record : (input : spec.Domain) → State → PMF (Outcome input)
  response : (input : spec.Domain) → Outcome input → spec.Range input
  advance : (input : spec.Domain) → State → Outcome input → State
  label : (input : spec.Domain) → Outcome input → Label
  active : spec.Domain → State → Bool
  base : PMF Label
  accept : ENNReal
  positive : accept ≠ 0
  lt_one : accept < 1
  cap : ∀ input state,active input state=true → ∀ point,
    accept*((record input state).map (label input)) point ≤ base point
namespace ProposalModel
variable {ι State Label : Type} {spec : OracleSpec ι}
noncomputable def rejected (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : State) : PMF Label :=
  if h : model.active input state=true then
    proposalResidualLaw model.base ((model.record input state).map (model.label input))
      model.accept model.lt_one (model.cap input state h)
  else model.base
noncomputable def original (model : ProposalModel spec State Label) :
    QueryImpl spec (StateT State PMF) := fun input => StateT.mk fun state =>
  (model.record input state).map fun outcome =>
    (model.response input outcome,model.advance input state outcome)
noncomputable def traced (model : ProposalModel spec State Label) :
    QueryImpl spec (StateT (List Label × State) PMF) :=
  proposalRecordImpl model.record model.response
    (fun input state _ outcome => model.advance input state outcome)
    model.label model.rejected model.active model.accept model.positive model.lt_one.le
theorem traced_query_erasure (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : List Label × State) :
    Prod.map id Prod.snd <$> (model.traced input).run state=
      (model.original input).run state.2 := by
  rw [traced,proposalRecordImpl_project]
  have h := lengthRecordImpl_project model.record model.response
    (fun input state _ outcome => model.advance input state outcome)
    model.active model.accept model.positive model.lt_one.le
    model.original id model.advance (fun _ _ _ _ => rfl) (fun _ _ => rfl) input state.2
  simpa only [Prod.map_id,id_map,id_eq] using h
theorem traced_erasure {Result : Type} (model : ProposalModel spec State Label)
    (computation : OracleComp spec Result) (state : List Label × State) :
    Prod.map id Prod.snd <$> (simulateQ model.traced computation).run state=
      (simulateQ model.original computation).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd model.traced_query_erasure computation state
theorem traced_query_complete (model : ProposalModel spec State Label)
    (total : Nat) (input : spec.Domain) (state : List Label × State) :
    ((model.traced input).run state).bind
        (fun result => completeProposalWord model.base total result.2.1)=
      completeProposalWord model.base total state.1 := by
  simp only [traced,proposalRecordImpl,StateT.run_mk]
  by_cases hactive : model.active input state.2=true
  · rw [if_pos hactive,PMF.bind_map,rejected,dif_pos hactive]
    simpa only [cappedRecordProposalBridge,List.append_assoc,Function.comp_def] using
      complete_cappedRecordProposalBridge_prefix model.base
        (model.record input state.2) (model.label input) model.accept model.positive model.lt_one
        (model.cap input state.2 hactive) total state.1
  · rw [if_neg hactive,PMF.bind_map]
    simp only [Function.comp_def]
    exact PMF.bind_const _ _
theorem traced_complete {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : List Label × State) :
    ((simulateQ model.traced computation).run state).bind
        (fun result => completeProposalWord model.base total result.2.1)=
      completeProposalWord model.base total state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,PMF.monad_pure_eq_pure,PMF.pure_bind]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,PMF.monad_bind_eq_bind,PMF.bind_bind]
      simp_rw [ih]
      exact model.traced_query_complete total input state
theorem completed_trace_independent {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : State) :
    ((simulateQ model.traced computation).run ([],state)).bind
        (fun result => completeProposalWord model.base total result.2.1)=
      independentProposalWord model.base total := by
  rw [model.traced_complete,completeProposalWord_nil]
theorem monotone_payoff_le_completion (base : PMF Label) (total : Nat)
    (payoff : List Label → ENNReal)
    (hmono : ∀ left right,left.Sublist right → payoff left ≤ payoff right)
    (consumed : List Label) (hused : consumed.length ≤ total) :
    payoff consumed ≤ expectedValue (completeProposalWord base total consumed) payoff := by
  rw [completeProposalWord_eq_padding,List.take_of_length_le hused,← PMF.monad_map_eq_map,
    expectedValue_map]
  calc
    _ = expectedValue (independentProposalWord base (total-consumed.length))
        (fun _ => payoff consumed) := (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun suffix => hmono _ _ (List.sublist_append_left _ _)
theorem capped_trace_expectation {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : State)
    (payoff : List Label → ENNReal)
    (hmono : ∀ left right,left.Sublist right → payoff left ≤ payoff right) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ total then payoff result.2.1 else 0) ≤
      expectedValue (independentProposalWord model.base total) payoff := by
  calc
    _ ≤ expectedValue ((simulateQ model.traced computation).run ([],state))
        (fun result => expectedValue (completeProposalWord model.base total result.2.1) payoff) := by
      apply expectedValue_mono
      intro result
      split
      · exact monotone_payoff_le_completion model.base total payoff hmono _ (by assumption)
      · exact bot_le
    _ = expectedValue (((simulateQ model.traced computation).run ([],state)).bind
        (fun result => completeProposalWord model.base total result.2.1)) payoff := by
      rw [← PMF.monad_bind_eq_bind,expectedValue_bind]
    _ = _ := by rw [model.completed_trace_independent]
theorem uniform_word_expectation [Fintype Label] [SampleableType Label]
    (total : Nat) (payoff : List Label → ENNReal) :
    expectedValue (independentProposalWord (PMF.uniformOfFintype Label) total) payoff=
      uniformWordAverage total payoff := by
  unfold expectedValue uniformWordAverage
  apply tsum_congr
  intro word
  simp only [probOutput_def,evalDist_sampleUniformProposalWord,PMF.evalSPMF_eq]
theorem capped_selected_expectation {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : State)
    (selected : Result × (List Label × State) → List Label)
    (hselected : ∀ result, (selected result).Sublist result.2.1)
    (payoff : List Label → ENNReal)
    (hmono : ∀ left right,left.Sublist right → payoff left ≤ payoff right) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ total then payoff (selected result) else 0) ≤
      expectedValue (independentProposalWord model.base total) payoff := by
  apply le_trans _ (model.capped_trace_expectation total computation state payoff hmono)
  apply expectedValue_mono
  intro result
  split
  · exact hmono _ _ (hselected result)
  · exact le_rfl
end ProposalModel
end SigGolfCandidate.T3.BPORS.Adaptive
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem atIndex_sublist {α β : Type} [DecidableEq α] (index : α)
    {left right : List (α × β)} (h : left.Sublist right) :
    (atIndex index left).Sublist (atIndex index right) := h.filterMap _
theorem bucketMass_sublist {left right : List (Fin 16)} (h : left.Sublist right)
    (bucket : Fin 16) : bucketMass left bucket ≤ bucketMass right bucket := by
  unfold bucketMass
  exact_mod_cast Nat.descFactorial_le 3 (Nat.mul_le_mul_left 3 (h.count_le bucket))
theorem coordinateEnvelope_sublist {left right : List (Fin 16)} (h : left.Sublist right) :
    coordinateEnvelope left ≤ coordinateEnvelope right := by
  unfold coordinateEnvelope
  apply ENNReal.div_le_div_right
  exact Finset.sum_le_sum fun bucket _ => bucketMass_sublist h bucket
theorem wordEnvelope_sublist {left right : List Buckets} (h : left.Sublist right) :
    wordEnvelope left ≤ wordEnvelope right := by
  unfold wordEnvelope
  apply ENNReal.div_le_div_right
  exact Finset.prod_le_prod' fun c _ => coordinateEnvelope_sublist (h.map (fun row => row c))
theorem nearCoordinateEnvelope_sublist {left right : List (Fin 16)} (h : left.Sublist right) :
    Numeric.nearCoordinateEnvelope left ≤ Numeric.nearCoordinateEnvelope right := by
  unfold Numeric.nearCoordinateEnvelope
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro bucket _
  exact_mod_cast Nat.descFactorial_le 2 (Nat.mul_le_mul_left 3 (h.count_le bucket))
theorem nearWordEnvelope_sublist (missing : Fin 7) {left right : List Buckets}
    (h : left.Sublist right) : nearWordEnvelope missing left ≤ nearWordEnvelope missing right := by
  unfold nearWordEnvelope
  apply ENNReal.div_le_div_right
  apply Finset.prod_le_prod'
  intro c _
  split
  · exact nearCoordinateEnvelope_sublist (h.map (fun row => row c))
  · exact coordinateEnvelope_sublist (h.map (fun row => row c))
theorem fullPrice_sublist {left right : List Proposal} (h : left.Sublist right) :
    fullPrice left ≤ fullPrice right := by
  unfold fullPrice
  apply mul_le_mul' le_rfl
  exact Finset.sum_le_sum fun index _ => wordEnvelope_sublist (atIndex_sublist index h)
theorem fullNearPrice_sublist {left right : List Proposal} (h : left.Sublist right) :
    fullNearPrice left ≤ fullNearPrice right := by
  unfold fullNearPrice
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro index _
  exact Finset.sum_le_sum fun missing _ => nearWordEnvelope_sublist missing (atIndex_sublist index h)
theorem adaptive_selected_full_excess {ι State Result : Type} {spec : OracleSpec ι}
    (model : Adaptive.ProposalModel spec State Proposal)
    (hbase : model.base=PMF.uniformOfFintype Proposal)
    (computation : OracleComp spec Result) (state : State)
    (selected : Result × (List Proposal × State) → List Proposal)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ Numeric.proposalLength
        then fullPrice (selected result)-1 else 0) ≤ 11324/100000000 := by
  apply le_trans (model.capped_selected_expectation Numeric.proposalLength computation state selected
    hselected (fun word => fullPrice word-1)
    (fun _ _ h => tsub_le_tsub_right (fullPrice_sublist h) 1))
  rw [hbase,Adaptive.ProposalModel.uniform_word_expectation]
  exact fullPrice_excess_bound
theorem adaptive_selected_near_price {ι State Result : Type} {spec : OracleSpec ι}
    (model : Adaptive.ProposalModel spec State Proposal)
    (hbase : model.base=PMF.uniformOfFintype Proposal)
    (computation : OracleComp spec Result) (state : State)
    (selected : Result × (List Proposal × State) → List Proposal)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ Numeric.proposalLength
        then fullNearPrice (selected result) else 0) ≤ 404 := by
  apply le_trans (model.capped_selected_expectation Numeric.proposalLength computation state selected
    hselected fullNearPrice (fun _ _ h => fullNearPrice_sublist h))
  rw [hbase,Adaptive.ProposalModel.uniform_word_expectation]
  exact fullNearPrice_bound
end SigGolfCandidate.T3.BPORS.History
namespace SigGolfCandidate.T3.Security
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def payloadAfterDigest (cache : Cache) (rho : Digest) (output : HashOutput) : M (Option Signature) := do
  let index := output.toNat % 2^31
  let chosen := selections output
  let state ← (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])
  let root ← forestPk index state.2.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)
def payloadRecordForNonce (cache : Cache) (rho : Digest) (message : Message) :
    M (Option Signature × Option HashOutput) := do
  let found ← digestSearch rho message 0 attemptLimit
  match found with
  | none => pure (none,none)
  | some (_,output) => do
      let signature ← payloadAfterDigest cache rho output
      pure (signature,some output)
def payloadRecord (cache : Cache) (message : Message) :
    M (Option Signature × Option HashOutput) := do
  let rho ← privateNonce message
  payloadRecordForNonce cache rho message
def signingRecord (cache : Cache) (message : Message) :
    M (Option Signature × Option HashOutput) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return (none,none)
  payloadRecord cache message
theorem signPayload_factor (cache : Cache) (message : Message) :
    signPayload cache message=(do
      let rho ← privateNonce message
      let found ← digestSearch rho message 0 attemptLimit
      match found with
      | none => pure none
      | some (_,output) => payloadAfterDigest cache rho output) := by
  unfold signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  cases found with
  | none => rfl
  | some found => cases found;rfl
attribute [local irreducible] digestSearch privateNonce privateMac payloadAfterDigest
theorem payloadRecord_erasure (cache : Cache) (message : Message) :
    Prod.fst <$> payloadRecord cache message=signPayload cache message := by
  rw [signPayload_factor]
  unfold payloadRecord payloadRecordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  cases found with
  | none => rfl
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [map_bind,map_pure]
      exact bind_pure (payloadAfterDigest cache rho output)
theorem signingRecord_erasure (cache : Cache) (message : Message) :
    Prod.fst <$> signingRecord cache message=sign cache message := by
  unfold signingRecord sign
  simp only [map_bind]
  apply bind_congr
  intro tag
  split
  · rfl
  · exact payloadRecord_erasure cache message
theorem realized_signingRecord_erasure (secret : BitVec 256) (cache : Cache) (message : Message) :
    Prod.fst <$> realize secret (signingRecord cache message)=realize secret (sign cache message) := by
  rw [← Cost.realize_map,signingRecord_erasure]
theorem roRun_signingRecord_erasure (secret : BitVec 256) (cache : Cache) (message : Message)
    (oracleCache : RCache) :
    (fun result => (result.1.1,result.2)) <$> roRun secret (signingRecord cache message) oracleCache=
      roRun secret (sign cache message) oracleCache := by
  rw [← roRun_map,signingRecord_erasure]
noncomputable def selectedLabelWeight (payoff : IndexBuckets → ENNReal)
    (record : Option Signature × Option HashOutput) : ENNReal :=
  record.2.elim 0 (fun output => payoff (samplingData output).1)
theorem payloadRecordForNonce_label_le (secret : BitVec 256) (cache : Cache)
    (rho : Digest) (message : Message) (oracleCache : RCache) (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (payloadRecordForNonce cache rho message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤
    expectedValue (roRun secret (digestSearch rho message 0 attemptLimit) oracleCache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1)) := by
  rw [payloadRecordForNonce,roRun_bind,expectedValue_bind]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp [selectedLabelWeight]
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [roRun_bind,expectedValue_bind,roRun_pure,expectedValue_pure,selectedLabelWeight,Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
theorem payloadRecordForNonce_label_cap (secret : BitVec 256) (cache : Cache)
    (rho : Digest) (message : Message) (oracleCache : RCache)
    (hreject : CachedTrialsReject (digestTrial rho message) digestDecode 0 (2^32) oracleCache)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (payloadRecordForNonce cache rho message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤ BPORS.finiteAverage payoff :=
  (payloadRecordForNonce_label_le secret cache rho message oracleCache payoff).trans
    (digestSearch_label_weight_le_of_cached_reject secret rho message attemptLimit 0
      (by decide) oracleCache hreject payoff)
theorem payloadRecord_selected_valid (answers : Correctness.Answers) (cache : Cache)
    (rho : Digest) (message : Message) (output : HashOutput)
    (hrecord : (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).2=some output) :
    ∃ counter,evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit)=some (counter,output) ∧
      admissible (selections output)=true := by
  unfold payloadRecordForNonce at hrecord
  simp only [evalWithAnswerFn_bind] at hrecord
  cases hd : evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,reduceCtorEq] at hrecord
  | some found =>
      rcases found with ⟨counter,value⟩
      simp only [hd,evalWithAnswerFn_bind,evalWithAnswerFn_pure,Option.some.injEq] at hrecord
      subst output
      exact ⟨counter,rfl,(Correctness.digestSearch_some answers rho message attemptLimit 0
        counter value (by decide) hd).2.2.2⟩
theorem payloadRecord_success_has_digest (answers : Correctness.Answers) (cache : Cache)
    (rho : Digest) (message : Message)
    (hs : (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).1 ≠ none) :
    (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).2 ≠ none := by
  unfold payloadRecordForNonce at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs ⊢
  cases hd : evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,ne_eq,not_true_eq_false] at hs
  | some found =>
      rcases found with ⟨counter,value⟩
      simp only [hd,evalWithAnswerFn_bind,evalWithAnswerFn_pure,ne_eq,reduceCtorEq,not_false_eq_true]
theorem payloadRecord_label_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache)
    (hreject : ∀ nonce ∈ support (roRun secret (privateNonce message) oracleCache),
      CachedTrialsReject (digestTrial nonce.1 message) digestDecode 0 (2^32) nonce.2)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (payloadRecord cache message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤ BPORS.finiteAverage payoff := by
  rw [payloadRecord,roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro nonce hn
  exact payloadRecordForNonce_label_cap secret cache nonce.1 message nonce.2 (hreject nonce hn) payoff
theorem signingRecord_label_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache)
    (hreject : ∀ auth ∈ support (roRun secret (privateMac cache.region) oracleCache),
      auth.1=cache.tag → ∀ nonce ∈ support (roRun secret (privateNonce message) auth.2),
      CachedTrialsReject (digestTrial nonce.1 message) digestDecode 0 (2^32) nonce.2)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (signingRecord cache message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤ BPORS.finiteAverage payoff := by
  rw [signingRecord,roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro auth ha
  split
  · simp [selectedLabelWeight]
  · rename_i htag
    apply payloadRecord_label_cap secret cache message auth.2 _ payoff
    exact hreject auth ha (by simpa only [ne_eq,not_not] using htag)
end SigGolfCandidate.T3.Security
namespace SigGolfCandidate.T3.Security
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestSearch payloadAfterDigest Finset.univ BPORS.finiteAverage DigestSampling.samplingData
theorem payloadRecordForNonce_completed_label_le (secret : BitVec 256) (cache : Cache)
    (rho : Digest) (message : Message) (oracleCache : RCache) (payoff : IndexBuckets → ENNReal) (fallback : ENNReal) :
    expectedValue (roRun secret (payloadRecordForNonce cache rho message) oracleCache)
      (fun result => result.1.2.elim fallback
        (fun output => payoff (samplingData output).1)) ≤
    expectedValue (roRun secret (digestSearch rho message 0 attemptLimit) oracleCache)
      (fun result => result.1.elim fallback
        (fun found => payoff (samplingData found.2).1)) := by
  rw [payloadRecordForNonce,roRun_bind,expectedValue_bind]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [roRun_pure,expectedValue_pure,Option.elim_none,le_refl]
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [roRun_bind,expectedValue_bind,roRun_pure,expectedValue_pure,Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
noncomputable def freshNoncePayloadRecord (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    ProbComp (((Option Signature × Option HashOutput) × RCache) × IndexBuckets) :=
  completeRecord (fun result => result.1.2) do
    let rho ← $ᵗ Digest
    roRun secret (payloadRecordForNonce cache rho message) oracleCache
theorem freshNoncePayloadRecord_erasure (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    𝒮[Prod.fst <$> freshNoncePayloadRecord secret cache message oracleCache]=
      𝒮[($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (payloadRecordForNonce cache rho message) oracleCache] :=
  completeRecord_erasure _ _
theorem freshNoncePayloadRecord_target_bound (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (targets : Finset IndexBuckets) :
    Pr[fun result => result.2 ∈ targets | freshNoncePayloadRecord secret cache message oracleCache] ≤
      targets.card/(2 : ENNReal)^59+cachedTargetCount targets oracleCache/(2 : ENNReal)^128 := by
  rw [← expectedValue_ite_one]
  change expectedValue (completeRecord _ _) (fun result => targetWeight targets result.2) ≤ _
  rw [completeRecord_expected,expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        expectedValue (roRun secret (digestSearch rho message 0 attemptLimit) oracleCache)
          (fun result => completedTargetScore targets result.1)) :=
      expectedValue_mono _ fun rho => payloadRecordForNonce_completed_label_le secret cache rho message oracleCache _ _
    _ ≤ _ := by
      rw [← expectedValue_bind]
      exact uniform_nonce_completed_target_bound secret message attemptLimit (by decide) oracleCache targets
theorem freshNoncePayloadRecord_point_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (hfinite : SphincsSecurity.Finite oracleCache)
    (budget : Nat) (hsize : QueryCache.enncard oracleCache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional oracleCache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    Pr[fun result => result.2=point | freshNoncePayloadRecord secret cache message oracleCache] ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  have h := freshNoncePayloadRecord_target_bound secret cache message oracleCache {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  exact h.trans (clean_point_bound_arithmetic oracleCache hfinite budget hsize hbudget hclean haccept point)
noncomputable def freshNoncePayloadLaw (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    PMF (((Option Signature × Option HashOutput) × RCache) × IndexBuckets) :=
  liftM (freshNoncePayloadRecord secret cache message oracleCache)
theorem freshNoncePayloadLaw_label_probability (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (point : IndexBuckets) :
    ((freshNoncePayloadLaw secret cache message oracleCache).map Prod.snd) point=
      Pr[fun result => result.2=point | freshNoncePayloadRecord secret cache message oracleCache] := by
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map]
  rfl
theorem freshNoncePayloadLaw_erasure (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    (freshNoncePayloadLaw secret cache message oracleCache).map Prod.fst=
      (liftM (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (payloadRecordForNonce cache rho message) oracleCache) :
        PMF ((Option Signature × Option HashOutput) × RCache)) := by
  apply PMF.ext
  intro result
  have h := evalSPMF_ext_iff.mp (freshNoncePayloadRecord_erasure secret cache message oracleCache) result
  rw [probOutput_map] at h
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map]
  rw [← PMF.probOutput_eq_apply]
  exact h
theorem freshNoncePayloadLaw_scaled_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (hfinite : SphincsSecurity.Finite oracleCache)
    (budget : Nat) (hsize : QueryCache.enncard oracleCache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional oracleCache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    (1024/1025 : ENNReal)*((freshNoncePayloadLaw secret cache message oracleCache).map Prod.snd) point ≤
      (PMF.uniformOfFintype IndexBuckets) point := by
  have hc : Fintype.card IndexBuckets=2^59 := by
    norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  rw [freshNoncePayloadLaw_label_probability,PMF.uniformOfFintype_apply,hc,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) :=
      mul_le_mul' le_rfl (freshNoncePayloadRecord_point_cap secret cache message oracleCache
        hfinite budget hsize hbudget hclean haccept point)
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SigGolfCandidate.T3.Security
namespace SigGolfCandidate.T3.Security
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling DigestSampling
theorem freshNoncePayloadLaw_scaled_cap_source (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (hfinite : SphincsSecurity.Finite oracleCache)
    (budget : Nat) (hsize : QueryCache.enncard oracleCache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional oracleCache) (point : IndexBuckets) :
    (1024/1025 : ENNReal)*((freshNoncePayloadLaw secret cache message oracleCache).map Prod.snd) point ≤
      (PMF.uniformOfFintype IndexBuckets) point :=
  freshNoncePayloadLaw_scaled_cap secret cache message oracleCache hfinite budget hsize hbudget
    hclean Acceptance.acceptanceProbability_le_one_sixteenth point
end SigGolfCandidate.T3.Security
end
section
namespace SigGolfCandidate.T3.Security.PrivateTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {ι D R State : Type} {base : OracleSpec ι}
variable [DecidableEq D] [SampleableType R]
abbrev Cache (D R : Type) := QueryCache (D →ₒ R)
def fill (cache : Cache D R) (table : D → R) : D → R :=
  fun input => (cache input).getD (table input)
omit [DecidableEq D] [SampleableType R] in
theorem fill_empty (table : D → R) : fill (∅ : Cache D R) table=table := by
  funext input
  rfl
omit [DecidableEq D] [SampleableType R] in
theorem fill_cached (cache : Cache D R) (table : D → R) (input : D) (value : R)
    (h : cache input=some value) : fill cache table input=value := by
  simp only [fill,h,Option.getD_some]
omit [SampleableType R] in
theorem cacheQuery_cached (cache : Cache D R) (input : D) (value : R)
    (h : cache input=some value) : cache.cacheQuery input value=cache := by
  funext other
  by_cases he : other=input
  · subst other
    rw [QueryCache.cacheQuery_self,h]
  · exact QueryCache.cacheQuery_of_ne cache value he
omit [SampleableType R] in
theorem fill_update (cache : Cache D R) (table : D → R) (input : D) (value : R)
    (h : cache input=none) :
    fill (cache.cacheQuery input value) table=fill cache (Function.update table input value) := by
  funext other
  by_cases he : other=input
  · subst other
    simp only [fill,QueryCache.cacheQuery_self,Option.getD_some,h,Option.getD_none,
      Function.update_self]
  · simp only [fill,QueryCache.cacheQuery_of_ne cache value he,Function.update_of_ne he]
noncomputable def lazyImpl (handler : QueryImpl base (StateT State ProbComp)) :
    QueryImpl (base+(D →ₒ R)) (StateT (Cache D R × State) ProbComp)
  | .inl input => StateT.mk fun state => do
      let result ← (handler input).run state.2
      pure (result.1,(state.1,result.2))
  | .inr input => StateT.mk fun state => do
      let result ← (randomOracle (spec := D →ₒ R) input).run state.1
      pure (result.1,(result.2,state.2))
noncomputable def eagerImpl (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) : QueryImpl (base+(D →ₒ R)) (StateT (Cache D R × State) ProbComp)
  | .inl input => StateT.mk fun state => do
      let result ← (handler input).run state.2
      pure (result.1,(state.1,result.2))
  | .inr input => StateT.mk fun state =>
      pure (table input,(state.1.cacheQuery input (table input),state.2))
noncomputable def lazyRun {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (cache : Cache D R) (state : State) :
    ProbComp (α × (Cache D R × State)) :=
  (simulateQ (lazyImpl handler) program).run (cache,state)
noncomputable def eagerRun {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) (program : OracleComp (base+(D →ₒ R)) α)
    (cache : Cache D R) (state : State) : ProbComp (α × (Cache D R × State)) :=
  (simulateQ (eagerImpl handler table) program).run (cache,state)
variable [Finite D] [Finite R] [Nonempty R] [SampleableType (D → R)]
theorem refresh_table {α : Type} (input : D) (next : (D → R) → ProbComp α) :
    𝒮[do let value ← $ᵗ R; let table ← $ᵗ (D → R); next (Function.update table input value)]=
      𝒮[do let table ← $ᵗ (D → R); next table] := by
  symm
  rw [evalSPMF_bind,← evalSPMF_uniformSample_bind_update input,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]
theorem lazyRun_eq_completed_table {α : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (cache : Cache D R) (state : State) :
    𝒮[lazyRun handler program cache state]=
      𝒮[do let table ← $ᵗ (D → R); eagerRun handler (fill cache table) program cache state] := by
  induction program using OracleComp.inductionOn generalizing cache state with
  | pure value =>
      apply evalSPMF_ext
      intro result
      simp [lazyRun,eagerRun]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun,eagerRun,simulateQ_bind,simulateQ_spec_query,lazyImpl,eagerImpl,
            StateT.run_bind,StateT.run_mk,bind_assoc,pure_bind]
          rw [evalSPMF_bind_bind_swap]
          apply evalSPMF_bind_congr'
          intro result
          exact ih result.1 cache result.2
      | inr input =>
          simp only [lazyRun,eagerRun,simulateQ_bind,simulateQ_spec_query,lazyImpl,eagerImpl,
            StateT.run_bind,StateT.run_mk,bind_assoc,pure_bind]
          cases hc : cache input with
          | some value =>
              rw [QueryImpl.withCaching_run_some _ hc,pure_bind]
              simp_rw [fill_cached cache _ input value hc,cacheQuery_cached cache input value hc]
              exact ih value cache state
          | none =>
              rw [QueryImpl.withCaching_run_none _ hc]
              simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_apply]
              trans 𝒮[do
                let value ← $ᵗ R
                let table ← $ᵗ (D → R)
                eagerRun handler (fill (cache.cacheQuery input value) table)
                  (next value) (cache.cacheQuery input value) state]
              · apply evalSPMF_bind_congr'
                intro value
                exact ih value (cache.cacheQuery input value) state
              · simp_rw [fill_update cache _ input _ hc]
                let continuation : (D → R) → ProbComp (α × (Cache D R × State)) :=
                  fun table => eagerRun handler (fill cache table)
                    (next (table input)) (cache.cacheQuery input (table input)) state
                have hpoint : ∀ value table,
                    eagerRun handler (fill cache (Function.update table input value))
                      (next value) (cache.cacheQuery input value) state=
                    continuation (Function.update table input value) := by
                  intro value table
                  simp only [continuation,Function.update_self]
                simp_rw [hpoint]
                rw [refresh_table input continuation]
                simp only [continuation,fill,hc,Option.getD_none]
                rfl
theorem lazyRun_empty_eq_uniform_table {α : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (state : State) :
    𝒮[lazyRun handler program ∅ state]=
      𝒮[do let table ← $ᵗ (D → R); eagerRun handler table program ∅ state] := by
  simpa only [fill_empty] using lazyRun_eq_completed_table handler program ∅ state
noncomputable def fixedImpl (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) : QueryImpl (base+(D →ₒ R)) (StateT State ProbComp) :=
  handler+(fun input => (pure (table input) : StateT State ProbComp R))
omit [SampleableType R] [Finite D] [Finite R] [Nonempty R] [SampleableType (D → R)] in
theorem eagerRun_erasure {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) (program : OracleComp (base+(D →ₒ R)) α)
    (cache : Cache D R) (state : State) :
    Prod.map id Prod.snd <$> eagerRun handler table program cache state=
      (simulateQ (fixedImpl handler table) program).run state := by
  apply map_run_simulateQ_eq_of_query_map_eq (eagerImpl handler table)
    (fixedImpl handler table) Prod.snd _ program (cache,state)
  intro input current
  cases input with
  | inl input =>
      change Prod.map id Prod.snd <$> (do
        let result ← (handler input).run current.2
        pure (result.1,(current.1,result.2)))=(handler input).run current.2
      simp only [map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta,bind_pure]
  | inr input =>
      change Prod.map id Prod.snd <$>
        (pure (table input,(current.1.cacheQuery input (table input),current.2)) : ProbComp _)=
        pure (table input,current.2)
      rw [map_pure]
      rfl
theorem lazyRun_erasure {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (state : State) :
    𝒮[Prod.map id Prod.snd <$> lazyRun handler program ∅ state]=
      𝒮[do let table ← $ᵗ (D → R); (simulateQ (fixedImpl handler table) program).run state] := by
  have h := congrArg (Functor.map (Prod.map id Prod.snd))
    (lazyRun_empty_eq_uniform_table handler program state)
  simpa only [← evalSPMF_map,map_bind,eagerRun_erasure] using h
end SigGolfCandidate.T3.Security.PrivateTable
namespace SigGolfCandidate.T3.Security.LazyPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType (Coordinate → HashOutput) :=
  Derivation.outputSampler Coordinate
abbrev PCache := QueryCache (Coordinate →ₒ HashOutput)
abbrev State := PCache × Sampling.RCache
noncomputable def run {α : Type} (program : M α) (state : State) : ProbComp (α × State) :=
  PrivateTable.lazyRun SphincsSecurity.romImpl program state.1 state.2
theorem fixedImpl_eq (outputs : Coordinate → HashOutput) :
    PrivateTable.fixedImpl SphincsSecurity.romImpl outputs=
      QueryImpl.compose SphincsSecurity.romImpl (Derivation.tableHandler outputs) := by
  funext input
  cases input with
  | inl input => simp only [PrivateTable.fixedImpl,QueryImpl.compose,
      Derivation.tableHandler,simulateQ_spec_query];rfl
  | inr input => simp only [PrivateTable.fixedImpl,QueryImpl.compose,
      Derivation.tableHandler,simulateQ_pure];rfl
theorem run_eq_table {α : Type} (program : M α) (cache : Sampling.RCache) :
    𝒮[Prod.map id Prod.snd <$> run program (∅,cache)]=
      𝒮[do
        let outputs ← $ᵗ (Coordinate → HashOutput)
        (simulateQ SphincsSecurity.romImpl (Derivation.tableRun outputs program)).run cache] := by
  rw [run,PrivateTable.lazyRun_erasure]
  simp only [fixedImpl_eq,QueryImpl.simulateQ_compose,Derivation.tableRun]
noncomputable def experiment (adversary : Adversary) (q : Nat) :
    ProbComp (Option (Bool × Nat)) :=
  Prod.fst <$> run (Derivation.cap (game adversary) q) (∅,∅)
theorem tableExperiment_eq (adversary : Adversary) (q : Nat) :
    𝒮[tableExperiment adversary q]=𝒮[experiment adversary q] := by
  have h := congrArg (Functor.map Prod.fst)
    (run_eq_table (Derivation.cap (game adversary) q) ∅)
  simp only [← evalSPMF_map,map_bind,Functor.map_map,Prod.map,
    id_eq,← StateT.run'_eq] at h
  unfold tableExperiment experiment
  simp only [evalSPMF_bind,evalSPMF_uniformSample] at h ⊢
  exact h.symm
theorem real_event_bound (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true |
        experiment adversary q]+q/((2^256 : Nat) : ENNReal) := by
  have h := private_derivation_event_bound adversary q hq
  have he : Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true |
      tableExperiment adversary q]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true |
        experiment adversary q] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (tableExperiment_eq adversary q)
  rw [he] at h
  exact h
@[simp] theorem run_pure {α : Type} (value : α) (state : State) :
    run (pure value : M α) state=pure (value,state) := by
  simp only [run,PrivateTable.lazyRun,simulateQ_pure,StateT.run_pure,Prod.mk.eta]
theorem run_bind {α β : Type} (program : M α) (next : α → M β) (state : State) :
    run (program >>= next) state=run program state >>= fun result => run (next result.1) result.2 := by
  simp only [run,PrivateTable.lazyRun,simulateQ_bind,StateT.run_bind]
theorem run_map {α β : Type} (f : α → β) (program : M α) (state : State) :
    run (f <$> program) state=Prod.map f id <$> run program state := by
  simp only [run,PrivateTable.lazyRun,simulateQ_map,StateT.run_map]
  rfl
theorem run_query (input : T3.Spec.Domain) (state : State) :
    run (liftM (T3.Spec.query input)) state=
      (PrivateTable.lazyImpl SphincsSecurity.romImpl input).run state := by
  simp only [run,PrivateTable.lazyRun,simulateQ_spec_query]
theorem run_publicQuery (input : HashInput) (state : State) :
    run (Sampling.publicHandler input) state=(do
      let result ← (randomOracle (spec := SphincsSecurity.HashSpec) input).run state.2
      pure (result.1,(state.1,result.2))) := by
  rw [Sampling.publicHandler,run_query]
  simp only [PrivateTable.lazyImpl,StateT.run_mk,SphincsSecurity.romImpl,
    QueryImpl.add_apply_inr]
  rfl
theorem run_publicProgram {α : Type} (program : Sampling.RawM α) (state : State) :
    run (Sampling.publicProgram program) state=
      (fun result => (result.1,(state.1,result.2))) <$>
        (simulateQ (randomOracle (spec := SphincsSecurity.HashSpec)) program).run state.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [Sampling.publicProgram]
  | query_bind input next ih =>
      simp only [Sampling.publicProgram,simulateQ_bind,simulateQ_spec_query,run_bind]
      rw [run_publicQuery]
      change ((do
        let result ← (randomOracle (spec := SphincsSecurity.HashSpec) input).run state.2
        pure (result.1,(state.1,result.2))) >>= fun result =>
          run (Sampling.publicProgram (next result.1)) result.2)=_
      simp only [bind_assoc,pure_bind,StateT.run_bind,map_bind]
      apply bind_congr
      intro result
      exact ih result.1 (state.1,result.2)
theorem run_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) (state : State) :
    run (digestSearch rho message counter fuel) state=
      (fun result => (result.1,(state.1,result.2))) <$>
        Sampling.roRun 0 (digestSearch rho message counter fuel) state.2 := by
  rw [Sampling.digestSearch_public,run_publicProgram,Sampling.roRun,Sampling.public_randomOracle]
theorem run_privateNonce_fresh (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) :
    run (privateNonce message) state=(do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (output.extractLsb' 0 128,
        (state.1.cacheQuery (.inr (.inl message)) output,state.2))) := by
  unfold privateNonce privateHash
  rw [run_bind,run_query]
  change ((do
    let result ← (randomOracle (spec := Coordinate →ₒ HashOutput) (.inr (.inl message))).run state.1
    pure (result.1,(result.2,state.2))) >>= fun result =>
      run (pure (result.1.extractLsb' 0 128)) result.2)=_
  rw [QueryImpl.withCaching_run_none _ hfresh]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,run_pure,Function.comp_apply]
  rfl
theorem payloadForNonce_completed_label_le (cache : T3.Cache) (rho : Digest) (message : Message)
    (state : State) (payoff : DigestSampling.IndexBuckets → ENNReal) (fallback : ENNReal) :
    expectedValue (run (payloadRecordForNonce cache rho message) state)
      (fun result => result.1.2.elim fallback
        (fun output => payoff (DigestSampling.samplingData output).1)) ≤
    expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
      (fun result => result.1.elim fallback
        (fun found => payoff (DigestSampling.samplingData found.2).1)) := by
  rw [payloadRecordForNonce,run_bind,expectedValue_bind,run_digestSearch,expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [run_pure,expectedValue_pure,Option.elim_none,le_refl]
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [run_bind,expectedValue_bind,run_pure,expectedValue_pure,Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
theorem uniform_hash_low_expectation (payoff : Digest → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => payoff (output.extractLsb' 0 128))=
      expectedValue ($ᵗ Digest : ProbComp Digest) payoff := by
  rw [← expectedValue_map]
  exact expectedValue_congr (evalSPMF_ext_iff.mp
    (SphincsSecurity.evalDist_hashOutput_extract_uniform (by decide : 128 ≤ SphincsSecurity.hashOutputBits))) payoff
theorem payload_completed_target_bound (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    expectedValue (run (payloadRecord cache message) state)
      (fun result => result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)) ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
  rw [payloadRecord,run_bind,run_privateNonce_fresh message state hfresh]
  simp only [bind_assoc,pure_bind,expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
        expectedValue (Sampling.roRun 0
          (digestSearch (output.extractLsb' 0 128) message 0 attemptLimit) state.2)
          (fun result => Sampling.completedTargetScore targets result.1)) :=
      expectedValue_mono _ fun output => payloadForNonce_completed_label_le cache _ message
        (state.1.cacheQuery (.inr (.inl message)) output,state.2)
        (Sampling.targetWeight targets) (BPORS.finiteAverage (Sampling.targetWeight targets))
    _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => Sampling.completedTargetScore targets result.1)) :=
      uniform_hash_low_expectation (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => Sampling.completedTargetScore targets result.1))
    _ ≤ targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
      rw [← expectedValue_bind]
      exact Sampling.uniform_nonce_completed_target_bound 0 message attemptLimit (by decide) state.2 targets
theorem run_privateHash (coordinate : Coordinate) (state : State) :
    run (privateHash coordinate) state=(do
      let result ← (randomOracle (spec := Coordinate →ₒ HashOutput) coordinate).run state.1
      pure (result.1,(result.2,state.2))) := by
  rw [privateHash,run_query]
  rfl
theorem privateHash_preserves_other (coordinate other : Coordinate) (hne : other ≠ coordinate)
    (state : State) (result : HashOutput × State) (hresult : result ∈ support (run (privateHash coordinate) state)) :
    result.2.1 other=state.1 other ∧ result.2.2=state.2 := by
  rw [run_privateHash] at hresult
  cases hc : state.1 coordinate with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hc,pure_bind,support_pure,Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨rfl,rfl⟩
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc] at hresult
      simp only [bind_map_left,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hresult
      obtain ⟨output,_,rfl⟩ := hresult
      exact ⟨QueryCache.cacheQuery_of_ne state.1 output hne,rfl⟩
theorem privateMac_preserves_nonce (region : Region) (message : Message)
    (state : State) (result : HashOutput × State)
    (hresult : result ∈ support (run (privateMac region) state)) :
    result.2.1 (.inr (.inl message))=state.1 (.inr (.inl message)) ∧ result.2.2=state.2 := by
  unfold privateMac privateMacKey at hresult
  simp only [bind_assoc,pure_bind,run_bind,mem_support_bind_iff] at hresult
  obtain ⟨first,hfirst,second,hsecond,htail⟩ := hresult
  rw [run_pure,support_pure,Set.mem_singleton_iff] at htail
  subst result
  have h0 := privateHash_preserves_other (.inl (header 14 0 0 0 0))
    (.inr (.inl message)) (by simp) state first hfirst
  have h1 := privateHash_preserves_other (.inl (header 14 0 0 0 1))
    (.inr (.inl message)) (by simp) first.2 second hsecond
  exact ⟨h1.1.trans h0.1,h1.2.trans h0.2⟩
theorem signing_completed_target_bound (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    expectedValue (run (signingRecord cache message) state)
      (fun result => result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)) ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
  rw [signingRecord,run_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro result hresult
  have hp := privateMac_preserves_nonce cache.region message state result hresult
  split_ifs with htag
  · simp only [run_pure,expectedValue_pure,Option.elim_none,Sampling.targetWeight_average]
    exact le_add_right le_rfl
  · have h := payload_completed_target_bound cache message result.2 (hp.1.trans hfresh) targets
    rw [hp.2] at h
    exact h
noncomputable def signingRecordLaw (cache : T3.Cache) (message : Message) (state : State) :
    PMF (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets) :=
  liftM (Sampling.completeRecord (fun result => result.1.2) (run (signingRecord cache message) state))
theorem signingRecordLaw_target_bound (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    Pr[fun result => result.2 ∈ targets | signingRecordLaw cache message state] ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
  rw [← expectedValue_ite_one]
  change expectedValue (Sampling.completeRecord (fun result => result.1.2)
    (run (signingRecord cache message) state)) (fun result => Sampling.targetWeight targets result.2) ≤ _
  rw [Sampling.completeRecord_expected]
  exact signing_completed_target_bound cache message state hfresh targets
theorem signingRecordLaw_scaled_cap (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (hfinite : SphincsSecurity.Finite state.2)
    (budget : Nat) (hsize : QueryCache.enncard state.2 ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬Sampling.TargetCacheExceptional state.2) (point : DigestSampling.IndexBuckets) :
    (1024/1025 : ENNReal)*((signingRecordLaw cache message state).map Prod.snd) point ≤
      (PMF.uniformOfFintype DigestSampling.IndexBuckets) point := by
  have hc : Fintype.card DigestSampling.IndexBuckets=2^59 := by
    norm_num [DigestSampling.IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  have h := signingRecordLaw_target_bound cache message state hfresh {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  have hpoint := h.trans (Sampling.clean_point_bound_arithmetic state.2 hfinite budget hsize hbudget
    hclean Acceptance.acceptanceProbability_le_one_sixteenth point)
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    PMF.uniformOfFintype_apply,hc,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) := mul_le_mul' le_rfl hpoint
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem signingRecordLaw_erasure (cache : T3.Cache) (message : Message) (state : State) :
    (signingRecordLaw cache message state).map (fun result => (result.1.1.1,result.1.2))=
      (liftM (run (sign cache message) state) : PMF (Option Signature × State)) := by
  have hsign : Prod.map Prod.fst id <$> run (signingRecord cache message) state=
      run (sign cache message) state := by
    rw [← run_map,signingRecord_erasure]
  have hg :
      𝒮[(fun result => (result.1.1.1,result.1.2)) <$>
        Sampling.completeRecord (fun result => result.1.2) (run (signingRecord cache message) state)]=
      𝒮[run (sign cache message) state] := by
    trans 𝒮[Prod.map Prod.fst id <$>
      (Prod.fst <$> Sampling.completeRecord (fun result => result.1.2) (run (signingRecord cache message) state))]
    · rw [Functor.map_map]
      rfl
    · rw [evalSPMF_map,Sampling.completeRecord_erasure,← evalSPMF_map,hsign]
  apply PMF.ext
  intro response
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    ← PMF.probOutput_eq_apply]
  have h := evalSPMF_ext_iff.mp hg response
  rw [probOutput_map] at h
  exact h
abbrev Interaction := SphincsSecurity.OracleWorld+Requests
def interactionSource : QueryImpl Interaction M
  | .inl input => forwardWorld input
  | .inr request => sign request.cache request.message
def InteractionOutcome : Interaction.Domain → Type
  | .inl input => SphincsSecurity.OracleWorld.Range input × State
  | .inr _ => (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets)
noncomputable def interactionRecord : (input : Interaction.Domain) → State → PMF (InteractionOutcome input)
  | .inl input,state => liftM (run (forwardWorld input) state)
  | .inr request,state => signingRecordLaw request.cache request.message state
def interactionResponse : (input : Interaction.Domain) → InteractionOutcome input → Interaction.Range input
  | .inl _,result => result.1
  | .inr _,result => result.1.1.1
def interactionAdvance : (input : Interaction.Domain) → State → InteractionOutcome input → State
  | .inl _,_,result => result.2
  | .inr _,_,result => result.1.2
def interactionLabel : (input : Interaction.Domain) → InteractionOutcome input → DigestSampling.IndexBuckets
  | .inl _,_ => default
  | .inr _,result => result.2
noncomputable def interactionActive (budget : Nat) : Interaction.Domain → State → Bool
  | .inl _,_ => false
  | .inr request,state => decide (
      state.1 (.inr (.inl request.message))=none ∧ SphincsSecurity.Finite state.2 ∧
      QueryCache.enncard state.2 ≤ budget ∧ ¬Sampling.TargetCacheExceptional state.2)
noncomputable def proposalModel (budget : Nat) (hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel Interaction State DigestSampling.IndexBuckets where
  Outcome := InteractionOutcome
  record := interactionRecord
  response := interactionResponse
  advance := interactionAdvance
  label := interactionLabel
  active := interactionActive budget
  base := PMF.uniformOfFintype DigestSampling.IndexBuckets
  accept := 1024/1025
  positive := by norm_num
  lt_one := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  cap := by
    intro input state hactive point
    cases input with
    | inl input => simp [interactionActive] at hactive
    | inr request =>
        change decide (_ ∧ _ ∧ _ ∧ _)=true at hactive
        obtain ⟨hfresh,hfinite,hsize,hclean⟩ := of_decide_eq_true hactive
        exact signingRecordLaw_scaled_cap request.cache request.message state
          hfresh hfinite budget hsize hbudget hclean point
theorem proposal_query_erasure (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : Interaction.Domain) (state : State) :
    (((proposalModel budget hbudget).original input).run state)=
      (liftM (run (interactionSource input) state) : PMF (Interaction.Range input × State)) := by
  cases input with
  | inl input =>
      change (fun result : SphincsSecurity.OracleWorld.Range input × State => (result.1,result.2)) <$>
        (liftM (run (forwardWorld input) state) : PMF _)=_
      change id <$> (liftM (run (forwardWorld input) state) : PMF _)=_
      rw [id_map]
      rfl
  | inr request =>
      exact signingRecordLaw_erasure request.cache request.message state
theorem proposal_execution_erasure {α : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction α) (state : State) :
    (simulateQ (proposalModel budget hbudget).original program).run state=
      (liftM (run (simulateQ interactionSource program) state) : PMF (α × State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction α) (history : List DigestSampling.IndexBuckets) (state : State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel budget hbudget).traced program).run (history,state)=
      (liftM (run (simulateQ interactionSource program) state) : PMF (α × State)) := by
  rw [(proposalModel budget hbudget).traced_erasure,proposal_execution_erasure]
end SigGolfCandidate.T3.Security.LazyPrivate
namespace SigGolfCandidate.T3.Security.NonceFreshness
open OracleComp OracleSpec
open LazyPrivate
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def nonceQuery (message : Message) : T3.Spec.Domain := .inr (.inr (.inl message))
abbrev Avoids {α : Type} (message : Message) (program : M α) : Prop :=
  AllQueriesSatisfy program (fun input => input ≠ nonceQuery message)
variable (protectedMessage : Message)
theorem avoids_pure {α : Type} (value : α) : Avoids protectedMessage (pure value) :=
  allQueriesSatisfy_pure _ _
theorem avoids_bind {α β : Type} {program : M α} {next : α → M β}
    (hp : Avoids protectedMessage program) (hn : ∀ value,Avoids protectedMessage (next value)) :
    Avoids protectedMessage (program >>= next) := allQueriesSatisfy_bind hp hn
theorem avoids_map {α β : Type} (f : α → β) {program : M α}
    (hp : Avoids protectedMessage program) : Avoids protectedMessage (f <$> program) := by
  rw [map_eq_bind_pure_comp]
  exact avoids_bind protectedMessage hp fun _ => avoids_pure _ _
theorem avoids_foldlM {α β : Type} (items : List β) (f : α → β → M α)
    (h : ∀ a b,Avoids protectedMessage (f a b)) (initial : α) :
    Avoids protectedMessage (items.foldlM f initial) := by
  induction items generalizing initial with
  | nil => exact avoids_pure _ _
  | cons a items ih =>
      rw [List.foldlM_cons]
      exact avoids_bind protectedMessage (h initial a) ih
theorem avoids_mapM {α β : Type} (items : List α) (f : α → M β)
    (h : ∀ a,Avoids protectedMessage (f a)) : Avoids protectedMessage (items.mapM f) := by
  induction items with
  | nil => exact avoids_pure _ _
  | cons a items ih =>
      rw [List.mapM_cons]
      exact avoids_bind protectedMessage (h a) fun _ =>
        avoids_bind protectedMessage ih fun _ => avoids_pure _ _
theorem avoids_publicHash (input : HashInput) : Avoids protectedMessage (publicHash input) := by
  exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])
theorem avoids_privatePair (tag lay tree position index : Nat) :
    Avoids protectedMessage (privatePair tag lay tree position index) := by
  unfold privatePair
  apply avoids_bind protectedMessage
  · exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])
  · intro _
    exact avoids_pure _ _
theorem avoids_privateMac (region : Region) : Avoids protectedMessage (privateMac region) := by
  have hk (i : Nat) : Avoids protectedMessage (privateHash (.inl (header 14 0 0 0 i))) :=
    (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])
  unfold privateMac privateMacKey
  simp only [bind_assoc,pure_bind]
  exact avoids_bind protectedMessage (hk 0) fun _ =>
    avoids_bind protectedMessage (hk 1) fun _ => avoids_pure _ _
theorem avoids_privateNonce (message : Message) (hne : message ≠ protectedMessage) :
    Avoids protectedMessage (privateNonce message) := by
  unfold privateNonce
  apply avoids_bind protectedMessage
  · exact (allQueriesSatisfy_query_iff _ _).mpr (by simpa [nonceQuery] using hne)
  · intro _
    exact avoids_pure _ _
attribute [local aesop safe apply] avoids_pure avoids_bind avoids_map avoids_foldlM avoids_mapM
  avoids_publicHash avoids_privatePair avoids_privateMac avoids_privateNonce
macro "nonce_safe" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))
theorem avoids_shortHash (input : HashInput) : Avoids protectedMessage (shortHash input) := by
  unfold shortHash; nonce_safe
attribute [local aesop safe apply] avoids_shortHash
theorem avoids_projHash (high : Bool) (input : HashInput) : Avoids protectedMessage (projHash high input) := by
  unfold projHash; nonce_safe
attribute [local aesop safe apply] avoids_projHash
theorem avoids_mask (level index : Nat) : Avoids protectedMessage (mask level index) := by
  unfold mask pairedMask; nonce_safe
attribute [local aesop safe apply] avoids_mask
theorem avoids_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids protectedMessage (chain lay tree leaf i start count value) := by
  unfold chain; nonce_safe
attribute [local aesop safe apply] avoids_chain
/-- Witness stack: the paired top chain (projected halves). -/
theorem avoids_topChain (leaf i start count : Nat) (value : Digest) :
    Avoids protectedMessage (topChain leaf i start count value) := by
  unfold topChain; nonce_safe
attribute [local aesop safe apply] avoids_topChain
theorem avoids_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Avoids protectedMessage (leafHash lay tree leaf ends) := by
  unfold leafHash; nonce_safe
attribute [local aesop safe apply] avoids_leafHash
theorem avoids_nodeHash (tag lay tree heap : Nat) (left right : Digest) :
    Avoids protectedMessage (nodeHash tag lay tree heap left right) := by
  unfold nodeHash; nonce_safe
attribute [local aesop safe apply] avoids_nodeHash
theorem avoids_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Avoids protectedMessage (buildLeaf lay tree leaf digits signatureOnly) := by
  unfold buildLeaf; nonce_safe
attribute [local aesop safe apply] avoids_buildLeaf
theorem avoids_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) :
    Avoids protectedMessage (buildLevel tag lay tree h level nodes) := by
  unfold buildLevel; nonce_safe
attribute [local aesop safe apply] avoids_buildLevel
theorem avoids_buildLevels (tag lay tree h : Nat) (leaves : List Digest) :
    Avoids protectedMessage (buildLevels tag lay tree h leaves) := by
  unfold buildLevels; nonce_safe
attribute [local aesop safe apply] avoids_buildLevels
theorem av_topNodeHashN_q (heap n : Nat) (left right : Digest) :
    Avoids protectedMessage (topNodeHashN heap n left right) := by
  unfold topNodeHashN; nonce_safe
attribute [local aesop safe apply] av_topNodeHashN_q
theorem av_topNonceSearch_q (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Avoids protectedMessage (topNonceSearch h heap left right fuel n)
  | 0, n => by unfold topNonceSearch; nonce_safe
  | fuel+1, n => by
      have ih := av_topNonceSearch_q (h := h) (heap := heap) (left := left) (right := right) fuel (n+1)
      unfold topNonceSearch; nonce_safe
attribute [local aesop safe apply] av_topNonceSearch_q
theorem av_topNodeAt_q (h heap : Nat) (left right : Digest) :
    Avoids protectedMessage (topNodeAt h heap left right) := by
  unfold topNodeAt; apply av_topNonceSearch_q
attribute [local aesop safe apply] av_topNodeAt_q
theorem av_buildTopLevel_q (level : Nat) (nodes : List Digest) :
    Avoids protectedMessage (buildTopLevel level nodes) := by
  unfold buildTopLevel; nonce_safe
attribute [local aesop safe apply] av_buildTopLevel_q
theorem av_buildTopLevels_q (leaves : List Digest) :
    Avoids protectedMessage (buildTopLevels leaves) := by
  unfold buildTopLevels; nonce_safe
attribute [local aesop safe apply] av_buildTopLevels_q
theorem avoids_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    Avoids protectedMessage (buildTree lay tree selected digits) := by
  unfold buildTree; nonce_safe
attribute [local aesop safe apply] avoids_buildTree
theorem avoids_topPairsFrom (first start : Nat) (init : List Digest) : Avoids protectedMessage (topPairsFrom first start init) := by
  unfold topPairsFrom topSeedPair; nonce_safe
attribute [local aesop safe apply] avoids_topPairsFrom
theorem avoids_topCoefs (leaf : Nat) : Avoids protectedMessage (topCoefs leaf) := by
  unfold topCoefs; nonce_safe
attribute [local aesop safe apply] avoids_topCoefs
theorem avoids_topCoefsK (f : Nat) (carry : Digest) : Avoids protectedMessage (topCoefsK f carry) := by
  unfold topCoefsK; nonce_safe
attribute [local aesop safe apply] avoids_topCoefsK
theorem avoids_buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) : Avoids protectedMessage (buildLeafTopC leaf coefs digits signatureOnly) := by
  unfold buildLeafTopC; nonce_safe
attribute [local aesop safe apply] avoids_buildLeafTopC
theorem avoids_topFamilyCoefs (leaf : Nat) (cc : List Digest × Digest) : Avoids protectedMessage (topFamilyCoefs leaf cc) := by
  unfold topFamilyCoefs; nonce_safe
attribute [local aesop safe apply] avoids_topFamilyCoefs
theorem avoids_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) : Avoids protectedMessage (topTreeStep st leaf) := by
  unfold topTreeStep; nonce_safe
attribute [local aesop safe apply] avoids_topTreeStep
theorem avoids_buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Avoids protectedMessage (buildLeafTop leaf digits signatureOnly) := by
  unfold buildLeafTop; nonce_safe
attribute [local aesop safe apply] avoids_buildLeafTop
theorem avoids_buildTopTree : Avoids protectedMessage buildTopTree := by
  unfold buildTopTree; nonce_safe
attribute [local aesop safe apply] avoids_buildTopTree
theorem avoids_keygenPayload : Avoids protectedMessage keygenPayload := by
  unfold keygenPayload maskedLevel pairedMask; nonce_safe
attribute [local aesop safe apply] avoids_keygenPayload
theorem avoids_keygen : Avoids protectedMessage keygen := by
  unfold keygen; nonce_safe
theorem avoids_counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    Avoids protectedMessage (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; nonce_safe
  | succ fuel ih => unfold counterSearch; nonce_safe
attribute [local aesop safe apply] avoids_counterSearch
theorem avoids_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Avoids protectedMessage (digest rho message counter) := by
  unfold digest; nonce_safe
attribute [local aesop safe apply] avoids_digest
theorem avoids_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids protectedMessage (digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; nonce_safe
  | succ fuel ih => unfold digestSearch; nonce_safe
attribute [local aesop safe apply] avoids_digestSearch
theorem avoids_ftsLeaf (index coord leaf : Nat) (secret : Digest) :
    Avoids protectedMessage (ftsLeaf index coord leaf secret) := by
  unfold ftsLeaf; nonce_safe
attribute [local aesop safe apply] avoids_ftsLeaf
theorem avoids_buildFts (index coord : Nat) : Avoids protectedMessage (buildFts index coord) := by
  unfold buildFts; nonce_safe
attribute [local aesop safe apply] avoids_buildFts
theorem avoids_forestPk (index : Nat) (roots : List Digest) :
    Avoids protectedMessage (forestPk index roots) := by
  unfold forestPk; nonce_safe
attribute [local aesop safe apply] avoids_forestPk
theorem avoids_topPath (cache : T3.Cache) (leaf : Nat) : Avoids protectedMessage (topPath cache leaf) := by
  unfold topPath; nonce_safe
attribute [local aesop safe apply] avoids_topPath
theorem avoids_signTop (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    Avoids protectedMessage (signTop cache leaf digits) := by
  unfold signTop; nonce_safe
attribute [local aesop safe apply] avoids_signTop
theorem avoids_signLayers (cache : T3.Cache) (index n : Nat) (message : Digest) :
    Avoids protectedMessage (signLayers cache index n message) := by
  induction n generalizing message with
  | zero => unfold signLayers; nonce_safe
  | succ n ih => unfold signLayers; nonce_safe
attribute [local aesop safe apply] avoids_signLayers
theorem avoids_signPayload (cache : T3.Cache) (message : Message) (hne : message ≠ protectedMessage) :
    Avoids protectedMessage (signPayload cache message) := by
  unfold signPayload; nonce_safe
attribute [local aesop safe apply] avoids_signPayload
theorem avoids_sign (cache : T3.Cache) (message : Message) (hne : message ≠ protectedMessage) :
    Avoids protectedMessage (sign cache message) := by
  unfold sign; nonce_safe
theorem query_preserves (input : T3.Spec.Domain) (hinput : input ≠ nonceQuery protectedMessage)
    (state : LazyPrivate.State) (result : T3.Spec.Range input × LazyPrivate.State)
    (hresult : result ∈ support (run (liftM (T3.Spec.query input)) state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) := by
  cases input with
  | inl input =>
      rw [run_query] at hresult
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,support_pure,
        Set.mem_singleton_iff] at hresult
      obtain ⟨_,_,rfl⟩ := hresult
      rfl
  | inr coordinate =>
      have hne : (.inr (.inl protectedMessage) : Coordinate) ≠ coordinate := by
        intro he
        apply hinput
        exact congrArg Sum.inr he.symm
      exact (privateHash_preserves_other coordinate _ hne state result hresult).1
theorem run_preserves {α : Type} (program : M α) (hprogram : Avoids protectedMessage program)
    (state : LazyPrivate.State) (result : α × LazyPrivate.State) (hresult : result ∈ support (run program state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [run_pure,support_pure,Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hprogram
      rw [run_bind,mem_support_bind_iff] at hresult
      obtain ⟨intermediate,hstep,htailResult⟩ := hresult
      exact (ih intermediate.1 (htail intermediate.1) intermediate.2 htailResult).trans
        (query_preserves protectedMessage input hinput state intermediate hstep)
theorem keygen_nonce_fresh (result : (Digest × T3.Cache) × LazyPrivate.State)
    (hresult : result ∈ support (run keygen (∅,∅))) :
    result.2.1 (.inr (.inl protectedMessage))=none :=
  run_preserves protectedMessage keygen (avoids_keygen protectedMessage) (∅,∅) result hresult
theorem sign_preserves_other_nonce (cache : T3.Cache) (message : Message) (hne : message ≠ protectedMessage)
    (state : LazyPrivate.State) (result : Option Signature × LazyPrivate.State)
    (hresult : result ∈ support (run (sign cache message) state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) :=
  run_preserves protectedMessage _ (avoids_sign protectedMessage cache message hne) state result hresult
def otherRequest (input : LazyPrivate.Interaction.Domain) : Prop :=
  match input with
  | .inl _ => True
  | .inr request => request.message ≠ protectedMessage
theorem interaction_avoids {α : Type} (program : OracleComp LazyPrivate.Interaction α)
    (hprogram : AllQueriesSatisfy program (otherRequest protectedMessage)) :
    Avoids protectedMessage (simulateQ LazyPrivate.interactionSource program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact avoids_pure _ _
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hprogram
      rw [simulateQ_bind,simulateQ_spec_query]
      apply avoids_bind protectedMessage _ (fun answer => ih answer (htail answer))
      cases input with
      | inl input =>
          exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])
      | inr request => exact avoids_sign protectedMessage request.cache request.message hinput
theorem interaction_nonce_preserved {α : Type} (program : OracleComp LazyPrivate.Interaction α)
    (hprogram : AllQueriesSatisfy program (otherRequest protectedMessage))
    (state : LazyPrivate.State) (result : α × LazyPrivate.State)
    (hresult : result ∈ support (run (simulateQ LazyPrivate.interactionSource program) state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) :=
  run_preserves protectedMessage _ (interaction_avoids protectedMessage program hprogram) state result hresult
theorem keygen_interaction_nonce_fresh {α : Type}
    (program : Digest → T3.Cache → OracleComp LazyPrivate.Interaction α)
    (hprogram : ∀ publicKey cache,AllQueriesSatisfy (program publicKey cache) (otherRequest protectedMessage))
    (result : α × LazyPrivate.State)
    (hresult : result ∈ support (run (do
      let generated ← keygen
      simulateQ LazyPrivate.interactionSource (program generated.1 generated.2)) (∅,∅))) :
    result.2.1 (.inr (.inl protectedMessage))=none := by
  apply run_preserves protectedMessage _ _ (∅,∅) result hresult
  exact avoids_bind protectedMessage (avoids_keygen protectedMessage) fun generated =>
    interaction_avoids protectedMessage _ (hprogram generated.1 generated.2)
end SigGolfCandidate.T3.Security.NonceFreshness
end
section
namespace SigGolfCandidate.T3.Security.SourceQueries
open OracleComp OracleSpec
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable (P : T3.Spec.Domain → Prop)
theorem pure_allowed {α : Type} (value : α) : AllQueriesSatisfy (pure value : M α) P :=
  allQueriesSatisfy_pure _ _
theorem bind_allowed {α β : Type} {program : M α} {next : α → M β}
    (hp : AllQueriesSatisfy program P) (hn : ∀ value, AllQueriesSatisfy (next value) P) :
    AllQueriesSatisfy (program >>= next) P := allQueriesSatisfy_bind hp hn
theorem map_allowed {α β : Type} (f : α → β) {program : M α}
    (hp : AllQueriesSatisfy program P) : AllQueriesSatisfy (f <$> program) P := by
  rw [map_eq_bind_pure_comp]
  exact bind_allowed P hp fun _ => pure_allowed _ _
theorem foldlM_allowed {α β : Type} (items : List β) (f : α → β → M α)
    (h : ∀ a b,AllQueriesSatisfy (f a b) P) (initial : α) :
    AllQueriesSatisfy (items.foldlM f initial) P := by
  induction items generalizing initial with
  | nil => exact pure_allowed _ _
  | cons a items ih =>
      rw [List.foldlM_cons]
      exact bind_allowed P (h initial a) ih
theorem mapM_allowed {α β : Type} (items : List α) (f : α → M β)
    (h : ∀ a,AllQueriesSatisfy (f a) P) : AllQueriesSatisfy (items.mapM f) P := by
  induction items with
  | nil => exact pure_allowed _ _
  | cons a items ih =>
      rw [List.mapM_cons]
      exact bind_allowed P (h a) fun _ => bind_allowed P ih fun _ => pure_allowed _ _
theorem map_allowed_iff {α β : Type} (f : α → β) (program : M α) :
    AllQueriesSatisfy (f <$> program) P ↔ AllQueriesSatisfy program P := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [map_pure,allQueriesSatisfy_pure]
  | query_bind input next ih =>
      simp only [map_bind,allQueriesSatisfy_query_bind_iff,ih]
theorem countWith_allowed {α : Type} (weight : T3.Spec.Domain → Nat) (program : M α)
    (h : AllQueriesSatisfy program P) : AllQueriesSatisfy (Cost.countWith weight program) P := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [Cost.countWith_pure]
      exact pure_allowed _ _
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      rw [Cost.countWith_bind,Cost.countWith_query]
      apply bind_allowed P
      · exact map_allowed P _ ((allQueriesSatisfy_query_iff _ _).mpr hinput)
      · intro result
        exact map_allowed P _ (ih result.1 (htail result.1))
variable (hpublic : ∀ input, P (.inl (.inr input)))
variable (hpair : ∀ tweak, P (.inr (.inl tweak)))
variable (hnonce : ∀ message, P (.inr (.inr (.inl message))))
include hpublic hpair hnonce
omit hpair hnonce in
theorem publicHash_allowed (input : HashInput) : AllQueriesSatisfy (publicHash input) P :=
  (allQueriesSatisfy_query_iff _ _).mpr (hpublic _)
omit hpublic hnonce in
theorem privatePair_allowed (tag lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair tag lay tree position index) P := by
  unfold privatePair
  apply bind_allowed P
  · exact (allQueriesSatisfy_query_iff _ _).mpr (hpair _)
  · intro _; exact pure_allowed _ _
omit hpublic hpair in
theorem privateNonce_allowed (message : Message) : AllQueriesSatisfy (privateNonce message) P := by
  unfold privateNonce
  apply bind_allowed P
  · exact (allQueriesSatisfy_query_iff _ _).mpr (hnonce _)
  · intro _; exact pure_allowed _ _
attribute [local aesop safe apply] pure_allowed bind_allowed map_allowed foldlM_allowed mapM_allowed
  publicHash_allowed privatePair_allowed privateNonce_allowed
macro "source_queries" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))
omit hpair hnonce in
theorem shortHash_allowed (input : HashInput) : AllQueriesSatisfy (shortHash input) P := by
  unfold shortHash; source_queries
attribute [local aesop safe apply] shortHash_allowed
omit hpair hnonce in
theorem projHash_allowed (high : Bool) (input : HashInput) : AllQueriesSatisfy (projHash high input) P := by
  unfold projHash; source_queries
attribute [local aesop safe apply] projHash_allowed
omit hpublic hnonce in
theorem mask_allowed (level index : Nat) : AllQueriesSatisfy (mask level index) P := by
  unfold mask pairedMask; source_queries
attribute [local aesop safe apply] mask_allowed
theorem chain_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) P := by
  unfold chain; source_queries
attribute [local aesop safe apply] chain_allowed
/-- Witness stack: the paired top chain (projected halves). -/
theorem topChain_allowed (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (topChain leaf i start count value) P := by
  unfold topChain; source_queries
attribute [local aesop safe apply] topChain_allowed
theorem leafHash_allowed (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) P := by
  unfold leafHash; source_queries
attribute [local aesop safe apply] leafHash_allowed
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) P := by
  unfold nodeHash; source_queries
attribute [local aesop safe apply] nodeHash_allowed
theorem buildLeaf_allowed (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) P := by
  unfold buildLeaf; source_queries
attribute [local aesop safe apply] buildLeaf_allowed
theorem buildLevel_allowed (tag lay tree h level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) P := by
  unfold buildLevel; source_queries
attribute [local aesop safe apply] buildLevel_allowed
theorem buildLevels_allowed (tag lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) P := by
  unfold buildLevels; source_queries
attribute [local aesop safe apply] buildLevels_allowed
theorem pq_topNodeHashN_q (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeHashN heap n left right) P := by
  unfold topNodeHashN; source_queries
attribute [local aesop safe apply] pq_topNodeHashN_q
theorem pq_topNonceSearch_q (h heap : Nat) (left right : Digest) :
    ∀ fuel n, AllQueriesSatisfy (topNonceSearch h heap left right fuel n) P
  | 0, n => by unfold topNonceSearch; source_queries
  | fuel+1, n => by
      have ih := pq_topNonceSearch_q (h := h) (heap := heap) (left := left) (right := right) fuel (n+1)
      unfold topNonceSearch; source_queries
attribute [local aesop safe apply] pq_topNonceSearch_q
theorem pq_topNodeAt_q (h heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeAt h heap left right) P := by
  unfold topNodeAt; apply pq_topNonceSearch_q <;> assumption
attribute [local aesop safe apply] pq_topNodeAt_q
theorem pq_buildTopLevel_q (level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (buildTopLevel level nodes) P := by
  unfold buildTopLevel; source_queries
attribute [local aesop safe apply] pq_buildTopLevel_q
theorem pq_buildTopLevels_q (leaves : List Digest) :
    AllQueriesSatisfy (buildTopLevels leaves) P := by
  unfold buildTopLevels; source_queries
attribute [local aesop safe apply] pq_buildTopLevels_q
theorem buildTree_allowed (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) P := by
  unfold buildTree; source_queries
attribute [local aesop safe apply] buildTree_allowed
theorem topPairsFrom_allowed (first start : Nat) (init : List Digest) : AllQueriesSatisfy (topPairsFrom first start init) P := by
  unfold topPairsFrom topSeedPair; source_queries
attribute [local aesop safe apply] topPairsFrom_allowed
theorem topCoefs_allowed (leaf : Nat) : AllQueriesSatisfy (topCoefs leaf) P := by
  unfold topCoefs; source_queries
attribute [local aesop safe apply] topCoefs_allowed
theorem topCoefsK_allowed (f : Nat) (carry : Digest) : AllQueriesSatisfy (topCoefsK f carry) P := by
  unfold topCoefsK; source_queries
attribute [local aesop safe apply] topCoefsK_allowed
theorem buildLeafTopC_allowed (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) : AllQueriesSatisfy (buildLeafTopC leaf coefs digits signatureOnly) P := by
  unfold buildLeafTopC; source_queries
attribute [local aesop safe apply] buildLeafTopC_allowed
theorem topFamilyCoefs_allowed (leaf : Nat) (cc : List Digest × Digest) : AllQueriesSatisfy (topFamilyCoefs leaf cc) P := by
  unfold topFamilyCoefs; source_queries
attribute [local aesop safe apply] topFamilyCoefs_allowed
theorem topTreeStep_allowed (st : List Digest × List Digest × Digest) (leaf : Nat) : AllQueriesSatisfy (topTreeStep st leaf) P := by
  unfold topTreeStep; source_queries
attribute [local aesop safe apply] topTreeStep_allowed
theorem buildLeafTop_allowed (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTop leaf digits signatureOnly) P := by
  unfold buildLeafTop; source_queries
attribute [local aesop safe apply] buildLeafTop_allowed
theorem buildTopTree_allowed : AllQueriesSatisfy buildTopTree P := by
  unfold buildTopTree; source_queries
attribute [local aesop safe apply] buildTopTree_allowed
theorem keygenPayload_allowed : AllQueriesSatisfy keygenPayload P := by
  unfold keygenPayload maskedLevel pairedMask; source_queries
theorem counterSearch_allowed (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) P := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; source_queries
  | succ fuel ih => unfold counterSearch; source_queries
attribute [local aesop safe apply] counterSearch_allowed
omit hpair hnonce in
theorem digest_allowed (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) P := by
  unfold digest; source_queries
attribute [local aesop safe apply] digest_allowed
theorem digestSearch_allowed (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (digestSearch rho message counter fuel) P := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; source_queries
  | succ fuel ih => unfold digestSearch; source_queries
attribute [local aesop safe apply] digestSearch_allowed
theorem ftsLeaf_allowed (index coord leaf : Nat) (secret : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf secret) P := by
  unfold ftsLeaf; source_queries
attribute [local aesop safe apply] ftsLeaf_allowed
theorem buildFts_allowed (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) P := by
  unfold buildFts; source_queries
attribute [local aesop safe apply] buildFts_allowed
theorem forestPk_allowed (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (forestPk index roots) P := by
  unfold forestPk; source_queries
attribute [local aesop safe apply] forestPk_allowed
theorem topPath_allowed (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) P := by
  unfold topPath; source_queries
attribute [local aesop safe apply] topPath_allowed
theorem signTop_allowed (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) P := by
  unfold signTop; source_queries
attribute [local aesop safe apply] signTop_allowed
theorem signLayers_allowed (cache : T3.Cache) (index n : Nat) (message : Digest) :
    AllQueriesSatisfy (signLayers cache index n message) P := by
  induction n generalizing message with
  | zero => unfold signLayers; source_queries
  | succ n ih => unfold signLayers; source_queries
attribute [local aesop safe apply] signLayers_allowed
theorem signPayload_allowed (cache : T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) P := by
  unfold signPayload; source_queries
omit hpublic hnonce in
theorem privateMac_allowed (region : Region) : AllQueriesSatisfy (privateMac region) P := by
  have hk (i : Nat) : AllQueriesSatisfy (privateHash (.inl (header 14 0 0 0 i))) P :=
    (allQueriesSatisfy_query_iff _ _).mpr (hpair _)
  unfold privateMac privateMacKey
  simp only [bind_assoc,pure_bind]
  exact bind_allowed P (hk 0) fun _ => bind_allowed P (hk 1) fun _ => pure_allowed _ _
theorem keygen_allowed (hmac : ∀ region,P (.inr (.inr (.inr region)))) :
    AllQueriesSatisfy keygen P := by
  unfold keygen
  apply bind_allowed P (keygenPayload_allowed P hpublic hpair hnonce)
  intro generated
  apply bind_allowed P (privateMac_allowed P hpair _)
  intro _; exact pure_allowed _ _
theorem sign_allowed (hmac : ∀ region,P (.inr (.inr (.inr region))))
    (cache : T3.Cache) (message : Message) : AllQueriesSatisfy (sign cache message) P := by
  unfold sign
  apply bind_allowed P (privateMac_allowed P hpair _)
  intro tag
  split_ifs
  · exact pure_allowed _ _
  · exact signPayload_allowed P hpublic hpair hnonce cache message
end SigGolfCandidate.T3.Security.SourceQueries
namespace SigGolfCandidate.T3.Security.SourceReplay
open OracleComp OracleSpec LazyPrivate
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def IsHash : T3.Spec.Domain → Prop
  | .inl (.inl _) => False
  | _ => True
abbrev HashOnly {α : Type} (program : M α) := AllQueriesSatisfy program IsHash
theorem sign_hashOnly (cache : T3.Cache) (message : Message) : HashOnly (sign cache message) :=
  SourceQueries.sign_allowed IsHash (fun _ => trivial) (fun _ => trivial)
    (fun _ => trivial) (fun _ => trivial) cache message
theorem keygen_hashOnly : HashOnly keygen :=
  SourceQueries.keygen_allowed IsHash (fun _ => trivial) (fun _ => trivial)
    (fun _ => trivial) (fun _ => trivial)
theorem signingRecord_hashOnly (cache : T3.Cache) (message : Message) :
    HashOnly (signingRecord cache message) := by
  apply (SourceQueries.map_allowed_iff IsHash Prod.fst _).mp
  rw [signingRecord_erasure]
  exact sign_hashOnly cache message
abbrev Extends (before after : LazyPrivate.State) : Prop := before ≤ after
def known (state : LazyPrivate.State) : QueryCache T3.Spec
  | .inl (.inl _) => none
  | .inl (.inr input) => state.2 input
  | .inr coordinate => state.1 coordinate
theorem known_mono (before after : LazyPrivate.State) (hle : Extends before after) :
    known before ≤ known after := by
  intro input answer h
  cases input with
  | inl input =>
      cases input with
      | inl input => cases h
      | inr input => exact hle.2 h
  | inr coordinate => exact hle.1 h
theorem query_extends (input : T3.Spec.Domain) (before : LazyPrivate.State)
    (result : T3.Spec.Range input × LazyPrivate.State)
    (h : result ∈ support (run (liftM (T3.Spec.query input)) before)) : Extends before result.2 := by
  rw [run_query] at h
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at h
      obtain ⟨step,hstep,rfl⟩ := h
      refine ⟨le_rfl,?_⟩
      cases input with
      | inl input =>
          change step ∈ support ((fun answer => (answer,before.2)) <$>
            ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl input)) : ProbComp _)) at hstep
          rw [support_map] at hstep
          obtain ⟨_,_,rfl⟩ := hstep
          exact le_rfl
      | inr input => exact QueryImpl.withCaching_cache_le _ input before.2 step hstep
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at h
      obtain ⟨step,hstep,rfl⟩ := h
      exact ⟨QueryImpl.withCaching_cache_le _ coordinate before.1 step hstep,le_rfl⟩
theorem run_extends {α : Type} (program : M α) (before : LazyPrivate.State)
    (result : α × LazyPrivate.State) (h : result ∈ support (run program before)) :
    Extends before result.2 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      rw [run_pure,mem_support_pure_iff] at h
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [run_bind,mem_support_bind_iff] at h
      obtain ⟨step,hstep,htail⟩ := h
      exact (query_extends input before step hstep).trans (ih step.1 step.2 htail)
theorem hash_query_caches (input : T3.Spec.Domain) (hhash : IsHash input)
    (before : LazyPrivate.State) (result : T3.Spec.Range input × LazyPrivate.State)
    (h : result ∈ support (run (liftM (T3.Spec.query input)) before)) :
    known result.2 input=some result.1 := by
  cases input with
  | inl input =>
      cases input with
      | inl input => exact False.elim hhash
      | inr input =>
          rw [run_query] at h
          simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
            support_pure,Set.mem_singleton_iff] at h
          obtain ⟨step,hstep,rfl⟩ := h
          exact DeterministicSigning.query_caches input before.2 step hstep
  | inr coordinate =>
      rw [run_query] at h
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at h
      obtain ⟨step,hstep,rfl⟩ := h
      exact DeterministicSigning.query_caches coordinate before.1 step hstep
inductive Resolves (state : LazyPrivate.State) {α : Type} : M α → α → Prop
  | pure (value : α) : Resolves state (pure value) value
  | query (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
      (hanswer : known state input=some answer) (next : T3.Spec.Range input → M α)
      (value : α) (tail : Resolves state (next answer) value) :
      Resolves state (liftM (T3.Spec.query input) >>= next) value
theorem Resolves.mono {α : Type} {before after : LazyPrivate.State}
    {program : M α} {value : α} (h : Resolves before program value) (hle : Extends before after) :
    Resolves after program value := by
  induction h with
  | pure value => exact .pure value
  | query input answer hanswer next value _ ih =>
      exact .query input answer (known_mono before after hle hanswer) next value ih
theorem resolves_of_run {α : Type} (program : M α) (hhash : HashOnly program)
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (h : result ∈ support (run program before)) : Resolves result.2 program result.1 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      rw [run_pure,mem_support_pure_iff] at h
      subst result
      exact .pure value
  | query_bind input next ih =>
      obtain ⟨hinput,hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hhash
      rw [run_bind,mem_support_bind_iff] at h
      obtain ⟨step,hstep,htail⟩ := h
      have hle := run_extends (next step.1) step.2 result htail
      exact .query input step.1
        (known_mono step.2 result.2 hle (hash_query_caches input hinput before step hstep))
        next result.1 (ih step.1 (hn step.1) step.2 htail)
theorem known_query_run (state : LazyPrivate.State) (input : T3.Spec.Domain)
    (answer : T3.Spec.Range input) (h : known state input=some answer) :
    run (liftM (T3.Spec.query input)) state=pure (answer,state) := by
  rw [run_query]
  cases input with
  | inl input =>
      cases input with
      | inl input => cases h
      | inr input =>
          change (do
            let result ← (randomOracle (spec := SphincsSecurity.HashSpec) input).run state.2
            pure (result.1,(state.1,result.2)))=pure (answer,state)
          simp only [known] at h
          rw [QueryImpl.withCaching_run_some _ h,pure_bind]
  | inr coordinate =>
      change (do
        let result ← (randomOracle (spec := Coordinate →ₒ HashOutput) coordinate).run state.1
        pure (result.1,(result.2,state.2)))=pure (answer,state)
      simp only [known] at h
      rw [QueryImpl.withCaching_run_some _ h,pure_bind]
theorem Resolves.run_eq_pure {α : Type} {state : LazyPrivate.State}
    {program : M α} {value : α} (h : Resolves state program value) :
    run program state=Pure.pure (value,state) := by
  induction h with
  | pure value => exact run_pure _ _
  | query input answer hanswer next value _ ih =>
      rw [run_bind,known_query_run state input answer hanswer,pure_bind,ih]
theorem replay_run {α : Type} (program : M α) (hhash : HashOnly program)
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (h : result ∈ support (run program before)) (after : LazyPrivate.State)
    (hle : Extends result.2 after) : run program after=pure (result.1,after) :=
  ((resolves_of_run program hhash before result h).mono hle).run_eq_pure
theorem sign_replay (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : Option Signature × LazyPrivate.State)
    (h : result ∈ support (run (sign cache message) before)) (after : LazyPrivate.State)
    (hle : Extends result.2 after) : run (sign cache message) after=pure (result.1,after) :=
  replay_run _ (sign_hashOnly cache message) before result h after hle
theorem signingRecord_replay (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (h : result ∈ support (run (signingRecord cache message) before)) (after : LazyPrivate.State)
    (hle : Extends result.2 after) :
    run (signingRecord cache message) after=pure (result.1,after) :=
  replay_run _ (signingRecord_hashOnly cache message) before result h after hle
theorem counted_sign_replay (weight : T3.Spec.Domain → Nat) (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : (Option Signature × Nat) × LazyPrivate.State)
    (h : result ∈ support (run (Cost.countWith weight (sign cache message)) before))
    (after : LazyPrivate.State) (hle : Extends result.2 after) :
    run (Cost.countWith weight (sign cache message)) after=pure (result.1,after) :=
  replay_run _ (SourceQueries.countWith_allowed IsHash weight _ (sign_hashOnly cache message))
    before result h after hle
theorem sign_after_intervening {α : Type} (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : Option Signature × LazyPrivate.State)
    (h : result ∈ support (run (sign cache message) before)) (intervening : M α)
    (later : α × LazyPrivate.State) (hlater : later ∈ support (run intervening result.2)) :
    run (sign cache message) later.2=pure (result.1,later.2) :=
  sign_replay cache message before result h later.2 (run_extends intervening result.2 later hlater)
end SigGolfCandidate.T3.Security.SourceReplay
end
end
-- ==== merged from T3_FullCache_RequestRun ====
section

namespace SigGolfCandidate.T3.Security.RequestHop
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State : Type}
abbrev Public (State : Type) := QueryImpl SphincsSecurity.OracleWorld (StateT State ProbComp)
abbrev Signer (State : Type) := Request → StateT State ProbComp (Option Signature)
noncomputable def run {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    ProbComp ((α × QueryLog Requests) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state
theorem run_pure {α : Type} (world : Public State) (signer : Signer State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl
theorem run_public {α : Type} (world : Public State) (signer : Signer State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl
theorem run_request {α : Type} (world : Public State) (signer : Signer State)
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl
theorem erasure {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2
theorem probEvent_bind_le_add_bind {α β γ : Type} (mx : ProbComp α)
    (left right : α → ProbComp β) (badRun : α → ProbComp γ)
    (event : β → Prop) (bad : γ → Prop)
    (hle : ∀ value ∈ support mx,Pr[event | left value] ≤
      Pr[event | right value]+Pr[bad | badRun value]) :
    Pr[event | mx >>= left] ≤ Pr[event | mx >>= right]+Pr[bad | mx >>= badRun] := by
  simp only [probEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hv : value ∈ support mx
  · rw [← mul_add]
    exact mul_le_mul' le_rfl (hle value hv)
  · simp [probOutput_eq_zero_of_not_mem_support hv]
def BadIn (bad : Request → Prop) (limit : Nat) (log : QueryLog Requests) : Prop :=
  ∃ entry ∈ log.take limit,bad entry.1
theorem identical_until_bad {α β : Type} (world : Public State) (bad : Request → Prop)
    (left right : Signer State) (hagree : ∀ request,¬bad request → left request=right request)
    (program : OracleComp LazyPrivate.Interaction α) :
    ∀ (limit : Nat) (state : State) (cont : ((α × QueryLog Requests) × State) → ProbComp β)
      (event : β → Prop),
      (∀ result,limit < result.1.2.length → Pr[event | cont result]=0) →
      Pr[event | run world left program state >>= cont] ≤
        Pr[event | run world right program state >>= cont]+
          Pr[fun result => BadIn bad limit result.1.2 | run world right program state] := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      intro limit state cont event _
      exact le_self_add
  | query_bind input next ih =>
      intro limit state cont event hlong
      cases input with
      | inl input =>
          rw [run_public,run_public,bind_assoc,bind_assoc]
          apply probEvent_bind_le_add_bind
          intro result _
          exact ih result.1 limit result.2 cont event hlong
      | inr request =>
          by_cases hbad : bad request
          · cases limit with
            | zero =>
                refine le_trans (le_of_eq ?_) zero_le
                rw [probEvent_eq_zero_iff]
                intro value hv
                rw [run_request,bind_assoc,mem_support_bind_iff] at hv
                obtain ⟨head,_,hv⟩ := hv
                rw [bind_map_left,mem_support_bind_iff] at hv
                obtain ⟨tail,_,hv⟩ := hv
                have hz := hlong ((tail.1.1,⟨request,head.1⟩::tail.1.2),tail.2) (by simp)
                rw [probEvent_eq_zero_iff] at hz
                exact hz value hv
            | succ limit =>
                have hone : Pr[fun result => BadIn bad (limit+1) result.1.2 |
                    run world right (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state]=1 := by
                  rw [probEvent_eq_one_iff]
                  refine ⟨by simp,?_⟩
                  intro result hr
                  rw [run_request,mem_support_bind_iff] at hr
                  obtain ⟨head,_,hr⟩ := hr
                  rw [support_map] at hr
                  obtain ⟨tail,_,rfl⟩ := hr
                  exact ⟨⟨request,head.1⟩,by simp,hbad⟩
                exact probEvent_le_one.trans (hone.symm.le.trans le_add_self)
          · rw [run_request,run_request,hagree request hbad,bind_assoc,bind_assoc]
            apply probEvent_bind_le_add_bind
            intro head _
            rw [bind_map_left,bind_map_left,probEvent_map]
            refine (ih head.1 (limit-1) head.2 _ event (fun result hr => hlong _ (by simp;omega))).trans
              (add_le_add le_rfl (probEvent_mono fun result _ hr => ?_))
            obtain ⟨entry,he,hbadEntry⟩ := hr
            cases limit with
            | zero => simp at he
            | succ limit =>
                simp only [Nat.add_sub_cancel] at he
                exact ⟨entry,by simp [he],hbadEntry⟩
end SigGolfCandidate.T3.Security.RequestHop
end
-- ==== merged from T3_FullCache_Polynomial ====
section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
set_option backward.isDefEq.respectTransparency false
theorem macPrime_eq_mersenne : macPrime = mersenne 61 := rfl
theorem macPrime_prime : macPrime.Prime := by
  rw [macPrime_eq_mersenne]
  exact lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)
instance : Fact macPrime.Prime := ⟨macPrime_prime⟩
theorem polyMac_lt (k : Nat) (cs : List Nat) : polyMac k cs < macPrime ∨ cs = [] := by
  rcases List.eq_nil_or_concat cs with h | ⟨cs', c, rfl⟩
  · exact Or.inr h
  · left
    unfold polyMac
    rw [List.concat_eq_append, List.foldl_append]
    exact Nat.mod_lt _ (by decide)
theorem polyMac_lt' (k : Nat) (cs : List Nat) : polyMac k cs < 2 ^ 61 := by
  rcases polyMac_lt k cs with h | h
  · have : macPrime < 2 ^ 61 := by decide
    omega
  · subst h; simp [polyMac]
open Polynomial
noncomputable def macPoly (cs : List Nat) : (ZMod macPrime)[X] :=
  cs.foldl (fun q c => (q + C (c : ZMod macPrime)) * X) 0
theorem macPoly_concat (cs : List Nat) (c : Nat) :
    macPoly (cs ++ [c]) = (macPoly cs + C (c : ZMod macPrime)) * X := by
  simp [macPoly, List.foldl_append]
theorem polyMac_cast_aux (k : Nat) (cs : List Nat) (acc : Nat) (q : (ZMod macPrime)[X])
    (h : (acc : ZMod macPrime) = q.eval (k : ZMod macPrime)) :
    ((cs.foldl (fun acc c => (acc + c) * k % macPrime) acc : Nat) : ZMod macPrime) =
      (cs.foldl (fun q c => (q + C (c : ZMod macPrime)) * X) q).eval (k : ZMod macPrime) := by
  induction cs generalizing acc q with
  | nil => simpa using h
  | cons c cs ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [ZMod.natCast_mod]
      simp [h]
theorem polyMac_cast (k : Nat) (cs : List Nat) :
    ((polyMac k cs : Nat) : ZMod macPrime) = (macPoly cs).eval (k : ZMod macPrime) :=
  polyMac_cast_aux k cs 0 0 (by simp)
theorem natDegree_macPoly_le (cs : List Nat) : (macPoly cs).natDegree ≤ cs.length := by
  induction cs using List.reverseRecOn with
  | nil => simp [macPoly]
  | append_singleton cs c ih =>
      rw [macPoly_concat, List.length_append, List.length_singleton]
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_X]
      refine Nat.add_le_add_right ((natDegree_add_le _ _).trans ?_) 1
      rw [natDegree_C]
      omega
theorem eq_of_macPoly_sub_eq_C : ∀ (xs ys : List Nat), xs.length = ys.length →
    (∀ x ∈ xs, x < macPrime) → (∀ y ∈ ys, y < macPrime) → ∀ d : ZMod macPrime, macPoly xs - macPoly ys = C d → xs = ys := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
      intro ys hlen _ _ _ _
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton xs x ih =>
      intro ys hlen hx hy d h
      rcases List.eq_nil_or_concat ys with hnil | ⟨ys', y, rfl⟩
      · subst hnil; simp at hlen
      rw [List.concat_eq_append] at hlen hy h ⊢
      have hlen' : xs.length = ys'.length := by simpa using hlen
      rw [macPoly_concat, macPoly_concat, ← sub_mul] at h
      have hd : d = 0 := by
        have := congrArg (Polynomial.eval 0) h
        simpa using this.symm
      subst hd
      have hzero : macPoly xs + C (x : ZMod macPrime) - (macPoly ys' + C (y : ZMod macPrime)) = 0 := by
        have := h
        rw [C_0, mul_eq_zero] at this
        exact this.resolve_right X_ne_zero
      have hsub : macPoly xs - macPoly ys' = C ((y : ZMod macPrime) - (x : ZMod macPrime)) := by
        rw [C_sub]
        linear_combination hzero
      have hxs := ih ys' hlen' (fun a ha => hx a (by simp [ha])) (fun a ha => hy a (by simp [ha])) _ hsub
      subst hxs
      rw [sub_self] at hsub
      have hc : (y : ZMod macPrime) - (x : ZMod macPrime) = 0 := by
        have := congrArg (fun q : (ZMod macPrime)[X] => q.coeff 0) hsub
        simpa using this.symm
      have hxy : (x : ZMod macPrime) = (y : ZMod macPrime) := (sub_eq_zero.mp hc).symm
      have hx' := hx x (by simp)
      have hy' := hy y (by simp)
      have : x = y := by
        have := (ZMod.natCast_eq_natCast_iff' x y macPrime).mp hxy
        rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at this
      rw [this]
theorem card_polyMac_diff_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (d : ZMod macPrime) :
    ((Finset.range (2 ^ 61)).filter fun k => ((polyMac k ys : Nat) : ZMod macPrime) - ((polyMac k xs : Nat) : ZMod macPrime) = d).card
      ≤ xs.length + 1 := by
  set D : (ZMod macPrime)[X] := macPoly ys - macPoly xs - C d with hD
  have hD0 : D ≠ 0 := by
    intro h0
    apply hne
    have : macPoly ys - macPoly xs = C d := by rw [hD] at h0; exact sub_eq_zero.mp h0
    exact (eq_of_macPoly_sub_eq_C ys xs hlen.symm hy hx d this).symm
  have hdeg : D.natDegree ≤ xs.length := by
    rw [hD]
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_C, max_eq_left (Nat.zero_le _)]
    refine (natDegree_sub_le _ _).trans ?_
    exact max_le (hlen ▸ natDegree_macPoly_le ys) (natDegree_macPoly_le xs)
  have hsub : ((Finset.range (2 ^ 61)).filter fun k =>
        ((polyMac k ys : Nat) : ZMod macPrime) - ((polyMac k xs : Nat) : ZMod macPrime) = d) ⊆
      insert macPrime (D.roots.toFinset.image ZMod.val) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk61, hkd⟩ := hk
    by_cases hkp : k = macPrime
    · rw [hkp]; exact Finset.mem_insert_self _ _
    · have hlt : k < macPrime := by
        have : macPrime + 1 = 2 ^ 61 := by decide
        omega
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(k : ZMod macPrime), ?_, ZMod.val_natCast_of_lt hlt⟩)
      rw [Multiset.mem_toFinset, mem_roots hD0, IsRoot.def, hD]
      simp only [eval_sub, eval_C]
      rw [← polyMac_cast, ← polyMac_cast, hkd, sub_self]
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ?_ 1
  refine Finset.card_image_le.trans ?_
  refine (Multiset.toFinset_card_le _).trans ?_
  exact (card_roots' D).trans hdeg
theorem answerOfWords_toNat (w0 w1 w2 w3 : BitVec 64) :
    (answerOfWords w0 w1 w2 w3).toNat =
      w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat := by
  change (BitVec.ofNat 256 (w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat)).toNat = _
  rw [BitVec.toNat_ofNat]
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  apply Nat.mod_eq_of_lt
  show _ < 2 ^ 256
  omega
theorem extract_answerOfWords (w0 w1 w2 w3 : BitVec 64) :
    (answerOfWords w0 w1 w2 w3).extractLsb' 0 64 = w0 ∧
    (answerOfWords w0 w1 w2 w3).extractLsb' 64 64 = w1 ∧
    (answerOfWords w0 w1 w2 w3).extractLsb' 128 64 = w2 ∧
    (answerOfWords w0 w1 w2 w3).extractLsb' 192 64 = w3 := by
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, answerOfWords_toNat, Nat.shiftRight_eq_div_pow]
    omega
theorem answerOfWords_extract (a : HashOutput) :
    answerOfWords (a.extractLsb' 0 64) (a.extractLsb' 64 64) (a.extractLsb' 128 64) (a.extractLsb' 192 64) = a := by
  apply BitVec.eq_of_toNat_eq
  rw [answerOfWords_toNat]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have : a.toNat < 2 ^ 256 := a.isLt
  omega
noncomputable def tagResidue (delta : BitVec 64) : ZMod macPrime :=
  if delta.toNat < 2 ^ 63 then (delta.toNat : ZMod macPrime)
  else (delta.toNat : ZMod macPrime) - ((2 ^ 64 : Nat) : ZMod macPrime)
theorem residue_of_tag_eq (ux uy : Nat) (hx : ux < 2 ^ 61) (hy : uy < 2 ^ 61) (t t' : BitVec 64)
    (h : BitVec.ofNat 64 uy + (t - BitVec.ofNat 64 ux) = t') :
    ((uy : Nat) : ZMod macPrime) - ((ux : Nat) : ZMod macPrime) = tagResidue (t' - t) := by
  have hd : BitVec.ofNat 64 uy - BitVec.ofNat 64 ux = t' - t := by rw [← h]; ring
  have hn := congrArg BitVec.toNat hd
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show ux < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show uy < 2 ^ 64 by omega)] at hn
  unfold tagResidue
  have hlt := (t' - t).isLt
  generalize (t' - t).toNat = dn at hn hlt ⊢
  split
  · have hu : uy = ux + dn := by omega
    rw [hu]; push_cast; ring
  · have hu : uy + 2 ^ 64 = ux + dn := by omega
    have h2 : ((uy + 2 ^ 64 : Nat) : ZMod macPrime) = ((ux + dn : Nat) : ZMod macPrime) := by rw [hu]
    push_cast at h2 ⊢
    linear_combination h2
theorem polyMac_lt_pow (k : Nat) (cs : List Nat) : polyMac k cs < 2 ^ 61 := polyMac_lt' k cs
theorem card_lowWords_le (B : Finset Nat) :
    (Finset.univ.filter fun w : BitVec 64 => w.toNat % 2 ^ 61 ∈ B).card ≤ 8 * B.card := by
  classical
  have hsub : (Finset.univ.filter fun w : BitVec 64 => w.toNat % 2 ^ 61 ∈ B) ⊆
      (B ×ˢ Finset.range 8).image fun p : Nat × Nat => BitVec.ofNat 64 (p.1 + 2 ^ 61 * p.2) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    refine Finset.mem_image.mpr ⟨(w.toNat % 2 ^ 61, w.toNat / 2 ^ 61), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range]
      have := w.isLt
      exact ⟨hw.2, by omega⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      have := w.isLt
      omega
  calc _ ≤ ((B ×ˢ Finset.range 8).image fun p : Nat × Nat => BitVec.ofNat 64 (p.1 + 2 ^ 61 * p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (B ×ˢ Finset.range 8).card := Finset.card_image_le
    _ = 8 * B.card := by rw [Finset.card_product, Finset.card_range, Nat.mul_comm]
noncomputable def badKeys (xs ys : List Nat) (d : ZMod macPrime) : Finset Nat :=
  (Finset.range (2 ^ 61)).filter fun k =>
    ((polyMac k ys : Nat) : ZMod macPrime) - ((polyMac k xs : Nat) : ZMod macPrime) = d
noncomputable def badWords (xs ys : List Nat) (d : ZMod macPrime) : Finset (BitVec 64) :=
  Finset.univ.filter fun w : BitVec 64 => w.toNat % 2 ^ 61 ∈ badKeys xs ys d
theorem card_badWords_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (d : ZMod macPrime) :
    (badWords xs ys d).card ≤ 8 * (xs.length + 1) :=
  (card_lowWords_le (badKeys xs ys d)).trans
    (Nat.mul_le_mul_left 8 (card_polyMac_diff_le xs ys hlen hne hx hy d))
theorem chunks32_lt (data : HashInput) : ∀ c ∈ chunks32 data, c < 2 ^ 32 := by
  induction data using chunks32.induct with
  | case1 b0 b1 b2 b3 rest ih =>
      intro c hc
      rw [chunks32] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
        omega
      · exact ih c hc
  | case2 data hne =>
      intro c hc
      rw [chunks32.eq_2 _ hne] at hc
      simp at hc
theorem chunks32_length (data : HashInput) : (chunks32 data).length = data.length / 4 := by
  induction data using chunks32.induct with
  | case1 b0 b1 b2 b3 rest ih =>
      rw [chunks32, List.length_cons, ih]
      simp only [List.length_cons]
      omega
  | case2 data hne =>
      rw [chunks32.eq_2 _ hne, List.length_nil]
      match data, hne with
      | [], _ => rfl
      | [_], _ => simp
      | [_, _], _ => simp
      | [_, _, _], _ => simp
      | a :: b :: c :: d :: r, hne => exact (hne a b c d r rfl).elim
theorem chunks32_injective : ∀ (a b : HashInput), a.length = b.length → 4 ∣ a.length →
    chunks32 a = chunks32 b → a = b := by
  intro a
  induction a using chunks32.induct with
  | case1 a0 a1 a2 a3 rest ih =>
      intro b hlen hdvd h
      match b, hlen with
      | b0 :: b1 :: b2 :: b3 :: rb, hlen =>
          rw [chunks32, chunks32, List.cons.injEq] at h
          obtain ⟨hc, hr⟩ := h
          have hrest := ih rb (by simpa using hlen) (by
            have : (a0 :: a1 :: a2 :: a3 :: rest).length = rest.length + 4 := by simp
            rw [this] at hdvd
            exact (Nat.dvd_add_left (dvd_refl 4)).mp hdvd) hr
          have h0 := a0.toNat_lt; have h1 := a1.toNat_lt; have h2 := a2.toNat_lt; have h3 := a3.toNat_lt
          have g0 := b0.toNat_lt; have g1 := b1.toNat_lt; have g2 := b2.toNat_lt; have g3 := b3.toNat_lt
          have e0 : a0 = b0 := UInt8.toNat_inj.mp (by omega)
          have e1 : a1 = b1 := UInt8.toNat_inj.mp (by omega)
          have e2 : a2 = b2 := UInt8.toNat_inj.mp (by omega)
          have e3 : a3 = b3 := UInt8.toNat_inj.mp (by omega)
          rw [e0, e1, e2, e3, hrest]
      | [], hlen => simp at hlen
      | [_], hlen => simp at hlen
      | [_, _], hlen => simp at hlen
      | [_, _, _], hlen => simp at hlen
  | case2 a hne =>
      intro b hlen hdvd _
      have ha : a = [] := by
        match a, hne, hdvd with
        | [], _, _ => rfl
        | [_], _, hd => simp at hd
        | [_, _], _, hd => simp at hd
        | [_, _, _], _, hd => simp at hd
        | x :: y :: z :: w :: r, hne, _ => exact (hne x y z w r rfl).elim
      subst ha
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
theorem chunks32_lt_macPrime (data : HashInput) : ∀ c ∈ chunks32 data, c < macPrime := fun c hc =>
  (chunks32_lt data c hc).trans (by decide)
end SphincsSecurity
end
-- ==== merged from T3_FullCache_Fields ====
section

namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal
open SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def macLowWord (key : MacKey) (j : Fin 4) : BitVec 64 :=
  (key ⟨j.val / 2, by omega⟩).extractLsb' (128 * (j.val % 2)) 64
def mkMacKey (lows pads : Fin 4 → BitVec 64) : MacKey := fun i =>
  answerOfWords (lows ⟨2 * i.val, by omega⟩) (pads ⟨2 * i.val, by omega⟩)
    (lows ⟨2 * i.val + 1, by omega⟩) (pads ⟨2 * i.val + 1, by omega⟩)
theorem fin4_cases (j : Fin 4) : ∃ i : Fin 2, j = ⟨2 * i.val, by omega⟩ ∨ j = ⟨2 * i.val + 1, by omega⟩ := by
  refine ⟨⟨j.val / 2, by omega⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · left; apply Fin.ext; simp only; omega
  · right; apply Fin.ext; simp only; omega
theorem macLowWord_mk (lows pads : Fin 4 → BitVec 64) (j : Fin 4) : macLowWord (mkMacKey lows pads) j = lows j := by
  obtain ⟨hA, _, hC, _⟩ := extract_answerOfWords (lows ⟨2 * (j.val / 2), by omega⟩) (pads ⟨2 * (j.val / 2), by omega⟩)
    (lows ⟨2 * (j.val / 2) + 1, by omega⟩) (pads ⟨2 * (j.val / 2) + 1, by omega⟩)
  unfold macLowWord mkMacKey
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · simp only [h, Nat.mul_zero]
    rw [hA]; congr 1; apply Fin.ext; simp only; omega
  · simp only [h, Nat.mul_one]
    rw [hC]; congr 1; apply Fin.ext; simp only; omega
theorem macPadWord_mk (lows pads : Fin 4 → BitVec 64) (j : Fin 4) : macPadWord (mkMacKey lows pads) j = pads j := by
  obtain ⟨_, hB, _, hD⟩ := extract_answerOfWords (lows ⟨2 * (j.val / 2), by omega⟩) (pads ⟨2 * (j.val / 2), by omega⟩)
    (lows ⟨2 * (j.val / 2) + 1, by omega⟩) (pads ⟨2 * (j.val / 2) + 1, by omega⟩)
  unfold macPadWord mkMacKey
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · simp only [h, Nat.mul_zero, Nat.zero_add]
    rw [hB]; congr 1; apply Fin.ext; simp only; omega
  · simp only [h, Nat.mul_one]
    rw [hD]; congr 1; apply Fin.ext; simp only; omega
theorem mkMacKey_words (key : MacKey) : mkMacKey (macLowWord key) (macPadWord key) = key := by
  funext i
  unfold mkMacKey macLowWord macPadWord
  have h0 : (2 * i.val) / 2 = i.val := by omega
  have h1 : (2 * i.val + 1) / 2 = i.val := by omega
  have m0 : (2 * i.val) % 2 = 0 := by omega
  have m1 : (2 * i.val + 1) % 2 = 1 := by omega
  simp only [h0, h1, m0, m1, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Fin.eta]
  exact answerOfWords_extract (key i)
theorem macKeyWord_eq (key : MacKey) (j : Fin 4) : macKeyWord key j = (macLowWord key j).toNat % 2 ^ 61 := by
  unfold macKeyWord macLowWord
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have : (key ⟨j.val / 2, by omega⟩).toNat < 2 ^ 256 := (key ⟨j.val / 2, by omega⟩).isLt
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp only [h, Nat.mul_zero, Nat.mul_one] <;> omega
theorem macKeyWord_mk (lows pads : Fin 4 → BitVec 64) (j : Fin 4) :
    macKeyWord (mkMacKey lows pads) j = (lows j).toNat % 2 ^ 61 := by
  rw [macKeyWord_eq, macLowWord_mk]
end SiggolfT3Mac4
end
-- ==== merged from T3_FullCache_Retag ====
section

namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def macTagOf (key : MacKey) (chunks : List Nat) : MacTag :=
  fun j => BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks) + macPadWord key j
theorem macTag_eq (key : MacKey) (data : HashInput) : macTag key data = macTagOf key (chunks32 data) := rfl
def retag (key : MacKey) (chunks : List Nat) (tag : MacTag) : MacKey :=
  mkMacKey (macLowWord key) fun j => tag j - BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks)
theorem macLowWord_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) :
    macLowWord (retag key chunks tag) = macLowWord key := by
  funext j; exact macLowWord_mk _ _ j
theorem macKeyWord_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) (j : Fin 4) :
    macKeyWord (retag key chunks tag) j = macKeyWord key j := by
  rw [macKeyWord_eq, macKeyWord_eq, macLowWord_retag]
theorem macTagOf_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) :
    macTagOf (retag key chunks tag) chunks = tag := by
  funext j
  unfold macTagOf
  rw [macKeyWord_retag]
  unfold retag
  rw [macPadWord_mk]
  exact add_sub_cancel _ _
theorem retag_macTagOf (key : MacKey) (chunks : List Nat) : retag key chunks (macTagOf key chunks) = key := by
  unfold retag
  have hp : (fun j => macTagOf key chunks j - BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks)) =
      macPadWord key := by
    funext j; unfold macTagOf; exact add_sub_cancel_left _ _
  rw [hp, mkMacKey_words]
theorem retag_mk_eq (h : MacKey) (chunks : List Nat) (pads : MacTag) :
    retag (mkMacKey (macLowWord h) pads) chunks (macTagOf h chunks) = h := by
  have hl : macLowWord (mkMacKey (macLowWord h) pads) = macLowWord h := by
    funext j; exact macLowWord_mk _ _ j
  have hk : ∀ j, macKeyWord (mkMacKey (macLowWord h) pads) j = macKeyWord h j := by
    intro j; rw [macKeyWord_eq, macKeyWord_eq, hl]
  have := retag_macTagOf h chunks
  unfold retag at this ⊢
  rw [hl]
  simp only [hk]
  exact this
theorem evalSPMF_uniformSample_bind_retag [SampleableType MacTag] [SampleableType MacKey] (chunks : List Nat) :
    𝒮[do let tag ← $ᵗ MacTag; let key ← $ᵗ MacKey; pure (retag key chunks tag)] = 𝒮[$ᵗ MacKey] := by
  classical
  refine evalSPMF_ext fun h => ?_
  rw [probOutput_uniformSample MacKey h, probOutput_bind_eq_sum_fintype]
  have hinner : ∀ tag : MacTag,
      Pr[= h | (do let key ← $ᵗ MacKey; pure (retag key chunks tag))]
        = (if tag = macTagOf h chunks then
            (Fintype.card MacTag : ℝ≥0∞) * (Fintype.card MacKey : ℝ≥0∞)⁻¹ else 0) := by
    intro tag
    rw [bind_pure_comp, probOutput_map_eq_sum_fintype_ite]
    simp only [probOutput_uniformSample MacKey]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.filter fun key : MacKey => h = retag key chunks tag).card : ℝ≥0∞)
          = if tag = macTagOf h chunks then (Fintype.card MacTag : ℝ≥0∞) else 0 := by
      by_cases ht : tag = macTagOf h chunks
      · have hset : (Finset.univ.filter fun key : MacKey => h = retag key chunks tag)
            = Finset.univ.image (fun pads : MacTag => mkMacKey (macLowWord h) pads) := by
          ext key
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hk
            refine ⟨macPadWord key, ?_⟩
            have hl : macLowWord h = macLowWord key := by rw [hk, macLowWord_retag]
            rw [hl, mkMacKey_words]
          · rintro ⟨pads, rfl⟩
            rw [ht]
            exact (retag_mk_eq h chunks pads).symm
        rw [hset, Finset.card_image_of_injective _ (fun p q hpq => by
              funext j
              have := congrArg (fun k => macPadWord k j) hpq
              simpa only [macPadWord_mk] using this),
            Finset.card_univ, if_pos ht]
      · rw [if_neg ht, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro key - rfl
        exact ht (macTagOf_retag key chunks tag).symm
    rw [hcard, ite_mul, zero_mul]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (macTagOf h chunks), if_pos (Finset.mem_univ _),
      probOutput_uniformSample MacTag, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]
end SiggolfT3Mac4
end
-- ==== merged from T3_FullCache_Region ====
section

section
namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
theorem mem_badWords_of_tag_eq (xs ys : List Nat) (key : MacKey) (tag tag' : MacTag) (j : Fin 4)
    (h : macTagOf (retag key xs tag) ys j = tag' j) :
    macLowWord key j ∈ badWords xs ys (tagResidue (tag' j - tag j)) := by
  unfold macTagOf at h
  rw [macKeyWord_retag] at h
  unfold retag at h
  rw [macPadWord_mk] at h
  have hres := residue_of_tag_eq _ _ (polyMac_lt_pow _ xs) (polyMac_lt_pow _ ys) _ _ h
  unfold badWords badKeys
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, ← macKeyWord_eq]
  refine ⟨Finset.mem_univ _, ?_, hres⟩
  rw [macKeyWord_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 61)
theorem card_retag_bad_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (tag tag' : MacTag) :
    Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'}
      ≤ (8 * (xs.length + 1)) ^ 4 * Fintype.card MacTag := by
  let f : {key : MacKey // macTagOf (retag key xs tag) ys = tag'} →
      ((j : Fin 4) → {w : BitVec 64 // w ∈ badWords xs ys (tagResidue (tag' j - tag j))}) × MacTag :=
    fun key => (fun j => ⟨macLowWord key.1 j,
      mem_badWords_of_tag_eq xs ys key.1 tag tag' j (congrFun key.2 j)⟩, macPadWord key.1)
  have hf : Function.Injective f := by
    intro k1 k2 h
    apply Subtype.ext
    have h1 : macLowWord k1.1 = macLowWord k2.1 := by
      funext j
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) j)
    have h2 : macPadWord k1.1 = macPadWord k2.1 := congrArg Prod.snd h
    rw [← mkMacKey_words k1.1, ← mkMacKey_words k2.1, h1, h2]
  refine (Fintype.card_le_of_injective f hf).trans ?_
  rw [Fintype.card_prod, Fintype.card_pi]
  refine Nat.mul_le_mul_right _ ?_
  simp only [Fintype.card_coe]
  refine (Finset.prod_le_prod' fun j _ => card_badWords_le xs ys hlen hne hx hy _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
theorem card_tagWord : Fintype.card (BitVec 64) = 2 ^ 64 := Fintype.card_bitVec 64
theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := Fintype.card_bitVec hashOutputBits
theorem card_macTag : Fintype.card MacTag = (2 ^ 64) ^ 4 := by
  rw [Fintype.card_fun, card_tagWord, Fintype.card_fin]
theorem card_macKey : Fintype.card MacKey = (2 ^ 256) ^ 2 := by
  rw [Fintype.card_fun, card_hashOutput, Fintype.card_fin]
theorem probEvent_retag_bad_le [SampleableType MacKey] (xs ys : List Nat) (hlen : xs.length = ys.length)
    (hne : xs ≠ ys) (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime)
    (hL : xs.length + 1 ≤ 2 ^ 15) (tag tag' : MacTag) :
    Pr[fun key : MacKey => macTagOf (retag key xs tag) ys = tag' | $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype, card_macKey]
  have hc := card_retag_bad_le xs ys hlen hne hx hy tag tag'
  rw [card_macTag] at hc
  have hn : Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} ≤ 2 ^ 328 := by
    refine hc.trans ?_
    calc (8 * (xs.length + 1)) ^ 4 * (2 ^ 64) ^ 4 ≤ (8 * 2 ^ 15) ^ 4 * (2 ^ 64) ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hL) 4)
      _ = 2 ^ 328 := by norm_num
  have hcast : ((Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} : ℕ) : ℝ≥0∞)
      ≤ (2 ^ 328 : ℝ≥0∞) := by exact_mod_cast hn
  refine ENNReal.div_le_of_le_mul (hcast.trans (le_of_eq ?_))
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show ((2 : ENNReal) ^ 256) ^ 2 = (2 : ENNReal) ^ 184 * 2 ^ 328 by
      rw [← pow_mul, ← pow_add],
    ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
end SiggolfT3Mac4
end
section
namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
abbrev Region := Fin 131040 → UInt8
def regionBytes (region : Region) : HashInput := List.ofFn region
def tagRegion (key : MacKey) (region : Region) : MacTag := macTag key (regionBytes region)
def tagBytes (tag : MacTag) : HashInput := (List.ofFn tag).flatMap (bytesLE 8)
theorem regionBytes_length (region : Region) : (regionBytes region).length = 131040 := by
  simp only [regionBytes, List.length_ofFn]
theorem regionBytes_injective : Function.Injective regionBytes := by
  intro a b h
  unfold regionBytes at h
  exact List.ofFn_injective h
theorem regionChunks_length (region : Region) : (chunks32 (regionBytes region)).length = 32760 := by
  rw [chunks32_length, regionBytes_length]
theorem regionChunks_injective : Function.Injective (fun region : Region => chunks32 (regionBytes region)) := by
  intro a b h
  apply regionBytes_injective
  exact chunks32_injective _ _ ((regionBytes_length a).trans (regionBytes_length b).symm)
    (by rw [regionBytes_length]; decide) h
theorem tagBytes_length (tag : MacTag) : (tagBytes tag).length = 32 := by
  simp [tagBytes, List.length_flatMap, bytesLE_length]
theorem tagBytes_injective : Function.Injective tagBytes := by
  intro a b h
  exact flatMap_bytesLE_ofFn_injective h
theorem fullCache_length (key : MacKey) (region : Region) :
    (regionBytes region ++ tagBytes (tagRegion key region)).length = 131072 := by
  rw [List.length_append, regionBytes_length, tagBytes_length]
theorem probEvent_region_bad_le [SampleableType MacKey] (published candidate : Region)
    (hne : candidate ≠ published) (tag tag' : MacTag) :
    Pr[fun key : MacKey => tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate = tag' |
      $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  exact probEvent_retag_bad_le (chunks32 (regionBytes published)) (chunks32 (regionBytes candidate))
    ((regionChunks_length published).trans (regionChunks_length candidate).symm)
    (fun h => hne (regionChunks_injective h).symm)
    (chunks32_lt_macPrime _) (chunks32_lt_macPrime _)
    (by rw [regionChunks_length]; decide) tag tag'
theorem probEvent_region_bad_bytes_le [SampleableType MacKey] (published candidate : Region)
    (hne : candidate ≠ published) (tag tag' : MacTag) :
    Pr[fun key : MacKey => tagBytes (tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate) = tagBytes tag' |
      $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  have he : (fun key : MacKey => tagBytes (tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate) = tagBytes tag') =
      (fun key : MacKey => tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate = tag') := by
    funext key
    exact propext ⟨fun h => tagBytes_injective h, fun h => congrArg tagBytes h⟩
  rw [he]
  exact probEvent_region_bad_le published candidate hne tag tag'
end SiggolfT3Mac4
end
end
-- ==== merged from T3_FullCache_KeySplit ====
section

section
namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
abbrev LowKeys := Fin 4 → BitVec 61
abbrev UnusedBits := Fin 4 → BitVec 3
abbrev Components := LowKeys × (MacTag × UnusedBits)
def joinLow (key : BitVec 61) (unused : BitVec 3) : BitVec 64 :=
  BitVec.ofNat 64 (key.toNat + 2 ^ 61 * unused.toNat)
theorem joinLow_low (key : BitVec 61) (unused : BitVec 3) :
    (joinLow key unused).extractLsb' 0 61 = key := by
  apply BitVec.eq_of_toNat_eq
  simp only [joinLow, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hk := key.isLt; have hu := unused.isLt
  omega
theorem joinLow_high (key : BitVec 61) (unused : BitVec 3) :
    (joinLow key unused).extractLsb' 61 3 = unused := by
  apply BitVec.eq_of_toNat_eq
  simp only [joinLow, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hk := key.isLt; have hu := unused.isLt
  omega
theorem joinLow_parts (word : BitVec 64) :
    joinLow (word.extractLsb' 0 61) (word.extractLsb' 61 3) = word := by
  apply BitVec.eq_of_toNat_eq
  simp only [joinLow, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hw := word.isLt
  omega
def components (key : MacKey) : Components :=
  (fun j => (macLowWord key j).extractLsb' 0 61,
   macPadWord key, fun j => (macLowWord key j).extractLsb' 61 3)
def ofComponents (c : Components) : MacKey :=
  mkMacKey (fun j => joinLow (c.1 j) (c.2.2 j)) c.2.1
theorem ofComponents_components (key : MacKey) : ofComponents (components key) = key := by
  simp only [ofComponents, components, joinLow_parts]
  exact mkMacKey_words key
theorem components_ofComponents (c : Components) : components (ofComponents c) = c := by
  apply Prod.ext
  · funext j
    simp only [components, ofComponents, macLowWord_mk, joinLow_low]
  · apply Prod.ext
    · funext j
      simp only [components, ofComponents, macPadWord_mk]
    · funext j
      simp only [components, ofComponents, macLowWord_mk, joinLow_high]
def componentsEquiv : MacKey ≃ Components where
  toFun := components
  invFun := ofComponents
  left_inv := ofComponents_components
  right_inv := components_ofComponents
theorem uniform_components [SampleableType MacKey] [SampleableType Components] :
    𝒮[components <$> ($ᵗ MacKey : ProbComp MacKey)] = 𝒮[($ᵗ Components : ProbComp Components)] :=
  evalSPMF_map_bijective_uniform_cross (α := MacKey) (β := Components) components componentsEquiv.bijective
theorem components_lowKeys (key : MacKey) (j : Fin 4) :
    ((components key).1 j).toNat = macKeyWord key j := by
  rw [macKeyWord_eq]
  simp [components, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem uniform_key_and_tag [SampleableType MacKey] [SampleableType MacTag] (chunks : List Nat) :
    𝒮[do let key ← $ᵗ MacKey; pure (macTagOf key chunks, key)] =
      𝒮[do let tag ← $ᵗ MacTag; let key ← $ᵗ MacKey; pure (tag, retag key chunks tag)] := by
  calc
    _ = (fun key : MacKey => (macTagOf key chunks, key)) <$> 𝒮[$ᵗ MacKey] := by
      rw [bind_pure_comp, evalSPMF_map]
    _ = (fun key : MacKey => (macTagOf key chunks, key)) <$>
        𝒮[do let tag ← $ᵗ MacTag; let key ← $ᵗ MacKey; pure (retag key chunks tag)] := by
      rw [evalSPMF_uniformSample_bind_retag chunks]
    _ = _ := by
      rw [← evalSPMF_map]
      apply congrArg evalSPMF
      simp only [map_bind, map_pure, macTagOf_retag]
theorem uniform_key_pads [SampleableType MacKey] [SampleableType (LowKeys × MacTag)] :
    𝒮[(fun key : MacKey => ((components key).1, (components key).2.1)) <$> ($ᵗ MacKey)] =
      𝒮[$ᵗ (LowKeys × MacTag)] := by
  let _ : SampleableType ((LowKeys × MacTag) × UnusedBits) := SampleableType.ofFintype _
  let e : MacKey ≃ ((LowKeys × MacTag) × UnusedBits) :=
    componentsEquiv.trans (Equiv.prodAssoc LowKeys MacTag UnusedBits).symm
  have h := evalSPMF_map_bijective_uniform_cross (α := MacKey)
    (β := ((LowKeys × MacTag) × UnusedBits)) e e.bijective
  have hm := congrArg (fun law : SPMF ((LowKeys × MacTag) × UnusedBits) => Prod.fst <$> law) h
  have hm' : 𝒮[(fun key : MacKey => ((components key).1, (components key).2.1)) <$> ($ᵗ MacKey)] =
      𝒮[Prod.fst <$> ($ᵗ ((LowKeys × MacTag) × UnusedBits))] := by
    simpa only [evalSPMF_map, Functor.map_map, Function.comp_def, e, Equiv.trans_apply,
      componentsEquiv, Equiv.coe_fn_mk, Equiv.prodAssoc_symm_apply] using hm
  exact hm'.trans evalSPMF_map_fst_uniformSample_prod
end SiggolfT3Mac4
end
section
namespace SiggolfT3Mac4
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option Elab.async false
structure Cache where
  region : Region
  tag : MacTag
structure Request (Message : Type) where
  message : Message
  cache : Cache
abbrev Requests (Message Signature : Type) := Request Message →ₒ Option Signature
abbrev Interaction (Message Signature : Type) := SphincsSecurity.OracleWorld + Requests Message Signature
end SiggolfT3Mac4
namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {Message Signature State : Type}
abbrev Public (State : Type) := QueryImpl SphincsSecurity.OracleWorld (StateT State ProbComp)
abbrev Signer (Message Signature State : Type) := Request Message → StateT State ProbComp (Option Signature)
noncomputable def run {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (program : OracleComp (Interaction Message Signature) α) (state : State) :
    ProbComp ((α × QueryLog (Requests Message Signature)) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state
theorem run_pure {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl
theorem run_public {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp (Interaction Message Signature) α)
    (state : State) :
    run world signer (liftM ((Interaction Message Signature).query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl
theorem run_request {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (request : Request Message) (next : Option Signature → OracleComp (Interaction Message Signature) α)
    (state : State) :
    run world signer (liftM ((Interaction Message Signature).query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl
theorem erasure {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (program : OracleComp (Interaction Message Signature) α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2
theorem probEvent_bind_le_add_bind {α β γ : Type} (mx : ProbComp α)
    (left right : α → ProbComp β) (badRun : α → ProbComp γ)
    (event : β → Prop) (bad : γ → Prop)
    (hle : ∀ value ∈ support mx,Pr[event | left value] ≤
      Pr[event | right value]+Pr[bad | badRun value]) :
    Pr[event | mx >>= left] ≤ Pr[event | mx >>= right]+Pr[bad | mx >>= badRun] := by
  simp only [probEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hv : value ∈ support mx
  · rw [← mul_add]
    exact mul_le_mul' le_rfl (hle value hv)
  · simp [probOutput_eq_zero_of_not_mem_support hv]
def BadIn (bad : Request Message → Prop) (limit : Nat) (log : QueryLog (Requests Message Signature)) : Prop :=
  ∃ entry ∈ log.take limit,bad entry.1
theorem identical_until_bad {α β : Type} (world : Public State) (bad : Request Message → Prop)
    (left right : Signer Message Signature State) (hagree : ∀ request,¬bad request → left request=right request)
    (program : OracleComp (Interaction Message Signature) α) :
    ∀ (limit : Nat) (state : State) (cont : ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β)
      (event : β → Prop),
      (∀ result,limit < result.1.2.length → Pr[event | cont result]=0) →
      Pr[event | run world left program state >>= cont] ≤
        Pr[event | run world right program state >>= cont]+
          Pr[fun result => BadIn bad limit result.1.2 | run world right program state] := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      intro limit state cont event _
      exact le_self_add
  | query_bind input next ih =>
      intro limit state cont event hlong
      cases input with
      | inl input =>
          rw [run_public,run_public,bind_assoc,bind_assoc]
          apply probEvent_bind_le_add_bind
          intro result _
          exact ih result.1 limit result.2 cont event hlong
      | inr request =>
          by_cases hbad : bad request
          · cases limit with
            | zero =>
                refine le_trans (le_of_eq ?_) zero_le
                rw [probEvent_eq_zero_iff]
                intro value hv
                rw [run_request,bind_assoc,mem_support_bind_iff] at hv
                obtain ⟨head,_,hv⟩ := hv
                rw [bind_map_left,mem_support_bind_iff] at hv
                obtain ⟨tail,_,hv⟩ := hv
                have hz := hlong ((tail.1.1,⟨request,head.1⟩::tail.1.2),tail.2) (by simp)
                rw [probEvent_eq_zero_iff] at hz
                exact hz value hv
            | succ limit =>
                have hone : Pr[fun result => BadIn bad (limit+1) result.1.2 |
                    run world right (liftM ((Interaction Message Signature).query (.inr request)) >>= next) state]=1 := by
                  rw [probEvent_eq_one_iff]
                  refine ⟨by simp,?_⟩
                  intro result hr
                  rw [run_request,mem_support_bind_iff] at hr
                  obtain ⟨head,_,hr⟩ := hr
                  rw [support_map] at hr
                  obtain ⟨tail,_,rfl⟩ := hr
                  exact ⟨⟨request,head.1⟩,by simp,hbad⟩
                exact probEvent_le_one.trans (hone.symm.le.trans le_add_self)
          · rw [run_request,run_request,hagree request hbad,bind_assoc,bind_assoc]
            apply probEvent_bind_le_add_bind
            intro head _
            rw [bind_map_left,bind_map_left,probEvent_map]
            refine (ih head.1 (limit-1) head.2 _ event (fun result hr => hlong _ (by simp;omega))).trans
              (add_le_add le_rfl (probEvent_mono fun result _ hr => ?_))
            obtain ⟨entry,he,hbadEntry⟩ := hr
            cases limit with
            | zero => simp at he
            | succ limit =>
                simp only [Nat.add_sub_cancel] at he
                exact ⟨entry,by simp [he],hbadEntry⟩
end SiggolfT3Mac4.Adaptive
end
section
namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {Message Signature : Type}
def retagRegion (key : MacKey) (published : Cache) : MacKey :=
  retag key (chunks32 (regionBytes published.region)) published.tag
def BadRequest (published : Cache) (key : MacKey) (request : Request Message) : Prop :=
  request.cache.region ≠ published.region ∧
    tagRegion (retagRegion key published) request.cache.region = request.cache.tag
theorem retagRegion_tag (key : MacKey) (published : Cache) :
    tagRegion (retagRegion key published) published.region = published.tag :=
  macTagOf_retag key (chunks32 (regionBytes published.region)) published.tag
theorem request_bad_bound [SampleableType MacKey] (published : Cache) (request : Request Message) :
    Pr[fun key : MacKey => BadRequest published key request | $ᵗ MacKey] ≤
      (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  by_cases hne : request.cache.region ≠ published.region
  · exact (probEvent_mono fun _ _ h => h.2).trans
      (probEvent_region_bad_le published.region request.cache.region hne published.tag request.cache.tag)
  · have hz : Pr[fun key : MacKey => BadRequest published key request | $ᵗ MacKey] = 0 := by
      apply probEvent_eq_zero_iff.mpr
      intro key _ h
      exact hne h.1
    rw [hz]
    exact zero_le
theorem list_events_bound {X Y : Type} (mx : ProbComp X) (entries : List Y)
    (event : Y → X → Prop) (cap : ENNReal) (hc : ∀ entry ∈ entries,Pr[event entry | mx] ≤ cap) :
    Pr[fun x => ∃ entry ∈ entries,event entry x | mx] ≤ entries.length*cap := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      calc
        _ = Pr[fun x => event entry x ∨ ∃ entry ∈ entries,event entry x | mx] := by
          apply probEvent_ext
          intro x _
          simp
        _ ≤ Pr[event entry | mx]+Pr[fun x => ∃ entry ∈ entries,event entry x | mx] :=
          probEvent_or_le _ _ _
        _ ≤ cap+entries.length*cap :=
          add_le_add (hc entry (by simp)) (ih fun entry he => hc entry (by simp [he]))
        _ = _ := by
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
          rw [add_comm]
theorem independent_log_bad_bound [SampleableType MacKey] {X : Type}
    (published : Cache) (mx : ProbComp X) (logOf : X → QueryLog (Requests Message Signature))
    (limit : Nat) :
    Pr[fun result : MacKey × X => BadIn (BadRequest published result.1) limit (logOf result.2) |
      ($ᵗ MacKey : ProbComp _) >>= fun key => (fun x => (key,x)) <$> mx] ≤
      limit*((2 : ENNReal)^184)⁻¹ := by
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  rw [probEvent_bind_bind_swap,probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' x,Pr[=x | mx]*(limit*((2 : ENNReal)^184)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul' le_rfl
      rw [bind_pure_comp,probEvent_map]
      exact (list_events_bound ($ᵗ MacKey) ((logOf x).take limit)
        (fun entry key => BadRequest published key entry.1) _
        (fun entry _ => request_bad_bound published entry.1)).trans
        (mul_le_mul' (by exact_mod_cast List.length_take_le _ _) le_rfl)
    _ = (∑' x,Pr[=x | mx])*(limit*((2 : ENNReal)^184)⁻¹) := ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_of_le_one_left zero_le tsum_probOutput_le_one
theorem lifetime_mac_charge [SampleableType MacKey] {X : Type}
    (published : Cache) (mx : ProbComp X) (logOf : X → QueryLog (Requests Message Signature)) :
    Pr[fun result : MacKey × X => BadIn (BadRequest published result.1) (2^32) (logOf result.2) |
      ($ᵗ MacKey : ProbComp _) >>= fun key => (fun x => (key,x)) <$> mx] ≤
      ((2 : ENNReal)^152)⁻¹ := by
  refine (independent_log_bad_bound published mx logOf (2^32)).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SiggolfT3Mac4.Adaptive
end
section
namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
variable {Message Signature State : Type}
noncomputable def realSigner (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (key : MacKey) : Signer Message Signature State :=
  fun request => do
    let _ ← overhead request
    if tagRegion key request.cache.region = request.cache.tag then payload request else pure none
noncomputable def idealSigner (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache) : Signer Message Signature State :=
  fun request => do
    let _ ← overhead request
    if request.cache = published then payload request else pure none
theorem signer_agrees (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache) (key : MacKey)
    (request : Request Message) (hgood : ¬BadRequest published key request) :
    realSigner overhead payload (retagRegion key published) request =
      idealSigner overhead payload published request := by
  unfold realSigner idealSigner
  apply congrArg (fun continuation => overhead request >>= continuation)
  funext answer
  by_cases hr : request.cache.region = published.region
  · rw [hr, retagRegion_tag]
    by_cases ht : published.tag = request.cache.tag
    · have he : request.cache = published := by
        cases request with
        | mk message cache => cases cache; cases published; cases hr; cases ht; rfl
      rw [if_pos ht, if_pos he]
    · have he : request.cache ≠ published := fun he => ht (congrArg Cache.tag he).symm
      rw [if_neg ht, if_neg he]
  · have ht : tagRegion (retagRegion key published) request.cache.region ≠ request.cache.tag :=
      fun ht => hgood ⟨hr,ht⟩
    have he : request.cache ≠ published := fun he => hr (congrArg Cache.region he)
    rw [if_neg ht,if_neg he]
theorem authentication_hop [SampleableType MacKey] {α β : Type}
    (world : Public State) (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache)
    (program : OracleComp (Interaction Message Signature) α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result, limit < result.1.2.length → Pr[event | cont result] = 0) :
    Pr[event | ($ᵗ MacKey : ProbComp _) >>= fun key =>
      run world (realSigner overhead payload (retagRegion key published)) program state >>= cont] ≤
      Pr[event | run world (idealSigner overhead payload published) program state >>= cont] +
        limit * ((2 : ENNReal)^184)⁻¹ := by
  have h := probEvent_bind_le_add_bind ($ᵗ MacKey : ProbComp _)
    (fun key => run world (realSigner overhead payload (retagRegion key published)) program state >>= cont)
    (fun _ => run world (idealSigner overhead payload published) program state >>= cont)
    (fun key => (fun result => (key,result)) <$> run world (idealSigner overhead payload published) program state)
    event (fun result => BadIn (BadRequest published result.1) limit result.2.1.2) (by
      intro key _
      rw [probEvent_map]
      exact identical_until_bad world (BadRequest published key) _ _
        (signer_agrees overhead payload published key) program limit state cont event hlong)
  rw [probEvent_bind_const] at h
  simp only [probFailure_eq_zero,tsub_zero,one_mul] at h
  exact h.trans (add_le_add le_rfl
    (independent_log_bad_bound published
      (run world (idealSigner overhead payload published) program state) (fun result => result.1.2) limit))
theorem lifetime_authentication_hop [SampleableType MacKey] {α β : Type}
    (world : Public State) (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache)
    (program : OracleComp (Interaction Message Signature) α) (state : State)
    (cont : ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result, 2^32 < result.1.2.length → Pr[event | cont result] = 0) :
    Pr[event | ($ᵗ MacKey : ProbComp _) >>= fun key =>
      run world (realSigner overhead payload (retagRegion key published)) program state >>= cont] ≤
      Pr[event | run world (idealSigner overhead payload published) program state >>= cont] +
        ((2 : ENNReal)^152)⁻¹ := by
  refine (authentication_hop world overhead payload published program (2^32) state cont event hlong).trans
    (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SiggolfT3Mac4.Adaptive
end
section
namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {Message Signature State : Type}
theorem publication_retag_law [SampleableType MacKey] [SampleableType MacTag] {β : Type}
    (region : Region) (next : Cache → MacKey → ProbComp β) :
    𝒮[do let key ← $ᵗ MacKey; next ⟨region, tagRegion key region⟩ key] =
      𝒮[do
        let tag ← $ᵗ MacTag
        let key ← $ᵗ MacKey
        next ⟨region, tag⟩ (retagRegion key ⟨region, tag⟩)] := by
  have hlaw := evalSPMF_uniformSample_bind_retag (chunks32 (regionBytes region))
  rw [evalSPMF_bind, ← hlaw, ← evalSPMF_bind]
  simp only [bind_assoc, pure_bind]
  apply congrArg evalSPMF
  apply bind_congr
  intro tag
  apply bind_congr
  intro key
  have ht := retagRegion_tag key (⟨region,tag⟩ : Cache)
  change tagRegion (retag key (chunks32 (regionBytes region)) tag) region = tag at ht
  rw [ht]
  rfl
theorem probEvent_bind_const_charge {X Y : Type} (mx : ProbComp X)
    (left right : X → ProbComp Y) (event : Y → Prop) (charge : ENNReal)
    (h : ∀ x, Pr[event | left x] ≤ Pr[event | right x] + charge) :
    Pr[event | mx >>= left] ≤ Pr[event | mx >>= right] + charge := by
  rw [probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' x,Pr[=x | mx] * (Pr[event | right x] + charge) :=
      ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = (∑' x,Pr[=x | mx] * Pr[event | right x]) + (∑' x,Pr[=x | mx]) * charge := by
      simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)
theorem published_authentication_hop [SampleableType MacKey] [SampleableType MacTag] {α β : Type}
    (region : Region) (world : Cache → Public State)
    (overhead : Cache → Request Message → StateT State ProbComp Unit)
    (payload : Cache → Signer Message Signature State)
    (program : Cache → OracleComp (Interaction Message Signature) α) (limit : Nat)
    (state : Cache → State)
    (cont : Cache → ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ published result,limit < result.1.2.length → Pr[event | cont published result] = 0) :
    Pr[event | do
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region,tagRegion key region⟩
      run (world published) (realSigner (overhead published) (payload published) key)
        (program published) (state published) >>= cont published] ≤
    Pr[event | do
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region,tag⟩
      run (world published) (idealSigner (overhead published) (payload published) published)
        (program published) (state published) >>= cont published] +
      limit * ((2 : ENNReal)^184)⁻¹ := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (publication_retag_law region
    (fun published key => run (world published)
      (realSigner (overhead published) (payload published) key)
      (program published) (state published) >>= cont published))]
  apply probEvent_bind_const_charge
  intro tag
  exact authentication_hop (world ⟨region,tag⟩) (overhead ⟨region,tag⟩) (payload ⟨region,tag⟩)
    ⟨region,tag⟩ (program ⟨region,tag⟩) limit (state ⟨region,tag⟩) (cont ⟨region,tag⟩) event
    (hlong ⟨region,tag⟩)
theorem published_lifetime_authentication_hop
    [SampleableType MacKey] [SampleableType MacTag] {α β : Type}
    (region : Region) (world : Cache → Public State)
    (overhead : Cache → Request Message → StateT State ProbComp Unit)
    (payload : Cache → Signer Message Signature State)
    (program : Cache → OracleComp (Interaction Message Signature) α)
    (state : Cache → State)
    (cont : Cache → ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ published result,2^32 < result.1.2.length → Pr[event | cont published result] = 0) :
    Pr[event | do
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region,tagRegion key region⟩
      run (world published) (realSigner (overhead published) (payload published) key)
        (program published) (state published) >>= cont published] ≤
    Pr[event | do
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region,tag⟩
      run (world published) (idealSigner (overhead published) (payload published) published)
        (program published) (state published) >>= cont published] +
      ((2 : ENNReal)^152)⁻¹ := by
  refine (published_authentication_hop region world overhead payload program (2^32) state cont event hlong).trans
    (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SiggolfT3Mac4.Adaptive
end
section
namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev T3Coordinate := SigGolfCandidate.T3.Coordinate
def keyTweak (i : Fin 2) : BitVec 128 := SigGolfCandidate.T3.header 14 0 0 0 i.val
def keyCoordinate (i : Fin 2) : T3Coordinate := .inl (keyTweak i)
theorem keyCoordinate_injective : Function.Injective keyCoordinate := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [keyCoordinate,keyTweak,SigGolfCandidate.T3.header,SigGolfCandidate.T3.packedNodeTag] at h ⊢
  all_goals have h' := congrArg BitVec.toNat h; norm_num at h'
theorem keyCoordinate_zero_ne_one : keyCoordinate 0 ≠ keyCoordinate 1 := by
  intro h
  have := keyCoordinate_injective h
  exact (by decide : (0 : Fin 2) ≠ 1) this
abbrev OtherCoordinate := {c : T3Coordinate // c ≠ keyCoordinate 0 ∧ c ≠ keyCoordinate 1}
abbrev OtherTable := OtherCoordinate → HashOutput
abbrev FullTable := T3Coordinate → HashOutput
noncomputable def joinTable (other : OtherTable) (key : MacKey) : FullTable := fun c => by
  classical
  exact if h0 : c = keyCoordinate 0 then key 0 else
    if h1 : c = keyCoordinate 1 then key 1 else other ⟨c,h0,h1⟩
theorem joinTable_key (other : OtherTable) (key : MacKey) (i : Fin 2) :
    joinTable other key (keyCoordinate i) = key i := by
  fin_cases i
  · simp [joinTable]
  · simp [joinTable,Ne.symm keyCoordinate_zero_ne_one]
theorem joinTable_other (other : OtherTable) (key : MacKey) (c : OtherCoordinate) :
    joinTable other key c = other c := by
  simp [joinTable,c.property.1,c.property.2]
noncomputable def tableEquiv : (OtherTable × MacKey) ≃ FullTable where
  toFun tables := joinTable tables.1 tables.2
  invFun table := ((fun c => table c),fun i => table (keyCoordinate i))
  left_inv tables := by
    apply Prod.ext
    · funext c; exact joinTable_other tables.1 tables.2 c
    · funext i; exact joinTable_key tables.1 tables.2 i
  right_inv table := by
    funext c
    classical
    unfold joinTable
    dsimp only
    split_ifs with h0 h1
    · rw [h0]
    · rw [h1]
    · rfl
theorem uniform_product {A B : Type} [Finite A] [Finite B]
    [SampleableType A] [SampleableType B] [SampleableType (A × B)] :
    𝒮[do let a ← ($ᵗ A : ProbComp _); let b ← $ᵗ B; pure (a,b)] = 𝒮[$ᵗ (A × B)] := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  apply evalSPMF_ext
  rintro ⟨a,b⟩
  change Pr[=(a,b) | do let x ← ($ᵗ A : ProbComp _); let y ← $ᵗ B; pure (id x,id y)] = _
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map,probOutput_uniformSample,Nat.card_eq_fintype_card,Fintype.card_prod,Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
theorem uniform_table_split [SampleableType OtherTable] [SampleableType MacKey]
    [SampleableType FullTable] [SampleableType (OtherTable × MacKey)] :
    𝒮[do
      let other ← ($ᵗ OtherTable : ProbComp _)
      let key ← $ᵗ MacKey
      pure (joinTable other key)] = 𝒮[$ᵗ FullTable] := by
  have h := congrArg (Functor.map tableEquiv) (uniform_product (A := OtherTable) (B := MacKey))
  simp only [← evalSPMF_map,map_bind,map_pure] at h
  exact h.trans (evalSPMF_map_bijective_uniform_cross (α := OtherTable × MacKey) (β := FullTable)
    tableEquiv tableEquiv.bijective)
theorem uniform_table_split_bind [SampleableType OtherTable] [SampleableType MacKey]
    [SampleableType FullTable] [SampleableType (OtherTable × MacKey)]
    {α : Type} (next : FullTable → ProbComp α) :
    𝒮[do let table ← ($ᵗ FullTable : ProbComp _); next table] =
      𝒮[do
        let other ← ($ᵗ OtherTable : ProbComp _)
        let key ← $ᵗ MacKey
        next (joinTable other key)] := by
  rw [evalSPMF_bind,← uniform_table_split,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]
end SiggolfT3Mac4.Source
end
end
-- ==== merged from T3_FullCache_CountedSigner ====
section

namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] tagRegion macTag macTagOf
abbrev T3M := SigGolfCandidate.T3.M
abbrev T3Spec := SigGolfCandidate.T3.Spec
abbrev T3Message := SigGolfCandidate.T3.Message
abbrev T3Signature := SigGolfCandidate.T3.Signature
abbrev CountState (S : Type) := Nat × S
def privateMacKey : T3M MacKey := do
  let k0 ← SigGolfCandidate.T3.privateHash (keyCoordinate 0)
  let k1 ← SigGolfCandidate.T3.privateHash (keyCoordinate 1)
  pure (fun i => if i = 0 then k0 else k1)
def privateMac (region : Region) : T3M MacTag := do
  let key ← privateMacKey
  pure (tagRegion key region)
noncomputable def sign (payload : Request T3Message → T3M (Option T3Signature))
    (request : Request T3Message) : T3M (Option T3Signature) := do
  let tag ← privateMac request.cache.region
  if tag = request.cache.tag then payload request else pure none
variable {S : Type}
noncomputable def tableHandler (world : Adaptive.Public (CountState S)) (table : FullTable) :
    QueryImpl T3Spec (StateT (CountState S) ProbComp)
  | .inl input => world input
  | .inr coordinate => StateT.mk fun state => pure (table coordinate,(state.1+1,state.2))
noncomputable def baseHandler (world : Adaptive.Public (CountState S)) (other : OtherTable) :
    QueryImpl T3Spec (StateT (CountState S) ProbComp) := tableHandler world (joinTable other (fun _ => 0))
theorem key_cases (key : MacKey) : (fun i : Fin 2 => if i = 0 then key 0 else key 1) = key := by
  funext i
  fin_cases i <;> simp
theorem privateMacKey_run (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (state : CountState S) :
    (simulateQ (tableHandler world (joinTable other key)) privateMacKey).run state =
      pure (key,(state.1+2,state.2)) := by
  simp [privateMacKey,SigGolfCandidate.T3.privateHash,simulateQ_bind,simulateQ_spec_query,
    tableHandler,StateT.run_bind,joinTable_key,key_cases,Nat.add_assoc]
theorem key_input_length (secret : BitVec 256) (i : Fin 2) :
    (SigGolfCandidate.T3.privateInput secret (keyCoordinate i)).length = 64 := by
  simp [SigGolfCandidate.T3.privateInput,keyCoordinate,SigGolfCandidate.T3.pad64,
    SigGolfCandidate.T3.zero16,bytesLE_length]
def NonMac : T3Spec.Domain → Prop
  | .inl _ => True
  | .inr c => c ≠ keyCoordinate 0 ∧ c ≠ keyCoordinate 1
theorem tableHandler_agrees (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (input : T3Spec.Domain) (h : NonMac input) :
    tableHandler world (joinTable other key) input = baseHandler world other input := by
  cases input with
  | inl input => rfl
  | inr coordinate =>
      have hk := joinTable_other other key (⟨coordinate,h⟩ : OtherCoordinate)
      have hz := joinTable_other other (fun _ => 0) (⟨coordinate,h⟩ : OtherCoordinate)
      simp only [baseHandler,tableHandler]
      rw [hk,hz]
theorem simulate_no_mac {α : Type} (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (program : T3M α) (h : AllQueriesSatisfy program NonMac) :
    simulateQ (tableHandler world (joinTable other key)) program = simulateQ (baseHandler world other) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      rw [simulateQ_bind,simulateQ_bind,simulateQ_spec_query,simulateQ_spec_query,
        tableHandler_agrees world other key input hinput]
      exact congrArg (fun continuation => baseHandler world other input >>= continuation)
        (funext fun answer => ih answer (htail answer))
def keyCharge (_request : Request T3Message) : StateT (CountState S) ProbComp Unit :=
  StateT.mk fun state => pure ((),(state.1+2,state.2))
theorem sign_interpretation (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (payload : Request T3Message → T3M (Option T3Signature))
    (hpayload : ∀ request, AllQueriesSatisfy (payload request) NonMac) (request : Request T3Message) :
    simulateQ (tableHandler world (joinTable other key)) (sign payload request) =
      Adaptive.realSigner keyCharge (fun request => simulateQ (baseHandler world other) (payload request))
        key request := by
  apply StateT.ext
  intro state
  unfold sign privateMac
  rw [bind_assoc]
  simp only [pure_bind,simulateQ_bind,StateT.run_bind,privateMacKey_run]
  by_cases ht : tagRegion key request.cache.region = request.cache.tag
  · simp only [if_pos ht,Adaptive.realSigner,keyCharge,StateT.run_bind,pure_bind]
    exact congrArg (fun p : StateT (CountState S) ProbComp (Option T3Signature) => p.run (state.1+2,state.2))
      (simulate_no_mac world other key _ (hpayload request))
  · simp only [if_neg ht,Adaptive.realSigner,keyCharge,StateT.run_bind,pure_bind]
    rfl
end SiggolfT3Mac4.Source
end
-- ==== merged from T3_FullCache_PayloadSeparation ====
section

section
namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem header_tag_nat (tag lay tree position index : Nat) :
    ((SigGolfCandidate.T3.header tag lay tree position index).toNat / 256) % 256 = tag % 256 := by
  rw [SigGolfCandidate.T3.header_toNat]
  have ht := Nat.mod_lt tag (by decide : 0 < 256)
  have hl := Nat.mod_lt lay (by decide : 0 < 256)
  have hth := Nat.mod_lt (tree/2^32) (by decide : 0 < 256)
  have hp := Nat.mod_lt position (by decide : 0 < 2^32)
  have htl := Nat.mod_lt tree (by decide : 0 < 2^32)
  have hi := Nat.mod_lt index (by decide : 0 < 2^32)
  have hw := SigGolfCandidate.T3.nodeWord_lt tag position index
  split_ifs <;> norm_num only [Nat.reducePow] at * <;> omega
theorem non_mac_tweak (tag lay tree position index : Nat) (htag : tag % 256 ≠ 14)
    (i : Fin 2) :
    (.inl (SigGolfCandidate.T3.header tag lay tree position index) : T3Coordinate) ≠ keyCoordinate i := by
  intro h
  have h' : SigGolfCandidate.T3.header tag lay tree position index =
      SigGolfCandidate.T3.header 14 0 0 0 i.val := Sum.inl.inj h
  have he := congrArg (fun t : BitVec 128 => (t.toNat / 256) % 256) h'
  rw [header_tag_nat,header_tag_nat] at he
  exact htag he
theorem mask_coordinate_other (level pair : Nat) :
    (.inl (SigGolfCandidate.T3.header 13 0 0 level pair) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inl (SigGolfCandidate.T3.header 13 0 0 level pair) : T3Coordinate) ≠ keyCoordinate 1 :=
  ⟨non_mac_tweak 13 0 0 level pair (by decide) 0,
   non_mac_tweak 13 0 0 level pair (by decide) 1⟩
theorem wots_coordinate_other (lay tree pair leaf : Nat) :
    (.inl (SigGolfCandidate.T3.header 0 lay tree pair leaf) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inl (SigGolfCandidate.T3.header 0 lay tree pair leaf) : T3Coordinate) ≠ keyCoordinate 1 :=
  ⟨non_mac_tweak 0 lay tree pair leaf (by decide) 0,
   non_mac_tweak 0 lay tree pair leaf (by decide) 1⟩
theorem bpors_coordinate_other (coord index pair : Nat) :
    (.inl (SigGolfCandidate.T3.header 8 coord index 0 pair) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inl (SigGolfCandidate.T3.header 8 coord index 0 pair) : T3Coordinate) ≠ keyCoordinate 1 :=
  ⟨non_mac_tweak 8 coord index 0 pair (by decide) 0,
   non_mac_tweak 8 coord index 0 pair (by decide) 1⟩
theorem nonce_coordinate_other (message : SigGolfCandidate.T3.Message) :
    (.inr (.inl message) : T3Coordinate) ≠ keyCoordinate 0 ∧
    (.inr (.inl message) : T3Coordinate) ≠ keyCoordinate 1 := by
  constructor <;> intro h <;> cases h
end SiggolfT3Mac4.Source
end
section
namespace SiggolfT3Mac4.Source.Payload
open OracleComp OracleSpec
open SigGolfCandidate.T3
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem pure_allowed {α : Type} (value : α) : AllQueriesSatisfy (pure value : M α) NonMac :=
  allQueriesSatisfy_pure _ _
theorem bind_allowed {α β : Type} {program : M α} {next : α → M β}
    (hp : AllQueriesSatisfy program NonMac) (hn : ∀ value, AllQueriesSatisfy (next value) NonMac) :
    AllQueriesSatisfy (program >>= next) NonMac := allQueriesSatisfy_bind hp hn
theorem map_allowed {α β : Type} (f : α → β) {program : M α}
    (hp : AllQueriesSatisfy program NonMac) : AllQueriesSatisfy (f <$> program) NonMac := by
  rw [map_eq_bind_pure_comp]
  exact bind_allowed hp fun _ => pure_allowed _
theorem foldlM_allowed {α β : Type} (items : List β) (f : α → β → M α)
    (h : ∀ a b,AllQueriesSatisfy (f a b) NonMac) (initial : α) :
    AllQueriesSatisfy (items.foldlM f initial) NonMac := by
  induction items generalizing initial with
  | nil => exact pure_allowed _
  | cons a items ih =>
      rw [List.foldlM_cons]
      exact bind_allowed (h initial a) ih
theorem mapM_allowed {α β : Type} (items : List α) (f : α → M β)
    (h : ∀ a,AllQueriesSatisfy (f a) NonMac) : AllQueriesSatisfy (items.mapM f) NonMac := by
  induction items with
  | nil => exact pure_allowed _
  | cons a items ih =>
      rw [List.mapM_cons]
      exact bind_allowed (h a) fun _ => bind_allowed ih fun _ => pure_allowed _
theorem map_allowed_iff {α β : Type} (f : α → β) (program : M α) :
    AllQueriesSatisfy (f <$> program) NonMac ↔ AllQueriesSatisfy program NonMac := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [map_pure,allQueriesSatisfy_pure]
  | query_bind input next ih =>
      simp only [map_bind,allQueriesSatisfy_query_bind_iff,ih]
theorem publicHash_allowed (input : HashInput) : AllQueriesSatisfy (publicHash input) NonMac :=
  (allQueriesSatisfy_query_iff _ _).mpr trivial
theorem privatePair_allowed (tag lay tree position index : Nat) (htag : tag % 256 ≠ 14) :
    AllQueriesSatisfy (privatePair tag lay tree position index) NonMac := by
  unfold privatePair
  apply bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr
      ⟨non_mac_tweak tag lay tree position index htag 0, non_mac_tweak tag lay tree position index htag 1⟩
  · intro _; exact pure_allowed _
theorem wotsPair_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 0 lay tree position index) NonMac :=
  privatePair_allowed 0 lay tree position index (by decide)
theorem maskPair_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 13 lay tree position index) NonMac :=
  privatePair_allowed 13 lay tree position index (by decide)
theorem ftsPair_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 8 lay tree position index) NonMac :=
  privatePair_allowed 8 lay tree position index (by decide)
theorem privateNonce_allowed (message : Message) : AllQueriesSatisfy (privateNonce message) NonMac := by
  unfold privateNonce
  apply bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (nonce_coordinate_other message)
  · intro _; exact pure_allowed _
attribute [local aesop safe apply] pure_allowed bind_allowed map_allowed foldlM_allowed mapM_allowed
  publicHash_allowed wotsPair_allowed maskPair_allowed ftsPair_allowed privateNonce_allowed
macro "source_queries" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))
theorem shortHash_allowed (input : HashInput) : AllQueriesSatisfy (shortHash input) NonMac := by
  unfold shortHash; source_queries
attribute [local aesop safe apply] shortHash_allowed
theorem projHash_allowed (high : Bool) (input : HashInput) : AllQueriesSatisfy (projHash high input) NonMac := by
  unfold projHash; source_queries
attribute [local aesop safe apply] projHash_allowed
theorem mask_allowed (level index : Nat) : AllQueriesSatisfy (mask level index) NonMac := by
  unfold mask pairedMask; source_queries
attribute [local aesop safe apply] mask_allowed
theorem chain_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NonMac := by
  unfold chain; source_queries
attribute [local aesop safe apply] chain_allowed
theorem topChain_allowed (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (topChain leaf i start count value) NonMac := by
  unfold topChain; source_queries
attribute [local aesop safe apply] topChain_allowed
theorem layChain_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (layChain lay tree leaf i start count value) NonMac := by
  unfold layChain; split <;> source_queries
attribute [local aesop safe apply] layChain_allowed
theorem leafHash_allowed (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NonMac := by
  unfold leafHash; source_queries
attribute [local aesop safe apply] leafHash_allowed
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NonMac := by
  unfold nodeHash; source_queries
attribute [local aesop safe apply] nodeHash_allowed
theorem buildLeaf_allowed (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NonMac := by
  unfold buildLeaf; source_queries
attribute [local aesop safe apply] buildLeaf_allowed
theorem buildLevel_allowed (tag lay tree h level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NonMac := by
  unfold buildLevel; source_queries
attribute [local aesop safe apply] buildLevel_allowed
theorem buildLevels_allowed (tag lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NonMac := by
  unfold buildLevels; source_queries
attribute [local aesop safe apply] buildLevels_allowed
theorem nm_topNodeHashN_q (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeHashN heap n left right) NonMac := by
  unfold topNodeHashN; source_queries
attribute [local aesop safe apply] nm_topNodeHashN_q
theorem nm_topNonceSearch_q (h heap : Nat) (left right : Digest) :
    ∀ fuel n, AllQueriesSatisfy (topNonceSearch h heap left right fuel n) NonMac
  | 0, n => by unfold topNonceSearch; source_queries
  | fuel+1, n => by
      have ih := nm_topNonceSearch_q h heap left right fuel (n+1)
      unfold topNonceSearch; source_queries
attribute [local aesop safe apply] nm_topNonceSearch_q
theorem nm_topNodeAt_q (h heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeAt h heap left right) NonMac := by
  unfold topNodeAt; exact nm_topNonceSearch_q h heap left right _ 0
attribute [local aesop safe apply] nm_topNodeAt_q
theorem nm_buildTopLevel_q (level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (buildTopLevel level nodes) NonMac := by
  unfold buildTopLevel; source_queries
attribute [local aesop safe apply] nm_buildTopLevel_q
theorem nm_buildTopLevels_q (leaves : List Digest) :
    AllQueriesSatisfy (buildTopLevels leaves) NonMac := by
  unfold buildTopLevels; source_queries
attribute [local aesop safe apply] nm_buildTopLevels_q
theorem buildTree_allowed (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NonMac := by
  unfold buildTree; source_queries
attribute [local aesop safe apply] buildTree_allowed
theorem topPairsFrom_allowed (first start : Nat) (init : List Digest) : AllQueriesSatisfy (topPairsFrom first start init) NonMac := by
  unfold topPairsFrom topSeedPair; source_queries
attribute [local aesop safe apply] topPairsFrom_allowed
theorem topCoefs_allowed (leaf : Nat) : AllQueriesSatisfy (topCoefs leaf) NonMac := by
  unfold topCoefs; source_queries
attribute [local aesop safe apply] topCoefs_allowed
theorem topCoefsK_allowed (f : Nat) (carry : Digest) : AllQueriesSatisfy (topCoefsK f carry) NonMac := by
  unfold topCoefsK; source_queries
attribute [local aesop safe apply] topCoefsK_allowed
theorem buildLeafTopC_allowed (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) : AllQueriesSatisfy (buildLeafTopC leaf coefs digits signatureOnly) NonMac := by
  unfold buildLeafTopC; source_queries
attribute [local aesop safe apply] buildLeafTopC_allowed
theorem topFamilyCoefs_allowed (leaf : Nat) (cc : List Digest × Digest) : AllQueriesSatisfy (topFamilyCoefs leaf cc) NonMac := by
  unfold topFamilyCoefs; source_queries
attribute [local aesop safe apply] topFamilyCoefs_allowed
theorem topTreeStep_allowed (st : List Digest × List Digest × Digest) (leaf : Nat) : AllQueriesSatisfy (topTreeStep st leaf) NonMac := by
  unfold topTreeStep; source_queries
attribute [local aesop safe apply] topTreeStep_allowed
theorem buildLeafTop_allowed (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTop leaf digits signatureOnly) NonMac := by
  unfold buildLeafTop; source_queries
attribute [local aesop safe apply] buildLeafTop_allowed
theorem buildTopTree_allowed : AllQueriesSatisfy buildTopTree NonMac := by
  unfold buildTopTree; source_queries
attribute [local aesop safe apply] buildTopTree_allowed
theorem keygenPayload_allowed : AllQueriesSatisfy keygenPayload NonMac := by
  unfold keygenPayload maskedLevel pairedMask; source_queries
theorem counterSearch_allowed (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) NonMac := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; source_queries
  | succ fuel ih => unfold counterSearch; source_queries
attribute [local aesop safe apply] counterSearch_allowed
theorem digest_allowed (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) NonMac := by
  unfold digest; source_queries
attribute [local aesop safe apply] digest_allowed
theorem digestSearch_allowed (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (digestSearch rho message counter fuel) NonMac := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; source_queries
  | succ fuel ih => unfold digestSearch; source_queries
attribute [local aesop safe apply] digestSearch_allowed
theorem ftsLeaf_allowed (index coord leaf : Nat) (secret : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf secret) NonMac := by
  unfold ftsLeaf; source_queries
attribute [local aesop safe apply] ftsLeaf_allowed
theorem buildFts_allowed (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) NonMac := by
  unfold buildFts; source_queries
attribute [local aesop safe apply] buildFts_allowed
theorem forestPk_allowed (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (forestPk index roots) NonMac := by
  unfold forestPk; source_queries
attribute [local aesop safe apply] forestPk_allowed
theorem topPath_allowed (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NonMac := by
  unfold topPath; source_queries
attribute [local aesop safe apply] topPath_allowed
theorem signTop_allowed (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NonMac := by
  unfold signTop; source_queries
attribute [local aesop safe apply] signTop_allowed
theorem signLayers_allowed (cache : SigGolfCandidate.T3.Cache) (index n : Nat) (message : Digest) :
    AllQueriesSatisfy (signLayers cache index n message) NonMac := by
  induction n generalizing message with
  | zero => unfold signLayers; source_queries
  | succ n ih => unfold signLayers; source_queries
attribute [local aesop safe apply] signLayers_allowed
theorem signPayload_allowed (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac := by
  unfold signPayload; source_queries
end SiggolfT3Mac4.Source.Payload
end
end
-- ==== merged from T3_FullCache_CoreBridge ====
section

section
namespace SiggolfT3Mac4
open SphincsSecurity
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem decodeTag_encodeTag (tag : MacTag) : decodeTag (encodeTag tag) = tag := by
  funext i
  obtain ⟨h0,h1,h2,h3⟩ := extract_answerOfWords (tag 0) (tag 1) (tag 2) (tag 3)
  fin_cases i <;> simp only [decodeTag,encodeTag] <;> assumption
theorem encodeTag_decodeTag (tag : HashOutput) : encodeTag (decodeTag tag) = tag :=
  answerOfWords_extract tag
def tagEquiv : MacTag ≃ HashOutput where
  toFun := encodeTag
  invFun := decodeTag
  left_inv := decodeTag_encodeTag
  right_inv := encodeTag_decodeTag
theorem encodeTag_injective : Function.Injective encodeTag := tagEquiv.injective
end SiggolfT3Mac4
end
section
namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def toCoreCache (cache : SiggolfT3Mac4.Cache) : SigGolfCandidate.T3.Cache :=
  ⟨encodeTag cache.tag,cache.region⟩
def fromCoreCache (cache : SigGolfCandidate.T3.Cache) : SiggolfT3Mac4.Cache :=
  ⟨cache.region,decodeTag cache.tag⟩
theorem fromCoreCache_toCoreCache (cache : SiggolfT3Mac4.Cache) :
    fromCoreCache (toCoreCache cache)=cache := by
  cases cache
  simp only [fromCoreCache,toCoreCache,decodeTag_encodeTag]
theorem toCoreCache_fromCoreCache (cache : SigGolfCandidate.T3.Cache) :
    toCoreCache (fromCoreCache cache)=cache := by
  cases cache
  simp only [fromCoreCache,toCoreCache,encodeTag_decodeTag]
def coreCacheEquiv : SiggolfT3Mac4.Cache ≃ SigGolfCandidate.T3.Cache where
  toFun := toCoreCache
  invFun := fromCoreCache
  left_inv := fromCoreCache_toCoreCache
  right_inv := toCoreCache_fromCoreCache
def corePayload (request : SiggolfT3Mac4.Request T3Message) : T3M (Option T3Signature) :=
  SigGolfCandidate.T3.signPayload (toCoreCache request.cache) request.message
theorem corePayload_nonMac (request : SiggolfT3Mac4.Request T3Message) :
    AllQueriesSatisfy (corePayload request) NonMac :=
  Payload.signPayload_allowed _ _
theorem privateMacKey_eq_core : privateMacKey=SigGolfCandidate.T3.privateMacKey := rfl
theorem core_sign_eq (cache : SiggolfT3Mac4.Cache) (message : T3Message) :
    SigGolfCandidate.T3.sign (toCoreCache cache) message = sign corePayload ⟨message,cache⟩ := by
  unfold SigGolfCandidate.T3.sign SigGolfCandidate.T3.privateMac sign privateMac
  rw [privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,toCoreCache,tagRegion,regionBytes]
  apply congrArg (fun k => SigGolfCandidate.T3.privateMacKey >>= k)
  funext key
  by_cases h : macTag key (List.ofFn cache.region)=cache.tag
  · simp only [h,ne_eq,not_true_eq_false,ite_false,ite_true,corePayload,toCoreCache]
  · have he : encodeTag (macTag key (List.ofFn cache.region)) ≠ encodeTag cache.tag :=
      fun hx => h (encodeTag_injective hx)
    rw [if_pos he, if_neg h]
end SiggolfT3Mac4.Source
end
end
-- ==== merged from T3_FullCache_RequestBridge ====
section

section
namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem counted_source_authentication_hop
    [SampleableType MacKey] [SampleableType MacTag] {S α β : Type}
    (world : Adaptive.Public (CountState S)) (other : OtherTable) (region : Region)
    (payload : Request T3Message → T3M (Option T3Signature))
    (hpayload : ∀ request, AllQueriesSatisfy (payload request) NonMac)
    (program : Cache → OracleComp (Interaction T3Message T3Signature) α)
    (state : Cache → CountState S)
    (cont : Cache → ((α × QueryLog (Requests T3Message T3Signature)) × CountState S) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ published result,2^32 < result.1.2.length → Pr[event | cont published result] = 0) :
    Pr[event | do
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region,tagRegion key region⟩
      Adaptive.run world
        (fun request => simulateQ (tableHandler world (joinTable other key)) (sign payload request))
        (program published) (state published) >>= cont published] ≤
    Pr[event | do
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region,tag⟩
      Adaptive.run world
        (Adaptive.idealSigner keyCharge
          (fun request => simulateQ (baseHandler world other) (payload request)) published)
        (program published) (state published) >>= cont published] +
      ((2 : ENNReal)^152)⁻¹ := by
  simp_rw [sign_interpretation world other _ payload hpayload]
  exact Adaptive.published_lifetime_authentication_hop region (fun _ => world)
    (fun _ => keyCharge) (fun _ request => simulateQ (baseHandler world other) (payload request))
    program state cont event hlong
theorem averaged_source_authentication_hop
    [SampleableType OtherTable] [SampleableType MacKey] [SampleableType MacTag] {S α β : Type}
    (world : OtherTable → Adaptive.Public (CountState S)) (region : OtherTable → Region)
    (payload : OtherTable → Request T3Message → T3M (Option T3Signature))
    (hpayload : ∀ other request, AllQueriesSatisfy (payload other request) NonMac)
    (program : OtherTable → Cache → OracleComp (Interaction T3Message T3Signature) α)
    (state : OtherTable → Cache → CountState S)
    (cont : OtherTable → Cache → ((α × QueryLog (Requests T3Message T3Signature)) × CountState S) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ other published result,2^32 < result.1.2.length → Pr[event | cont other published result] = 0) :
    Pr[event | do
      let other ← $ᵗ OtherTable
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region other,tagRegion key (region other)⟩
      Adaptive.run (world other)
        (fun request => simulateQ (tableHandler (world other) (joinTable other key)) (sign (payload other) request))
        (program other published) (state other published) >>= cont other published] ≤
    Pr[event | do
      let other ← $ᵗ OtherTable
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region other,tag⟩
      Adaptive.run (world other)
        (Adaptive.idealSigner keyCharge
          (fun request => simulateQ (baseHandler (world other) other) (payload other request)) published)
        (program other published) (state other published) >>= cont other published] +
      ((2 : ENNReal)^152)⁻¹ := by
  apply Adaptive.probEvent_bind_const_charge
  intro other
  exact counted_source_authentication_hop (world other) other (region other) (payload other)
    (hpayload other) (program other) (state other) (cont other) event (hlong other)
end SiggolfT3Mac4.Source
end
section
namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Security
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev CoreRequest := SigGolfCandidate.T3.Security.Request
abbrev CoreRequests := SigGolfCandidate.T3.Security.Requests
abbrev CoreInteraction := SigGolfCandidate.T3.Security.LazyPrivate.Interaction
def toCoreRequest (request : Request T3Message) : CoreRequest :=
  ⟨request.message,toCoreCache request.cache⟩
def fromCoreRequest (request : CoreRequest) : Request T3Message :=
  ⟨request.message,fromCoreCache request.cache⟩
theorem toCoreRequest_fromCoreRequest (request : CoreRequest) :
    toCoreRequest (fromCoreRequest request)=request := by
  cases request
  simp only [toCoreRequest,fromCoreRequest,toCoreCache_fromCoreCache]
theorem fromCoreRequest_toCoreRequest (request : Request T3Message) :
    fromCoreRequest (toCoreRequest request)=request := by
  cases request
  simp only [toCoreRequest,fromCoreRequest,fromCoreCache_toCoreCache]
theorem entry_roundtrip (request : CoreRequest) (answer : Option T3Signature) :
    (⟨toCoreRequest (fromCoreRequest request),answer⟩ : (input : CoreRequests.Domain) × CoreRequests.Range input)=⟨request,answer⟩ := by
  exact Sigma.ext (toCoreRequest_fromCoreRequest request) HEq.rfl
def toCoreLog (log : QueryLog (Requests T3Message T3Signature)) : QueryLog CoreRequests :=
  log.map fun entry => ⟨toCoreRequest entry.1,entry.2⟩
theorem toCoreLog_length (log : QueryLog (Requests T3Message T3Signature)) :
    (toCoreLog log).length=log.length := by simp [toCoreLog]
noncomputable def interactionMap : QueryImpl CoreInteraction
    (OracleComp (Interaction T3Message T3Signature))
  | .inl input => liftM ((Interaction T3Message T3Signature).query (.inl input))
  | .inr request => liftM ((Interaction T3Message T3Signature).query (.inr (fromCoreRequest request)))
noncomputable def transport {α : Type} (program : OracleComp CoreInteraction α) :
    OracleComp (Interaction T3Message T3Signature) α := simulateQ interactionMap program
def restore {α State : Type}
    (result : (α × QueryLog (Requests T3Message T3Signature)) × State) :
    (α × QueryLog CoreRequests) × State := ((result.1.1,toCoreLog result.1.2),result.2)
theorem run_transport {α State : Type} (world : RequestHop.Public State)
    (signer : RequestHop.Signer State) (program : OracleComp CoreInteraction α) (state : State) :
    RequestHop.run world signer program state =
      restore <$> Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [RequestHop.run_public,Adaptive.run_public,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [RequestHop.run_request,Adaptive.run_request,map_bind,toCoreRequest_fromCoreRequest]
          apply bind_congr
          intro head
          rw [ih]
          simp only [Functor.map_map,Function.comp_def,restore,toCoreLog,List.map_cons,
            toCoreRequest_fromCoreRequest,entry_roundtrip]
          rfl
theorem run_transport_bind {α β State : Type} (world : RequestHop.Public State)
    (signer : RequestHop.Signer State) (program : OracleComp CoreInteraction α) (state : State)
    (cont : ((α × QueryLog CoreRequests) × State) → ProbComp β) :
    RequestHop.run world signer program state >>= cont =
      Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state >>= fun result => cont (restore result) := by
  rw [run_transport,bind_map_left]
end SiggolfT3Mac4.Source
end
end
-- ==== merged from T3_FullCache_NativeMac ====
section

namespace SigGolfCandidate.T3.Security.CacheAuthentication
open OracleComp OracleSpec SphincsSecurity
@[irreducible] noncomputable def regionFintype : Fintype Region := by
  classical
  exact inferInstance
abbrev MacTable := SiggolfT3Mac4.MacKey
@[irreducible] noncomputable def macTableSampler : SampleableType MacTable := by
  classical
  exact SampleableType.ofFintype _
end SigGolfCandidate.T3.Security.CacheAuthentication
namespace SigGolfCandidate.T3.Security.MacGame
open OracleComp OracleSpec ENNReal CacheAuthentication
open SiggolfT3Mac4 (MacKey encodeTag decodeTag tagRegion)
open SiggolfT3Mac4.Adaptive (retagRegion)
open SiggolfT3Mac4.Source (keyCoordinate toCoreCache fromCoreCache toCoreRequest fromCoreRequest)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType MacTable := macTableSampler
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
variable {State : Type}
abbrev NonMac := SiggolfT3Mac4.Source.NonMac
def tagAt (key : MacTable) (region : Region) : HashOutput := encodeTag (tagRegion key region)
def retag (key : MacTable) (published : T3.Cache) : MacTable := retagRegion key (fromCoreCache published)
noncomputable def sourceHandler (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable) :
    QueryImpl T3.Spec (StateT State ProbComp)
  | .inl input => base (.inl input)
  | .inr coordinate => do
      let answer ← base (.inr coordinate)
      if coordinate=keyCoordinate 0 then pure (key 0)
      else if coordinate=keyCoordinate 1 then pure (key 1) else pure answer
theorem sourceHandler_agrees (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable)
    (input : T3.Spec.Domain) (h : NonMac input) : sourceHandler base key input=base input := by
  cases input with
  | inl input => rfl
  | inr coordinate => simp only [sourceHandler,h.1,h.2,ite_false,bind_pure]
theorem simulate_no_mac {α : Type} (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable)
    (program : M α) (h : AllQueriesSatisfy program NonMac) :
    simulateQ (sourceHandler base key) program=simulateQ base program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      rw [simulateQ_bind,simulateQ_bind,simulateQ_spec_query,simulateQ_spec_query,
        sourceHandler_agrees base key input hinput]
      exact congrArg (fun continuation => base input >>= continuation) (funext fun answer => ih answer (htail answer))
theorem payload_no_mac (cache : T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac :=
  SiggolfT3Mac4.Source.Payload.signPayload_allowed cache message
noncomputable def overhead (base : QueryImpl T3.Spec (StateT State ProbComp)) : StateT State ProbComp Unit := do
  let _ ← base (.inr (keyCoordinate 0))
  let _ ← base (.inr (keyCoordinate 1))
  pure ()
noncomputable def realSigner (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable) :
    RequestHop.Signer State := fun request =>
  SiggolfT3Mac4.Adaptive.realSigner (fun _ => overhead base)
    (fun request => simulateQ base (SiggolfT3Mac4.Source.corePayload request)) key (fromCoreRequest request)
noncomputable def idealSigner (base : QueryImpl T3.Spec (StateT State ProbComp)) (published : T3.Cache) :
    RequestHop.Signer State := fun request =>
  SiggolfT3Mac4.Adaptive.idealSigner (fun _ => overhead base)
    (fun request => simulateQ base (SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (fromCoreRequest request)
theorem source_key_eq (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable) :
    simulateQ (sourceHandler base key) privateMacKey =
      (do let _ ← overhead base; pure key) := by
  rw [← SiggolfT3Mac4.Source.privateMacKey_eq_core]
  unfold SiggolfT3Mac4.Source.privateMacKey privateHash
  simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure,sourceHandler]
  simp only [ite_true,SiggolfT3Mac4.Source.keyCoordinate_zero_ne_one,
    Ne.symm SiggolfT3Mac4.Source.keyCoordinate_zero_ne_one,ite_false,bind_assoc,pure_bind]
  rw [SiggolfT3Mac4.Source.key_cases]
  simp only [overhead,bind_assoc,pure_bind]
theorem source_signer_eq (base : QueryImpl T3.Spec (StateT State ProbComp))
    (key : MacTable) (request : Request) :
    simulateQ (sourceHandler base key) (sign request.cache request.message)=realSigner base key request := by
  rw [← SiggolfT3Mac4.Source.toCoreCache_fromCoreCache request.cache,
    SiggolfT3Mac4.Source.core_sign_eq]
  unfold SiggolfT3Mac4.Source.sign SiggolfT3Mac4.Source.privateMac
  rw [SiggolfT3Mac4.Source.privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,simulateQ_bind,source_key_eq,bind_assoc,pure_bind]
  change (overhead base >>= fun _ => _)=_
  unfold realSigner SiggolfT3Mac4.Adaptive.realSigner
  apply congrArg (fun next => overhead base >>= next)
  funext ignored
  simp only [SiggolfT3Mac4.Source.toCoreCache_fromCoreCache,
    fromCoreRequest,fromCoreCache]
  split_ifs
  · exact simulate_no_mac base key _ (SiggolfT3Mac4.Source.corePayload_nonMac _)
  · rfl
theorem authentication_hop {α β : Type} (world : RequestHop.Public State)
    (base : QueryImpl T3.Spec (StateT State ProbComp)) (published : T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog Requests) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result,limit < result.1.2.length → Pr[event | cont result]=0) :
    Pr[event | ($ᵗ MacTable : ProbComp _) >>= fun key =>
      RequestHop.run world (realSigner base (retag key published)) program state >>= cont] ≤
      Pr[event | RequestHop.run world (idealSigner base published) program state >>= cont]+
        limit*((2 : ENNReal)^184)⁻¹ := by
  have hr := @SiggolfT3Mac4.Source.run_transport_bind α β State
  simp only [hr]
  simp only [realSigner,idealSigner,retag,SiggolfT3Mac4.Source.fromCoreRequest_toCoreRequest]
  exact SiggolfT3Mac4.Adaptive.authentication_hop world (fun _ => overhead base)
    (fun request => simulateQ base (SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (SiggolfT3Mac4.Source.transport program) limit state
    (fun result => cont (SiggolfT3Mac4.Source.restore result)) event
    (fun result hlong' => hlong _ (by simpa only [SiggolfT3Mac4.Source.restore,
      SiggolfT3Mac4.Source.toCoreLog_length] using hlong'))
noncomputable local instance : SampleableType SiggolfT3Mac4.MacTag := SampleableType.ofFintype _
theorem encoded_uniform_bind {α : Type} (next : HashOutput → ProbComp α) :
    𝒮[do let tag ← ($ᵗ SiggolfT3Mac4.MacTag : ProbComp _); next (encodeTag tag)] =
      𝒮[do let tag ← ($ᵗ HashOutput : ProbComp _); next tag] := by
  have h := evalSPMF_map_bijective_uniform_cross (α := SiggolfT3Mac4.MacTag)
    (β := HashOutput) encodeTag SiggolfT3Mac4.tagEquiv.bijective
  rw [← bind_map_left,evalSPMF_bind,h,← evalSPMF_bind]
theorem refresh_published {α : Type} (region : Region) (next : HashOutput → MacTable → ProbComp α) :
    𝒮[do let key ← ($ᵗ MacTable : ProbComp _); next (tagAt key region) key] =
      𝒮[do
        let tag ← ($ᵗ HashOutput : ProbComp _)
        let key ← ($ᵗ MacTable : ProbComp _)
        next tag (retag key ⟨tag,region⟩)] := by
  have h := SiggolfT3Mac4.Adaptive.publication_retag_law region
    (fun published key => next (encodeTag published.tag) key)
  have he := encoded_uniform_bind (fun tag => do
    let key ← ($ᵗ MacTable : ProbComp _)
    next tag (retag key ⟨tag,region⟩))
  simp only [retag,fromCoreCache,SiggolfT3Mac4.decodeTag_encodeTag] at he
  exact h.trans he
theorem sample_mac_at_bind {α : Type} (region : Region) (next : HashOutput → ProbComp α) :
    𝒮[do let key ← ($ᵗ MacTable : ProbComp _); next (tagAt key region)] =
      𝒮[do let tag ← ($ᵗ HashOutput : ProbComp _); next tag] := by
  rw [refresh_published region (fun tag _ => next tag)]
  apply evalSPMF_bind_congr'
  intro tag
  apply evalSPMF_ext
  intro result
  change Pr[=result | ($ᵗ MacTable : ProbComp _) >>= fun _ => next tag]=Pr[=result | next tag]
  rw [probOutput_bind_const]
  simp
end SigGolfCandidate.T3.Security.MacGame
end
-- ==== merged from T3_SearchCost ====
section

namespace SigGolfCandidate.T3.SearchCost
open OracleComp OracleSpec Cost Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def cost {α : Type} (answers : Answers) (program : M α) : Nat :=
  (evalWithAnswerFn answers (Cost.countBlocks program)).2
theorem counted_fst {α : Type} (answers : Answers) (program : M α) :
    (evalWithAnswerFn answers (Cost.countBlocks program)).1=evalWithAnswerFn answers program := by
  have h := congrArg (evalWithAnswerFn answers) (fst_countWith weight program)
  simpa only [evalWithAnswerFn_map,countBlocks] using h
@[simp] theorem cost_pure {α : Type} (answers : Answers) (value : α) :
    cost answers (pure value : M α)=0 := rfl
theorem cost_bind {α β : Type} (answers : Answers) (first : M α) (next : α → M β) :
    cost answers (first >>= next)=cost answers first+cost answers (next (evalWithAnswerFn answers first)) := by
  unfold cost
  rw [countBlocks,countWith_bind,evalWithAnswerFn_bind,evalWithAnswerFn_map]
  rw [show (evalWithAnswerFn answers (countWith weight first)).1=evalWithAnswerFn answers first from
    counted_fst answers first]
  rfl
@[simp] theorem cost_query (answers : Answers) (q : Cost.Query) :
    cost answers (T3.Spec.query q)=Cost.weight q := by
  unfold cost countBlocks
  rw [countWith_query,evalWithAnswerFn_map]
theorem eval_mem_support {α : Type} (answers : Answers) (program : M α) :
    evalWithAnswerFn answers program ∈ support program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [evalWithAnswerFn_pure,support_pure,Set.mem_singleton_iff]
  | query_bind q next ih =>
      rw [evalWithAnswerFn_bind,mem_support_bind_iff]
      exact ⟨_,mem_support_query q _,ih _⟩
theorem cost_bound {α : Type} {P : Cost.Query → Prop} {Post : α → Prop} {k : Nat}
    {program : M α} (answers : Answers) (h : Cost.Bound P Post k program) :
    cost answers program ≤ k :=
  (h.count_support _ (eval_mem_support answers (Cost.countBlocks program))).2
theorem post_bound {α : Type} {P : Cost.Query → Prop} {Post : α → Prop} {k : Nat}
    {program : M α} (answers : Answers) (h : Cost.Bound P Post k program) :
    Post (evalWithAnswerFn answers program) := by
  have hh := (h.count_support _ (eval_mem_support answers (Cost.countBlocks program))).1
  rwa [counted_fst] at hh
end SigGolfCandidate.T3.SearchCost
end
-- ==== merged from T3_FullCache_ExpansionCost ====
section

namespace SigGolfCandidate.T3.FullCacheExpansionCost
open OracleComp OracleSpec Cost Correctness SearchCost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem foldlM_cost_ge {α β : Type} (answers : Answers)
    (f : β → α → M β) (k : Nat)
    (h : ∀ state value, k ≤ cost answers (f state value))
    (values : List α) (init : β) :
    values.length*k ≤ cost answers (values.foldlM f init) := by
  induction values generalizing init with
  | nil => simp only [List.foldlM_nil, cost_pure, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons value values ih =>
      rw [List.foldlM_cons, cost_bind, List.length_cons, Nat.add_mul, Nat.one_mul]
      simpa only [Nat.add_comm] using Nat.add_le_add (h init value)
        (ih (evalWithAnswerFn answers (f init value)))
theorem privatePair_cost (answers : Answers) (tag lay tree position index : Nat) :
    cost answers (privatePair tag lay tree position index) = 1 := by
  simp only [privatePair, privateHash, cost_bind, cost_query, cost_pure, Nat.add_zero]
  rfl
theorem buildFts_cost_ge (answers : Answers) (index coord : Nat) :
    1024 ≤ cost answers (buildFts index coord) := by
  unfold buildFts
  rw [cost_bind]
  apply Nat.le_trans _ (Nat.le_add_right _ _)
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest) pair => do
      let (left, right) ← privatePair 8 coord index 0 pair
      let leftLeaf ← ftsLeaf index coord (2*pair) left
      let rightLeaf ← ftsLeaf index coord (2*pair+1) right
      pure (state.1 ++ [leftLeaf,rightLeaf],state.2 ++ [left,right])) 1
    (fun state pair => by
      simp only [cost_bind, privatePair_cost, cost_pure]
      omega) (List.range 1024) ([], [])
  simpa only [List.length_range, Nat.mul_one] using h
theorem forestRows_cost_ge (answers : Answers) (index : Nat) (chosen : List Selection) :
    7168 ≤ cost answers (forestRows index chosen) := by
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map fun s => sel.bucket*128+s
      let opened := selected.map fun s => secrets.getD s 0
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1++opened,state.2.1++inner++outer,state.2.2++[(levels.getD 11 []).getD 0 0]))
    1024
    (fun state coord => by
      rw [cost_bind]
      exact Nat.le_trans (buildFts_cost_ge answers index coord) (Nat.le_add_right _ _))
    (List.range 7) ([],[],[])
  exact h
theorem signPayload_cost_ge (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hs : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    90 ≤ cost answers (signPayload cache message) := by
  rw [signPayload_forestRows] at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs
  rw [cost_bind]
  cases hd : evalWithAnswerFn answers
      (digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [cost_bind, hd]
      have h := forestRows_cost_ge answers (output.toNat%2^31) (selections output)
      omega
end SigGolfCandidate.T3.FullCacheExpansionCost
end
-- ==== merged from T3_FullCache_NativeBudget ====
section

section
end
section
end
set_option Elab.async false
namespace SigGolfCandidate.T3.Security.ProposalOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open BPORS.Adaptive
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable def tailBase : ENNReal := 4097 / 4096
noncomputable def tailMoment : ENNReal := 4195328 / 4194303
theorem tailBase_one_le : 1 ≤ tailBase := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold tailBase; finiteness)).mp
  norm_num [tailBase, ENNReal.toReal_div]
theorem tailMoment_one_le : 1 ≤ tailMoment := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold tailMoment; finiteness)).mp
  norm_num [tailMoment, ENNReal.toReal_div]
theorem acceptance_le_one : (1024/1025 : ENNReal) ≤ 1 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
theorem tailMoment_eq : tailMoment =
    (1024/1025 : ENNReal) * tailBase / (1 - (1 - 1024/1025) * tailBase) := by
  have hrem : (1 - (1024/1025 : ENNReal)).toReal = 1 - (1024/1025 : ENNReal).toReal := by
    rw [ENNReal.toReal_sub_of_le acceptance_le_one (by finiteness), ENNReal.toReal_one]
  have hlt : (1 - (1024/1025 : ENNReal)) * tailBase < 1 := by
    apply (ENNReal.toReal_lt_toReal (by unfold tailBase; finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, hrem]
    norm_num [tailBase, ENNReal.toReal_div]
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold tailMoment; finiteness)
    (ENNReal.div_ne_top (by unfold tailBase; finiteness) (tsub_pos_iff_lt.mpr hlt).ne')).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hlt.le (by finiteness)]
  simp only [ENNReal.toReal_mul, hrem]
  norm_num [tailMoment, tailBase, ENNReal.toReal_div]
theorem block_moment :
    expectedValue (proposalBlockLength (1024/1025) (by norm_num) acceptance_le_one)
      (fun length => tailBase ^ length) = tailMoment := by
  simp only [expectedValue, PMF.probOutput_eq_apply]
  rw [proposalBlockLength_power_moment, ← tailMoment_eq]
theorem initial_bound :
    tailMoment ^ (2^32) / tailBase ^ BPORS.Numeric.proposalLength ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  let z : ℝ := 4097 / 4096
  let m : ℝ := 4195328 / 4194303
  have hz : 0 < z := by norm_num [z]
  have hm : 0 < m := by norm_num [m]
  have hlog : (2^32 : ℝ) * Real.log m -
      BPORS.Numeric.proposalLength * Real.log z ≤ -700 * Real.log 2 := by
    have hu := Real.log_le_sub_one_of_pos hm
    have hl := Real.one_sub_inv_le_log_of_pos hz
    have ht := Real.log_two_lt_d9
    norm_num [m, z, BPORS.Numeric.proposalLength] at hu hl ⊢
    linarith
  have hreal : m ^ (2^32 : Nat) / z ^ BPORS.Numeric.proposalLength ≤ (2 : ℝ)⁻¹ ^ 700 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_inv]
    push_cast
    nlinarith only [hlog]
  have hfinite : tailMoment ^ (2^32 : Nat) / tailBase ^ BPORS.Numeric.proposalLength ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.pow_ne_top (by unfold tailMoment; finiteness)
    · exact pow_ne_zero _ (by norm_num [tailBase])
  apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
  simpa only [tailBase, tailMoment, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, m, z] using hreal
variable {ι State Label : Type} {spec : OracleSpec ι}
noncomputable def weight (remaining : State → Nat) (state : List Label × State) : ENNReal :=
  tailBase ^ state.1.length * tailMoment ^ remaining state.2
theorem query_weight (model : ProposalModel spec State Label) (haccept : model.accept = 1024/1025)
    (remaining : State → Nat) (input : spec.Domain) (state : List Label × State)
    (hactive : model.active input state.2 = true → 0 < remaining state.2)
    (hadvance : ∀ outcome, remaining (model.advance input state.2 outcome) =
      if model.active input state.2 then remaining state.2 - 1 else remaining state.2) :
    expectedValue ((model.traced input).run state) (fun result => weight remaining result.2) =
      weight remaining state := by
  simp only [ProposalModel.traced, proposalRecordImpl, StateT.run_mk]
  by_cases ha : model.active input state.2 = true
  · rw [if_pos ha, ← PMF.monad_map_eq_map, expectedValue_map]
    simp only [weight, List.length_append, List.length_singleton, hadvance, ha, if_true]
    have hp := hactive ha
    have he : remaining state.2 = (remaining state.2 - 1) + 1 := by omega
    have hproject := congrArg
      (fun law : PMF Nat => expectedValue law (fun length => tailBase ^ length))
      (recordLengthBridge_length (model.record input state.2) model.accept model.positive model.lt_one.le)
    rw [← recordProposalBridge_length_record (model.record input state.2)
      (model.rejected input state.2) model.accept model.positive model.lt_one.le] at hproject
    simp only [← PMF.monad_map_eq_map, expectedValue_map, Function.comp_def] at hproject
    have hmoment : expectedValue
        (recordProposalBridge (model.record input state.2) (model.rejected input state.2)
          model.accept model.positive model.lt_one.le)
        (fun result => tailBase ^ (result.1.length + 1)) = tailMoment := by
      rw [hproject]
      simp only [expectedValue, PMF.probOutput_eq_apply]
      rw [proposalBlockLength_power_moment, haccept, ← tailMoment_eq]
    calc
      _ = expectedValue
          (recordProposalBridge (model.record input state.2) (model.rejected input state.2)
            model.accept model.positive model.lt_one.le)
          (fun result => tailBase ^ (result.1.length + 1)) *
          (tailBase ^ state.1.length * tailMoment ^ (remaining state.2 - 1)) := by
        rw [← expectedValue_mul_const]
        congr 1
        funext result
        rw [Nat.add_assoc, pow_add]
        ring
      _ = weight remaining state := by
        rw [hmoment]
        conv_rhs => rw [weight, he, pow_succ]
        ring
  · rw [if_neg ha, ← PMF.monad_map_eq_map, expectedValue_map]
    simp only [weight, hadvance, ha, if_false]
    exact expectedValue_const (by simp) _
theorem weight_dominates_overflow (remaining : State → Nat)
    (state : List Label × State) (cap : Nat) (hbad : cap < state.1.length) :
    1 ≤ weight remaining state / tailBase ^ cap := by
  have hnz : tailBase ^ cap ≠ 0 := pow_ne_zero _ (by norm_num [tailBase])
  have hfin : tailBase ^ cap ≠ ⊤ := ENNReal.pow_ne_top (by unfold tailBase; finiteness)
  calc
    1 = tailBase ^ cap / tailBase ^ cap := (ENNReal.div_self hnz hfin).symm
    _ ≤ _ := ENNReal.div_le_div_right (calc
      tailBase ^ cap ≤ tailBase ^ state.1.length := pow_le_pow_right₀ tailBase_one_le hbad.le
      _ ≤ weight remaining state := by
        unfold weight
        exact le_mul_of_one_le_right' (one_le_pow₀ tailMoment_one_le)) _
noncomputable def counted (model : ProposalModel spec State Label) :
    ProposalModel spec (Nat × State) Label where
  Outcome := model.Outcome
  record input state := model.record input state.2
  response := model.response
  advance input state outcome :=
    (state.1 + if model.active input state.2 then 1 else 0,
      model.advance input state.2 outcome)
  label := model.label
  active input state := model.active input state.2
  base := model.base
  accept := model.accept
  positive := model.positive
  lt_one := model.lt_one
  cap input state ha point := model.cap input state.2 ha point
noncomputable def killedWeight (limit : Nat) (state : List Label × (Nat × State)) : ENNReal :=
  if state.2.1 ≤ limit then weight (fun current : Nat × State => limit - current.1) state else 0
theorem counted_query_weight (model : ProposalModel spec State Label) (haccept : model.accept = 1024/1025)
    (limit : Nat) (input : spec.Domain) (state : List Label × (Nat × State)) :
    expectedValue (((counted model).traced input).run state)
      (fun result => killedWeight limit result.2) ≤ killedWeight limit state := by
  by_cases ha : model.active input state.2.2 = true
  · by_cases hroom : state.2.1 < limit
    · have hrewrite : expectedValue (((counted model).traced input).run state)
          (fun result => killedWeight limit result.2) =
        expectedValue (((counted model).traced input).run state)
          (fun result => weight (fun current : Nat × State => limit-current.1) result.2) := by
        simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk, ha, if_true,
          ← PMF.monad_map_eq_map, expectedValue_map, killedWeight, show state.2.1+1 ≤ limit by omega]
      rw [hrewrite, query_weight (counted model) haccept _ input state
        (fun _ => by omega) (fun _ => by simp only [counted, ha, if_true]; omega)]
      simp [killedWeight, Nat.le_of_lt hroom]
    · have hnext : ¬state.2.1 + 1 ≤ limit := by omega
      simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk, ha, if_true,
        ← PMF.monad_map_eq_map, expectedValue_map, killedWeight, hnext, if_false]
      rw [expectedValue_const (by simp)]
      exact bot_le
  · simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk, ha, Bool.false_eq_true, if_false,
      ← PMF.monad_map_eq_map, expectedValue_map, killedWeight, Nat.add_zero, weight]
    rw [expectedValue_const (by simp)]
attribute [local irreducible] ProposalModel.traced counted
theorem counted_execution_weight {Result : Type} (model : ProposalModel spec State Label)
    (haccept : model.accept = 1024/1025) (limit : Nat)
    (computation : OracleComp spec Result) (state : List Label × (Nat × State)) :
    expectedValue ((simulateQ (counted model).traced computation).run state)
      (fun result => killedWeight limit result.2) ≤ killedWeight limit state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, expectedValue, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind]
      apply le_trans ?_ (counted_query_weight model haccept limit input state)
      apply expectedValue_mono
      intro middle
      exact ih middle.1 middle.2
theorem counted_overflow_bound {Result : Type} (model : ProposalModel spec State Label)
    (haccept : model.accept = 1024/1025) (limit cap : Nat)
    (computation : OracleComp spec Result) (state : State) :
    Pr[fun result => result.2.2.1 ≤ limit ∧ cap < result.2.1.length |
      (simulateQ (counted model).traced computation).run ([], 0, state)] ≤
      tailMoment ^ limit / tailBase ^ cap := by
  classical
  rw [← expectedValue_ite_one]
  calc
    _ ≤ expectedValue ((simulateQ (counted model).traced computation).run ([],0,state))
        (fun result => killedWeight limit result.2 / tailBase ^ cap) := by
      apply expectedValue_mono
      intro result
      split
      · rename_i h
        rw [killedWeight, if_pos h.1]
        exact weight_dominates_overflow _ _ cap h.2
      · exact bot_le
    _ = expectedValue ((simulateQ (counted model).traced computation).run ([],0,state))
        (fun result => killedWeight limit result.2) / tailBase ^ cap := by
      simp only [div_eq_mul_inv, expectedValue_mul_const]
    _ ≤ killedWeight limit ([], (0, state)) / tailBase ^ cap :=
      ENNReal.div_le_div_right (counted_execution_weight model haccept limit computation ([],0,state)) _
    _ = _ := by simp [killedWeight, weight]
theorem full_trace_overflow_bound {Result : Type} (model : ProposalModel spec State Label)
    (haccept : model.accept = 1024/1025) (computation : OracleComp spec Result) (state : State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted model).traced computation).run ([],0,state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 :=
  (counted_overflow_bound model haccept _ _ computation state).trans initial_bound
attribute [local semireducible] ProposalModel.traced counted
theorem counted_rejected (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : Nat × State) :
    (counted model).rejected input state = model.rejected input state.2 := rfl
theorem counted_query_trace_erasure (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : List Label × (Nat × State)) :
    Prod.map id (fun current => (current.1,current.2.2)) <$>
      (((counted model).traced input).run state) =
      (model.traced input).run (state.1,state.2.2) := by
  simp only [ProposalModel.traced, proposalRecordImpl, StateT.run_mk]
  change PMF.map _ (if model.active input state.2.2 then _ else _) = _
  by_cases ha : model.active input state.2.2 = true
  · simp only [ha, if_true, PMF.map_comp, counted_rejected, counted]
    rfl
  · simp only [ha, Bool.false_eq_true, if_false, PMF.map_comp, counted]
    rfl
theorem counted_trace_erasure {Result : Type} (model : ProposalModel spec State Label)
    (computation : OracleComp spec Result) (state : List Label × (Nat × State)) :
    Prod.map id (fun current => (current.1,current.2.2)) <$>
      (simulateQ (counted model).traced computation).run state =
      (simulateQ model.traced computation).run (state.1,state.2.2) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (fun current => (current.1,current.2.2))
    (counted_query_trace_erasure model) computation state
theorem counted_source_erasure {Result : Type} (model : ProposalModel spec State Label)
    (computation : OracleComp spec Result) (state : List Label × (Nat × State)) :
    Prod.map id (fun current => current.2.2) <$>
      (simulateQ (counted model).traced computation).run state =
      (simulateQ model.original computation).run state.2.2 := by
  have h := congrArg (fun law => Prod.map id Prod.snd <$> law)
    (counted_trace_erasure model computation state)
  rw [model.traced_erasure] at h
  change (fun a : Result × (List Label × (Nat × State)) => (a.1,a.2.2.2)) <$> _ = _
  simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq] using h
theorem signing_trace_overflow {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced program).run ([],0,state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 :=
  full_trace_overflow_bound (LazyPrivate.proposalModel budget hbudget) rfl program state
theorem signing_trace_erasure {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Prod.map id (fun current => current.2.2) <$>
      (simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced program).run ([],0,state) =
      (liftM (LazyPrivate.run (simulateQ LazyPrivate.interactionSource program) state) :
        PMF (Result × LazyPrivate.State)) := by
  rw [counted_source_erasure, LazyPrivate.proposal_execution_erasure]
def logFragment : (input : LazyPrivate.Interaction.Domain) →
    LazyPrivate.Interaction.Range input → QueryLog Requests
  | .inl _, _ => []
  | .inr request, response => [⟨request,response⟩]
def logging : QueryImpl LazyPrivate.Interaction
    (WriterT (QueryLog Requests) (OracleComp LazyPrivate.Interaction)) :=
  QueryImpl.withTraceAppend (fun input => LazyPrivate.Interaction.query input) logFragment
def logged {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    OracleComp LazyPrivate.Interaction (Result × QueryLog Requests) :=
  (simulateQ logging program).run
theorem logged_pure {Result : Type} (value : Result) : logged (pure value) = pure (value,[]) := rfl
theorem logged_query_bind {Result : Type} (input : LazyPrivate.Interaction.Domain)
    (next : LazyPrivate.Interaction.Range input → OracleComp LazyPrivate.Interaction Result) :
    logged (LazyPrivate.Interaction.query input >>= next) = (do
      let response ← LazyPrivate.Interaction.query input
      let result ← logged (next response)
      pure (result.1, logFragment input response ++ result.2)) := by
  simp [logged, logging, QueryImpl.withTraceAppend_apply]
theorem counted_query_count (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : List Label × (Nat × State))
    (result : spec.Range input × (List Label × (Nat × State)))
    (hr : result ∈ (((counted model).traced input).run state).support) :
    result.2.2.1 = state.2.1 + if model.active input state.2.2 then 1 else 0 := by
  simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk] at hr
  by_cases ha : model.active input state.2.2 = true
  · simp only [ha, if_true, PMF.support_map, Set.mem_image] at hr
    obtain ⟨outcome, _, rfl⟩ := hr
    simp only [ha, Bool.false_eq_true, if_true, if_false]
  · simp only [ha, Bool.false_eq_true, if_false, PMF.support_map, Set.mem_image] at hr
    obtain ⟨outcome, _, rfl⟩ := hr
    simp only [ha, Bool.false_eq_true, if_true, if_false]
theorem signing_count_le_fragment (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : LazyPrivate.Interaction.Domain) (state : List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State))
    (result : LazyPrivate.Interaction.Range input × (List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State)))
    (hr : result ∈ (((counted (LazyPrivate.proposalModel budget hbudget)).traced input).run state).support) :
    result.2.2.1 ≤ state.2.1 + (logFragment input result.1).length := by
  rw [counted_query_count _ input state result hr]
  cases input with
  | inl input => simp [LazyPrivate.proposalModel, LazyPrivate.interactionActive, logFragment]
  | inr request => simp only [logFragment, List.length_singleton]; split <;> omega
theorem signing_count_le_log {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result)
    (state : List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State))
    (result : (Result × QueryLog Requests) × (List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State)))
    (hr : result ∈ ((simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
      (logged program)).run state).support) :
    result.2.2.1 ≤ state.2.1 + result.1.2.length := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [logged_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [logged_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      have hstep := signing_count_le_fragment budget hbudget input state middle hm
      rw [simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨last, hl, hr⟩ := hr
      have hrest := ih middle.1 middle.2 last hl
      rw [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      simp only [List.length_append]
      omega
theorem signing_log_overflow {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
        (logged program)).run ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  apply le_trans ?_ (signing_trace_overflow budget hbudget (logged program) state)
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ ((simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
      (logged program)).run ([],0,state)).support
  · by_cases hb : result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length
    · have hcount := signing_count_le_log budget hbudget program ([],0,state) result hr
      have hc : result.2.2.1 ≤ result.1.2.length := by simpa using hcount
      simp only [hb, if_true, show result.2.2.1 ≤ 2^32 ∧
        BPORS.Numeric.proposalLength < result.2.1.length from ⟨hc.trans hb.1,hb.2⟩, le_refl]
    · simp only [hb, if_false, zero_le]
  · have hz : ((simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
        (logged program)).run ([],0,state)) result = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hr
    simp only [PMF.probOutput_eq_apply, hz, ite_self, le_refl]
theorem source_proposal_overflow {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (LazyPrivate.proposalModel budget hbudget).traced (logged program)).run ([],state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 := by
  rw [← counted_trace_erasure (LazyPrivate.proposalModel budget hbudget) (logged program) ([],0,state),
    probEvent_map]
  exact signing_log_overflow budget hbudget program state
theorem logged_source {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    simulateQ LazyPrivate.interactionSource (logged program) =
      (simulateQ
        ((fun input => liftM (forwardWorld input) :
          QueryImpl SphincsSecurity.OracleWorld (WriterT (QueryLog Requests) M)) + signingOracle)
        program).run := by
  rw [logged, QueryImpl.simulateQ_writerTMapBase_run]
  congr 2
  funext input
  cases input <;>
    simp [QueryImpl.writerTMapBase, logging, QueryImpl.withTraceAppend_apply,
      logFragment, LazyPrivate.interactionSource, signingOracle]
  · rfl
  · apply WriterT.ext
    simp
end SigGolfCandidate.T3.Security.ProposalOverflow
section
namespace SigGolfCandidate.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem encodingInput_injective {lay lay' : Layer} {tree tree' leaf leaf' : Nat}
    {message message' : Digest} {counter counter' : BitVec 32}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (he : encodingInput lay tree leaf message counter =
      encodingInput lay' tree' leaf' message' counter') :
    lay=lay' ∧ tree=tree' ∧ leaf=leaf' ∧ message=message' ∧ counter=counter' := by
  unfold encodingInput at he
  obtain ⟨hh,hc⟩ := List.append_inj he (by simp only [List.length_append,bytesLE_length])
  obtain ⟨hm,hh⟩ := List.append_inj hh (by simp only [bytesLE_length])
  obtain ⟨a,b,c⟩ := rowTweak_injective hl hr hl' hr' (bytesLE_injective hh)
  exact ⟨a,b,c,bytesLE_injective hm,bytesLE_injective hc⟩
theorem encodingTrial_coordinates {lay lay' : Layer} {tree tree' leaf leaf' : Nat}
    {message message' : Digest} {counter counter' : Nat}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (hc : counter < 2^32) (hc' : counter' < 2^32)
    (he : encodingTrial lay tree leaf message counter =
      encodingTrial lay' tree' leaf' message' counter') :
    lay=lay' ∧ tree=tree' ∧ leaf=leaf' ∧ message=message' ∧ counter=counter' := by
  have he := pad64_inj_of_length (by simp [encodingInput,bytesLE_length]) he
  obtain ⟨a,b,c,d,e⟩ := encodingInput_injective hl hr hl' hr' he
  refine ⟨a,b,c,d,?_⟩
  have e := congrArg BitVec.toNat e
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hc'] using e
theorem digestTrial_coordinates {rho rho' : Digest} {message message' : Message}
    {counter counter' : Nat} (hc : counter<2^32) (hc' : counter'<2^32)
    (he : digestTrial rho message counter=digestTrial rho' message' counter') :
    rho=rho' ∧ message=message' ∧ counter=counter' := by
  have he := pad64_inj_of_length (by simp [digestInput,bytesLE_length]) he
  obtain ⟨a,b,c⟩ := digestInput_injective he
  refine ⟨a,b,?_⟩
  have c := congrArg BitVec.toNat c
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hc'] using c
def queryHeader (input : HashInput) : HashInput := (input.drop 16).take 16
theorem header_tag (tag lay tree position index : Nat) :
    ((header tag lay tree position index).toNat/256)%256=tag%256 := by
  rw [header_toNat]
  have ht := Nat.mod_lt tag (by decide : 0<256)
  have hw := nodeWord_lt tag position index
  norm_num only [Nat.reducePow] at *
  split_ifs <;> omega
theorem header_ne_of_tag {tag tag' lay lay' tree tree' position position' index index' : Nat}
    (h : tag%256 ≠ tag'%256) :
    header tag lay tree position index ≠ header tag' lay' tree' position' index' := by
  intro he
  have ht := congrArg (fun h : BitVec 128 => (h.toNat/256)%256) he
  exact h (by simpa only [header_tag] using ht)
theorem header_layer (tag lay tree position index : Nat) :
    ((header tag lay tree position index).toNat/65536)%256=lay%256 := by
  rw [header_toNat]
  have ht := Nat.mod_lt tag (by decide : 0<256)
  have hl := Nat.mod_lt lay (by decide : 0<256)
  have hw := nodeWord_lt tag position index
  norm_num only [Nat.reducePow] at *
  split_ifs <;> omega
theorem header_ne_of_layer {tag tag' lay lay' tree tree' position position' index index' : Nat}
    (h : lay%256 ≠ lay'%256) :
    header tag lay tree position index ≠ header tag' lay' tree' position' index' := by
  intro he
  have hl := congrArg (fun h : BitVec 128 => (h.toNat/65536)%256) he
  exact h (by simpa only [header_layer] using hl)
theorem queryHeader_padded (front back : HashInput) (hprefix : front.length=16)
    (h : BitVec 128) : queryHeader (pad64 (front ++ bytesLE 16 h ++ back))=bytesLE 16 h := by
  simp [queryHeader,pad64,List.append_assoc,hprefix,bytesLE_length]
theorem padded_headers_ne (leftPrefix rightPrefix leftSuffix rightSuffix : HashInput)
    (hl : leftPrefix.length=16) (hr : rightPrefix.length=16)
    (tag tag' lay lay' tree tree' position position' index index' : Nat)
    (htags : tag%256 ≠ tag'%256) :
    pad64 (leftPrefix ++ bytesLE 16 (header tag lay tree position index) ++ leftSuffix) ≠
      pad64 (rightPrefix ++ bytesLE 16 (header tag' lay' tree' position' index') ++ rightSuffix) := by
  intro he
  have he := congrArg queryHeader he
  rw [queryHeader_padded _ _ hl,queryHeader_padded _ _ hr] at he
  exact header_ne_of_tag htags (bytesLE_injective he)
@[simp] theorem queryHeader_encoding (lay : Layer) (tree leaf : Nat) (message : Digest)
    (counter : Nat) : queryHeader (encodingTrial lay tree leaf message counter) =
      bytesLE 16 (rowTweak lay tree leaf) := by
  simp [queryHeader,encodingTrial,encodingInput,pad64,List.append_assoc,bytesLE_length]
@[simp] theorem queryHeader_digest (rho : Digest) (message : Message) (counter : Nat) :
    queryHeader (digestTrial rho message counter) =
      bytesLE 16 (digestHeader (BitVec.ofNat 32 counter)) := by
  simp [queryHeader,digestTrial,digestInput,pad64,List.append_assoc,bytesLE_length]
theorem queryHeader_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    queryHeader (pad64 (leafInput lay tree leaf ends)) = bytesLE 16 (leafTweak lay tree leaf) := by
  unfold leafInput
  split
  · exact queryHeader_padded zero16 _ (by simp [zero16]) _
  · exact queryHeader_padded _ _ (bytesLE_length ..) _
theorem encodingTrial_ne_digestTrial (lay : Layer) (tree leaf : Nat) (message : Digest)
    (counter : Nat) (rho : Digest) (msg : Message) (ctr : Nat) :
    encodingTrial lay tree leaf message counter ≠ digestTrial rho msg ctr := by
  intro he
  have he := congrArg queryHeader he
  simp only [queryHeader_encoding,queryHeader_digest] at he
  exact (digestHeader_ne_rowTweak _ lay tree leaf) (bytesLE_injective he).symm
def routedTree (lay : Layer) (r : Nat) : Nat := r / 2 ^ height lay
def routedLeaf (lay : Layer) (r : Nat) : Nat := r % 2 ^ height lay
theorem routedLeaf_lt (lay : Layer) (r : Nat) : routedLeaf lay r < 2 ^ height lay := Nat.mod_lt _ (by positivity)
theorem routed_eq (lay : Layer) (r : Nat) : routedTree lay r * 2 ^ height lay + routedLeaf lay r = r := by
  unfold routedTree routedLeaf; rw [Nat.mul_comm]; exact Nat.div_add_mod r _
theorem routedTree_of (lay : Layer) {tree leaf : Nat} (hl : leaf < 2 ^ height lay) :
    routedTree lay (tree * 2 ^ height lay + leaf) = tree := by
  unfold routedTree
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hl, Nat.zero_add]
theorem routedLeaf_of (lay : Layer) {tree leaf : Nat} (hl : leaf < 2 ^ height lay) :
    routedLeaf lay (tree * 2 ^ height lay + leaf) = leaf := by
  unfold routedLeaf
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
abbrev EncodingFamily := Layer × Fin (2^32) × Digest
abbrev DigestFamily := Digest × Message
abbrev EncodingKey := EncodingFamily × Fin (2^22)
abbrev DigestKey := DigestFamily × Fin (2^20)
abbrev SearchKey := EncodingKey ⊕ DigestKey
def encodingQuery (key : EncodingKey) : HashInput :=
  encodingTrial key.1.1 (routedTree key.1.1 key.1.2.1) (routedLeaf key.1.1 key.1.2.1) key.1.2.2 key.2
def digestQuery (key : DigestKey) : HashInput := digestTrial key.1.1 key.1.2 key.2
def searchQuery : SearchKey → HashInput := Sum.elim encodingQuery digestQuery
theorem encodingQuery_injective : Function.Injective encodingQuery := by
  rintro ⟨⟨lay,r,message⟩,counter⟩ ⟨⟨lay',r',message'⟩,counter'⟩ he
  obtain ⟨a,b,c,d,e⟩ := encodingTrial_coordinates (routedLeaf_lt lay r)
    (by rw [routed_eq]; exact r.isLt) (routedLeaf_lt lay' r') (by rw [routed_eq]; exact r'.isLt)
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  subst a
  have hr : r = r' := Fin.ext (by rw [← routed_eq lay r.val, ← routed_eq lay r'.val, b, c])
  have e := Fin.ext e
  cases hr; cases d; cases e; rfl
theorem digestQuery_injective : Function.Injective digestQuery := by
  rintro ⟨⟨rho,msg⟩,counter⟩ ⟨⟨rho',msg'⟩,counter'⟩ he
  obtain ⟨a,b,c⟩ := digestTrial_coordinates
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  have c := Fin.ext c
  cases a; cases b; cases c; rfl
theorem searchQuery_injective : Function.Injective searchQuery := by
  intro left right he
  cases left with
  | inl l =>
    cases right with
    | inl r => exact congrArg Sum.inl (encodingQuery_injective he)
    | inr r => exact False.elim (encodingTrial_ne_digestTrial _ _ _ _ _ _ _ _ he)
  | inr l =>
    cases right with
    | inl r => exact False.elim (encodingTrial_ne_digestTrial _ _ _ _ _ _ _ _ he.symm)
    | inr r => exact congrArg Sum.inr (digestQuery_injective he)
end SigGolfCandidate.T3.QuerySpace
end
section
namespace SigGolfCandidate.T3.Presampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open QuerySpace
abbrev HashInput := SphincsSecurity.HashInput
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[irreducible] noncomputable def tableSampler : SampleableType (SearchKey → HashOutput) :=
  Derivation.outputSampler SearchKey
noncomputable local instance : SampleableType (SearchKey → HashOutput) := tableSampler
noncomputable def preparedCache (outputs : SearchKey → HashOutput) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ searchQuery outputs
theorem preparedCache_apply (outputs : SearchKey → HashOutput) (key : SearchKey) :
    preparedCache outputs (searchQuery key)=some (outputs key) :=
  cacheTable_apply ∅ searchQuery searchQuery_injective outputs key
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (SearchKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' (preparedCache outputs)] := by
  let : SampleableType (SearchKey → SphincsSecurity.HashOutput) := tableSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (SearchKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) searchQuery)
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) searchQuery)).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec)) (queryTable (R := SphincsSecurity.HashOutput) searchQuery))
  rw [evalDist_presample_computation (realize secret program) preparation ∅,hprep,
    evalSPMF_bind,evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput) searchQuery searchQuery_injective
      ∅ (fun _ => rfl)]
  simp only [evalSPMF_map,bind_map_left]
  rw [evalSPMF_bind]
  congr 1
noncomputable def tableAnswers (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) : Correctness.Answers
  | .inl (.inr input) => (preparedCache outputs input).getD (fallback (.inl (.inr input)))
  | .inl (.inl input) => fallback (.inl (.inl input))
  | .inr input => fallback (.inr input)
theorem tableAnswers_apply (outputs : SearchKey → HashOutput) (fallback : Correctness.Answers)
    (key : SearchKey) : tableAnswers outputs fallback (.inl (.inr (searchQuery key)))=outputs key := by
  simp only [tableAnswers,preparedCache_apply,Option.getD_some]
theorem eval_shortHash (answers : Correctness.Answers) (input : HashInput) :
    evalWithAnswerFn answers (shortHash input) =
      (answers (.inl (.inr (pad64 input)))).extractLsb' 0 128 := rfl
theorem eval_digest (answers : Correctness.Answers) (rho : Digest) (message : Message)
    (counter : BitVec 32) : evalWithAnswerFn answers (digest rho message counter) =
      answers (.inl (.inr (pad64 (digestInput rho message counter)))) := rfl
theorem uniform_table_forall {J : Type} [Fintype J] [DecidableEq J] [SampleableType (J → HashOutput)]
    (p : HashOutput → Prop) :
    Pr[fun outputs : J → HashOutput => ∀ j,p (outputs j) | ($ᵗ (J → HashOutput) : ProbComp _)] =
      Pr[p | ($ᵗ HashOutput : ProbComp _)] ^ Fintype.card J := by
  classical
  rw [probEvent_uniformSample,probEvent_uniformSample]
  have hc : (Finset.univ.filter fun outputs : J → HashOutput => ∀ j,p (outputs j)).card =
      (Finset.univ.filter p).card ^ Fintype.card J := by
    rw [← Fintype.card_subtype,Fintype.card_congr
      (Equiv.subtypePiEquivPi (p := fun (_ : J) (x : HashOutput) => p x)),Fintype.card_pi]
    simp only [Fintype.card_subtype,Finset.prod_const,Finset.card_univ]
  rw [hc,Fintype.card_fun,Nat.cast_pow,Nat.cast_pow]
  simp only [div_eq_mul_inv,mul_pow,ENNReal.inv_pow]
theorem uniform_table_restriction_failure {J : Type} [Fintype J]
    [DecidableEq J] [SampleableType (J → HashOutput)] (e : J → SearchKey) (he : Function.Injective e)
    (p : HashOutput → Prop) :
    Pr[fun outputs : SearchKey → HashOutput => ∀ j,p (outputs (e j)) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
      Pr[p | ($ᵗ HashOutput : ProbComp _)] ^ Fintype.card J := by
  have h := evalSPMF_uniformSample_map_comp_injective (R := HashOutput) he
  have hp := congrArg (fun law => probEvent law (fun outputs : J → HashOutput => ∀ j,p (outputs j))) h
  simpa only [probEvent_evalSPMF,bind_pure_comp,probEvent_map,Function.comp_def,uniform_table_forall] using hp
theorem counterSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (family : EncodingFamily) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (counterSearch family.1 (QuerySpace.routedTree family.1 family.2.1) (QuerySpace.routedLeaf family.1 family.2.1) family.2.2 0
        counterLimit)=none ↔
    ∀ c : Fin (2^22), Sampling.encodingDecode family.1 (outputs (.inl (family,c)))=none := by
  rw [Correctness.counterSearch_none_iff]
  have hv (c : Nat) (hc : c<counterLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (shortHash (encodingInput family.1 (QuerySpace.routedTree family.1 family.2.1) (QuerySpace.routedLeaf family.1 family.2.1)
          family.2.2 (BitVec.ofNat 32 (0+c)))) = (outputs (.inl (family,⟨c,hc⟩))).extractLsb' 0 128 := by
    rw [eval_shortHash]
    have hinput : pad64 (encodingInput family.1 (QuerySpace.routedTree family.1 family.2.1) (QuerySpace.routedLeaf family.1 family.2.1)
        family.2.2 (BitVec.ofNat 32 (0+c))) = searchQuery (.inl (family,⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inl,encodingQuery,Sampling.encodingTrial,Nat.zero_add]
    rw [hinput,tableAnswers_apply]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c,hc⟩
theorem digestSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (family : DigestFamily) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (digestSearch family.1 family.2 0 attemptLimit)=none ↔
    ∀ c : Fin (2^20), Sampling.digestDecode (outputs (.inr (family,c)))=none := by
  rw [Correctness.digestSearch_none_iff]
  have hv (c : Nat) (hc : c<attemptLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (digest family.1 family.2 (BitVec.ofNat 32 (0+c))) = outputs (.inr (family,⟨c,hc⟩)) := by
    rw [eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0+c))) =
        searchQuery (.inr (family,⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inr,digestQuery,Sampling.digestTrial,Nat.zero_add]
    rw [hinput,tableAnswers_apply]
  have hd (value : HashOutput) : Sampling.digestDecode value=none ↔ digestAdmissible value=false := by
    simp [Sampling.digestDecode]
  constructor
  · intro h c
    rw [hd]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)
theorem counterSearch_table_failure (fallback : Correctness.Answers) (family : EncodingFamily) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (counterSearch family.1 (QuerySpace.routedTree family.1 family.2.1) (QuerySpace.routedLeaf family.1 family.2.1) family.2.2 0
        counterLimit)=none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass (Sampling.encodingDecode family.1)^counterLimit := by
  simp_rw [counterSearch_none_table]
  have h := uniform_table_restriction_failure (fun c : Fin (2^22) => .inl (family,c))
    (fun _ _ h => congrArg Prod.snd (Sum.inl.inj h)) (fun x => Sampling.encodingDecode family.1 x=none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent,Fintype.card_fin,counterLimit,
    HashOutput,SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits] using h
theorem digestSearch_table_failure (fallback : Correctness.Answers) (family : DigestFamily) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (digestSearch family.1 family.2 0 attemptLimit)=none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass Sampling.digestDecode^attemptLimit := by
  simp_rw [digestSearch_none_table]
  have h := uniform_table_restriction_failure (fun c : Fin (2^20) => .inr (family,c))
    (fun _ _ h => congrArg Prod.snd (Sum.inr.inj h)) (fun x => Sampling.digestDecode x=none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent,Fintype.card_fin,attemptLimit,
    HashOutput,SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits] using h
end SigGolfCandidate.T3.Presampling
end
section
noncomputable section
end
end
section
namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def signForest (index : Nat) (chosen : List Selection) :
    M (List Digest × List Digest × List Digest) :=
  (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])
theorem eval_signForest (answers : Answers) (index : Nat) (chosen : List Selection) :
    evalWithAnswerFn answers (signForest index chosen)=
      (forestOpenPrefix answers index chosen 7,forestProofPrefix answers index chosen 7,
        forestRoots answers index 7) :=
  eval_forestRows answers index chosen
def assembledSignature (rho : Digest) (state : List Digest × List Digest × List Digest)
    (pieces : List Pieces) : Signature :=
  ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (pieces.getD lay.val ([],[]))⟩
@[simp] theorem assembledSignature_rho (rho : Digest)
    (state : List Digest × List Digest × List Digest) (pieces : List Pieces) :
    (assembledSignature rho state pieces).rho=rho := rfl
theorem signPayload_eq (cache : Cache) (message : Message) : signPayload cache message=(do
    let rho ← privateNonce message
    let some (_,output) ← digestSearch rho message 0 attemptLimit | pure none
    let state ← signForest (output.toNat%2^31) (selections output)
    let root ← forestPk (output.toNat%2^31) state.2.2
    let some pieces ← signLayers cache (output.toNat%2^31) 4 root | pure none
    pure (some (assembledSignature rho state pieces))) := rfl
theorem assembled_forest_recovery (answers : Answers) (rho : Digest) (output : HashOutput)
    (pieces : List Pieces) (hadm : admissible (selections output)=true) :
    evalWithAnswerFn answers (recoverFts
      (assembledSignature rho (evalWithAnswerFn answers
        (signForest (output.toNat%2^31) (selections output))) pieces)
      (output.toNat%2^31) (selections output))=
      some (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
        (forestRoots answers (output.toNat%2^31) 7))) := by
  rw [eval_signForest]
  exact recoverFts_from_signer_lists answers _ (output.toNat%2^31) output hadm
    (fun _ => rfl) (fun _ => rfl)
end SigGolfCandidate.T3.Correctness
end
section
namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
abbrev EncodingFamily := QuerySpace.EncodingFamily
abbrev DigestFamily := Digest × Message
def EncodingSearchesSucceed (answers : Answers) : Prop :=
  ∀ family : EncodingFamily, ∃ found,
    evalWithAnswerFn answers (counterSearch family.1 (QuerySpace.routedTree family.1 family.2.1)
      (QuerySpace.routedLeaf family.1 family.2.1) family.2.2 0 counterLimit)=some found
def DigestSearchesSucceed (answers : Answers) : Prop :=
  ∀ family : DigestFamily, ∃ found,
    evalWithAnswerFn answers (digestSearch family.1 family.2 0 attemptLimit)=some found
def SearchesSucceed (answers : Answers) : Prop :=
  DigestSearchesSucceed answers ∧ EncodingSearchesSucceed answers
theorem encodingFamily_card : Fintype.card EncodingFamily=2^162 := by
  norm_num [EncodingFamily,QuerySpace.EncodingFamily,Layer,Fintype.card_prod,Fintype.card_bitVec]
theorem encodingFamily_card_le : (Fintype.card EncodingFamily : ENNReal) ≤ 2^173 := by
  rw [encodingFamily_card, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)
theorem digestFamily_card : Fintype.card DigestFamily=2^384 := by
  calc
    Fintype.card DigestFamily = (2 : Nat)^128 * (2 : Nat)^256 := by
      simp only [DigestFamily,Digest,Message,Fintype.card_prod,Fintype.card_bitVec]
    _ = (2 : Nat)^(128+256) := (pow_add (2 : Nat) 128 256).symm
    _ = (2 : Nat)^384 := rfl
theorem route_tree_bound (index : Nat) (lay : Layer) (hindex : index < 2^31) :
    (route index lay).2 < 2^31 := by
  exact lt_of_le_of_lt (Nat.div_le_self _ _) hindex
theorem route_leaf_4096 (index : Nat) (lay : Layer) : (route index lay).1 < 4096 := by
  have h := route_leaf_bound index lay
  fin_cases lay <;> norm_num [height] at h ⊢ <;> omega
theorem encodingSearchesSucceed_at_route (answers : Answers)
    (hgood : EncodingSearchesSucceed answers) (index : Nat) (hindex : index < 2^31)
    (lay : Layer) (message : Digest) : ∃ found,
    evalWithAnswerFn answers (counterSearch lay (route index lay).2
      (route index lay).1 message 0 counterLimit)=some found := by
  have hl := route_leaf_bound index lay
  have hr : (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
    fin_cases lay <;> simp [route, height] <;> omega
  obtain ⟨found, hf⟩ := hgood (lay,⟨_,hr⟩,message)
  refine ⟨found, ?_⟩
  simpa only [QuerySpace.routedTree_of lay hl, QuerySpace.routedLeaf_of lay hl] using hf
theorem topSearchesSucceed_of (answers : Answers) (hgood : EncodingSearchesSucceed answers) :
    TopSearchesSucceed answers :=
  fun index hindex m => encodingSearchesSucceed_at_route answers hgood index hindex (Fin.ofNat 4 0) m
theorem signLayers_succeeds (answers : Answers) (cache : Cache) (index : Nat)
    (hindex : index < 2^31) (hgood : EncodingSearchesSucceed answers) :
    ∀ n message, ∃ pieces,
      evalWithAnswerFn answers (signLayers cache index n message)=some pieces := by
  intro n
  induction n with
  | zero => intro message;exact ⟨[],rfl⟩
  | succ n ih =>
      intro message
      obtain ⟨⟨counter,digits⟩,hs⟩ :=
        encodingSearchesSucceed_at_route answers hgood index hindex (Fin.ofNat 4 n) message
      simp only [signLayers,evalWithAnswerFn_bind,hs]
      by_cases hn : n=0
      · simp only [hn,ite_true,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
        exact ⟨_,rfl⟩
      · simp only [hn,ite_false,evalWithAnswerFn_bind]
        obtain ⟨previous,hp⟩ := ih
          ((((evalWithAnswerFn answers (buildTree (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits)).1).getD
            (height (Fin.ofNat 4 n)) []).getD 0 0)
        simp only [hp,evalWithAnswerFn_pure]
        exact ⟨_,rfl⟩
theorem signPayload_succeeds (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceed answers) :
    ∃ sig,evalWithAnswerFn answers (signPayload cache message)=some sig := by
  obtain ⟨⟨counter,output⟩,hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message),message)
  rw [signPayload_eq]
  simp only [evalWithAnswerFn_bind,hd,eval_signForest]
  obtain ⟨pieces,hp⟩ := signLayers_succeeds answers cache (output.toNat%2^31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
      (forestRoots answers (output.toNat%2^31) 7)))
  simp only [hp,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩
def SigningComplete (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (sign keys.2 message)=some sig ∧
    evalWithAnswerFn answers (expand message keys.1 sig)=some w ∧
    evalWithAnswerFn answers (verify message keys.1 w)=true
def RealizedSigningComplete (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (realize secret (sign keys.2 message))=some sig ∧
    evalWithAnswerFn answers (realize secret (expand message keys.1 sig))=some w ∧
    evalWithAnswerFn answers (realize secret (verify message keys.1 w))=true
end SigGolfCandidate.T3.Correctness
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass failMass_eq_probEvent)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable def encodingRate (lay : Layer) : ℝ := (EncodingCounting.acceptedCount lay : ℝ)/2^128
theorem encodingRate_bounds (lay : Layer) : 1/7400 ≤ encodingRate lay ∧ encodingRate lay ≤ 1 := by
  fin_cases lay <;> norm_num [encodingRate,EncodingCounting.acceptedCount]
theorem encodingRate_cast (lay : Layer) :
    ENNReal.ofReal (encodingRate lay)=(EncodingCounting.acceptedCount lay : ENNReal)/2^128 := by
  rw [encodingRate,ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num)]
  simp
theorem failMass_eq_one_sub_accept {β : Type} (decoder : HashOutput → Option β) :
    failMass decoder=1-Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [failMass_eq_probEvent]
  have h := Sampling.probEvent_not (fun answer => (decoder answer).isSome)
  simp only [probEvent_uniformSample] at h ⊢
  simpa only [HashOutput,SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits,
    Bool.not_eq_true,Option.isSome_eq_false_iff,Option.isNone_iff_eq_none] using h
theorem encoding_failMass (lay : Layer) :
    failMass (Sampling.encodingDecode lay)=ENNReal.ofReal (1-encodingRate lay) := by
  rw [failMass_eq_one_sub_accept,EncodingCounting.encoding_uniform_probability,← encodingRate_cast]
  rw [ENNReal.ofReal_sub 1 (by linarith [(encodingRate_bounds lay).1])]
  simp
theorem rejection_power_le (p : ℝ) (hp : p ≤ 1) (trials bits : Nat)
    (h : bits * Real.log 2 ≤ trials*p) : (1-p)^trials ≤ 1/(2 : ℝ)^bits := by
  calc
    (1-p)^trials ≤ (Real.exp (-p))^trials :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) _
    _ = Real.exp (-(trials*p)) := by rw [← Real.exp_nat_mul];congr 1;ring
    _ ≤ Real.exp (-(bits*Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/(2 : ℝ)^bits := by
      rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      simp [one_div]
@[simp] theorem ofReal_inv_two_pow (n : Nat) :
    ENNReal.ofReal (1/(2 : ℝ)^n)=1/(2 : ENNReal)^n := by
  rw [ENNReal.ofReal_div_of_pos (show 0 < (2 : ℝ)^n by positivity),
    ENNReal.ofReal_one,ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),ENNReal.ofReal_ofNat]
theorem encoding_failure_power (lay : Layer) :
    failMass (Sampling.encodingDecode lay)^counterLimit ≤ 1/(2 : ENNReal)^800 := by
  rw [encoding_failMass,← ENNReal.ofReal_pow (by linarith [(encodingRate_bounds lay).2])]
  have hreal := rejection_power_le (encodingRate lay) (encodingRate_bounds lay).2 counterLimit 800
    (by have hl := Real.log_two_lt_d9;have hp := (encodingRate_bounds lay).1
        change (800 : ℝ)*Real.log 2 ≤ 4194304*encodingRate lay
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
theorem counterSearch_failure_le (secret : BitVec 256) (lay : Layer)
    (tree leaf : Nat) (message : Digest) (cache : Sampling.RCache)
    (hfresh : ∀ c,0 ≤ c → c < 2^32 → cache (Sampling.encodingTrial lay tree leaf message c)=none) :
    Pr[fun result => result.1=none |
      Sampling.roRun secret (counterSearch lay tree leaf message 0 counterLimit) cache] ≤
      1/(2 : ENNReal)^800 := by
  exact (Sampling.counterSearch_failure secret lay tree leaf message counterLimit 0
    (by decide) cache hfresh).trans (encoding_failure_power lay)
theorem digest_failure_power_of_acceptance (p : ℝ) (hp : 1/3300 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal p) :
    failMass Sampling.digestDecode^attemptLimit ≤ 1/(2 : ENNReal)^450 := by
  have hm : failMass Sampling.digestDecode=ENNReal.ofReal (1-p) := by
    rw [failMass_eq_one_sub_accept,haccept,ENNReal.ofReal_sub 1 (by linarith)]
    simp
  rw [hm,← ENNReal.ofReal_pow (by linarith)]
  have hreal := rejection_power_le p hp1 attemptLimit 450
    (by have hl := Real.log_two_lt_d9
        change (450 : ℝ)*Real.log 2 ≤ 1048576*p
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
open Correctness
def DigestFailed (family : DigestFamily) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (digestSearch family.1 family.2 0 attemptLimit)=none
def EncodingFailed (family : EncodingFamily) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (counterSearch family.1 (QuerySpace.routedTree family.1 family.2.1)
    (QuerySpace.routedLeaf family.1 family.2.1) family.2.2 0 counterLimit)=none
theorem finite_family_failure_le {ι α : Type} [Fintype ι]
    (law : ProbComp α) (event : ι → α → Prop) (δ : ENNReal)
    (h : ∀ i,Pr[event i | law] ≤ δ) :
    Pr[fun value => ∃ i,event i value | law] ≤ (Fintype.card ι : ENNReal)*δ := by
  classical
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset ι) law event
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => h i)
  have hu' : Pr[fun value => ∃ i,event i value | law] ≤
      ∑ i : ι,Pr[event i | law] := by
    simpa only [Finset.mem_univ,true_and] using hu
  exact hu'.trans (hb.trans_eq (by simp))
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def SearchesSucceedFor (answers : Answers) (message : Message) : Prop :=
  (∀ rho : Digest, ∃ found,
    evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit)=some found) ∧
  EncodingSearchesSucceed answers
theorem signPayload_succeedsFor (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig,evalWithAnswerFn answers (signPayload cache message)=some sig := by
  obtain ⟨⟨counter,output⟩,hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message))
  rw [signPayload_eq]
  simp only [evalWithAnswerFn_bind,hd,eval_signForest]
  obtain ⟨pieces,hp⟩ := signLayers_succeeds answers cache (output.toNat%2^31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
      (forestRoots answers (output.toNat%2^31) 7)))
  simp only [hp,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩
end SigGolfCandidate.T3.Correctness
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Correctness
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) := Presampling.tableSampler
def zeroAnswers : Answers := fun q => by
  rcases q with (input | input) | input
  · exact (0 : Fin (input+1))
  · exact (0 : HashOutput)
  · exact (0 : HashOutput)
def SearchAgreement (outputs : QuerySpace.SearchKey → HashOutput) (answers : Answers) : Prop :=
  ∀ key,answers (.inl (.inr (QuerySpace.searchQuery key)))=outputs key
def tableGood (outputs : QuerySpace.SearchKey → HashOutput) : Prop :=
  SearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)
theorem counterSearch_none_agreement (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : EncodingFamily) :
    evalWithAnswerFn answers
      (counterSearch family.1 (QuerySpace.routedTree family.1 family.2.1) (QuerySpace.routedLeaf family.1 family.2.1) family.2.2 0
        counterLimit)=none ↔
    ∀ c : Fin (2^22), Sampling.encodingDecode family.1 (outputs (.inl (family,c)))=none := by
  rw [counterSearch_none_iff]
  have hv (c : Nat) (hc : c<counterLimit) :
      evalWithAnswerFn answers
        (shortHash (encodingInput family.1 (QuerySpace.routedTree family.1 family.2.1) (QuerySpace.routedLeaf family.1 family.2.1)
          family.2.2 (BitVec.ofNat 32 (0+c)))) = (outputs (.inl (family,⟨c,hc⟩))).extractLsb' 0 128 := by
    rw [Presampling.eval_shortHash]
    have hinput : pad64 (encodingInput family.1 (QuerySpace.routedTree family.1 family.2.1) (QuerySpace.routedLeaf family.1 family.2.1)
        family.2.2 (BitVec.ofNat 32 (0+c))) = QuerySpace.searchQuery (.inl (family,⟨c,hc⟩)) := by
      simp only [QuerySpace.searchQuery,Sum.elim_inl,QuerySpace.encodingQuery,Sampling.encodingTrial,Nat.zero_add]
    rw [hinput,hagree]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c,hc⟩
theorem digestSearch_none_agreement (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : DigestFamily) :
    evalWithAnswerFn answers (digestSearch family.1 family.2 0 attemptLimit)=none ↔
    ∀ c : Fin (2^20), Sampling.digestDecode (outputs (.inr (family,c)))=none := by
  rw [digestSearch_none_iff]
  have hv (c : Nat) (hc : c<attemptLimit) :
      evalWithAnswerFn answers (digest family.1 family.2 (BitVec.ofNat 32 (0+c))) =
        outputs (.inr (family,⟨c,hc⟩)) := by
    rw [Presampling.eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0+c))) =
        QuerySpace.searchQuery (.inr (family,⟨c,hc⟩)) := by
      simp only [QuerySpace.searchQuery,Sum.elim_inr,QuerySpace.digestQuery,Sampling.digestTrial,Nat.zero_add]
    rw [hinput,hagree]
  have hd (value : HashOutput) : Sampling.digestDecode value=none ↔ digestAdmissible value=false := by
    simp [Sampling.digestDecode]
  constructor
  · intro h c
    rw [hd]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)
theorem tableGood_iff_searchesSucceed (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGood outputs ↔ SearchesSucceed answers := by
  unfold tableGood SearchesSucceed DigestSearchesSucceed EncodingSearchesSucceed
  simp only [← Option.ne_none_iff_exists']
  apply and_congr
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.digestSearch_none_table outputs zeroAnswers family).trans
      (digestSearch_none_agreement outputs answers hagree family).symm)
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.counterSearch_none_table outputs zeroAnswers family).trans
      (counterSearch_none_agreement outputs answers hagree family).symm)
theorem tableGood_searchesSucceed (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGood outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceed answers := (tableGood_iff_searchesSucceed outputs answers hagree).mp hgood
theorem tableGood_fallback_iff (outputs : QuerySpace.SearchKey → HashOutput) (fallback : Answers) :
    tableGood outputs ↔ SearchesSucceed (Presampling.tableAnswers outputs fallback) :=
  tableGood_iff_searchesSucceed outputs _ (Presampling.tableAnswers_apply outputs fallback)
theorem not_searchesSucceed_iff (answers : Answers) :
    ¬ SearchesSucceed answers ↔
      (∃ family,DigestFailed family answers) ∨ (∃ family,EncodingFailed family answers) := by
  classical
  simp only [SearchesSucceed,DigestSearchesSucceed,EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists',not_and_or,not_forall,not_not,DigestFailed,EncodingFailed]
theorem tableGood_failure_le (digestFail encodingFail : ENNReal)
    (hd : failMass Sampling.digestDecode^attemptLimit ≤ digestFail)
    (he : ∀ lay,failMass (Sampling.encodingDecode lay)^counterLimit ≤ encodingFail) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal)^384*digestFail+(2 : ENNReal)^173*encodingFail := by
  let law := ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun family outputs => DigestFailed family (Presampling.tableAnswers outputs zeroAnswers)) digestFail
    (fun family => (Presampling.digestSearch_table_failure zeroAnswers family).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (he family.1))
  rw [digestFamily_card,Nat.cast_pow,Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamily_card_le le_rfl)
  simp only [tableGood,not_searchesSucceed_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGood_failure_small_of_acceptance (p : ℝ) (hp : 1/3300 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^65 := by
  refine (tableGood_failure_le _ _
    (digest_failure_power_of_acceptance p hp hp1 haccept) encoding_failure_power).trans ?_
  have hreal : (2 : ℝ)^384*(1/2^450)+2^173*(1/2^800) ≤ 1/2^65 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ)^384*(1/2^450) by positivity)
    (show 0 ≤ (2 : ℝ)^173*(1/2^800) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^384 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^173 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using hcast
def tableGoodFor (message : Message) (outputs : QuerySpace.SearchKey → HashOutput) : Prop :=
  SearchesSucceedFor (Presampling.tableAnswers outputs zeroAnswers) message
theorem tableGoodFor_iff_searchesSucceedFor (message : Message) (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGoodFor message outputs ↔ SearchesSucceedFor answers message := by
  unfold tableGoodFor SearchesSucceedFor EncodingSearchesSucceed
  simp only [← Option.ne_none_iff_exists']
  apply and_congr
  · apply forall_congr'; intro rho
    exact not_congr ((Presampling.digestSearch_none_table outputs zeroAnswers (rho,message)).trans
      (digestSearch_none_agreement outputs answers hagree (rho,message)).symm)
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.counterSearch_none_table outputs zeroAnswers family).trans
      (counterSearch_none_agreement outputs answers hagree family).symm)
theorem tableGoodFor_searchesSucceedFor (message : Message) (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGoodFor message outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceedFor answers message := (tableGoodFor_iff_searchesSucceedFor message outputs answers hagree).mp hgood
theorem not_searchesSucceedFor_iff (answers : Answers) (message : Message) :
    ¬ SearchesSucceedFor answers message ↔
      (∃ rho : Digest,DigestFailed (rho,message) answers) ∨ (∃ family,EncodingFailed family answers) := by
  classical
  simp only [SearchesSucceedFor,EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists',not_and_or,not_forall,not_not,DigestFailed,EncodingFailed]
theorem tableGoodFor_failure_le (message : Message) (digestFail encodingFail : ENNReal)
    (hd : failMass Sampling.digestDecode^attemptLimit ≤ digestFail)
    (he : ∀ lay,failMass (Sampling.encodingDecode lay)^counterLimit ≤ encodingFail) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal)^128*digestFail+(2 : ENNReal)^173*encodingFail := by
  let law := ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (rho : Digest) outputs => DigestFailed (rho,message) (Presampling.tableAnswers outputs zeroAnswers)) digestFail
    (fun rho => (Presampling.digestSearch_table_failure zeroAnswers (rho,message)).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (he family.1))
  rw [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamily_card_le le_rfl)
  simp only [tableGoodFor,not_searchesSucceedFor_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGoodFor_failure_small_of_acceptance (message : Message) (p : ℝ) (hp : 1/3300 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^321 := by
  refine (tableGoodFor_failure_le message _ _
    (digest_failure_power_of_acceptance p hp hp1 haccept) encoding_failure_power).trans ?_
  have hreal : (2 : ℝ)^128*(1/2^450)+2^173*(1/2^800) ≤ 1/2^321 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ)^128*(1/2^450) by positivity)
    (show 0 ≤ (2 : ℝ)^173*(1/2^800) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^128 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^173 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using hcast
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem signing_z_le : SigGolfCandidate.Budget.zOf 131072 ≤ ENNReal.ofReal (BaseAudit.zU : ℝ) := by
  unfold SigGolfCandidate.Budget.zOf
  apply ENNReal.ofReal_le_ofReal
  convert SigGolfCandidate.Budget.rpow_two_inv_le 131072 (by decide) using 1 <;>
    norm_num [BaseAudit.zU]
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable def digestEnvelope : ENNReal := ENNReal.ofReal (BaseAudit.b0 : ℝ)
theorem digestEnvelope_ge_one : 1 ≤ digestEnvelope := by
  rw [digestEnvelope,← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  norm_num [BaseAudit.b0]
theorem digest_failMass_of_acceptance
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (DigestCounting.p0 : ℝ)) :
    failMass Sampling.digestDecode=ENNReal.ofReal (1-(DigestCounting.p0 : ℝ)) := by
  rw [failMass_eq_one_sub_accept,haccept,
    ENNReal.ofReal_sub 1 (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0])]
  simp
theorem digest_moment_step_of_acceptance
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (DigestCounting.p0 : ℝ)) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass Sampling.digestDecode*digestEnvelope+(1-failMass Sampling.digestDecode)) ≤ digestEnvelope := by
  have hp0 : 0 ≤ (DigestCounting.p0 : ℝ) := by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]
  have hp1 : 0 ≤ 1-(DigestCounting.p0 : ℝ) := by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]
  have hb0 : 0 ≤ (BaseAudit.b0 : ℝ) := by norm_num [BaseAudit.b0]
  have hz0 : 0 ≤ (BaseAudit.zU : ℝ) := by norm_num [BaseAudit.zU]
  have hs : 1-(1-(DigestCounting.p0 : ℝ))=(DigestCounting.p0 : ℝ) := by ring
  rw [digest_failMass_of_acceptance haccept,← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hp1,hs,digestEnvelope]
  calc
    _ ≤ ENNReal.ofReal (BaseAudit.zU : ℝ) *
      (ENNReal.ofReal (1-(DigestCounting.p0 : ℝ))*ENNReal.ofReal (BaseAudit.b0 : ℝ)+
        ENNReal.ofReal (DigestCounting.p0 : ℝ)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((BaseAudit.zU : ℝ)*
        ((1-(DigestCounting.p0 : ℝ))*(BaseAudit.b0 : ℝ)+(DigestCounting.p0 : ℝ))) := by
      rw [← ENNReal.ofReal_mul hp1,← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := by apply ENNReal.ofReal_le_ofReal;norm_num [BaseAudit.zU,DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0,BaseAudit.b0]
theorem V_digestSearch_fresh_of_acceptance (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter+fuel ≤ 2^32) (cache : Sampling.RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (Sampling.digestTrial rho message c)=none)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (DigestCounting.p0 : ℝ)) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  Sampling.V_digestSearch secret _ _ digestEnvelope_ge_one
    rho message (digest_moment_step_of_acceptance haccept) fuel counter hlimit cache hfresh
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) := Presampling.tableSampler
theorem digest_failure_power :
    failMass Sampling.digestDecode^attemptLimit ≤ 1/(2 : ENNReal)^450 :=
  digest_failure_power_of_acceptance (DigestCounting.p0 : ℝ)
    (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) DigestCounting.digest_probability_eq_p0
theorem tableGood_failure_small :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^65 :=
  tableGood_failure_small_of_acceptance (DigestCounting.p0 : ℝ)
    (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) DigestCounting.digest_probability_eq_p0
theorem tableGoodFor_failure_small (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^321 :=
  tableGoodFor_failure_small_of_acceptance message (DigestCounting.p0 : ℝ)
    (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) DigestCounting.digest_probability_eq_p0
theorem tableGoodFor_failure_128 (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^128 := by
  refine (tableGoodFor_failure_small message).trans ?_
  simp only [one_div,ENNReal.inv_le_inv]
  exact pow_le_pow_right₀ (by norm_num) (by decide)
theorem digest_moment_step :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass Sampling.digestDecode*digestEnvelope+(1-failMass Sampling.digestDecode)) ≤ digestEnvelope :=
  digest_moment_step_of_acceptance DigestCounting.digest_probability_eq_p0
theorem V_digestSearch_fresh (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter+fuel ≤ 2^32) (cache : Sampling.RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (Sampling.digestTrial rho message c)=none) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  V_digestSearch_fresh_of_acceptance secret rho message fuel counter hlimit cache hfresh
    DigestCounting.digest_probability_eq_p0
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Sampling Cost Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev signingZ : ENNReal := SigGolfCandidate.Budget.zOf 131072
def EncodingFreshBelow (n : Nat) (cache : RCache) : Prop :=
  ∀ lay : Layer,lay.val<n → ∀ tree leaf message c,c<2^32 →
    cache (encodingTrial lay tree leaf message c)=none
def AllSearchesFresh (cache : RCache) : Prop :=
  (∀ rho message c,c<2^32 → cache (digestTrial rho message c)=none) ∧ EncodingFreshBelow 4 cache
structure SourceFreshness (secret : BitVec 256) : Prop where
  counter : ∀ lay tree leaf message cache,EncodingFreshBelow (lay.val+1) cache →
    ∀ result ∈ support (roRun secret (counterSearch lay tree leaf message 0 counterLimit) cache),
      EncodingFreshBelow lay.val result.2
  tree : ∀ lay tree leaf digits cache,EncodingFreshBelow lay.val cache →
    ∀ result ∈ support (roRun secret (buildTree lay tree leaf digits) cache),
      EncodingFreshBelow lay.val result.2
  mac : ∀ region cache,AllSearchesFresh cache →
    ∀ result ∈ support (roRun secret (privateMac region) cache),AllSearchesFresh result.2
  nonce : ∀ message cache,AllSearchesFresh cache →
    ∀ result ∈ support (roRun secret (privateNonce message) cache),AllSearchesFresh result.2
  digest : ∀ rho message cache,AllSearchesFresh cache →
    ∀ result ∈ support (roRun secret (digestSearch rho message 0 attemptLimit) cache),
      EncodingFreshBelow 4 result.2
  forest : ∀ index chosen cache,EncodingFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (signForest index chosen) cache),EncodingFreshBelow 4 result.2
  forestPk : ∀ index roots cache,EncodingFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (forestPk index roots) cache),EncodingFreshBelow 4 result.2
@[simp] theorem allSearchesFresh_empty : AllSearchesFresh ∅ := by
  constructor
  · intro rho message c hc;rfl
  · intro lay hl tree leaf message c hc;rfl
theorem post_of_roRun {α : Type} {P : Cost.Query → Prop} {Post : α → Prop} {k : Nat}
    {program : M α} (h : Cost.Bound P Post k program) (secret : BitVec 256) (cache : RCache)
    (result : α × RCache) (hr : result ∈ support (roRun secret program cache)) : Post result.1 := by
  have hs : result.1 ∈ support (realize secret program) := by
    apply support_simulateQ_run'_subset SphincsSecurity.romImpl _ cache
    rw [StateT.run'_eq,support_map]
    exact ⟨result,hr,rfl⟩
  have hs' := realize_support_subset secret program hs
  rw [← fst_countWith weight program,support_map] at hs'
  obtain ⟨counted,hc,he⟩ := hs'
  rw [← he]
  exact (h.count_support counted hc).1
theorem V_bind_bounded {α β : Type} (secret : BitVec 256) (z : ENNReal)
    (first : M α) (next : α → M β) (cache : RCache) (a b : ENNReal)
    (ha : V secret z first cache ≤ a)
    (hb : ∀ result ∈ support (roRun secret first cache),V secret z (next result.1) result.2 ≤ b) :
    V secret z (first >>= next) cache ≤ a*b :=
  (V_bind_le secret z first next cache b hb).trans (mul_le_mul' ha le_rfl)
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def SearchesSucceedSelected (answers : Answers) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn answers (digestSearch
      (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit)=some found) ∧
  EncodingSearchesSucceed answers
theorem signPayload_succeedsSelected (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedSelected answers) :
    ∃ sig,evalWithAnswerFn answers (signPayload cache message)=some sig := by
  obtain ⟨⟨counter,output⟩,hd⟩ := hgood.1 message
  rw [signPayload_eq]
  simp only [evalWithAnswerFn_bind,hd,eval_signForest]
  obtain ⟨pieces,hp⟩ := signLayers_succeeds answers cache (output.toNat%2^31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
      (forestRoots answers (output.toNat%2^31) 7)))
  simp only [hp,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩
end SigGolfCandidate.T3.Correctness
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) := Presampling.tableSampler
def tableGoodForNonces (nonces : Message → HashOutput) (outputs : QuerySpace.SearchKey → HashOutput) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn (Presampling.tableAnswers outputs zeroAnswers)
      (digestSearch ((nonces message).extractLsb' 0 128) message 0 attemptLimit)=some found) ∧
  EncodingSearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)
def NonceAgreement (nonces : Message → HashOutput) (answers : Answers) : Prop :=
  ∀ message,evalWithAnswerFn answers (privateNonce message)=(nonces message).extractLsb' 0 128
theorem tableGoodForNonces_searchesSucceedSelected (nonces : Message → HashOutput)
    (outputs : QuerySpace.SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) : SearchesSucceedSelected answers := by
  constructor
  · intro message
    rw [hnonce]
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (Presampling.digestSearch_none_table outputs zeroAnswers
      ((nonces message).extractLsb' 0 128,message)).mpr
      ((digestSearch_none_agreement outputs answers hagree
        ((nonces message).extractLsb' 0 128,message)).mp hnone)
    obtain ⟨found,hfound⟩ := hgood.1 message
    rw [hfound] at hnone'
    cases hnone'
  · intro family
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (Presampling.counterSearch_none_table outputs zeroAnswers family).mpr
      ((counterSearch_none_agreement outputs answers hagree family).mp hnone)
    obtain ⟨found,hfound⟩ := hgood.2 family
    rw [hfound] at hnone'
    cases hnone'
theorem not_tableGoodForNonces_iff (nonces : Message → HashOutput)
    (outputs : QuerySpace.SearchKey → HashOutput) :
    ¬tableGoodForNonces nonces outputs ↔
    (∃ message : Message,DigestFailed ((nonces message).extractLsb' 0 128,message)
      (Presampling.tableAnswers outputs zeroAnswers)) ∨
    (∃ family,EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) := by
  classical
  simp only [tableGoodForNonces,EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists',not_and_or,not_forall,not_not,DigestFailed,EncodingFailed]
theorem tableGoodForNonces_failure_le (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal)^256*(1/2^450)+(2 : ENNReal)^173*(1/2^800) := by
  let law := ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (message : Message) outputs => DigestFailed ((nonces message).extractLsb' 0 128,message)
      (Presampling.tableAnswers outputs zeroAnswers)) (1/(2 : ENNReal)^450)
    (fun message => (Presampling.digestSearch_table_failure zeroAnswers
      ((nonces message).extractLsb' 0 128,message)).le.trans digest_failure_power)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers))
      (1/(2 : ENNReal)^800)
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (encoding_failure_power family.1))
  rw [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamily_card_le le_rfl)
  simp only [not_tableGoodForNonces_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGoodForNonces_failure_small (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^193 := by
  refine (tableGoodForNonces_failure_le nonces).trans ?_
  have hreal : (2 : ℝ)^256*(1/2^450)+2^173*(1/2^800) ≤ 1/2^193 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ)^256*(1/2^450) by positivity)
    (show 0 ≤ (2 : ℝ)^173*(1/2^800) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^256 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^173 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using hcast
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Sampling Cost Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bound_signForest (index : Nat) (chosen : List Selection) :
    CBound (fun state : List Digest × List Digest × List Digest => state.2.2.length=7)
      35833 (signForest index chosen) := by
  unfold signForest
  refine (Bound.foldlM_range 7 _
    (fun coord (state : List Digest × List Digest × List Digest) => state.2.2.length=coord)
    (fun _ => 5119) ([],[],[]) rfl (fun coord _ state hstate => ?_)).mono_k (by decide)
  refine (bound_buildFts index coord).bind' (l := 0) (fun result _ => ?_) (by decide)
  exact .pure _ 0 (by simp [hstate])
end SigGolfCandidate.T3.Budgets
namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Sampling Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem signingZ_pow (cost : Nat) :
    signingZ^cost=(2 : ENNReal)^((cost : ℝ)/131072) := by
  rw [SigGolfCandidate.Budget.zOf_pow,← ENNReal.ofReal_rpow_of_pos (by norm_num),ENNReal.ofReal_ofNat]
  norm_num
end SigGolfCandidate.T3.Budgets
end
section
namespace SigGolfCandidate.T3.Freshness
open OracleComp OracleSpec Sampling QuerySpace Correctness
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Seeded (cacheAfter romImpl_support_cacheAfter)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def avoidsQuery (secret : BitVec 256) (target : HashInput) : Spec.Domain → Prop
 | .inl (.inl _) => True
 | .inl (.inr input) => input ≠ target
 | .inr coordinate => privateInput secret coordinate ≠ target
abbrev Avoids {α : Type} (secret : BitVec 256) (target : HashInput) (program : M α) : Prop :=
 AllQueriesSatisfy program (avoidsQuery secret target)
theorem avoids_pure {α : Type} (secret : BitVec 256) (target : HashInput) (value : α) :
 Avoids secret target (pure value) := allQueriesSatisfy_pure _ _
theorem avoids_bind {α β : Type} {secret : BitVec 256} {target : HashInput}
 {program : M α} {next : α → M β} (hp : Avoids secret target program)
 (hn : ∀ a, Avoids secret target (next a)) : Avoids secret target (program >>= next) :=
 allQueriesSatisfy_bind hp hn
theorem avoids_map {α β : Type} (f : α → β) {secret : BitVec 256} {target : HashInput}
 {program : M α} (hp : Avoids secret target program) : Avoids secret target (f <$> program) := by
 rw [map_eq_bind_pure_comp]
 exact avoids_bind hp fun _ => avoids_pure _ _ _
theorem avoids_mapM {α β : Type} (secret : BitVec 256) (target : HashInput)
 (items : List α) (f : α → M β) (h : ∀ a, Avoids secret target (f a)) :
 Avoids secret target (items.mapM f) := by
 induction items with
 | nil => exact avoids_pure _ _ _
 | cons a items ih =>
   rw [List.mapM_cons]
   exact avoids_bind (h a) fun _ => avoids_bind ih fun _ => avoids_pure _ _ _
theorem avoids_foldlM {α β : Type} (secret : BitVec 256) (target : HashInput)
 (items : List β) (f : α → β → M α) (h : ∀ a b, Avoids secret target (f a b)) (initial : α) :
 Avoids secret target (items.foldlM f initial) := by
 induction items generalizing initial with
 | nil => exact avoids_pure _ _ _
 | cons a items ih =>
   rw [List.foldlM_cons]
   exact avoids_bind (h initial a) ih
theorem cache_step_ne (input target : HashInput) (hne : input ≠ target) (cache : RCache)
 (result : HashOutput × RCache) (hr : result ∈ support ((SphincsSecurity.romImpl (.inr input)).run cache)) :
 result.2 target = cache target := by
 rw [romImpl_support_cacheAfter (.inr input) cache result hr]
 dsimp only [cacheAfter]
 cases hc : cache input <;> simp only [hc]
 exact QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)
theorem query_preserves (secret : BitVec 256) (target : HashInput) (q : Spec.Domain)
 (hq : avoidsQuery secret target q) (cache : RCache) (result : Spec.Range q × RCache)
 (hr : result ∈ support (roRun secret (liftM (Spec.query q)) cache)) : result.2 target=cache target := by
 rcases q with (n|input)|coordinate
 · change result ∈ support ((SphincsSecurity.romImpl (.inl n)).run cache) at hr
   rw [romImpl_support_cacheAfter (.inl n) cache result hr]
   rfl
 · have hr : result ∈ support ((SphincsSecurity.romImpl (.inr input)).run cache) := by
     simpa only [roRun,realize,simulateQ_spec_query,realHandler] using hr
   exact cache_step_ne input target hq cache result hr
 · have hr : result ∈ support ((SphincsSecurity.romImpl (.inr (privateInput secret coordinate))).run cache) := by
     simpa only [roRun,realize,simulateQ_spec_query,realHandler] using hr
   exact cache_step_ne _ target hq cache result hr
theorem preserves {α : Type} (secret : BitVec 256) (target : HashInput) (program : M α)
 (hp : Avoids secret target program) (cache : RCache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) : result.2 target=cache target := by
 induction program using OracleComp.inductionOn generalizing cache with
 | pure value =>
   rw [roRun_pure,support_pure,Set.mem_singleton_iff] at hr
   subst result; rfl
 | query_bind q next ih =>
   change AllQueriesSatisfy _ (avoidsQuery secret target) at hp
   rw [allQueriesSatisfy_query_bind_iff] at hp
   rw [roRun_bind,mem_support_bind_iff] at hr
   obtain ⟨step,hs,hr⟩ := hr
   exact (ih step.1 (hp.2 step.1) step.2 hr).trans (query_preserves secret target q hp.1 cache step hs)
def HasTag (tag : Nat) (input : HashInput) : Prop :=
 ∃ lay tree position index, queryHeader input = bytesLE 16 (header tag lay tree position index)
theorem tagged_ne {tag tag' : Nat} {input input' : HashInput}
 (h : HasTag tag input) (h' : HasTag tag' input') (hne : tag%256 ≠ tag'%256) : input ≠ input' := by
 rcases h with ⟨l,t,p,i,h⟩
 rcases h' with ⟨l',t',p',i',h'⟩
 intro he
 exact header_ne_of_tag hne (bytesLE_injective (h.symm.trans ((congrArg queryHeader he).trans h')))
theorem hasTag_padded (front back : HashInput) (hfront : front.length=16)
 (tag lay tree position index : Nat) :
 HasTag tag (pad64 (front ++ bytesLE 16 (header tag lay tree position index) ++ back)) :=
 ⟨lay,tree,position,index,queryHeader_padded _ _ hfront _⟩
def RowHdr (hdr : BitVec 128) : Prop := tweakMarker hdr = 1 ∧ tweakTag hdr = 2 ∧ tweakHigh hdr = 1
/-- Search headers: the digest header (C4: whole low word 0, since top labels `256 k` have marker byte 0) or a row
header. -/
def SearchHdr (hdr : BitVec 128) : Prop := (tweakMarker hdr = 0 ∧ tweakLow hdr = 0) ∨ RowHdr hdr
def RowQ (input : HashInput) : Prop := ∃ hdr, queryHeader input = bytesLE 16 hdr ∧ RowHdr hdr
def SearchQ (input : HashInput) : Prop := ∃ hdr, queryHeader input = bytesLE 16 hdr ∧ SearchHdr hdr
theorem RowQ.searchQ {input : HashInput} (h : RowQ input) : SearchQ input :=
 let ⟨hdr, hq, hr⟩ := h; ⟨hdr, hq, Or.inr hr⟩
theorem searchQ_ne {input target : HashInput} {hdr : BitVec 128}
 (h : queryHeader input = bytesLE 16 hdr) (hn : ¬ SearchHdr hdr) (ht : SearchQ target) : input ≠ target := by
 rintro rfl
 obtain ⟨hdr', h', hs⟩ := ht
 rw [h] at h'
 exact hn ((bytesLE_injective h') ▸ hs)
theorem rowQ_ne {input target : HashInput} {hdr : BitVec 128}
 (h : queryHeader input = bytesLE 16 hdr) (hn : ¬ RowHdr hdr) (ht : RowQ target) : input ≠ target := by
 rintro rfl
 obtain ⟨hdr', h', hs⟩ := ht
 rw [h] at h'
 exact hn ((bytesLE_injective h') ▸ hs)
theorem header_not_search (tag lay tree position index : Nat) (ht : tag % 256 ≠ 2) :
 ¬ SearchHdr (header tag lay tree position index) := by
 unfold SearchHdr RowHdr; rw [header_marker, header_tag]; omega
theorem chainHeader_not_search (lay : Layer) (tree leaf i step : Nat) :
 ¬ SearchHdr (chainHeader lay tree leaf i step) := by
 have := chainHeader_tweakMarker lay tree leaf i step
 unfold SearchHdr RowHdr; omega
theorem leafTweak_not_search (lay : Layer) (tree leaf : Nat) : ¬ SearchHdr (leafTweak lay tree leaf) := by
 unfold SearchHdr RowHdr; rw [leafTweak_marker, leafTweak_high]; omega
theorem digestHeader_not_row (counter : BitVec 32) : ¬ RowHdr (digestHeader counter) := by
 unfold RowHdr; rw [digestHeader_marker]; omega
theorem nodeTweak_not_search (tag lay tree heap : Nat) (htag : tag % 256 ≠ 2)
 (hroot : tag = 3 → 1 ≤ lay → lay < 4 → heap % 2 ^ 64 ≠ 1) : ¬ SearchHdr (nodeTweak tag lay tree heap) := by
 by_cases h : tag = 3 ∧ lay < 4
 · obtain ⟨rfl, h4⟩ := h
   by_cases h0 : lay = 0
   · subst h0; unfold SearchHdr RowHdr; rw [nodeTweak_top_low, nodeTweak_top_high]
     have := topNodeWord_pos heap
     omega
   · have hh := hroot rfl (by omega) h4
     unfold SearchHdr RowHdr
     rw [nodeTweak_lower_marker h0 h4, nodeTweak_hyper_high h4, if_neg h0]; omega
 · by_cases hf : tag = 3 ∧ lay < 13
   · obtain ⟨rfl, h13⟩ := hf
     unfold SearchHdr RowHdr
     rw [nodeTweak_fts_marker (by omega) h13, nodeTweak_fts_tag (by omega) h13]
     by_cases hn : FtsNew heap
     · rw [if_pos hn, if_pos hn]; obtain ⟨_, _⟩ := hn; omega
     · rw [if_neg hn, if_neg hn]; omega
   · rw [nodeTweak_other hf]; exact header_not_search _ _ _ _ _ htag
@[simp] theorem rowQ_encoding (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : Nat) :
 RowQ (encodingTrial lay tree leaf message counter) :=
 ⟨rowTweak lay tree leaf, queryHeader_encoding .., rowTweak_marker .., rowTweak_tag .., rowTweak_high ..⟩
@[simp] theorem searchQ_encoding (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : Nat) :
 SearchQ (encodingTrial lay tree leaf message counter) := (rowQ_encoding ..).searchQ
@[simp] theorem searchQ_digest (rho : Digest) (message : Message) (counter : Nat) :
 SearchQ (digestTrial rho message counter) :=
 ⟨digestHeader _, queryHeader_digest .., Or.inl ⟨digestHeader_marker _, digestHeader_lowNat _⟩⟩
theorem avoids_shortHash_of_ne (secret : BitVec 256) (target input : HashInput)
 (hne : pad64 input ≠ target) : Avoids secret target (shortHash input) := by
 unfold shortHash
 apply avoids_bind
 · exact (allQueriesSatisfy_query_iff _ _).mpr hne
 · intro _; exact avoids_pure _ _ _
theorem avoids_privateHash_of_ne (secret : BitVec 256) (target : HashInput) (coordinate : Coordinate)
 (hne : privateInput secret coordinate ≠ target) : Avoids secret target (privateHash coordinate) :=
 (allQueriesSatisfy_query_iff _ _).mpr hne
theorem hasTag_privatePair (secret : BitVec 256) (tag lay tree position index : Nat) :
 HasTag tag (privateInput secret (.inl (header tag lay tree position index))) := by
 exact hasTag_padded _ _ (bytesLE_length ..) tag lay tree position index
theorem hasTag_privateMac (secret : BitVec 256) (region : Region) :
 HasTag 14 (privateInput secret (.inr (.inr region))) := by
 exact hasTag_padded _ _ (bytesLE_length ..) 14 0 0 0 0
theorem hasTag_privateNonce (secret : BitVec 256) (message : Message) :
 HasTag 7 (privateInput secret (.inr (.inl message))) := by
 exact hasTag_padded _ _ (bytesLE_length ..) 7 0 0 0 0
theorem hasTag_not_search {tag : Nat} {input target : HashInput} (hi : HasTag tag input) (h2 : tag % 256 ≠ 2)
 (ht : SearchQ target) : input ≠ target := by
 obtain ⟨l, tr, p, ix, h⟩ := hi
 exact searchQ_ne h (header_not_search _ _ _ _ _ h2) ht
attribute [aesop safe apply] avoids_pure avoids_bind avoids_map avoids_mapM avoids_foldlM
macro "avoids_search" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))
section NonSearch
variable (secret : BitVec 256) (target : HashInput) (ht : SearchQ target)
include ht
@[aesop safe apply] theorem avoids_privatePair (tag lay tree position index : Nat) (h2 : tag%256 ≠ 2) :
 Avoids secret target (privatePair tag lay tree position index) := by
 unfold privatePair
 apply avoids_bind
 · exact avoids_privateHash_of_ne secret target _ (hasTag_not_search (hasTag_privatePair ..) h2 ht)
 · intro _; exact avoids_pure _ _ _
@[aesop safe apply] theorem avoids_privateMac (region : Region) :
 Avoids secret target (privateMac region) := by
 have hk (i : Nat) : Avoids secret target (privateHash (.inl (header 14 0 0 0 i))) :=
   avoids_privateHash_of_ne secret target _
     (hasTag_not_search (hasTag_privatePair secret 14 0 0 0 i) (by decide) ht)
 unfold privateMac privateMacKey
 simp only [bind_assoc,pure_bind]
 exact avoids_bind (hk 0) fun _ => avoids_bind (hk 1) fun _ => avoids_pure _ _ _
@[aesop safe apply] theorem avoids_privateNonce (message : Message) :
 Avoids secret target (privateNonce message) := by
 unfold privateNonce
 apply avoids_bind
 · exact avoids_privateHash_of_ne secret target _ (hasTag_not_search (hasTag_privateNonce ..) (by decide) ht)
 · intro _; exact avoids_pure _ _ _
@[aesop safe apply] theorem avoids_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
 Avoids secret target (chain lay tree leaf i start count value) := by
 unfold chain
 apply avoids_foldlM
 intro value step
 apply avoids_shortHash_of_ne
 have hh : queryHeader (pad64 (chainInput lay tree leaf i step value)) =
     bytesLE 16 (chainHeader lay tree leaf i step) := by
   simpa only [chainInput, List.append_assoc] using
     queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16])
       (chainHeader lay tree leaf i step)
 exact searchQ_ne hh (chainHeader_not_search lay tree leaf i step) ht
/-- Witness stack: top chains (G inputs `value | header | 0 | 0`, F inputs `0 | header | 0 | value`) carry the
chain header in bytes `16..32` either way, so they never hit a search query. -/
@[aesop safe apply] theorem avoids_topChain (leaf i start count : Nat) (value : Digest) :
 Avoids secret target (topChain leaf i start count value) := by
 unfold topChain
 apply avoids_foldlM
 intro value step
 unfold projHash
 apply avoids_bind
 · apply (allQueriesSatisfy_query_iff _ _).mpr
   have hh : queryHeader (pad64 (topChainInput leaf i step value)) = bytesLE 16 (chainHeader 0 0 leaf i step) := by
     unfold topChainInput
     split
     · simpa only [List.append_assoc] using
         queryHeader_padded (bytesLE 16 value) (zero16 ++ zero16) (bytesLE_length ..) (chainHeader 0 0 leaf i step)
     · simpa only [chainInput, List.append_assoc] using
         queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16]) (chainHeader 0 0 leaf i step)
   exact searchQ_ne hh (chainHeader_not_search 0 0 leaf i step) ht
 · intro _; exact avoids_pure _ _ _
@[aesop safe apply] theorem avoids_layChain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
 Avoids secret target (layChain lay tree leaf i start count value) := by
 unfold layChain; split
 · exact avoids_topChain secret target ht _ _ _ _ _
 · exact avoids_chain secret target ht _ _ _ _ _ _ _
@[aesop safe apply] theorem avoids_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
 Avoids secret target (leafHash lay tree leaf ends) := by
 unfold leafHash
 apply avoids_shortHash_of_ne
 exact searchQ_ne (queryHeader_leafInput ..) (leafTweak_not_search lay tree leaf) ht
@[aesop safe apply] theorem avoids_nodeHash (tag lay tree heap : Nat) (left right : Digest)
 (h2 : tag%256 ≠ 2) (hroot : tag = 3 → 1 ≤ lay → lay < 4 → heap % 2 ^ 64 ≠ 1) :
 Avoids secret target (nodeHash tag lay tree heap left right) := by
 unfold nodeHash
 apply avoids_shortHash_of_ne
 apply searchQ_ne _ (nodeTweak_not_search tag lay tree heap h2 hroot) ht
 simpa only [List.append_assoc] using
   (queryHeader_padded (bytesLE 16 left) (zero16 ++ bytesLE 16 right) (bytesLE_length ..)
     (nodeTweak tag lay tree heap))
@[aesop safe apply] theorem avoids_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
 (signatureOnly : Bool) : Avoids secret target (buildLeaf lay tree leaf digits signatureOnly) := by
 unfold buildLeaf; avoids_search
@[aesop safe apply] theorem avoids_buildLevel (tag lay tree h level : Nat) (nodes : List Digest)
 (h2 : tag%256 ≠ 2) (hlow : tag = 3 → lay = 0 ∨ 4 ≤ lay) :
 Avoids secret target (buildLevel tag lay tree h level nodes) := by
 unfold buildLevel
 exact avoids_mapM _ _ _ _ fun i => avoids_nodeHash secret target ht _ _ _ _ _ _ h2
   (fun h3 h1 h4 => by rcases hlow h3 with h | h <;> omega)
@[aesop safe apply] theorem avoids_buildLevels (tag lay tree h : Nat) (leaves : List Digest)
 (h2 : tag%256 ≠ 2) (hlow : tag = 3 → lay = 0 ∨ 4 ≤ lay) :
 Avoids secret target (buildLevels tag lay tree h leaves) := by unfold buildLevels; avoids_search
@[aesop safe apply] theorem nbav_topNodeHashN_q (heap n : Nat) (left right : Digest) :
    Avoids secret target (topNodeHashN heap n left right) := by
 unfold topNodeHashN
 apply avoids_shortHash_of_ne
 apply searchQ_ne _ (nodeTweak_not_search 3 0 0 heap (by decide) (fun _ h _ => by omega)) ht
 simpa only [topNodeInput, List.append_assoc] using
   (queryHeader_padded (bytesLE 16 left) (nonceBytes n ++ bytesLE 16 right) (bytesLE_length ..)
     (nodeTweak 3 0 0 heap))
theorem nbav_topNonceSearch_q (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Avoids secret target (topNonceSearch h heap left right fuel n)
  | 0, n => by unfold topNonceSearch; avoids_search
  | fuel+1, n => by
      have ih := nbav_topNonceSearch_q (h := h) (heap := heap) (left := left) (right := right) fuel (n+1)
      unfold topNonceSearch; avoids_search
attribute [aesop safe apply] nbav_topNonceSearch_q
@[aesop safe apply] theorem nbav_topNodeAt_q (h heap : Nat) (left right : Digest) :
    Avoids secret target (topNodeAt h heap left right) := by unfold topNodeAt; apply nbav_topNonceSearch_q <;> assumption
@[aesop safe apply] theorem nbav_buildTopLevel_q (level : Nat) (nodes : List Digest) :
    Avoids secret target (buildTopLevel level nodes) := by unfold buildTopLevel; avoids_search
@[aesop safe apply] theorem nbav_buildTopLevels_q (leaves : List Digest) :
    Avoids secret target (buildTopLevels leaves) := by unfold buildTopLevels; avoids_search
@[aesop safe apply] theorem avoids_buildTree_top (tree selected : Nat) (digits : List Nat) :
 Avoids secret target (buildTree 0 tree selected digits) := by
 unfold buildTree; avoids_search
@[aesop safe apply] theorem avoids_topPairsFrom (first start : Nat) (init : List Digest) : Avoids secret target (topPairsFrom first start init) := by
 unfold topPairsFrom topSeedPair; avoids_search
@[aesop safe apply] theorem avoids_topCoefs (leaf : Nat) : Avoids secret target (topCoefs leaf) := by
 unfold topCoefs; avoids_search
@[aesop safe apply] theorem avoids_topCoefsK (f : Nat) (carry : Digest) : Avoids secret target (topCoefsK f carry) := by
 unfold topCoefsK; avoids_search
@[aesop safe apply] theorem avoids_buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) : Avoids secret target (buildLeafTopC leaf coefs digits signatureOnly) := by
 unfold buildLeafTopC; avoids_search
@[aesop safe apply] theorem avoids_topFamilyCoefs (leaf : Nat) (cc : List Digest × Digest) : Avoids secret target (topFamilyCoefs leaf cc) := by
 unfold topFamilyCoefs; avoids_search
@[aesop safe apply] theorem avoids_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) : Avoids secret target (topTreeStep st leaf) := by
 unfold topTreeStep; avoids_search
@[aesop safe apply] theorem avoids_buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
 Avoids secret target (buildLeafTop leaf digits signatureOnly) := by
 unfold buildLeafTop; avoids_search
@[aesop safe apply] theorem avoids_buildTopTree : Avoids secret target buildTopTree := by
 unfold buildTopTree; avoids_search
@[aesop safe apply] theorem avoids_ftsLeaf (index coord leaf : Nat) (value : Digest) :
 Avoids secret target (ftsLeaf index coord leaf value) := by
 unfold ftsLeaf
 apply avoids_shortHash_of_ne
 apply searchQ_ne _ (header_not_search 9 coord index 0 leaf (by decide)) ht
 simpa only [List.append_assoc] using
   (queryHeader_padded zero16 (bytesLE 16 value ++ zero16) (by simp [zero16]) (header 9 coord index 0 leaf))
@[aesop safe apply] theorem avoids_buildFts (index coord : Nat) :
 Avoids secret target (buildFts index coord) := by unfold buildFts; avoids_search
@[aesop safe apply] theorem avoids_signForest (index : Nat) (chosen : List Selection) :
 Avoids secret target (signForest index chosen) := by unfold signForest; avoids_search
@[aesop safe apply] theorem avoids_forestPk (index : Nat) (roots : List Digest) :
 Avoids secret target (forestPk index roots) := by
 unfold forestPk
 apply avoids_shortHash_of_ne
 exact searchQ_ne (queryHeader_padded _ _ (bytesLE_length ..) _) (header_not_search 11 0 index 0 0 (by decide)) ht
@[aesop safe apply] theorem avoids_mask (level index : Nat) :
 Avoids secret target (mask level index) := by unfold mask pairedMask; avoids_search
@[aesop safe apply] theorem avoids_keygenPayload : Avoids secret target keygenPayload := by
 unfold keygenPayload maskedLevel pairedMask; avoids_search
@[aesop safe apply] theorem avoids_keygen : Avoids secret target keygen := by
 unfold keygen; avoids_search
end NonSearch
theorem hyperWord_layer (lay routed : Nat) : (hyperWord lay routed).toNat / 2 ^ 48 % 256 = lay % 256 := by
 rw [hyperWord_toNat]
 have := Nat.mod_lt routed (show 0 < 2 ^ 32 by decide)
 have := Nat.mod_lt lay (show 0 < 256 by decide)
 omega
theorem encodingTrial_ne_of_layer (lay other : Layer) (hne : lay ≠ other)
 (tree leaf : Nat) (message : Digest) (counter : Nat)
 (tree' leaf' : Nat) (message' : Digest) (counter' : Nat) :
 encodingTrial lay tree leaf message counter ≠ encodingTrial other tree' leaf' message' counter' := by
 intro he
 have hh := congrArg queryHeader he
 simp only [queryHeader_encoding] at hh
 have hw := (append64_inj (bytesLE_injective hh)).2
 have hl := congrArg (fun w : BitVec 64 => w.toNat / 2 ^ 48 % 256) hw
 simp only [hyperWord_layer] at hl
 have h1 : lay.val < 256 := by have := lay.isLt; omega
 have h2 : other.val < 256 := by have := other.isLt; omega
 rw [Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2] at hl
 exact hne (Fin.ext hl)
theorem avoids_counterSearch (secret : BitVec 256) (lay other : Layer) (hne : lay ≠ other)
 (tree leaf : Nat) (message : Digest) (counter fuel : Nat)
 (tree' leaf' : Nat) (message' : Digest) (counter' : Nat) :
 Avoids secret (encodingTrial other tree' leaf' message' counter')
   (counterSearch lay tree leaf message counter fuel) := by
 induction fuel generalizing counter with
 | zero => exact avoids_pure _ _ _
 | succ fuel ih =>
   unfold counterSearch
   apply avoids_bind
   · apply avoids_shortHash_of_ne
     exact encodingTrial_ne_of_layer lay other hne tree leaf message counter tree' leaf' message' counter'
   · intro answer
     split
     · exact ih _
     · exact avoids_pure _ _ _
@[aesop safe apply] theorem avoids_digest_encoding (secret : BitVec 256) (target : HashInput)
 (ht : RowQ target) (rho : Digest) (message : Message) (counter : BitVec 32) :
 Avoids secret target (digest rho message counter) := by
 unfold digest publicHash
 apply (allQueriesSatisfy_query_iff _ _).mpr
 change pad64 (digestInput rho message counter) ≠ target
 exact rowQ_ne (queryHeader_padded _ _ (bytesLE_length ..) _) (digestHeader_not_row counter) ht
theorem avoids_digestSearch_encoding (secret : BitVec 256) (target : HashInput) (ht : RowQ target)
 (rho : Digest) (message : Message) (counter fuel : Nat) :
 Avoids secret target (digestSearch rho message counter fuel) := by
 induction fuel generalizing counter with
 | zero => unfold digestSearch; avoids_search
 | succ fuel ih => unfold digestSearch; avoids_search
theorem preserves_allSearches {α : Type} (secret : BitVec 256) (program : M α)
 (h : ∀ target, SearchQ target → Avoids secret target program)
 (cache : RCache) (hc : Budgets.AllSearchesFresh cache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) : Budgets.AllSearchesFresh result.2 := by
 constructor
 · intro rho message c hlt
   rw [preserves secret _ program (h _ (searchQ_digest ..)) cache result hr]
   exact hc.1 rho message c hlt
 · intro lay hl tree leaf message c hlt
   rw [preserves secret _ program (h _ (searchQ_encoding ..)) cache result hr]
   exact hc.2 lay hl tree leaf message c hlt
theorem preserves_encodingBelow {α : Type} (secret : BitVec 256) (program : M α)
 (h : ∀ target, RowQ target → Avoids secret target program)
 (n : Nat) (cache : RCache) (hc : Budgets.EncodingFreshBelow n cache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) : Budgets.EncodingFreshBelow n result.2 := by
 intro lay hl tree leaf message c hlt
 rw [preserves secret _ program (h _ (rowQ_encoding ..)) cache result hr]
 exact hc lay hl tree leaf message c hlt
theorem keygen_preserves_fresh (secret : BitVec 256) (cache : RCache)
 (hc : Budgets.AllSearchesFresh cache) (result : (Digest × Cache) × RCache)
 (hr : result ∈ support (roRun secret keygen cache)) : Budgets.AllSearchesFresh result.2 :=
 preserves_allSearches secret keygen (fun target ht => avoids_keygen secret target ht) cache hc result hr
theorem keygen_fresh_from_empty (secret : BitVec 256) (result : (Digest × Cache) × RCache)
 (hr : result ∈ support (roRun secret keygen ∅)) : Budgets.AllSearchesFresh result.2 :=
 keygen_preserves_fresh secret ∅ Budgets.allSearchesFresh_empty result hr
end SigGolfCandidate.T3.Freshness
end
section
namespace SigGolfCandidate.T3.BudgetClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Sampling Budgets Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (sign keys.2 message)
theorem honestSignCount_realize (secret : BitVec 256) (message : Message) :
    realize secret (honestSignCount message)=(do
      let keys ← realize secret keygen
      World.countBlocks (realize secret (sign keys.2 message))) := by
  rw [honestSignCount,realize_bind]
  congr 1
  funext keys
  exact realize_count secret _
end SigGolfCandidate.T3.BudgetClosure
end
section
namespace SigGolfCandidate.T3.SourceReplay
open OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def isHash : Spec.Domain → Prop
 | .inl (.inl _) => False
 | _ => True
abbrev HashOnly {α : Type} (program : M α) : Prop := AllQueriesSatisfy program isHash
theorem hashOnly_pure {α : Type} (value : α) : HashOnly (pure value) :=
 allQueriesSatisfy_pure _ _
theorem hashOnly_bind {α β : Type} {program : M α} {next : α → M β}
 (hp : HashOnly program) (hn : ∀ a, HashOnly (next a)) : HashOnly (program >>= next) :=
 allQueriesSatisfy_bind hp hn
theorem hashOnly_map {α β : Type} (f : α → β) {program : M α}
 (hp : HashOnly program) : HashOnly (f <$> program) := by
 rw [map_eq_bind_pure_comp]
 exact hashOnly_bind hp fun _ => hashOnly_pure _
theorem hashOnly_mapM {α β : Type} (items : List α) (f : α → M β)
 (h : ∀ a, HashOnly (f a)) : HashOnly (items.mapM f) := by
 induction items with
 | nil => exact hashOnly_pure []
 | cons a items ih =>
   rw [List.mapM_cons]
   exact hashOnly_bind (h a) fun _ => hashOnly_bind ih fun _ => hashOnly_pure _
theorem hashOnly_foldlM {α β : Type} (items : List β) (f : α → β → M α)
 (h : ∀ a b, HashOnly (f a b)) (initial : α) : HashOnly (items.foldlM f initial) := by
 induction items generalizing initial with
 | nil => exact hashOnly_pure _
 | cons a items ih =>
   rw [List.foldlM_cons]
   exact hashOnly_bind (h initial a) ih
@[simp] theorem hashOnly_publicHash (input : HashInput) : HashOnly (publicHash input) := by
 exact (allQueriesSatisfy_query_iff _ _).mpr trivial
@[simp] theorem hashOnly_privateHash (coordinate : Coordinate) : HashOnly (privateHash coordinate) := by
 exact (allQueriesSatisfy_query_iff _ _).mpr trivial
def fixedAnswers (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id) :
 Correctness.Answers
 | .inl (.inl n) => (⟨0,Nat.zero_lt_succ n⟩ : Fin (n+1))
 | .inl (.inr input) => hash input
 | .inr coordinate => hash (privateInput secret coordinate)
theorem fixed_replay {α : Type} (secret : BitVec 256)
 (hash : QueryImpl SphincsSecurity.HashSpec Id) (program : M α) (hp : HashOnly program) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret program) =
   pure (evalWithAnswerFn (fixedAnswers secret hash) program) := by
 induction program using OracleComp.inductionOn with
 | pure a => simp [realize]
 | query_bind q next ih =>
   change AllQueriesSatisfy _ isHash at hp
   rw [allQueriesSatisfy_query_bind_iff] at hp
   rcases q with (n|input)|coordinate
   · exact False.elim hp.1
   · simp only [realize,simulateQ_bind,simulateQ_spec_query,realHandler]
     simp only [simulateQ_bind,simulateQ_spec_query,unifFwdAnswerImpl,QueryImpl.add_apply_inr,
       QueryImpl.liftTarget_apply,evalWithAnswerFn_bind,evalWithAnswerFn,fixedAnswers,
       pure_bind]
     exact ih _ (hp.2 _)
   · simp only [realize,simulateQ_bind,simulateQ_spec_query,realHandler]
     simp only [simulateQ_bind,simulateQ_spec_query,unifFwdAnswerImpl,QueryImpl.add_apply_inr,
       QueryImpl.liftTarget_apply,evalWithAnswerFn_bind,evalWithAnswerFn,fixedAnswers,
       pure_bind]
     exact ih _ (hp.2 _)
attribute [aesop safe apply] hashOnly_pure hashOnly_bind hashOnly_map hashOnly_mapM hashOnly_foldlM
  hashOnly_publicHash hashOnly_privateHash
macro "hashes" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))
@[aesop safe apply] theorem hashOnly_shortHash (input : HashInput) : HashOnly (shortHash input) := by
 unfold shortHash; hashes
@[aesop safe apply] theorem hashOnly_privatePair (tag lay tree position index : Nat) :
 HashOnly (privatePair tag lay tree position index) := by
 unfold privatePair; hashes
@[aesop safe apply] theorem hashOnly_privateMac (region : Region) : HashOnly (privateMac region) := by
 exact Security.SourceQueries.privateMac_allowed isHash (fun _ => trivial) region
@[aesop safe apply] theorem hashOnly_privateNonce (message : Message) : HashOnly (privateNonce message) := by
 unfold privateNonce; hashes
@[aesop safe apply] theorem hashOnly_mask (level index : Nat) : HashOnly (mask level index) := by
 unfold mask pairedMask; hashes
@[aesop safe apply] theorem hashOnly_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
 HashOnly (chain lay tree leaf i start count value) := by
 unfold chain; hashes
@[aesop safe apply] theorem hashOnly_projHash (high : Bool) (input : HashInput) : HashOnly (projHash high input) := by
 unfold projHash; hashes
@[aesop safe apply] theorem hashOnly_topChain (leaf i start count : Nat) (value : Digest) :
 HashOnly (topChain leaf i start count value) := by
 unfold topChain; hashes
@[aesop safe apply] theorem hashOnly_layChain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
 HashOnly (layChain lay tree leaf i start count value) := by
 unfold layChain; split <;> hashes
@[aesop safe apply] theorem hashOnly_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
 HashOnly (leafHash lay tree leaf ends) := by unfold leafHash; hashes
@[aesop safe apply] theorem hashOnly_nodeHash (tag lay tree heap : Nat) (left right : Digest) :
 HashOnly (nodeHash tag lay tree heap left right) := by unfold nodeHash; hashes
@[aesop safe apply] theorem hashOnly_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
 (signatureOnly : Bool) : HashOnly (buildLeaf lay tree leaf digits signatureOnly) := by
 unfold buildLeaf; hashes
@[aesop safe apply] theorem hashOnly_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) :
 HashOnly (buildLevel tag lay tree h level nodes) := by unfold buildLevel; hashes
@[aesop safe apply] theorem hashOnly_buildLevels (tag lay tree h : Nat) (leaves : List Digest) :
 HashOnly (buildLevels tag lay tree h leaves) := by unfold buildLevels; hashes
@[aesop safe apply] theorem nbho_topNodeHashN_q (heap n : Nat) (left right : Digest) :
    HashOnly (topNodeHashN heap n left right) := by unfold topNodeHashN; hashes
theorem nbho_topNonceSearch_q (h heap : Nat) (left right : Digest) :
    ∀ fuel n, HashOnly (topNonceSearch h heap left right fuel n)
  | 0, n => by unfold topNonceSearch; hashes
  | fuel+1, n => by
      have ih := nbho_topNonceSearch_q (h := h) (heap := heap) (left := left) (right := right) fuel (n+1)
      unfold topNonceSearch; hashes
attribute [aesop safe apply] nbho_topNonceSearch_q
@[aesop safe apply] theorem nbho_topNodeAt_q (h heap : Nat) (left right : Digest) :
    HashOnly (topNodeAt h heap left right) := by unfold topNodeAt; apply nbho_topNonceSearch_q <;> assumption
@[aesop safe apply] theorem nbho_buildTopLevel_q (level : Nat) (nodes : List Digest) :
    HashOnly (buildTopLevel level nodes) := by unfold buildTopLevel; hashes
@[aesop safe apply] theorem nbho_buildTopLevels_q (leaves : List Digest) :
    HashOnly (buildTopLevels leaves) := by unfold buildTopLevels; hashes
@[aesop safe apply] theorem hashOnly_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
 HashOnly (buildTree lay tree selected digits) := by unfold buildTree; hashes
@[aesop safe apply] theorem hashOnly_topPairsFrom (first start : Nat) (init : List Digest) : HashOnly (topPairsFrom first start init) := by
 unfold topPairsFrom topSeedPair; hashes
@[aesop safe apply] theorem hashOnly_topCoefs (leaf : Nat) : HashOnly (topCoefs leaf) := by
 unfold topCoefs; hashes
@[aesop safe apply] theorem hashOnly_topCoefsK (f : Nat) (carry : Digest) : HashOnly (topCoefsK f carry) := by
 unfold topCoefsK; hashes
@[aesop safe apply] theorem hashOnly_buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) : HashOnly (buildLeafTopC leaf coefs digits signatureOnly) := by
 unfold buildLeafTopC; hashes
@[aesop safe apply] theorem hashOnly_topFamilyCoefs (leaf : Nat) (cc : List Digest × Digest) : HashOnly (topFamilyCoefs leaf cc) := by
 unfold topFamilyCoefs; hashes
@[aesop safe apply] theorem hashOnly_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) : HashOnly (topTreeStep st leaf) := by
 unfold topTreeStep; hashes
@[aesop safe apply] theorem hashOnly_buildLeafTop (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
 HashOnly (buildLeafTop leaf digits signatureOnly) := by unfold buildLeafTop; hashes
@[aesop safe apply] theorem hashOnly_buildTopTree : HashOnly buildTopTree := by unfold buildTopTree; hashes
@[aesop safe apply] theorem hashOnly_keygenPayload : HashOnly keygenPayload := by
 unfold keygenPayload maskedLevel pairedMask; hashes
@[aesop safe apply] theorem hashOnly_keygen : HashOnly keygen := by
 unfold keygen; hashes
@[aesop safe apply] theorem hashOnly_counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest)
 (counter fuel : Nat) : HashOnly (counterSearch lay tree leaf message counter fuel) := by
 induction fuel generalizing counter with
 | zero => unfold counterSearch; hashes
 | succ fuel ih => unfold counterSearch; hashes
@[aesop safe apply] theorem hashOnly_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
 HashOnly (digest rho message counter) := by unfold digest; hashes
@[aesop safe apply] theorem hashOnly_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
 HashOnly (digestSearch rho message counter fuel) := by
 induction fuel generalizing counter with
 | zero => unfold digestSearch; hashes
 | succ fuel ih => unfold digestSearch; hashes
@[aesop safe apply] theorem hashOnly_ftsLeaf (index coord leaf : Nat) (secret : Digest) :
 HashOnly (ftsLeaf index coord leaf secret) := by unfold ftsLeaf; hashes
@[aesop safe apply] theorem hashOnly_buildFts (index coord : Nat) : HashOnly (buildFts index coord) := by
 unfold buildFts; hashes
@[aesop safe apply] theorem hashOnly_forestPk (index : Nat) (roots : List Digest) :
 HashOnly (forestPk index roots) := by unfold forestPk; hashes
@[aesop safe apply] theorem hashOnly_topPath (cache : Cache) (leaf : Nat) : HashOnly (topPath cache leaf) := by
 unfold topPath; hashes
@[aesop safe apply] theorem hashOnly_signTop (cache : Cache) (leaf : Nat) (digits : List Nat) :
 HashOnly (signTop cache leaf digits) := by unfold signTop; hashes
@[aesop safe apply] theorem hashOnly_signLayers (cache : Cache) (index n : Nat) (message : Digest) :
 HashOnly (signLayers cache index n message) := by
 induction n generalizing message with
 | zero => unfold signLayers; hashes
 | succ n ih => unfold signLayers; hashes
@[aesop safe apply] theorem hashOnly_signPayload (cache : Cache) (message : Message) :
 HashOnly (signPayload cache message) := by unfold signPayload; hashes
@[aesop safe apply] theorem hashOnly_sign (cache : Cache) (message : Message) :
 HashOnly (sign cache message) := by unfold sign; hashes
@[aesop safe apply] theorem hashOnly_recoverChild (index coord : Nat) (leaves : List Nat)
 (values : List Digest) (proof : Fin 115 → Digest) (level node used : Nat) :
 HashOnly (recoverChild index coord leaves values proof level node used) := by
 induction level generalizing node used with
 | zero => unfold recoverChild; hashes
 | succ level ih => unfold recoverChild; hashes
@[aesop safe apply] theorem hashOnly_recoverFts (sig : Signature) (index : Nat) (chosen : List Selection) :
 HashOnly (recoverFts sig index chosen) := by unfold recoverFts; hashes
@[aesop safe apply] theorem hashOnly_recoverLayer (sig : Signature) (index : Nat) (lay : Layer)
 (digits : List Nat) : HashOnly (recoverLayer sig index lay digits) := by unfold recoverLayer; hashes
@[aesop safe apply] theorem hashOnly_expandLayers (sig : Signature) (index n : Nat) (value : Digest) :
 HashOnly (expandLayers sig index n value) := by
 induction n generalizing value with
 | zero => unfold expandLayers; hashes
 | succ n ih => unfold expandLayers; hashes
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
 HashOnly (expand message pk sig) := by unfold expand; hashes
@[aesop safe apply] theorem hashOnly_verifyLayers (w : Witness) (index n : Nat) (root : Digest) :
 HashOnly (verifyLayers w index n root) := by
 induction n generalizing root with
 | zero => unfold verifyLayers; hashes
 | succ n ih => unfold verifyLayers; hashes
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
 HashOnly (verify message pk w) := by unfold verify; hashes
theorem keygen_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret keygen) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) keygen) :=
 fixed_replay secret hash keygen hashOnly_keygen
theorem sign_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
 (cache : Cache) (message : Message) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret (sign cache message)) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) (sign cache message)) :=
 fixed_replay secret hash (sign cache message) (hashOnly_sign cache message)
theorem expand_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
 (message : Message) (pk : Digest) (sig : Signature) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret (expand message pk sig)) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) (expand message pk sig)) :=
 fixed_replay secret hash (expand message pk sig) (hashOnly_expand message pk sig)
theorem verify_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
 (message : Message) (pk : Digest) (w : Witness) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret (verify message pk w)) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) (verify message pk w)) :=
 fixed_replay secret hash (verify message pk w) (hashOnly_verify message pk w)
end SigGolfCandidate.T3.SourceReplay
end
section
namespace SigGolfCandidate.T3.NonceSampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev NonceOutputs := Message → HashOutput
abbrev SearchOutputs := SearchKey → HashOutput
abbrev QueryKey := Message ⊕ SearchKey
@[irreducible] noncomputable def nonceSampler : SampleableType NonceOutputs :=
  Derivation.outputSampler Message
@[irreducible] noncomputable def combinedSampler : SampleableType (QueryKey → HashOutput) :=
  Derivation.outputSampler QueryKey
noncomputable local instance : SampleableType NonceOutputs := nonceSampler
noncomputable local instance : SampleableType SearchOutputs := Presampling.tableSampler
noncomputable local instance : SampleableType (QueryKey → HashOutput) := combinedSampler
def nonceInputs (secret : BitVec 256) (message : Message) : HashInput :=
  privateInput secret (.inr (.inl message))
theorem nonceInputs_injective (secret : BitVec 256) : Function.Injective (nonceInputs secret) := by
  intro a b he
  exact Sum.inl.inj (Sum.inr.inj (privateInput_injective secret he))
theorem nonceInputs_length (secret : BitVec 256) (message : Message) :
    (nonceInputs secret message).length = 128 := by
  simp only [nonceInputs, privateInput_nonce, List.length_append, SphincsSecurity.bytesLE_length,
    zero16, List.length_replicate]
theorem searchQuery_length (key : SearchKey) : (searchQuery key).length = 64 := by
  cases key with
  | inl key => exact Sampling.encodingTrial_length _ _ _ _ _
  | inr key => exact Sampling.digestTrial_length _ _ _
theorem nonceInputs_ne_searchQuery (secret : BitVec 256) (message : Message) (key : SearchKey) :
    nonceInputs secret message ≠ searchQuery key := by
  intro he
  have hl := congrArg List.length he
  rw [nonceInputs_length, searchQuery_length] at hl
  omega
def combinedInputs (secret : BitVec 256) : QueryKey → HashInput :=
  Sum.elim (nonceInputs secret) searchQuery
theorem combinedInputs_injective (secret : BitVec 256) : Function.Injective (combinedInputs secret) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (nonceInputs_injective secret he)
    | inr b => exact False.elim (nonceInputs_ne_searchQuery secret a b he)
  | inr a =>
    cases b with
    | inl b => exact False.elim (nonceInputs_ne_searchQuery secret b a he.symm)
    | inr b => exact congrArg Sum.inr (searchQuery_injective he)
noncomputable def preparedCache (secret : BitVec 256)
    (nonceOutputs : NonceOutputs) (searchOutputs : SearchOutputs) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ (combinedInputs secret) (Sum.elim nonceOutputs searchOutputs)
theorem preparedCache_nonce (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (message : Message) :
    preparedCache secret nonceOutputs searchOutputs (nonceInputs secret message) = some (nonceOutputs message) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inl message)
theorem preparedCache_search (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (key : SearchKey) :
    preparedCache secret nonceOutputs searchOutputs (searchQuery key) = some (searchOutputs key) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inr key)
theorem combined_uniform :
    𝒮[($ᵗ (QueryKey → HashOutput) : ProbComp _)] =
    𝒮[do
      let nonces ← ($ᵗ NonceOutputs : ProbComp _)
      let searches ← ($ᵗ SearchOutputs : ProbComp _)
      pure (Sum.elim nonces searches)] := by
  classical
  let : Fintype SearchOutputs := @Pi.instFintype SearchKey (fun _ => HashOutput)
    (Classical.decEq SearchKey) inferInstance (fun _ => inferInstance)
  let : Fintype NonceOutputs := @Pi.instFintype Message (fun _ => HashOutput)
    (Classical.decEq Message) inferInstance (fun _ => inferInstance)
  let split : (QueryKey → HashOutput) ≃ NonceOutputs × SearchOutputs :=
    Equiv.sumArrowEquivProdArrow Message SearchKey HashOutput
  have he := evalSPMF_map_bijective_uniform_cross
    (α := NonceOutputs × SearchOutputs) (β := QueryKey → HashOutput) split.symm split.symm.bijective
  have hp := evalDist_independent_uniform_pair (α := NonceOutputs) (β := SearchOutputs)
  rw [evalSPMF_map, ← hp] at he
  simpa only [evalSPMF_bind, evalSPMF_pure, map_bind, map_pure, split,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk] using he.symm
theorem presample_combined {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (QueryKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (cacheTable ∅ (combinedInputs secret) outputs)] := by
  let : SampleableType (QueryKey → SphincsSecurity.HashOutput) := combinedSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (QueryKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec))
        (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret)))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput)
      (combinedInputs secret) (combinedInputs_injective secret) ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let nonceOutputs ← ($ᵗ NonceOutputs : ProbComp _)
      let searchOutputs ← ($ᵗ SearchOutputs : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (preparedCache secret nonceOutputs searchOutputs)] := by
  rw [presample_combined, evalSPMF_bind, combined_uniform]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  rfl
end SigGolfCandidate.T3.NonceSampling
end
section
namespace SigGolfCandidate.T3.Completeness
open OracleComp OracleSpec ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true
theorem hashOnly_honestProgram (message : Message) : SourceReplay.HashOnly (honestProgram message) := by
  unfold honestProgram
  apply SourceReplay.hashOnly_bind SourceReplay.hashOnly_keygen
  intro keys
  apply SourceReplay.hashOnly_bind (SourceReplay.hashOnly_sign keys.2 message)
  intro sig
  cases sig with
  | none => exact SourceReplay.hashOnly_pure false
  | some sig =>
    apply SourceReplay.hashOnly_bind (SourceReplay.hashOnly_expand message keys.1 sig)
    intro witness
    cases witness with
    | none => exact SourceReplay.hashOnly_pure false
    | some witness => exact SourceReplay.hashOnly_verify message keys.1 witness
theorem hashOnly_everyMessageProgram : SourceReplay.HashOnly everyMessageProgram := by
  apply SourceReplay.hashOnly_foldlM
  intro accepted message
  exact SourceReplay.hashOnly_bind (hashOnly_honestProgram message) fun _ =>
    SourceReplay.hashOnly_pure _
theorem everyMessageProgram_true (answers : Correctness.Answers)
    (hall : ∀ message,evalWithAnswerFn answers (honestProgram message)=true) :
    evalWithAnswerFn answers everyMessageProgram=true := by
  have hf : ∀ messages : List Message,∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted)=accepted := by
    intro messages
    induction messages with
    | nil => intro accepted;rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons,evalWithAnswerFn_bind,evalWithAnswerFn_pure,hall,Bool.and_true]
      exact ih accepted
  exact hf _ true
theorem everyMessageProgram_true_of_complete (answers : Correctness.Answers)
    (hcomplete : Correctness.SigningComplete answers (evalWithAnswerFn answers keygen)) :
    evalWithAnswerFn answers everyMessageProgram=true := by
  apply everyMessageProgram_true
  intro message
  obtain ⟨sig,witness,hs,he,hv⟩ := hcomplete message
  simp only [honestProgram,evalWithAnswerFn_bind,hs,he,hv]
noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) :=
  Presampling.tableSampler
theorem failure_le_bad_table (secret : BitVec 256) (program : M Bool)
    (good : (QuerySpace.SearchKey → HashOutput) → Prop)
    (hzero : ∀ outputs,good outputs →
      Pr[fun value => value=false |
        (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
          (Presampling.preparedCache outputs)]=0) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] ≤
    Pr[fun outputs => ¬good outputs | ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false))
    (Presampling.presample_source secret program)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_probEvent
  intro outputs _ hgood
  exact hzero outputs (not_not.mp hgood)
theorem failure_zero_of_fixed_replay (secret : BitVec 256) (program : M Bool)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      cache.AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program)=(pure true : ProbComp Bool)) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        cache]=0 := by
  rw [probEvent_eq_zero_iff]
  intro value hv
  rw [StateT.run'_eq,support_map] at hv
  obtain ⟨result,hr,he⟩ := hv
  have hx := (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
    (realize secret program) cache result.1).mpr ⟨result.2,hr⟩
  obtain ⟨f,hf,hvalue⟩ := hx
  rw [hgood f hf,mem_support_pure_iff] at hvalue
  simp only [← he,hvalue,Bool.true_eq_false,not_false_eq_true]
theorem prepared_failure_zero (secret : BitVec 256) (program : M Bool)
    (outputs : QuerySpace.SearchKey → HashOutput)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      (Presampling.preparedCache outputs).AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program)=(pure true : ProbComp Bool)) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (Presampling.preparedCache outputs)]=0 :=
  failure_zero_of_fixed_replay secret program _ hgood
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler
end SigGolfCandidate.T3.Completeness
end
section
namespace SigGolfCandidate.T3.CountedReplay
open OracleComp OracleSpec SourceReplay Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem hashOnly_countWith {α : Type} (weight : Cost.Query → Nat) (program : M α)
 (hp : HashOnly program) : HashOnly (Cost.countWith weight program) := by
 induction program using OracleComp.inductionOn with
 | pure value =>
   rw [Cost.countWith_pure]
   exact hashOnly_pure _
 | query_bind q next ih =>
   change AllQueriesSatisfy _ isHash at hp
   rw [allQueriesSatisfy_query_bind_iff] at hp
   rw [Cost.countWith_bind,Cost.countWith_query]
   apply hashOnly_bind
   · apply hashOnly_map
     exact (allQueriesSatisfy_query_iff _ _).mpr hp.1
   · intro pair
     exact hashOnly_map _ (ih pair.1 (hp.2 pair.1))
theorem hashOnly_countBlocks {α : Type} (program : M α) (hp : HashOnly program) :
 HashOnly (Cost.countBlocks program) := hashOnly_countWith Cost.weight program hp
theorem support_replay {α : Type} (secret : BitVec 256) (program : M α) (hp : HashOnly program)
 (cache : RCache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) :
 ∃ hash : QueryImpl SphincsSecurity.HashSpec Id,
   cache.AgreesWithFn hash ∧ result.1 = evalWithAnswerFn (fixedAnswers secret hash) program := by
 have hsupport : ∃ cache' : RCache,
     (result.1,cache') ∈ support ((simulateQ
       (unifFwdImpl SphincsSecurity.HashSpec + SphincsSecurity.HashSpec.randomOracle)
       (realize secret program)).run cache) := by
   exact ⟨result.2,hr⟩
 obtain ⟨hash,hagree,hreplay⟩ :=
   (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
     (realize secret program) cache result.1).mpr hsupport
 rw [fixed_replay secret hash program hp,support_pure,Set.mem_singleton_iff] at hreplay
 exact ⟨hash,hagree,hreplay⟩
theorem counted_support_replay {α : Type} (program : M α) (hp : HashOnly program)
 (secret : BitVec 256) (cache : RCache) (result : (α × Nat) × RCache)
 (hr : result ∈ support (roRun secret (Cost.countBlocks program) cache)) :
 ∃ hash : QueryImpl SphincsSecurity.HashSpec Id,
   cache.AgreesWithFn hash ∧
   result.1 = evalWithAnswerFn (fixedAnswers secret hash) (Cost.countBlocks program) :=
 support_replay secret (Cost.countBlocks program) (hashOnly_countBlocks program hp) cache result hr
end SigGolfCandidate.T3.CountedReplay
end
section
end
section
namespace SigGolfCandidate.T3.ExpansionBudget
open OracleComp OracleSpec Cost Correctness SearchCost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem expandLayers_cost_step (answers : Answers) (sig : Signature) (index n : Nat)
    (value : Digest) (counter : BitVec 32) (digits : List Nat)
    (hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
      (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit)=some (counter,digits)) :
    cost answers (expandLayers sig index (n+1) value) =
      cost answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) +
      cost answers (recoverLayer sig index (Fin.ofNat 4 n) digits) +
      cost answers (expandLayers sig index n
        (evalWithAnswerFn answers (recoverLayer sig index (Fin.ofNat 4 n) digits))) := by
  simp only [expandLayers, cost_bind, hs]
  cases hx : evalWithAnswerFn answers (expandLayers sig index n
      (evalWithAnswerFn answers (recoverLayer sig index (Fin.ofNat 4 n) digits))) <;>
    simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem signLayers_cost_step (answers : Answers) (cache : Cache) (index n : Nat)
    (value : Digest) (counter : BitVec 32) (digits : List Nat)
    (hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
      (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit)=some (counter,digits)) :
    cost answers (signLayers cache index (n+1) value) =
      cost answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) +
      if n=0 then cost answers (signTop cache (route index (Fin.ofNat 4 n)).1 digits)
      else cost answers (buildTree (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 digits) +
        cost answers (signLayers cache index n
          (((evalWithAnswerFn answers (buildTree (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
            (route index (Fin.ofNat 4 n)).1 digits)).1.getD (height (Fin.ofNat 4 n)) []).getD 0 0)) := by
  simp only [signLayers, cost_bind, hs]
  split
  · simp only [cost_bind, cost_pure, Nat.add_zero, Option.map_some, Option.getD_some]
  · simp only [cost_bind]
    split <;> simp only [cost_pure, Nat.add_zero]
theorem signLayers_length (answers : Answers) (cache : Cache) (index : Nat) :
    ∀ n value pieces,evalWithAnswerFn answers (signLayers cache index n value)=some pieces → pieces.length=n := by
  intro n
  induction n with
  | zero =>
      intro value pieces he
      simp only [signLayers,evalWithAnswerFn_pure,Option.some.injEq] at he
      subst pieces
      rfl
  | succ n ih =>
      intro value pieces he
      simp only [signLayers,evalWithAnswerFn_bind] at he
      by_cases hn0 : n=0
      · subst n
        simp only [ite_true,evalWithAnswerFn_bind,evalWithAnswerFn_pure,Option.some.injEq] at he
        subst pieces
        rfl
      · simp only [hn0,ite_false] at he
        cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
          (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) with
        | none => simp only [hs,evalWithAnswerFn_pure,reduceCtorEq] at he
        | some found =>
            obtain ⟨counter,digits⟩ := found
            simp only [hs,evalWithAnswerFn_bind] at he
            cases hp : evalWithAnswerFn answers (signLayers cache index n
              (((evalWithAnswerFn answers (buildTree (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                (route index (Fin.ofNat 4 n)).1 digits)).1.getD (height (Fin.ofNat 4 n)) []).getD 0 0)) with
            | none => simp only [hp,evalWithAnswerFn_pure,reduceCtorEq] at he
            | some previous =>
                simp only [hp,evalWithAnswerFn_pure,Option.some.injEq] at he
                subst pieces
                simp [ih _ previous hp]
theorem expand_cost_step (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput) (root : Digest)
    (hd : evalWithAnswerFn answers (digestSearch sig.rho message 0 attemptLimit)=some (counter,output))
    (hf : evalWithAnswerFn answers (recoverFts sig (output.toNat%2^31) (selections output))=some root) :
    cost answers (expand message pk sig) =
      cost answers (digestSearch sig.rho message 0 attemptLimit) +
      cost answers (recoverFts sig (output.toNat%2^31) (selections output)) +
      cost answers (expandLayers sig (output.toNat%2^31) 4 root) := by
  simp only [expand,cost_bind,hd,hf]
  split
  · split <;> simp only [cost_pure,Nat.add_zero,Nat.add_assoc]
  · simp only [cost_pure,Nat.add_zero,Nat.add_assoc]
theorem signPayload_cost_step (answers : Answers) (cache : Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit)=some (counter,output)) :
    cost answers (signPayload cache message) =
      cost answers (privateNonce message) +
      cost answers (digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit) +
      cost answers (signForest (output.toNat%2^31) (selections output)) +
      cost answers (forestPk (output.toNat%2^31)
        (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))).2.2) +
      cost answers (signLayers cache (output.toNat%2^31) 4
        (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
          (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))).2.2))) := by
  rw [signPayload_eq]
  simp only [cost_bind,hd]
  split <;> simp only [cost_pure,Nat.add_zero,Nat.add_assoc]
theorem sign_cost_ge_mac (answers : Answers) (cache : Cache) (message : Message) :
    2 ≤ cost answers (sign cache message) := by
  have hmac : cost answers (privateMac cache.region)=2 := by
    simp only [cost,privateMac_count,evalWithAnswerFn_map]
  simp only [sign,cost_bind,hmac]
  omega
theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers keygen).2 message) =
      2+cost answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers keygen).2.region)=2 := by
    simp only [cost,privateMac_count,evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [sign,cost_bind,hmac,← hvalid,ne_eq,not_true_eq_false,ite_false]
end SigGolfCandidate.T3.ExpansionBudget
end
section
namespace SigGolfCandidate.T3.ExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Sampling Cost SearchCost
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def jointCounts {κ σ ω : Type} (initial : M κ) (signer : κ → M (Option σ))
    (expander : κ → σ → M ω) : M (Nat × Nat) := do
  let keys ← initial
  let signed ← countBlocks (signer keys)
  match signed.1 with
  | none => pure (signed.2,0)
  | some sig =>
      let expanded ← countBlocks (expander keys sig)
      pure (signed.2,expanded.2)
theorem eval_joint_cost_le {κ σ ω : Type} (answers : Correctness.Answers)
    (initial : M κ) (signer : κ → M (Option σ)) (expander : κ → σ → M ω)
    (hbound : ∀ sig,
      evalWithAnswerFn answers (signer (evalWithAnswerFn answers initial))=some sig →
      cost answers (expander (evalWithAnswerFn answers initial) sig) ≤
        8*cost answers (signer (evalWithAnswerFn answers initial))) :
    (evalWithAnswerFn answers (jointCounts initial signer expander)).2 ≤
      8*(evalWithAnswerFn answers (jointCounts initial signer expander)).1 := by
  unfold jointCounts
  have hfst := counted_fst answers (signer (evalWithAnswerFn answers initial))
  generalize hk : evalWithAnswerFn answers initial = keys at hfst hbound ⊢
  simp only [evalWithAnswerFn_bind,hk]
  generalize hc : evalWithAnswerFn answers (countBlocks (signer keys)) = signed at hfst ⊢
  rcases signed with ⟨sig,n⟩
  cases sig with
  | none => simp only [evalWithAnswerFn_pure];omega
  | some sig =>
      simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
      have hh := hbound sig hfst.symm
      simpa only [SearchCost.cost,hc] using hh
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
theorem hashOnly_honestJointCounts (message : Message) : SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply SourceReplay.hashOnly_bind SourceReplay.hashOnly_keygen
  intro keys
  apply SourceReplay.hashOnly_bind (CountedReplay.hashOnly_countBlocks _ (SourceReplay.hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact SourceReplay.hashOnly_pure _
  | some sig =>
    apply SourceReplay.hashOnly_bind (CountedReplay.hashOnly_countBlocks _ (SourceReplay.hashOnly_expand message keys.1 sig))
    intro expanded
    exact SourceReplay.hashOnly_pure _
end SigGolfCandidate.T3.ExpansionClosure
end
end
-- ==== merged from T3_FullCache_NativeTables ====
section

namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem uniform_product {A B : Type} [Finite A] [Finite B]
    [SampleableType A] [SampleableType B] [SampleableType (A × B)] :
    𝒮[do let a ← ($ᵗ A : ProbComp _); let b ← $ᵗ B; pure (a,b)]=𝒮[$ᵗ (A × B)] := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  apply evalSPMF_ext
  rintro ⟨a,b⟩
  change Pr[=(a,b) | do let x ← ($ᵗ A : ProbComp _); let y ← $ᵗ B; pure (id x,id y)]=_
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map,probOutput_uniformSample,Nat.card_eq_fintype_card,Fintype.card_prod,
    Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
abbrev OtherCoordinate := SiggolfT3Mac4.Source.OtherCoordinate
abbrev OtherTable := OtherCoordinate → HashOutput
abbrev FullTable := Coordinate → HashOutput
abbrev MacTable := CacheAuthentication.MacTable
@[irreducible] noncomputable def otherFintype : Fintype OtherCoordinate := by
  classical
  let _ : Fintype Coordinate := coordinateFintype
  exact inferInstance
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : Fintype Coordinate := coordinateFintype
@[irreducible] noncomputable def otherSampler : SampleableType OtherTable := by
  classical
  exact SampleableType.ofFintype _
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType (OtherTable × MacTable) :=
  SampleableType.ofFintype _
noncomputable def joinTable (other : OtherTable) (mac : MacTable) : FullTable :=
  SiggolfT3Mac4.Source.joinTable other mac
noncomputable def tableEquiv : (OtherTable × MacTable) ≃ FullTable := SiggolfT3Mac4.Source.tableEquiv
theorem uniform_table_split :
    𝒮[do let other ← ($ᵗ OtherTable : ProbComp _); let mac ← $ᵗ MacTable; pure (joinTable other mac)] =
      𝒮[$ᵗ FullTable] := by
  have h := congrArg (Functor.map tableEquiv) (uniform_product (A := OtherTable) (B := MacTable))
  simp only [← evalSPMF_map,map_bind,map_pure] at h
  exact h.trans (evalSPMF_map_bijective_uniform_cross (α := OtherTable × MacTable) (β := FullTable) tableEquiv tableEquiv.bijective)
theorem uniform_table_split_bind {α : Type} (next : FullTable → ProbComp α) :
    𝒮[do let table ← ($ᵗ FullTable : ProbComp _); next table]=
      𝒮[do let other ← ($ᵗ OtherTable : ProbComp _); let mac ← $ᵗ MacTable; next (joinTable other mac)] := by
  rw [evalSPMF_bind,← uniform_table_split,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]
abbrev RCache := QueryCache SphincsSecurity.HashSpec
abbrev CountState := Nat × RCache
def queryCharge (input : T3.Spec.Domain) : Nat := if Derivation.charged input then 1 else 0
noncomputable def countHandler (handler : QueryImpl T3.Spec (StateT RCache ProbComp)) :
    QueryImpl T3.Spec (StateT CountState ProbComp) := fun input => StateT.mk fun state => do
  let result ← (handler input).run state.2
  pure (result.1,(state.1+queryCharge input,result.2))
noncomputable def plainHandler (table : FullTable) : QueryImpl T3.Spec (StateT RCache ProbComp) :=
  PrivateTable.fixedImpl romImpl table
noncomputable def tableHandler (table : FullTable) : QueryImpl T3.Spec (StateT CountState ProbComp) :=
  countHandler (plainHandler table)
noncomputable def baseHandler (other : OtherTable) : QueryImpl T3.Spec (StateT CountState ProbComp) :=
  tableHandler (joinTable other (fun _ => 0))
noncomputable def run {α : Type} (table : FullTable) (program : M α) (state : CountState) :
    ProbComp (α × CountState) := (simulateQ (tableHandler table) program).run state
theorem tableHandler_split (other : OtherTable) (mac : MacTable) :
    tableHandler (joinTable other mac)=MacGame.sourceHandler (baseHandler other) mac := by
  funext input
  apply StateT.ext
  intro state
  cases input with
  | inl world => rfl
  | inr coordinate =>
      simp only [tableHandler,countHandler,plainHandler,PrivateTable.fixedImpl,
        QueryImpl.add_apply_inr,StateT.run_pure,StateT.run_mk,baseHandler,
        MacGame.sourceHandler,StateT.run_bind,pure_bind,queryCharge,Derivation.charged,ite_true]
      simp only [joinTable,SiggolfT3Mac4.Source.joinTable]
      dsimp only [HAdd.hAdd,QueryImpl.instHAddSumHAddOracleSpec,QueryImpl.add]
      simp only [StateT.run_pure,pure_bind]
      split_ifs <;> rfl
theorem run_pure {α : Type} (table : FullTable) (value : α) (state : CountState) :
    run table (pure value) state=pure (value,state) := rfl
theorem run_bind {α β : Type} (table : FullTable) (program : M α) (next : α → M β)
    (state : CountState) :
    run table (program >>= next) state=
      (do let result ← run table program state; run table (next result.1) result.2) := by
  simp only [run,simulateQ_bind,StateT.run_bind]
theorem run_map {α β : Type} (table : FullTable) (f : α → β) (program : M α) (state : CountState) :
    run table (f <$> program) state=Prod.map f id <$> run table program state := by
  simp only [run,simulateQ_map,StateT.run_map]
  rfl
theorem countHandler_run {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (program : M α) (state : CountState) :
    (simulateQ (countHandler handler) program).run state=
      (fun result => (result.1.1,(state.1+result.1.2,result.2))) <$>
        (simulateQ handler (SphincsSecurity.QueryCap.counted Derivation.charged program)).run state.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp [SphincsSecurity.QueryCap.counted_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,countHandler,
        StateT.run_mk,SphincsSecurity.QueryCap.counted_query_bind]
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,map_bind,bind_assoc,pure_bind]
      apply bind_congr
      intro step
      rw [ih]
      simp only [map_pure,queryCharge,Nat.add_assoc,bind_pure_comp]
theorem plainHandler_eq (table : FullTable) :
    plainHandler table=QueryImpl.compose romImpl (Derivation.tableHandler table) :=
  LazyPrivate.fixedImpl_eq table
theorem plain_run {α : Type} (table : FullTable) (program : M α) (cache : RCache) :
    (simulateQ (plainHandler table) program).run cache=
      (simulateQ romImpl (Derivation.tableRun table program)).run cache := by
  rw [plainHandler_eq,QueryImpl.simulateQ_compose]
  rfl
end SigGolfCandidate.T3.Security.FullGame
end
-- ==== merged from T3_FullCache_NativeGame ====
section

section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
set_option backward.isDefEq.respectTransparency false
abbrev NonMac {α : Type} (program : M α) := AllQueriesSatisfy program MacGame.NonMac
theorem shortHash_nonMac (input : HashInput) : NonMac (shortHash input) :=
  SourceQueries.shortHash_allowed MacGame.NonMac (fun _ => trivial) input
theorem projHash_nonMac (high : Bool) (input : HashInput) : NonMac (projHash high input) :=
  SourceQueries.projHash_allowed MacGame.NonMac (fun _ => trivial) high input
theorem chain_nonMac (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    NonMac (chain lay tree leaf i start count value) := by
  unfold chain
  exact SourceQueries.foldlM_allowed _ _ _ (fun _ _ => shortHash_nonMac _) _
theorem topChain_nonMac (leaf i start count : Nat) (value : Digest) :
    NonMac (topChain leaf i start count value) := by
  unfold topChain
  exact SourceQueries.foldlM_allowed _ _ _ (fun _ _ => projHash_nonMac _ _) _
theorem layChain_nonMac (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    NonMac (layChain lay tree leaf i start count value) := by
  unfold layChain; split
  · exact topChain_nonMac _ _ _ _ _
  · exact chain_nonMac _ _ _ _ _ _ _
theorem leafHash_nonMac (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    NonMac (leafHash lay tree leaf ends) := projHash_nonMac _ _
theorem nodeHash_nonMac (tag lay tree heap : Nat) (left right : Digest) :
    NonMac (nodeHash tag lay tree heap left right) := projHash_nonMac _ _
theorem ftsLeaf_nonMac (index coord leaf : Nat) (value : Digest) :
    NonMac (ftsLeaf index coord leaf value) := shortHash_nonMac _
theorem forestPk_nonMac (index : Nat) (roots : List Digest) :
    NonMac (forestPk index roots) := shortHash_nonMac _
theorem digest_nonMac (rho : Digest) (message : Message) (counter : BitVec 32) :
    NonMac (digest rho message counter) :=
  SourceQueries.publicHash_allowed _ (fun _ => trivial) _
attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed
  SourceQueries.map_allowed SourceQueries.foldlM_allowed SourceQueries.mapM_allowed
  shortHash_nonMac chain_nonMac topChain_nonMac layChain_nonMac leafHash_nonMac nodeHash_nonMac ftsLeaf_nonMac
  forestPk_nonMac digest_nonMac
macro "public_queries" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))
theorem counterSearch_nonMac (lay : Layer) (tree leaf : Nat) (message : Digest)
    (counter fuel : Nat) : NonMac (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; public_queries
  | succ fuel ih => unfold counterSearch; public_queries
theorem digestSearch_nonMac (rho : Digest) (message : Message) (counter fuel : Nat) :
    NonMac (digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; public_queries
  | succ fuel ih => unfold digestSearch; public_queries
end SigGolfCandidate.T3.Security.FullGame
end
section
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed
  SourceQueries.map_allowed SourceQueries.foldlM_allowed SourceQueries.mapM_allowed
  shortHash_nonMac nodeHash_nonMac leafHash_nonMac chain_nonMac topChain_nonMac layChain_nonMac ftsLeaf_nonMac forestPk_nonMac
  digest_nonMac digestSearch_nonMac counterSearch_nonMac
macro "verdict_queries" : tactic => `(tactic|
  aesop (config := { maxRuleApplications := 1000 }) (add simp MacGame.NonMac))
theorem recoverChild_nonMac (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) (level node used : Nat) :
    NonMac (recoverChild index coord leaves values proof level node used) := by
  induction level generalizing node used with
  | zero => unfold recoverChild;verdict_queries
  | succ level ih => unfold recoverChild;verdict_queries
attribute [local aesop safe apply] recoverChild_nonMac
theorem recoverFts_nonMac (sig : Signature) (index : Nat) (chosen : List Selection) :
    NonMac (recoverFts sig index chosen) := by
  unfold recoverFts;verdict_queries
attribute [local aesop safe apply] recoverFts_nonMac
theorem recoverLayer_nonMac (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    NonMac (recoverLayer sig index lay digits) := by
  unfold recoverLayer;verdict_queries
attribute [local aesop safe apply] recoverLayer_nonMac
theorem expandLayers_nonMac (sig : Signature) (index n : Nat) (value : Digest) :
    NonMac (expandLayers sig index n value) := by
  induction n generalizing value with
  | zero => unfold expandLayers;verdict_queries
  | succ n ih => unfold expandLayers;verdict_queries
attribute [local aesop safe apply] expandLayers_nonMac
theorem expand_nonMac (message : Message) (pk : Digest) (sig : Signature) :
    NonMac (expand message pk sig) := by
  unfold expand;verdict_queries
attribute [local aesop safe apply] expand_nonMac
theorem verifyLayers_nonMac (witness : Witness) (index n : Nat) (root : Digest) :
    NonMac (verifyLayers witness index n root) := by
  induction n generalizing root with
  | zero => unfold verifyLayers;verdict_queries
  | succ n ih => unfold verifyLayers;verdict_queries
attribute [local aesop safe apply] verifyLayers_nonMac
theorem verify_nonMac (message : Message) (pk : Digest) (witness : Witness) :
    NonMac (verify message pk witness) := by
  unfold verify;verdict_queries
attribute [local aesop safe apply] verify_nonMac
theorem checkForgery_nonMac (publicKey : Digest) (log : QueryLog Requests) (forgery : Forgery) :
    NonMac (checkForgery publicKey log forgery) := by
  cases forgery <;> unfold checkForgery <;> verdict_queries
noncomputable def verdict (publicKey : Digest) (result : Option Forgery × QueryLog Requests) : M Bool := do
  let some forgery := result.1 | return false
  let verified ← checkForgery publicKey result.2 forgery
  pure (decide (result.2.length ≤ 2^32) && verified)
theorem verdict_nonMac (publicKey : Digest) (result : Option Forgery × QueryLog Requests) :
    NonMac (verdict publicKey result) := by
  unfold verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (checkForgery_nonMac publicKey result.2 forgery)
        (fun _ => SourceQueries.pure_allowed _ _)
noncomputable def logged (program : OracleComp LazyPrivate.Interaction (Option Forgery)) :
    M (Option Forgery × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl SphincsSecurity.OracleWorld (WriterT (QueryLog Requests) M))+signingOracle) program).run
theorem game_expansion (adversary : Adversary) : game adversary=(do
    let generated ← keygen
    let result ← logged (adversary generated.1 generated.2)
    verdict generated.1 result) := rfl
theorem logged_pure (value : Option Forgery) : logged (pure value)=pure (value,[]) := rfl
theorem logged_world (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction (Option Forgery)) :
    logged (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => logged (next answer)) := by
  unfold logged
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem logged_request (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction (Option Forgery)) :
    logged (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (sign request.cache request.message >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> logged (next answer)) := by
  unfold logged
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp [signingOracle,WriterT.run_bind']
theorem logged_interpretation {State : Type} (handler : QueryImpl T3.Spec (StateT State ProbComp))
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : State) :
    (simulateQ handler (logged program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (sign request.cache request.message)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [logged_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [logged_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [logged_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]
end SigGolfCandidate.T3.Security.FullGame
end
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def plainResult {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (program : M α) (cache : RCache) : ProbComp α := (simulateQ handler program).run' cache
theorem plainResult_pure {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (value : α) (cache : RCache) : plainResult handler (pure value) cache=pure value := by
  simp [plainResult,StateT.run'_eq]
theorem plainResult_map {α β : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (f : α → β) (program : M α) (cache : RCache) :
    plainResult handler (f <$> program) cache=f <$> plainResult handler program cache := by
  simp [plainResult,StateT.run'_eq,StateT.run_map,Functor.map_map]
theorem plainResult_query_bind {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) (cache : RCache) :
    plainResult handler (liftM (T3.Spec.query input) >>= next) cache=
      ((handler input).run cache >>= fun result => plainResult handler (next result.1) result.2) := by
  simp only [plainResult,simulateQ_bind,simulateQ_spec_query,StateT.run'_eq,StateT.run_bind,map_bind]
theorem countedResult_query_bind {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) (cache : RCache) :
    plainResult handler (SphincsSecurity.QueryCap.counted Derivation.charged
        (liftM (T3.Spec.query input) >>= next)) cache=
      ((handler input).run cache >>= fun result =>
        (fun outcome => (outcome.1,queryCharge input+outcome.2)) <$>
          plainResult handler (SphincsSecurity.QueryCap.counted Derivation.charged (next result.1)) result.2) := by
  rw [SphincsSecurity.QueryCap.counted_query_bind,plainResult_query_bind]
  apply bind_congr
  intro result
  rw [bind_pure_comp,plainResult_map]
  rfl
theorem cap_count_event {α : Type} (handler : QueryImpl T3.Spec (StateT RCache ProbComp))
    (program : M α) (cache : RCache) (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      plainResult handler (SphincsSecurity.QueryCap.counted Derivation.charged program) cache]=
    Pr[fun outcome => ∃ result,outcome=some result ∧ event result.1 |
      plainResult handler (Derivation.cap program budget) cache] := by
  unfold Derivation.cap
  induction program using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
      simp [Derivation.cap,SphincsSecurity.QueryCap.counted_pure,
        SphincsSecurity.QueryCap.run_pure,plainResult_pure]
  | query_bind input next ih =>
      rw [countedResult_query_bind]
      change _=Pr[_ | plainResult handler (SphincsSecurity.QueryCap.run Derivation.charged
        (liftM (T3.Spec.query input) >>= next) budget) cache]
      rw [SphincsSecurity.QueryCap.run_query_bind]
      by_cases hc : Derivation.charged input
      · rw [if_pos hc]
        cases budget with
        | zero =>
            rw [plainResult_pure,probEvent_pure]
            simp only [reduceCtorEq,false_and,exists_false,if_false]
            apply probEvent_eq_zero
            intro result hresult hevent
            rw [mem_support_bind_iff] at hresult
            obtain ⟨step,_,hresult⟩ := hresult
            rw [support_map] at hresult
            obtain ⟨inner,_,rfl⟩ := hresult
            have := hevent.2
            simp [queryCharge,hc] at this
        | succ remaining =>
            rw [plainResult_query_bind,probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
            apply tsum_congr
            intro step
            apply congrArg
            rw [probEvent_map,← ih step.1 step.2 remaining]
            apply probEvent_ext
            intro result _
            simp only [Function.comp_def,queryCharge,hc,if_true]
            constructor <;> rintro ⟨he,hq⟩ <;> exact ⟨he,by omega⟩
      · rw [if_neg hc,plainResult_query_bind,probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
        apply tsum_congr
        intro step
        apply congrArg
        rw [probEvent_map,← ih step.1 step.2 budget]
        apply probEvent_ext
        intro result _
        simp only [Function.comp_def,queryCharge,hc,if_false,Nat.zero_add]
theorem table_cap_event {α : Type} (table : FullTable) (program : M α) (cache : RCache)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2.1 ≤ budget | run table program (0,cache)]=
    Pr[fun outcome => ∃ result,outcome=some result ∧ event result.1 |
      (simulateQ romImpl (Derivation.tableRun table (Derivation.cap program budget))).run' cache] := by
  have h := cap_count_event (plainHandler table) program cache budget event
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simpa only [plainResult,StateT.run'_eq,probEvent_map,Function.comp_def,Nat.zero_add,plain_run] using h
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable def countedTableExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (game adversary) (0,∅)
theorem counted_table_event (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment adversary]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true | tableExperiment adversary q] := by
  unfold countedTableExperiment tableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  exact table_cap_event table (game adversary) ∅ q (·=true)
theorem real_to_counted_table (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment adversary]+
        q/((2^256 : Nat) : ENNReal) := by
  rw [counted_table_event]
  exact private_derivation_event_bound adversary q hq
noncomputable def splitTableExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let mac ← ($ᵗ MacTable : ProbComp _)
  run (joinTable other mac) (game adversary) (0,∅)
theorem table_experiment_split (adversary : Adversary) :
    𝒮[countedTableExperiment adversary]=𝒮[splitTableExperiment adversary] :=
  uniform_table_split_bind (fun table => run table (game adversary) (0,∅))
end SigGolfCandidate.T3.Security.FullGame
end
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable def worldHandler (other : OtherTable) : RequestHop.Public CountState :=
  fun input => baseHandler other (.inl input)
noncomputable def checkContinuation (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState) : ProbComp (Bool × CountState) :=
  (simulateQ (baseHandler other) (verdict publicKey result.1)).run result.2
noncomputable def realRest (other : OtherTable) (mac : MacTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac)
    (adversary publicKey published) state >>= checkContinuation other publicKey
noncomputable def idealRest (other : OtherTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= checkContinuation other publicKey
theorem keygenPayload_nonMac : NonMac keygenPayload :=
  SiggolfT3Mac4.Source.Payload.keygenPayload_allowed
theorem base_key_run (other : OtherTable) (i : Fin 2) (state : CountState) :
    (baseHandler other (.inr (SiggolfT3Mac4.Source.keyCoordinate i))).run state=
      pure ((0 : HashOutput),(state.1+1,state.2)) := by
  simp only [baseHandler,tableHandler,countHandler,plainHandler,PrivateTable.fixedImpl,
    StateT.run_mk,queryCharge,Derivation.charged,ite_true]
  dsimp only [HAdd.hAdd,QueryImpl.instHAddSumHAddOracleSpec,QueryImpl.add]
  simp only [StateT.run_pure,pure_bind,joinTable,SiggolfT3Mac4.Source.joinTable_key]
theorem base_overhead_run (other : OtherTable) (state : CountState) :
    (MacGame.overhead (baseHandler other)).run state=pure ((),(state.1+2,state.2)) := by
  simp only [MacGame.overhead,StateT.run_bind,base_key_run,pure_bind,StateT.run_pure,Nat.add_assoc]
theorem source_mac_run (other : OtherTable) (mac : MacTable) (region : Region) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (privateMac region)).run state=
      pure (MacGame.tagAt mac region,(state.1+2,state.2)) := by
  simp only [privateMac,simulateQ_bind,MacGame.source_key_eq,StateT.run_bind,
    base_overhead_run,pure_bind,StateT.run_pure,simulateQ_pure]
  rfl
theorem logged_source_run (other : OtherTable) (mac : MacTable)
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (logged program)).run state=
      RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac) program state := by
  rw [logged_interpretation]
  change RequestHop.run (worldHandler other)
    (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (sign request.cache request.message)) program state=_
  exact congrArg (fun signer => RequestHop.run (worldHandler other) signer program state)
    (funext fun request => MacGame.source_signer_eq (baseHandler other) mac request)
theorem source_rest_run (other : OtherTable) (mac : MacTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← logged (adversary publicKey published)
      verdict publicKey result)).run state=
      realRest other mac adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,logged_source_run]
  unfold realRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac publicKey result.1)]
  rfl
theorem fixed_game_expansion (other : OtherTable) (mac : MacTable) (adversary : Adversary) :
    run (joinTable other mac) (game adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        realRest other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,game_expansion]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    source_rest_run other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
theorem refresh_published_mac (other : OtherTable) (adversary : Adversary)
    (generated : (Digest × Region) × CountState) :
    𝒮[do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
        (generated.2.1+2,generated.2.2)]=
    𝒮[do
      let tag ← ($ᵗ HashOutput : ProbComp _)
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest other (MacGame.retag mac ⟨tag,generated.1.2⟩) adversary
        generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2)] := by
  exact MacGame.refresh_published generated.1.2 (fun tag mac =>
    realRest other mac adversary generated.1.1 ⟨tag,generated.1.2⟩
      (generated.2.1+2,generated.2.2))
structure Setup where
  other : OtherTable
  publicKey : Digest
  published : T3.Cache
  state : CountState
noncomputable def setup : ProbComp Setup := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
  let tag ← ($ᵗ HashOutput : ProbComp _)
  pure ⟨other,generated.1.1,⟨tag,generated.1.2⟩,(generated.2.1+2,generated.2.2)⟩
noncomputable def preparedExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  let mac ← ($ᵗ MacTable : ProbComp _)
  realRest prepared.other (MacGame.retag mac prepared.published)
    adversary prepared.publicKey prepared.published prepared.state
noncomputable def authenticatedExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  idealRest prepared.other adversary prepared.publicKey prepared.published prepared.state
theorem split_experiment_prepared (adversary : Adversary) :
    𝒮[splitTableExperiment adversary]=𝒮[preparedExperiment adversary] := by
  unfold splitTableExperiment preparedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_game_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact refresh_published_mac other adversary generated
theorem checkContinuation_long (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState)
    (hlong : 2^32 < result.1.2.length) (q : Nat) :
    Pr[fun outcome => outcome.1=true ∧ outcome.2.1≤q | checkContinuation other publicKey result]=0 := by
  have hn : ¬result.1.2.length≤2^32 := Nat.not_le.mpr hlong
  unfold checkContinuation verdict
  cases result.1.1 with
  | none => simp [StateT.run_pure]
  | some forgery =>
      simp
      intro count cache _ hshort
      exact False.elim (hn hshort)
theorem rest_authentication_bound (adversary : Adversary) (prepared : Setup) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest prepared.other (MacGame.retag mac prepared.published)
        adversary prepared.publicKey prepared.published prepared.state] ≤
    Pr[fun result => result.1=true ∧ result.2.1≤q |
      idealRest prepared.other adversary prepared.publicKey prepared.published prepared.state]+
      ((2 : ENNReal)^152)⁻¹ := by
  have h := MacGame.authentication_hop (worldHandler prepared.other) (baseHandler prepared.other)
    prepared.published (adversary prepared.publicKey prepared.published) (2^32) prepared.state
    (checkContinuation prepared.other prepared.publicKey) (fun result => result.1=true ∧ result.2.1≤q)
    (fun result hlong => checkContinuation_long prepared.other prepared.publicKey result hlong q)
  refine h.trans (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem probEvent_bind_le_add {α β : Type} (source : ProbComp α)
    (left right : α → ProbComp β) (event : β → Prop) (error : ENNReal)
    (h : ∀ value,Pr[event | left value] ≤ Pr[event | right value]+error) :
    Pr[event | source >>= left] ≤ Pr[event | source >>= right]+error := by
  simp only [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value,Pr[=value | source]*(Pr[event | right value]+error) :=
      ENNReal.tsum_le_tsum (fun value => mul_le_mul' le_rfl (h value))
    _ = (∑' value,Pr[=value | source]*Pr[event | right value])+
        (∑' value,Pr[=value | source])*error := by
      simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)
theorem prepared_authentication_bound (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary]+
        ((2 : ENNReal)^152)⁻¹ :=
  probEvent_bind_le_add setup _ _ _ _ (fun prepared => rest_authentication_bound adversary prepared q)
theorem real_to_authenticated (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := real_to_counted_table adversary q hq
  have he := (table_experiment_split adversary).trans (split_experiment_prepared adversary)
  have hp : Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) he
  rw [hp] at h
  exact h.trans (add_le_add (prepared_authentication_bound adversary q) le_rfl)
end SigGolfCandidate.T3.Security.FullGame
end
section
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable def authenticatedSign (published : T3.Cache) (request : Request) : M (Option Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then signPayload request.cache request.message else pure none
noncomputable def authenticatedRecord (published : T3.Cache) (request : Request) :
    M (Option Signature × Option HashOutput) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then payloadRecord request.cache request.message else pure (none,none)
theorem authenticatedRecord_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> authenticatedRecord published request=authenticatedSign published request := by
  unfold authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure request.cache request.message
  · rfl
noncomputable def loggedWith {α : Type} (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) : M (α × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M))+
      (QueryImpl.withLogging (fun request => signer request) :
        QueryImpl Requests (WriterT (QueryLog Requests) M))) program).run
theorem loggedWith_pure {α : Type} (signer : Request → M (Option Signature)) (value : α) :
    loggedWith signer (pure value)=pure (value,[]) := rfl
theorem loggedWith_world {α : Type} (signer : Request → M (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem loggedWith_request {α : Type} (signer : Request → M (Option Signature))
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (signer request >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp
theorem loggedWith_interpretation {State α : Type}
    (handler : QueryImpl T3.Spec (StateT State ProbComp)) (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (simulateQ handler (loggedWith signer program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (signer request)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [loggedWith_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedWith_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [loggedWith_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]
noncomputable def idealGame (adversary : Adversary) : M Bool := do
  let generated ← keygen
  let result ← loggedWith (authenticatedSign generated.2) (adversary generated.1 generated.2)
  verdict generated.1 result
theorem authenticatedSign_interpretation (other : OtherTable) (mac : MacTable)
    (published : T3.Cache) (request : Request) :
    simulateQ (MacGame.sourceHandler (baseHandler other) mac) (authenticatedSign published request)=
      MacGame.idealSigner (baseHandler other) published request := by
  classical
  unfold authenticatedSign privateMac
  simp only [bind_assoc,pure_bind,simulateQ_bind,MacGame.source_key_eq,bind_assoc,pure_bind]
  unfold MacGame.idealSigner SiggolfT3Mac4.Adaptive.idealSigner
  apply congrArg (fun next => MacGame.overhead (baseHandler other) >>= next)
  funext ignored
  simp only [SiggolfT3Mac4.Source.fromCoreRequest]
  have he : SiggolfT3Mac4.Source.fromCoreCache request.cache =
      SiggolfT3Mac4.Source.fromCoreCache published ↔ request.cache=published :=
    SiggolfT3Mac4.Source.coreCacheEquiv.symm.injective.eq_iff
  simp only [he]
  split_ifs
  · simpa only [SiggolfT3Mac4.Source.corePayload,SiggolfT3Mac4.Source.toCoreCache_fromCoreCache] using
      MacGame.simulate_no_mac (baseHandler other) mac _ (MacGame.payload_no_mac request.cache request.message)
  · rfl
theorem ideal_rest_run (other : OtherTable) (mac : MacTable) (adversary : Adversary)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← loggedWith (authenticatedSign published) (adversary publicKey published)
      verdict publicKey result)).run state=idealRest other adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,loggedWith_interpretation]
  have hs : (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (authenticatedSign published request))=MacGame.idealSigner (baseHandler other) published :=
    funext fun request => authenticatedSign_interpretation other mac published request
  rw [hs]
  change RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= _ = _
  unfold idealRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac publicKey result.1)]
  rfl
theorem fixed_ideal_expansion (other : OtherTable) (mac : MacTable) (adversary : Adversary) :
    run (joinTable other mac) (idealGame adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        idealRest other adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,idealGame]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    ideal_rest_run other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
theorem sample_mac_at_bind {α : Type} (region : Region) (next : HashOutput → ProbComp α) :
    𝒮[do let mac ← ($ᵗ MacTable : ProbComp _); next (MacGame.tagAt mac region)]=
      𝒮[do let tag ← ($ᵗ HashOutput : ProbComp _); next tag] :=
  MacGame.sample_mac_at_bind region next
noncomputable def idealTableExperiment (adversary : Adversary) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (idealGame adversary) (0,∅)
theorem ideal_table_authenticated (adversary : Adversary) :
    𝒮[idealTableExperiment adversary]=𝒮[authenticatedExperiment adversary] := by
  unfold idealTableExperiment
  rw [uniform_table_split_bind]
  unfold authenticatedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_ideal_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact sample_mac_at_bind generated.1.2 (fun tag =>
    idealRest other adversary generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2))
noncomputable def idealLazyExperiment (adversary : Adversary) :
    ProbComp ((Bool × Nat) × LazyPrivate.State) :=
  LazyPrivate.run (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame adversary)) (∅,∅)
theorem ideal_lazy_event (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary] := by
  have h := LazyPrivate.run_eq_table
    (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame adversary)) ∅
  have hp : Pr[fun result => result.1.1=true ∧ result.1.2≤q |
      Prod.map id Prod.snd <$> idealLazyExperiment adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | do
        let table ← ($ᵗ FullTable : ProbComp _)
        (simulateQ romImpl (Derivation.tableRun table
          (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame adversary)))).run ∅] :=
    probEvent_congr' (fun _ _ => Iff.rfl) h
  simp only [probEvent_map,Prod.map,id_eq,Function.comp_def] at hp
  rw [hp]
  have he : Pr[fun result => result.1=true ∧ result.2.1≤q | idealTableExperiment adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (ideal_table_authenticated adversary)
  rw [← he]
  unfold idealTableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simp only [plain_run,Function.comp_def,Nat.zero_add]
theorem real_to_ideal_lazy (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [ideal_lazy_event]
  exact real_to_authenticated adversary q hq
end SigGolfCandidate.T3.Security.FullGame
end
end
end
-- ==== merged from T3M_Witness_Layout ====
section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
def wsize : Nat := 22984
abbrev WBytes := BitVec (8 * 22984)
def wbyte (w : WBytes) (i : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * i) 8)
def wdig (w : WBytes) (off : Nat) : Digest := w.extractLsb' (8 * off) 128
def wle32 (w : WBytes) (off : Nat) : BitVec 32 := w.extractLsb' (8 * off) 32
def rhoOff : Nat := 0
def dcOff : Nat := 16
def counterOff (lay : Layer) : Nat := 20 + 4 * lay.val
def leafBlock (s : Nat) : Nat := 64 + 48 * s
def streamBase : Nat := 1088
def streamEnd : Nat := 8728
def foldBlock (ptr r : Nat) : Nat := ptr + 8 + 64 * r
def segNext (ptr a : Nat) : Nat := ptr + 8 + 64 * a
def sibOff (side : Nat) : Nat := if side = 1 then 0 else 48
def layerBase (lay : Layer) : Nat := (![9288, 13512, 16712, 19848] : Layer → Nat) lay
def merkleBlock (lay : Layer) (j : Nat) : Nat := layerBase lay + 64 * (height lay - 1 - j)
def chainBlock (lay : Layer) (i : Nat) : Nat := layerBase lay + 64 * height lay + 64 * (chainCount lay - 1 - i)
def wrho (w : WBytes) : Digest := wdig w rhoOff
def wdc (w : WBytes) : BitVec 32 := wle32 w dcOff
def wctr (w : WBytes) (lay : Layer) : BitVec 32 := wle32 w (counterOff lay)
def wsecret (w : WBytes) (s : Nat) : Digest := wdig w (leafBlock s + 32)
def wleafPad (w : WBytes) (s : Nat) : Digest := wdig w (leafBlock s)
def wvalue (w : WBytes) (lay : Layer) (i : Nat) : Digest := wdig w (chainBlock lay i + 48)
def wchainPads (w : WBytes) (lay : Layer) (i : Nat) : Digest × Digest :=
  (wdig w (chainBlock lay i), wdig w (chainBlock lay i + 32))
def wchainHeaderPad (w : WBytes) (lay : Layer) (i : Nat) : BitVec 64 :=
  (wdig w (chainBlock lay i + 16)).extractLsb' 64 64
def wpath (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest :=
  wdig w (merkleBlock lay j + sibOff (leaf / 2 ^ j % 2))
def wmerklePad (w : WBytes) (lay : Layer) (j : Nat) : Digest := wdig w (merkleBlock lay j + 32)
def selLeaf (sel : Selection) (j : Nat) : Nat := sel.bucket * 128 + sel.leaves.getD j 0
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Schedule ====
section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
def lcaLevel (x y : Nat) : Nat := (x ^^^ y).log2 + 1
structure Segment where
  coord : Nat
  g : Nat
  lo : Nat
  a : Nat
  merge : Bool
  deriving DecidableEq, Repr, Inhabited
def Segment.heap (seg : Segment) (r : Nat) : Nat := (2048 + seg.g) / 2 ^ (seg.lo + r)
def Segment.t (seg : Segment) : Nat := seg.heap 0 % 2
def Segment.byte0 (seg : Segment) : Nat := seg.a + 16 * (if seg.merge then 1 else 0) + 32 * seg.t
def Segment.sib (seg : Segment) (r : Nat) : Nat × Nat :=
  (seg.lo + r, seg.g / 2 ^ (seg.lo + r) ^^^ 1)
def coordSchedule (coord : Nat) (sel : Selection) : List Segment :=
  let g0 := selLeaf sel 0
  let g1 := selLeaf sel 1
  let g2 := selLeaf sel 2
  let d01 := lcaLevel g0 g1
  let d12 := lcaLevel g1 g2
  if d01 < d12 then
    [⟨coord, g0, 0, d01 - 1, false⟩, ⟨coord, g1, 0, d01 - 1, true⟩, ⟨coord, g1, d01, d12 - 1 - d01, false⟩,
      ⟨coord, g2, 0, d12 - 1, true⟩, ⟨coord, g2, d12, 11 - d12, false⟩]
  else
    [⟨coord, g0, 0, d01 - 1, false⟩, ⟨coord, g1, 0, d12 - 1, false⟩, ⟨coord, g2, 0, d12 - 1, true⟩,
      ⟨coord, g2, d12, d01 - 1 - d12, true⟩, ⟨coord, g2, d01, 11 - d01, false⟩]
def schedule (chosen : List Selection) : List Segment :=
  (List.range 7).flatMap fun c => coordSchedule c (chosen.getD c ⟨0, []⟩)
def segPtr (segs : List Segment) (n : Nat) : Nat :=
  streamBase + ((segs.take n).map fun s => 8 + 64 * s.a).sum
def selectedLeaves (sel : Selection) : List Nat := sel.leaves.map fun s => sel.bucket * 128 + s
def slotPositions (sel : Selection) : List (Nat × Nat) :=
  frontier (selectedLeaves sel) 7 sel.bucket ++ (List.range 4).map fun j => (7 + j, sel.bucket / 2 ^ j ^^^ 1)
def slotBase (chosen : List Selection) (c : Nat) : Nat :=
  ((List.range c).map fun c' => (slotPositions (chosen.getD c' ⟨0, []⟩)).length).sum
def foldSlot (chosen : List Selection) (seg : Segment) (r : Nat) : Nat :=
  slotBase chosen seg.coord + (slotPositions (chosen.getD seg.coord ⟨0, []⟩)).idxOf (seg.sib r)
def foldPositions (segs : List Segment) : List (Nat × Nat) :=
  (List.range segs.length).flatMap fun n => (List.range (segs.getD n default).a).map fun r => (n, r)
def streamPlan (chosen : List Selection) (k : Fin 115) : Option (Nat × Nat) :=
  (foldPositions (schedule chosen)).find? fun p =>
    foldSlot chosen ((schedule chosen).getD p.1 default) p.2 = k.val
def slotBlock (chosen : List Selection) (k : Fin 115) : Option Nat :=
  (streamPlan chosen k).map fun p => foldBlock (segPtr (schedule chosen) p.1) p.2
def slotOffset (chosen : List Selection) (k : Fin 115) : Option Nat :=
  (streamPlan chosen k).map fun p =>
    let seg := (schedule chosen).getD p.1 default
    foldBlock (segPtr (schedule chosen) p.1) p.2 + sibOff (seg.heap p.2 % 2)
def Segment.Matches (seg : Segment) (b : Nat) : Prop :=
  b % 16 = seg.a ∧ (b / 16 % 2 = 1 ↔ seg.merge = true) ∧ (0 < seg.a → b / 32 % 2 = seg.t)
instance (seg : Segment) (b : Nat) : Decidable (seg.Matches b) := by
  unfold Segment.Matches; infer_instance
def StreamMatches (chosen : List Selection) (w : WBytes) : Prop :=
  ∀ n, n < (schedule chosen).length →
    ((schedule chosen).getD n default).Matches (wbyte w (segPtr (schedule chosen) n)).toNat
instance (chosen : List Selection) (w : WBytes) : Decidable (StreamMatches chosen w) := by
  unfold StreamMatches; infer_instance
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_VerifyP ====
section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def ftsLeafP (index coord leaf : Nat) (pad0 secret pad1 : Digest) : M Digest :=
  shortHash (bytesLE 16 pad0 ++ bytesLE 16 (header 9 coord index 0 leaf) ++ bytesLE 16 secret ++
    bytesLE 16 pad1)
/-- Padded node (pad at bytes 32..48). C4 (as b3cc11b's campaign S1): projected like `nodeHash` (`nodeHalfHigh`). -/
def nodeHashP (tag lay tree heap : Nat) (left pad right : Digest) : M Digest :=
  projHash (nodeHalfHigh tag lay heap)
    (bytesLE 16 left ++ bytesLE 16 (nodeTweak tag lay tree heap) ++ bytesLE 16 pad ++ bytesLE 16 right)
def chainHeaderP (lay : Layer) (tree leaf i step : Nat) (headerPad : BitVec 64) : Digest :=
  headerPad ++ (chainHeader lay tree leaf i step).extractLsb' 0 64
def chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) : HashInput :=
  bytesLE 16 pad0 ++ bytesLE 16 (chainHeaderP lay tree leaf i step headerPad) ++ bytesLE 16 pad1 ++
    bytesLE 16 value
def chainP (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => shortHash (chainInputP lay tree leaf i step pad0 pad1 headerPad value)) value
/-- Witness stack: the padded chain of layer `lay`: on the top, G chains (`T3.topIsG`) are value-first
(`value | header | pad0 | pad1`) and keep the high half on interior steps (`T3.topChainHigh`); otherwise `chainP`. -/
def chainInputPL (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64)
    (value : Digest) : HashInput :=
  if lay = 0 ∧ topIsG i = true then
    bytesLE 16 value ++ bytesLE 16 (chainHeaderP lay tree leaf i step headerPad) ++ bytesLE 16 pad0 ++
      bytesLE 16 pad1
  else chainInputP lay tree leaf i step pad0 pad1 headerPad value
def chainPL (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) : M Digest :=
  (List.range' start count).foldlM
    (fun value step => projHash (decide (lay = 0) && topChainHigh i step)
      (chainInputPL lay tree leaf i step pad0 pad1 headerPad value)) value
def digestP (m : Message) (w : WBytes) : M (Option HashOutput) :=
  if (wdc w).toNat ≥ attemptLimit then pure none else some <$> digest (wrho w) m (wdc w)
def selectionsOk (chosen : List Selection) : Bool :=
  chosen.all fun s => match s.leaves with
    | [x0, x1, x2] => decide (x0 < x1) && decide (x1 < x2)
    | _ => false
inductive Pending where
  | leaf (slot g : Nat)
  | merge (heap : Nat) (left : Digest)
def pendingHash (w : WBytes) (index coord : Nat) (node : Digest) : Pending → M Digest
  | .leaf s g => ftsLeafP index coord g (wleafPad w s) (wsecret w s) (wleafPad w (s + 1))
  | .merge heap left => nodeHash 10 coord index heap left node
def foldStep (w : WBytes) (index coord ptr : Nat) (state : Digest × Nat) (r : Nat) : M (Digest × Nat) := do
  let blk := foldBlock ptr r
  let parent ← if state.2 % 2 = 1 then
      nodeHashP 10 coord index (state.2 / 2) (wdig w blk) (wdig w (blk + 32)) state.1
    else nodeHashP 10 coord index (state.2 / 2) state.1 (wdig w (blk + 32)) (wdig w (blk + 48))
  pure (parent, state.2 / 2)
def foldsP (w : WBytes) (index coord ptr a : Nat) (node : Digest) (E : Nat) : M (Digest × Nat) :=
  (List.range a).foldlM (foldStep w index coord ptr) (node, E)
def segLoop (w : WBytes) (index coord : Nat) :
    List (Digest × Nat) → Pending → Nat → Nat → Digest →
      M (Option (Digest × Nat × Nat × List (Digest × Nat)))
  | stack, pending, E, ptr, node => do
      let b := (wbyte w ptr).toNat
      if 11 < b % 16 then return none
      if 0 < b % 16 ∧ b / 32 % 2 ≠ E % 2 then return none
      let node ← pendingHash w index coord node pending
      let (node, E) ← foldsP w index coord ptr (b % 16) node E
      let ptr := segNext ptr (b % 16)
      match stack with
      | [] => return if b / 16 % 2 = 1 then none else some (node, E, ptr, [])
      | (pnode, Q) :: rest =>
          if b / 16 % 2 = 0 then return some (node, E, ptr, (pnode, Q) :: rest)
          if Q ≠ E then return none
          segLoop w index coord rest (.merge (E / 2) pnode) (E / 2) ptr node
def ftsCoordP (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat) :
    M (Option (Digest × Nat)) := do
  let some (n0, E0, p0, s0) ← segLoop w index coord [] (.leaf (3 * coord) (selLeaf sel 0))
      (2048 + selLeaf sel 0) ptr 0 | pure none
  let some (n1, E1, p1, s1) ← segLoop w index coord ((n0, E0 ^^^ 1) :: s0)
      (.leaf (3 * coord + 1) (selLeaf sel 1)) (2048 + selLeaf sel 1) p0 n0 | pure none
  let some (n2, E2, p2, s2) ← segLoop w index coord ((n1, E1 ^^^ 1) :: s1)
      (.leaf (3 * coord + 2) (selLeaf sel 2)) (2048 + selLeaf sel 2) p1 n1 | pure none
  if E2 = 1 ∧ s2 = [] then pure (some (n2, p2)) else pure none
def ftsP (w : WBytes) (index : Nat) (chosen : List Selection) : M (Option Digest) := do
  let state ← (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, ptr) := state | pure none
      let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
      pure (some (roots ++ [root], ptr))) (some ([], streamBase))
  let some (roots, ptr) := state | pure none
  if streamEnd < ptr then return none
  pure (some (← forestPk index roots))
def layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPL lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalue w lay i.val)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerklePad w lay j.val) pair.2) value
def layersP (w : WBytes) (index : Nat) : Nat → Digest → M (Option Digest)
  | 0, root => pure (some root)
  | n + 1, root => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := wctr w lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (encodingInput lay tree leaf root counter)
      let some digits := decode lay answer | pure none
      let value ← layerP w index lay digits
      layersP w index n value
def verifyP (m : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some N ← digestP m w | pure false
  let chosen := selections N
  if !selectionsOk chosen then return false
  if !digestGate N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← ftsP w index chosen | pure false
  let some root ← layersP w index 4 root | pure false
  pure (root == pk)
structure Pads where
  leaf : Fin 22 → Digest
  fold : Fin 115 → Digest
  chain : (lay : Layer) → Fin (chainCount lay) → Digest × Digest
  merkle : (lay : Layer) → Fin (height lay) → Digest
  chainHeader : (lay : Layer) → Fin (chainCount lay) → BitVec 64
instance : Zero Pads := ⟨⟨fun _ => 0, fun _ => 0, fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => 0⟩⟩
def foldPad (pads : Pads) (leaves : List Nat) (level node used next : Nat) : Digest :=
  if !hasLeaf leaves level (2 * node) then pads.fold ⟨used % 115, Nat.mod_lt _ (by decide)⟩
  else if !hasLeaf leaves level (2 * node + 1) then pads.fold ⟨next % 115, Nat.mod_lt _ (by decide)⟩
  else 0
def recoverChildP (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) (pads : Pads) : Nat → Nat → Nat → M (Option (Digest × Nat))
  | level, node, used =>
      if !hasLeaf leaves level node then
        if h : used < 115 then pure (some (proof ⟨used, h⟩, used + 1)) else pure none
      else match level with
      | 0 => do
          let s := 3 * coord + leaves.idxOf node
          let value ← ftsLeafP index coord node (pads.leaf ⟨s % 22, Nat.mod_lt _ (by decide)⟩)
            (values.getD (leaves.idxOf node) 0) (pads.leaf ⟨(s + 1) % 22, Nat.mod_lt _ (by decide)⟩)
          pure (some (value, used))
      | level + 1 => do
          let some (left, next) ← recoverChildP index coord leaves values proof pads level (2 * node) used
            | pure none
          let some (right, next') ← recoverChildP index coord leaves values proof pads level (2 * node + 1) next
            | pure none
          let value ← nodeHashP 10 coord index (2 ^ (11 - (level + 1)) + node) left
            (foldPad pads leaves level node used next) right
          pure (some (value, next'))
def recoverFtsP (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection) :
    M (Option Digest) := do
  let state ← (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, used) := state | pure none
      let sel := chosen.getD coord ⟨0, []⟩
      let selected := sel.leaves.map (fun s => sel.bucket * 128 + s)
      let values := (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)
      let some (value, next) ← recoverChildP index coord selected values sig.proof pads 7 sel.bucket used
        | pure none
      let result ← (List.range 4).foldlM
        (fun (state : Option (Digest × Nat)) j => do
          let some (value, used) := state | pure none
          if h : used < 115 then
            let other := sig.proof ⟨used, h⟩
            let pair := if sel.bucket / 2 ^ j % 2 = 0 then (value, other) else (other, value)
            let parent ← nodeHashP 10 coord index (2 ^ (4 - j - 1) + sel.bucket / 2 ^ (j + 1)) pair.1
              (pads.fold ⟨used, h⟩) pair.2
            pure (some (parent, used + 1))
          else pure none) (some (value, next))
      let some (root, next) := result | pure none
      pure (some (roots ++ [root], next))) (some ([], 0))
  let some (roots, used) := state | pure none
  if !(List.range (115 - used)).all (fun j =>
      decide (sig.proof ⟨(used + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
  pure (some (← forestPk index roots))
def recoverLayerP (sig : Signature) (pads : Pads) (index : Nat) (lay : Layer) (digits : List Nat) :
    M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainPL lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (pads.chain lay i).1 (pads.chain lay i).2 (pads.chainHeader lay i) ((sig.layers lay).values i)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := (sig.layers lay).path j
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkle lay j) pair.2) value
def verifyLayersP (w : Witness) (pads : Pads) (index : Nat) : Nat → Digest → M (Option Digest)
  | 0, root => pure (some root)
  | n + 1, root => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ counterLimit then return none
      let (leaf, tree) := route index lay
      let answer ← shortHash (encodingInput lay tree leaf root counter)
      let some digits := decode lay answer | pure none
      let value ← recoverLayerP w.signature pads index lay digits
      verifyLayersP w pads index n value
def verifyPadsTail (pk : Digest) (output : HashOutput) (w : Witness) (pads : Pads) : M Bool := do
  let chosen := selections output
  if !digestAdmissible output then return false
  let index := output.toNat % 2 ^ 31
  let some root ← recoverFtsP w.signature pads index chosen | pure false
  let some root ← verifyLayersP w pads index 4 root | pure false
  pure (root == pk)
def verifyPads (m : Message) (pk : Digest) (w : Witness) (pads : Pads) : M Bool := do
  if w.digestCounter.toNat ≥ attemptLimit then return false
  let output ← digest w.signature.rho m w.digestCounter
  verifyPadsTail pk output w pads
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Basic ====
section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option maxRecDepth 10000
open SphincsSecurity (bytesLE) in
theorem bytesLE_zero16 : bytesLE 16 (0 : Digest) = zero16 := by decide
@[simp] theorem Pads.zero_leaf (s : Fin 22) : (0 : Pads).leaf s = 0 := rfl
@[simp] theorem Pads.zero_fold (k : Fin 115) : (0 : Pads).fold k = 0 := rfl
@[simp] theorem Pads.zero_chain (lay : Layer) (i : Fin (chainCount lay)) : (0 : Pads).chain lay i = (0, 0) := rfl
@[simp] theorem Pads.zero_merkle (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkle lay j = 0 := rfl
@[simp] theorem Pads.zero_chainHeader (lay : Layer) (i : Fin (chainCount lay)) :
    (0 : Pads).chainHeader lay i = 0 := rfl
@[simp] theorem ftsLeafP_zero (index coord leaf : Nat) (secret : Digest) :
    ftsLeafP index coord leaf 0 secret 0 = ftsLeaf index coord leaf secret := by
  simp only [ftsLeafP, ftsLeaf, bytesLE_zero16]
@[simp] theorem nodeHashP_zero (tag lay tree heap : Nat) (left right : Digest) :
    nodeHashP tag lay tree heap left 0 right = nodeHash tag lay tree heap left right := by
  simp only [nodeHashP, nodeHash, bytesLE_zero16]
theorem chainHeaderP_source (lay : Layer) (tree leaf i step : Nat) :
    chainHeaderP lay tree leaf i step ((chainHeader lay tree leaf i step).extractLsb' 64 64) =
      chainHeader lay tree leaf i step := BitVec.extractLsb'_append_extractLsb'
private theorem extract_high_zero (x : Digest) (h : x.toNat / 2^64 = 0) :
    x.extractLsb' 64 64 = 0 := by
  apply BitVec.eq_of_toNat_eq
  change (x.extractLsb' 64 64).toNat = (0 : Nat)
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, h]
theorem chainHeader_high_zero (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    (chainHeader lay tree leaf i step).extractLsb' 64 64 = 0 :=
  extract_high_zero _ (T3.chainHeader_high_zero lay tree leaf i step ht hl hi hs)
@[simp] theorem chainHeaderP_zero (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    chainHeaderP lay tree leaf i step 0 = chainHeader lay tree leaf i step := by
  rw [← chainHeader_high_zero lay tree leaf i step ht hl hi hs]
  exact chainHeaderP_source _ _ _ _ _
private theorem fold_steps_eq {α β : Type} (f g : β → α → M β) (xs : List α)
    (h : ∀ s ∈ xs, ∀ v, f v s = g v s) (v : β) :
    xs.foldlM f v = xs.foldlM g v := by
  induction xs generalizing v with
  | nil => rfl
  | cons s rest ih =>
      simp only [List.foldlM_cons]
      rw [h s (by simp)]
      apply congrArg (fun k : β → M β => g v s >>= k)
      funext next
      exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) next
theorem chainP_zero (lay : Layer) (tree leaf i start count : Nat) (value : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8) :
    chainP lay tree leaf i start count 0 0 0 value = chain lay tree leaf i start count value := by
  apply fold_steps_eq
  intro s hs v
  have hs8 : s < 8 := by
    have := List.mem_range'_1.mp hs
    rcases hsteps with hzero | hbound <;> omega
  simp only [chainInputP, chainInput, bytesLE_zero16,
    chainHeaderP_zero _ _ _ _ _ ht hl hi hs8]
/-- Witness stack: zero pads give the scheme chain of layer `lay` (`T3.layChain`). -/
theorem chainPL_zero (lay : Layer) (tree leaf i start count : Nat) (value : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8) (ht0 : lay = 0 → tree = 0) :
    chainPL lay tree leaf i start count 0 0 0 value = layChain lay tree leaf i start count value := by
  unfold layChain
  split
  · rename_i h0
    subst h0
    obtain rfl := ht0 rfl
    apply fold_steps_eq
    intro s hs v
    have hs8 : s < 8 := by
      have := List.mem_range'_1.mp hs
      rcases hsteps with hzero | hbound <;> omega
    by_cases hg : topIsG i = true
    · simp only [chainInputPL, topChainInput, hg, true_and, if_true, decide_true, Bool.true_and,
        bytesLE_zero16, chainHeaderP_zero _ _ _ _ _ ht hl hi hs8]
    · have hg' : topIsG i = false := by simpa using hg
      simp only [chainInputPL, topChainInput, hg', Bool.false_eq_true, and_false, if_false, decide_true,
        Bool.true_and, chainInputP, chainInput, bytesLE_zero16, chainHeaderP_zero _ _ _ _ _ ht hl hi hs8]
  · rename_i h0
    apply fold_steps_eq
    intro s hs v
    have hs8 : s < 8 := by
      have := List.mem_range'_1.mp hs
      rcases hsteps with hzero | hbound <;> omega
    simp only [chainInputPL, h0, false_and, if_false, decide_false, Bool.false_and, projHash_false, chainInputP,
      chainInput, bytesLE_zero16, chainHeaderP_zero _ _ _ _ _ ht hl hi hs8]
theorem route_packed_bound (index : Nat) (lay : Layer) (hindex : index < 2^31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2^32 := by
  fin_cases lay <;> simp [route, height] <;> omega
/-- Witness stack: `chainPL` with zero pads on the routed tree is `T3.layChain`. -/
theorem chainPL_zero_route (index : Nat) (lay : Layer) (i : Fin (chainCount lay))
    (digit : Nat) (value : Digest) (hindex : index < 2^31) :
    chainPL lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) 0 0 0 value =
    layChain lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) value := by
  have hi := i.isLt
  apply chainPL_zero
  · fin_cases lay <;> simp [route, height] <;> omega
  · fin_cases lay <;> simp [route, height] <;> omega
  · fin_cases lay <;> simp [chainCount] at hi <;> omega
  · have hm : maxDigit lay i.val ≤ 7 := by unfold maxDigit; split_ifs <;> decide
    omega
  · intro h0; subst h0; simp [route, height]; omega
theorem chainP_zero_route (index : Nat) (lay : Layer) (i : Fin (chainCount lay))
    (digit : Nat) (value : Digest) (hindex : index < 2^31) :
    chainP lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) 0 0 0 value =
    chain lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) value := by
  have hi := i.isLt
  apply chainP_zero
  · fin_cases lay <;> simp [route, height] <;> omega
  · fin_cases lay <;> simp [route, height] <;> omega
  · fin_cases lay <;> simp [chainCount] at hi <;> omega
  · have hm : maxDigit lay i.val ≤ 7 := by unfold maxDigit; split_ifs <;> decide
    omega
@[simp] theorem foldPad_zero (leaves : List Nat) (level node used next : Nat) :
    foldPad 0 leaves level node used next = 0 := by
  unfold foldPad; split <;> [rfl; split <;> rfl]
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Dfs ====
section

section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
theorem xor_one_div_two (x : Nat) : (x ^^^ 1) / 2 = x / 2 := by
  rw [Nat.xor_div_two]; simp
theorem xor_one_mod_two (x : Nat) : (x ^^^ 1) % 2 = 1 - x % 2 := by
  have h := @Nat.xor_mod_two_eq_one x 1
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (x ^^^ 1) with hy | hy <;> simp_all
theorem xor_one_eq (x : Nat) : x ^^^ 1 = 2 * (x / 2) + (1 - x % 2) := by
  have h1 := xor_one_div_two x
  have h2 := xor_one_mod_two x
  have := Nat.div_add_mod (x ^^^ 1) 2
  omega
theorem xor_one_ne (x : Nat) : x ^^^ 1 ≠ x := by
  have := xor_one_eq x; omega
theorem xor_one_xor_one (x : Nat) : x ^^^ 1 ^^^ 1 = x := by
  rw [Nat.xor_assoc]; simp
theorem eq_xor_one_of {x y : Nat} (hdiv : x / 2 = y / 2) (hne : x ≠ y) : y = x ^^^ 1 := by
  have := xor_one_eq x; omega
theorem two_pow_add_xor_one {m u : Nat} (hm : 1 ≤ m) : (2 ^ m + u) ^^^ 1 = 2 ^ m + (u ^^^ 1) := by
  have h2 : 2 ^ m % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]; simp
  rw [xor_one_eq, xor_one_eq u]
  have hd : (2 ^ m + u) / 2 = 2 ^ m / 2 + u / 2 := by omega
  omega
theorem div_eq_iff_lca {x y : Nat} (h : x ≠ y) (ℓ : Nat) : x / 2 ^ ℓ = y / 2 ^ ℓ ↔ lcaLevel x y ≤ ℓ := by
  have hx : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr h
  unfold lcaLevel
  constructor
  · intro he
    have h0 : (x ^^^ y) / 2 ^ ℓ = 0 := by rw [Nat.xor_div_two_pow, he, Nat.xor_self]
    have hlt : x ^^^ y < 2 ^ ℓ := by
      by_contra hc
      have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos ℓ)
      omega
    have := (Nat.log2_lt hx).mpr hlt
    omega
  · intro hl
    have hlt : x ^^^ y < 2 ^ ℓ := (Nat.log2_lt hx).mp (by omega)
    have h0 : (x ^^^ y) / 2 ^ ℓ = 0 := Nat.div_eq_of_lt hlt
    rw [Nat.xor_div_two_pow] at h0
    exact xor_eq_zero_iff.mp h0
theorem lcaLevel_comm (x y : Nat) : lcaLevel x y = lcaLevel y x := by
  unfold lcaLevel; rw [Nat.xor_comm]
theorem lcaLevel_pos (x y : Nat) : 0 < lcaLevel x y := by unfold lcaLevel; omega
theorem div_ne_of_lt_lca {x y : Nat} (h : x ≠ y) {ℓ : Nat} (hl : ℓ < lcaLevel x y) :
    x / 2 ^ ℓ ≠ y / 2 ^ ℓ := fun he => by have := (div_eq_iff_lca h ℓ).mp he; omega
theorem div_eq_of_lca_le {x y : Nat} (h : x ≠ y) {ℓ : Nat} (hl : lcaLevel x y ≤ ℓ) :
    x / 2 ^ ℓ = y / 2 ^ ℓ := (div_eq_iff_lca h ℓ).mpr hl
theorem div_pow_mono {x y : Nat} (h : x ≤ y) (ℓ : Nat) : x / 2 ^ ℓ ≤ y / 2 ^ ℓ := Nat.div_le_div_right h
theorem lca_outer {x0 x1 x2 : Nat} (h01 : x0 < x1) (h12 : x1 < x2) :
    lcaLevel x0 x2 = max (lcaLevel x0 x1) (lcaLevel x1 x2) := by
  have key : ∀ ℓ, x0 / 2 ^ ℓ = x2 / 2 ^ ℓ ↔ x0 / 2 ^ ℓ = x1 / 2 ^ ℓ ∧ x1 / 2 ^ ℓ = x2 / 2 ^ ℓ := by
    intro ℓ
    have a := div_pow_mono h01.le ℓ
    have b := div_pow_mono h12.le ℓ
    constructor
    · intro he; constructor <;> omega
    · rintro ⟨h1, h2⟩; omega
  apply le_antisymm
  · rw [← div_eq_iff_lca (by omega), key]
    exact ⟨div_eq_of_lca_le (by omega) (le_max_left _ _), div_eq_of_lca_le (by omega) (le_max_right _ _)⟩
  · apply max_le
    · rw [← div_eq_iff_lca (by omega)]; exact ((key _).mp (div_eq_of_lca_le (by omega) le_rfl)).1
    · rw [← div_eq_iff_lca (by omega)]; exact ((key _).mp (div_eq_of_lca_le (by omega) le_rfl)).2
theorem lca_ne {x0 x1 x2 : Nat} (h01 : x0 < x1) (h12 : x1 < x2) : lcaLevel x0 x1 ≠ lcaLevel x1 x2 := by
  intro he
  set d := lcaLevel x0 x1 with hd
  have hpos := lcaLevel_pos x0 x1
  have n01 := div_ne_of_lt_lca (show x0 ≠ x1 by omega) (show d - 1 < lcaLevel x0 x1 by omega)
  have n12 := div_ne_of_lt_lca (show x1 ≠ x2 by omega) (show d - 1 < lcaLevel x1 x2 by omega)
  have e01 := div_eq_of_lca_le (show x0 ≠ x1 by omega) (show lcaLevel x0 x1 ≤ d by omega)
  have e12 := div_eq_of_lca_le (show x1 ≠ x2 by omega) (show lcaLevel x1 x2 ≤ d by omega)
  have hp : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at e01 e12
  have a := div_pow_mono h01.le (d - 1)
  have b := div_pow_mono h12.le (d - 1)
  omega
theorem div_sib_of_lca {x y : Nat} (h : x ≠ y) {k : Nat} (hk : lcaLevel x y = k + 1) :
    y / 2 ^ k = x / 2 ^ k ^^^ 1 := by
  apply eq_xor_one_of
  · rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ]
    exact div_eq_of_lca_le h (by omega)
  · exact fun he => div_ne_of_lt_lca h (show k < lcaLevel x y by omega) he
theorem lca_of_div_sib {x y : Nat} {k : Nat} (hs : y / 2 ^ k = x / 2 ^ k ^^^ 1) : lcaLevel x y = k + 1 := by
  have hxy : x ≠ y := fun he => by rw [he] at hs; exact xor_one_ne _ hs.symm
  have hne : x / 2 ^ k ≠ y / 2 ^ k := by rw [hs]; exact (xor_one_ne _).symm
  have heq : x / 2 ^ (k + 1) = y / 2 ^ (k + 1) := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hs, xor_one_div_two]
  have h1 := (div_eq_iff_lca hxy (k + 1)).mp heq
  have h2 : ¬ lcaLevel x y ≤ k := fun hc => hne ((div_eq_iff_lca hxy k).mpr hc)
  omega
theorem heap_eq {g ℓ : Nat} (hl : ℓ ≤ 11) : (2048 + g) / 2 ^ ℓ = 2 ^ (11 - ℓ) + g / 2 ^ ℓ := by
  have h2 : 2048 = 2 ^ (11 - ℓ) * 2 ^ ℓ := by rw [← pow_add, Nat.sub_add_cancel hl]; norm_num
  rw [h2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos ℓ), Nat.add_comm]
theorem heap_div_two (g k : Nat) : (2048 + g) / 2 ^ k / 2 = (2048 + g) / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]
theorem heap_div_pow (g k a : Nat) : (2048 + g) / 2 ^ k / 2 ^ a = (2048 + g) / 2 ^ (k + a) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]
theorem heap_mod_two {g k : Nat} (hk : k < 11) : (2048 + g) / 2 ^ k % 2 = g / 2 ^ k % 2 := by
  rw [heap_eq (by omega)]
  obtain ⟨m, hm⟩ : ∃ m, 11 - k = m + 1 := ⟨10 - k, by omega⟩
  rw [hm, pow_succ]; omega
theorem heap_parent {g k : Nat} (hk : k < 11) :
    (2048 + g) / 2 ^ k / 2 = 2 ^ (11 - (k + 1)) + g / 2 ^ k / 2 := by
  rw [heap_div_two, heap_eq (by omega), Nat.div_div_eq_div_mul, ← pow_succ]
theorem heap_sib {g g' k : Nat} (h : g ≠ g') (hk : k + 1 ≤ 11) (hl : lcaLevel g g' = k + 1) :
    (2048 + g) / 2 ^ k ^^^ 1 = (2048 + g') / 2 ^ k := by
  rw [heap_eq (by omega), heap_eq (by omega), two_pow_add_xor_one (by omega), div_sib_of_lca h hl]
theorem heap_level_of_two_le {g K : Nat} (hg : g < 2048) (h2 : 2 ≤ (2048 + g) / 2 ^ K) : K ≤ 10 := by
  by_contra hc
  have : (2048 + g) / 2 ^ K < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos K)]
    have : 2 ^ 11 ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) (by omega)
    have h12 : (2 : Nat) ^ 12 = 2 * 2 ^ 11 := by norm_num
    calc 2048 + g < 4096 := by omega
      _ = 2 * 2 ^ 11 := by norm_num
      _ ≤ 2 * 2 ^ K := by omega
  omega
theorem log2_heap {g K : Nat} (hg : g < 2048) (hK : K ≤ 11) : ((2048 + g) / 2 ^ K).log2 = 11 - K := by
  rw [heap_eq hK]
  have hlt : g / 2 ^ K < 2 ^ (11 - K) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos K), ← pow_add, Nat.sub_add_cancel hK]; norm_num; omega
  rw [Nat.log2_eq_iff (by positivity)]
  generalize g / 2 ^ K = d at *
  constructor
  · omega
  · rw [pow_succ]; omega
theorem log2_xor_one {x : Nat} (hx : 2 ≤ x) : (x ^^^ 1).log2 = x.log2 := by
  have hx1 : x ^^^ 1 ≠ 0 := by have := xor_one_eq x; omega
  have hx0 : x ≠ 0 := by omega
  have e1 := Nat.log2_self_le hx0
  have e2 := Nat.lt_log2_self (n := x)
  have hle : 1 ≤ x.log2 := (Nat.le_log2 hx0).mpr (by omega)
  rw [Nat.log2_eq_iff hx1]
  have hxo := xor_one_eq x
  obtain ⟨m, hm⟩ : ∃ m, x.log2 = m + 1 := ⟨x.log2 - 1, by omega⟩
  rw [hm] at e1 e2 ⊢
  rw [pow_succ] at e1 e2 ⊢
  constructor <;> omega
theorem heap_sib_inv {g g' K K' : Nat} (hg : g < 2048) (hg' : g' < 2048)
    (hs : (2048 + g) / 2 ^ K ^^^ 1 = (2048 + g') / 2 ^ K') (h2 : 2 ≤ (2048 + g') / 2 ^ K') :
    K' ≤ 10 ∧ K = K' ∧ lcaLevel g g' = K + 1 := by
  have hK' := heap_level_of_two_le hg' h2
  have hx2 : 2 ≤ (2048 + g) / 2 ^ K := by
    have := xor_one_eq ((2048 + g) / 2 ^ K); omega
  have hK := heap_level_of_two_le hg hx2
  have hlog := congrArg Nat.log2 hs
  rw [log2_xor_one hx2, log2_heap hg (by omega), log2_heap hg' (by omega)] at hlog
  have hKK : K = K' := by omega
  subst hKK
  refine ⟨hK', rfl, ?_⟩
  rw [heap_eq (by omega), heap_eq (by omega), two_pow_add_xor_one (by omega)] at hs
  exact lca_of_div_sib (by omega)
theorem bucket_leaf_lt {b x : Nat} (hb : b < 16) (hx : x < 128) : b * 128 + x < 2048 := by omega
theorem bucket_div {b x k : Nat} (_hx : x < 128) (hk : k ≤ 7) :
    (b * 128 + x) / 2 ^ k = b * 2 ^ (7 - k) + x / 2 ^ k := by
  have h : b * 128 = b * 2 ^ (7 - k) * 2 ^ k := by
    rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hk]; norm_num
  rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.add_comm]
theorem bucket_div_eight {b x : Nat} (hx : x < 128) : (b * 128 + x) / 2 ^ 7 = b := by
  rw [bucket_div hx le_rfl]; simp only [Nat.sub_self, pow_zero, Nat.mul_one]
  rw [Nat.div_eq_of_lt (by norm_num; omega)]; simp
theorem bucket_div_outer {b x j : Nat} (hx : x < 128) : (b * 128 + x) / 2 ^ (7 + j) = b / 2 ^ j := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, bucket_div_eight hx]
theorem lca_le_eight {b x y : Nat} (hx : x < 128) (hy : y < 128) (hxy : x ≠ y) :
    lcaLevel (b * 128 + x) (b * 128 + y) ≤ 7 :=
  (div_eq_iff_lca (by omega) 7).mp (by rw [bucket_div_eight hx, bucket_div_eight hy])
theorem lca_bucket {b x y : Nat} (hx : x < 128) (hy : y < 128) (hxy : x ≠ y) :
    lcaLevel (b * 128 + x) (b * 128 + y) = lcaLevel x y := by
  have hl := lca_le_eight (b := b) hx hy hxy
  have hl' : lcaLevel x y ≤ 7 :=
    (div_eq_iff_lca hxy 7).mp (by rw [Nat.div_eq_of_lt (by norm_num; omega), Nat.div_eq_of_lt (by norm_num; omega)])
  have key : ∀ ℓ, ℓ ≤ 7 → ((b * 128 + x) / 2 ^ ℓ = (b * 128 + y) / 2 ^ ℓ ↔ x / 2 ^ ℓ = y / 2 ^ ℓ) := by
    intro ℓ hℓ; rw [bucket_div hx hℓ, bucket_div hy hℓ]; omega
  apply le_antisymm
  · rw [← div_eq_iff_lca (by omega), key _ hl']; exact div_eq_of_lca_le hxy le_rfl
  · rw [← div_eq_iff_lca hxy, ← key _ hl]; exact div_eq_of_lca_le (by omega) le_rfl
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem hasLeaf_iff (leaves : List Nat) (level node : Nat) :
    hasLeaf leaves level node = true ↔ ∃ leaf ∈ leaves, leaf / 2 ^ level = node := by
  simp only [hasLeaf, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨leaf, hm, hlo, hhi⟩
    exact ⟨leaf, hm, Nat.div_eq_of_lt_le hlo hhi⟩
  · rintro ⟨leaf, hm, rfl⟩
    exact ⟨leaf, hm, Nat.div_mul_le_self leaf _, by
      rw [Nat.add_mul, Nat.one_mul]; have := Nat.lt_div_mul_add (a := leaf) (Nat.two_pow_pos level); omega⟩
theorem hasLeaf_false_iff (leaves : List Nat) (level node : Nat) :
    hasLeaf leaves level node = false ↔ ∀ leaf ∈ leaves, leaf / 2 ^ level ≠ node := by
  rw [← Bool.not_eq_true, hasLeaf_iff]; simp
theorem hasLeaf_self {leaves : List Nat} {g : Nat} (hg : g ∈ leaves) (k : Nat) :
    hasLeaf leaves k (g / 2 ^ k) = true := (hasLeaf_iff _ _ _).mpr ⟨g, hg, rfl⟩
theorem hasLeaf_sib_false {leaves : List Nat} {g k : Nat}
    (h : ∀ g' ∈ leaves, g' ≠ g → lcaLevel g g' ≠ k + 1) : hasLeaf leaves k (g / 2 ^ k ^^^ 1) = false := by
  rw [hasLeaf_false_iff]
  intro g' hg' he
  by_cases hgg : g' = g
  · subst hgg; exact xor_one_ne _ he.symm
  · exact h g' hg' hgg (lca_of_div_sib he)
def dfsPad (leaves : List Nat) (pad : Nat × Nat → Digest) (level node : Nat) : Digest :=
  if !hasLeaf leaves level (2 * node) then pad (level, 2 * node)
  else if !hasLeaf leaves level (2 * node + 1) then pad (level, 2 * node + 1) else 0
def dfsP (index coord : Nat) (leaves : List Nat) (leafH : Nat → M Digest) (val pad : Nat × Nat → Digest) :
    Nat → Nat → M Digest
  | level, node =>
      if !hasLeaf leaves level node then pure (val (level, node))
      else match level with
      | 0 => leafH node
      | level + 1 => do
          let left ← dfsP index coord leaves leafH val pad level (2 * node)
          let right ← dfsP index coord leaves leafH val pad level (2 * node + 1)
          nodeHashP 10 coord index (2 ^ (11 - (level + 1)) + node) left (dfsPad leaves pad level node) right
def leafHP (index coord : Nat) (leaves : List Nat) (values : List Digest) (pads : Pads) (node : Nat) : M Digest :=
  ftsLeafP index coord node (pads.leaf ⟨(3 * coord + leaves.idxOf node) % 22, Nat.mod_lt _ (by decide)⟩)
    (values.getD (leaves.idxOf node) 0)
    (pads.leaf ⟨(3 * coord + leaves.idxOf node + 1) % 22, Nat.mod_lt _ (by decide)⟩)
def SlotsMatch (proof : Fin 115 → Digest) (pads : Pads) (val pad : Nat × Nat → Digest) (used : Nat)
    (ps : List (Nat × Nat)) : Prop :=
  ∀ i (hi : i < ps.length) (h : used + i < 115), proof ⟨used + i, h⟩ = val ps[i] ∧ pads.fold ⟨used + i, h⟩ = pad ps[i]
theorem SlotsMatch.left {proof : Fin 115 → Digest} {pads : Pads} {val pad : Nat × Nat → Digest} {used : Nat}
    {l r : List (Nat × Nat)} (h : SlotsMatch proof pads val pad used (l ++ r)) : SlotsMatch proof pads val pad used l := by
  intro i hi hb
  have := h i (by simp; omega) hb
  rwa [List.getElem_append_left hi] at this
theorem SlotsMatch.right {proof : Fin 115 → Digest} {pads : Pads} {val pad : Nat × Nat → Digest} {used : Nat}
    {l r : List (Nat × Nat)} (h : SlotsMatch proof pads val pad used (l ++ r)) :
    SlotsMatch proof pads val pad (used + l.length) r := by
  intro i hi hb
  have := h (l.length + i) (by simp; omega) (by omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  simpa only [Nat.add_assoc] using this
theorem recoverChildP_eq_dfsP (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) (pads : Pads) (val pad : Nat × Nat → Digest) :
    ∀ level node used, used + (frontier leaves level node).length ≤ 115 →
      SlotsMatch proof pads val pad used (frontier leaves level node) →
      recoverChildP index coord leaves values proof pads level node used =
        (fun v => some (v, used + (frontier leaves level node).length)) <$>
          dfsP index coord leaves (leafHP index coord leaves values pads) val pad level node := by
  intro level
  induction level with
  | zero =>
      intro node used hfit hm
      by_cases hh : hasLeaf leaves 0 node = true
      · simp only [recoverChildP, dfsP, hh, Bool.not_true, Bool.false_eq_true, ite_false, T3.frontier, ite_true,
          List.length_nil, Nat.add_zero, leafHP, map_eq_bind_pure_comp, Function.comp_def]
      · have hh : hasLeaf leaves 0 node = false := by simpa using hh
        simp only [T3.frontier, hh, Bool.false_eq_true, ite_false, List.length_singleton] at hfit hm ⊢
        have hp := (hm 0 (by simp) (by omega)).1
        simp only [recoverChildP, dfsP, hh, Bool.not_false, ite_true, dif_pos (show used < 115 by omega),
          map_pure]
        simp only [Nat.add_zero] at hp
        rw [hp]; rfl
  | succ level ih =>
      intro node used hfit hm
      by_cases hh : hasLeaf leaves (level + 1) node = true
      · have hsplit : frontier leaves (level + 1) node =
            frontier leaves level (2 * node) ++ frontier leaves level (2 * node + 1) := by
          simp only [T3.frontier, hh, ite_true]
        rw [hsplit, List.length_append] at hfit
        rw [hsplit] at hm
        have hleft := ih (2 * node) used (by omega) hm.left
        have hright := ih (2 * node + 1) (used + (frontier leaves level (2 * node)).length) (by omega) hm.right
        have hpad : foldPad pads leaves level node used (used + (frontier leaves level (2 * node)).length) =
            dfsPad leaves pad level node := by
          unfold foldPad dfsPad
          by_cases hl : hasLeaf leaves level (2 * node) = true
          · by_cases hr : hasLeaf leaves level (2 * node + 1) = true
            · simp [hl, hr]
            · have hr : hasLeaf leaves level (2 * node + 1) = false := by simpa using hr
              have hlen : (frontier leaves level (2 * node + 1)) = [(level, 2 * node + 1)] := by
                cases level <;> simp [T3.frontier, hr]
              have := (hm.right 0 (by simp [hlen]) (by rw [hlen] at hfit; simp at hfit; omega)).2
              simp only [hlen, List.getElem_cons_zero, Nat.add_zero] at this
              simp only [hl, hr, Bool.not_true, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
              rw [← this]; congr 1; ext; simp only [Fin.val_mk]; rw [Nat.mod_eq_of_lt]
              rw [hlen] at hfit; simp at hfit; omega
          · have hl : hasLeaf leaves level (2 * node) = false := by simpa using hl
            have hlen : (frontier leaves level (2 * node)) = [(level, 2 * node)] := by
              cases level <;> simp [T3.frontier, hl]
            have := (hm.left 0 (by simp [hlen]) (by rw [hlen] at hfit; simp at hfit; omega)).2
            simp only [hlen, List.getElem_cons_zero, Nat.add_zero] at this
            simp only [hl, Bool.not_false, ite_true]
            rw [← this]; congr 1; ext; simp only [Fin.val_mk]; rw [Nat.mod_eq_of_lt]
            rw [hlen] at hfit; simp at hfit; omega
        conv_lhs => unfold recoverChildP
        conv_rhs => unfold dfsP
        simp only [hh, Bool.not_true, Bool.false_eq_true, ite_false, hleft, hright, hpad, hsplit,
          List.length_append, bind_map_left, map_bind, Nat.add_assoc]
        rfl
      · have hh : hasLeaf leaves (level + 1) node = false := by simpa using hh
        simp only [T3.frontier, hh, Bool.false_eq_true, ite_false, List.length_singleton] at hfit hm ⊢
        have hp := (hm 0 (by simp) (by omega)).1
        simp only [recoverChildP, dfsP, hh, Bool.not_false, ite_true, dif_pos (show used < 115 by omega),
          map_pure]
        simp only [Nat.add_zero] at hp
        rw [hp]; rfl
def climbStep (index coord : Nat) (val pad : Nat × Nat → Digest) (g k : Nat) (v : Digest) : M Digest :=
  if g / 2 ^ k % 2 = 1 then
    nodeHashP 10 coord index (2 ^ (11 - (k + 1)) + g / 2 ^ k / 2) (val (k, g / 2 ^ k ^^^ 1)) (pad (k, g / 2 ^ k ^^^ 1)) v
  else
    nodeHashP 10 coord index (2 ^ (11 - (k + 1)) + g / 2 ^ k / 2) v (pad (k, g / 2 ^ k ^^^ 1)) (val (k, g / 2 ^ k ^^^ 1))
def climbV (index coord : Nat) (val pad : Nat × Nat → Digest) (g : Nat) : Nat → Nat → Digest → M Digest
  | _, 0, v => pure v
  | lo, a + 1, v => do
      let v ← climbStep index coord val pad g lo v
      climbV index coord val pad g (lo + 1) a v
section climb
variable (index coord : Nat) (val pad : Nat × Nat → Digest) (g : Nat)
@[simp] theorem climbV_zero (lo : Nat) (v : Digest) : climbV index coord val pad g lo 0 v = pure v := rfl
@[simp] theorem climbV_zero' (lo : Nat) : climbV index coord val pad g lo 0 = pure := rfl
theorem climbV_succ (lo a : Nat) (v : Digest) :
    climbV index coord val pad g lo (a + 1) v =
      climbStep index coord val pad g lo v >>= climbV index coord val pad g (lo + 1) a := rfl
theorem climbV_snoc : ∀ (a lo : Nat) (v : Digest), climbV index coord val pad g lo (a + 1) v =
    climbV index coord val pad g lo a v >>= climbStep index coord val pad g (lo + a) := by
  intro a
  induction a with
  | zero => intro lo v; simp only [climbV_succ, climbV_zero', bind_pure, Nat.add_zero, pure_bind]
  | succ a ih =>
      intro lo v
      rw [climbV_succ, climbV_succ, bind_assoc]
      congr 1; funext x
      rw [ih]; simp only [Nat.add_assoc, Nat.add_comm 1 a]
theorem climbV_add : ∀ (a b lo : Nat) (v : Digest), climbV index coord val pad g lo (a + b) v =
    climbV index coord val pad g lo a v >>= climbV index coord val pad g (lo + a) b := by
  intro a
  induction a with
  | zero => intro b lo v; simp
  | succ a ih =>
      intro b lo v
      rw [show a + 1 + b = (a + b) + 1 by omega, climbV_succ, climbV_succ, bind_assoc]
      congr 1; funext x
      rw [ih]; simp only [Nat.add_assoc, Nat.add_comm 1 a]
end climb
section dfs
variable {index coord : Nat} {leaves : List Nat} {leafH : Nat → M Digest} {val pad : Nat × Nat → Digest}
theorem dfsP_empty {level node : Nat} (h : hasLeaf leaves level node = false) :
    dfsP index coord leaves leafH val pad level node = pure (val (level, node)) := by
  cases level <;> simp [dfsP, h]
theorem dfsP_leaf {node : Nat} (h : hasLeaf leaves 0 node = true) :
    dfsP index coord leaves leafH val pad 0 node = leafH node := by
  simp [dfsP, h]
theorem dfsP_node {l node : Nat} (h : hasLeaf leaves (l + 1) node = true) :
    dfsP index coord leaves leafH val pad (l + 1) node = (do
      let left ← dfsP index coord leaves leafH val pad l (2 * node)
      let right ← dfsP index coord leaves leafH val pad l (2 * node + 1)
      nodeHashP 10 coord index (2 ^ (11 - (l + 1)) + node) left (dfsPad leaves pad l node) right) := by
  conv_lhs => unfold dfsP
  simp [h]
theorem hasLeaf_parent {l n : Nat} (h : hasLeaf leaves l n = true) : hasLeaf leaves (l + 1) (n / 2) = true := by
  obtain ⟨leaf, hm, he⟩ := (hasLeaf_iff _ _ _).mp h
  exact (hasLeaf_iff _ _ _).mpr ⟨leaf, hm, by rw [pow_succ, ← Nat.div_div_eq_div_mul, he]⟩
theorem dfsP_merge {l n : Nat} (hl : hasLeaf leaves l (2 * n) = true) (hr : hasLeaf leaves l (2 * n + 1) = true) :
    dfsP index coord leaves leafH val pad (l + 1) n = (do
      let left ← dfsP index coord leaves leafH val pad l (2 * n)
      let right ← dfsP index coord leaves leafH val pad l (2 * n + 1)
      nodeHash 10 coord index (2 ^ (11 - (l + 1)) + n) left right) := by
  have hp : hasLeaf leaves (l + 1) n = true := by
    have := hasLeaf_parent (leaves := leaves) hl; rwa [show 2 * n / 2 = n by omega] at this
  rw [dfsP_node hp]
  have : dfsPad leaves pad l n = 0 := by simp [dfsPad, hl, hr]
  simp only [this, nodeHashP_zero]
theorem dfsP_climb {g : Nat} (hg : g ∈ leaves) (lo : Nat) : ∀ d,
    (∀ k, lo ≤ k → k < lo + d → hasLeaf leaves k (g / 2 ^ k ^^^ 1) = false) →
    dfsP index coord leaves leafH val pad (lo + d) (g / 2 ^ (lo + d)) =
      dfsP index coord leaves leafH val pad lo (g / 2 ^ lo) >>= climbV index coord val pad g lo d := by
  intro d
  induction d with
  | zero => intro _; simp only [Nat.add_zero, climbV_zero', bind_pure]
  | succ d ih =>
      intro hsib
      rw [show lo + (d + 1) = (lo + d) + 1 by omega]
      set k := lo + d with hk
      set n := g / 2 ^ k with hn
      have hdiv : g / 2 ^ (k + 1) = n / 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
      have hpar : hasLeaf leaves (k + 1) (n / 2) = true := by rw [← hdiv]; exact hasLeaf_self hg _
      have hself : hasLeaf leaves k n = true := hasLeaf_self hg k
      have hsk : hasLeaf leaves k (n ^^^ 1) = false := hsib k (by omega) (by omega)
      have ihk := ih (fun k' h1 h2 => hsib k' h1 (by omega))
      have hrhs : dfsP index coord leaves leafH val pad lo (g / 2 ^ lo) >>= climbV index coord val pad g lo (d + 1) =
          dfsP index coord leaves leafH val pad k n >>= climbStep index coord val pad g k := by
        rw [ihk, bind_assoc]; congr 1; funext v; exact climbV_snoc index coord val pad g d lo v
      rw [hdiv, dfsP_node hpar, hrhs]
      have hx := xor_one_eq n
      rcases Nat.mod_two_eq_zero_or_one n with hpar2 | hpar2
      · have e1 : 2 * (n / 2) = n := by omega
        have e2 : 2 * (n / 2) + 1 = n ^^^ 1 := by omega
        have hpad : dfsPad leaves pad k (n / 2) = pad (k, n ^^^ 1) := by
          unfold dfsPad; rw [e2, e1]; simp [hself, hsk]
        rw [e2, e1, hpad, dfsP_empty hsk]
        congr 1; funext v
        simp [climbStep, ← hn, hpar2]
      · have e1 : 2 * (n / 2) = n ^^^ 1 := by omega
        have e2 : 2 * (n / 2) + 1 = n := by omega
        have hpad : dfsPad leaves pad k (n / 2) = pad (k, n ^^^ 1) := by
          unfold dfsPad; rw [e2, e1]; simp [hsk]
        rw [e2, e1, hpad, dfsP_empty hsk, pure_bind]
        congr 1; funext v
        simp [climbStep, ← hn, hpar2]
end dfs
def coordCanon (index coord : Nat) (leafH : Nat → M Digest) (val pad : Nat × Nat → Digest) (g0 g1 g2 : Nat) :
    M Digest :=
  if lcaLevel g0 g1 < lcaLevel g1 g2 then do
    let v0 ← leafH g0
    let v0 ← climbV index coord val pad g0 0 (lcaLevel g0 g1 - 1) v0
    let v1 ← leafH g1
    let v1 ← climbV index coord val pad g1 0 (lcaLevel g0 g1 - 1) v1
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g0 g1) + g1 / 2 ^ lcaLevel g0 g1) v0 v1
    let m ← climbV index coord val pad g1 (lcaLevel g0 g1) (lcaLevel g1 g2 - 1 - lcaLevel g0 g1) m
    let v2 ← leafH g2
    let v2 ← climbV index coord val pad g2 0 (lcaLevel g1 g2 - 1) v2
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g1 g2) + g2 / 2 ^ lcaLevel g1 g2) m v2
    climbV index coord val pad g2 (lcaLevel g1 g2) (11 - lcaLevel g1 g2) m
  else do
    let v0 ← leafH g0
    let v0 ← climbV index coord val pad g0 0 (lcaLevel g0 g1 - 1) v0
    let v1 ← leafH g1
    let v1 ← climbV index coord val pad g1 0 (lcaLevel g1 g2 - 1) v1
    let v2 ← leafH g2
    let v2 ← climbV index coord val pad g2 0 (lcaLevel g1 g2 - 1) v2
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g1 g2) + g2 / 2 ^ lcaLevel g1 g2) v1 v2
    let m ← climbV index coord val pad g2 (lcaLevel g1 g2) (lcaLevel g0 g1 - 1 - lcaLevel g1 g2) m
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g0 g1) + g2 / 2 ^ lcaLevel g0 g1) v0 m
    climbV index coord val pad g2 (lcaLevel g0 g1) (11 - lcaLevel g0 g1) m
theorem merge_children {g g' l : Nat} (hlt : g < g') (hl : lcaLevel g g' = l + 1) :
    2 * (g' / 2 ^ (l + 1)) = g / 2 ^ l ∧ 2 * (g' / 2 ^ (l + 1)) + 1 = g' / 2 ^ l := by
  have hs := div_sib_of_lca (show g ≠ g' by omega) hl
  have hm := div_pow_mono hlt.le l
  have hx := xor_one_eq (g / 2 ^ l)
  have hd : g' / 2 ^ (l + 1) = g' / 2 ^ l / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hd]
  generalize g / 2 ^ l = u at *
  generalize g' / 2 ^ l = v at *
  subst hs
  omega
section bucket
variable {index coord : Nat} {leafH : Nat → M Digest} {val pad : Nat × Nat → Digest}
theorem dfsP_bucket {g0 g1 g2 b : Nat} (h01 : g0 < g1) (h12 : g1 < g2)
    (hb0 : g0 / 2 ^ 7 = b) (hb1 : g1 / 2 ^ 7 = b) (hb2 : g2 / 2 ^ 7 = b) :
    dfsP index coord [g0, g1, g2] leafH val pad 7 b >>= climbV index coord val pad g2 7 4 =
      coordCanon index coord leafH val pad g0 g1 g2 := by
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [hb0, hb1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [hb1, hb2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer h01 h12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne h01 h12
  have c10 : lcaLevel g1 g0 = lcaLevel g0 g1 := lcaLevel_comm _ _
  have c21 : lcaLevel g2 g1 = lcaLevel g1 g2 := lcaLevel_comm _ _
  have c20 : lcaLevel g2 g0 = lcaLevel g0 g2 := lcaLevel_comm _ _
  have sib : ∀ g k, (∀ g' ∈ [g0, g1, g2], g' ≠ g → lcaLevel g g' ≠ k + 1) →
      hasLeaf [g0, g1, g2] k (g / 2 ^ k ^^^ 1) = false := fun g k h => hasLeaf_sib_false h
  have s0 : ∀ k, k + 1 < lcaLevel g0 g1 → hasLeaf [g0, g1, g2] k (g0 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' | omega
  have s1lo : ∀ k, k + 1 < min (lcaLevel g0 g1) (lcaLevel g1 g2) →
      hasLeaf [g0, g1, g2] k (g1 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' | (rw [c10]; omega) | omega
  have s1hi : ∀ k, lcaLevel g0 g1 ≤ k → k + 1 < lcaLevel g1 g2 →
      hasLeaf [g0, g1, g2] k (g1 / 2 ^ k ^^^ 1) = false := by
    intro k hk1 hk2; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' | (rw [c10]; omega) | omega
  have s2lo : ∀ k, k + 1 < lcaLevel g1 g2 → hasLeaf [g0, g1, g2] k (g2 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;>
      first | exact absurd rfl hne' | (rw [c20, l02]; omega) | (rw [c21]; omega) | omega
  have s2mid : ∀ k, lcaLevel g1 g2 ≤ k → k + 1 < lcaLevel g0 g1 →
      hasLeaf [g0, g1, g2] k (g2 / 2 ^ k ^^^ 1) = false := by
    intro k hk1 hk2; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;>
      first | exact absurd rfl hne' | (rw [c20, l02]; omega) | (rw [c21]; omega) | omega
  have s2hi : ∀ k, max (lcaLevel g0 g1) (lcaLevel g1 g2) ≤ k →
      hasLeaf [g0, g1, g2] k (g2 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;>
      first | exact absurd rfl hne' | (rw [c20, l02]; omega) | (rw [c21]; omega) | omega
  have m0 : g0 ∈ [g0, g1, g2] := by simp
  have m1 : g1 ∈ [g0, g1, g2] := by simp
  have m2 : g2 ∈ [g0, g1, g2] := by simp
  have leafAt : ∀ g, g ∈ [g0, g1, g2] → dfsP index coord [g0, g1, g2] leafH val pad 0 (g / 2 ^ 0) = leafH g := by
    intro g hg; have h := hasLeaf_self hg 0; simp only [pow_zero, Nat.div_one] at h ⊢; exact dfsP_leaf h
  have outer : ∀ (lo : Nat) (v : Digest), lo ≤ 7 →
      climbV index coord val pad g2 lo (7 - lo) v >>= climbV index coord val pad g2 7 4 =
        climbV index coord val pad g2 lo (11 - lo) v := by
    intro lo v hlo
    rw [show 11 - lo = (7 - lo) + 4 by omega, climbV_add, show lo + (7 - lo) = 7 by omega]
  unfold coordCanon
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · rw [if_pos hA]
    have top := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 d12 (7 - d12) (fun k h1 _ => s2hi k (by omega))
    rw [show d12 + (7 - d12) = 7 by omega, hb2] at top
    obtain ⟨l, hl⟩ : ∃ l, d12 = l + 1 := ⟨d12 - 1, by omega⟩
    obtain ⟨c12a, c12b⟩ := merge_children h12 (show lcaLevel g1 g2 = l + 1 by rw [hd12, hl])
    have mid := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := l) (n := g2 / 2 ^ (l + 1)) (by rw [c12a]; exact hasLeaf_self m1 l) (by rw [c12b]; exact hasLeaf_self m2 l)
    rw [c12b, c12a] at mid
    have left := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m1 d01 (l - d01) (fun k h1 h2 => s1hi k h1 (by omega))
    rw [show d01 + (l - d01) = l by omega] at left
    obtain ⟨m, hm⟩ : ∃ m, d01 = m + 1 := ⟨d01 - 1, by omega⟩
    obtain ⟨c01a, c01b⟩ := merge_children h01 (show lcaLevel g0 g1 = m + 1 by rw [hd01, hm])
    have low := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := m) (n := g1 / 2 ^ (m + 1)) (by rw [c01a]; exact hasLeaf_self m0 m) (by rw [c01b]; exact hasLeaf_self m1 m)
    rw [c01b, c01a] at low
    have p0 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m0 0 m (fun k _ h2 => s0 k (by omega))
    have p1 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m1 0 m (fun k _ h2 => s1lo k (by omega))
    have p2 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 0 l (fun k _ h2 => s2lo k (by omega))
    simp only [Nat.zero_add] at p0 p1 p2
    rw [leafAt g0 m0] at p0; rw [leafAt g1 m1] at p1; rw [leafAt g2 m2] at p2
    rw [top, bind_assoc, hl, mid, ← hl, left, hm, low, ← hm, p0, p1, p2]
    have hout := fun v => outer (l + 1) v (by omega)
    simp only [bind_assoc, hl, hout]
    rw [show d01 - 1 = m by omega, show l + 1 - 1 - d01 = l - d01 by omega, show l + 1 - 1 = l by omega]
  · rw [if_neg hA]
    have hB : d12 < d01 := by omega
    have top := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 d01 (7 - d01) (fun k h1 _ => s2hi k (by omega))
    rw [show d01 + (7 - d01) = 7 by omega, hb2] at top
    obtain ⟨l, hl⟩ : ∃ l, d01 = l + 1 := ⟨d01 - 1, by omega⟩
    obtain ⟨c01a, c01b⟩ := merge_children h01 (show lcaLevel g0 g1 = l + 1 by rw [hd01, hl])
    have e21 : g2 / 2 ^ (l + 1) = g1 / 2 ^ (l + 1) := div_eq_of_lca_le (by omega) (by rw [c21]; omega)
    have e21' : g2 / 2 ^ l = g1 / 2 ^ l := div_eq_of_lca_le (by omega) (by rw [c21]; omega)
    have mid := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := l) (n := g2 / 2 ^ (l + 1)) (by rw [e21, c01a]; exact hasLeaf_self m0 l)
        (by rw [e21, c01b, ← e21']; exact hasLeaf_self m2 l)
    rw [e21, c01b, c01a, ← e21', ← e21] at mid
    have p0 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m0 0 l (fun k _ h2 => s0 k (by omega))
    have right := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 d12 (l - d12) (fun k h1 h2 => s2mid k h1 (by omega))
    rw [show d12 + (l - d12) = l by omega] at right
    obtain ⟨m, hm⟩ : ∃ m, d12 = m + 1 := ⟨d12 - 1, by omega⟩
    obtain ⟨c12a, c12b⟩ := merge_children h12 (show lcaLevel g1 g2 = m + 1 by rw [hd12, hm])
    have low := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := m) (n := g2 / 2 ^ (m + 1)) (by rw [c12a]; exact hasLeaf_self m1 m) (by rw [c12b]; exact hasLeaf_self m2 m)
    rw [c12b, c12a] at low
    have p1 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m1 0 m (fun k _ h2 => s1lo k (by omega))
    have p2 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 0 m (fun k _ h2 => s2lo k (by omega))
    simp only [Nat.zero_add] at p0 p1 p2
    rw [leafAt g0 m0] at p0; rw [leafAt g1 m1] at p1; rw [leafAt g2 m2] at p2
    rw [top, bind_assoc, hl, mid, ← hl, p0, right, hm, low, ← hm, p1, p2]
    have hout := fun v => outer (l + 1) v (by omega)
    simp only [bind_assoc, hl, hout]
    rw [show d12 - 1 = m by omega, show l + 1 - 1 - d12 = l - d12 by omega, show l + 1 - 1 = l by omega]
end bucket
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3M_Witness_Encode ====
section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
def expandN (message : Message) (pk : Digest) (sig : Signature) : M (Option (HashOutput × Witness)) := do
  let some (counter, output) ← digestSearch sig.rho message 0 attemptLimit | pure none
  let index := output.toNat % 2 ^ 31
  let some root ← recoverFts sig index (selections output) | pure none
  let some (root, counters) ← expandLayers sig index 4 root | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
def zeros (n : Nat) : List UInt8 := List.replicate n 0
def headerBytes (w : Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++
    (List.finRange 4).flatMap (fun lay => bytesLE 4 (w.counters lay)) ++ zeros 28
def leafBytes (sig : Signature) : List UInt8 :=
  (List.finRange 21).flatMap (fun s => zeros 32 ++ bytesLE 16 (sig.secrets s)) ++ zeros 16
def foldBytes (E : Nat) (sib : Digest) : List UInt8 :=
  if E % 2 = 1 then bytesLE 16 sib ++ zeros 48 else zeros 48 ++ bytesLE 16 sib
def segBytes (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) : List UInt8 :=
  [UInt8.ofNat seg.byte0] ++ zeros 7 ++ (List.range seg.a).flatMap fun r =>
    foldBytes (seg.heap r) (proof ⟨foldSlot chosen seg r % 115, Nat.mod_lt _ (by decide)⟩)
def streamBytes (chosen : List Selection) (proof : Fin 115 → Digest) : List UInt8 :=
  (((schedule chosen).flatMap (segBytes chosen proof)) ++ zeros 8200).take 8200
def layerBytes (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  (List.finRange (height lay)).reverse.flatMap (fun j =>
      if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)) ++
    (List.finRange (chainCount lay)).reverse.flatMap (fun i => zeros 48 ++ bytesLE 16 (ls.values i))
def layerStorage (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  layerBytes lay leaf ls
def witList (N : HashOutput) (w : Witness) : List UInt8 :=
  headerBytes w ++ leafBytes w.signature ++ streamBytes (selections N) w.signature.proof ++
    (List.finRange 4).flatMap fun lay =>
      layerStorage lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)
def witEnc (N : HashOutput) (w : Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))
def expandB (message : Message) (pk : Digest) (sig : Signature) : M (Option WBytes) :=
  (Option.map fun x => witEnc x.1 x.2) <$> expandN message pk sig
def witDecP (N : HashOutput) (w : WBytes) : Witness where
  signature :=
    { rho := wrho w
      secrets := fun s => wsecret w s.val
      proof := fun k => match slotOffset (selections N) k with
        | some off => wdig w off
        | none => 0
      layers := fun lay =>
        ⟨fun i => wvalue w lay i.val, fun j => wpath w lay (route (N.toNat % 2 ^ 31) lay).1 j.val⟩ }
  digestCounter := wdc w
  counters := fun lay => wctr w lay
def padDecP (N : HashOutput) (w : WBytes) : Pads where
  leaf s := wleafPad w s.val
  fold k := match slotBlock (selections N) k with
    | some blk => wdig w (blk + 32)
    | none => 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := wmerklePad w lay j.val
  chainHeader lay i := wchainHeaderPad w lay i.val
def Shaped (N : HashOutput) (w : WBytes) : Prop :=
  selectionsOk (selections N) = true ∧ admissible (selections N) = true ∧ StreamMatches (selections N) w
instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Shaped ====
section

section
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def FoldOk (w : WBytes) (val pad : Nat × Nat → Digest) (g k ptr r : Nat) : Prop :=
  val (k, g / 2 ^ k ^^^ 1) = wdig w (foldBlock ptr r + sibOff (g / 2 ^ k % 2)) ∧
    pad (k, g / 2 ^ k ^^^ 1) = wdig w (foldBlock ptr r + 32)
theorem folds_climb (w : WBytes) (index coord ptr : Nat) (val pad : Nat × Nat → Digest) (g : Nat) :
    ∀ (a r0 k : Nat) (v : Digest), k + a ≤ 11 → (∀ r < a, FoldOk w val pad g (k + r) ptr (r0 + r)) →
      (List.range' r0 a).foldlM (foldStep w index coord ptr) (v, (2048 + g) / 2 ^ k) =
        (fun v' => (v', (2048 + g) / 2 ^ (k + a))) <$> climbV index coord val pad g k a v := by
  intro a
  induction a with
  | zero => intro r0 k v _ _; simp
  | succ a ih =>
      intro r0 k v hk hok
      have h0 := hok 0 (by omega)
      simp only [Nat.add_zero] at h0
      obtain ⟨hv, hp⟩ := h0
      rw [List.range'_succ, List.foldlM_cons, climbV_succ, map_bind]
      have hmod := heap_mod_two (g := g) (show k < 11 by omega)
      have hpar := heap_parent (g := g) (show k < 11 by omega)
      have hdiv := heap_div_two g k
      have hrest := fun x => ih (r0 + 1) (k + 1) x (by omega) (fun r hr => by
        have := hok (r + 1) (by omega); simpa only [Nat.add_assoc, Nat.add_comm 1 r] using this)
      have hstep : foldStep w index coord ptr (v, (2048 + g) / 2 ^ k) r0 =
          (fun p => (p, (2048 + g) / 2 ^ (k + 1))) <$> climbStep index coord val pad g k v := by
        unfold foldStep climbStep
        rcases Nat.mod_two_eq_zero_or_one (g / 2 ^ k) with hg | hg
        · simp only [sibOff, hg, show (0 : Nat) ≠ 1 by decide, if_false] at hv
          simp only [hmod, hg, show (0 : Nat) ≠ 1 by decide, if_false, hpar, hv, hp, map_eq_bind_pure_comp,
            Function.comp_def, ← hdiv]
        · simp only [sibOff, hg, if_true, Nat.add_zero] at hv
          simp only [hmod, hg, if_true, hpar, hv, hp, map_eq_bind_pure_comp, Function.comp_def, ← hdiv]
      rw [hstep, bind_map_left]
      congr 1; funext x
      rw [hrest x, show k + 1 + a = k + (a + 1) by omega]
theorem foldsP_climb (w : WBytes) (index coord ptr : Nat) (val pad : Nat × Nat → Digest) (g a k : Nat)
    (v : Digest) (hk : k + a ≤ 11) (hok : ∀ r < a, FoldOk w val pad g (k + r) ptr r) :
    foldsP w index coord ptr a v ((2048 + g) / 2 ^ k) =
      (fun v' => (v', (2048 + g) / 2 ^ (k + a))) <$> climbV index coord val pad g k a v := by
  unfold foldsP
  rw [List.range_eq_range']
  exact folds_climb w index coord ptr val pad g a 0 k v hk (fun r hr => by simpa using hok r hr)
structure HdrOk (b A merge E : Nat) : Prop where
  a : b % 16 = A
  le : A ≤ 11
  m : b / 16 % 2 = merge
  t : 0 < A → b / 32 % 2 = E % 2
theorem segLoop_stop (w : WBytes) (index coord : Nat) (stack : List (Digest × Nat)) (pending : Pending)
    (E ptr A : Nat) (node : Digest) (h : HdrOk (wbyte w ptr).toNat A 0 E) :
    segLoop w index coord stack pending E ptr node = (do
      let n ← pendingHash w index coord node pending
      let r ← foldsP w index coord ptr A n E
      pure (some (r.1, r.2, segNext ptr A, stack))) := by
  rw [segLoop.eq_1]
  have h1 : ¬ 11 < A := Nat.not_lt.mpr h.le
  have h2 : ¬ (0 < A ∧ (wbyte w ptr).toNat / 32 % 2 ≠ E % 2) := by
    rintro ⟨hp, hne⟩; exact hne (h.t hp)
  simp only [h.a, h.m]
  rw [if_neg h1, if_neg h2]
  congr 1; funext n; congr 1; funext r
  rcases stack with _ | ⟨⟨pn, Q⟩, rest⟩ <;> simp
theorem segLoop_merge (w : WBytes) (index coord : Nat) (pnode : Digest) (Q : Nat) (rest : List (Digest × Nat))
    (pending : Pending) (E ptr A : Nat) (node : Digest) (h : HdrOk (wbyte w ptr).toNat A 1 E) :
    segLoop w index coord ((pnode, Q) :: rest) pending E ptr node = (do
      let n ← pendingHash w index coord node pending
      let r ← foldsP w index coord ptr A n E
      if Q ≠ r.2 then pure none
      else segLoop w index coord rest (.merge (r.2 / 2) pnode) (r.2 / 2) (segNext ptr A) r.1) := by
  rw [segLoop.eq_1]
  have h1 : ¬ 11 < A := Nat.not_lt.mpr h.le
  have h2 : ¬ (0 < A ∧ (wbyte w ptr).toNat / 32 % 2 ≠ E % 2) := by
    rintro ⟨hp, hne⟩; exact hne (h.t hp)
  simp only [h.a, h.m]
  rw [if_neg h1, if_neg h2]
  simp
section seg
variable (w : WBytes) (index coord : Nat) (val pad : Nat × Nat → Digest)
theorem seg_stop (stack : List (Digest × Nat)) (pending : Pending) (g k ptr A : Nat) (node : Digest)
    (hdr : HdrOk (wbyte w ptr).toNat A 0 ((2048 + g) / 2 ^ k)) (hk : k + A ≤ 11)
    (hf : ∀ r < A, FoldOk w val pad g (k + r) ptr r) :
    segLoop w index coord stack pending ((2048 + g) / 2 ^ k) ptr node =
      (fun v => some (v, (2048 + g) / 2 ^ (k + A), segNext ptr A, stack)) <$>
        (pendingHash w index coord node pending >>= climbV index coord val pad g k A) := by
  rw [segLoop_stop w index coord stack pending _ ptr A node hdr]
  simp only [map_bind]
  congr 1; funext n
  rw [foldsP_climb w index coord ptr val pad g A k n hk hf]
  simp [map_eq_bind_pure_comp]
theorem seg_merge (pnode : Digest) (Q : Nat) (rest : List (Digest × Nat)) (pending : Pending) (g k ptr A : Nat)
    (node : Digest) (hdr : HdrOk (wbyte w ptr).toNat A 1 ((2048 + g) / 2 ^ k)) (hk : k + A ≤ 11)
    (hf : ∀ r < A, FoldOk w val pad g (k + r) ptr r) (hQ : Q = (2048 + g) / 2 ^ (k + A)) :
    segLoop w index coord ((pnode, Q) :: rest) pending ((2048 + g) / 2 ^ k) ptr node =
      (pendingHash w index coord node pending >>= climbV index coord val pad g k A) >>= fun v =>
        segLoop w index coord rest (.merge ((2048 + g) / 2 ^ (k + A + 1)) pnode) ((2048 + g) / 2 ^ (k + A + 1))
          (segNext ptr A) v := by
  rw [segLoop_merge w index coord pnode Q rest pending _ ptr A node hdr, bind_assoc]
  congr 1; funext n
  rw [foldsP_climb w index coord ptr val pad g A k n hk hf]
  simp [hQ, heap_div_two]
end seg
theorem hdrOk_of_matches {seg : Segment} {b : Nat} (h : seg.Matches b) (hle : seg.a ≤ 11) :
    HdrOk b seg.a (if seg.merge then 1 else 0) ((2048 + seg.g) / 2 ^ seg.lo) where
  a := h.1
  le := hle
  m := by
    have := h.2.1
    cases hm : seg.merge <;> simp [hm] at this ⊢ <;> omega
  t := fun hp => by have := h.2.2 hp; simpa [Segment.t, Segment.heap] using this
def SegOk (w : WBytes) (val pad : Nat × Nat → Digest) (seg : Segment) (ptr : Nat) : Prop :=
  seg.Matches (wbyte w ptr).toNat ∧ ∀ r < seg.a, FoldOk w val pad seg.g (seg.lo + r) ptr r
def SegsOk (w : WBytes) (val pad : Nat × Nat → Digest) : Nat → List Segment → Prop
  | _, [] => True
  | ptr, s :: rest => SegOk w val pad s ptr ∧ SegsOk w val pad (segNext ptr s.a) rest
def segsEnd : Nat → List Segment → Nat
  | ptr, [] => ptr
  | ptr, s :: rest => segsEnd (segNext ptr s.a) rest
def leafAt (w : WBytes) (index coord : Nat) (gs : List Nat) (g : Nat) : M Digest :=
  pendingHash w index coord 0 (.leaf (3 * coord + gs.idxOf g) g)
theorem coordCanon_congr_leaf {index coord : Nat} {leafH leafH' : Nat → M Digest} {val pad : Nat × Nat → Digest}
    {g0 g1 g2 : Nat} (h0 : leafH g0 = leafH' g0) (h1 : leafH g1 = leafH' g1) (h2 : leafH g2 = leafH' g2) :
    coordCanon index coord leafH val pad g0 g1 g2 = coordCanon index coord leafH' val pad g0 g1 g2 := by
  unfold coordCanon; rw [h0, h1, h2]
theorem ftsCoordP_canon (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat)
    (val pad : Nat × Nat → Digest) (hb : sel.bucket < 16) (h2 : sel.leaves.getD 2 0 < 128)
    (h01 : sel.leaves.getD 0 0 < sel.leaves.getD 1 0) (h12 : sel.leaves.getD 1 0 < sel.leaves.getD 2 0)
    (hok : SegsOk w val pad ptr (coordSchedule coord sel)) :
    ftsCoordP w index coord sel ptr =
      (fun v => some (v, segsEnd ptr (coordSchedule coord sel))) <$>
        coordCanon index coord (leafAt w index coord [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2]) val pad
          (selLeaf sel 0) (selLeaf sel 1) (selLeaf sel 2) := by
  unfold ftsCoordP
  unfold coordSchedule at hok ⊢
  unfold coordCanon
  simp only [] at hok ⊢
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; omega
  have g2l : selLeaf sel 2 < 2048 := by unfold selLeaf; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := bucket_div_eight (by omega)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := bucket_div_eight (by omega)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := bucket_div_eight (by omega)
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1, bk2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer g01 g12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne g01 g12
  have i0 : [g0, g1, g2].idxOf g0 = 0 := by simp
  have i1 : [g0, g1, g2].idxOf g1 = 1 := by simp [List.idxOf_cons_ne _ (show g0 ≠ g1 by omega)]
  have i2 : [g0, g1, g2].idxOf g2 = 2 := by
    simp [List.idxOf_cons_ne _ (show g0 ≠ g2 by omega), List.idxOf_cons_ne _ (show g1 ≠ g2 by omega)]
  have lf : ∀ j g (nd : Digest), j < 3 → [g0, g1, g2].idxOf g = j →
      pendingHash w index coord nd (.leaf (3 * coord + j) g) = leafAt w index coord [g0, g1, g2] g := by
    intro j g nd _ hj; unfold leafAt; rw [hj]; rfl
  have lf0 : ∀ (nd : Digest), pendingHash w index coord nd (.leaf (3 * coord) g0) =
      leafAt w index coord [g0, g1, g2] g0 := by
    intro nd; have := lf 0 g0 nd (by omega) i0; simpa using this
  have e0 : ∀ g, 2048 + g = (2048 + g) / 2 ^ 0 := by intro g; simp
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · simp only [if_pos hA] at hok ⊢
    simp only [SegsOk, SegOk, segsEnd, Nat.zero_add] at hok ⊢
    obtain ⟨⟨m0, f0⟩, ⟨m1, f1⟩, ⟨m2, f2⟩, ⟨m3, f3⟩, ⟨m4, f4⟩, -⟩ := hok
    have H0 := hdrOk_of_matches m0 (by dsimp only; omega)
    have H1 := hdrOk_of_matches m1 (by dsimp only; omega)
    have H2 := hdrOk_of_matches m2 (by dsimp only; omega)
    have H3 := hdrOk_of_matches m3 (by dsimp only; omega)
    have H4 := hdrOk_of_matches m4 (by dsimp only; omega)
    simp only [Bool.false_eq_true, if_false, if_true] at H0 H1 H2 H3 H4
    rw [e0 g0, seg_stop w index coord val pad [] _ g0 0 _ (d01 - 1) 0 H0 (by omega) (by simpa using f0)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf0]
    congr 1; funext v0; congr 1; funext v0'
    have hq1 : (2048 + g0) / 2 ^ (d01 - 1) ^^^ 1 = (2048 + g1) / 2 ^ (0 + (d01 - 1)) := by
      rw [Nat.zero_add]; exact heap_sib (by omega) (by omega) (by omega)
    rw [e0 g1, seg_merge w index coord val pad v0' _ [] _ g1 0 _ (d01 - 1) v0' H1 (by omega)
      (by simpa using f1) hq1]
    simp only [Nat.zero_add, show d01 - 1 + 1 = d01 by omega, bind_assoc]
    rw [lf 1 g1 v0' (by omega) i1]
    congr 1; funext v1; congr 1; funext v1'
    rw [seg_stop w index coord val pad [] _ g1 d01 _ (d12 - 1 - d01) _ (by simpa using H2) (by omega)
      (by simpa using f2)]
    simp only [map_bind, bind_map_left, bind_assoc, pendingHash, heap_eq (show d01 ≤ 11 by omega)]
    congr 1; funext mm; congr 1; funext mm'
    have hq3 : (2048 + g1) / 2 ^ (d01 + (d12 - 1 - d01)) ^^^ 1 = (2048 + g2) / 2 ^ (0 + (d12 - 1)) := by
      rw [show d01 + (d12 - 1 - d01) = d12 - 1 by omega, Nat.zero_add]
      exact heap_sib (by omega) (by omega) (by omega)
    rw [e0 g2, seg_merge w index coord val pad mm' _ [] _ g2 0 _ (d12 - 1) mm' H3 (by omega)
      (by simpa using f3) hq3]
    simp only [Nat.zero_add, show d12 - 1 + 1 = d12 by omega, bind_assoc]
    rw [lf 2 g2 mm' (by omega) i2]
    congr 1; funext v2; congr 1; funext v2'
    rw [seg_stop w index coord val pad [] _ g2 d12 _ (11 - d12) _ (by simpa using H4) (by omega)
      (by simpa using f4)]
    simp only [map_bind, bind_map_left, bind_assoc, pendingHash, heap_eq (show d12 ≤ 11 by omega)]
    congr 1; funext r
    have hroot : (2048 + g2) / 2 ^ (d12 + (11 - d12)) = 1 := by
      rw [show d12 + (11 - d12) = 11 by omega]; omega
    simp only [hroot, and_self, if_true, map_eq_bind_pure_comp, Function.comp_def]
  · simp only [if_neg hA] at hok ⊢
    have hB : d12 < d01 := by omega
    simp only [SegsOk, SegOk, segsEnd, Nat.zero_add] at hok ⊢
    obtain ⟨⟨m0, f0⟩, ⟨m1, f1⟩, ⟨m2, f2⟩, ⟨m3, f3⟩, ⟨m4, f4⟩, -⟩ := hok
    have H0 := hdrOk_of_matches m0 (by dsimp only; omega)
    have H1 := hdrOk_of_matches m1 (by dsimp only; omega)
    have H2 := hdrOk_of_matches m2 (by dsimp only; omega)
    have H3 := hdrOk_of_matches m3 (by dsimp only; omega)
    have H4 := hdrOk_of_matches m4 (by dsimp only; omega)
    simp only [Bool.false_eq_true, if_false, if_true] at H0 H1 H2 H3 H4
    rw [e0 g0, seg_stop w index coord val pad [] _ g0 0 _ (d01 - 1) 0 H0 (by omega) (by simpa using f0)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf0]
    congr 1; funext v0; congr 1; funext v0'
    rw [e0 g1, seg_stop w index coord val pad _ _ g1 0 _ (d12 - 1) v0' H1 (by omega) (by simpa using f1)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf 1 g1 v0' (by omega) i1]
    congr 1; funext v1; congr 1; funext v1'
    have hq2 : (2048 + g1) / 2 ^ (d12 - 1) ^^^ 1 = (2048 + g2) / 2 ^ (0 + (d12 - 1)) := by
      rw [Nat.zero_add]; exact heap_sib (by omega) (by omega) (by omega)
    rw [e0 g2, seg_merge w index coord val pad v1' _ _ _ g2 0 _ (d12 - 1) v1' H2 (by omega)
      (by simpa using f2) hq2]
    simp only [Nat.zero_add, show d12 - 1 + 1 = d12 by omega, bind_assoc]
    rw [lf 2 g2 v1' (by omega) i2]
    congr 1; funext v2; congr 1; funext v2'
    have hq3 : (2048 + g0) / 2 ^ (d01 - 1) ^^^ 1 = (2048 + g2) / 2 ^ (d12 + (d01 - 1 - d12)) := by
      rw [show d12 + (d01 - 1 - d12) = d01 - 1 by omega]
      exact heap_sib (by omega) (by omega) (by rw [l02]; omega)
    rw [seg_merge w index coord val pad v0' _ [] _ g2 d12 _ (d01 - 1 - d12) _ (by simpa using H3) (by omega)
      (by simpa using f3) hq3]
    simp only [show d12 + (d01 - 1 - d12) + 1 = d01 by omega, bind_assoc, pendingHash,
      heap_eq (show d12 ≤ 11 by omega)]
    congr 1; funext mm; congr 1; funext mm'
    rw [seg_stop w index coord val pad [] _ g2 d01 _ (11 - d01) _ (by simpa using H4) (by omega)
      (by simpa using f4)]
    simp only [map_bind, bind_map_left, bind_assoc, pendingHash, heap_eq (show d01 ≤ 11 by omega)]
    congr 1; funext nn
    have hroot : (2048 + g2) / 2 ^ (d01 + (11 - d01)) = 1 := by
      rw [show d01 + (11 - d01) = 11 by omega]; omega
    simp only [hroot, and_self, if_true, map_eq_bind_pure_comp, Function.comp_def]
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem hasLeaf_up {leaves : List Nat} {j n : Nat} (h : hasLeaf leaves j n = true) (d : Nat) :
    hasLeaf leaves (j + d) (n / 2 ^ d) = true := by
  obtain ⟨leaf, hm, he⟩ := (hasLeaf_iff _ _ _).mp h
  exact (hasLeaf_iff _ _ _).mpr ⟨leaf, hm, by rw [pow_add, ← Nat.div_div_eq_div_mul, he]⟩
theorem frontier_inside {leaves : List Nat} : ∀ L N p, p ∈ T3.frontier leaves L N →
    p.1 ≤ L ∧ p.2 / 2 ^ (L - p.1) = N := by
  intro L
  induction L with
  | zero =>
      intro N p hp
      simp only [T3.frontier] at hp
      split at hp
      · simp at hp
      · simp only [List.mem_singleton] at hp; subst hp; simp
  | succ L ih =>
      intro N p hp
      simp only [T3.frontier] at hp
      split at hp
      · rcases List.mem_append.mp hp with h | h
        · obtain ⟨h1, h2⟩ := ih _ _ h
          refine ⟨by omega, ?_⟩
          rw [show L + 1 - p.1 = (L - p.1) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, h2]; omega
        · obtain ⟨h1, h2⟩ := ih _ _ h
          refine ⟨by omega, ?_⟩
          rw [show L + 1 - p.1 = (L - p.1) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, h2]; omega
      · simp only [List.mem_singleton] at hp; subst hp; simp
theorem frontier_nodup {leaves : List Nat} : ∀ L N, (T3.frontier leaves L N).Nodup := by
  intro L
  induction L with
  | zero => intro N; simp only [T3.frontier]; split <;> simp
  | succ L ih =>
      intro N
      simp only [T3.frontier]
      split
      · refine List.nodup_append.mpr ⟨ih _, ih _, ?_⟩
        intro a ha b hb hab
        subst hab
        have h1 := (frontier_inside _ _ _ ha).2
        have h2 := (frontier_inside _ _ _ hb).2
        omega
      · simp
theorem frontier_mem {leaves : List Nat} : ∀ L N k s, k ≤ L → s / 2 ^ (L - k) = N →
    hasLeaf leaves k s = false → (k = L ∨ hasLeaf leaves (k + 1) (s / 2) = true) →
    (k, s) ∈ T3.frontier leaves L N := by
  intro L
  induction L with
  | zero =>
      intro N k s hk hN he _
      obtain rfl : k = 0 := by omega
      simp only [Nat.sub_zero, pow_zero, Nat.div_one] at hN; subst hN
      simp [T3.frontier, he]
  | succ L ih =>
      intro N k s hk hN he hp
      by_cases hkL : k = L + 1
      · subst hkL
        simp only [Nat.sub_self, pow_zero, Nat.div_one] at hN; subst hN
        simp [T3.frontier, he]
      · have hp' : hasLeaf leaves (k + 1) (s / 2) = true := by rcases hp with h | h; omega; exact h
        have hup := hasLeaf_up hp' (L - k)
        have hsN : s / 2 / 2 ^ (L - k) = N := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ', show L - k + 1 = L + 1 - k by omega, hN]
        rw [show k + 1 + (L - k) = L + 1 by omega, hsN] at hup
        simp only [T3.frontier, hup, ite_true]
        have hdiv : s / 2 ^ (L - k) / 2 = N := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ, show L - k + 1 = L + 1 - k by omega, hN]
        rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ (L - k)) with h2 | h2
        · exact List.mem_append_left _ (ih (2 * N) k s (by omega) (by omega) he (Or.inr hp'))
        · exact List.mem_append_right _ (ih (2 * N + 1) k s (by omega) (by omega) he (Or.inr hp'))
theorem slotPositions_nodup (sel : Selection) : (slotPositions sel).Nodup := by
  unfold slotPositions
  refine List.nodup_append.mpr ⟨frontier_nodup _ _, ?_, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.singleton_append, List.cons_append]
    simp
  · intro a ha b hb hab
    subst hab
    have h1 := frontier_inside _ _ _ ha
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp only at h1
    rcases j with _ | j
    · simp only [Nat.add_zero, Nat.sub_self, pow_zero, Nat.div_one] at h1
      exact xor_one_ne _ h1.2
    · omega
theorem sib_eq_imp {g g' k k' : Nat} (h : (k, g / 2 ^ k ^^^ 1) = (k', g' / 2 ^ k' ^^^ 1)) :
    k = k' ∧ (g = g' ∨ (g ≠ g' ∧ lcaLevel g g' ≤ k)) := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  refine ⟨rfl, ?_⟩
  by_cases hg : g = g'
  · exact Or.inl hg
  · refine Or.inr ⟨hg, (div_eq_iff_lca hg k).mp ?_⟩
    have := congrArg (· ^^^ 1) h
    simpa only [xor_one_xor_one] using this
structure SelOk (sel : Selection) : Prop where
  len : sel.leaves.length = 3
  b : sel.bucket < 16
  l2 : sel.leaves.getD 2 0 < 128
  s01 : sel.leaves.getD 0 0 < sel.leaves.getD 1 0
  s12 : sel.leaves.getD 1 0 < sel.leaves.getD 2 0
theorem SelOk.leaves_eq {sel : Selection} (h : SelOk sel) :
    sel.leaves = [sel.leaves.getD 0 0, sel.leaves.getD 1 0, sel.leaves.getD 2 0] := by
  have := h.len
  match hl : sel.leaves, this with
  | [a, b, c], _ => simp
theorem SelOk.selected {sel : Selection} (h : SelOk sel) :
    selectedLeaves sel = [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] := by
  unfold selectedLeaves selLeaf; rw [h.leaves_eq]; simp
structure FoldFacts (leaves : List Nat) (segs : List Segment) : Prop where
  empty : ∀ i < 5, ∀ r < (segs.getD i default).a,
    hasLeaf leaves ((segs.getD i default).lo + r)
      ((segs.getD i default).g / 2 ^ ((segs.getD i default).lo + r) ^^^ 1) = false
  top : ∀ i < 5, (segs.getD i default).lo + (segs.getD i default).a ≤ 11
  leaf : ∀ i < 5, (segs.getD i default).g ∈ leaves
  inj : ∀ i < 5, ∀ i' < 5, ∀ r < (segs.getD i default).a, ∀ r' < (segs.getD i' default).a,
    (segs.getD i default).sib r = (segs.getD i' default).sib r' → i = i' ∧ r = r'
  len : segs.length = 5
theorem foldFacts (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    FoldFacts (selectedLeaves sel) (coordSchedule coord sel) := by
  have hsel := hs.selected
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s01; have := hs.s12; have := hs.l2; omega)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s12; have := hs.l2; omega)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := bucket_div_eight hs.l2
  unfold coordSchedule
  rw [hsel]
  simp only []
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1, bk2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer g01 g12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne g01 g12
  have c10 : lcaLevel g1 g0 = lcaLevel g0 g1 := lcaLevel_comm _ _
  have c21 : lcaLevel g2 g1 = lcaLevel g1 g2 := lcaLevel_comm _ _
  have c20 : lcaLevel g2 g0 = lcaLevel g0 g2 := lcaLevel_comm _ _
  have sib : ∀ g k, (∀ g' ∈ [g0, g1, g2], g' ≠ g → lcaLevel g g' ≠ k + 1) →
      hasLeaf [g0, g1, g2] k (g / 2 ^ k ^^^ 1) = false := fun g k h => hasLeaf_sib_false h
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · simp only [if_pos hA]
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · intro i hi r hr
      interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hr ⊢ <;>
        apply sib <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] <;>
        rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' |
          (simp only [c10, c21, c20, l02, hd01, hd12]; omega)
    · intro i hi; interval_cases i <;> simp <;> omega
    · intro i hi; interval_cases i <;> simp
    · intro i hi i' hi' r hr r' hr' h
      interval_cases i <;> interval_cases i' <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ, Segment.sib] at hr hr' h <;>
        obtain ⟨hk, hg | ⟨hg, hl⟩⟩ := sib_eq_imp h <;>
        first | omega | (simp only [c10, c21, c20, l02, hd01, hd12] at hl; omega)
  · simp only [if_neg hA]
    have hB : d12 < d01 := by omega
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · intro i hi r hr
      interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hr ⊢ <;>
        apply sib <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] <;>
        rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' |
          (simp only [c10, c21, c20, l02, hd01, hd12]; omega)
    · intro i hi; interval_cases i <;> simp <;> omega
    · intro i hi; interval_cases i <;> simp
    · intro i hi i' hi' r hr r' hr' h
      interval_cases i <;> interval_cases i' <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ, Segment.sib] at hr hr' h <;>
        obtain ⟨hk, hg | ⟨hg, hl⟩⟩ := sib_eq_imp h <;>
        first | omega | (simp only [c10, c21, c20, l02, hd01, hd12] at hl; omega)
theorem xor_one_div_pow (x m : Nat) (hm : 1 ≤ m) : (x ^^^ 1) / 2 ^ m = x / 2 ^ m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, xor_one_div_two]
theorem SelOk.bucket_div {sel : Selection} (hs : SelOk sel) {g : Nat} (hg : g ∈ selectedLeaves sel) :
    g / 2 ^ 7 = sel.bucket := by
  rw [hs.selected] at hg
  have := hs.s01; have := hs.s12; have := hs.l2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact bucket_div_eight (by omega)
theorem fold_sib_mem (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    ∀ i < 5, ∀ r < ((coordSchedule coord sel).getD i default).a,
      ((coordSchedule coord sel).getD i default).sib r ∈ slotPositions sel := by
  intro i hi r hr
  have F := foldFacts coord sel hs
  set seg := (coordSchedule coord sel).getD i default with hseg
  have hb := hs.bucket_div (F.leaf i hi)
  have htop := F.top i hi
  have hem := F.empty i hi r hr
  rw [← hseg] at hb htop hem
  unfold slotPositions Segment.sib
  by_cases hk : seg.lo + r < 7
  · apply List.mem_append_left
    apply frontier_mem 7 sel.bucket _ _ (by omega)
    · rw [xor_one_div_pow _ _ (by omega), Nat.div_div_eq_div_mul, ← pow_add,
        show seg.lo + r + (7 - (seg.lo + r)) = 7 by omega, hb]
    · exact hem
    · right
      rw [xor_one_div_two, Nat.div_div_eq_div_mul, ← pow_succ]
      exact hasLeaf_self (F.leaf i hi) _
  · apply List.mem_append_right
    simp only [List.mem_map, List.mem_range]
    refine ⟨seg.lo + r - 7, by omega, ?_⟩
    have e : seg.g / 2 ^ (seg.lo + r) = sel.bucket / 2 ^ (seg.lo + r - 7) := by
      rw [show seg.lo + r = 7 + (seg.lo + r - 7) by omega, pow_add, ← Nat.div_div_eq_div_mul, hb]
      simp
    rw [e, show 7 + (seg.lo + r - 7) = seg.lo + r by omega]
theorem SelOk.exists {sel : Selection} (h : SelOk sel) :
    ∃ x0 x1 x2, sel.leaves = [x0, x1, x2] ∧ x0 < x1 ∧ x1 < x2 ∧ x2 < 128 := by
  have hl := h.leaves_eq
  refine ⟨_, _, _, hl, h.s01, h.s12, h.l2⟩
theorem coord_fold_count (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    ((coordSchedule coord sel).map Segment.a).sum = (slotPositions sel).length := by
  obtain ⟨x0, x1, x2, hl, h01, h12, h2⟩ := hs.exists
  have hb : ∀ leaf ∈ sel.leaves, leaf < 128 := by
    rw [hl]; simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  have hn : sel.leaves.Nodup := by rw [hl]; simp; omega
  have hsorted : sel.leaves.SortedLE := by
    rw [hl, List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  have hf := Correctness.bucket_frontier_length sel.leaves sel.bucket hs.len hn hsorted hb
  unfold slotPositions selectedLeaves
  rw [List.length_append, hf]
  simp only [List.length_map, List.length_range]
  have ha : authCount sel.leaves = 3 + lcaLevel x0 x1 + lcaLevel x1 x2 := by
    rw [hl]; simp [authCount, lcaLevel]; omega
  rw [ha]
  have e01 := lca_bucket (b := sel.bucket) (show x0 < 128 by omega) (show x1 < 128 by omega) (by omega)
  have e12 := lca_bucket (b := sel.bucket) (show x1 < 128 by omega) h2 (by omega)
  have l01 := lca_le_eight (b := sel.bucket) (show x0 < 128 by omega) (show x1 < 128 by omega) (by omega)
  have l12 := lca_le_eight (b := sel.bucket) (show x1 < 128 by omega) h2 (by omega)
  have p01 := lcaLevel_pos (sel.bucket * 128 + x0) (sel.bucket * 128 + x1)
  have p12 := lcaLevel_pos (sel.bucket * 128 + x1) (sel.bucket * 128 + x2)
  have hne := lca_ne (show sel.bucket * 128 + x0 < sel.bucket * 128 + x1 by omega)
    (show sel.bucket * 128 + x1 < sel.bucket * 128 + x2 by omega)
  unfold coordSchedule selLeaf
  simp only [hl, List.getD_cons_zero, List.getD_cons_succ]
  rw [e01, e12] at *
  split <;> simp <;> omega
theorem getD_flatMap_five {α : Type} (f : Nat → List α) (hf : ∀ c, (f c).length = 5) (d : α) :
    ∀ m n, n < 5 * m → ((List.range m).flatMap f).getD n d = (f (n / 5)).getD (n % 5) d := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
      intro n hn
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hlen : ((List.range m).flatMap f).length = 5 * m := by
        rw [List.length_flatMap]; simp [hf, List.sum_replicate]; ring
      by_cases h : n < 5 * m
      · rw [List.getD_append _ _ _ _ (by omega), ih n h]
      · rw [List.getD_append_right _ _ _ _ (by omega), hlen]
        rw [show n / 5 = m by omega, show n % 5 = n - 5 * m by omega]
theorem coordSchedule_length (coord : Nat) (sel : Selection) : (coordSchedule coord sel).length = 5 := by
  unfold coordSchedule; dsimp only; split <;> rfl
theorem schedule_length (chosen : List Selection) : (schedule chosen).length = 35 := by
  unfold schedule; rw [List.length_flatMap]; simp [coordSchedule_length]
theorem schedule_getD (chosen : List Selection) {n : Nat} (hn : n < 35) :
    (schedule chosen).getD n default = (coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default :=
  getD_flatMap_five _ (fun c => coordSchedule_length _ _) default 7 n (by omega)
theorem coordSchedule_coord (coord : Nat) (sel : Selection) {i : Nat} (hi : i < 5) :
    ((coordSchedule coord sel).getD i default).coord = coord := by
  unfold coordSchedule; dsimp only; split <;> interval_cases i <;> rfl
theorem schedule_coord (chosen : List Selection) {n : Nat} (hn : n < 35) :
    ((schedule chosen).getD n default).coord = n / 5 := by
  rw [schedule_getD chosen hn, coordSchedule_coord _ _ (by omega)]
theorem slotBase_succ (chosen : List Selection) (c : Nat) :
    slotBase chosen (c + 1) = slotBase chosen c + (slotPositions (chosen.getD c ⟨0, []⟩)).length := by
  unfold slotBase; rw [List.range_succ, List.map_append, List.sum_append]; simp
theorem slotBase_mono (chosen : List Selection) {c c' : Nat} (h : c ≤ c') : slotBase chosen c ≤ slotBase chosen c' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [slotBase_succ]; omega
theorem slotBase_inj (chosen : List Selection) {c c' x x' : Nat}
    (hx : x < (slotPositions (chosen.getD c ⟨0, []⟩)).length)
    (hx' : x' < (slotPositions (chosen.getD c' ⟨0, []⟩)).length)
    (h : slotBase chosen c + x = slotBase chosen c' + x') : c = c' ∧ x = x' := by
  rcases Nat.lt_trichotomy c c' with hc | rfl | hc
  · have := slotBase_mono chosen (show c + 1 ≤ c' by omega)
    rw [slotBase_succ] at this; omega
  · exact ⟨rfl, by omega⟩
  · have := slotBase_mono chosen (show c' + 1 ≤ c by omega)
    rw [slotBase_succ] at this; omega
def ChosenOk (chosen : List Selection) : Prop := ∀ c < 7, SelOk (chosen.getD c ⟨0, []⟩)
theorem mem_foldPositions {segs : List Segment} {p : Nat × Nat} :
    p ∈ foldPositions segs ↔ p.1 < segs.length ∧ p.2 < (segs.getD p.1 default).a := by
  obtain ⟨n, r⟩ := p
  simp only [foldPositions, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨n', hn', r', hr', rfl, rfl⟩; exact ⟨hn', hr'⟩
  · rintro ⟨hn, hr⟩; exact ⟨n, hn, r, hr, rfl, rfl⟩
theorem foldSlot_split (chosen : List Selection) (hc : ChosenOk chosen) {n r : Nat} (hn : n < 35)
    (hr : r < ((schedule chosen).getD n default).a) :
    foldSlot chosen ((schedule chosen).getD n default) r =
      slotBase chosen (n / 5) + (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).idxOf
        (((coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default).sib r) ∧
    (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).idxOf
        (((coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default).sib r) <
      (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).length := by
  rw [schedule_getD chosen hn] at hr ⊢
  refine ⟨?_, List.idxOf_lt_length_of_mem (fold_sib_mem _ _ (hc _ (by omega)) _ (by omega) _ hr)⟩
  unfold foldSlot
  rw [coordSchedule_coord _ _ (by omega)]
theorem foldSlot_inj (chosen : List Selection) (hc : ChosenOk chosen) {n n' r r' : Nat} (hn : n < 35)
    (hn' : n' < 35) (hr : r < ((schedule chosen).getD n default).a) (hr' : r' < ((schedule chosen).getD n' default).a)
    (h : foldSlot chosen ((schedule chosen).getD n default) r = foldSlot chosen ((schedule chosen).getD n' default) r') :
    n = n' ∧ r = r' := by
  obtain ⟨e1, l1⟩ := foldSlot_split chosen hc hn hr
  obtain ⟨e2, l2⟩ := foldSlot_split chosen hc hn' hr'
  rw [e1, e2] at h
  obtain ⟨hcc, hx⟩ := slotBase_inj chosen l1 l2 h
  rw [schedule_getD chosen hn] at hr
  rw [schedule_getD chosen hn'] at hr'
  rw [← hcc] at hx hr'
  have hm := fold_sib_mem _ _ (hc _ (by omega)) _ (by omega) _ hr
  have hsib := (List.idxOf_inj hm).mp hx
  obtain ⟨hi, hrr⟩ := (foldFacts _ _ (hc _ (by omega))).inj _ (by omega) _ (by omega) _ hr _ hr' hsib
  exact ⟨by omega, hrr⟩
theorem find?_unique {α : Type} (l : List α) (p : α → Bool) (x : α) (hx : x ∈ l) (hp : p x = true)
    (hu : ∀ y ∈ l, p y = true → y = x) : l.find? p = some x := by
  cases h : l.find? p with
  | none => exact absurd hp (by simpa using List.find?_eq_none.mp h x hx)
  | some y => exact congrArg some (hu y (List.mem_of_find?_eq_some h) (List.find?_some h))
theorem streamPlan_foldSlot (chosen : List Selection) (hc : ChosenOk chosen) {n r : Nat} (hn : n < 35)
    (hr : r < ((schedule chosen).getD n default).a)
    (hk : foldSlot chosen ((schedule chosen).getD n default) r < 115) :
    streamPlan chosen ⟨_, hk⟩ = some (n, r) := by
  unfold streamPlan
  apply find?_unique
  · exact mem_foldPositions.mpr ⟨by rw [schedule_length]; exact hn, hr⟩
  · simp
  · rintro ⟨n', r'⟩ hy hp
    have := mem_foldPositions.mp hy
    rw [schedule_length] at this
    simp only [decide_eq_true_eq] at hp
    obtain ⟨h1, h2⟩ := foldSlot_inj chosen hc this.1 hn this.2 hr hp
    exact Prod.ext h1 h2
end SigGolfCandidate.T3M
end
section
set_option maxRecDepth 10000
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def valOf (proof : Fin 115 → Digest) (base : Nat) (ps : List (Nat × Nat)) (p : Nat × Nat) : Digest :=
  proof ⟨(base + ps.idxOf p) % 115, Nat.mod_lt _ (by decide)⟩
theorem slotsMatch_valOf (proof : Fin 115 → Digest) (pads : Pads) (base : Nat) (ps : List (Nat × Nat))
    (hnd : ps.Nodup) : SlotsMatch proof pads (valOf proof base ps) (valOf pads.fold base ps) base ps := by
  intro i hi h
  refine ⟨?_, ?_⟩ <;> simp only [valOf, List.Nodup.idxOf_getElem hnd, Nat.mod_eq_of_lt h]
def outerStepP (sig : Signature) (pads : Pads) (index coord bucket : Nat) (state : Option (Digest × Nat)) (j : Nat) :
    M (Option (Digest × Nat)) := do
  let some (value, used) := state | pure none
  if h : used < 115 then
    let other := sig.proof ⟨used, h⟩
    let pair := if bucket / 2 ^ j % 2 = 0 then (value, other) else (other, value)
    let parent ← nodeHashP 10 coord index (2 ^ (4 - j - 1) + bucket / 2 ^ (j + 1)) pair.1
      (pads.fold ⟨used, h⟩) pair.2
    pure (some (parent, used + 1))
  else pure none
def ftsStepP (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (state : Option (List Digest × Nat)) (coord : Nat) : M (Option (List Digest × Nat)) := do
  let some (roots, used) := state | pure none
  let sel := chosen.getD coord ⟨0, []⟩
  let selected := sel.leaves.map (fun s => sel.bucket * 128 + s)
  let values := (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)
  let some (value, next) ← recoverChildP index coord selected values sig.proof pads 7 sel.bucket used
    | pure none
  let result ← (List.range 4).foldlM (outerStepP sig pads index coord sel.bucket) (some (value, next))
  let some (root, next) := result | pure none
  pure (some (roots ++ [root], next))
theorem recoverFtsP_eq (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection) :
    recoverFtsP sig pads index chosen = (do
      let state ← (List.range 7).foldlM (ftsStepP sig pads index chosen) (some ([], 0))
      let some (roots, used) := state | pure none
      if !(List.range (115 - used)).all (fun j =>
          decide (sig.proof ⟨(used + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
      pure (some (← forestPk index roots))) := rfl
theorem outer_climb (sig : Signature) (pads : Pads) (index coord bucket g : Nat) (hg : g / 2 ^ 7 = bucket)
    (val pad : Nat × Nat → Digest) : ∀ n j0 (v : Digest) (u : Nat), j0 + n ≤ 4 → u + n ≤ 115 →
      (∀ j < n, ∀ h : u + j < 115, sig.proof ⟨u + j, h⟩ = val (7 + j0 + j, g / 2 ^ (7 + j0 + j) ^^^ 1) ∧
        pads.fold ⟨u + j, h⟩ = pad (7 + j0 + j, g / 2 ^ (7 + j0 + j) ^^^ 1)) →
      (List.range' j0 n).foldlM (outerStepP sig pads index coord bucket) (some (v, u)) =
        (fun v' => some (v', u + n)) <$> climbV index coord val pad g (7 + j0) n v := by
  intro n
  induction n with
  | zero => intro j0 v u _ _ _; simp
  | succ n ih =>
      intro j0 v u hj hu hm
      have hb : g / 2 ^ (7 + j0) = bucket / 2 ^ j0 := by
        rw [pow_add, ← Nat.div_div_eq_div_mul, hg]
      obtain ⟨hv, hp⟩ := hm 0 (by omega) (by omega)
      simp only [Nat.add_zero] at hv hp
      rw [List.range'_succ, List.foldlM_cons, climbV_succ, map_bind]
      have hstep : outerStepP sig pads index coord bucket (some (v, u)) j0 =
          (fun p => some (p, u + 1)) <$> climbStep index coord val pad g (7 + j0) v := by
        unfold outerStepP climbStep
        simp only [dif_pos (show u < 115 by omega), hb, hv, hp]
        have hh : 2 ^ (11 - (7 + j0 + 1)) + bucket / 2 ^ j0 / 2 = 2 ^ (4 - j0 - 1) + bucket / 2 ^ (j0 + 1) := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ, show 11 - (7 + j0 + 1) = 4 - j0 - 1 by omega]
        rw [hh]
        rcases Nat.mod_two_eq_zero_or_one (bucket / 2 ^ j0) with h0 | h0 <;>
          simp [h0, map_eq_bind_pure_comp]
      rw [hstep, bind_map_left]
      congr 1; funext x
      rw [ih (j0 + 1) x (u + 1) (by omega) (by omega) (fun j hj h => by
        have := hm (j + 1) (by omega) (by omega)
        simpa only [show u + (j + 1) = u + 1 + j by omega, show 7 + j0 + (j + 1) = 7 + (j0 + 1) + j by omega]
          using this)]
      simp only [show u + 1 + n = u + (n + 1) by omega, show 7 + j0 + 1 = 7 + (j0 + 1) by omega]
theorem ftsStepP_some (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (used coord : Nat) :
    ftsStepP sig pads index chosen (some (roots, used)) coord = (do
      let some (value, next) ← recoverChildP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
        ((List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩))
        sig.proof pads 7 (chosen.getD coord ⟨0, []⟩).bucket used | pure none
      let result ← (List.range 4).foldlM (outerStepP sig pads index coord (chosen.getD coord ⟨0, []⟩).bucket)
        (some (value, next))
      let some (root, next) := result | pure none
      pure (some (roots ++ [root], next))) := rfl
theorem ftsStepP_canon (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (used coord : Nat) (hs : SelOk (chosen.getD coord ⟨0, []⟩))
    (hfit : used + (slotPositions (chosen.getD coord ⟨0, []⟩)).length ≤ 115)
    (val pad : Nat × Nat → Digest)
    (hm : SlotsMatch sig.proof pads val pad used (slotPositions (chosen.getD coord ⟨0, []⟩))) :
    ftsStepP sig pads index chosen (some (roots, used)) coord =
      (fun v => some (roots ++ [v], used + (slotPositions (chosen.getD coord ⟨0, []⟩)).length)) <$>
        coordCanon index coord (leafHP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
            ((List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) pads)
          val pad (selLeaf (chosen.getD coord ⟨0, []⟩) 0) (selLeaf (chosen.getD coord ⟨0, []⟩) 1)
          (selLeaf (chosen.getD coord ⟨0, []⟩) 2) := by
  rw [ftsStepP_some]
  generalize chosen.getD coord ⟨0, []⟩ = sel at *
  generalize hvals : (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩) =
    values
  have hsp : slotPositions sel = T3.frontier (selectedLeaves sel) 7 sel.bucket ++
      (List.range 4).map (fun j => (7 + j, sel.bucket / 2 ^ j ^^^ 1)) := rfl
  rw [hsp] at hfit hm ⊢
  rw [List.length_append] at hfit ⊢
  simp only [List.length_map, List.length_range] at hfit ⊢
  have hF := recoverChildP_eq_dfsP index coord (selectedLeaves sel) values sig.proof pads val pad 7 sel.bucket used
    (by omega) hm.left
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have hb2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hs.selected]; simp)
  have hO := outer_climb sig pads index coord sel.bucket (selLeaf sel 2) hb2 val pad 4 0
  have hbk : ∀ j, selLeaf sel 2 / 2 ^ (7 + 0 + j) = sel.bucket / 2 ^ j := by
    intro j; rw [Nat.add_zero]; exact bucket_div_outer hs.l2
  have hD := dfsP_bucket (index := index) (coord := coord)
    (leafH := leafHP index coord (selectedLeaves sel) values pads)
    (val := val) (pad := pad) g01 g12 (hs.bucket_div (by rw [hs.selected]; simp))
    (hs.bucket_div (by rw [hs.selected]; simp)) hb2
  rw [← hs.selected] at hD
  rw [hF, bind_map_left, ← hD, map_bind]
  congr 1; funext v
  dsimp only
  rw [show List.range 4 = List.range' 0 4 from List.range_eq_range' ..]
  rw [hO v _ (by omega) (by omega) (fun j hj h => by
    have := hm.right j (by simp; omega) h
    simp only [List.getElem_map, List.getElem_range] at this
    rw [hbk j, Nat.add_zero]; exact this)]
  simp only [bind_map_left, map_eq_bind_pure_comp, Function.comp_def, List.length_map, List.length_range,
    Nat.add_assoc, Nat.zero_add, Nat.add_zero, bind_assoc, pure_bind]
theorem selectionsOk_sel {chosen : List Selection} (h : selectionsOk chosen = true) {sel : Selection}
    (hm : sel ∈ chosen) : ∃ x0 x1 x2, sel.leaves = [x0, x1, x2] ∧ x0 < x1 ∧ x1 < x2 := by
  unfold selectionsOk at h
  have := List.all_eq_true.mp h sel hm
  match hl : sel.leaves, this with
  | [x0, x1, x2], h' =>
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact ⟨x0, x1, x2, rfl, h'.1, h'.2⟩
theorem chosenOk_of (N : HashOutput) (h : selectionsOk (selections N) = true) : ChosenOk (selections N) := by
  intro c hc
  have hm := Correctness.selection_getD_mem N c hc
  obtain ⟨x0, x1, x2, hl, h01, h12⟩ := selectionsOk_sel h hm
  have hb := selection_bucket_bound N _ hm
  have h2 := selection_leaf_bound N _ x2 hm (by rw [hl]; simp)
  exact ⟨by rw [hl]; rfl, hb, by rw [hl]; simpa using h2, by rw [hl]; simpa using h01, by rw [hl]; simpa using h12⟩
theorem slotPositions_length {sel : Selection} (hs : SelOk sel) :
    (slotPositions sel).length = authCount sel.leaves + 4 := by
  obtain ⟨x0, x1, x2, hl, h01, h12, h2⟩ := hs.exists
  have hb : ∀ leaf ∈ sel.leaves, leaf < 128 := by
    rw [hl]; simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  have hn : sel.leaves.Nodup := by rw [hl]; simp; omega
  have hsorted : sel.leaves.SortedLE := by
    rw [hl, List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  unfold slotPositions selectedLeaves
  rw [List.length_append, Correctness.bucket_frontier_length sel.leaves sel.bucket hs.len hn hsorted hb]
  simp
theorem sum_range_getD {α : Type} (items : List α) (d : α) (f : α → Nat) :
    ((List.range items.length).map (fun i => f (items.getD i d))).sum = (items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
      simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, ih, List.map_cons, List.sum_cons]
theorem slotBase_seven_eq (N : HashOutput) (hc : ChosenOk (selections N)) :
    slotBase (selections N) 7 = 28 + ((selections N).map fun s => authCount s.leaves).sum := by
  have e : ((List.range 7).map fun c => (slotPositions ((selections N).getD c ⟨0, []⟩)).length) =
      (List.range 7).map fun c => authCount ((selections N).getD c ⟨0, []⟩).leaves + 4 :=
    List.map_congr_left (fun c hc' => slotPositions_length (hc c (List.mem_range.mp hc')))
  unfold slotBase
  rw [e, ← sum_range_getD (selections N) ⟨0, []⟩ (fun s => authCount s.leaves), selections_length,
    List.sum_map_add]
  simp
  omega
theorem slotBase_seven_le (N : HashOutput) (hc : ChosenOk (selections N))
    (hadm : admissible (selections N) = true) : slotBase (selections N) 7 ≤ 115 := by
  have h := hadm
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have e : ((List.range 7).map fun c => (slotPositions ((selections N).getD c ⟨0, []⟩)).length) =
      (List.range 7).map fun c => authCount ((selections N).getD c ⟨0, []⟩).leaves + 4 :=
    List.map_congr_left (fun c hc' => slotPositions_length (hc c (List.mem_range.mp hc')))
  have hsum : slotBase (selections N) 7 = 28 + ((selections N).map fun s => authCount s.leaves).sum := by
    unfold slotBase
    rw [e, ← sum_range_getD (selections N) ⟨0, []⟩ (fun s => authCount s.leaves), selections_length,
      List.sum_map_add]
    simp
    omega
  omega
theorem segPtr_succ (segs : List Segment) {m : Nat} (hm : m < segs.length) :
    segPtr segs (m + 1) = segNext (segPtr segs m) (segs.getD m default).a := by
  unfold segPtr segNext
  rw [List.take_add_one, List.getElem?_eq_getElem hm, List.map_append, List.sum_append]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.getD,
    List.getElem?_eq_getElem hm, Option.getD_some]
  omega
theorem segsOk_of_getD (w : WBytes) (val pad : Nat × Nat → Digest) : ∀ (segs : List Segment) (f : Nat → Nat),
    (∀ i < segs.length, f (i + 1) = segNext (f i) (segs.getD i default).a) →
    (∀ i < segs.length, SegOk w val pad (segs.getD i default) (f i)) →
    SegsOk w val pad (f 0) segs ∧ segsEnd (f 0) segs = f segs.length := by
  intro segs
  induction segs with
  | nil => intro f _ _; exact ⟨trivial, rfl⟩
  | cons s rest ih =>
      intro f hf hok
      have h0 := hf 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      obtain ⟨h1, h2⟩ := ih (fun i => f (i + 1)) (fun i hi => by
          have := hf (i + 1) (by simp; omega); simpa using this)
        (fun i hi => by have := hok (i + 1) (by simp; omega); simpa using this)
      simp only [h0] at h1 h2
      refine ⟨⟨by simpa using hok 0 (by simp), h1⟩, ?_⟩
      simp only [segsEnd, h2, List.length_cons]
theorem sum_flatMap_nat {β : Type} (l : List β) (f : β → List Nat) :
    (l.flatMap f).sum = (l.map fun b => (f b).sum).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]
theorem schedule_folds (chosen : List Selection) (hc : ChosenOk chosen) :
    ((schedule chosen).map Segment.a).sum = slotBase chosen 7 := by
  unfold schedule slotBase
  rw [List.map_flatMap, sum_flatMap_nat]
  congr 1
  apply List.map_congr_left
  intro c hc'
  rw [List.mem_range] at hc'
  exact coord_fold_count c _ (hc c hc')
theorem segPtr_end (chosen : List Selection) (hc : ChosenOk chosen) :
    segPtr (schedule chosen) 35 = streamBase + 280 + 64 * slotBase chosen 7 := by
  unfold segPtr
  rw [List.take_of_length_le (by rw [schedule_length])]
  have h1 := schedule_folds chosen hc
  have h2 : ((schedule chosen).map fun s => 8 + 64 * s.a).sum = 8 * 35 + 64 * ((schedule chosen).map Segment.a).sum := by
    rw [List.sum_map_add, List.map_const', List.sum_replicate, schedule_length, List.sum_map_mul_left]; rfl
  rw [h2, h1]; omega
def decVal (N : HashOutput) (w : WBytes) (c : Nat) : Nat × Nat → Digest :=
  valOf (witDecP N w).signature.proof (slotBase (selections N) c) (slotPositions ((selections N).getD c ⟨0, []⟩))
def decPad (N : HashOutput) (w : WBytes) (c : Nat) : Nat × Nat → Digest :=
  valOf (padDecP N w).fold (slotBase (selections N) c) (slotPositions ((selections N).getD c ⟨0, []⟩))
theorem decoded_foldOk (N : HashOutput) (w : WBytes) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115) {c i r : Nat} (hc7 : c < 7) (hi : i < 5)
    (hr : r < ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).a) :
    FoldOk w (decVal N w c) (decPad N w c) ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).g
      (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).lo + r)
      (segPtr (schedule (selections N)) (5 * c + i)) r := by
  have hn : 5 * c + i < 35 := by omega
  have hsg := schedule_getD (selections N) hn
  rw [show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at hsg
  have hr' : r < ((schedule (selections N)).getD (5 * c + i) default).a := by rw [hsg]; exact hr
  obtain ⟨hsplit, hlt⟩ := foldSlot_split (selections N) hc hn hr'
  rw [show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at hsplit hlt
  have hb1 := slotBase_mono (selections N) (show c + 1 ≤ 7 by omega)
  rw [slotBase_succ] at hb1
  have hk : foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r < 115 := by omega
  have hplan := streamPlan_foldSlot (selections N) hc hn hr' hk
  have htop := (foldFacts c _ (hc c hc7)).top i hi
  have hpar : ((schedule (selections N)).getD (5 * c + i) default).heap r % 2 =
      ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).g /
        2 ^ (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).lo + r) % 2 := by
    rw [hsg]; unfold Segment.heap; exact heap_mod_two (by omega)
  have hidx : (slotBase (selections N) c + (slotPositions ((selections N).getD c ⟨0, []⟩)).idxOf
      (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).sib r)) % 115 =
      foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r := by
    rw [hsplit, Nat.mod_eq_of_lt (by omega)]
  have hP : ∀ (x : Fin 115), x.val = foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r →
      (witDecP N w).signature.proof x = (witDecP N w).signature.proof ⟨_, hk⟩ := fun x hx => congrArg _ (Fin.ext hx)
  have hQ : ∀ (x : Fin 115), x.val = foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r →
      (padDecP N w).fold x = (padDecP N w).fold ⟨_, hk⟩ := fun x hx => congrArg _ (Fin.ext hx)
  constructor
  · show valOf _ _ _ _ = _
    unfold valOf
    rw [hP _ hidx]
    unfold witDecP
    simp only [slotOffset, hplan, Option.map_some, hpar]
  · show valOf _ _ _ _ = _
    unfold valOf
    rw [hQ _ hidx]
    unfold padDecP
    simp only [slotBlock, hplan, Option.map_some]
theorem segPtr_zero (segs : List Segment) : segPtr segs 0 = streamBase := by simp [segPtr]
theorem decoded_segsOk (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7) :
    SegsOk w (decVal N w c) (decPad N w c) (segPtr (schedule (selections N)) (5 * c))
      (coordSchedule c ((selections N).getD c ⟨0, []⟩)) ∧
    segsEnd (segPtr (schedule (selections N)) (5 * c)) (coordSchedule c ((selections N).getD c ⟨0, []⟩)) =
      segPtr (schedule (selections N)) (5 * (c + 1)) := by
  obtain ⟨hok, hadm, hmatch⟩ := h
  have hc := chosenOk_of N hok
  have hle := slotBase_seven_le N hc hadm
  have hlen := coordSchedule_length c ((selections N).getD c ⟨0, []⟩)
  have := segsOk_of_getD w (decVal N w c) (decPad N w c) (coordSchedule c ((selections N).getD c ⟨0, []⟩))
    (fun i => segPtr (schedule (selections N)) (5 * c + i))
    (fun i hi => by
      rw [hlen] at hi
      have hn : 5 * c + i < 35 := by omega
      have := segPtr_succ (schedule (selections N)) (m := 5 * c + i) (by rw [schedule_length]; exact hn)
      rw [schedule_getD _ hn, show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at this
      simpa only [Nat.add_assoc] using this)
    (fun i hi => by
      rw [hlen] at hi
      have hn : 5 * c + i < 35 := by omega
      refine ⟨?_, fun r hr => decoded_foldOk N w hc hle hc7 hi hr⟩
      have := hmatch (5 * c + i) (by rw [schedule_length]; exact hn)
      rwa [schedule_getD _ hn, show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at this)
  simp only [Nat.add_zero, hlen] at this
  exact ⟨this.1, by rw [this.2]; ring_nf⟩
def ftsStreamStep (w : WBytes) (index : Nat) (chosen : List Selection) (state : Option (List Digest × Nat))
    (coord : Nat) : M (Option (List Digest × Nat)) := do
  let some (roots, ptr) := state | pure none
  let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
  pure (some (roots ++ [root], ptr))
theorem ftsP_eq (w : WBytes) (index : Nat) (chosen : List Selection) :
    ftsP w index chosen = (do
      let state ← (List.range 7).foldlM (ftsStreamStep w index chosen) (some ([], streamBase))
      let some (roots, ptr) := state | pure none
      if streamEnd < ptr then return none
      pure (some (← forestPk index roots))) := rfl
def canonD (N : HashOutput) (w : WBytes) (c : Nat) : M Digest :=
  coordCanon (N.toNat % 2 ^ 31) c
    (leafAt w (N.toNat % 2 ^ 31) c [selLeaf ((selections N).getD c ⟨0, []⟩) 0, selLeaf ((selections N).getD c ⟨0, []⟩) 1,
      selLeaf ((selections N).getD c ⟨0, []⟩) 2])
    (decVal N w c) (decPad N w c) (selLeaf ((selections N).getD c ⟨0, []⟩) 0)
    (selLeaf ((selections N).getD c ⟨0, []⟩) 1) (selLeaf ((selections N).getD c ⟨0, []⟩) 2)
theorem stream_step_dec (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7)
    (roots : List Digest) :
    ftsStreamStep w (N.toNat % 2 ^ 31) (selections N) (some (roots, segPtr (schedule (selections N)) (5 * c))) c =
      (fun v => some (roots ++ [v], segPtr (schedule (selections N)) (5 * (c + 1)))) <$> canonD N w c := by
  have hs := chosenOk_of N h.1 c hc7
  obtain ⟨hok, hend⟩ := decoded_segsOk N w h hc7
  unfold ftsStreamStep
  simp only []
  rw [ftsCoordP_canon w _ c _ _ (decVal N w c) (decPad N w c) hs.b hs.l2 hs.s01 hs.s12 hok, hend]
  simp only [bind_map_left, map_eq_bind_pure_comp, Function.comp_def, canonD, bind_assoc, pure_bind]
theorem leafHP_dec (N : HashOutput) (w : WBytes) {c : Nat} (hc7 : c < 7) (gs : List Nat) (g : Nat)
    (hg : gs.idxOf g < 3) :
    leafHP (N.toNat % 2 ^ 31) c gs ((List.range 3).map (fun j =>
        (witDecP N w).signature.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) (padDecP N w) g =
      leafAt w (N.toNat % 2 ^ 31) c gs g := by
  unfold leafHP leafAt pendingHash
  have h1 : (3 * c + gs.idxOf g) % 22 = 3 * c + gs.idxOf g := Nat.mod_eq_of_lt (by omega)
  have h2 : (3 * c + gs.idxOf g + 1) % 22 = 3 * c + gs.idxOf g + 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : (c * 3 + gs.idxOf g) % 21 = 3 * c + gs.idxOf g := by rw [Nat.mod_eq_of_lt (by omega)]; ring
  simp only [padDecP, h1, h2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg,
    Option.map_some, Option.getD_some, witDecP, h3]
theorem core_step_dec (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7)
    (roots : List Digest) :
    ftsStepP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)
        (some (roots, slotBase (selections N) c)) c =
      (fun v => some (roots ++ [v], slotBase (selections N) (c + 1))) <$> canonD N w c := by
  have hc := chosenOk_of N h.1
  have hs := hc c hc7
  have hle := slotBase_seven_le N hc h.2.1
  have hb1 := slotBase_mono (selections N) (show c + 1 ≤ 7 by omega)
  rw [slotBase_succ] at hb1 ⊢
  rw [ftsStepP_canon _ _ _ _ roots _ c hs (by omega) (decVal N w c) (decPad N w c)
    (slotsMatch_valOf _ _ _ _ (slotPositions_nodup _))]
  unfold canonD
  rw [hs.selected]
  congr 1
  have hg := hs.selected
  have g01 : selLeaf ((selections N).getD c ⟨0, []⟩) 0 < selLeaf ((selections N).getD c ⟨0, []⟩) 1 := by
    unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf ((selections N).getD c ⟨0, []⟩) 1 < selLeaf ((selections N).getD c ⟨0, []⟩) 2 := by
    unfold selLeaf; have := hs.s12; omega
  apply coordCanon_congr_leaf <;> apply leafHP_dec N w hc7 <;>
    exact List.idxOf_lt_length_of_mem (by simp)
theorem foldlM_canon (step : Option (List Digest × Nat) → Nat → M (Option (List Digest × Nat)))
    (P : Nat → M Digest) (pos : Nat → Nat)
    (hstep : ∀ c < 7, ∀ roots, step (some (roots, pos c)) c = (fun v => some (roots ++ [v], pos (c + 1))) <$> P c) :
    ∀ n ≤ 7, (List.range n).foldlM step (some ([], pos 0)) =
      (fun roots => some (roots, pos n)) <$> (List.range n).foldlM (fun roots c => (fun v => roots ++ [v]) <$> P c) [] := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldlM_append, List.foldlM_append, ih (by omega), bind_map_left, map_bind]
      congr 1; funext roots
      simp only [List.foldlM_cons, List.foldlM_nil, hstep n (by omega), bind_map_left, map_bind,
        Functor.map_map, bind_pure]
theorem dec_proof_tail (N : HashOutput) (w : WBytes) (h : Shaped N w) (k : Fin 115)
    (hk : slotBase (selections N) 7 ≤ k.val) : (witDecP N w).signature.proof k = 0 := by
  have hc := chosenOk_of N h.1
  have hnone : streamPlan (selections N) k = none := by
    unfold streamPlan
    rw [List.find?_eq_none]
    rintro ⟨n, r⟩ hp
    obtain ⟨hm1, hm2⟩ := mem_foldPositions.mp hp
    rw [schedule_length] at hm1
    simp only at hm1 hm2
    obtain ⟨e, l⟩ := foldSlot_split (selections N) hc hm1 hm2
    have hb1 := slotBase_mono (selections N) (show n / 5 + 1 ≤ 7 by omega)
    rw [slotBase_succ] at hb1
    simp only [decide_eq_true_eq]
    omega
  show (match slotOffset (selections N) k with | some off => wdig w off | none => 0) = 0
  simp [slotOffset, hnone]
theorem ftsP_shaped (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    ftsP w (N.toNat % 2 ^ 31) (selections N) =
      recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N) := by
  have hc := chosenOk_of N h.1
  have hle := slotBase_seven_le N hc h.2.1
  rw [ftsP_eq, recoverFtsP_eq]
  have A := foldlM_canon (ftsStreamStep w (N.toNat % 2 ^ 31) (selections N)) (canonD N w)
      (fun c => segPtr (schedule (selections N)) (5 * c)) (fun c hc7 roots => stream_step_dec N w h hc7 roots) 7 le_rfl
  have B := foldlM_canon (ftsStepP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N))
      (canonD N w) (fun c => slotBase (selections N) c) (fun c hc7 roots => core_step_dec N w h hc7 roots) 7 le_rfl
  simp only [Nat.mul_zero, segPtr_zero] at A
  simp only [show slotBase (selections N) 0 = 0 from rfl] at B
  rw [A, B, bind_map_left, bind_map_left]
  refine bind_congr (fun roots => ?_)
  have hend : ¬ streamEnd < segPtr (schedule (selections N)) (5 * 7) := by
    rw [show 5 * 7 = 35 by rfl, segPtr_end _ hc]; unfold streamEnd streamBase; omega
  have htail : ((List.range (115 - slotBase (selections N) 7)).all fun j =>
      decide ((witDecP N w).signature.proof ⟨(slotBase (selections N) 7 + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) =
        true := by
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    simp only [decide_eq_true_eq]
    exact dec_proof_tail N w h _ (by simp only [Nat.mod_eq_of_lt (show slotBase (selections N) 7 + j < 115 by omega)]; omega)
  dsimp only
  rw [if_neg hend, htail]
  rfl
theorem layerP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat) :
    layerP w (N.toNat % 2 ^ 31) lay digits =
      recoverLayerP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) lay digits := rfl
theorem layersP_dec (N : HashOutput) (w : WBytes) : ∀ n root,
    layersP w (N.toNat % 2 ^ 31) n root = verifyLayersP (witDecP N w) (padDecP N w) (N.toNat % 2 ^ 31) n root := by
  intro n
  induction n with
  | zero => intro root; rfl
  | succ n ih =>
      intro root
      simp only [layersP, verifyLayersP, layerP_dec, ih]
      rfl
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  let chosen := selections N
  if !selectionsOk chosen then return false
  if !digestGate N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← ftsP w index chosen | pure false
  let some root ← layersP w index 4 root | pure false
  pure (root == pk)
theorem verifyP_eq_tail (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w = ((do
      let some N ← digestP m w | pure false
      verifyTailP pk w N) : M Bool) := rfl
theorem verifyTailP_shaped (pk : Digest) (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    verifyTailP pk w N = verifyPadsTail pk N (witDecP N w) (padDecP N w) := by
  unfold verifyTailP verifyPadsTail
  simp only []
  rw [if_neg (by simp [h.1])]
  cases hg : digestGate N with
  | false => simp [digestAdmissible, hg]
  | true =>
      have ha : digestAdmissible N=true := by simp [digestAdmissible,h.2.1,hg]
      simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [ftsP_shaped N w h]
      simp only [layersP_dec]
      try
        refine bind_congr (fun r => ?_)
        rcases r with _ | root
        · rfl
        · refine bind_congr (fun r => ?_)
          rcases r with _ | root <;> rfl
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3_Gate6_VerifierGate ====
section

namespace SigGolfCandidate.T3M
open OracleComp SigGolfCandidate.T3
set_option maxHeartbeats 1000000
theorem verifyP_digestGate (answers : Correctness.Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    digestGate (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) = true := by
  rw [verifyP_eq_tail, evalWithAnswerFn_bind] at hv
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · simp [digestP, hdc] at hv
  · simp only [digestP, if_neg hdc, evalWithAnswerFn_map] at hv
    unfold verifyTailP at hv
    by_cases hs : selectionsOk (selections (evalWithAnswerFn answers (digest (wrho w) m (wdc w)))) = true
    · rw [if_neg (by simpa using hs)] at hv
      by_contra hg
      rw [if_pos (by simpa using hg)] at hv
      simp at hv
    · rw [if_pos (by simpa using hs)] at hv
      simp at hv
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Normal ====
section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
def rejectTail (w : WBytes) (N : HashOutput) : M Bool :=
  if !selectionsOk (selections N) then pure false
  else if !digestGate N then pure false
  else (fun _ => false) <$> ftsP w (N.toNat % 2 ^ 31) (selections N)
def segShape (w : WBytes) : List Nat → Nat → Nat → Option (Nat × Nat × List Nat)
  | stack, E, ptr =>
      let b := (wbyte w ptr).toNat
      if 11 < b % 16 then none
      else if 0 < b % 16 ∧ b / 32 % 2 ≠ E % 2 then none
      else
        let E := E / 2 ^ (b % 16)
        let ptr := segNext ptr (b % 16)
        match stack with
        | [] => if b / 16 % 2 = 1 then none else some (E, ptr, [])
        | Q :: rest =>
            if b / 16 % 2 = 0 then some (E, ptr, Q :: rest)
            else if Q ≠ E then none
            else segShape w rest (E / 2) ptr
def coordShape (w : WBytes) (sel : Selection) (ptr : Nat) : Option Nat := do
  let (E0, p0, s0) ← segShape w [] (2048 + selLeaf sel 0) ptr
  let (E1, p1, s1) ← segShape w ((E0 ^^^ 1) :: s0) (2048 + selLeaf sel 1) p0
  let (E2, p2, s2) ← segShape w ((E1 ^^^ 1) :: s1) (2048 + selLeaf sel 2) p1
  if E2 = 1 ∧ s2 = [] then some p2 else none
def ftsShape (w : WBytes) (chosen : List Selection) : Option Nat :=
  ((List.range 7).foldlM (fun ptr c => coordShape w (chosen.getD c ⟨0, []⟩) ptr) streamBase).filter
    (fun ptr => decide (ptr ≤ streamEnd))
def VerifyPNormal : Prop := ∀ (m : Message) (pk : Digest) (w : WBytes),
  verifyP m pk w =
    if (wdc w).toNat ≥ attemptLimit then pure false else do
      let N ← digest (wrho w) m (wdc w)
      if Shaped N w then verifyPadsTail pk N (witDecP N w) (padDecP N w) else rejectTail w N
def RejectTailFalse : Prop := ∀ (w : WBytes) (N : HashOutput), ∀ b ∈ support (rejectTail w N), b = false
def VerifyPadsZero : Prop := ∀ (m : Message) (pk : Digest) (w : Witness), verifyPads m pk w 0 = verify m pk w
def StreamShapedIff : Prop := ∀ (N : HashOutput) (w : WBytes), selectionsOk (selections N) = true →
  ((ftsShape w (selections N)).isSome = true ↔
    admissible (selections N) = true ∧ StreamMatches (selections N) w)
theorem rejectTail_false (w : WBytes) (N : HashOutput) : ∀ b ∈ support (rejectTail w N), b = false := by
  intro b hb
  unfold rejectTail at hb
  split at hb
  · simpa using hb
  · split at hb
    · simpa using hb
    · simp only [support_map, Set.mem_image] at hb
      obtain ⟨_, _, rfl⟩ := hb
      rfl
theorem recoverChildP_zero (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) : ∀ level node used,
    recoverChildP index coord leaves values proof 0 level node used =
      recoverChild index coord leaves values proof level node used := by
  intro level
  induction level with
  | zero => intro node used; simp only [recoverChildP, recoverChild, Pads.zero_leaf, ftsLeafP_zero]
  | succ level ih =>
      intro node used
      simp only [recoverChildP, recoverChild, ih, foldPad_zero, nodeHashP_zero]
      rfl
theorem recoverFtsP_zero (sig : Signature) (index : Nat) (chosen : List Selection) :
    recoverFtsP sig 0 index chosen = recoverFts sig index chosen := by
  simp only [recoverFtsP, recoverFts, recoverChildP_zero, Pads.zero_fold, nodeHashP_zero]
  rfl
theorem recoverLayerP_zero (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hindex : index < 2^31) :
    recoverLayerP sig 0 index lay digits = recoverLayer sig index lay digits := by
  simp only [recoverLayerP, recoverLayer, Pads.zero_chain, Pads.zero_chainHeader,
    chainPL_zero_route _ _ _ _ _ hindex, Pads.zero_merkle, nodeHashP_zero]
theorem verifyLayersP_zero (w : Witness) (index : Nat) (hindex : index < 2^31) : ∀ n root,
    verifyLayersP w 0 index n root = verifyLayers w index n root := by
  intro n
  induction n with
  | zero => intro root; rfl
  | succ n ih =>
      intro root
      simp only [verifyLayersP, verifyLayers, recoverLayerP_zero _ _ _ _ hindex, ih]
      rfl
theorem verifyPads_zero (m : Message) (pk : Digest) (w : Witness) : verifyPads m pk w 0 = verify m pk w := by
  simp only [verifyPads, verifyPadsTail, verify, recoverFtsP_zero,
    verifyLayersP_zero _ _ (Nat.mod_lt _ (by decide))]
  rfl
theorem verifyPadsZero_holds : VerifyPadsZero := verifyPads_zero
theorem rejectTailFalse_holds : RejectTailFalse := rejectTail_false
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Roundtrip ====
section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem readLE_cons (b : UInt8) (L : List UInt8) : readLE (b :: L) = b.toNat + 256 * readLE L := rfl
theorem readLE_append (A B : List UInt8) : readLE (A ++ B) = readLE A + 256 ^ A.length * readLE B := by
  induction A with
  | nil => simp [readLE]
  | cons a A ih => rw [List.cons_append, readLE_cons, readLE_cons, ih, List.length_cons, pow_succ]; ring
theorem readLE_lt (L : List UInt8) : readLE L < 256 ^ L.length := by
  induction L with
  | nil => simp [readLE]
  | cons a L ih =>
      rw [readLE_cons, List.length_cons, pow_succ]
      have := a.toNat_lt
      omega
theorem readLE_drop : ∀ (L : List UInt8) (k : Nat), readLE L / 256 ^ k = readLE (L.drop k) := by
  intro L k
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
      cases L with
      | nil => simp [readLE]
      | cons a L =>
          rw [List.drop_succ_cons, ← ih L, readLE_cons, pow_succ', ← Nat.div_div_eq_div_mul]
          congr 1
          have := a.toNat_lt
          omega
theorem readLE_take : ∀ (L : List UInt8) (k : Nat), readLE L % 256 ^ k = readLE (L.take k) := by
  intro L k
  induction k generalizing L with
  | zero => simp [readLE, Nat.mod_one]
  | succ k ih =>
      cases L with
      | nil => simp [readLE]
      | cons a L =>
          rw [List.take_succ_cons, readLE_cons, readLE_cons, ← ih L, pow_succ', Nat.mod_mul]
          have := a.toNat_lt
          have h1 : (a.toNat + 256 * readLE L) % 256 = a.toNat := by omega
          have h2 : (a.toNat + 256 * readLE L) / 256 = readLE L := by omega
          rw [h1, h2]
theorem extract_readLE (L : List UInt8) (n : Nat) (hL : L.length ≤ n) (off k : Nat) :
    (BitVec.ofNat (8 * n) (readLE L)).extractLsb' (8 * off) (8 * k) =
      BitVec.ofNat (8 * k) (readLE ((L.drop off).take k)) := by
  have hlt : readLE L < 2 ^ (8 * n) := by
    have := readLE_lt L
    calc readLE L < 256 ^ L.length := this
      _ ≤ 256 ^ n := Nat.pow_le_pow_right (by norm_num) hL
      _ = 2 ^ (8 * n) := by rw [pow_mul]; norm_num
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.shiftRight_eq_div_pow, show 2 ^ (8 * off) = 256 ^ off by rw [pow_mul]; norm_num, readLE_drop,
    show 2 ^ (8 * k) = 256 ^ k by rw [pow_mul]; norm_num, readLE_take]
  rw [Nat.mod_eq_of_lt]
  have := readLE_lt ((L.drop off).take k)
  calc readLE ((L.drop off).take k) < 256 ^ ((L.drop off).take k).length := this
    _ ≤ 256 ^ k := Nat.pow_le_pow_right (by norm_num) (by simp)
theorem headerBytes_length (w : Witness) : (headerBytes w).length = 64 := by
  simp [headerBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem leafBytes_length (sig : Signature) : (leafBytes sig).length = 1024 := by
  simp [leafBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem streamBytes_length (chosen : List Selection) (proof : Fin 115 → Digest) :
    (streamBytes chosen proof).length = 8200 := by
  simp only [streamBytes, zeros, List.length_take, List.length_append, List.length_replicate]
  omega
theorem layerBytes_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerBytes lay leaf ls).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytes
  rw [List.length_append, List.length_flatMap, List.length_flatMap]
  have h1 : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by
    intro j; split <;> simp [zeros, bytesLE_length]
  simp only [h1]
  simp only [List.length_append, zeros, List.length_replicate, bytesLE_length, List.map_const',
    List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
  ring
theorem layerStorage_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerStorage lay leaf ls).length = 64 * (height lay + chainCount lay) := by
  simp only [layerStorage, layerBytes_length]

theorem take_one_drop (L : List UInt8) : ∀ i, readLE ((L.drop i).take 1) = (L.getD i 0).toNat := by
  induction L with
  | nil => intro i; simp [readLE]
  | cons a L ih =>
      intro i
      cases i with
      | zero => simp [readLE]
      | succ i => rw [List.drop_succ_cons, ih i]; simp
def window (L : List UInt8) (off n : Nat) : List UInt8 := (L.drop off).take n
theorem window_append_left (A B : List UInt8) (off n : Nat) (h : off + n ≤ A.length) :
    window (A ++ B) off n = window A off n := by
  unfold window
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem window_append_right (A B : List UInt8) (off n : Nat) (h : A.length ≤ off) :
    window (A ++ B) off n = window B (off - A.length) n := by
  unfold window
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
theorem window_flatMap {β : Type} (l : List β) (f : β → List UInt8) :
    ∀ (i : Nat) (hi : i < l.length) (j n : Nat), j + n ≤ (f l[i]).length →
      window (l.flatMap f) (((l.take i).map fun b => (f b).length).sum + j) n = window (f l[i]) j n := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons b l ih =>
      intro i hi j n hjn
      cases i with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons,
            List.getElem_cons_zero] at hjn ⊢
          exact window_append_left _ _ _ _ hjn
      | succ i =>
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons,
            List.getElem_cons_succ] at hjn ⊢
          rw [window_append_right _ _ _ _ (by omega), show (f b).length + ((l.take i).map fun b => (f b).length).sum + j
            - (f b).length = ((l.take i).map fun b => (f b).length).sum + j by omega]
          exact ih i (by simpa using hi) j n hjn
theorem window_flatMap_const {β : Type} (l : List β) (f : β → List UInt8) (k : Nat) (hk : ∀ b, (f b).length = k)
    (i : Nat) (hi : i < l.length) (j n : Nat) (hjn : j + n ≤ k) :
    window (l.flatMap f) (k * i + j) n = window (f l[i]) j n := by
  have := window_flatMap l f i hi j n (by rw [hk]; exact hjn)
  rwa [show ((l.take i).map fun b => (f b).length).sum = k * i by
    rw [List.map_congr_left (fun b _ => hk b), List.map_const', List.sum_replicate, List.length_take,
      Nat.min_eq_left hi.le, smul_eq_mul, Nat.mul_comm]] at this
theorem window_full (L : List UInt8) (n : Nat) (h : L.length = n) : window L 0 n = L := by
  unfold window; rw [List.drop_zero, List.take_of_length_le (by omega)]
theorem window_zeros (m off n : Nat) (h : off + n ≤ m) : window (zeros m) off n = zeros n := by
  unfold window zeros; rw [List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]
theorem readDigest_zeros : readDigest (zeros 16) = 0 := by
  rw [show zeros 16 = bytesLE 16 0 from bytesLE_zero16.symm, Correctness.readDigest_bytesLE]
theorem readLE_bytesLE_32 (v : BitVec 32) : BitVec.ofNat 32 (readLE (bytesLE 4 v)) = v := by
  rw [Correctness.readLE_bytesLE]; exact BitVec.ofNat_toNat 32 v
theorem window_take (L : List UInt8) (m off n : Nat) (h : off + n ≤ m) : window (L.take m) off n = window L off n := by
  unfold window; rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
theorem getD_of_window (L : List UInt8) (i : Nat) (x : UInt8) (h : window L i 1 = [x]) : L.getD i 0 = x := by
  unfold window at h
  rcases hl : L.drop i with _ | ⟨y, rest⟩
  · rw [hl] at h; simp at h
  · rw [hl] at h
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at h
    have hi : i < L.length := by
      by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; simp at hl
    rw [List.getD_eq_getElem _ _ hi]
    have e := congrArg (fun l => l[0]?) hl
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero, List.getElem?_eq_getElem hi] at e
    rw [Option.some.inj e, h]
section regions
variable (N : HashOutput) (w : Witness)
theorem win_header (off n : Nat) (h : off + n ≤ 64) :
    window (witList N w) off n = window (headerBytes w) off n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length]; omega)]
theorem win_leaf (off n : Nat) (h1 : 64 ≤ off) (h : off + n ≤ 1088) :
    window (witList N w) off n = window (leafBytes w.signature) (off - 64) n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [headerBytes_length]; omega), headerBytes_length]
theorem win_stream (off n : Nat) (h1 : 1088 ≤ off) (h : off + n ≤ 9288) :
    window (witList N w) off n = window (streamBytes (selections N) w.signature.proof) (off - 1088) n := by
  unfold witList
  rw [window_append_left _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [headerBytes_length, leafBytes_length]; omega)]
  simp [headerBytes_length, leafBytes_length]
theorem win_layers (off n : Nat) (h1 : 9288 ≤ off) :
    window (witList N w) off n = window ((List.finRange 4).flatMap fun lay =>
      layerStorage lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) (off - 9288) n := by
  unfold witList
  rw [window_append_right _ _ _ _ (by simp [headerBytes_length, leafBytes_length, streamBytes_length]; omega)]
  simp [headerBytes_length, leafBytes_length, streamBytes_length]
end regions
theorem foldBytes_length (E : Nat) (sib : Digest) : (foldBytes E sib).length = 64 := by
  unfold foldBytes; split <;> simp [zeros, bytesLE_length]
theorem segBytes_length (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) :
    (segBytes chosen proof seg).length = 8 + 64 * seg.a := by
  unfold segBytes
  simp only [List.length_append, List.length_singleton, zeros, List.length_replicate, List.length_flatMap,
    foldBytes_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega
theorem stream_flat_length (chosen : List Selection) (proof : Fin 115 → Digest) :
    ((schedule chosen).flatMap (segBytes chosen proof)).length = ((schedule chosen).map fun s => 8 + 64 * s.a).sum := by
  rw [List.length_flatMap]; congr 1; exact List.map_congr_left (fun s _ => segBytes_length _ _ _)
theorem segPtr_le_end (chosen : List Selection) (_hc : ChosenOk chosen) {n : Nat} (_hn : n ≤ 35) :
    segPtr (schedule chosen) n ≤ segPtr (schedule chosen) 35 := by
  unfold segPtr
  have := List.sum_take_add_sum_drop ((schedule chosen).map fun s => 8 + 64 * s.a) n
  rw [← List.map_take] at this
  rw [show (schedule chosen).take 35 = schedule chosen from List.take_of_length_le (by rw [schedule_length])]
  omega
theorem win_seg (N : HashOutput) (w : Witness) (hc : ChosenOk (selections N)) (hle : slotBase (selections N) 7 ≤ 115)
    {n : Nat} (hn : n < 35) (j m : Nat) (hjm : j + m ≤ 8 + 64 * ((schedule (selections N)).getD n default).a) :
    window (witList N w) (segPtr (schedule (selections N)) n + j) m =
      window (segBytes (selections N) w.signature.proof ((schedule (selections N)).getD n default)) j m := by
  have hend := segPtr_end (selections N) hc
  have hsucc := segPtr_succ (schedule (selections N)) (m := n) (by rw [schedule_length]; exact hn)
  have hmono := segPtr_le_end (selections N) hc (show n + 1 ≤ 35 by omega)
  unfold segNext at hsucc
  have hb : 1088 ≤ segPtr (schedule (selections N)) n := by unfold segPtr streamBase; omega
  have hflat := stream_flat_length (selections N) w.signature.proof
  have hsum : segPtr (schedule (selections N)) 35 = 1088 + ((schedule (selections N)).map fun s => 8 + 64 * s.a).sum := by
    unfold segPtr streamBase; rw [List.take_of_length_le (by rw [schedule_length])]
  rw [win_stream _ _ _ _ (by omega) (by unfold streamBase at hend; omega)]
  unfold streamBytes
  rw [window_take _ _ _ _ (by unfold streamBase at hend; omega),
    window_append_left _ _ _ _ (by rw [hflat]; omega)]
  have hpre : segPtr (schedule (selections N)) n + j - 1088 =
      (((schedule (selections N)).take n).map fun s => (segBytes (selections N) w.signature.proof s).length).sum + j := by
    unfold segPtr streamBase
    rw [List.map_congr_left (fun s _ => segBytes_length _ _ s)]
    omega
  rw [hpre, window_flatMap _ _ n (by rw [schedule_length]; exact hn) j m
    (by rw [segBytes_length, ← List.getD_eq_getElem _ default (by rw [schedule_length]; exact hn)]; exact hjm)]
  rw [List.getD_eq_getElem _ default (by rw [schedule_length]; exact hn)]
theorem segBytes_header (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) :
    window (segBytes chosen proof seg) 0 1 = [UInt8.ofNat seg.byte0] := by
  unfold segBytes window; simp
theorem segBytes_fold (chosen : List Selection) (proof : Fin 115 → Digest) (seg : Segment) {r : Nat}
    (hr : r < seg.a) (j : Nat) (hj : j + 16 ≤ 64) :
    window (segBytes chosen proof seg) (8 + 64 * r + j) 16 =
      window (foldBytes (seg.heap r) (proof ⟨foldSlot chosen seg r % 115, Nat.mod_lt _ (by decide)⟩)) j 16 := by
  unfold segBytes
  have hl : ([UInt8.ofNat seg.byte0] ++ zeros 7).length = 8 := by simp [zeros]
  rw [window_append_right _ _ _ _ (by rw [hl]; omega), hl, show 8 + 64 * r + j - 8 = 64 * r + j by omega]
  rw [window_flatMap_const _ _ 64 (fun _ => foldBytes_length _ _) r (by simpa using hr) j 16 hj]
  simp only [List.getElem_range]
theorem foldBytes_sib (E : Nat) (sib : Digest) : window (foldBytes E sib) (sibOff (E % 2)) 16 = bytesLE 16 sib := by
  unfold foldBytes sibOff
  rcases Nat.mod_two_eq_zero_or_one E with h | h
  · simp only [h, show (0 : Nat) ≠ 1 by decide, if_false]
    rw [window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
  · simp only [h, if_true]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
theorem foldBytes_pad (E : Nat) (sib : Digest) : window (foldBytes E sib) 32 16 = zeros 16 := by
  unfold foldBytes
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length])]
  · rw [window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega)]

theorem layerBytes_merkle (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (j : Fin (height lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (layerBytes lay leaf ls) (64 * (height lay - 1 - j.val) + o) 16 =
      window (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)) o 16 := by
  unfold layerBytes
  rw [window_append_left _ _ _ _ (by
    rw [List.length_flatMap]
    have : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by intro j; split <;> simp [zeros, bytesLE_length]
    simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
    have := j.isLt; omega)]
  rw [window_flatMap_const _ _ 64 (fun j => by split <;> simp [zeros, bytesLE_length]) (height lay - 1 - j.val)
    (by simp; omega) o 16 ho]
  have hj : ((List.finRange (height lay)).reverse[height lay - 1 - j.val]'(by simp; omega)) = j := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hj]
theorem layerBytes_chain (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (i : Fin (chainCount lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (layerBytes lay leaf ls) (64 * height lay + 64 * (chainCount lay - 1 - i.val) + o) 16 =
      window (zeros 48 ++ bytesLE 16 (ls.values i)) o 16 := by
  unfold layerBytes
  have hM : ((List.finRange (height lay)).reverse.flatMap fun j =>
      if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 * height lay := by
    rw [List.length_flatMap]
    have : ∀ j : Fin (height lay), (if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (ls.path j)).length = 64 := by intro j; split <;> simp [zeros, bytesLE_length]
    simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
    ring
  rw [window_append_right _ _ _ _ (by rw [hM]; omega), hM,
    show 64 * height lay + 64 * (chainCount lay - 1 - i.val) + o - 64 * height lay =
      64 * (chainCount lay - 1 - i.val) + o by omega]
  rw [window_flatMap_const _ _ 64 (fun j => by simp [zeros, bytesLE_length]) (chainCount lay - 1 - i.val)
    (by simp; omega) o 16 ho]
  have hi : ((List.finRange (chainCount lay)).reverse[chainCount lay - 1 - i.val]'(by simp; omega)) = i := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hi]
section fields
variable (N : HashOutput) (w : Witness)
end fields
theorem schedule_a_le (chosen : List Selection) (hc : ChosenOk chosen) {n : Nat} (hn : n < 35) :
    ((schedule chosen).getD n default).lo + ((schedule chosen).getD n default).a ≤ 11 := by
  rw [schedule_getD chosen hn]; exact (foldFacts _ _ (hc _ (by omega))).top _ (by omega)
theorem byte0_lt (seg : Segment) (h : seg.a ≤ 11) : seg.byte0 < 64 := by
  unfold Segment.byte0 Segment.t
  have := Nat.mod_lt (seg.heap 0) (show 0 < 2 by decide)
  split <;> omega
theorem Segment.matches_byte0 (seg : Segment) (h : seg.a ≤ 11) : seg.Matches seg.byte0 := by
  unfold Segment.Matches Segment.byte0
  have ht : seg.t < 2 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · split <;> omega
  · cases seg.merge <;> simp <;> omega
  · intro _; split <;> omega
theorem foldPositions_nodup (segs : List Segment) : (foldPositions segs).Nodup := by
  unfold foldPositions
  refine List.nodup_flatMap.mpr ⟨fun n _ => (List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
  refine (List.nodup_range).pairwise_of_forall_ne (fun a _ b _ hab => ?_)
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range, not_exists, not_and]
  rintro p ⟨r, _, rfl⟩ r' _ h
  simp only [Prod.mk.injEq] at h
  exact hab h.1.symm
theorem foldPositions_length (segs : List Segment) : (foldPositions segs).length = (segs.map Segment.a).sum := by
  unfold foldPositions
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [← sum_range_getD segs default Segment.a]
theorem foldSlot_surj (chosen : List Selection) (hc : ChosenOk chosen) {k : Nat} (hk : k < slotBase chosen 7) :
    ∃ p ∈ foldPositions (schedule chosen), foldSlot chosen ((schedule chosen).getD p.1 default) p.2 = k := by
  classical
  have key := Finset.surj_on_of_inj_on_of_card_le (s := (foldPositions (schedule chosen)).toFinset)
    (t := Finset.range (slotBase chosen 7))
    (fun p _ => foldSlot chosen ((schedule chosen).getD p.1 default) p.2)
    (fun p hp => by
      have hm := mem_foldPositions.mp (List.mem_toFinset.mp hp)
      rw [schedule_length] at hm
      obtain ⟨e, l⟩ := foldSlot_split chosen hc hm.1 hm.2
      have hb1 := slotBase_mono chosen (show p.1 / 5 + 1 ≤ 7 by omega)
      rw [slotBase_succ] at hb1
      rw [Finset.mem_range, e]; omega)
    (fun p q hp hq h => by
      have hm := mem_foldPositions.mp (List.mem_toFinset.mp hp)
      have hm' := mem_foldPositions.mp (List.mem_toFinset.mp hq)
      rw [schedule_length] at hm hm'
      obtain ⟨h1, h2⟩ := foldSlot_inj chosen hc hm.1 hm'.1 hm.2 hm'.2 h
      exact Prod.ext h1 h2)
    (by
      rw [Finset.card_range, List.toFinset_card_of_nodup (foldPositions_nodup _), foldPositions_length,
        schedule_folds chosen hc])
  obtain ⟨p, hp, he⟩ := key k (Finset.mem_range.mpr hk)
  exact ⟨p, List.mem_toFinset.mp hp, he.symm⟩
theorem LayerSignature.ext' {lay : Layer} {x y : LayerSignature lay} (hv : x.values = y.values)
    (hp : x.path = y.path) : x = y := by
  cases x; cases y; simp_all
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Honest ====
section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
def honestProgramCore (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness
def honestProgramB (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let wb ← expandB message keys.1 sig
    match wb with
    | none => pure false
    | some wb => verifyP message keys.1 wb
def isHash : Spec.Domain → Prop
  | .inl (.inl _) => False
  | _ => True
def isPublic : Spec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False
def ExpandEqExpandN : Prop := ∀ (m : Message) (pk : Digest) (σ : Signature),
  expand m pk σ = Option.map Prod.snd <$> expandN m pk σ
def VerifyPWitEncEval : Prop := ∀ (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature)
    (N : HashOutput) (w : Witness),
  evalWithAnswerFn answers (expandN m pk σ) = some (N, w) →
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (verify m pk w))
def HonestBEval : Prop := ∀ (answers : Correctness.Answers) (m : Message),
  evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m)
theorem expand_eq_expandN (m : Message) (pk : Digest) (σ : Signature) :
    expand m pk σ = Option.map Prod.snd <$> expandN m pk σ := by
  unfold expand expandN
  rw [map_bind]; congr 1; funext r
  rcases r with _ | ⟨counter, output⟩
  · simp
  · simp only
    rw [map_bind]; congr 1; funext r
    rcases r with _ | root
    · simp
    · simp only
      rw [map_bind]; congr 1; funext r
      rcases r with _ | ⟨root, counters⟩
      · simp
      · simp only
        split <;> simp
theorem expandEqExpandN_holds : ExpandEqExpandN := expand_eq_expandN
theorem recoverFtsP_canon (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (hc : ChosenOk chosen) (hle : slotBase chosen 7 ≤ 115) :
    recoverFtsP sig pads index chosen = (do
      let roots ← (List.range 7).foldlM (fun roots c => (fun v => roots ++ [v]) <$>
        coordCanon index c (leafHP index c (selectedLeaves (chosen.getD c ⟨0, []⟩))
            ((List.range 3).map (fun j => sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) pads)
          (valOf sig.proof (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
          (valOf pads.fold (slotBase chosen c) (slotPositions (chosen.getD c ⟨0, []⟩)))
          (selLeaf (chosen.getD c ⟨0, []⟩) 0) (selLeaf (chosen.getD c ⟨0, []⟩) 1)
          (selLeaf (chosen.getD c ⟨0, []⟩) 2)) []
      if !(List.range (115 - slotBase chosen 7)).all (fun j =>
          decide (sig.proof ⟨(slotBase chosen 7 + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
      pure (some (← forestPk index roots))) := by
  rw [recoverFtsP_eq]
  have B := foldlM_canon (ftsStepP sig pads index chosen) _ (fun c => slotBase chosen c)
    (fun c hc7 roots => by
      have hb1 := slotBase_mono chosen (show c + 1 ≤ 7 by omega)
      rw [slotBase_succ] at hb1 ⊢
      exact ftsStepP_canon sig pads index chosen roots _ c (hc c hc7) (by omega) _ _
        (slotsMatch_valOf _ _ _ _ (slotPositions_nodup _))) 7 le_rfl
  simp only [show slotBase chosen 0 = 0 from rfl] at B
  rw [B, bind_map_left]
theorem eval_recoverFtsP_tail (answers : Correctness.Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (hc : ChosenOk chosen) (hle : slotBase chosen 7 ≤ 115) (root : Digest)
    (h : evalWithAnswerFn answers (recoverFtsP sig pads index chosen) = some root) :
    ∀ k : Fin 115, slotBase chosen 7 ≤ k.val → sig.proof k = 0 := by
  rw [recoverFtsP_canon sig pads index chosen hc hle, evalWithAnswerFn_bind] at h
  intro k hk
  by_contra hne
  have hall : ((List.range (115 - slotBase chosen 7)).all (fun j =>
      decide (sig.proof ⟨(slotBase chosen 7 + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0))) = false := by
    by_contra hc
    rw [Bool.not_eq_false, List.all_eq_true] at hc
    have := hc (k.val - slotBase chosen 7) (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at this
    rw [show slotBase chosen 7 + (k.val - slotBase chosen 7) = k.val by omega] at this
    apply hne
    rw [← this]; congr 1; ext; simp [Nat.mod_eq_of_lt k.isLt]
  simp only [hall, Bool.not_false, if_true, evalWithAnswerFn_pure] at h
  exact absurd h (by simp)
theorem selectionsOk_of_admissible (N : HashOutput) (h : admissible (selections N) = true) :
    selectionsOk (selections N) = true := by
  unfold selectionsOk
  rw [List.all_eq_true]
  intro sel hm
  have hn : sel.leaves.Nodup := by
    simp only [admissible, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1 sel hm
  have hs := Correctness.selection_leaves_sorted N sel hm
  have hl := selection_leaves_length N sel hm
  obtain ⟨a, b, c, he⟩ := List.length_eq_three.mp hl
  rw [he] at hn hs ⊢
  rw [List.sortedLE_iff_pairwise] at hs
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hs
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega
structure ExpandFacts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature) (N : HashOutput)
    (w : Witness) : Prop where
  sig : w.signature = σ
  dc : w.digestCounter.toNat < attemptLimit
  digest : evalWithAnswerFn answers (digest σ.rho m w.digestCounter) = N
  adm : admissible (selections N) = true
  root : ∃ root, evalWithAnswerFn answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)) = some root
theorem expandN_facts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature) (N : HashOutput)
    (w : Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    ExpandFacts answers m pk σ N w := by
  simp only [expandN, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hf : evalWithAnswerFn answers (recoverFts σ (output.toNat % 2 ^ 31) (selections output)) with
      | none => simp only [hf, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some forest =>
          simp only [hf, evalWithAnswerFn_bind] at he
          cases hl : evalWithAnswerFn answers (expandLayers σ (output.toNat % 2 ^ 31) 4 forest) with
          | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some layers =>
              obtain ⟨root, counters⟩ := layers
              simp only [hl] at he
              split at he
              · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
              · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                obtain ⟨_, hcounter, houtput, hadm⟩ := Correctness.digestSearch_some answers σ.rho m
                  attemptLimit 0 counter output (by decide) hd
                exact ⟨rfl, by simpa using hcounter, houtput, hadm, ⟨forest, hf⟩⟩
theorem eval_map (answers : Correctness.Answers) {α β : Type} (f : α → β) (oa : M α) :
    evalWithAnswerFn answers (f <$> oa) = f (evalWithAnswerFn answers oa) := by
  rw [map_eq_bind_pure_comp, evalWithAnswerFn_bind]; rfl
theorem eval_countCalls_fst (answers : Correctness.Answers) {α : Type} (oa : M α) :
    (evalWithAnswerFn answers (Cost.countCalls oa)).1 = evalWithAnswerFn answers oa := by
  have := congrArg (evalWithAnswerFn answers) (Cost.fst_countWith (fun _ => 1) oa)
  rw [eval_map] at this
  exact this
theorem eval_countCalls_bind_congr (answers : Correctness.Answers) {α β : Type} (oa : M α) (f g : α → M β)
    (h : f (evalWithAnswerFn answers oa) = g (evalWithAnswerFn answers oa)) :
    evalWithAnswerFn answers (Cost.countCalls (oa >>= f)) = evalWithAnswerFn answers (Cost.countCalls (oa >>= g)) := by
  have h1 := eval_countCalls_fst answers oa
  unfold Cost.countCalls at h1 ⊢
  rw [Cost.countWith_bind, Cost.countWith_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind, h1, h]
theorem eval_expandB (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : Signature) :
    evalWithAnswerFn answers (expandB m pk σ) =
      (evalWithAnswerFn answers (expandN m pk σ)).map (fun x => witEnc x.1 x.2) := by
  unfold expandB; rw [eval_map]
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Witness_Queries ====
section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
def PubGood (q : Spec.Domain) : Prop := isPublic q ∧ Cost.GoodQuery q
def HashGood (q : Spec.Domain) : Prop := isHash q ∧ Cost.GoodQuery q
theorem PubGood.hashGood {q : Spec.Domain} (h : PubGood q) : HashGood q := by
  obtain ⟨hp, hg⟩ := h
  rcases q with (n | input) | c
  · exact hp.elim
  · exact ⟨trivial, hg⟩
  · exact hp.elim
section comb
variable {P : Spec.Domain → Prop}
theorem allQ_pure {α : Type} (a : α) : AllQueriesSatisfy (pure a : M α) P := allQueriesSatisfy_pure _ _
theorem allQ_bind {α β : Type} {p : M α} {f : α → M β} (hp : AllQueriesSatisfy p P)
    (hf : ∀ a, AllQueriesSatisfy (f a) P) : AllQueriesSatisfy (p >>= f) P := allQueriesSatisfy_bind hp hf
theorem allQ_map {α β : Type} (f : α → β) {p : M α} (hp : AllQueriesSatisfy p P) :
    AllQueriesSatisfy (f <$> p) P := by
  rw [map_eq_bind_pure_comp]; exact allQ_bind hp fun _ => allQ_pure _
theorem allQ_ite {α : Type} (c : Prop) [Decidable c] {p q : M α} (hp : AllQueriesSatisfy p P)
    (hq : AllQueriesSatisfy q P) : AllQueriesSatisfy (if c then p else q) P := by
  split <;> assumption
theorem allQ_foldlM {α β : Type} (l : List β) (f : α → β → M α) (h : ∀ a b, AllQueriesSatisfy (f a b) P)
    (init : α) : AllQueriesSatisfy (l.foldlM f init) P := by
  induction l generalizing init with
  | nil => exact allQ_pure _
  | cons b l ih => rw [List.foldlM_cons]; exact allQ_bind (h init b) ih
theorem allQ_mapM {α β : Type} (l : List α) (f : α → M β) (h : ∀ a, AllQueriesSatisfy (f a) P) :
    AllQueriesSatisfy (l.mapM f) P := by
  induction l with
  | nil => exact allQ_pure _
  | cons a l ih => rw [List.mapM_cons]; exact allQ_bind (h a) fun _ => allQ_bind ih fun _ => allQ_pure _
end comb
theorem pubGood_publicHash (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (publicHash input) PubGood :=
  (allQueriesSatisfy_query_iff _ _).mpr ⟨trivial, Cost.pad64_positive input h, Cost.pad64_aligned input⟩
theorem pubGood_shortHash (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (shortHash input) PubGood := by
  unfold shortHash; exact allQ_bind (pubGood_publicHash input h) fun _ => allQ_pure _
theorem pubGood_projHash (high : Bool) (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (projHash high input) PubGood := by
  unfold projHash; exact allQ_bind (pubGood_publicHash input h) fun _ => allQ_pure _
theorem pubGood_ftsLeafP (index coord leaf : Nat) (p0 s p1 : Digest) :
    AllQueriesSatisfy (ftsLeafP index coord leaf p0 s p1) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])
theorem pubGood_nodeHashP (tag lay tree heap : Nat) (l p r : Digest) :
    AllQueriesSatisfy (nodeHashP tag lay tree heap l p r) PubGood :=
  pubGood_projHash _ _ (by simp [bytesLE_length])
theorem pubGood_nodeHash (tag lay tree heap : Nat) (l r : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap l r) PubGood :=
  pubGood_projHash _ _ (by simp [bytesLE_length])
theorem pubGood_ftsLeaf (index coord leaf : Nat) (s : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf s) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length, zero16])
theorem pubGood_chainP (lay : Layer) (tree leaf i start count : Nat) (p0 p1 : Digest)
    (headerPad : BitVec 64) (v : Digest) :
    AllQueriesSatisfy (chainP lay tree leaf i start count p0 p1 headerPad v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [chainInputP, bytesLE_length])) _
theorem pubGood_chain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [chainInput, bytesLE_length, zero16])) _
/-- Witness stack: the top-aware padded chain and the scheme chain of layer `lay`. -/
theorem pubGood_chainPL (lay : Layer) (tree leaf i start count : Nat) (p0 p1 : Digest)
    (headerPad : BitVec 64) (v : Digest) :
    AllQueriesSatisfy (chainPL lay tree leaf i start count p0 p1 headerPad v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_projHash _ _ (by
    unfold chainInputPL; split <;> simp [chainInputP, bytesLE_length])) _
theorem pubGood_topChain (leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (topChain leaf i start count v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_projHash _ _ (by
    unfold topChainInput; split <;> simp [chainInput, bytesLE_length, zero16])) _
theorem pubGood_layChain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (layChain lay tree leaf i start count v) PubGood := by
  unfold layChain; split
  · exact pubGood_topChain _ _ _ _ _
  · exact pubGood_chain _ _ _ _ _ _ _
theorem pubGood_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) PubGood :=
  pubGood_projHash _ _ (by rw [leafInput_length]; split_ifs <;> omega)
theorem pubGood_forestPk (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (forestPk index roots) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])
theorem pubGood_digest (rho : Digest) (m : Message) (c : BitVec 32) :
    AllQueriesSatisfy (digest rho m c) PubGood :=
  pubGood_publicHash _ (by simp [digestInput, bytesLE_length])
theorem pubGood_encoding (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    AllQueriesSatisfy (shortHash (encodingInput lay tree leaf msg c)) PubGood :=
  pubGood_shortHash _ (by simp [encodingInput, bytesLE_length])
theorem pubGood_pendingHash (w : WBytes) (index coord : Nat) (node : Digest) (pending : Pending) :
    AllQueriesSatisfy (pendingHash w index coord node pending) PubGood := by
  cases pending <;> unfold pendingHash
  · exact pubGood_ftsLeafP _ _ _ _ _ _
  · exact pubGood_nodeHash _ _ _ _ _ _
theorem pubGood_foldsP (w : WBytes) (index coord ptr a : Nat) (node : Digest) (E : Nat) :
    AllQueriesSatisfy (foldsP w index coord ptr a node E) PubGood := by
  unfold foldsP
  refine allQ_foldlM _ _ (fun st r => ?_) _
  unfold foldStep
  simp only []
  split <;> exact allQ_bind (pubGood_nodeHashP _ _ _ _ _ _ _) fun _ => allQ_pure _
theorem pubGood_segLoop (w : WBytes) (index coord : Nat) : ∀ (stack : List (Digest × Nat)) (pending : Pending)
    (E ptr : Nat) (node : Digest), AllQueriesSatisfy (segLoop w index coord stack pending E ptr node) PubGood := by
  intro stack
  induction stack with
  | nil =>
      intro pending E ptr node
      rw [segLoop.eq_1]
      refine allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) ?_)
      exact allQ_bind (pubGood_pendingHash _ _ _ _ _) fun _ =>
        allQ_bind (pubGood_foldsP _ _ _ _ _ _ _) fun _ => allQ_pure _
  | cons top rest ih =>
      intro pending E ptr node
      obtain ⟨pn, Q⟩ := top
      rw [segLoop.eq_1]
      refine allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) ?_)
      exact allQ_bind (pubGood_pendingHash _ _ _ _ _) fun _ =>
        allQ_bind (pubGood_foldsP _ _ _ _ _ _ _) fun _ =>
          allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) (ih _ _ _ _))
theorem pubGood_ftsCoordP (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat) :
    AllQueriesSatisfy (ftsCoordP w index coord sel ptr) PubGood := by
  unfold ftsCoordP
  refine allQ_bind (pubGood_segLoop _ _ _ _ _ _ _ _) fun r0 => ?_
  rcases r0 with _ | ⟨n0, E0, p0, s0⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_segLoop _ _ _ _ _ _ _ _) fun r1 => ?_
  rcases r1 with _ | ⟨n1, E1, p1, s1⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_segLoop _ _ _ _ _ _ _ _) fun r2 => ?_
  rcases r2 with _ | ⟨n2, E2, p2, s2⟩
  · exact allQ_pure _
  exact allQ_ite _ (allQ_pure _) (allQ_pure _)
theorem pubGood_ftsP (w : WBytes) (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (ftsP w index chosen) PubGood := by
  unfold ftsP
  refine allQ_bind (allQ_foldlM _ _ (fun st c => ?_) _) fun st => ?_
  · rcases st with _ | ⟨roots, ptr⟩
    · exact allQ_pure _
    refine allQ_bind (pubGood_ftsCoordP _ _ _ _ _) fun r => ?_
    rcases r with _ | ⟨root, ptr'⟩ <;> exact allQ_pure _
  · rcases st with _ | ⟨roots, ptr⟩
    · exact allQ_pure _
    exact allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_forestPk _ _) fun _ => allQ_pure _)
theorem pubGood_layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (layerP w index lay digits) PubGood := by
  unfold layerP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chainPL _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHashP _ _ _ _ _ _ _) _
theorem pubGood_layersP (w : WBytes) (index : Nat) : ∀ n root,
    AllQueriesSatisfy (layersP w index n root) PubGood := by
  intro n
  induction n with
  | zero => intro root; exact allQ_pure _
  | succ n ih =>
      intro root
      unfold layersP
      refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_encoding _ _ _ _ _) fun d => ?_)
      split
      · exact allQ_bind (pubGood_layerP _ _ _ _) fun _ => ih _
      · exact allQ_pure _
theorem pubGood_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) PubGood := by
  rw [verifyP_eq_tail]
  refine allQ_bind ?_ fun r => ?_
  · unfold digestP; exact allQ_ite _ (allQ_pure _) (allQ_map _ (pubGood_digest _ _ _))
  · rcases r with _ | N
    · exact allQ_pure _
    unfold verifyTailP
    refine allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_ftsP _ _ _) fun r => ?_))
    rcases r with _ | root
    · exact allQ_pure _
    refine allQ_bind (pubGood_layersP _ _ _ _) fun r => ?_
    rcases r with _ | root <;> exact allQ_pure _
theorem pubGood_digestSearch (rho : Digest) (m : Message) : ∀ fuel counter,
    AllQueriesSatisfy (digestSearch rho m counter fuel) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact allQ_pure _
  | succ fuel ih =>
      intro counter
      unfold digestSearch
      exact allQ_bind (pubGood_digest _ _ _) fun _ => allQ_ite _ (allQ_pure _) (ih _)
theorem pubGood_counterSearch (lay : Layer) (tree leaf : Nat) (msg : Digest) : ∀ fuel counter,
    AllQueriesSatisfy (counterSearch lay tree leaf msg counter fuel) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact allQ_pure _
  | succ fuel ih =>
      intro counter
      unfold counterSearch
      refine allQ_bind (pubGood_encoding _ _ _ _ _) fun a => ?_
      split
      · exact ih _
      · exact allQ_pure _
theorem pubGood_recoverChild (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) : ∀ level node used,
    AllQueriesSatisfy (recoverChild index coord leaves values proof level node used) PubGood := by
  intro level
  induction level with
  | zero =>
      intro node used
      unfold recoverChild
      refine allQ_ite _ ?_ (allQ_bind (pubGood_ftsLeaf _ _ _ _) fun _ => allQ_pure _)
      split <;> exact allQ_pure _
  | succ level ih =>
      intro node used
      unfold recoverChild
      refine allQ_ite _ ?_ ?_
      · split <;> exact allQ_pure _
      · refine allQ_bind (ih _ _) fun r => ?_
        rcases r with _ | ⟨l, n⟩
        · exact allQ_pure _
        refine allQ_bind (ih _ _) fun r => ?_
        rcases r with _ | ⟨rr, n'⟩
        · exact allQ_pure _
        exact allQ_bind (pubGood_nodeHash _ _ _ _ _ _) fun _ => allQ_pure _
theorem pubGood_recoverFts (sig : Signature) (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (recoverFts sig index chosen) PubGood := by
  unfold recoverFts
  refine allQ_bind (allQ_foldlM _ _ (fun st c => ?_) _) fun st => ?_
  · rcases st with _ | ⟨roots, used⟩
    · exact allQ_pure _
    refine allQ_bind (pubGood_recoverChild _ _ _ _ _ _ _ _) fun r => ?_
    rcases r with _ | ⟨v, n⟩
    · exact allQ_pure _
    refine allQ_bind (allQ_foldlM _ _ (fun st j => ?_) _) fun r => ?_
    · rcases st with _ | ⟨v, u⟩
      · exact allQ_pure _
      simp only []
      split
      · exact allQ_bind (pubGood_nodeHash _ _ _ _ _ _) fun _ => allQ_pure _
      · exact allQ_pure _
    · rcases r with _ | ⟨root, n⟩ <;> exact allQ_pure _
  · rcases st with _ | ⟨roots, used⟩
    · exact allQ_pure _
    exact allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_forestPk _ _) fun _ => allQ_pure _)
theorem pubGood_recoverLayer (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (recoverLayer sig index lay digits) PubGood := by
  unfold recoverLayer
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_layChain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ => allQ_foldlM _ _ (fun _ _ => pubGood_nodeHash _ _ _ _ _ _) _
theorem pubGood_expandLayers (sig : Signature) (index : Nat) : ∀ n root,
    AllQueriesSatisfy (expandLayers sig index n root) PubGood := by
  intro n
  induction n with
  | zero => intro root; exact allQ_pure _
  | succ n ih =>
      intro root
      unfold expandLayers
      refine allQ_bind (pubGood_counterSearch _ _ _ _ _ _) fun r => ?_
      rcases r with _ | ⟨c, digits⟩
      · exact allQ_pure _
      refine allQ_bind (pubGood_recoverLayer _ _ _ _) fun _ => allQ_bind (ih _) fun r => ?_
      rcases r with _ | ⟨root', cs⟩ <;> exact allQ_pure _
theorem pubGood_expandN (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandN m pk σ) PubGood := by
  unfold expandN
  refine allQ_bind (pubGood_digestSearch _ _ _ _) fun r => ?_
  rcases r with _ | ⟨c, N⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_recoverFts _ _ _) fun r => ?_
  rcases r with _ | root
  · exact allQ_pure _
  refine allQ_bind (pubGood_expandLayers _ _ _ _) fun r => ?_
  rcases r with _ | ⟨root', cs⟩
  · exact allQ_pure _
  exact allQ_ite _ (allQ_pure _) (allQ_pure _)
theorem pubGood_expandB (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandB m pk σ) PubGood := allQ_map _ (pubGood_expandN m pk σ)
theorem allQ_mono {α : Type} {P Q : Spec.Domain → Prop} {p : M α} (h : AllQueriesSatisfy p P)
    (hPQ : ∀ q, P q → Q q) : AllQueriesSatisfy p Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
      rw [allQueriesSatisfy_query_bind_iff] at h ⊢
      exact ⟨hPQ _ h.1, fun u => ih u (h.2 u)⟩
theorem hashOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isHash :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.hashGood.1
theorem hashOnly_expandN (m : Message) (pk : Digest) (σ : Signature) : AllQueriesSatisfy (expandN m pk σ) isHash :=
  allQ_mono (pubGood_expandN m pk σ) fun _ h => h.hashGood.1
theorem hashOnly_expandB (m : Message) (pk : Digest) (σ : Signature) : AllQueriesSatisfy (expandB m pk σ) isHash :=
  allQ_mono (pubGood_expandB m pk σ) fun _ h => h.hashGood.1
theorem publicOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isPublic :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.1
theorem publicOnly_expandN (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandN m pk σ) isPublic := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.1
theorem hashOnly_honestProgramB (hk : AllQueriesSatisfy keygen isHash)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) isHash) (m : Message) :
    AllQueriesSatisfy (honestProgramB m) isHash := by
  unfold honestProgramB
  apply allQ_bind hk
  intro keys
  apply allQ_bind (hs _ _)
  intro sig
  rcases sig with _ | sig
  · exact allQ_pure _
  apply allQ_bind (hashOnly_expandB _ _ _)
  intro wb
  rcases wb with _ | wb
  · exact allQ_pure _
  exact hashOnly_verifyP _ _ _
theorem allQ_of_bound {α : Type} {P : Spec.Domain → Prop} {Post : α → Prop} {k : Nat} {p : M α}
    (h : Cost.Bound P Post k p) : AllQueriesSatisfy p P := by
  induction h with
  | pure a k _ => exact allQueriesSatisfy_pure _ _
  | query q f k hq _ ih =>
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hq, ih⟩
theorem goodQ_keygen : AllQueriesSatisfy keygen Cost.GoodQuery := allQ_of_bound Cost.bound_keygen
theorem goodQ_sign (cache : SigGolfCandidate.T3.Cache) (m : Message) : AllQueriesSatisfy (sign cache m) Cost.GoodQuery :=
  allQ_of_bound (Cost.bound_sign cache m)
theorem goodQ_expand (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expand m pk σ) Cost.GoodQuery := allQ_of_bound (Cost.bound_expand m pk σ)
theorem goodQ_verify (m : Message) (pk : Digest) (w : Witness) :
    AllQueriesSatisfy (verify m pk w) Cost.GoodQuery := allQ_of_bound (Cost.bound_verify m pk w)
theorem goodQ_expandN (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandN m pk σ) Cost.GoodQuery := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.2
theorem goodQ_verifyP (m : Message) (pk : Digest) (w : WBytes) :
    AllQueriesSatisfy (verifyP m pk w) Cost.GoodQuery := allQ_mono (pubGood_verifyP m pk w) fun _ h => h.2
theorem privateInput_positive_aligned (sk : BitVec 256) (c : Coordinate) :
    0 < (privateInput sk c).length ∧ (privateInput sk c).length % 64 = 0 := by
  have h1 := Cost.private_realization_weight sk c
  refine ⟨?_, ?_⟩
  · have hw : 1 ≤ Cost.weight (.inr c) := by rcases c with t | m | r <;> simp [Cost.weight]
    omega
  · unfold privateInput; exact Cost.pad64_aligned _
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
def block4 (a b c d : Digest) : HashInput :=
  bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c ++ bytesLE 16 d
@[simp] theorem block4_length (a b c d : Digest) : (block4 a b c d).length = 64 := by
  simp [block4, bytesLE_length]
@[simp] theorem pad64_block4 (a b c d : Digest) : pad64 (block4 a b c d) = block4 a b c d := by
  simp [pad64]
theorem block4_injective {a b c d a' b' c' d' : Digest}
    (h : block4 a b c d = block4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  unfold block4 at h
  obtain ⟨h, hd⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨ha, hb⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective ha, bytesLE_injective hb, bytesLE_injective hc, bytesLE_injective hd⟩
@[simp] theorem block4_eq_iff {a b c d a' b' c' d' : Digest} :
    block4 a b c d = block4 a' b' c' d' ↔
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · exact block4_injective
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl
private theorem bytesLE_zero : bytesLE 16 (0 : Digest) = zero16 := by decide
def ftsLeafInputP (index coord leaf : Nat) (pad0 secret pad1 : Digest) : HashInput :=
  block4 pad0 (header 9 coord index 0 leaf) secret pad1
def nodeInputP (tag lay tree heap : Nat) (left pad right : Digest) : HashInput :=
  block4 left (nodeTweak tag lay tree heap) pad right
theorem ftsLeafP_eq_shortHash (index coord leaf : Nat) (pad0 secret pad1 : Digest) :
    ftsLeafP index coord leaf pad0 secret pad1 = shortHash (ftsLeafInputP index coord leaf pad0 secret pad1) := rfl
/-- Replace the high word of a marked (byte0 >= 128) tweak by `hp`; unmarked tweaks are kept. For marked tweaks the
high word is ignored by `canonicalHeader`, so the verifier may leave it to the witness. -/
def withHigh (t : BitVec 128) (hp : BitVec 64) : BitVec 128 :=
  if 128 ≤ t.toNat % 256 then hp ++ t.extractLsb' 0 64 else t
theorem withHigh_zero_of_high {t : BitVec 128} (h : t.extractLsb' 64 64 = 0) : withHigh t 0 = t := by
  unfold withHigh
  split
  · rw [show (0 : BitVec 64) = t.extractLsb' 64 64 from h.symm]; exact BitVec.extractLsb'_append_extractLsb'
  · rfl
theorem withHigh_nodeTweak_zero (tag lay tree heap : Nat) :
    withHigh (nodeTweak tag lay tree heap) 0 = nodeTweak tag lay tree heap := by
  by_cases htop : tag = 3 ∧ lay = 0
  · obtain ⟨rfl, rfl⟩ := htop
    apply withHigh_zero_of_high
    rw [nodeTweak_top]; exact BitVec.extractLsb'_append_eq_left
  unfold withHigh
  split
  · rename_i hm
    have hk := nodeTweak_marker tag lay tree heap
    unfold tweakMarker at hk
    rw [hk, if_neg htop] at hm
    split_ifs at hm with hf
    · obtain ⟨rfl, h4, h13, hn⟩ := hf
      rw [nodeTweak_ftsN h4 h13 tree hn, append64_low]
      rfl
    · omega
  · rfl
/-- FTS node input with a witness-supplied high tweak word (ignored for marked tweaks). -/
def nodeInputPH (tag lay tree heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) : HashInput :=
  block4 left (withHigh (nodeTweak tag lay tree heap) hp) pad right
theorem nodeInputPH_zero (tag lay tree heap : Nat) (left pad right : Digest) :
    nodeInputPH tag lay tree heap left 0 pad right = nodeInputP tag lay tree heap left pad right := by
  unfold nodeInputPH nodeInputP; rw [withHigh_nodeTweak_zero]
@[simp] theorem pad64_nodeInputPH (tag lay tree heap : Nat) (left : Digest) (hp : BitVec 64) (pad right : Digest) :
    pad64 (nodeInputPH tag lay tree heap left hp pad right) = nodeInputPH tag lay tree heap left hp pad right :=
  pad64_block4 _ _ _ _
/-- C4: the padded node hash keeps the half `nodeHalfHigh` (high only for an even top heap). -/
theorem nodeHashP_eq_projHash (tag lay tree heap : Nat) (left pad right : Digest) :
    nodeHashP tag lay tree heap left pad right =
      projHash (nodeHalfHigh tag lay heap) (nodeInputP tag lay tree heap left pad right) := rfl
theorem nodeHashP_eq_shortHash {tag lay heap : Nat} (h : nodeHalfHigh tag lay heap = false) (tree : Nat)
    (left pad right : Digest) :
    nodeHashP tag lay tree heap left pad right = shortHash (nodeInputP tag lay tree heap left pad right) := by
  rw [nodeHashP_eq_projHash, h, projHash_false]
theorem ftsLeaf_eq_shortHash (index coord leaf : Nat) (secret : Digest) :
    ftsLeaf index coord leaf secret = shortHash (ftsLeafInputP index coord leaf 0 secret 0) := by
  simp only [ftsLeaf, ftsLeafInputP, block4, bytesLE_zero]
/-- C4: the node hash keeps the half `nodeHalfHigh` (high only for an even top heap). -/
theorem nodeHash_eq_projHash (tag lay tree heap : Nat) (left right : Digest) :
    nodeHash tag lay tree heap left right =
      projHash (nodeHalfHigh tag lay heap) (nodeInputP tag lay tree heap left 0 right) := by
  simp only [nodeHash, nodeInputP, block4, bytesLE_zero]
theorem nodeHash_eq_shortHash {tag lay heap : Nat} (h : nodeHalfHigh tag lay heap = false) (tree : Nat)
    (left right : Digest) :
    nodeHash tag lay tree heap left right = shortHash (nodeInputP tag lay tree heap left 0 right) := by
  rw [nodeHash_eq_projHash, h, projHash_false]
theorem chainInputP_eq_block4 (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) :
    chainInputP lay tree leaf i step pad0 pad1 headerPad value =
      block4 pad0 (chainHeaderP lay tree leaf i step headerPad) pad1 value := rfl
theorem chainInput_eq_source (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    chainInput lay tree leaf i step value = chainInputP lay tree leaf i step 0 0
      ((chainHeader lay tree leaf i step).extractLsb' 64 64) value := by
  simp only [chainInput, chainInputP, bytesLE_zero, chainHeaderP_source]
theorem chainInput_eq_zero (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    chainInput lay tree leaf i step value = chainInputP lay tree leaf i step 0 0 0 value := by
  rw [chainInput_eq_source, T3M.chainHeader_high_zero _ _ _ _ _ ht hl hi hs]
@[simp] theorem pad64_ftsLeafInputP (index coord leaf : Nat) (pad0 secret pad1 : Digest) :
    pad64 (ftsLeafInputP index coord leaf pad0 secret pad1) = ftsLeafInputP index coord leaf pad0 secret pad1 :=
  pad64_block4 _ _ _ _
@[simp] theorem pad64_nodeInputP (tag lay tree heap : Nat) (left pad right : Digest) :
    pad64 (nodeInputP tag lay tree heap left pad right) = nodeInputP tag lay tree heap left pad right :=
  pad64_block4 _ _ _ _
@[simp] theorem pad64_chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) :
    pad64 (chainInputP lay tree leaf i step pad0 pad1 headerPad value) =
      chainInputP lay tree leaf i step pad0 pad1 headerPad value :=
  pad64_block4 _ _ _ _
theorem ftsLeafInputP_fields {index coord leaf index' coord' leaf' : Nat}
    {pad0 secret pad1 pad0' secret' pad1' : Digest}
    (h : ftsLeafInputP index coord leaf pad0 secret pad1 =
      ftsLeafInputP index' coord' leaf' pad0' secret' pad1') :
    pad0 = pad0' ∧ header 9 coord index 0 leaf = header 9 coord' index' 0 leaf' ∧
      secret = secret' ∧ pad1 = pad1' := block4_injective h
theorem nodeInputP_fields {tag lay tree heap tag' lay' tree' heap' : Nat}
    {left pad right left' pad' right' : Digest}
    (h : nodeInputP tag lay tree heap left pad right = nodeInputP tag' lay' tree' heap' left' pad' right') :
    left = left' ∧ nodeTweak tag lay tree heap = nodeTweak tag' lay' tree' heap' ∧
      pad = pad' ∧ right = right' := block4_injective h
theorem chainInputP_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value pad0' pad1' value' : Digest}
    {headerPad headerPad' : BitVec 64}
    (h : chainInputP lay tree leaf i step pad0 pad1 headerPad value =
      chainInputP lay' tree' leaf' i' step' pad0' pad1' headerPad' value') :
    pad0 = pad0' ∧ chainHeaderP lay tree leaf i step headerPad =
      chainHeaderP lay' tree' leaf' i' step' headerPad' ∧ pad1 = pad1' ∧ value = value' :=
  block4_injective h
theorem chainInputP_headerPad_eq {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value pad0' pad1' value' : Digest} {headerPad headerPad' : BitVec 64}
    (h : chainInputP lay tree leaf i step pad0 pad1 headerPad value =
      chainInputP lay' tree' leaf' i' step' pad0' pad1' headerPad' value') :
    headerPad = headerPad' := by
  have hh := congrArg (fun x : Digest => x.extractLsb' 64 64) (chainInputP_fields h).2.1
  simpa only [chainHeaderP, BitVec.extractLsb'_append_eq_left] using hh
private theorem low64_toNat_eq (x y : Digest)
    (h : x.extractLsb' 0 64 = y.extractLsb' 0 64) :
    x.toNat % 2^64 = y.toNat % 2^64 := by
  have hn := congrArg BitVec.toNat h
  simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] using hn
private theorem marker_of_low64_eq (x y : Digest)
    (h : x.extractLsb' 0 64 = y.extractLsb' 0 64) :
    x.toNat / 2^56 % 256 = y.toNat / 2^56 % 256 := by
  have := low64_toNat_eq x y h
  omega
private theorem firstByte_of_low64_eq (x y : Digest)
    (h : x.extractLsb' 0 64 = y.extractLsb' 0 64) :
    x.toNat % 256 = y.toNat % 256 := by
  have := low64_toNat_eq x y h
  omega
theorem chainHeaderP_marker (lay : Layer) (tree leaf i step : Nat) (headerPad : BitVec 64) :
    (chainHeaderP lay tree leaf i step headerPad).toNat / 2^56 % 256 = 193 :=
  (marker_of_low64_eq _ _ BitVec.extractLsb'_append_eq_right).trans
    (T3.chainHeader_marker lay tree leaf i step)
theorem chainHeaderP_firstByte (lay : Layer) (tree leaf i step : Nat) (headerPad : BitVec 64) :
    128 ≤ (chainHeaderP lay tree leaf i step headerPad).toNat % 256 := by
  rw [firstByte_of_low64_eq (chainHeaderP lay tree leaf i step headerPad)
    (chainHeader lay tree leaf i step) BitVec.extractLsb'_append_eq_right]
  exact T3.chainHeader_firstByte lay tree leaf i step
theorem chainHeaderP_ne_header (lay : Layer) (tree leaf i step : Nat) (headerPad : BitVec 64)
    (tag roleLay roleTree position index : Nat) :
    chainHeaderP lay tree leaf i step headerPad ≠ header tag roleLay roleTree position index := by
  intro he
  have hc := chainHeaderP_firstByte lay tree leaf i step headerPad
  rw [he, T3.header_firstByte] at hc
  omega
theorem ftsLeafInputP_eq_canonical {index coord leaf index' coord' leaf' : Nat}
    {pad0 secret pad1 secret' : Digest}
    (h : ftsLeafInputP index coord leaf pad0 secret pad1 =
      zero16 ++ bytesLE 16 (header 9 coord' index' 0 leaf') ++ bytesLE 16 secret' ++ zero16) :
    pad0 = 0 ∧ header 9 coord index 0 leaf = header 9 coord' index' 0 leaf' ∧
      secret = secret' ∧ pad1 = 0 := by
  apply ftsLeafInputP_fields
  simpa only [ftsLeafInputP, block4, bytesLE_zero] using h
theorem nodeInputP_eq_canonical {tag lay tree heap tag' lay' tree' heap' : Nat}
    {left pad right left' right' : Digest}
    (h : nodeInputP tag lay tree heap left pad right = bytesLE 16 left' ++
      bytesLE 16 (nodeTweak tag' lay' tree' heap') ++ zero16 ++ bytesLE 16 right') :
    left = left' ∧ nodeTweak tag lay tree heap = nodeTweak tag' lay' tree' heap' ∧
      pad = 0 ∧ right = right' := by
  apply nodeInputP_fields
  simpa only [nodeInputP, block4, bytesLE_zero] using h
theorem chainInputP_eq_canonical {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value value' : Digest} {headerPad : BitVec 64}
    (h : chainInputP lay tree leaf i step pad0 pad1 headerPad value = chainInput lay' tree' leaf' i' step' value') :
    pad0 = 0 ∧ chainHeaderP lay tree leaf i step headerPad =
      chainHeader lay' tree' leaf' i' step' ∧ pad1 = 0 ∧ value = value' := by
  simpa only [chainHeaderP_source] using
    chainInputP_fields (h.trans (chainInput_eq_source _ _ _ _ _ _))
theorem chainInputP_headerPad_canonical {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value value' : Digest} {headerPad : BitVec 64}
    (h : chainInputP lay tree leaf i step pad0 pad1 headerPad value = chainInput lay' tree' leaf' i' step' value') :
    headerPad = (chainHeader lay' tree' leaf' i' step').extractLsb' 64 64 :=
  chainInputP_headerPad_eq (h.trans (chainInput_eq_source _ _ _ _ _ _))
theorem ftsLeafInputP_injective {index coord leaf index' coord' leaf' : Nat}
    {pad0 secret pad1 pad0' secret' pad1' : Digest}
    (hc : coord < 256) (hi : index < 2^40) (hl : leaf < 2^32)
    (hc' : coord' < 256) (hi' : index' < 2^40) (hl' : leaf' < 2^32)
    (h : ftsLeafInputP index coord leaf pad0 secret pad1 =
      ftsLeafInputP index' coord' leaf' pad0' secret' pad1') :
    index = index' ∧ coord = coord' ∧ leaf = leaf' ∧ pad0 = pad0' ∧ secret = secret' ∧ pad1 = pad1' := by
  obtain ⟨hp0, hh, hs, hp1⟩ := ftsLeafInputP_fields h
  obtain ⟨_, hc, hi, _, hl⟩ := header_injective (by decide) hc hi (by decide) hl
    (by decide) hc' hi' (by decide) hl' hh
  exact ⟨hi, hc, hl, hp0, hs, hp1⟩
theorem chainInputP_injective {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value pad0' pad1' value' : Digest}
    {headerPad headerPad' : BitVec 64}
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8)
    (ht' : tree' < 2^31) (hl' : leaf' < 4096) (hi' : i' < 64) (hs' : step' < 8)
    (h : chainInputP lay tree leaf i step pad0 pad1 headerPad value =
      chainInputP lay' tree' leaf' i' step' pad0' pad1' headerPad' value') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ i = i' ∧ step = step' ∧
      pad0 = pad0' ∧ pad1 = pad1' ∧ value = value' ∧ headerPad = headerPad' := by
  obtain ⟨hp0, he, hp1, hv⟩ := chainInputP_fields h
  have hlo := congrArg (fun x : Digest => x.extractLsb' 0 64) he
  simp only [chainHeaderP, BitVec.extractLsb'_append_eq_right] at hlo
  obtain ⟨hla, htree, hleaf, hindex, hstep⟩ := chainHeader_low_injective
    ht hl hi hs ht' hl' hi' hs' hlo
  exact ⟨hla, htree, hleaf, hindex, hstep, hp0, hp1, hv, chainInputP_headerPad_eq h⟩
end SigGolfCandidate.T3M.SecurityInputs
namespace SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec SigGolfCandidate.T3
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def queried {α : Type} (answers : Answers) (program : M α) : List Spec.Domain :=
  ((simulateQ answers.withLogging program).run).2.map Sigma.fst
@[simp] theorem queried_pure {α : Type} (answers : Answers) (value : α) :
    queried answers (pure value) = [] := rfl
@[simp] theorem queried_query_bind {α : Type} (answers : Answers)
    (q : Spec.Domain) (next : Spec.Range q → M α) :
    queried answers (liftM (Spec.query q) >>= next) =
      q :: queried answers (next (answers q)) := rfl
theorem queried_bind {α β : Type} (answers : Answers) (program : M α) (next : α → M β) :
    queried answers (program >>= next) = queried answers program ++
      queried answers (next (evalWithAnswerFn answers program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind q rest ih =>
      rw [bind_assoc, queried_query_bind, queried_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn answers (liftM (Spec.query q)) = answers q from
          simulateQ_spec_query answers q, List.cons_append]
@[simp] theorem queried_shortHash (answers : Answers) (input : HashInput) :
    queried answers (shortHash input) = [.inl (.inr (pad64 input))] := rfl
theorem eval_shortHash (answers : Answers) (input : HashInput) :
    evalWithAnswerFn answers (shortHash input) =
      (answers (.inl (.inr (pad64 input)))).extractLsb' 0 128 := rfl
@[simp] theorem queried_projHash (answers : Answers) (high : Bool) (input : HashInput) :
    queried answers (projHash high input) = [.inl (.inr (pad64 input))] := rfl
theorem eval_projHash (answers : Answers) (high : Bool) (input : HashInput) :
    evalWithAnswerFn answers (projHash high input) = projHalf high (answers (.inl (.inr (pad64 input)))) := rfl
def hashPath (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) : M Digest :=
  (List.range count).foldlM (fun value step => shortHash (input step value)) initial
def pathValue (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (count : Nat) : Digest :=
  evalWithAnswerFn answers (hashPath input count initial)
def pathInput (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) : HashInput := input step (pathValue answers input initial step)
theorem hashPath_succ (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPath input (count + 1) initial =
      (hashPath input count initial >>= fun value => shortHash (input count value)) := by
  simp [hashPath, List.range_succ, List.foldlM_append]
@[simp] theorem pathValue_zero (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) : pathValue answers input initial 0 = initial := rfl
theorem pathValue_succ (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) :
    pathValue answers input initial (step + 1) =
      evalWithAnswerFn answers (shortHash (pathInput answers input initial step)) := by
  simp only [pathValue, hashPath_succ, evalWithAnswerFn_bind, pathInput]
theorem pathInput_queried (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (count step : Nat) (hstep : step < count) :
    .inl (.inr (pad64 (pathInput answers input initial step))) ∈
      queried answers (hashPath input count initial) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [hashPath_succ, queried_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
      · exact List.mem_append_left _ (ih hlt)
      · apply List.mem_append_right
        simp only [queried_shortHash, List.mem_singleton]
        rfl
def HashHit (answers : Answers) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧
    (answers (.inl (.inr actual))).extractLsb' 0 128 =
      (answers (.inl (.inr honest))).extractLsb' 0 128
theorem hashPath_extract (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValue answers input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count → Good step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers input initial step))) ∈
          queried answers (hashPath input count initial) ∧
        HashHit answers (pad64 (honestInput step)) (pad64 (pathInput answers input initial step)) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInput answers input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hhit⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact hgood
        · exact Or.inr ⟨step, by omega, pathInput_queried answers input initial _ _ (by omega), hhit⟩
      · right
        refine ⟨count, by omega, pathInput_queried answers input initial _ _ (by omega), heq, ?_⟩
        rw [pathValue_succ] at reaches
        exact reaches.trans (reference count (by omega)).symm
theorem foldlM_range'_eq_hashPath (input : Nat → Digest → HashInput)
    (start count : Nat) (initial : Digest) :
    (List.range' start count).foldlM (fun value step => shortHash (input step value)) initial =
      hashPath (fun step value => input (start + step) value) count initial := by
  rw [List.range'_eq_map_range, List.foldlM_map]
  rfl
theorem chainP_eq_hashPath (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (initial : Digest) :
    chainP lay tree leaf i start count pad0 pad1 headerPad initial =
      hashPath (fun step value => chainInputP lay tree leaf i (start + step) pad0 pad1 headerPad value)
        count initial := by
  exact foldlM_range'_eq_hashPath (fun step value => chainInputP lay tree leaf i step pad0 pad1 headerPad value)
    start count initial
theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp
theorem foldlM_finRange_eq_hashPath (input : Nat → Digest → HashInput)
    (count : Nat) (initial : Digest) :
    (List.finRange count).foldlM (fun value j => shortHash (input j.val value)) initial =
      hashPath input count initial := by
  unfold hashPath
  rw [← map_val_finRange count, List.foldlM_map]
end SigGolfCandidate.T3M.SecurityExtraction
namespace SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs
open Correctness (Answers TreeLevels treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem ftsLeafP_extract (answers : Answers) (index coord leaf : Nat)
    (pad0 secret pad1 honestSecret : Digest)
    (reaches : evalWithAnswerFn answers (ftsLeafP index coord leaf pad0 secret pad1) =
      evalWithAnswerFn answers (ftsLeaf index coord leaf honestSecret)) :
    (pad0 = 0 ∧ secret = honestSecret ∧ pad1 = 0) ∨
      (HashHit answers (ftsLeafInputP index coord leaf 0 honestSecret 0)
        (ftsLeafInputP index coord leaf pad0 secret pad1) ∧
      .inl (.inr (ftsLeafInputP index coord leaf pad0 secret pad1)) ∈
        queried answers (ftsLeafP index coord leaf pad0 secret pad1)) := by
  by_cases heq : ftsLeafInputP index coord leaf pad0 secret pad1 =
      ftsLeafInputP index coord leaf 0 honestSecret 0
  · obtain ⟨h0, _, hs, h1⟩ := ftsLeafInputP_fields heq
    exact Or.inl ⟨h0, hs, h1⟩
  · right
    constructor
    · refine ⟨heq, ?_⟩
      rw [ftsLeafP_eq_shortHash, ftsLeaf_eq_shortHash, eval_shortHash, eval_shortHash,
        pad64_ftsLeafInputP, pad64_ftsLeafInputP] at reaches
      exact reaches
    · rw [ftsLeafP_eq_shortHash, queried_shortHash, pad64_ftsLeafInputP]
      exact List.mem_singleton_self _
theorem nodeHashP_extract (answers : Answers) (tag lay tree heap : Nat)
    (hlow : nodeHalfHigh tag lay heap = false) (left pad right honestLeft honestRight : Digest)
    (reaches : evalWithAnswerFn answers (nodeHashP tag lay tree heap left pad right) =
      evalWithAnswerFn answers (nodeHash tag lay tree heap honestLeft honestRight)) :
    (left = honestLeft ∧ pad = 0 ∧ right = honestRight) ∨
      (HashHit answers (nodeInputP tag lay tree heap honestLeft 0 honestRight)
        (nodeInputP tag lay tree heap left pad right) ∧
      .inl (.inr (nodeInputP tag lay tree heap left pad right)) ∈
        queried answers (nodeHashP tag lay tree heap left pad right)) := by
  by_cases heq : nodeInputP tag lay tree heap left pad right =
      nodeInputP tag lay tree heap honestLeft 0 honestRight
  · obtain ⟨hl, _, hp, hr⟩ := nodeInputP_fields heq
    exact Or.inl ⟨hl, hp, hr⟩
  · right
    constructor
    · refine ⟨heq, ?_⟩
      rw [nodeHashP_eq_shortHash hlow, nodeHash_eq_shortHash hlow, eval_shortHash, eval_shortHash,
        pad64_nodeInputP, pad64_nodeInputP] at reaches
      exact reaches
    · rw [nodeHashP_eq_projHash, queried_projHash, pad64_nodeInputP]
      exact List.mem_singleton_self _
def honestChainValue (answers : Answers) (lay : Layer) (tree leaf i : Nat)
    (seed : Digest) (step : Nat) : Digest :=
  evalWithAnswerFn answers (chain lay tree leaf i 0 step seed)
theorem honestChainValue_succ (answers : Answers) (lay : Layer) (tree leaf i : Nat)
    (seed : Digest) (step : Nat) :
    evalWithAnswerFn answers (shortHash (chainInput lay tree leaf i step
      (honestChainValue answers lay tree leaf i seed step))) =
        honestChainValue answers lay tree leaf i seed (step + 1) := by
  unfold honestChainValue
  rw [Correctness.eval_chain_add]
  simp [chain]
def chainPathInput (lay : Layer) (tree leaf i start : Nat) (pad0 pad1 : Digest) (headerPad : BitVec 64) :
    Nat → Digest → HashInput := fun step value =>
  chainInputP lay tree leaf i (start + step) pad0 pad1 headerPad value
theorem chainPath_extract (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : pathValue answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value count =
      honestChainValue answers lay tree leaf i seed (start + count)) :
    (value = honestChainValue answers lay tree leaf i seed start ∧
      (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
          queried answers (hashPath (chainPathInput lay tree leaf i start pad0 pad1 headerPad) count value) ∧
        HashHit answers
          (pad64 (chainInput lay tree leaf i (start + step)
            (honestChainValue answers lay tree leaf i seed (start + step))))
          (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) := by
  have h := hashPath_extract answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad)
    (fun step => chainInput lay tree leaf i (start + step)
      (honestChainValue answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValue answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) value count
    (fun step _ => by simpa only [Nat.add_assoc] using
      honestChainValue_succ answers lay tree leaf i seed (start + step))
    (fun step hstep current heq => by
      have hs : start + step < 8 := by rcases hsteps with hz | hb <;> omega
      simp only [chainPathInput, chainInput_eq_zero _ _ _ _ _ _ ht hl hi hs,
        pad64_chainInputP] at heq
      have hhp := chainInputP_headerPad_eq heq
      obtain ⟨hp0, _, hp1, hv⟩ := chainInputP_fields heq
      exact ⟨hv, hp0, hp1, hhp⟩) reaches
  rcases h with ⟨hvalue, hpads⟩ | hhit
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => hpads 0 hcount⟩
  · exact Or.inr hhit
theorem chainP_extract (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : evalWithAnswerFn answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) =
      honestChainValue answers lay tree leaf i seed (start + count)) :
    (value = honestChainValue answers lay tree leaf i seed start ∧
      (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
          queried answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) ∧
        HashHit answers
          (pad64 (chainInput lay tree leaf i (start + step)
            (honestChainValue answers lay tree leaf i seed (start + step))))
          (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) := by
  rw [chainP_eq_hashPath] at reaches ⊢
  exact chainPath_extract answers lay tree leaf i start count pad0 pad1 headerPad value seed ht hl hi hsteps reaches
def merkleInput (tag lay tree height leaf : Nat) (path pads : Nat → Digest)
    (step : Nat) (value : Digest) : HashInput :=
  let pair := if leaf / 2^step % 2 = 0 then (value, path step) else (path step, value)
  nodeInputP tag lay tree (2^(height-step-1) + leaf/2^(step+1)) pair.1 (pads step) pair.2
theorem merkleInput_parse (tag lay tree height leaf step : Nat)
    (path pads honestPath : Nat → Digest) (current target : Digest)
    (heq : pad64 (merkleInput tag lay tree height leaf path pads step current) =
      pad64 (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step target)) :
    current = target ∧ path step = honestPath step ∧ pads step = 0 := by
  unfold merkleInput at heq
  split at heq <;> simp only [pad64_nodeInputP] at heq
  · obtain ⟨hc, _, hp, hs⟩ := nodeInputP_fields heq
    exact ⟨hc, hs, hp⟩
  · obtain ⟨hs, _, hp, hc⟩ := nodeInputP_fields heq
    exact ⟨hc, hs, hp⟩
theorem merklePath_extract (answers : Answers) (tag lay tree height leaf count : Nat)
    (path pads honestPath target : Nat → Digest) (value : Digest)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash
        (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step))) =
          target (step + 1))
    (reaches : pathValue answers (merkleInput tag lay tree height leaf path pads) value count = target count) :
    (value = target 0 ∧ ∀ step, step < count → path step = honestPath step ∧ pads step = 0) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers (merkleInput tag lay tree height leaf path pads) value step))) ∈
          queried answers (hashPath (merkleInput tag lay tree height leaf path pads) count value) ∧
        HashHit answers
          (pad64 (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step)))
          (pad64 (pathInput answers (merkleInput tag lay tree height leaf path pads) value step)) :=
  hashPath_extract answers _ _ target _ value count reference
    (fun step _ current => merkleInput_parse tag lay tree height leaf step path pads honestPath current (target step)) reaches
def merkleInputH (tag lay tree height leaf : Nat) (path pads : Nat → Digest) (hpads : Nat → BitVec 64)
    (step : Nat) (value : Digest) : HashInput :=
  let pair := if leaf / 2^step % 2 = 0 then (value, path step) else (path step, value)
  nodeInputPH tag lay tree (2^(height-step-1) + leaf/2^(step+1)) pair.1 (hpads step) (pads step) pair.2
/-- The witness high word at `step` is harmless: it is ignored (unmarked tweak) or equal to the honest 0. -/
def HighOK (tag lay tree height leaf : Nat) (hpads : Nat → BitVec 64) (step : Nat) : Prop :=
  withHigh (nodeTweak tag lay tree (2^(height-step-1) + leaf/2^(step+1))) (hpads step) =
    nodeTweak tag lay tree (2^(height-step-1) + leaf/2^(step+1))
theorem merkleInputH_ok (tag lay tree height leaf : Nat) (path pads : Nat → Digest) (hpads : Nat → BitVec 64)
    (step : Nat) (value : Digest) (h : HighOK tag lay tree height leaf hpads step) :
    merkleInputH tag lay tree height leaf path pads hpads step value =
      merkleInput tag lay tree height leaf path pads step value := by
  unfold merkleInputH merkleInput nodeInputPH nodeInputP
  unfold HighOK at h
  dsimp only
  rw [h]
theorem merkleInputH_zero (tag lay tree height leaf : Nat) (path pads : Nat → Digest) :
    merkleInputH tag lay tree height leaf path pads (fun _ => 0) =
      merkleInput tag lay tree height leaf path pads := by
  funext step value
  exact merkleInputH_ok _ _ _ _ _ _ _ _ _ _ (withHigh_nodeTweak_zero _ _ _ _)
theorem merkleInputH_parse (tag lay tree height leaf step : Nat)
    (path pads honestPath : Nat → Digest) (hpads : Nat → BitVec 64) (current target : Digest)
    (heq : pad64 (merkleInputH tag lay tree height leaf path pads hpads step current) =
      pad64 (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step target)) :
    current = target ∧ path step = honestPath step ∧ pads step = 0 ∧ HighOK tag lay tree height leaf hpads step := by
  unfold merkleInputH merkleInput at heq
  unfold HighOK
  split at heq <;> simp only [pad64_nodeInputPH, pad64_nodeInputP, nodeInputPH, nodeInputP, pad64_block4] at heq
  · obtain ⟨hc, hh, hp, hs⟩ := block4_injective heq
    exact ⟨hc, hs, hp, hh⟩
  · obtain ⟨hs, hh, hp, hc⟩ := block4_injective heq
    exact ⟨hc, hs, hp, hh⟩
theorem merkleHPath_extract (answers : Answers) (tag lay tree height leaf count : Nat)
    (path pads honestPath target : Nat → Digest) (hpads : Nat → BitVec 64) (value : Digest)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash
        (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step))) =
          target (step + 1))
    (reaches : pathValue answers (merkleInputH tag lay tree height leaf path pads hpads) value count = target count) :
    (value = target 0 ∧ ∀ step, step < count → path step = honestPath step ∧ pads step = 0 ∧
        HighOK tag lay tree height leaf hpads step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers (merkleInputH tag lay tree height leaf path pads hpads) value step))) ∈
          queried answers (hashPath (merkleInputH tag lay tree height leaf path pads hpads) count value) ∧
        HashHit answers
          (pad64 (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step)))
          (pad64 (pathInput answers (merkleInputH tag lay tree height leaf path pads hpads) value step)) :=
  hashPath_extract answers _ _ target _ value count reference
    (fun step _ current => merkleInputH_parse tag lay tree height leaf step path pads honestPath hpads current
      (target step)) reaches
theorem merkleInput_tree_reference (answers : Answers) (tag lay tree height leaf : Nat)
    (hlow : ¬ (tag = 3 ∧ lay = 0)) (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves height levels)
    (hleaf : leaf < 2^height) (step : Nat) (hstep : step < height) :
    evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2^j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2^step)))) =
      treeValue levels (step + 1) (leaf / 2^(step + 1)) := by
  unfold merkleInput
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  rw [← nodeHash_eq_shortHash (nodeHalfHigh_of_ne hlow _)]
  have hparent : leaf / 2^(step + 1) < 2^(height - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2^(step + 1)) hparent
  simpa only [treeValue, Nat.sub_sub] using hp.symm
theorem merkleInput_tree_reference_prefix (answers : Answers) (tag lay tree height leaf count : Nat)
    (hlow : ¬ (tag = 3 ∧ lay = 0)) (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves height levels)
    (hleaf : leaf < 2^height) (hcount : count ≤ height) :
    ∀ step, step < count → evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2^j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2^step)))) =
      treeValue levels (step + 1) (leaf / 2^(step + 1)) := by
  intro step hstep
  exact merkleInput_tree_reference answers tag lay tree height leaf hlow levels leaves htree hleaf step
    (lt_of_lt_of_le hstep hcount)
end SigGolfCandidate.T3M.SecurityExtraction
end
-- ==== merged from Rv_Steps ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
inductive Steps (image : Image) : MachineState → Nat → Nat → MachineState → Prop where
  | refl (s : MachineState) : Steps image s 0 0 s
  | step {s t u : MachineState} {i : Instruction} {k c : Nat}
      (hf : fetch image s = some i) (hs : ordinaryStep s i = some t)
      (tail : Steps image t k c u) :
      Steps image s (k + 1) (instructionCycles i + c) u
theorem Steps.of_eq {image : Image} {s t : MachineState} {k c k' c' : Nat}
    (h : Steps image s k c t) (hk : k = k') (hc : c = c') : Steps image s k' c' t := by
  subst hk hc; exact h
theorem Steps.trans {image : Image} {s t u : MachineState} {k₁ c₁ k₂ c₂ : Nat}
    (h₁ : Steps image s k₁ c₁ t) (h₂ : Steps image t k₂ c₂ u) :
    Steps image s (k₁ + k₂) (c₁ + c₂) u := by
  induction h₁ with
  | refl => simpa using h₂
  | @step s t u i k c hf hs _ ih =>
    have := Steps.step hf hs (ih h₂)
    exact Steps.of_eq this (by omega) (by omega)
@[simp] theorem Execution.charge_zero (e : Execution) : e.charge 0 0 0 = e := by
  cases e; simp [Execution.charge]
@[simp] theorem Execution.charge_charge (e : Execution) (a b c a' b' c' : Nat) :
    (e.charge a b c).charge a' b' c' = e.charge (a' + a) (b' + b) (c' + c) := by
  cases e; simp [Execution.charge, Nat.add_assoc]
@[simp] theorem Execution.charge_exit (e : Execution) (a b c : Nat) : (e.charge a b c).exit = e.exit := rfl
@[simp] theorem Execution.charge_state (e : Execution) (a b c : Nat) : (e.charge a b c).state = e.state := rfl
@[simp] theorem Execution.charge_cycles (e : Execution) (a b c : Nat) :
    (e.charge a b c).cycles = a + e.cycles := rfl
@[simp] theorem Execution.charge_hashCalls (e : Execution) (a b c : Nat) :
    (e.charge a b c).hashCalls = b + e.hashCalls := rfl
@[simp] theorem Execution.charge_hashCompressions (e : Execution) (a b c : Nat) :
    (e.charge a b c).hashCompressions = c + e.hashCompressions := rfl
theorem ordinaryStep_ne_ecall {s t : MachineState} {i : Instruction}
    (h : ordinaryStep s i = some t) : i ≠ .base .ECALL := by
  rintro rfl; simp [ordinaryStep] at h
theorem execute_ordinary {image : Image} {s t : MachineState} {i : Instruction} (fuel : Nat)
    (hf : fetch image s = some i) (hs : ordinaryStep s i = some t) :
    execute (fuel + 1) image s =
      (fun r => r.charge (instructionCycles i) 0 0) <$> execute fuel image t := by
  cases i with
  | base j =>
    have hne := ordinaryStep_ne_ecall hs
    cases j <;> first | exact absurd rfl hne | simp_all [execute]
  | word op rd rs1 rs2 => simp [execute, hf, hs]
  | sraiw rd rs sh => simp [execute, hf, hs]
theorem Steps.execute {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) (fuel : Nat) :
    Riscv.execute (fuel + k) image s = (fun r => r.charge c 0 0) <$> Riscv.execute fuel image t := by
  induction h with
  | refl => simp
  | @step s t u i k c hf hs _ ih =>
    rw [← Nat.add_assoc, execute_ordinary _ hf hs, ih, Functor.map_map]
    simp [Nat.add_comm]
theorem Steps.execute_le {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) {fuel : Nat} (hle : k ≤ fuel) :
    Riscv.execute fuel image s =
      (fun r => r.charge c 0 0) <$> Riscv.execute (fuel - k) image t := by
  have := h.execute (fuel - k)
  rwa [Nat.sub_add_cancel hle] at this
theorem execute_hash {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) :
    Riscv.execute (fuel + 1) image s = (do
      let a ← HashSpec.query (hashInput s)
      (fun r => r.charge (8 * (hashInput s).blocks) 1 (hashInput s).blocks) <$>
        Riscv.execute fuel image (writeHash s a)) := by
  simp [Riscv.execute, hf, ht0, hv, map_eq_bind_pure_comp]
theorem execute_halt {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 1) :
    Riscv.execute (fuel + 1) image s =
      pure ⟨if s.getReg .x10 = 0 then .success else .failure, s, 1, 0, 0⟩ := by
  simp [Riscv.execute, hf, ht0]
theorem execute_ecall_fail {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL))
    (hbad : ¬ (s.getReg .x5 = 0 ∧ hashArgumentsValid s = true)) (ht0 : s.getReg .x5 ≠ 1) :
    Riscv.execute (fuel + 1) image s = pure ⟨.failure, s, 1, 0, 0⟩ := by
  have hbad' : ¬ (s.getReg .x5 = 0#64 ∧ hashArgumentsValid s = true) := hbad
  have ht0' : ¬ s.getReg .x5 = 1#64 := ht0
  simp [Riscv.execute, hf]
  rw [if_neg hbad', if_neg ht0']
theorem execute_fetch_none {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = none) :
    Riscv.execute (fuel + 1) image s = pure ⟨.failure, s, 0, 0, 0⟩ := by
  simp [Riscv.execute, hf]
theorem Steps.evalWith {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) (hash : Hash) (fuel : Nat) :
    evalWithAnswerFn hash (Riscv.execute (fuel + k) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image t)).charge c 0 0 := by
  rw [h.execute, evalWithAnswerFn_map]
theorem evalWith_hash {image : Image} {s : MachineState} (hash : Hash) (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) :
    evalWithAnswerFn hash (Riscv.execute (fuel + 1) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image (writeHash s (hash (hashInput s))))).charge
        (8 * (hashInput s).blocks) 1 (hashInput s).blocks := by
  rw [execute_hash fuel hf ht0 hv, evalWithAnswerFn_bind, evalWithAnswerFn_map]
  have : evalWithAnswerFn hash (HashSpec.query (hashInput s) : OracleComp HashSpec _) =
      hash (hashInput s) := evalWithAnswerFn_query hash _
  rw [this]
theorem evalWith_halt {image : Image} {s : MachineState} (hash : Hash) (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 1) :
    evalWithAnswerFn hash (Riscv.execute (fuel + 1) image s) =
      ⟨if s.getReg .x10 = 0 then .success else .failure, s, 1, 0, 0⟩ := by
  rw [execute_halt fuel hf ht0]; rfl
def toRunResult (submission : Submission) (phase : Phase) (e : Execution) :
    RunResult (Output submission.sizes phase) :=
  ⟨if e.exit = .success then
      some (readOutput submission.sizes submission.layout phase e.state) else none,
    e.exit != .unfinished, e.cycles, e.hashCalls, e.hashCompressions⟩
theorem run_eq (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    (s : MachineState) (hinit : initialState submission phase input = some s) :
    submission.run phase input =
      toRunResult submission phase <$> Riscv.execute CYCLE_LIMIT (submission.image phase) s := by
  simp only [Submission.run, hinit, map_eq_bind_pure_comp]
  rfl
theorem runWith_eq (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase)
    (s : MachineState) (hinit : initialState submission phase input = some s) :
    submission.runWith hash phase input =
      toRunResult submission phase
        (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT (submission.image phase) s)) := by
  rw [Submission.runWith, run_eq submission phase input s hinit, evalWithAnswerFn_map]
theorem initialState_pc (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase) (s : MachineState)
    (hinit : initialState submission phase input = some s) : s.pc = 0x1000 := by
  unfold initialState at hinit
  dsimp only at hinit
  split at hinit
  · cases hinit
    simp only [MachineState.pc_setReg]
    generalize (inputBuffers submission.sizes submission.layout phase input) = bufs
    suffices ∀ (st : MachineState), st.pc = 0x1000 → (bufs.foldl (fun state buffer =>
        state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) st).pc = 0x1000 from
      this _ (by simp)
    induction bufs with
    | nil => intro st h; exact h
    | cons b bs ih => intro st h; exact ih _ (by simp [h])
  · cases hinit
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Expr ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
deriving instance Lean.ToExpr for Reg
deriving instance Lean.ToExpr for WordOp
inductive LoadKind where
  | d | w | wu | h | hu | b | bu
  deriving DecidableEq, Repr, Lean.ToExpr
inductive StoreKind where
  | d | w | h | b
  deriving DecidableEq, Repr, Lean.ToExpr
def LoadKind.width : LoadKind → Nat
  | .d => 8 | .w => 4 | .wu => 4 | .h => 2 | .hu => 2 | .b => 1 | .bu => 1
def StoreKind.width : StoreKind → Nat
  | .d => 8 | .w => 4 | .h => 2 | .b => 1
def LoadKind.fromWord : LoadKind → Word → Nat → Word
  | .d, x, _ => x
  | .w, x, bo => (extractWord32 x (bo / 4)).signExtend 64
  | .wu, x, bo => (extractWord32 x (bo / 4)).zeroExtend 64
  | .h, x, bo => (extractHalfword x (bo / 2)).signExtend 64
  | .hu, x, bo => (extractHalfword x (bo / 2)).zeroExtend 64
  | .b, x, bo => (extractByte x bo).signExtend 64
  | .bu, x, bo => (extractByte x bo).zeroExtend 64
def StoreKind.merge : StoreKind → Word → Nat → Word → Word
  | .d, _, _, v => v
  | .w, old, bo, v => replaceWord32 old (bo / 4) (v.truncate 32)
  | .h, old, bo, v => replaceHalfword old (bo / 2) (v.truncate 16)
  | .b, old, bo, v => replaceByte old bo (v.truncate 8)
inductive BinOp where
  | add | sub | and | or | xor | sll | srl | sra | slt | sltu
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  | w (op : WordOp)
  | st (k : StoreKind) (bo : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr
inductive UnOp where
  | ld (k : LoadKind) (bo : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr
inductive CmpOp where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr, Lean.ToExpr
def BinOp.eval : BinOp → Word → Word → Word
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .sll, x, y => x <<< (y.toNat % 64)
  | .srl, x, y => x >>> (y.toNat % 64)
  | .sra, x, y => BitVec.sshiftRight x (y.toNat % 64)
  | .slt, x, y => if BitVec.slt x y then 1 else 0
  | .sltu, x, y => if BitVec.ult x y then 1 else 0
  | .mul, x, y => x * y
  | .mulh, x, y => rv64_mulh x y
  | .mulhsu, x, y => rv64_mulhsu x y
  | .mulhu, x, y => rv64_mulhu x y
  | .div, x, y => rv64_div x y
  | .divu, x, y => rv64_divu x y
  | .rem, x, y => rv64_rem x y
  | .remu, x, y => rv64_remu x y
  | .w op, x, y => (wordResult op (x.truncate 32) (y.truncate 32)).signExtend 64
  | .st k bo, x, y => k.merge x bo y
def UnOp.eval : UnOp → Word → Word
  | .ld k bo, x => k.fromWord x bo
def CmpOp.eval : CmpOp → Word → Word → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lt, x, y => BitVec.slt x y
  | .ge, x, y => !BitVec.slt x y
  | .ltu, x, y => BitVec.ult x y
  | .geu, x, y => !BitVec.ult x y
inductive E where
  | c (v : Word)
  | reg (r : Reg)
  | ld (a : E)
  | un (op : UnOp) (a : E)
  | bin (op : BinOp) (a b : E)
  | ite (op : CmpOp) (x y a b : E)
  deriving Repr, Lean.ToExpr
def E.eval (s : MachineState) : E → Word
  | .c v => v
  | .reg r => s.getReg r
  | .ld a => s.getMem (a.eval s)
  | .un op a => op.eval (a.eval s)
  | .bin op a b => op.eval (a.eval s) (b.eval s)
  | .ite op x y a b => if op.eval (x.eval s) (y.eval s) then a.eval s else b.eval s
def Reg.beqN (a b : Reg) : Bool := a.toNat == b.toNat
theorem Reg.toNat_inj {a b : Reg} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Reg.toNat] at h)
theorem Reg.beqN_eq {a b : Reg} (h : Reg.beqN a b = true) : a = b :=
  Reg.toNat_inj (by simpa [Reg.beqN] using h)
def E.beq : E → E → Bool
  | .c x, .c y => x.toNat == y.toNat
  | .reg a, .reg b => Reg.beqN a b
  | .ld a, .ld b => E.beq a b
  | .un o a, .un o' b => decide (o = o') && E.beq a b
  | .bin o a b, .bin o' a' b' => decide (o = o') && E.beq a a' && E.beq b b'
  | .ite o x y a b, .ite o' x' y' a' b' =>
      decide (o = o') && E.beq x x' && E.beq y y' && E.beq a a' && E.beq b b'
  | _, _ => false
theorem E.beq_eq : ∀ {a b : E}, E.beq a b = true → a = b := by
  intro a
  induction a with
  | c x => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (BitVec.eq_of_toNat_eq h)
  | reg r => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (Reg.beqN_eq h)
  | ld a ih => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (ih h)
  | un o a ih =>
    intro b h; cases b <;> simp [E.beq] at h
    obtain ⟨h1, h2⟩ := h; subst h1; rw [ih h2]
  | bin o a b iha ihb =>
    intro b' h; cases b' <;> simp [E.beq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h; subst h1; rw [iha h2, ihb h3]
  | ite o x y a b ihx ihy iha ihb =>
    intro b' h; cases b' <;> simp [E.beq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h; subst h1; rw [ihx h2, ihy h3, iha h4, ihb h5]
def addC (a : E) (k : Word) : E :=
  match a with
  | .c x => .c (x + k)
  | .bin .add a' (.c x) => if (x + k).toNat == 0 then a' else .bin .add a' (.c (x + k))
  | a => if k.toNat == 0 then a else .bin .add a (.c k)
def mkAdd (a b : E) : E :=
  match b with
  | .c k => addC a k
  | b =>
    match a with
    | .c k => addC b k
    | a =>
      match b with
      | .bin .add b' (.c k) => addC (.bin .add a b') k
      | b => .bin .add a b
def mkBin (op : BinOp) (a b : E) : E :=
  match op with
  | .add => mkAdd a b
  | .sub =>
    match a, b with
    | .c x, .c y => .c (x - y)
    | a, .c y => addC a (-y)
    | a, b => .bin .sub a b
  | op =>
    match a, b with
    | .c x, .c y => .c (op.eval x y)
    | a, b => .bin op a b
def mkUn (op : UnOp) (a : E) : E :=
  match a with
  | .c x => .c (op.eval x)
  | a => .un op a
def mkIte (op : CmpOp) (x y a b : E) : E :=
  match x, y with
  | .c u, .c v => if op.eval u v then a else b
  | x, y => .ite op x y a b
theorem addC_eval (s : MachineState) (a : E) (k : Word) :
    (addC a k).eval s = a.eval s + k := by
  unfold addC
  split
  · rfl
  · rename_i a' x
    split
    · rename_i h
      have h0 : x + k = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
      simp [E.eval, BinOp.eval, BitVec.add_assoc, h0]
    · simp [E.eval, BinOp.eval, BitVec.add_assoc]
  · split
    · rename_i h
      have h0 : k = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
      simp [h0]
    · rfl
theorem mkAdd_eval (s : MachineState) (a b : E) :
    (mkAdd a b).eval s = a.eval s + b.eval s := by
  unfold mkAdd
  split
  · rw [addC_eval]; rfl
  · split
    · rw [addC_eval, BitVec.add_comm]; rfl
    · split
      · rw [addC_eval]; simp [E.eval, BinOp.eval, BitVec.add_assoc]
      · rfl
theorem mkBin_eval (s : MachineState) (op : BinOp) (a b : E) :
    (mkBin op a b).eval s = op.eval (a.eval s) (b.eval s) := by
  unfold mkBin
  split
  · exact mkAdd_eval s a b
  · split
    · rfl
    · rw [addC_eval]; simp [E.eval, BinOp.eval, BitVec.sub_eq_add_neg]
    · rfl
  · split
    · rfl
    · rfl
theorem mkUn_eval (s : MachineState) (op : UnOp) (a : E) :
    (mkUn op a).eval s = op.eval (a.eval s) := by
  unfold mkUn; split <;> rfl
theorem mkIte_eval (s : MachineState) (op : CmpOp) (x y a b : E) :
    (mkIte op x y a b).eval s =
      if op.eval (x.eval s) (y.eval s) then a.eval s else b.eval s := by
  unfold mkIte
  split
  · split <;> simp_all [E.eval]
  · rfl
structure Addr where
  base : Option E
  off : Word
  deriving Repr, Lean.ToExpr
def Addr.eval (s : MachineState) (a : Addr) : Word :=
  match a.base with
  | none => a.off
  | some b => b.eval s + a.off
def Addr.toE (a : Addr) : E :=
  match a.base with
  | none => .c a.off
  | some b => addC b a.off
theorem Addr.toE_eval (s : MachineState) (a : Addr) : a.toE.eval s = a.eval s := by
  rcases a with ⟨_ | b, off⟩
  · rfl
  · simp [Addr.toE, Addr.eval, addC_eval]
def norm : E → Addr
  | .c k => ⟨none, k⟩
  | .bin .add a (.c k) => ⟨some a, k⟩
  | e => ⟨some e, 0⟩
theorem norm_eval (s : MachineState) (e : E) : (norm e).eval s = e.eval s := by
  unfold norm
  split
  · rfl
  · rfl
  · simp [Addr.eval]
def Addr.beq (a b : Addr) : Bool :=
  (match a.base, b.base with
   | none, none => true
   | some x, some y => E.beq x y
   | _, _ => false) && a.off.toNat == b.off.toNat
theorem Addr.beq_eq {a b : Addr} (h : Addr.beq a b = true) : a = b := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;> simp [Addr.beq] at h
  · rw [BitVec.eq_of_toNat_eq h]
  · rw [E.beq_eq h.1, BitVec.eq_of_toNat_eq h.2]
inductive Alias where
  | same | diff | unknown
  deriving DecidableEq, Repr
def Addr.alias (a b : Addr) : Alias :=
  match a.base, b.base with
  | none, none => if a.off.toNat == b.off.toNat then .same else .diff
  | some x, some y =>
    if E.beq x y then (if a.off.toNat == b.off.toNat then .same else .diff) else .unknown
  | _, _ => .unknown
theorem Addr.alias_same {a b : Addr} (h : a.alias b = .same) (s : MachineState) :
    a.eval s = b.eval s := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;>
    simp only [Addr.alias, Addr.eval] at h ⊢
  · split at h
    · rename_i h'; exact BitVec.eq_of_toNat_eq (by simpa using h')
    · cases h
  · cases h
  · cases h
  · split at h
    · rename_i hb; split at h
      · rename_i h'
        have h1 := E.beq_eq hb
        have h2 : o = o' := BitVec.eq_of_toNat_eq (by simpa using h')
        rw [h1, h2]
      · cases h
    · cases h
theorem Addr.alias_diff {a b : Addr} (h : a.alias b = .diff) (s : MachineState) :
    a.eval s ≠ b.eval s := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;>
    simp only [Addr.alias, Addr.eval] at h ⊢
  · split at h
    · cases h
    · rename_i h'; intro heq; apply h'; simp [heq]
  · cases h
  · cases h
  · split at h
    · rename_i hb; split at h
      · cases h
      · rename_i h'; rw [E.beq_eq hb]; intro heq; apply h'
        have := (BitVec.add_right_inj _).mp heq
        simp [this]
    · cases h
inductive Oblig where
  | valid (a : Addr) (w : Nat)
  | align8 (b : E)
  | ne (a b : Addr)
  deriving Repr, Lean.ToExpr
def Oblig.holds (s : MachineState) : Oblig → Prop
  | .valid a w => accessValid (a.eval s) w = true
  | .align8 b => (b.eval s).toNat % 8 = 0
  | .ne a b => a.eval s ≠ b.eval s
def Oblig.beq : Oblig → Oblig → Bool
  | .valid a w, .valid b w' => Addr.beq a b && w == w'
  | .align8 a, .align8 b => E.beq a b
  | .ne a b, .ne a' b' => Addr.beq a a' && Addr.beq b b'
  | _, _ => false
theorem Oblig.beq_eq {a b : Oblig} (h : Oblig.beq a b = true) : a = b := by
  cases a <;> cases b <;> simp [Oblig.beq] at h
  · rw [Addr.beq_eq h.1, h.2]
  · rw [E.beq_eq h]
  · rw [Addr.beq_eq h.1, Addr.beq_eq h.2]
def Oblig.all (s : MachineState) : List Oblig → Prop
  | [] => True
  | [o] => o.holds s
  | o :: os => o.holds s ∧ Oblig.all s os
theorem Oblig.all_iff (s : MachineState) (os : List Oblig) :
    Oblig.all s os ↔ ∀ o ∈ os, o.holds s := by
  induction os with
  | nil => simp [Oblig.all]
  | cons o os ih =>
    cases os with
    | nil => simp [Oblig.all]
    | cons o' os' => simp only [Oblig.all] at ih ⊢; simp [ih]
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Micro ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
inductive Src where
  | reg (r : Reg)
  | imm (v : Word)
  | pc
  deriving Repr
def Src.eval (s : MachineState) : Src → Word
  | .reg r => s.getReg r
  | .imm v => v
  | .pc => s.pc
inductive Micro where
  | alu (rd : Reg) (op : BinOp) (a b : Src)
  | load (k : LoadKind) (rd rs : Reg) (off : Word)
  | store (k : StoreKind) (rs1 rs2 : Reg) (off : Word)
  | branch (op : CmpOp) (rs1 rs2 : Reg) (off : Word)
  | jal (rd : Reg) (off : Word)
  | jalr (rd rs : Reg) (off : Word)
  deriving Repr
def LoadKind.read (s : MachineState) (addr : Word) : LoadKind → Word
  | .d => s.getMem addr
  | .w => (s.getWord32 addr).signExtend 64
  | .wu => (s.getWord32 addr).zeroExtend 64
  | .h => (s.getHalfword addr).signExtend 64
  | .hu => (s.getHalfword addr).zeroExtend 64
  | .b => (s.getByte addr).signExtend 64
  | .bu => (s.getByte addr).zeroExtend 64
def StoreKind.write (s : MachineState) (addr v : Word) : StoreKind → MachineState
  | .d => s.setMem addr v
  | .w => s.setWord32 addr (v.truncate 32)
  | .h => s.setHalfword addr (v.truncate 16)
  | .b => s.setByte addr (v.truncate 8)
theorem LoadKind.read_sub (s : MachineState) (addr : Word) (k : LoadKind) (hk : k ≠ .d) :
    k.read s addr = k.fromWord (s.getMem (alignToDword addr)) (byteOffset addr) := by
  cases k <;> first | exact absurd rfl hk | rfl
theorem StoreKind.write_sub (s : MachineState) (addr v : Word) (k : StoreKind) (hk : k ≠ .d) :
    k.write s addr v =
      s.setMem (alignToDword addr) (k.merge (s.getMem (alignToDword addr)) (byteOffset addr) v) := by
  cases k <;> first | exact absurd rfl hk | rfl
def Micro.exec (s : MachineState) : Micro → Option MachineState
  | .alu rd op a b => some ((s.setReg rd (op.eval (a.eval s) (b.eval s))).setPC (s.pc + 4))
  | .load k rd rs off =>
    if accessValid (s.getReg rs + off) k.width then
      some ((s.setReg rd (k.read s (s.getReg rs + off))).setPC (s.pc + 4))
    else none
  | .store k rs1 rs2 off =>
    if accessValid (s.getReg rs1 + off) k.width then
      some ((k.write s (s.getReg rs1 + off) (s.getReg rs2)).setPC (s.pc + 4))
    else none
  | .branch op rs1 rs2 off =>
    some (s.setPC (if op.eval (s.getReg rs1) (s.getReg rs2) then s.pc + off else s.pc + 4))
  | .jal rd off => some ((s.setReg rd (s.pc + 4)).setPC (s.pc + off))
  | .jalr rd rs off => some ((s.setReg rd (s.pc + 4)).setPC ((s.getReg rs + off) &&& ~~~1#64))
def luiVal (imm : BitVec 20) : Word := ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
def classify : Instruction → Option Micro
  | .base i =>
    match i with
    | .ADD rd a b => some (.alu rd .add (.reg a) (.reg b))
    | .SUB rd a b => some (.alu rd .sub (.reg a) (.reg b))
    | .SLL rd a b => some (.alu rd .sll (.reg a) (.reg b))
    | .SRL rd a b => some (.alu rd .srl (.reg a) (.reg b))
    | .SRA rd a b => some (.alu rd .sra (.reg a) (.reg b))
    | .AND rd a b => some (.alu rd .and (.reg a) (.reg b))
    | .OR rd a b => some (.alu rd .or (.reg a) (.reg b))
    | .XOR rd a b => some (.alu rd .xor (.reg a) (.reg b))
    | .SLT rd a b => some (.alu rd .slt (.reg a) (.reg b))
    | .SLTU rd a b => some (.alu rd .sltu (.reg a) (.reg b))
    | .ADDI rd a imm => some (.alu rd .add (.reg a) (.imm (signExtend12 imm)))
    | .ANDI rd a imm => some (.alu rd .and (.reg a) (.imm (signExtend12 imm)))
    | .ORI rd a imm => some (.alu rd .or (.reg a) (.imm (signExtend12 imm)))
    | .XORI rd a imm => some (.alu rd .xor (.reg a) (.imm (signExtend12 imm)))
    | .SLTI rd a imm => some (.alu rd .slt (.reg a) (.imm (signExtend12 imm)))
    | .SLTIU rd a imm => some (.alu rd .sltu (.reg a) (.imm (signExtend12 imm)))
    | .SLLI rd a sh => some (.alu rd .sll (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRLI rd a sh => some (.alu rd .srl (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRAI rd a sh => some (.alu rd .sra (.reg a) (.imm (sh.zeroExtend 64)))
    | .LUI rd imm => some (.alu rd .add (.imm (luiVal imm)) (.imm 0))
    | .AUIPC rd imm => some (.alu rd .add .pc (.imm (luiVal imm)))
    | .LD rd a off => some (.load .d rd a (signExtend12 off))
    | .LW rd a off => some (.load .w rd a (signExtend12 off))
    | .LWU rd a off => some (.load .wu rd a (signExtend12 off))
    | .LH rd a off => some (.load .h rd a (signExtend12 off))
    | .LHU rd a off => some (.load .hu rd a (signExtend12 off))
    | .LB rd a off => some (.load .b rd a (signExtend12 off))
    | .LBU rd a off => some (.load .bu rd a (signExtend12 off))
    | .SD a b off => some (.store .d a b (signExtend12 off))
    | .SW a b off => some (.store .w a b (signExtend12 off))
    | .SH a b off => some (.store .h a b (signExtend12 off))
    | .SB a b off => some (.store .b a b (signExtend12 off))
    | .BEQ a b off => some (.branch .eq a b (signExtend13 off))
    | .BNE a b off => some (.branch .ne a b (signExtend13 off))
    | .BLT a b off => some (.branch .lt a b (signExtend13 off))
    | .BGE a b off => some (.branch .ge a b (signExtend13 off))
    | .BLTU a b off => some (.branch .ltu a b (signExtend13 off))
    | .BGEU a b off => some (.branch .geu a b (signExtend13 off))
    | .JAL rd off => some (.jal rd (signExtend21 off))
    | .JALR rd a off => some (.jalr rd a (signExtend12 off))
    | .ADDIW rd a imm => some (.alu rd (.w .add) (.reg a) (.imm (signExtend12 imm)))
    | .SUBW rd a b => some (.alu rd (.w .sub) (.reg a) (.reg b))
    | .SRLW rd a b => some (.alu rd (.w .srl) (.reg a) (.reg b))
    | .SLLIW rd a sh => some (.alu rd (.w .sll) (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRLIW rd a sh => some (.alu rd (.w .srl) (.reg a) (.imm (sh.zeroExtend 64)))
    | .MUL rd a b => some (.alu rd .mul (.reg a) (.reg b))
    | .MULH rd a b => some (.alu rd .mulh (.reg a) (.reg b))
    | .MULHSU rd a b => some (.alu rd .mulhsu (.reg a) (.reg b))
    | .MULHU rd a b => some (.alu rd .mulhu (.reg a) (.reg b))
    | .DIV rd a b => some (.alu rd .div (.reg a) (.reg b))
    | .DIVU rd a b => some (.alu rd .divu (.reg a) (.reg b))
    | .REM rd a b => some (.alu rd .rem (.reg a) (.reg b))
    | .REMU rd a b => some (.alu rd .remu (.reg a) (.reg b))
    | .FENCE => some (.alu .x0 .add (.imm 0) (.imm 0))
    | _ => none
  | .word op rd a b => some (.alu rd (.w op) (.reg a) (.reg b))
  | .sraiw rd a sh => some (.alu rd (.w .sra) (.reg a) (.imm (sh.zeroExtend 64)))
private theorem toNat_zext6 (sh : BitVec 6) : (sh.zeroExtend 64).toNat % 64 = sh.toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := sh.isLt
  omega
private theorem toNat_trunc_zext5 (sh : BitVec 5) :
    ((sh.zeroExtend 64).truncate 32).toNat % 32 = sh.toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := sh.isLt
  omega
private theorem toNat_trunc32 (x : Word) : (x.truncate 32).toNat % 32 = x.toNat % 32 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega
private theorem toNat_mod32 (sh : BitVec 5) : sh.toNat % 32 = sh.toNat := by
  have := sh.isLt; omega
private theorem setPC_ite (s : MachineState) (c : Prop) [Decidable c] (a b : Word) :
    (if c then s.setPC a else s.setPC b) = s.setPC (if c then a else b) := by
  split <;> rfl
set_option maxHeartbeats 1000000 in
theorem classify_sound {i : Instruction} {m : Micro} (h : classify i = some m) (s : MachineState) :
    ordinaryStep s i = m.exec s := by
  cases i with
  | base i =>
    cases i <;> simp only [classify, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first
        | rfl
        | (refine (show some (execInstrBr s _) = _ from ?_)
           simp only [execInstrBr, Micro.exec, Src.eval, BinOp.eval, CmpOp.eval, toNat_zext6,
             toNat_trunc32, wordResult, luiVal, setPC_ite]
           try simp only [toNat_mod32]
           try simp
           try congr
           all_goals exact (toNat_mod32 _).symm)
  | word op rd a b =>
    simp only [classify, Option.some.injEq] at h; subst h; rfl
  | sraiw rd a sh =>
    simp only [classify, Option.some.injEq] at h; subst h
    simp only [ordinaryStep, Micro.exec, Src.eval, BinOp.eval, wordResult, toNat_trunc_zext5]
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Exec ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
structure RegFile where
  r1 : E
  r2 : E
  r3 : E
  r4 : E
  r5 : E
  r6 : E
  r7 : E
  r8 : E
  r9 : E
  r10 : E
  r11 : E
  r12 : E
  r13 : E
  r14 : E
  r15 : E
  r16 : E
  r17 : E
  r18 : E
  r19 : E
  r20 : E
  r21 : E
  r22 : E
  r23 : E
  r24 : E
  r25 : E
  r26 : E
  r27 : E
  r28 : E
  r29 : E
  r30 : E
  r31 : E
  deriving Repr, Lean.ToExpr
def RegFile.fields (rf : RegFile) : List E := [rf.r1, rf.r2, rf.r3, rf.r4, rf.r5, rf.r6, rf.r7, rf.r8, rf.r9, rf.r10, rf.r11, rf.r12, rf.r13, rf.r14, rf.r15, rf.r16, rf.r17, rf.r18, rf.r19, rf.r20, rf.r21, rf.r22, rf.r23, rf.r24, rf.r25, rf.r26, rf.r27, rf.r28, rf.r29, rf.r30, rf.r31]
def RegFile.init : RegFile := ⟨.reg .x1, .reg .x2, .reg .x3, .reg .x4, .reg .x5, .reg .x6, .reg .x7, .reg .x8, .reg .x9, .reg .x10, .reg .x11, .reg .x12, .reg .x13, .reg .x14, .reg .x15, .reg .x16, .reg .x17, .reg .x18, .reg .x19, .reg .x20, .reg .x21, .reg .x22, .reg .x23, .reg .x24, .reg .x25, .reg .x26, .reg .x27, .reg .x28, .reg .x29, .reg .x30, .reg .x31⟩
def RegFile.get (rf : RegFile) : Reg → E
  | .x0 => .c 0
  | .x1 => rf.r1
  | .x2 => rf.r2
  | .x3 => rf.r3
  | .x4 => rf.r4
  | .x5 => rf.r5
  | .x6 => rf.r6
  | .x7 => rf.r7
  | .x8 => rf.r8
  | .x9 => rf.r9
  | .x10 => rf.r10
  | .x11 => rf.r11
  | .x12 => rf.r12
  | .x13 => rf.r13
  | .x14 => rf.r14
  | .x15 => rf.r15
  | .x16 => rf.r16
  | .x17 => rf.r17
  | .x18 => rf.r18
  | .x19 => rf.r19
  | .x20 => rf.r20
  | .x21 => rf.r21
  | .x22 => rf.r22
  | .x23 => rf.r23
  | .x24 => rf.r24
  | .x25 => rf.r25
  | .x26 => rf.r26
  | .x27 => rf.r27
  | .x28 => rf.r28
  | .x29 => rf.r29
  | .x30 => rf.r30
  | .x31 => rf.r31
def RegFile.set (rf : RegFile) (r : Reg) (e : E) : RegFile :=
  match r with
  | .x0 => rf
  | .x1 => { rf with r1 := e }
  | .x2 => { rf with r2 := e }
  | .x3 => { rf with r3 := e }
  | .x4 => { rf with r4 := e }
  | .x5 => { rf with r5 := e }
  | .x6 => { rf with r6 := e }
  | .x7 => { rf with r7 := e }
  | .x8 => { rf with r8 := e }
  | .x9 => { rf with r9 := e }
  | .x10 => { rf with r10 := e }
  | .x11 => { rf with r11 := e }
  | .x12 => { rf with r12 := e }
  | .x13 => { rf with r13 := e }
  | .x14 => { rf with r14 := e }
  | .x15 => { rf with r15 := e }
  | .x16 => { rf with r16 := e }
  | .x17 => { rf with r17 := e }
  | .x18 => { rf with r18 := e }
  | .x19 => { rf with r19 := e }
  | .x20 => { rf with r20 := e }
  | .x21 => { rf with r21 := e }
  | .x22 => { rf with r22 := e }
  | .x23 => { rf with r23 := e }
  | .x24 => { rf with r24 := e }
  | .x25 => { rf with r25 := e }
  | .x26 => { rf with r26 := e }
  | .x27 => { rf with r27 := e }
  | .x28 => { rf with r28 := e }
  | .x29 => { rf with r29 := e }
  | .x30 => { rf with r30 := e }
  | .x31 => { rf with r31 := e }
abbrev SymMem := List (Addr × E)
def memEval (s : MachineState) : SymMem → Word → Word
  | [], a => s.getMem a
  | (k, v) :: ws, a => if a = k.eval s then v.eval s else memEval s ws a
structure Config where
  noAlias : Bool := false
  deriving Repr
def readMem (cfg : Config) (k : Addr) : SymMem → Option (E × List Oblig)
  | [] => some (.ld k.toE, [])
  | (k', v) :: ws =>
    match k.alias k' with
    | .same => some (v, [])
    | .diff => readMem cfg k ws
    | .unknown =>
      if cfg.noAlias then
        match readMem cfg k ws with
        | none => none
        | some (e, os) => some (e, .ne k k' :: os)
      else none
def isSame (k k' : Addr) : Bool :=
  match k.alias k' with
  | .same => true
  | _ => false
def writeMem (k : Addr) (v : E) (ws : SymMem) : SymMem :=
  (k, v) :: ws.filter (fun p => !isSame k p.1)
structure SymState where
  regs : RegFile
  mem : SymMem
  obl : List Oblig
  deriving Repr, Lean.ToExpr
def SymState.init : SymState := ⟨RegFile.init, [], []⟩
def Oblig.dedupable : Oblig → Bool
  | .ne .. => false
  | _ => true
def SymState.addObl (σ : SymState) (o : Oblig) : SymState :=
  if o.dedupable && σ.obl.any (Oblig.beq o) then σ else { σ with obl := o :: σ.obl }
def SymState.addObls (σ : SymState) (os : List Oblig) : SymState :=
  os.foldl SymState.addObl σ
def Src.sym (rf : RegFile) (pc : Word) : Src → E
  | .reg r => rf.get r
  | .imm v => .c v
  | .pc => .c pc
def checkValid (σ : SymState) (a : Addr) (w : Nat) : Option SymState :=
  match a.base with
  | none => if accessValid a.off w then some σ else none
  | some _ => some (σ.addObl (.valid a w))
def subKey (σ : SymState) (a : Addr) : SymState × Addr × Nat :=
  match a.base with
  | none => (σ, ⟨none, alignToDword a.off⟩, byteOffset a.off)
  | some b => (σ.addObl (.align8 b), ⟨some b, alignToDword a.off⟩, byteOffset a.off)
def LoadKind.isD : LoadKind → Bool
  | .d => true
  | _ => false
def StoreKind.isD : StoreKind → Bool
  | .d => true
  | _ => false
def symMicro (cfg : Config) (pc : Word) (σ : SymState) : Micro → Option (SymState × Option E)
  | .alu rd op a b =>
    some ({ σ with regs := σ.regs.set rd (mkBin op (a.sym σ.regs pc) (b.sym σ.regs pc)) }, none)
  | .load k rd rs off =>
    let a := norm (mkAdd (σ.regs.get rs) (.c off))
    match checkValid σ a k.width with
    | none => none
    | some σ₁ =>
      if k.isD then
        match readMem cfg a σ₁.mem with
        | none => none
        | some (v, os) =>
          let σ₂ := σ₁.addObls os
          some ({ σ₂ with regs := σ₂.regs.set rd v }, none)
      else
        match subKey σ₁ a with
        | (σ₂, key, bo) =>
          match readMem cfg key σ₂.mem with
          | none => none
          | some (w, os) =>
            let σ₃ := σ₂.addObls os
            some ({ σ₃ with regs := σ₃.regs.set rd (mkUn (.ld k bo) w) }, none)
  | .store k rs1 rs2 off =>
    let a := norm (mkAdd (σ.regs.get rs1) (.c off))
    let v := σ.regs.get rs2
    match checkValid σ a k.width with
    | none => none
    | some σ₁ =>
      if k.isD then
        some ({ σ₁ with mem := writeMem a v σ₁.mem }, none)
      else
        match subKey σ₁ a with
        | (σ₂, key, bo) =>
          match readMem cfg key σ₂.mem with
          | none => none
          | some (old, os) =>
            let σ₃ := σ₂.addObls os
            some ({ σ₃ with mem := writeMem key (mkBin (.st k bo) old v) σ₃.mem }, none)
  | .branch op r1 r2 off =>
    some (σ, some (mkIte op (σ.regs.get r1) (σ.regs.get r2) (.c (pc + off)) (.c (pc + 4))))
  | .jal rd off =>
    some ({ σ with regs := σ.regs.set rd (.c (pc + 4)) }, some (.c (pc + off)))
  | .jalr rd rs off =>
    some ({ σ with regs := σ.regs.set rd (.c (pc + 4)) },
      some (mkBin .and (mkAdd (σ.regs.get rs) (.c off)) (.c (~~~1#64))))
inductive Stop where
  | fuel | endOfCode | branch | jump | ecall
  deriving DecidableEq, Repr, Lean.ToExpr
structure Result where
  st : SymState
  pc : E
  stop : Stop
  steps : Nat
  cycles : Nat
  deriving Repr, Lean.ToExpr
def Micro.stopKind : Micro → Stop
  | .branch .. => .branch
  | _ => .jump
def isEcall : Instruction → Bool
  | .base .ECALL => true
  | _ => false
def symRunAux (cfg : Config) : List (BitVec 32) → Word → Nat → SymState → Option Result
  | _, pc, 0, σ => some ⟨σ, .c pc, .fuel, 0, 0⟩
  | [], pc, _ + 1, σ => some ⟨σ, .c pc, .endOfCode, 0, 0⟩
  | w :: ws, pc, f + 1, σ =>
    match decodeInstruction w with
    | none => none
    | some i =>
      if isEcall i then some ⟨σ, .c pc, .ecall, 0, 0⟩ else
      match classify i with
      | none => none
      | some m =>
        match symMicro cfg pc σ m with
        | none => none
        | some (σ', none) =>
          match symRunAux cfg ws (pc + 4) f σ' with
          | none => none
          | some r => some { r with steps := r.steps + 1, cycles := instructionCycles i + r.cycles }
        | some (σ', some t) => some ⟨σ', t, m.stopKind, 1, instructionCycles i⟩
def symRun (cfg : Config) (code : List (BitVec 32)) (pc : Word) (fuel : Nat) : Option Result :=
  symRunAux cfg code pc fuel SymState.init
def SymState.toState (σ : SymState) (s : MachineState) (pc : Word) : MachineState :=
  { s with
    regs := fun r => if r = .x0 then s.regs .x0 else (σ.regs.get r).eval s
    mem := memEval s σ.mem
    pc := pc }
def Result.toState (r : Result) (s : MachineState) : MachineState :=
  r.st.toState s (r.pc.eval s)
def Result.obligs (r : Result) (s : MachineState) : Prop := Oblig.all s r.st.obl
def CodeAt (image : Image) (pc : Word) (code : List (BitVec 32)) : Prop :=
  0x1000 ≤ pc.toNat ∧ pc.toNat % 4 = 0 ∧ pc.toNat + 4 * code.length < 2 ^ 64 ∧
    code <+: image.code.drop ((pc.toNat - 0x1000) / 4)
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Sound ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
@[simp] theorem RegFile.get_x0 (rf : RegFile) : rf.get .x0 = .c 0 := rfl
@[simp] theorem RegFile.set_x0 (rf : RegFile) (e : E) : rf.set .x0 e = rf := rfl
theorem RegFile.get_set_self (rf : RegFile) {r : Reg} (e : E) (h : r ≠ .x0) :
    (rf.set r e).get r = e := by
  cases r <;> first | exact absurd rfl h | rfl
set_option maxHeartbeats 4000000 in
theorem RegFile.get_set_ne (rf : RegFile) {r r' : Reg} (e : E) (h : r' ≠ r) :
    (rf.set r e).get r' = rf.get r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl
theorem RegFile.init_get_eval (s : MachineState) (r : Reg) :
    (RegFile.init.get r).eval s = s.getReg r := by
  cases r <;> rfl
theorem MachineState.ext' {a b : MachineState} (hr : a.regs = b.regs) (hm : a.mem = b.mem)
    (hc : a.code = b.code) (hp : a.pc = b.pc) (h1 : a.committed = b.committed)
    (h2 : a.publicValues = b.publicValues) (h3 : a.privateInput = b.privateInput)
    (h4 : a.inputBufBase = b.inputBufBase) : a = b := by
  cases a; cases b; simp_all
@[simp] theorem SymState.toState_getReg (σ : SymState) (s : MachineState) (pc : Word) (r : Reg) :
    (σ.toState s pc).getReg r = (σ.regs.get r).eval s := by
  cases r <;> rfl
@[simp] theorem SymState.toState_getMem (σ : SymState) (s : MachineState) (pc a : Word) :
    (σ.toState s pc).getMem a = memEval s σ.mem a := rfl
@[simp] theorem SymState.toState_pc (σ : SymState) (s : MachineState) (pc : Word) :
    (σ.toState s pc).pc = pc := rfl
@[simp] theorem SymState.toState_code (σ : SymState) (s : MachineState) (pc : Word) :
    (σ.toState s pc).code = s.code := rfl
theorem SymState.toState_setPC (σ : SymState) (s : MachineState) (pc pc' : Word) :
    (σ.toState s pc).setPC pc' = σ.toState s pc' := rfl
theorem SymState.toState_congr {σ σ' : SymState} {s : MachineState} (hr : σ.regs = σ'.regs)
    (hm : memEval s σ.mem = memEval s σ'.mem) (pc : Word) : σ.toState s pc = σ'.toState s pc := by
  unfold SymState.toState; rw [hr, hm]
theorem SymState.init_toState (s : MachineState) : SymState.init.toState s s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl
theorem setReg_of_ne (t : MachineState) {r : Reg} (v : Word) (h : r ≠ .x0) :
    t.setReg r v = { t with regs := fun r' => if r' = r then v else t.regs r' } := by
  cases r <;> first | exact absurd rfl h | (simp only [MachineState.setReg, beq_iff_eq])
theorem SymState.toState_setReg (σ : SymState) (s : MachineState) (pc : Word) (rd : Reg) (e : E) :
    (σ.toState s pc).setReg rd (e.eval s) = ({ σ with regs := σ.regs.set rd e }).toState s pc := by
  by_cases hrd : rd = .x0
  · subst hrd; rfl
  · rw [setReg_of_ne _ _ hrd]
    apply MachineState.ext' <;> try rfl
    funext r'
    simp only [SymState.toState]
    by_cases h : r' = rd
    · subst h; simp [hrd, RegFile.get_set_self _ _ hrd]
    · simp [h, RegFile.get_set_ne _ _ h]
theorem SymState.toState_setMem (σ : SymState) (s : MachineState) (pc : Word) (k : Addr) (e : E) :
    (σ.toState s pc).setMem (k.eval s) (e.eval s) =
      ({ σ with mem := (k, e) :: σ.mem }).toState s pc := by
  apply MachineState.ext' <;> try rfl
  funext a
  simp [MachineState.setMem, SymState.toState, memEval]
theorem memEval_nil (s : MachineState) (a : Word) : memEval s [] a = s.getMem a := rfl
theorem memEval_cons (s : MachineState) (k : Addr) (v : E) (ws : SymMem) (a : Word) :
    memEval s ((k, v) :: ws) a = if a = k.eval s then v.eval s else memEval s ws a := rfl
theorem memEval_frame (s : MachineState) (ws : SymMem) (a : Word)
    (h : ∀ p ∈ ws, a ≠ p.1.eval s) : memEval s ws a = s.getMem a := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨k, v⟩ := p
    rw [memEval_cons, if_neg (h _ (List.mem_cons_self ..))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
theorem isSame_eval {k k' : Addr} (h : isSame k k' = true) (s : MachineState) :
    k.eval s = k'.eval s := by
  unfold isSame at h
  split at h
  · rename_i hs; exact Addr.alias_same hs s
  · cases h
theorem memEval_writeMem (s : MachineState) (k : Addr) (v : E) (ws : SymMem) :
    memEval s (writeMem k v ws) = memEval s ((k, v) :: ws) := by
  funext a
  simp only [writeMem, memEval_cons]
  split
  · rfl
  · rename_i hne
    induction ws with
    | nil => rfl
    | cons p ws ih =>
      obtain ⟨k', v'⟩ := p
      simp only [List.filter_cons]
      split
      · rw [memEval_cons, memEval_cons, ih]
      · rename_i hs
        have hs' : isSame k k' = true := by simpa using hs
        rw [memEval_cons, if_neg, ih]
        rw [← isSame_eval hs' s]; exact hne
theorem readMem_sound {cfg : Config} {k : Addr} {ws : SymMem} {e : E} {os : List Oblig}
    (h : readMem cfg k ws = some (e, os)) (s : MachineState) (hos : ∀ o ∈ os, o.holds s) :
    memEval s ws (k.eval s) = e.eval s := by
  induction ws generalizing e os with
  | nil =>
    simp only [readMem, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [memEval_nil, E.eval, Addr.toE_eval]
  | cons p ws ih =>
    obtain ⟨k', v⟩ := p
    simp only [readMem] at h
    rw [memEval_cons]
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_pos (Addr.alias_same hs s)]
    · rename_i hd
      rw [if_neg (Addr.alias_diff hd s)]
      exact ih h hos
    · split at h
      · split at h
        · cases h
        · rename_i e' os' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hne := hos _ (List.mem_cons_self ..)
          simp only [Oblig.holds] at hne
          rw [if_neg hne]
          exact ih hr (fun o ho => hos o (List.mem_cons_of_mem _ ho))
      · cases h
theorem SymState.addObl_regs (σ : SymState) (o : Oblig) : (σ.addObl o).regs = σ.regs := by
  unfold SymState.addObl; split <;> rfl
theorem SymState.addObl_mem (σ : SymState) (o : Oblig) : (σ.addObl o).mem = σ.mem := by
  unfold SymState.addObl; split <;> rfl
theorem SymState.addObl_sub (σ : SymState) (o : Oblig) : σ.obl ⊆ (σ.addObl o).obl := by
  unfold SymState.addObl; split
  · exact List.Subset.refl _
  · exact List.subset_cons_self _ _
theorem SymState.addObl_mem_obl (σ : SymState) (o : Oblig) : o ∈ (σ.addObl o).obl := by
  unfold SymState.addObl; split
  · rename_i h
    obtain ⟨o', ho', hb⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp h).2
    rw [Oblig.beq_eq hb]; exact ho'
  · exact List.mem_cons_self ..
theorem SymState.addObls_regs (σ : SymState) (os : List Oblig) : (σ.addObls os).regs = σ.regs := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih => simp only [SymState.addObls, List.foldl_cons] at ih ⊢; rw [ih, addObl_regs]
theorem SymState.addObls_mem (σ : SymState) (os : List Oblig) : (σ.addObls os).mem = σ.mem := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih => simp only [SymState.addObls, List.foldl_cons] at ih ⊢; rw [ih, addObl_mem]
theorem SymState.addObls_sub (σ : SymState) (os : List Oblig) : σ.obl ⊆ (σ.addObls os).obl := by
  induction os generalizing σ with
  | nil => exact List.Subset.refl _
  | cons o os ih =>
    simp only [SymState.addObls, List.foldl_cons] at ih ⊢
    exact List.Subset.trans (addObl_sub σ o) (ih _)
theorem SymState.addObls_mem_obl (σ : SymState) (os : List Oblig) :
    ∀ o ∈ os, o ∈ (σ.addObls os).obl := by
  induction os generalizing σ with
  | nil => intro o h; cases h
  | cons o os ih =>
    intro o' h
    simp only [SymState.addObls, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact addObls_sub _ os (addObl_mem_obl σ o')
    · exact ih _ o' h
theorem byteOffset_eq (x : Word) : byteOffset x = x.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, show (7#64).toNat = 7 from rfl]
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 3
theorem alignToDword_toNat (x : Word) : (alignToDword x).toNat = x.toNat - x.toNat % 8 := by
  unfold alignToDword
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  have hhi_mod : (x.toNat &&& (2 ^ 64 - 1 - 7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_mod_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) % 2 ^ 3 = 0 from by decide]
    simp
  have hhi_div : (x.toNat &&& (2 ^ 64 - 1 - 7)) / 8 = x.toNat / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_div_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) / 2 ^ 3 = 2 ^ 61 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by have := x.isLt; omega)
  have heucl := Nat.div_add_mod (x.toNat &&& (2 ^ 64 - 1 - 7)) 8
  have heucl2 := Nat.div_add_mod x.toNat 8
  omega
theorem aligned_add (b k : Word) (hb : b.toNat % 8 = 0) :
    alignToDword (b + k) = b + alignToDword k ∧ byteOffset (b + k) = byteOffset k := by
  have hbl := b.isLt
  have hkl := k.isLt
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, BitVec.toNat_add, BitVec.toNat_add, alignToDword_toNat]
    omega
  · rw [byteOffset_eq, byteOffset_eq, BitVec.toNat_add]
    omega
theorem checkValid_sound {σ σ₁ : SymState} {a : Addr} {w : Nat} (h : checkValid σ a w = some σ₁)
    (s : MachineState) (hobl : ∀ o ∈ σ₁.obl, o.holds s) :
    accessValid (a.eval s) w = true ∧ σ₁.regs = σ.regs ∧ σ₁.mem = σ.mem ∧ σ.obl ⊆ σ₁.obl := by
  unfold checkValid at h
  split at h
  · rename_i hb
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h; subst h
      refine ⟨?_, rfl, rfl, List.Subset.refl _⟩
      simp only [Addr.eval, hb]; exact hv
    · cases h
  · rename_i b hb
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, SymState.addObl_regs _ _, SymState.addObl_mem _ _, SymState.addObl_sub _ _⟩
    exact hobl _ (SymState.addObl_mem_obl _ _)
theorem subKey_sound {σ σ₂ : SymState} {a key : Addr} {bo : Nat} (h : subKey σ a = (σ₂, key, bo))
    (s : MachineState) (hobl : ∀ o ∈ σ₂.obl, o.holds s) :
    key.eval s = alignToDword (a.eval s) ∧ bo = byteOffset (a.eval s) ∧
      σ₂.regs = σ.regs ∧ σ₂.mem = σ.mem ∧ σ.obl ⊆ σ₂.obl := by
  unfold subKey at h
  split at h
  · rename_i hb
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Addr.eval, hb]
  · rename_i b hb
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hal : (b.eval s).toNat % 8 = 0 := hobl _ (SymState.addObl_mem_obl _ _)
    have := aligned_add (b.eval s) a.off hal
    refine ⟨?_, ?_, SymState.addObl_regs _ _, SymState.addObl_mem _ _, SymState.addObl_sub _ _⟩
    · simp [Addr.eval, hb, this.1]
    · simp [Addr.eval, hb, this.2]
theorem Src.sym_eval (σ : SymState) (s : MachineState) (pc : Word) (a : Src) :
    (a.sym σ.regs pc).eval s = a.eval (σ.toState s pc) := by
  cases a <;> simp [Src.sym, Src.eval, E.eval]
theorem LoadKind.isD_iff (k : LoadKind) : k.isD = true ↔ k = .d := by cases k <;> simp [LoadKind.isD]
theorem StoreKind.isD_iff (k : StoreKind) : k.isD = true ↔ k = .d := by
  cases k <;> simp [StoreKind.isD]
def nextPc (s : MachineState) (pc : Word) : Option E → Word
  | none => pc + 4
  | some t => t.eval s
set_option maxHeartbeats 1000000 in
theorem symMicro_sound {cfg : Config} {pc : Word} {σ σ' : SymState} {m : Micro} {ctl : Option E}
    (h : symMicro cfg pc σ m = some (σ', ctl)) (s : MachineState)
    (hobl : ∀ o ∈ σ'.obl, o.holds s) :
    σ.obl ⊆ σ'.obl ∧ m.exec (σ.toState s pc) = some (σ'.toState s (nextPc s pc ctl)) := by
  cases m with
  | alu rd op a b =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, SymState.toState_pc, ← Src.sym_eval, ← mkBin_eval,
      SymState.toState_setReg, SymState.toState_setPC, nextPc]
  | load k rd rs off =>
    simp only [symMicro] at h
    split at h
    · cases h
    · rename_i σ₁ hcv
      have haddr : (norm (mkAdd (σ.regs.get rs) (.c off))).eval s =
          (σ.toState s pc).getReg rs + off := by
        rw [norm_eval, mkAdd_eval]; simp [E.eval]
      split at h
      ·
        rename_i hk
        have hk' : k = .d := (LoadKind.isD_iff k).mp hk
        subst hk'
        split at h
        · cases h
        · rename_i v os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub2 := SymState.addObls_sub σ₁ os
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl o (hsub2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₁ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 hsub2, ?_⟩
          rw [haddr, hm1] at hread
          rw [haddr] at hv
          simp only [Micro.exec, hv, if_true, LoadKind.read, SymState.toState_getMem,
            SymState.toState_pc]
          rw [hread, SymState.toState_setReg, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1]
          · simp [SymState.addObls_mem, hm1]
      ·
        rename_i hk
        have hk' : k ≠ .d := fun h' => hk ((LoadKind.isD_iff k).mpr h')
        generalize hsk : subKey σ₁ (norm (mkAdd (σ.regs.get rs) (E.c off))) = p at h
        obtain ⟨σ₂, key, bo⟩ := p
        simp only at h
        split at h
        · cases h
        · rename_i w os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub3 := SymState.addObls_sub σ₂ os
          have hobl2 : ∀ o ∈ σ₂.obl, o.holds s := fun o ho => hobl o (hsub3 ho)
          obtain ⟨hkey, hbo, hr2, hm2, hs2⟩ := subKey_sound hsk s hobl2
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl2 o (hs2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₂ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 (List.Subset.trans hs2 hsub3), ?_⟩
          rw [haddr] at hv hkey hbo
          rw [hkey, hm2, hm1] at hread
          simp only [Micro.exec, hv, if_true, SymState.toState_pc]
          rw [LoadKind.read_sub _ _ _ hk', SymState.toState_getMem, hread, ← hbo,
            show k.fromWord (w.eval s) bo = (mkUn (.ld k bo) w).eval s by rw [mkUn_eval]; rfl,
            SymState.toState_setReg, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1, hr2]
          · simp [SymState.addObls_mem, hm1, hm2]
  | store k rs1 rs2 off =>
    simp only [symMicro] at h
    split at h
    · cases h
    · rename_i σ₁ hcv
      have haddr : (norm (mkAdd (σ.regs.get rs1) (.c off))).eval s =
          (σ.toState s pc).getReg rs1 + off := by
        rw [norm_eval, mkAdd_eval]; simp [E.eval]
      split at h
      · rename_i hk
        have hk' : k = .d := (StoreKind.isD_iff k).mp hk
        subst hk'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl
        refine ⟨hs1, ?_⟩
        rw [haddr] at hv
        simp only [Micro.exec, hv, if_true, StoreKind.write, SymState.toState_pc]
        rw [← haddr, show (σ.toState s pc).getReg rs2 = (σ.regs.get rs2).eval s by simp,
          SymState.toState_setMem, SymState.toState_setPC]
        congr 1
        apply SymState.toState_congr
        · simp [hr1]
        · simp [memEval_writeMem, hm1]
      · rename_i hk
        have hk' : k ≠ .d := fun h' => hk ((StoreKind.isD_iff k).mpr h')
        generalize hsk : subKey σ₁ (norm (mkAdd (σ.regs.get rs1) (E.c off))) = p at h
        obtain ⟨σ₂, key, bo⟩ := p
        simp only at h
        split at h
        · cases h
        · rename_i old os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub3 := SymState.addObls_sub σ₂ os
          have hobl2 : ∀ o ∈ σ₂.obl, o.holds s := fun o ho => hobl o (hsub3 ho)
          obtain ⟨hkey, hbo, hr2, hm2, hs2⟩ := subKey_sound hsk s hobl2
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl2 o (hs2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₂ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 (List.Subset.trans hs2 hsub3), ?_⟩
          rw [haddr] at hv hkey hbo
          rw [hkey, hm2, hm1] at hread
          simp only [Micro.exec, hv, if_true, SymState.toState_pc]
          rw [StoreKind.write_sub _ _ _ _ hk', SymState.toState_getMem, hread, ← hbo, ← hkey,
            show k.merge (old.eval s) bo ((σ.toState s pc).getReg rs2) =
              (mkBin (.st k bo) old (σ.regs.get rs2)).eval s by rw [mkBin_eval]; simp; rfl,
            SymState.toState_setMem, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1, hr2]
          · simp [memEval_writeMem, SymState.addObls_mem, hm1, hm2]
  | branch op r1 r2 off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, mkIte_eval, SymState.toState_getReg, SymState.toState_pc,
      SymState.toState_setPC, E.eval]
  | jal rd off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, SymState.toState_pc, E.eval]
    rw [show pc + 4 = (E.c (pc + 4)).eval s from rfl, SymState.toState_setReg,
      SymState.toState_setPC]
    rfl
  | jalr rd rs off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, SymState.toState_pc, mkBin_eval, mkAdd_eval, E.eval,
      SymState.toState_getReg, BinOp.eval]
    rw [show pc + 4 = (E.c (pc + 4)).eval s from rfl, SymState.toState_setReg,
      SymState.toState_setPC]
    rfl
theorem getElem?_of_prefix_drop {l : List (BitVec 32)} {i : Nat} {w : BitVec 32}
    {ws : List (BitVec 32)} (h4 : w :: ws <+: List.drop i l) : l[i]? = some w := by
  obtain ⟨t, ht⟩ := h4
  have := congrArg (·[0]?) ht
  simp only [List.getElem?_drop, List.cons_append, List.getElem?_cons_zero, Nat.add_zero] at this
  exact this.symm
theorem CodeAt.fetch {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    (h : CodeAt image pc (w :: ws)) (t : MachineState) (ht : t.pc = pc) :
    fetch image t = decodeInstruction w := by
  obtain ⟨h1, h2, _, h4⟩ := h
  have hget : image.code[(pc.toNat - 0x1000) / 4]? = some w := getElem?_of_prefix_drop h4
  unfold Riscv.fetch
  rw [ht]
  have hc : (decide (pc.toNat < 0x1000) || pc.toNat % 4 != 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq]
    exact ⟨by omega, h2⟩
  simp only [hc, Bool.false_eq_true, if_false, hget]
  rfl
theorem CodeAt.tail {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    (h : CodeAt image pc (w :: ws)) : CodeAt image (pc + 4) ws := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.length_cons] at h3
  have hpc : (pc + 4).toNat = pc.toNat + 4 := by
    rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (pc.toNat + 4 - 0x1000) / 4 = (pc.toNat - 0x1000) / 4 + 1 by omega,
    ← List.drop_drop]
  obtain ⟨t, ht⟩ := h4
  rw [← ht]
  exact ⟨t, by simp⟩
theorem CodeAt.of_append {image : Image} {pre code post : List (BitVec 32)}
    (h : image.code = pre ++ code ++ post) (pc : Word)
    (hpc : pc.toNat = 0x1000 + 4 * pre.length)
    (hrange : 0x1000 + 4 * (pre.length + code.length) < 2 ^ 64) : CodeAt image pc code := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * pre.length - 0x1000) / 4 = pre.length by omega, h,
    List.append_assoc, List.drop_left]
  exact List.prefix_append _ _
theorem isEcall_eq {i : Instruction} (h : isEcall i = true) : i = .base .ECALL := by
  unfold isEcall at h; split at h <;> first | rfl | cases h
theorem symRunAux_sound (cfg : Config) (image : Image) (s : MachineState) :
    ∀ (code : List (BitVec 32)) (pc : Word) (fuel : Nat) (σ : SymState) (r : Result),
      symRunAux cfg code pc fuel σ = some r → CodeAt image pc code →
      (∀ o ∈ r.st.obl, o.holds s) →
      Steps image (σ.toState s pc) r.steps r.cycles (r.toState s) ∧ σ.obl ⊆ r.st.obl ∧
        (r.stop = .ecall → fetch image (r.toState s) = some (.base .ECALL)) := by
  intro code
  induction code with
  | nil =>
    intro pc fuel σ r h _ _
    cases fuel <;> simp only [symRunAux, Option.some.injEq] at h <;> subst h <;>
      exact ⟨Steps.refl _, List.Subset.refl _, by simp⟩
  | cons w ws ih =>
    intro pc fuel σ r h hcode hobl
    cases fuel with
    | zero =>
      simp only [symRunAux, Option.some.injEq] at h; subst h
      exact ⟨Steps.refl _, List.Subset.refl _, by simp⟩
    | succ f =>
      simp only [symRunAux] at h
      split at h
      · cases h
      · rename_i i hdec
        split at h
        · rename_i he
          simp only [Option.some.injEq] at h; subst h
          refine ⟨Steps.refl _, List.Subset.refl _, fun _ => ?_⟩
          rw [hcode.fetch _ rfl, hdec, isEcall_eq he]
        · split at h
          · cases h
          · rename_i m hcl
            split at h
            · cases h
            · rename_i σ' hm
              split at h
              · cases h
              · rename_i r' hr'
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨hsteps, hsub, hec⟩ := ih (pc + 4) f σ' r' hr' hcode.tail hobl
                obtain ⟨hsub', hexec⟩ := symMicro_sound hm s (fun o ho => hobl o (hsub ho))
                refine ⟨?_, List.Subset.trans hsub' hsub, hec⟩
                refine Steps.step ((hcode.fetch (σ.toState s pc) rfl).trans hdec) ?_ hsteps
                rw [classify_sound hcl, hexec]; rfl
            · rename_i σ' t hm
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨hsub', hexec⟩ := symMicro_sound hm s hobl
              refine ⟨?_, hsub', ?_⟩
              · refine Steps.step (i := i) ((hcode.fetch (σ.toState s pc) rfl).trans hdec) ?_ (Steps.refl _)
                rw [classify_sound hcl, hexec]; rfl
              · intro hst; cases m <;> cases hst
theorem symRun_sound {cfg : Config} {image : Image} {code : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg code pc fuel = some r)
    (hcode : CodeAt image pc code) (s : MachineState) (hpc : s.pc = pc) (hobl : r.obligs s) :
    Steps image s r.steps r.cycles (r.toState s) := by
  have := (symRunAux_sound cfg image s code pc fuel _ r hrun hcode
    ((Oblig.all_iff s _).mp hobl)).1
  rwa [← hpc, SymState.init_toState] at this
theorem symRun_ecall {cfg : Config} {image : Image} {code : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg code pc fuel = some r)
    (hcode : CodeAt image pc code) (s : MachineState) (hobl : r.obligs s)
    (hstop : r.stop = .ecall) : fetch image (r.toState s) = some (.base .ECALL) :=
  (symRunAux_sound cfg image s code pc fuel _ r hrun hcode ((Oblig.all_iff s _).mp hobl)).2.2 hstop
@[simp] theorem Result.toState_getReg (r : Result) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := by
  simp [Result.toState]
@[simp] theorem Result.toState_getMem (r : Result) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
@[simp] theorem Result.toState_pc (r : Result) (s : MachineState) :
    (r.toState s).pc = r.pc.eval s := rfl
@[simp] theorem Result.toState_code (r : Result) (s : MachineState) :
    (r.toState s).code = s.code := rfl
theorem Result.toState_getMem_of_read (r : Result) (s : MachineState) {cfg : Config} {k : Addr}
    {e : E} {os : List Oblig} (h : readMem cfg k r.st.mem = some (e, os))
    (hos : Oblig.all s os) : (r.toState s).getMem (k.eval s) = e.eval s :=
  readMem_sound h s ((Oblig.all_iff s _).mp hos)
theorem Result.toState_getMem_frame (r : Result) (s : MachineState) (a : Word)
    (h : ∀ p ∈ r.st.mem, a ≠ p.1.eval s) : (r.toState s).getMem a = s.getMem a :=
  memEval_frame s _ a h
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Hash ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
def wordsToNat : List Word → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * wordsToNat ws
def queryOfWords (n : Nat) (ws : List Word) : Query := ⟨n, BitVec.ofNat _ (wordsToNat ws)⟩
theorem wordsToNat_append_single (l : List Word) (w : Word) :
    wordsToNat (l ++ [w]) = wordsToNat l + 2 ^ (64 * l.length) * w.toNat := by
  induction l with
  | nil => simp [wordsToNat]
  | cons x xs ih =>
    simp only [List.cons_append, wordsToNat, ih, List.length_cons]
    rw [show 64 * (xs.length + 1) = 64 + 64 * xs.length by ring, Nat.pow_add]
    ring
theorem readWords_succ_last (t : MachineState) (base : Word) (m : Nat) :
    t.readWords base (m + 1) = t.readWords base m ++ [t.getMem (base + BitVec.ofNat 64 (8 * m))] := by
  induction m generalizing base with
  | zero => simp
  | succ m ih =>
    rw [MachineState.readWords_succ, ih (base + 8), MachineState.readWords_succ]
    simp only [List.cons_append, List.cons.injEq, List.append_cancel_left_eq, List.cons.injEq,
      and_true, true_and]
    congr 1
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
    omega
theorem readWords_length (t : MachineState) (base : Word) (m : Nat) :
    (t.readWords base m).length = m := by
  induction m generalizing base with
  | zero => rfl
  | succ m ih => simp [ih]
private theorem foldl_range_succ (g : Nat → Nat) (N : Nat) :
    (List.range (N + 1)).foldl (fun acc i => acc + g i) 0 =
      (List.range N).foldl (fun acc i => acc + g i) 0 + g N := by
  rw [List.range_succ, List.foldl_append]; rfl
private theorem extractByte_toNat (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
private theorem word_bytes (x : Nat) (hx : x < 2 ^ 64) :
    x / 2 ^ (8 * 0) % 256 * 2 ^ (8 * 0) + x / 2 ^ (8 * 1) % 256 * 2 ^ (8 * 1) +
      x / 2 ^ (8 * 2) % 256 * 2 ^ (8 * 2) + x / 2 ^ (8 * 3) % 256 * 2 ^ (8 * 3) +
      x / 2 ^ (8 * 4) % 256 * 2 ^ (8 * 4) + x / 2 ^ (8 * 5) % 256 * 2 ^ (8 * 5) +
      x / 2 ^ (8 * 6) % 256 * 2 ^ (8 * 6) + x / 2 ^ (8 * 7) % 256 * 2 ^ (8 * 7) = x := by
  simp only [Nat.reducePow, Nat.reduceMul]
  omega
private theorem getByte_aligned (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b : Nat) (hb : b < 8) (hi : 8 * m + b < 2 ^ 64) :
    t.getByte (src + BitVec.ofNat 64 (8 * m + b)) =
      extractByte (t.getMem (src + BitVec.ofNat 64 (8 * m))) b := by
  unfold MachineState.getByte
  obtain ⟨h1, h2⟩ := aligned_add src (BitVec.ofNat 64 (8 * m + b)) hal
  rw [h1, h2, byteOffset_eq]
  have hlt : (BitVec.ofNat 64 (8 * m + b)).toNat = 8 * m + b := by
    simp only [BitVec.toNat_ofNat]; omega
  congr 2
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hlt]
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [hlt]; omega
private theorem byte_term (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b i : Nat) (hb : b < 8) (hi : i = 8 * m + b) (hlt : i < 2 ^ 64) :
    (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i) =
      2 ^ (64 * m) * ((t.getMem (src + BitVec.ofNat 64 (8 * m))).toNat / 2 ^ (8 * b) % 256 *
        2 ^ (8 * b)) := by
  subst hi
  rw [getByte_aligned t src hal m b hb hlt, extractByte_toNat,
    show 8 * (8 * m + b) = 64 * m + 8 * b by ring, Nat.pow_add]
  ring
theorem hashInput_eq_words (t : MachineState) (n : Nat)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1))) (hn : 64 * (n + 1) < 2 ^ 64)
    (h10 : (t.getReg .x10).toNat % 8 = 0) :
    hashInput t = queryOfWords n (t.readWords (t.getReg .x10) (8 * (n + 1))) := by
  have hN : (t.getReg .x11).toNat / 64 - 1 = n := by
    rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
  generalize hsrc : t.getReg .x10 = src at h10
  have key : ∀ m, 8 * m ≤ 64 * (n + 1) →
      (List.range (8 * m)).foldl (fun acc i =>
        acc + (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0 =
        wordsToNat (t.readWords src m) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [show 8 * (m + 1) = 8 * m + 7 + 1 by omega]
      simp only [foldl_range_succ]
      rw [ih (by omega), readWords_succ_last, wordsToNat_append_single, readWords_length,
        byte_term t src h10 m 0 (8 * m) (by omega) (by omega) (by omega),
        byte_term t src h10 m 1 (8 * m + 1) (by omega) (by omega) (by omega),
        byte_term t src h10 m 2 (8 * m + 2) (by omega) (by omega) (by omega),
        byte_term t src h10 m 3 (8 * m + 3) (by omega) (by omega) (by omega),
        byte_term t src h10 m 4 (8 * m + 4) (by omega) (by omega) (by omega),
        byte_term t src h10 m 5 (8 * m + 5) (by omega) (by omega) (by omega),
        byte_term t src h10 m 6 (8 * m + 6) (by omega) (by omega) (by omega),
        byte_term t src h10 m 7 (8 * m + 6 + 1) (by omega) (by omega) (by omega)]
      generalize (t.getMem (src + BitVec.ofNat 64 (8 * m))) = w
      conv_rhs => rw [← word_bytes w.toNat w.isLt]
      ring
  have k := key (8 * (n + 1)) (by omega)
  rw [show 8 * (8 * (n + 1)) = 64 * (n + 1) by ring] at k
  unfold hashInput queryOfWords
  rw [hsrc]
  generalize (t.getReg .x11).toNat / 64 - 1 = N at hN ⊢
  subst hN
  simp only []
  rw [k]
end SigGolfCandidate.Rv
end
-- ==== merged from T3M_Bytes ====
section

set_option maxRecDepth 20000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (readLE pad64 zero16 header privateInput Cache cacheBytes Region)
open SphincsSecurity (bytesLE bytesLE_length)
@[simp] theorem readLE_nil : readLE [] = 0 := rfl
theorem readLE_inj : ∀ {l₁ l₂ : List UInt8}, l₁.length = l₂.length → readLE l₁ = readLE l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, h => by
    simp only [readLE_cons, List.length_cons, Nat.add_right_cancel_iff] at hl h
    have h1 : b₁.toNat < 256 := b₁.toNat_lt
    have h2 : b₂.toNat < 256 := b₂.toNat_lt
    have hb : b₁.toNat = b₂.toNat := by omega
    have hr : readLE l₁ = readLE l₂ := by omega
    rw [UInt8.toNat_inj.mp hb, readLE_inj hl hr]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
@[simp] theorem readLE_replicate_zero (n : Nat) : readLE (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, readLE_cons, ih]; rfl
theorem readLE_ofFn_digits : ∀ (n N : Nat),
    readLE (List.ofFn fun i : Fin n => UInt8.ofNat (N / 256 ^ i.val % 256)) = N % 256 ^ n
  | 0, N => by simp [Nat.mod_one]
  | n + 1, N => by
    rw [List.ofFn_succ, readLE_cons]
    have e : (fun i : Fin n => UInt8.ofNat (N / 256 ^ (i.succ : Fin (n + 1)).val % 256)) =
        fun i : Fin n => UInt8.ofNat (N / 256 / 256 ^ i.val % 256) := by
      funext i
      rw [Fin.val_succ, pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    rw [e, readLE_ofFn_digits n (N / 256), pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    simp
theorem readLE_bytesLE (n : Nat) (x : BitVec (8 * n)) : readLE (bytesLE n x) = x.toNat := by
  have e : bytesLE n x = List.ofFn fun i : Fin n => UInt8.ofNat (x.toNat / 256 ^ i.val % 256) := by
    unfold bytesLE
    congr 1; funext i
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, UInt8.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [show 256 ^ i.val = 2 ^ (8 * i.val) by rw [Nat.pow_mul]]
    omega
  rw [e, readLE_ofFn_digits, Nat.mod_eq_of_lt]
  have := x.isLt
  rwa [Nat.pow_mul] at this
theorem readLE_div_mod (l : List UInt8) (i : Nat) : readLE l / 256 ^ i % 256 = (l.getD i 0).toNat := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rcases i with _ | i
    · have := b.toNat_lt
      simp only [readLE_cons, pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    · rw [readLE_cons, pow_succ, Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul,
        show (b.toNat + 256 * readLE l) / 256 = readLE l by have := b.toNat_lt; omega, ih]
      simp
def toQ (l : List UInt8) : Query := ⟨l.length / 64 - 1, BitVec.ofNat _ (readLE l)⟩
def Aligned (l : List UInt8) : Prop := 0 < l.length ∧ l.length % 64 = 0
def ofQ (q : Query) : List UInt8 := bytesLE (64 * (q.1 + 1)) q.2
theorem aligned_len {l : List UInt8} (h : Aligned l) : 64 * (l.length / 64 - 1 + 1) = l.length := by
  obtain ⟨h0, h64⟩ := h
  have : 1 ≤ l.length / 64 := by omega
  rw [Nat.sub_add_cancel this]
  omega
theorem toQ_injOn : Set.InjOn toQ {l | Aligned l} := by
  intro l₁ h₁ l₂ h₂ h
  have hn : l₁.length / 64 - 1 = l₂.length / 64 - 1 := congrArg (fun q : Query => q.1) h
  have ht : (toQ l₁).2.toNat = (toQ l₂).2.toNat := congrArg (fun q : Query => q.2.toNat) h
  have e₁ := aligned_len h₁
  have e₂ := aligned_len h₂
  have hlen : l₁.length = l₂.length := by omega
  simp only [toQ, BitVec.toNat_ofNat] at ht
  rw [e₁, e₂] at ht
  have hp : ∀ l : List UInt8, (2 : Nat) ^ (8 * l.length) = 256 ^ l.length := fun l => by
    rw [pow_mul]; norm_num
  rw [hp, hp, Nat.mod_eq_of_lt (readLE_lt l₁), Nat.mod_eq_of_lt (readLE_lt l₂)] at ht
  exact readLE_inj hlen ht
theorem blocks_toQ {l : List UInt8} (h : Aligned l) : (toQ l).blocks = l.length / 64 := by
  have := aligned_len h
  unfold toQ Query.blocks
  dsimp only
  omega
theorem ofQ_length (q : Query) : (ofQ q).length = 64 * (q.1 + 1) := bytesLE_length _ _
theorem toQ_eq (l : List UInt8) (n : Nat) (hl : l.length = 64 * (n + 1)) :
    toQ l = ⟨n, BitVec.ofNat _ (readLE l)⟩ := by
  have hn : l.length / 64 - 1 = n := by rw [hl]; omega
  unfold toQ
  rw [hn]
theorem toQ_ofQ (q : Query) : toQ (ofQ q) = q := by
  obtain ⟨n, v⟩ := q
  rw [toQ_eq _ n (ofQ_length _), ofQ, readLE_bytesLE]
  simp
theorem ofQ_toQ {l : List UInt8} (h : Aligned l) : ofQ (toQ l) = l := by
  have e := aligned_len h
  apply readLE_inj
  · rw [ofQ_length]; exact e
  · unfold ofQ toQ
    rw [readLE_bytesLE]
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hl := readLE_lt l
    rw [show (2 : Nat) ^ (8 * (64 * (l.length / 64 - 1 + 1))) = 256 ^ l.length by
      rw [e, pow_mul]; norm_num]
    exact hl
def wordsOf : List UInt8 → List Word
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      BitVec.ofNat 64 (readLE [b0, b1, b2, b3, b4, b5, b6, b7]) :: wordsOf rest
  | _ => []
@[simp] theorem wordsOf_nil : wordsOf [] = [] := rfl
theorem wordsOf_append8 (l rest : List UInt8) (hl : l.length = 8) :
    wordsOf (l ++ rest) = BitVec.ofNat 64 (readLE l) :: wordsOf rest := by
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl
theorem wordsOf_append (l₁ l₂ : List UInt8) (h : l₁.length % 8 = 0) :
    wordsOf (l₁ ++ l₂) = wordsOf l₁ ++ wordsOf l₂ := by
  obtain ⟨n, hn⟩ : ∃ n, l₁.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing l₁ with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      rw [List.length_eq_zero_iff] at hn
      subst hn; rfl
    · have ht : (l₁.take 8).length = 8 := by simp; omega
      rw [← List.take_append_drop 8 l₁, List.append_assoc,
        wordsOf_append8 (l₁.take 8) (l₁.drop 8 ++ l₂) ht, wordsOf_append8 (l₁.take 8) (l₁.drop 8) ht,
        ih (n - 8) (by omega) (l₁.drop 8) (by simp; omega) (by simp; omega)]
      rfl
theorem wordsOf_eq_range : ∀ (m : Nat) (l : List UInt8), l.length = 8 * m →
    wordsOf l = (List.range m).map fun j => BitVec.ofNat 64 (readLE l / 2 ^ (64 * j))
  | 0, l, h => by
    rw [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | m + 1, l, h => by
    have hl : l = l.take 8 ++ l.drop 8 := (List.take_append_drop 8 l).symm
    have ht : (l.take 8).length = 8 := by simp; omega
    have hd : (l.drop 8).length = 8 * m := by simp; omega
    have hr : readLE l = readLE (l.take 8) + 2 ^ 64 * readLE (l.drop 8) := by
      conv_lhs => rw [hl]
      rw [readLE_append, ht]; norm_num
    have hlt : readLE (l.take 8) < 2 ^ 64 := by
      have := readLE_lt (l.take 8); rw [ht] at this; norm_num at this ⊢; exact this
    rw [hl, wordsOf_append8 _ _ ht, ← hl, wordsOf_eq_range m _ hd, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.mul_zero, pow_zero, Nat.div_one, hr]
      omega
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp, hr]
      congr 1
      rw [show 64 * (j + 1) = 64 + 64 * j by ring, pow_add, ← Nat.div_div_eq_div_mul]
      congr 1
      omega
theorem length_wordsOf (m : Nat) (l : List UInt8) (h : l.length = 8 * m) : (wordsOf l).length = m := by
  rw [wordsOf_eq_range m l h]; simp
theorem wordsToNat_wordsOf : ∀ (m : Nat) (l : List UInt8), l.length = 8 * m →
    wordsToNat (wordsOf l) = readLE l
  | 0, l, h => by
    rw [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | m + 1, l, h => by
    have hl : l = l.take 8 ++ l.drop 8 := (List.take_append_drop 8 l).symm
    have ht : (l.take 8).length = 8 := by simp; omega
    have hd : (l.drop 8).length = 8 * m := by simp; omega
    have hlt : readLE (l.take 8) < 2 ^ 64 := by
      have := readLE_lt (l.take 8); rw [ht] at this; norm_num at this ⊢; exact this
    rw [hl, wordsOf_append8 _ _ ht, wordsToNat, wordsToNat_wordsOf m _ hd, readLE_append, ht,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    norm_num
theorem wordsOf_bytesLE (m : Nat) (x : BitVec (8 * (8 * m))) :
    wordsOf (bytesLE (8 * m) x) = (List.range m).map fun j => x.extractLsb' (64 * j) 64 := by
  rw [wordsOf_eq_range m _ (bytesLE_length _ _), readLE_bytesLE]
  apply List.map_congr_left
  intro j _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem wordsOf_bytesLE16 (x : BitVec 128) :
    wordsOf (bytesLE 16 x) = [x.extractLsb' 0 64, x.extractLsb' 64 64] :=
  wordsOf_bytesLE 2 x
theorem wordsOf_bytesLE32 (x : BitVec 256) :
    wordsOf (bytesLE 32 x) =
      [x.extractLsb' 0 64, x.extractLsb' 64 64, x.extractLsb' 128 64, x.extractLsb' 192 64] :=
  wordsOf_bytesLE 4 x
@[simp] theorem wordsOf_zero16 : wordsOf zero16 = [0, 0] := rfl
theorem wordsOf_replicate_zero (m : Nat) : wordsOf (List.replicate (8 * m) 0) = List.replicate m 0 := by
  rw [wordsOf_eq_range m _ (by simp), readLE_replicate_zero]
  apply List.ext_getElem (by simp)
  intro i _ _
  simp
theorem wordsOf_flatMap16 (ds : List (BitVec 128)) :
    wordsOf (ds.flatMap (bytesLE 16)) = ds.flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by rw [bytesLE_length]),
      wordsOf_bytesLE16, ih]
def hdr0 (tag lay tree position : Nat) : Nat :=
  1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + tree / 2 ^ 32 % 256 * 2 ^ 24 + position % 2 ^ 32 * 2 ^ 32
def hdr1 (tree index : Nat) : Nat := tree % 2 ^ 32 + index % 2 ^ 32 * 2 ^ 32
theorem hdr0_lt (tag lay tree position : Nat) : hdr0 tag lay tree position < 2 ^ 64 := by
  unfold hdr0
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  have := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  omega
theorem hdr1_lt (tree index : Nat) : hdr1 tree index < 2 ^ 64 := by
  unfold hdr1
  have := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  omega
theorem nodeWord_3 (position index : Nat) : T3.nodeWord 3 position index = hdr1 index position := by
  simp [T3.nodeWord, T3.revNodeTag, hdr1]
theorem nodeWord_10 (position index : Nat) :
    T3.nodeWord 10 position index = T3.Rev.revBits 64 (hdr1 index position) := by
  simp [T3.nodeWord, T3.revNodeTag, hdr1]
theorem nodeWord_9 (position index : Nat) :
    T3.nodeWord 9 position index = T3.Rev.revBits 64 (hdr1 (index % 2 ^ 32 ^^^ 2048) position) := by
  have hx : index % 2 ^ 32 ^^^ 2048 < 2 ^ 32 := Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by decide)
  simp only [T3.nodeWord, T3.revNodeTag, hdr1, Nat.mod_eq_of_lt hx]
  norm_num
theorem header_toNat (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat =
      if T3.packedNodeTag tag then hdr0 tag lay tree tree + 2 ^ 64 * T3.nodeWord tag position index
      else hdr0 tag lay tree position + 2 ^ 64 * hdr1 tree index := by
  unfold header hdr0 hdr1
  rw [BitVec.toNat_ofNat]
  have ht := Nat.mod_lt tag (by decide : 0 < 256)
  have hl := Nat.mod_lt lay (by decide : 0 < 256)
  have hth := Nat.mod_lt (tree / 2 ^ 32) (by decide : 0 < 256)
  have hp := Nat.mod_lt position (by decide : 0 < 2 ^ 32)
  have htl := Nat.mod_lt tree (by decide : 0 < 2 ^ 32)
  have hi := Nat.mod_lt index (by decide : 0 < 2 ^ 32)
  have hw := T3.nodeWord_lt tag position index
  split_ifs <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
theorem header_lo (tag lay tree position index : Nat) :
    (header tag lay tree position index).extractLsb' 0 64 =
      BitVec.ofNat 64 (if T3.packedNodeTag tag then hdr0 tag lay tree tree else hdr0 tag lay tree position) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := hdr0_lt tag lay tree position
  have hp := hdr0_lt tag lay tree tree
  have h1 := hdr1_lt tree index
  have hq := T3.nodeWord_lt tag position index
  rw [BitVec.extractLsb'_toNat, header_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  split_ifs <;> omega
theorem header_hi (tag lay tree position index : Nat) :
    (header tag lay tree position index).extractLsb' 64 64 =
      BitVec.ofNat 64 (if T3.packedNodeTag tag then T3.nodeWord tag position index else hdr1 tree index) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := hdr0_lt tag lay tree position
  have hp := hdr0_lt tag lay tree tree
  have h1 := hdr1_lt tree index
  have hq := T3.nodeWord_lt tag position index
  rw [BitVec.extractLsb'_toNat, header_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split_ifs <;> omega
theorem wordsOf_header (tag lay tree position index : Nat) :
    wordsOf (bytesLE 16 (header tag lay tree position index)) =
      [BitVec.ofNat 64 (if T3.packedNodeTag tag then hdr0 tag lay tree tree else hdr0 tag lay tree position),
       BitVec.ofNat 64 (if T3.packedNodeTag tag then T3.nodeWord tag position index else hdr1 tree index)] := by
  rw [wordsOf_bytesLE16, header_lo, header_hi]
theorem header_packed_lo (tag lay tree position index : Nat)
    (hn : T3.packedNodeTag tag := by decide) :
    (header tag lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 tag lay tree tree) := by
  rw [header_lo, if_pos hn]
theorem header_packed_hi (tag lay tree position index : Nat)
    (hn : T3.packedNodeTag tag := by decide) :
    (header tag lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (T3.nodeWord tag position index) := by
  rw [header_hi, if_pos hn]
theorem header_packed_lo_3 (lay tree position index : Nat) :
    (header 3 lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 3 lay tree tree) :=
  header_packed_lo 3 lay tree position index (by decide)
theorem header_packed_hi_3 (lay tree position index : Nat) :
    (header 3 lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (hdr1 index position) := by
  rw [header_packed_hi 3 lay tree position index (by decide), nodeWord_3]
theorem header_packed_lo_9 (lay tree position index : Nat) :
    (header 9 lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 9 lay tree tree) :=
  header_packed_lo 9 lay tree position index (by decide)
theorem header_packed_hi_9 (lay tree position index : Nat) :
    (header 9 lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (T3.nodeWord 9 position index) :=
  header_packed_hi 9 lay tree position index (by decide)
theorem header_packed_lo_10 (lay tree position index : Nat) :
    (header 10 lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 10 lay tree tree) :=
  header_packed_lo 10 lay tree position index (by decide)
theorem header_packed_hi_10 (lay tree position index : Nat) :
    (header 10 lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (T3.nodeWord 10 position index) :=
  header_packed_hi 10 lay tree position index (by decide)
theorem wordsOf_packed_header (tag lay tree position index : Nat)
    (hn : T3.packedNodeTag tag := by decide) :
    wordsOf (bytesLE 16 (header tag lay tree position index)) =
      [BitVec.ofNat 64 (hdr0 tag lay tree tree), BitVec.ofNat 64 (T3.nodeWord tag position index)] := by
  rw [wordsOf_bytesLE16, header_packed_lo _ _ _ _ _ hn, header_packed_hi _ _ _ _ _ hn]
theorem wordsOf_packed_header_3 (lay tree position index : Nat) :
    wordsOf (bytesLE 16 (header 3 lay tree position index)) =
      [BitVec.ofNat 64 (hdr0 3 lay tree tree), BitVec.ofNat 64 (hdr1 index position)] := by
  rw [wordsOf_packed_header 3 lay tree position index (by decide), nodeWord_3]
theorem hdr0_eq (tag lay tree position : Nat) (ht : tag < 256) (hl : lay < 256) (htr : tree < 2 ^ 32)
    (hp : position < 2 ^ 32) :
    hdr0 tag lay tree position = 1 + 256 * tag + 65536 * lay + 2 ^ 32 * position := by
  unfold hdr0
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hp, Nat.div_eq_of_lt htr]
  omega
theorem hdr1_eq (tree index : Nat) (htr : tree < 2 ^ 32) (hi : index < 2 ^ 32) :
    hdr1 tree index = tree + 2 ^ 32 * index := by
  unfold hdr1
  rw [Nat.mod_eq_of_lt htr, Nat.mod_eq_of_lt hi]
  omega
theorem pad64_of_aligned (l : List UInt8) (h : l.length % 64 = 0) : pad64 l = l := by
  unfold pad64; rw [h]; simp
theorem pad64_length (l : List UInt8) : (pad64 l).length = l.length + (64 - l.length % 64) % 64 := by
  simp [pad64]
theorem pad64_aligned (l : List UInt8) (h : 0 < l.length) : Aligned (pad64 l) := by
  rw [Aligned, pad64_length]; omega
theorem sk_words (sk : BitVec 256) :
    (sk.extractLsb' 0 128).extractLsb' 0 64 = sk.extractLsb' 0 64 ∧
    (sk.extractLsb' 0 128).extractLsb' 64 64 = sk.extractLsb' 64 64 ∧
    (sk.extractLsb' 128 128).extractLsb' 0 64 = sk.extractLsb' 128 64 ∧
    (sk.extractLsb' 128 128).extractLsb' 64 64 = sk.extractLsb' 192 64 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] <;>
    norm_num <;> omega
theorem privateInput_tweak (sk : BitVec 256) (tw : BitVec 128) :
    privateInput sk (.inl tw) = bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 tw ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 := by
  show pad64 (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 tw ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++ []) = _
  rw [List.append_nil, pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length]; rfl)]
theorem wordsOf_privateInput_tweak (sk : BitVec 256) (tw : BitVec 128) :
    wordsOf (privateInput sk (.inl tw)) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, tw.extractLsb' 0 64, tw.extractLsb' 64 64,
        sk.extractLsb' 128 64, sk.extractLsb' 192 64, 0, 0] := by
  obtain ⟨h1, h2, h3, h4⟩ := sk_words sk
  rw [privateInput_tweak, wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16, h1, h2, h3, h4]
  rfl
theorem privateInput_tweak_length (sk : BitVec 256) (tw : BitVec 128) :
    (privateInput sk (.inl tw)).length = 64 := by
  rw [privateInput_tweak]; simp [bytesLE_length, zero16]
theorem privateInput_mac_eq (sk : BitVec 256) (region : Region) :
    privateInput sk (.inr (.inr region)) = bytesLE 16 (sk.extractLsb' 0 128) ++
      bytesLE 16 (header 14 0 0 0 0) ++ bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++
      List.ofFn region ++ List.replicate 32 0 := by
  simp only [privateInput, pad64, List.length_append, bytesLE_length, zero16, List.length_replicate,
    List.length_ofFn]
theorem privateInput_mac_length (sk : BitVec 256) (region : Region) :
    (privateInput sk (.inr (.inr region))).length = 131136 := by
  rw [privateInput_mac_eq]
  simp only [List.length_append, bytesLE_length, List.length_ofFn, List.length_replicate, zero16]
theorem privateInput_nonce_eq (sk : BitVec 256) (m : T3.Message) :
    privateInput sk (.inr (.inl m)) = bytesLE 16 (sk.extractLsb' 0 128) ++
      bytesLE 16 (header 7 0 0 0 0) ++ bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++
      bytesLE 32 m ++ List.replicate 32 0 := by
  simp only [privateInput, pad64, List.length_append, bytesLE_length, zero16, List.length_replicate]
theorem privateInput_aligned (sk : BitVec 256) (c : T3.Coordinate) : Aligned (privateInput sk c) := by
  rcases c with tw | m | region
  · rw [Aligned, privateInput_tweak_length]; omega
  · rw [Aligned, privateInput_nonce_eq]
    simp only [List.length_append, bytesLE_length, List.length_replicate, zero16]; decide
  · rw [Aligned, privateInput_mac_length]; omega
theorem hashInput_toQ (t : MachineState) (l : List UInt8) (n A : Nat)
    (hl : l.length = 64 * (n + 1)) (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A < 2 ^ 64) (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1)))
    (hn : 64 * (n + 1) < 2 ^ 64)
    (hw : t.readWords (BitVec.ofNat 64 A) (8 * (n + 1)) = wordsOf l) : hashInput t = toQ l := by
  rw [hashInput_eq_words t n h11 hn (by rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA']; exact hA),
    h10, hw, queryOfWords, wordsToNat_wordsOf (8 * (n + 1)) l (by rw [hl]; ring)]
  have hn' : l.length / 64 - 1 = n := by rw [hl]; omega
  unfold toQ
  rw [hn']
theorem readWords_add (t : MachineState) (A m₁ m₂ : Nat) :
    t.readWords (BitVec.ofNat 64 A) (m₁ + m₂) =
      t.readWords (BitVec.ofNat 64 A) m₁ ++ t.readWords (BitVec.ofNat 64 (A + 8 * m₁)) m₂ := by
  induction m₁ generalizing A with
  | zero => simp
  | succ m ih =>
    have e : BitVec.ofNat 64 A + 8 = BitVec.ofNat 64 (A + 8) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [show m + 1 + m₂ = (m + m₂) + 1 by omega, MachineState.readWords_succ,
      MachineState.readWords_succ, e, ih]
    simp only [List.cons_append]
    rw [show A + 8 + 8 * m = A + 8 * (m + 1) by ring]
theorem readWords_one (t : MachineState) (A : Nat) :
    t.readWords (BitVec.ofNat 64 A) 1 = [t.getMem (BitVec.ofNat 64 A)] := rfl
theorem readWords_two (t : MachineState) (A : Nat) :
    t.readWords (BitVec.ofNat 64 A) 2 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8))] := by
  have := readWords_add t A 1 1
  rw [readWords_one, readWords_one] at this
  simpa using this
private theorem foldl_range_succ (g : Nat → Nat) (N : Nat) :
    (List.range (N + 1)).foldl (fun acc i => acc + g i) 0 =
      (List.range N).foldl (fun acc i => acc + g i) 0 + g N := by
  rw [List.range_succ, List.foldl_append]; rfl
private theorem extractByte_toNat (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
private theorem word_bytes (x : Nat) (hx : x < 2 ^ 64) :
    x / 2 ^ (8 * 0) % 256 * 2 ^ (8 * 0) + x / 2 ^ (8 * 1) % 256 * 2 ^ (8 * 1) +
      x / 2 ^ (8 * 2) % 256 * 2 ^ (8 * 2) + x / 2 ^ (8 * 3) % 256 * 2 ^ (8 * 3) +
      x / 2 ^ (8 * 4) % 256 * 2 ^ (8 * 4) + x / 2 ^ (8 * 5) % 256 * 2 ^ (8 * 5) +
      x / 2 ^ (8 * 6) % 256 * 2 ^ (8 * 6) + x / 2 ^ (8 * 7) % 256 * 2 ^ (8 * 7) = x := by
  simp only [Nat.reducePow, Nat.reduceMul]
  omega
private theorem getByte_aligned (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b : Nat) (hb : b < 8) (hi : 8 * m + b < 2 ^ 64) :
    t.getByte (src + BitVec.ofNat 64 (8 * m + b)) =
      extractByte (t.getMem (src + BitVec.ofNat 64 (8 * m))) b := by
  unfold MachineState.getByte
  obtain ⟨h1, h2⟩ := aligned_add src (BitVec.ofNat 64 (8 * m + b)) hal
  rw [h1, h2, byteOffset_eq]
  have hlt : (BitVec.ofNat 64 (8 * m + b)).toNat = 8 * m + b := by
    simp only [BitVec.toNat_ofNat]; omega
  congr 2
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hlt]
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [hlt]; omega
private theorem byte_term (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b i : Nat) (hb : b < 8) (hi : i = 8 * m + b) (hlt : i < 2 ^ 64) :
    (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i) =
      2 ^ (64 * m) * ((t.getMem (src + BitVec.ofNat 64 (8 * m))).toNat / 2 ^ (8 * b) % 256 *
        2 ^ (8 * b)) := by
  subst hi
  rw [getByte_aligned t src hal m b hb hlt, extractByte_toNat,
    show 8 * (8 * m + b) = 64 * m + 8 * b by ring, Nat.pow_add]
  ring
theorem foldl_bytes_eq_words (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0) :
    ∀ m, 8 * m < 2 ^ 64 →
      (List.range (8 * m)).foldl (fun acc i =>
        acc + (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0 =
        wordsToNat (t.readWords src m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [show 8 * (m + 1) = 8 * m + 7 + 1 by omega]
    simp only [foldl_range_succ]
    rw [ih (by omega), readWords_succ_last, wordsToNat_append_single, readWords_length,
      byte_term t src hal m 0 (8 * m) (by omega) (by omega) (by omega),
      byte_term t src hal m 1 (8 * m + 1) (by omega) (by omega) (by omega),
      byte_term t src hal m 2 (8 * m + 2) (by omega) (by omega) (by omega),
      byte_term t src hal m 3 (8 * m + 3) (by omega) (by omega) (by omega),
      byte_term t src hal m 4 (8 * m + 4) (by omega) (by omega) (by omega),
      byte_term t src hal m 5 (8 * m + 5) (by omega) (by omega) (by omega),
      byte_term t src hal m 6 (8 * m + 6) (by omega) (by omega) (by omega),
      byte_term t src hal m 7 (8 * m + 6 + 1) (by omega) (by omega) (by omega)]
    generalize (t.getMem (src + BitVec.ofNat 64 (8 * m))) = w
    conv_rhs => rw [← word_bytes w.toNat w.isLt]
    ring
theorem readBuffer_of_words (t : MachineState) (A m : Nat) (l : List UInt8) (hA : A % 8 = 0)
    (hA' : A + 8 * m < 2 ^ 64) (hl : l.length = 8 * m)
    (hw : t.readWords (BitVec.ofNat 64 A) m = wordsOf l) :
    readBuffer t A (8 * m) = BitVec.ofNat _ (readLE l) := by
  unfold readBuffer
  have e : ∀ i, BitVec.ofNat 64 (A + i) = BitVec.ofNat 64 A + BitVec.ofNat 64 i := fun i => by
    apply BitVec.eq_of_toNat_eq; simp
  simp only [e]
  rw [foldl_bytes_eq_words t _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega)]; exact hA) m
    (by omega), hw, wordsToNat_wordsOf m l hl]
def cacheB (c : SigGolfCandidate.T3.Cache) : Bytes 131072 := BitVec.ofNat _ (readLE (cacheBytes c))
def cacheDec (b : Bytes 131072) : SigGolfCandidate.T3.Cache :=
  ⟨b.extractLsb' 0 256, fun i => UInt8.ofNat (b.toNat / 256 ^ (32 + i.val) % 256)⟩
theorem cacheBytes_length (c : SigGolfCandidate.T3.Cache) : (cacheBytes c).length = 131072 := by
  simp only [cacheBytes, List.length_append, bytesLE_length, List.length_ofFn]
theorem two_pow_eight_mul (n : Nat) : (2 : Nat) ^ (8 * n) = 256 ^ n := by
  rw [pow_mul]; norm_num
theorem readLE_cacheBytes_lt (c : SigGolfCandidate.T3.Cache) : readLE (cacheBytes c) < 2 ^ (8 * 131072) := by
  have := readLE_lt (cacheBytes c)
  rwa [cacheBytes_length, ← two_pow_eight_mul] at this
theorem cacheDec_cacheB (c : SigGolfCandidate.T3.Cache) : cacheDec (cacheB c) = c := by
  obtain ⟨tag, region⟩ := c
  have hlt := readLE_cacheBytes_lt ⟨tag, region⟩
  have hr : readLE (cacheBytes ⟨tag, region⟩) = tag.toNat + 256 ^ 32 * readLE (List.ofFn region) := by
    rw [cacheBytes, readLE_append, readLE_bytesLE, bytesLE_length]
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num
  have htag : tag.toNat < 256 ^ 32 := by have := tag.isLt; rwa [h256] at this
  unfold cacheDec cacheB
  refine congrArg₂ SigGolfCandidate.T3.Cache.mk ?_ ?_
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.shiftRight_zero, hr,
      h256, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htag]
  · funext i
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, pow_add, ← Nat.div_div_eq_div_mul,
      hr, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt htag, Nat.zero_add, readLE_div_mod]
    have hi := (region i).toNat_lt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
    simp
theorem cacheB_cacheDec (b : Bytes 131072) : cacheB (cacheDec b) = b := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have e2 : (256 : Nat) ^ 131072 = 256 ^ 131040 * 256 ^ 32 := (pow_add 256 131040 32 : _)
  have hb' : b.toNat < 256 ^ 131040 * 256 ^ 32 := by
    have h := hb
    rw [two_pow_eight_mul, e2] at h; exact h
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num
  have h3 : b.toNat / 256 ^ 32 < 256 ^ 131040 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr hb'
  unfold cacheB cacheDec cacheBytes
  rw [BitVec.toNat_ofNat, readLE_append, readLE_bytesLE, bytesLE_length]
  have e : List.ofFn (fun i : Fin 131040 => UInt8.ofNat (b.toNat / 256 ^ (32 + i.val) % 256)) =
      List.ofFn fun i : Fin 131040 => UInt8.ofNat (b.toNat / 256 ^ 32 / 256 ^ i.val % 256) := by
    exact congrArg List.ofFn (funext fun i => by rw [pow_add, Nat.div_div_eq_div_mul])
  rw [e, readLE_ofFn_digits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, h256, Nat.mod_eq_of_lt h3,
    Nat.mod_add_div]
  exact Nat.mod_eq_of_lt hb
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Extract_Normalize ====
section

namespace SigGolfCandidate.T3M.Extract
open SigGolfCandidate.T3
def canonicalHeader (hdr : HashInput) : HashInput :=
  if 128 ≤ (hdr.getD 0 0).toNat then hdr.take 8 ++ List.replicate 8 0 else hdr
@[simp] theorem canonicalHeader_unmarked (hdr : HashInput) (h : ¬128 ≤ (hdr.getD 0 0).toNat) :
    canonicalHeader hdr = hdr := by
  unfold canonicalHeader
  rw [if_neg h]
theorem canonicalHeader_marked (low pad : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = low ++ List.replicate 8 0 := by
  have hm : 128 ≤ ((low ++ pad).getD 0 0).toNat := by
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hmark
  unfold canonicalHeader
  rw [if_pos hm]
  simp [List.take_append, hlen]
theorem canonicalHeader_pad_irrelevant (low pad pad' : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = canonicalHeader (low ++ pad') := by
  rw [canonicalHeader_marked low pad hlen hmark, canonicalHeader_marked low pad' hlen hmark]
theorem canonicalHeader_zero_pad (low : HashInput) (hlen : low.length = 8) :
    canonicalHeader (low ++ List.replicate 8 0) = low ++ List.replicate 8 0 := by
  by_cases hm : 128 ≤ (low.getD 0 0).toNat
  · exact canonicalHeader_marked low _ hlen hm
  · apply canonicalHeader_unmarked
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hm
end SigGolfCandidate.T3M.Extract
end
-- ==== merged from T3M_Extract_Basic ====
section

namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd)
open SphincsSecurity (bytesLE)
noncomputable def honestRoot (answers : Answers) (lay : Layer) (tree : Nat) : Digest :=
  treeValue (builtTree answers lay tree) (height lay) 0
def ftsLevels (answers : Answers) (index coord : Nat) : List (List Digest) :=
  (evalWithAnswerFn answers (buildFts index coord)).1
def ftsSecret (answers : Answers) (index coord leaf : Nat) : Digest :=
  (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0
def ftsRoot (answers : Answers) (index coord : Nat) : Digest := treeValue (ftsLevels answers index coord) 11 0
def ftsRootsHonest (answers : Answers) (index : Nat) : List Digest := (List.range 7).map (ftsRoot answers index)
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  T3.leafInput lay tree leaf ends
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  listInput (roots.getD 0 0) (header 11 0 index 0 0) (roots.drop 1)
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (forestPk index (ftsRootsHonest answers index))
noncomputable def honestMsg (answers : Answers) (index : Nat) (lay : Layer) : Digest :=
  if h : lay.val < 3 then honestRoot answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2
  else honestForest answers index
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | ftsLeaf (index coord leaf : Nat)
  | ftsNode (index coord level node : Nat)
noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .chain lay tree leaf i step => pad64 (chainInput lay tree leaf i step
      (honestChainValue answers lay tree leaf i (leafSeed answers lay tree leaf i) step))
  | .leaf lay tree leaf => pad64 (leafInput lay tree leaf
      ((List.range (chainCount lay)).map (leafEnd answers lay tree leaf)))
  | .node lay tree level node => pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - level - 1) + node)
      (treeValue (builtTree answers lay tree) level (2 * node)) 0
      (treeValue (builtTree answers lay tree) level (2 * node + 1)))
  | .forest index => pad64 (forestInput index (ftsRootsHonest answers index))
  | .ftsLeaf index coord leaf => pad64 (ftsLeafInputP index coord leaf 0 (ftsSecret answers index coord leaf) 0)
  | .ftsNode index coord level node => pad64 (nodeInputP 10 coord index (2 ^ (11 - level - 1) + node)
      (treeValue (ftsLevels answers index coord) level (2 * node)) 0
      (treeValue (ftsLevels answers index coord) level (2 * node + 1)))
def Pos.hdr : Pos → BitVec 128
  | .chain lay tree lf i step => chainHeader lay tree lf i step
  | .leaf lay tree lf => leafTweak lay tree lf
  | .node lay tree level nd => nodeTweak 3 lay.val tree (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 11 0 index 0 0
  | .ftsLeaf index coord lf => header 9 coord index 0 lf
  | .ftsNode index coord level nd => header 10 coord index 0 (2 ^ (11 - level - 1) + nd)
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 31 ∧ lf < 4096 ∧ i < 64 ∧ step < 8
  | .leaf lay tree lf => lf < 2 ^ height lay ∧ tree * 2 ^ height lay + lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 32 ∧ (lay = 0 → tree = 0) ∧ level < height lay ∧
      nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .ftsLeaf index coord lf => coord < 256 ∧ index < 2 ^ 40 ∧ lf < 2 ^ 32
  | .ftsNode index coord level nd => coord < 256 ∧ index < 2 ^ 40 ∧ level < 11 ∧ nd < 2 ^ (11 - level - 1)
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
def SameHeader (actual honest : HashInput) : Prop :=
  canonicalHeader (hdrBlock actual) = canonicalHeader (hdrBlock honest)
def HitIn (answers : Answers) (qs : List Spec.Domain) : Prop :=
  ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ HashHit answers (honestInput answers pos) actual ∧
    SameHeader actual (honestInput answers pos)
theorem HitIn.mono {answers : Answers} {qs qs' : List Spec.Domain} (h : HitIn answers qs)
    (hsub : ∀ q ∈ qs, q ∈ qs') : HitIn answers qs' := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  exact ⟨pos, actual, hb, hsub _ hq, hh, hs⟩
theorem HitIn.append_left {answers : Answers} {qs : List Spec.Domain} (qs' : List Spec.Domain)
    (h : HitIn answers qs) : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_left _ hq
theorem HitIn.append_right {answers : Answers} {qs' : List Spec.Domain} (qs : List Spec.Domain)
    (h : HitIn answers qs') : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_right _ hq
def ftsRoots (w : WBytes) (index : Nat) (chosen : List Selection) : M (Option (List Digest × Nat)) :=
  (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, ptr) := state | pure none
      let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
      pure (some (roots ++ [root], ptr))) (some ([], streamBase))
theorem ftsP_eq (w : WBytes) (index : Nat) (chosen : List Selection) :
    ftsP w index chosen = (do
      let state ← ftsRoots w index chosen
      let some (roots, ptr) := state | pure none
      if streamEnd < ptr then return none
      pure (some (← forestPk index roots))) := rfl
/-- Kept from the deleted legacy `Extract.Layer` and `Extract.VerifyP` (C4, D6). -/
theorem height_le (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
end SigGolfCandidate.T3M.Extract
end
