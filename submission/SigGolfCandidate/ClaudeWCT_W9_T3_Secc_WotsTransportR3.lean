import SigGolfCandidate.T3_Secc_WotsTransportR3
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsReference
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_SeccLaw
set_option Elab.async false

namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem offlineInteraction_pure (T : Answers) (published : T3.Cache) {α : Type} (value : α) :
    offlineInteraction T published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, []) := rfl
theorem offlineInteraction_world (T : Answers) (published : T3.Cache) {α : Type}
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) =
      (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind', WriterT.run_liftM, bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem offlineInteraction_request (T : Answers) (published : T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (offlineSign T published request >>= fun answer =>
        (fun result => (result.1, ⟨request, answer⟩ :: result.2)) <$> offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr]
  simp
theorem authenticatedSign_hashOnly (published : T3.Cache) (request : Request) :
    Security.SourceReplay.HashOnly (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SourceReplay.IsHash
  · exact SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) request.cache.region
  · intro tag
    rcases Classical.em (request.cache = published) with h | h
    · rw [if_pos h]
      exact ClaudeWCT.W9.T3.Security.Signer.signPayload_hashOnly request.cache request.message
    · rw [if_neg h]
      exact SourceQueries.pure_allowed _ _
theorem interaction_counted (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
        (FullGame.loggedWith (FullGame.authenticatedSign published) program)) =
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged (offlineInteraction T published program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with input | request
      · rw [FullGame.loggedWith_world, offlineInteraction_world]
        change simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
          (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer))) = _
        rw [SphincsSecurity.QueryCap.counted_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
        rcases input with n | x
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
      · rw [FullGame.loggedWith_request, offlineInteraction_request]
        rw [SphincsSecurity.QueryCap.counted_bind]
        unfold offlineSign
        simp only [bind_assoc, pure_bind]
        rw [SphincsSecurity.QueryCap.counted_bind]
        simp only [simulateQ_bind, fixedWorld_counted_hashOnly T _ (authenticatedSign_hashOnly published request),
          ticks_counted, pure_bind, SphincsSecurity.QueryCap.counted_map, simulateQ_map, simulateQ_pure, ih]
        rfl
end ClaudeWCT.W9.T3.Security.Wots.Ref

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem offlineInteraction_pure (T : Answers) (published : T3.Cache) {α : Type} (value : α) :
    offlineInteraction T published (pure value : OracleComp PairedOuter.LazyPrivate.Interaction α) = pure (value, []) := rfl
theorem offlineInteraction_world (T : Answers) (published : T3.Cache) {α : Type}
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp PairedOuter.LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inl input)) >>= next) =
      (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind', WriterT.run_liftM, bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem offlineInteraction_request (T : Answers) (published : T3.Cache) {α : Type}
    (request : Request) (next : Option SigGolfCandidate.Research.SharedForest.Signature → OracleComp PairedOuter.LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (PairedOuter.LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (offlineSign T published request >>= fun answer =>
        (fun result => (result.1, ⟨request, answer⟩ :: result.2)) <$> offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr]
  simp
theorem shared_digest_hashOnly (rho : Digest) (message : Message) : ∀ fuel counter,
    Security.SourceReplay.HashOnly (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter;exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter
      unfold SigGolfCandidate.Research.SharedForest.sharedDigestSearch
      refine SourceQueries.bind_allowed _ (SourceQueries.digest_allowed _ (fun _ => trivial) _ _ _) ?_
      intro output
      split
      · exact SourceQueries.pure_allowed _ _
      · exact ih _

theorem shared_signPayload_hashOnly (cache : T3.Cache) (message : Message) :
    Security.SourceReplay.HashOnly (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  have ht := ClaudeWCT.Bank.Paired.tail_public SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
    (SourceQueries.signTop_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial))
  have hf := ClaudeWCT.Bank.Paired.forest_public SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
  have hout (rho : Digest) (counter : BitVec 32) (output : HashOutput) : Security.SourceReplay.HashOnly
      (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output) :=
    SharedQueries.signFromOutput_allowed _ ht (ClaudeWCT.Bank.Paired.forest_allowed _ hf) cache rho counter output
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine SourceQueries.bind_allowed _ (SourceQueries.privateNonce_allowed _ (fun _ => trivial) _) ?_
  intro rho
  refine SourceQueries.bind_allowed _ (shared_digest_hashOnly rho message _ _) ?_
  intro found
  cases found with
  | none => exact SourceQueries.pure_allowed _ _
  | some value =>
      refine SourceQueries.bind_allowed _ (hout rho value.1 value.2) ?_
      intro result
      cases result <;> exact SourceQueries.pure_allowed _ _

theorem authenticatedSign_hashOnly (published : T3.Cache) (request : Request) :
    Security.SourceReplay.HashOnly (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SourceReplay.IsHash
  · exact SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) request.cache.region
  · intro tag
    rcases Classical.em (request.cache = published) with h | h
    · rw [if_pos h]
      exact shared_signPayload_hashOnly request.cache request.message
    · rw [if_neg h]
      exact SourceQueries.pure_allowed _ _
theorem interaction_counted (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
    simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
        (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) program)) =
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged (offlineInteraction T published program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with input | request
      · rw [PairedOuter.FullGame.loggedWith_world, offlineInteraction_world]
        change simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
          (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign published) (next answer))) = _
        rw [SphincsSecurity.QueryCap.counted_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
        rcases input with n | x
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
      · rw [PairedOuter.FullGame.loggedWith_request, offlineInteraction_request]
        rw [SphincsSecurity.QueryCap.counted_bind]
        unfold offlineSign
        simp only [bind_assoc, pure_bind]
        rw [SphincsSecurity.QueryCap.counted_bind]
        simp only [simulateQ_bind, fixedWorld_counted_hashOnly T _ (authenticatedSign_hashOnly published request),
          ticks_counted, pure_bind, SphincsSecurity.QueryCap.counted_map, simulateQ_map, simulateQ_pure, ih]
        rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
