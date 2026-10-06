import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufSigned
import SigGolfCandidate.ClaudeWCT.W9.New.Positions.FtsBridge

namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (wrho wdc)
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind queried_shortHash)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open Correctness (treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9seccSufRoute : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem digestSearch_succ (rho : Digest) (m : Message) (counter fuel : Nat) :
    WCT9.digestSearch rho m counter (fuel + 1) = (digest rho m (BitVec.ofNat 32 counter) >>= fun output =>
      if WCT9.producerAdmissible output = true then pure (some (BitVec.ofNat 32 counter, output))
      else WCT9.digestSearch rho m (counter + 1) fuel) := rfl
theorem digestSearch_queried (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start (q : Spec.Domain), q ∈ queried answers (WCT9.digestSearch rho m start fuel) →
      ∃ c, start ≤ c ∧ c < start + fuel ∧ q = .inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))) ∧
        ∀ c', start ≤ c' → c' < c →
          WCT9.producerAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c'))) = false := by
  intro fuel
  induction fuel with
  | zero => intro start q hq; simp [WCT9.digestSearch] at hq
  | succ fuel ih =>
      intro start q hq
      rw [digestSearch_succ, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_digest] at hq
      rcases List.mem_append.mp hq with hq | hq
      · rw [List.mem_singleton] at hq
        exact ⟨start, le_rfl, by omega, hq, fun c' h1 h2 => by omega⟩
      · by_cases hadm : WCT9.producerAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 start))) = true
        · rw [if_pos hadm] at hq; simp at hq
        · rw [if_neg hadm] at hq
          obtain ⟨c, h1, h2, h3, h4⟩ := ih (start + 1) q hq
          refine ⟨c, by omega, by omega, h3, fun c' h1' h2' => ?_⟩
          by_cases hc' : c' = start
          · subst hc'; simpa using hadm
          · exact h4 c' (by omega) h2'
theorem digestSearch_accepts (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start c, start ≤ c → c < start + fuel →
      (∀ c', start ≤ c' → c' < c →
        WCT9.producerAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c'))) = false) →
      WCT9.producerAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) = true →
      evalWithAnswerFn answers (WCT9.digestSearch rho m start fuel) =
        some (BitVec.ofNat 32 c, evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) := by
  intro fuel
  induction fuel with
  | zero => intro start c h1 h2; omega
  | succ fuel ih =>
      intro start c h1 h2 hrej hadm
      rw [digestSearch_succ, evalWithAnswerFn_bind]
      by_cases hc : c = start
      · subst hc
        rw [if_pos hadm, evalWithAnswerFn_pure]
      · rw [if_neg (by rw [hrej start le_rfl (by omega)]; decide)]
        exact ih (start + 1) c (by omega) (by omega) (fun c' h1' h2' => hrej c' (by omega) h2') hadm
theorem rejected_trial_inadmissible (answers : Correctness.Answers) (rho : Digest) (m : Message) (c : Nat)
    (hq : (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))) : Spec.Domain) ∈
      queried answers (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit))
    (hadm : WCT9.producerAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) = true) :
    evalWithAnswerFn answers (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) =
      some (BitVec.ofNat 32 c, evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) := by
  obtain ⟨c', _, hc', heq, hrej⟩ := digestSearch_queried answers rho m WCT9.digestAttemptLimit 0 _ hq
  have hcc : BitVec.ofNat 32 c = BitVec.ofNat 32 c' := by
    simp only [Sum.inl.injEq, Sum.inr.injEq] at heq
    exact (SigGolfCandidate.T3.Security.BPB.digestInput_injective heq).2.1
  rw [hcc] at hadm ⊢
  exact digestSearch_accepts answers rho m WCT9.digestAttemptLimit 0 c' (Nat.zero_le _) hc' hrej hadm
theorem layerCounterSearch_none (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat)
    (msg : WCT9.LayerMsg) :
    ∀ fuel counter, evalWithAnswerFn answers (WCT9.layerCounterSearch lay tree leaf msg counter fuel) = none →
      ∀ offset, offset < fuel → WCT9.producerDecode lay (evalWithAnswerFn answers
        (shortHash (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (counter + offset))))) = none := by
  intro fuel
  induction fuel with
  | zero => intro counter _ offset h; omega
  | succ fuel ih =>
      intro counter h offset hoff
      simp only [WCT9.layerCounterSearch, evalWithAnswerFn_bind] at h
      cases hd : WCT9.producerDecode lay (evalWithAnswerFn answers
          (shortHash (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | some digits => simp [hd, evalWithAnswerFn_pure] at h
      | none =>
          simp only [hd] at h
          rcases Nat.eq_zero_or_pos offset with rfl | hpos
          · simpa using hd
          · have := ih (counter + 1) h (offset - 1) (by omega)
            rwa [show counter + 1 + (offset - 1) = counter + offset by omega] at this
theorem goodZ_row (answers : Correctness.Answers) (w : WBytes) (index : Nat) (lay : Layer)
    (hgood : ClaudeWCT.W9.T3M.BC.GoodZ answers w index lay) :
    ∃ digits, (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < counterLimit ∧
      decode lay (evalWithAnswerFn answers (shortHash (WCT9.layerEncodingInput lay (route index lay).2
        (route index lay).1 (ClaudeWCT.W9.T3M.Extract.honestMsg answers index lay)
        (ClaudeWCT.W9.T3M.wbcCtr w lay)))) = some digits := by
  obtain ⟨⟨digits, ⟨hlt, hdec⟩, -⟩, hpad⟩ := hgood
  refine ⟨digits, hlt, ?_⟩
  have hfit := ClaudeWCT.W9.T3M.Extract.msgFits_honestMsg answers index lay
  by_cases h3 : lay.val < 3
  · rw [← ClaudeWCT.W9.T3M.BC.layerEncodingInputP_zero, ← hpad h3]
    exact hdec
  · revert hfit hdec
    cases ClaudeWCT.W9.T3M.Extract.honestMsg answers index lay with
    | forest root => intro hdec _; exact hdec
    | pair l r => intro _ hfit; exact absurd hfit (by change ¬(lay.val < 3); exact h3)
theorem honestMsg_lower (answers : Correctness.Answers) (index n : Nat) (hn : n + 1 < 4) :
    ClaudeWCT.W9.T3M.Extract.honestMsg answers index (Fin.ofNat 4 n) =
      .pair (ClaudeWCT.W9.T3M.Extract.honestPair answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2).1
        (ClaudeWCT.W9.T3M.Extract.honestPair answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2).2 := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
  have hl : (⟨n + 1, by omega⟩ : Layer) = Fin.ofNat 4 (n + 1) := Fin.ext (by simp; omega)
  simp only [ClaudeWCT.W9.T3M.Extract.honestMsg, hv, dif_pos (show n < 3 by omega), hl]
theorem honestMsg_three (answers : Correctness.Answers) (index : Nat) :
    ClaudeWCT.W9.T3M.Extract.honestMsg answers index (Fin.ofNat 4 3) = .forest (WCT9.honestForest answers index) := by
  rw [show (Fin.ofNat 4 3 : Layer) = 3 from rfl]
  simp only [ClaudeWCT.W9.T3M.Extract.honestMsg, show ¬((3 : Layer).val < 3) by decide, dite_false,
    ClaudeWCT.W9.T3M.Extract.honestForest_eq_recover]
  rfl
theorem route_tree_lower (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ 25 := by
  fin_cases lay <;> simp [route, height] <;> omega
theorem signLayers_complete (answers : Correctness.Answers) (hcomp : SignerComplete answers)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg : WCT9.LayerMsg,
      ∃ pieces, evalWithAnswerFn answers (WCT9.signLayersBC cache index n msg) = some pieces := by
  intro n
  induction n with
  | zero => intro _ msg; exact ⟨[], by simp [WCT9.signLayersBC]⟩
  | succ n ih =>
      intro hn msg
      by_cases hn0 : n = 0
      · subst hn0
        rw [WCT9.signLayersBC]
        simp only [evalWithAnswerFn_bind, ite_true, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩
      · have hl : (Fin.ofNat 4 n : Layer) ≠ 0 := by
          intro h
          have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
          rw [h] at hv
          exact hn0 hv.symm
        obtain ⟨⟨counter, digits⟩, hs⟩ := Option.isSome_iff_exists.mp
          (hcomp.2 (Fin.ofNat 4 n) hl (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            (route_tree_lower index hindex _) (route_leaf_bound index _))
        rw [WCT9.signLayersBC]
        simp only [evalWithAnswerFn_bind, hs, hn0, ite_false]
        generalize evalWithAnswerFn answers (WCT9.buildTreeP (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 digits) = bt
        rcases bt with ⟨levels, values⟩
        obtain ⟨pieces, hp⟩ := ih (by omega) (.pair (WCT9.topPair (Fin.ofNat 4 n) levels).1
          (WCT9.topPair (Fin.ofNat 4 n) levels).2)
        simp only [hp, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩
theorem payload_succeeds_of_complete (answers : Correctness.Answers) (hcomp : SignerComplete answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) :
    ∃ sig, evalWithAnswerFn answers (payloadForNonce cache rho m) = some sig ∧ sig.rho = rho := by
  obtain ⟨⟨counter, N⟩, hds⟩ := Option.isSome_iff_exists.mp (hcomp.1 rho m)
  obtain ⟨pieces, hp⟩ := signLayers_complete answers hcomp cache (WCT9.digestIndex N) (WCT9.digestIndex_lt _)
    4 le_rfl (.forest (WCT9.honestForest answers (WCT9.digestIndex N)))
  unfold payloadForNonce
  simp only [evalWithAnswerFn_bind, hds, WCT9.eval_signForest, hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl, rfl⟩
theorem hdrBlock_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (WCT9.pairEncodingInputP lay tree leaf left right counter pad)) =
      SphincsSecurity.bytesLE 16 (header 4 lay.val tree 0 leaf) := by
  have hl : (WCT9.pairEncodingInputP lay tree leaf left right counter pad).length = 64 := by
    simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by omega)]
  unfold WCT9.pairEncodingInputP
  rw [List.append_assoc, List.append_assoc]
  exact SigGolfCandidate.T3M.Extract.hdrBlock_prefix _ _ _
theorem layerEncoding_ok (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    AllQueriesSatisfy (shortHash (WCT9.layerEncodingInput lay tree leaf msg counter))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  cases msg with
  | forest root => exact SigGolfCandidate.T3.Security.BPB.encoding_ok lay tree leaf root counter
  | pair left right =>
      exact SigGolfCandidate.T3.Security.BPB.shortHash_ok
        (hdrBlock_pairEncodingInputP lay tree leaf left right counter 0) (by decide)
theorem afterDigest_ok (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (do
      let forest ← WCT9.signForest (WCT9.digestIndex output) output
      let some pieces ← WCT9.signLayersBC cache (WCT9.digestIndex output) 4 (.forest forest.2) | pure none
      pure (some (WCT9.assembledSignature rho forest.1 pieces)) : M (Option Signature))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  apply SourceQueries.bind_allowed _ (ClaudeWCT.WCT9.Wots.BPB.signForest_ok _ output)
  intro forest
  apply SourceQueries.bind_allowed _ (ClaudeWCT.W9.T3.Security.Signer.signLayersBC_allowed' _ _ layerEncoding_ok
    (ClaudeWCT.W9.T3.Security.Signer.buildTreeP_allowed' _ SigGolfCandidate.T3.Security.BPB.chain_ok
      SigGolfCandidate.T3.Security.BPB.leafHash_ok
      (fun _ _ _ _ => SigGolfCandidate.T3.Security.BPB.buildLevels_ok _ _ _ _ _ (by decide))
      (fun _ _ _ => SigGolfCandidate.T3.Security.BPB.privatePair_ok _ _ _ _ _))
    (SigGolfCandidate.T3.Security.BPB.signTop_ok _) _ _ _)
  intro layers
  rcases layers with _ | pieces
  · exact SourceQueries.pure_allowed _ _
  · exact SourceQueries.pure_allowed _ _
theorem signer_digest_query (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (rho : Digest) (m : Message) (ctr : BitVec 32)
    (hq : (.inl (.inr (pad64 (digestInput rho m ctr))) : Spec.Domain) ∈
      queried answers (FullGame.authenticatedSign published request)) :
    request.cache = published ∧ request.message = m ∧
      rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      (.inl (.inr (pad64 (digestInput rho m ctr))) : Spec.Domain) ∈
        queried answers (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) := by
  unfold FullGame.authenticatedSign at hq
  rw [queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateMac] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  by_cases hc : request.cache = published
  swap
  · rw [if_neg hc] at hq; simp at hq
  rw [if_pos hc] at hq
  change _ ∈ queried answers (WCT9.Rev3.signPayload request.cache request.message) at hq
  rw [signPayload_nonce, queried_bind, SigGolfCandidate.T3.Security.BPB.queried_privateNonce] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  unfold payloadForNonce at hq
  rw [queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  ·
    obtain ⟨c, -, -, heq, -⟩ := digestSearch_queried answers _ _ WCT9.digestAttemptLimit 0 _ hq
    simp only [Sum.inl.injEq, Sum.inr.injEq] at heq
    obtain ⟨hrho, hctr, hm⟩ := SigGolfCandidate.T3.Security.BPB.digestInput_injective heq
    subst hrho hm
    exact ⟨hc, rfl, rfl, hq⟩
  ·
    exfalso
    generalize evalWithAnswerFn answers (WCT9.digestSearch (evalWithAnswerFn answers (privateNonce request.message))
      request.message 0 WCT9.digestAttemptLimit) = found at hq
    rcases found with _ | ⟨_, output⟩
    · simp at hq
    · have := SigGolfCandidate.T3.Security.BPB.allQ_queried answers _ _ (afterDigest_ok request.cache
        (evalWithAnswerFn answers (privateNonce request.message)) output) _ hq
      exact this (SigGolfCandidate.T3.Security.BPB.hdrTag_digestInput rho m ctr)
theorem caseC_fresh_not_signer (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests) (state : LazyPrivate.State)
    (hres : ∀ entry ∈ log, SourceReplay.Resolves state (FullGame.authenticatedSign published entry.1) entry.2)
    (hagree : ∀ input answer, SourceReplay.known state input = some answer → answers input = answer)
    (m : Message) (w : WBytes) (hcomp : SignerComplete answers) (hfresh : ¬SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, -⟩ := signer_digest_query answers published entry.1 _ _ _ hq
  obtain ⟨sig, hsig, hsrho⟩ := payload_succeeds_of_complete answers hcomp published (wrho w) m
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [← (hres entry he).eval answers hagree, eval_authenticatedSign, if_pos hc, ← hrho, hm]
  exact hsig
theorem caseCAt_fresh_not_signer (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests) (state : LazyPrivate.State)
    (hres : ∀ entry ∈ log, SourceReplay.Resolves state (FullGame.authenticatedSign published entry.1) entry.2)
    (hagree : ∀ input answer, SourceReplay.known state input = some answer → answers input = answer)
    (message : Message) (witness : WBytes) (events : List FirstHit.QueryEvent)
    (hC : CaseCAt answers message witness events) (hfresh : ¬SignedDigest log message witness) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))) : Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  obtain ⟨N, -, hN, -, hS, hgood, -, hcomp⟩ := hC
  exact caseC_fresh_not_signer answers published log state hres hagree message witness hcomp hfresh
theorem caseC_fresh_first_occurrence (adversary : ClaudeWCT.W9.T3M.Final.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hC : CaseCFresh adversary z) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record
        (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        SourceReplay.Extends interaction.state (QueryRecorded.recordedTrace z.1).state ∧
        ∃ (message : Message) (witness : WBytes) (N : HashOutput),
          evalWithAnswerFn z.2 (digest (wrho witness) message (wdc witness)) = N ∧
          (∀ entry ∈ interaction.value.2,
            (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))) : Spec.Domain) ∉
              queried z.2 (FullGame.authenticatedSign generated.value.2 entry.1)) ∧
          ∃ first : LazyPrivate.State,
            (⟨first, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), N⟩ :
              FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events ∧
            first.2 (pad64 (digestInput (wrho witness) message (wdc witness))) = none := by
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  obtain ⟨generated, hg, interaction, hi, hext, -, -, forgery, -, -, message, witness, -, hsigned, hC⟩ := hC
  obtain ⟨N, -, hN, ⟨prior, hev⟩, hS, hgood, -, hcomp⟩ := hC
  have hai : ∀ input answer, SourceReplay.known interaction.state input = some answer → z.2 input = answer :=
    fun input answer hk => hagree input answer (SourceReplay.known_mono _ _ hext hk)
  have hres := logged_resolves generated.value.2 _ generated.state _ (FirstHit.recorded_support _ _ _ hi)
  refine ⟨generated, hg, interaction, hi, hext, message, witness, N, hN,
    caseC_fresh_not_signer z.2 generated.value.2 interaction.value.2 interaction.state hres hai message witness
      hcomp hsigned, ?_⟩
  exact FirstHit.first_public_occurrence _ _ (PaddedExtraction.traced_record_support adversary q hq z.1 hz1)
    prior _ _ hev
end ClaudeWCT.W9.T3.Security.BPB
