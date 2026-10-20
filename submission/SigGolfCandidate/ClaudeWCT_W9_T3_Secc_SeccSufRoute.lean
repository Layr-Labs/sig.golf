import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_SeccSufSigned
import SigGolfCandidate.ClaudeWCT_W9_New_Positions_FtsBridge

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
theorem honestMsg_lower (answers : Correctness.Answers) (index n : Nat) (hn : n + 1 < 4) :
    ClaudeWCT.W9.T3M.Extract.honestMsg answers index (Fin.ofNat 4 n) =
      .pair (ClaudeWCT.W9.T3M.Extract.honestPair answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2).1
        (ClaudeWCT.W9.T3M.Extract.honestPair answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2).2 := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
  have hl : (⟨n + 1, by omega⟩ : Layer) = Fin.ofNat 4 (n + 1) := Fin.ext (by simp; omega)
  simp only [ClaudeWCT.W9.T3M.Extract.honestMsg, hv, dif_pos (show n < 3 by omega), hl]
theorem honestMsg_three (answers : Correctness.Answers) (index : Nat) :
    ClaudeWCT.W9.T3M.Extract.honestMsg answers index (Fin.ofNat 4 3) = .pair (WCT9.honestTop answers index).1 (WCT9.honestTop answers index).2 := by
  rw [show (Fin.ofNat 4 3 : Layer) = 3 from rfl]
  simp only [ClaudeWCT.W9.T3M.Extract.honestMsg, show ¬((3 : Layer).val < 3) by decide, dite_false,
    ClaudeWCT.W9.T3M.Extract.honestTop_eq_wct9]
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
      · rw [WCT9.signLayersBC]
        simp only [evalWithAnswerFn_bind, hn0, ite_false]
        split
        · simp only [evalWithAnswerFn_bind]
          split
          · simp only [evalWithAnswerFn_pure]
            exact ⟨_, rfl⟩
          · rename_i hs'
            exfalso
            exact (ih (by omega) _).elim fun p hp => hs' p hp
        · rename_i hs
          exfalso
          refine (Option.isSome_iff_exists.mp (hcomp.2 _ ?_ _ _ _ ?_ ?_)).elim fun ⟨c, d⟩ hsome => hs c d hsome
          · intro h; rw [Fin.ext_iff, Fin.val_ofNat, Fin.val_zero] at h; omega
          · exact route_tree_lower index hindex _
          · exact route_leaf_bound index _
theorem payload_succeeds_of_complete (answers : Correctness.Answers) (hcomp : SignerComplete answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) :
    ∃ sig, evalWithAnswerFn answers (payloadForNonce cache rho m) = some sig ∧ sig.rho = rho := by
  obtain ⟨⟨counter, N⟩, hds⟩ := Option.isSome_iff_exists.mp (hcomp.1 rho m)
  obtain ⟨pieces, hp⟩ := signLayers_complete answers hcomp cache (WCT9.digestIndex N) (WCT9.digestIndex_lt _)
    4 le_rfl (.pair (WCT9.honestTop answers (WCT9.digestIndex N)).1 (WCT9.honestTop answers (WCT9.digestIndex N)).2)
  unfold payloadForNonce
  simp only [evalWithAnswerFn_bind, hds, WCT9.eval_signForest, hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl, rfl⟩
theorem hdrBlock_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (WCT9.pairEncodingInputP lay tree leaf left right counter pad)) =
      SphincsSecurity.bytesLE 16 (rowTweak lay tree leaf) := by
  have hl : (WCT9.pairEncodingInputP lay tree leaf left right counter pad).length = 64 := by
    simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by omega)]
  unfold WCT9.pairEncodingInputP
  rw [List.append_assoc, List.append_assoc]
  exact SigGolfCandidate.T3M.Extract.hdrBlock_prefix _ _ _
/-- C2 (FULL): a lower node query of the honest tree shape (heap below `2 ^ height lay`) is no digest query: the
packed node word's marker is `128 + heap`. -/
theorem lowerNodeHash_notDigest (lay : Layer) (tree heap : Nat) (left right : Digest) (hh : heap < 2 ^ height lay) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerNodeHash lay.val tree heap left right)
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  by_cases h0 : lay.val = 0
  · rw [h0, ClaudeWCT.WCT9.lowerNodeHash_top]
    exact SigGolfCandidate.T3.Security.BPB.nodeHash_ok _ _ _ _ _ _ (by decide)
  · have h7 : heap < 128 := lt_of_lt_of_le hh
      ((Nat.pow_le_pow_right (by decide) (ClaudeWCT.W9.T3.Security.Signer.height_le_seven h0)).trans (by norm_num))
    unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash
    refine ClaudeWCT.W9.T3.Security.Signer.halfHash_allowed_of_short _ _
      (SigGolfCandidate.T3.Security.BPB.shortHash_ok_marker
        (hdr := ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ?_ ?_)
    · unfold ClaudeWCT.WCT9.merkleNodeInput
      rw [List.append_assoc (SphincsSecurity.bytesLE 16 left ++
          SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap)),
        SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [SphincsSecurity.bytesLE_length, zero16]),
        SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
    · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]
      unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
      rw [SigGolfCandidate.T3.append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat,
        SigGolfCandidate.T3.hyperWord_toNat]
      omega
theorem layerEncoding_ok (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  cases msg with
  | forest root => exact SigGolfCandidate.T3.Security.BPB.encoding_ok lay tree leaf root counter
  | pair left right =>
      exact SigGolfCandidate.T3.Security.BPB.shortHash_ok_marker
        (hdrBlock_pairEncodingInputP lay tree leaf left right counter 0) (by rw [rowTweak_marker]; decide)
open SigGolfCandidate.T3.Security.BPB SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs in
/-- Pairing stage 1: a chain step of the current scheme (either format) is not a digest query. -/
theorem chainStepW_ok (lay : SigGolfCandidate.T3.Layer) (tree leaf i step : Nat) (v : SigGolfCandidate.T3.Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.shortHash (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  unfold SigGolfCandidate.T3.shortHash SigGolfCandidate.T3.publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change hdrMarker (SigGolfCandidate.T3.pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v)) ≠ 0
    rw [ClaudeWCT.WCT9.chainInputW_padded]
    apply hdrMarker_ne_zero_of_byte0
    unfold hdrByte0 Extract.hdrBlock
    rw [ClaudeWCT.WCT9.chainInputW_header, bytesLE16_first_toNat]
    have := SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem afterDigest_ok (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (do
      let forest ← WCT9.signForest (WCT9.digestIndex output) output
      let some pieces ← WCT9.signLayersBC cache (WCT9.digestIndex output) 4 (.pair forest.2.1 forest.2.2) | pure none
      pure (some (WCT9.assembledSignature rho forest.1 pieces)) : M (Option Signature))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  apply SourceQueries.bind_allowed _ (ClaudeWCT.WCT9.Wots.BPB.signForest_ok _ output)
  intro forest
  apply SourceQueries.bind_allowed _ (ClaudeWCT.W9.T3.Security.Signer.signLayersBC_allowed' _ _ layerEncoding_ok
    (ClaudeWCT.W9.T3.Security.Signer.buildTreeP_allowed' _ chainStepW_ok
      SigGolfCandidate.T3.Security.BPB.leafHash_ok
      (fun lay _ _ _ _ hh => lowerNodeHash_notDigest lay _ _ _ _ hh)
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
      exact this (SigGolfCandidate.T3.Security.BPB.hdrMarker_digestInput rho m ctr)
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
end ClaudeWCT.W9.T3.Security.BPB
