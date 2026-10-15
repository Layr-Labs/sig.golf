import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.T3.Secc.WotsExtractVerify

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low dummyDigits_valid)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem referenceSearch_producerDecode (answers : Answers) (L : LeafAddr) {c : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (c, digits)) :
    WCT9.producerDecode L.lay (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L (leafMsg answers L) c 0))))) = some digits := by
  have hs := (WCT9.layerCounterSearch_some_search answers L.lay L.tree L.leaf (leafMsg answers L)
    (WCT9.searchLimit L.lay) 0 c digits
    (by have := WCT9.searchLimit_le L.lay; unfold counterLimit at this; omega) h).2.2
  rw [encRow_zero]
  exact hs
theorem referenceSearch_decode (answers : Answers) (L : LeafAddr) {c : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (c, digits)) :
    decode L.lay (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L (leafMsg answers L) c 0))))) = some digits :=
  WCT9.producerDecode_decode (referenceSearch_producerDecode answers L h)
theorem referenceDigits_decode (answers : Answers) (L : LeafAddr) :
    ∃ value : Digest, decode L.lay value = some (referenceDigits answers L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers L with
  | none => exact SigGolfCandidate.T3.Security.Wots.dummyDigits_valid L.lay
  | some s =>
      obtain ⟨c, digits⟩ := s
      exact ⟨_, referenceSearch_decode answers L hs⟩
theorem dummyDigits_credit (lay : Layer) :
    WCT9.producerFloor lay + WCT9.dispatchPenalty lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) ≤
      WCT9.wordCredit lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) +
        4 * WCT9.savedCopies lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) := by
  fin_cases lay <;> decide +kernel
theorem dummyDigits_zeroBound (lay : Layer) :
    WCT9.producerZeroBound lay (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) := by
  fin_cases lay <;> decide +kernel
theorem dummyDigest_rankBound (lay : Layer) :
    WCT9.producerRankBound lay (SigGolfCandidate.T3.Security.WotsExtract.dummyDigest lay) := by
  fin_cases lay <;> decide +kernel
theorem dummyDigest_producerDecode (lay : Layer) :
    WCT9.producerDecode lay (SigGolfCandidate.T3.Security.WotsExtract.dummyDigest lay) =
      some (SigGolfCandidate.T3.Security.Wots.dummyDigits lay) :=
  WCT9.producerDecode_of (SigGolfCandidate.T3.Security.WotsExtract.dummyDigest_decode lay)
    (dummyDigits_credit lay) (dummyDigits_zeroBound lay) (dummyDigest_rankBound lay)
theorem referenceDigits_producerDecode (answers : Answers) (L : LeafAddr) :
    ∃ value : Digest, WCT9.producerDecode L.lay value = some (referenceDigits answers L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers L with
  | none => exact ⟨_, dummyDigest_producerDecode L.lay⟩
  | some s =>
      obtain ⟨c, digits⟩ := s
      exact ⟨_, referenceSearch_producerDecode answers L hs⟩
theorem referenceDigits_credit (answers : Answers) (L : LeafAddr) :
    WCT9.producerFloor L.lay + WCT9.dispatchPenalty L.lay (referenceDigits answers L) ≤
      WCT9.wordCredit L.lay (referenceDigits answers L) + 4 * WCT9.savedCopies L.lay (referenceDigits answers L) := by
  obtain ⟨u, hu⟩ := referenceDigits_producerDecode answers L
  exact WCT9.producerDecode_credit hu
theorem producerDecode_canonical {lay : Layer} {a b : Digest} {ds : List Nat}
    (ha : WCT9.producerDecode lay a = some ds) (hb : decode lay b = some ds) :
    WCT9.producerDecode lay b = some ds := by
  have hab := decode_some_injective (WCT9.producerDecode_decode ha) hb
  subst b
  exact ha
theorem producerDecode_of_reference (answers : Answers) (L : LeafAddr) {v : Digest}
    (h : decode L.lay v = some (referenceDigits answers L)) :
    WCT9.producerDecode L.lay v = some (referenceDigits answers L) := by
  obtain ⟨value, hp⟩ := referenceDigits_producerDecode answers L
  exact producerDecode_canonical hp h
#print axioms dummyDigest_producerDecode
#print axioms referenceDigits_producerDecode
#print axioms producerDecode_of_reference
theorem depth_le (answers : Answers) (a : ChainAddr) (ha : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers a.key
  have := decode_digit_max hv a.chain ha
  unfold depth
  omega
theorem referenceDigits_length (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers L
  exact (decode_length_sum hv).1
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    ContactAt answers trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono hs hsub⟩
theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    TwoEdgeAt answers trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono h1 hsub,
    SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono h2 hsub⟩
theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers trace L) (hsub : ∀ e ∈ trace, e ∈ trace') :
    EncodingMatchAt answers trace' L := by
  obtain ⟨message, counter, pad, answer, hfit, hm, hne, hd⟩ := h
  exact ⟨message, counter, pad, answer, hfit, hsub _ hm, hne, hd⟩
theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    MarkerAt answers trace' a := by
  obtain ⟨message, counter, pad, answer, digits, hfit, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, pad, answer, digits, hfit, hsub _ hm, hne, hd, hl, hu⟩
theorem structuralHit_mono (h : StructuralHit answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    StructuralHit answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hc, hh⟩
end mono
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
theorem WotsPrimitive.mono {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitive answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') : WotsPrimitive answers trace' := by
  rcases h with ⟨L, h⟩ | h | ⟨a, h⟩ | ⟨a, b, hab, h1, h2⟩ | ⟨a, hm, hc⟩
  · exact Or.inl ⟨L, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHit_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end ClaudeWCT.W9.T3.Security.Wots
namespace ClaudeWCT.W9.T3.Security.PaddedExtraction
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] verifyP expandB
theorem check_hashOnly (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    Security.SourceReplay.HashOnly (checkForgeryP publicKey log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (ClaudeWCT.W9.T3.Security.PaddedGame.check_public publicKey log forgery)
  intro input h
  rcases input with (coin | input) | coordinate
  · exact h.elim
  · trivial
  · trivial
theorem check_accepting (answers : Answers) (publicKey : Digest) (log : QueryLog Requests)
    (forgery : ForgeryP) (hw : evalWithAnswerFn answers (checkForgeryP publicKey log forgery) = true) :
    Fresh log forgery ∧ ∃ message witness, WitnessOf answers publicKey forgery message witness ∧
      evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
      ∀ input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (verifyP message publicKey witness),
        input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (checkForgeryP publicKey log forgery) := by
  cases forgery with
  | witness message witness =>
      simp only [checkForgeryP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Bool.and_eq_true,
        decide_eq_true_eq] at hw
      refine ⟨hw.1, message, witness, ⟨rfl, rfl⟩, hw.2, ?_⟩
      intro input hi
      simpa only [checkForgeryP, SigGolfCandidate.T3M.SecurityExtraction.queried_bind, SigGolfCandidate.T3M.SecurityExtraction.queried_pure,
        List.append_nil] using hi
  | signature message signature =>
      cases he : evalWithAnswerFn answers (expandB message publicKey signature) with
      | none => simp [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure] at hw
      | some witness =>
          simp only [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure, Bool.and_eq_true,
            decide_eq_true_eq] at hw
          refine ⟨hw.1, message, witness, ⟨rfl, he⟩, hw.2, ?_⟩
          intro input hi
          simp only [checkForgeryP, SigGolfCandidate.T3M.SecurityExtraction.queried_bind, he, SigGolfCandidate.T3M.SecurityExtraction.queried_pure,
            List.append_nil]
          exact List.mem_append_right _ hi
end ClaudeWCT.W9.T3.Security.PaddedExtraction

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem counterSearch_decode (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : WCT9.LayerMsg) : ∀ fuel start c digits,
    evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg start fuel) =
      some (c, digits) →
    WCT9.CanonicalPolicy.producerDecodeAt lay floor
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg c))) =
      some digits := by
  intro fuel
  induction fuel with
  | zero => intro start c digits h; simp [WCT9.CanonicalPolicy.layerCounterSearchAt] at h
  | succ fuel ih =>
      intro start c digits h
      rw [WCT9.CanonicalPolicy.layerCounterSearchAt, evalWithAnswerFn_bind] at h
      cases hd : WCT9.CanonicalPolicy.producerDecodeAt lay floor
        (evalWithAnswerFn answers (WCT9.encodingHash lay
          (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 start)))) with
      | none => rw [hd] at h; exact ih (start + 1) c digits h
      | some ds =>
          rw [hd, evalWithAnswerFn_pure] at h
          cases h
          exact hd

theorem referenceSearch_decode (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {c : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers messages L = some (c, digits)) :
    WCT9.CanonicalPolicy.decode L.lay
      (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L (messages L) c 0))))) = some digits := by
  unfold referenceSearch selected at h
  cases hc : context (searchOf answers messages) WCT9.CanonicalPolicy.credit L with
  | none => rw [hc] at h; cases h
  | some remaining =>
      rw [hc] at h
      have hd := counterSearch_decode answers L.lay
        (WCT9.CanonicalPolicy.threshold L.lay.val remaining) L.tree L.leaf (messages L)
        (WCT9.searchLimit L.lay) 0 c digits h
      rw [encRow_zero]
      exact (WCT9.CanonicalPolicy.producerDecodeAt_spec hd).1

theorem referenceDigits_decode (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) :
    ∃ value : Digest, WCT9.CanonicalPolicy.decode L.lay value = some (referenceDigits answers messages L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers messages L with
  | none => exact dummyDigits_valid (WCT9.CanonicalPolicy.normalLayer L.lay)
  | some found =>
      obtain ⟨c, digits⟩ := found
      exact ⟨_, referenceSearch_decode answers messages L hs⟩

theorem normalLayer_chainCount (lay : Layer) :
    chainCount (WCT9.CanonicalPolicy.normalLayer lay) = chainCount lay := by
  fin_cases lay <;> rfl

theorem normalLayer_maxDigit (lay : Layer) (i : Nat) :
    maxDigit (WCT9.CanonicalPolicy.normalLayer lay) i = maxDigit lay i := by
  fin_cases lay <;> rfl

theorem referenceDigits_length (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) : (referenceDigits answers messages L).length = chainCount L.lay := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers messages L
  exact (decode_length_sum hv).1.trans (normalLayer_chainCount L.lay)

theorem depth_le (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) (ha : a.chain < chainCount a.key.lay) :
    depth answers messages a ≤ maxDigit a.key.lay a.chain := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers messages a.key
  have hi : a.chain < chainCount (WCT9.CanonicalPolicy.normalLayer a.key.lay) := by
    rw [normalLayer_chainCount]; exact ha
  have hd := decode_digit_max hv a.chain hi
  rw [normalLayer_maxDigit] at hd
  exact hd

#print axioms referenceSearch_decode
#print axioms referenceDigits_decode
#print axioms depth_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem referenceInput_ne (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    {digits : List Nat}
    (hd : WCT9.CanonicalPolicy.decode L.lay
      (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L msg ctr pad))))) = some digits)
    (hne : msg ≠ messages L ∨ digits ≠ referenceDigits answers messages L) :
    referenceInput answers messages L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers messages L with
  | none => rw [hs] at h; simp at h
  | some s =>
      obtain ⟨c, w'⟩ := s
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hm, hc, -⟩ := BC.layerEncodingRow_injective_leaf hfitRef hfit h
      rw [← h] at hd
      subst hm hc
      have hdec := referenceSearch_decode answers messages L hs
      have hw : referenceDigits answers messages L = w' := by unfold referenceDigits; rw [hs]; rfl
      have hdw : digits = w' := Option.some.inj (hd.symm.trans hdec)
      rcases hne with hne | hne
      · exact hne rfl
      · exact hne (hdw.trans hw.symm)

theorem referenceInput_ne_pad (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfitRef : Extract.msgFits L.lay (messages L)) (hfit : Extract.msgFits L.lay msg)
    (hpad : pad.1 ≠ 0) : referenceInput answers messages L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers messages L with
  | none => rw [hs] at h; simp at h
  | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨-, -, hp, -⟩ := BC.layerEncodingRow_injective_leaf hfitRef hfit h
      exact hpad hp.symm

theorem canonical_word_cases {lay : Layer} {refDigest candDigest : Digest} {refDigits candDigits : List Nat}
    (hr : WCT9.CanonicalPolicy.decode lay refDigest = some refDigits)
    (hc : WCT9.CanonicalPolicy.decode lay candDigest = some candDigits) :
    candDigits = refDigits ∨
      (∃ i, i < chainCount lay ∧ candDigits.getD i 0 + 1 = refDigits.getD i 0 ∧
        ∀ j, j < chainCount lay → j ≠ i → refDigits.getD j 0 ≤ candDigits.getD j 0) ∨
      (∃ i, i < chainCount lay ∧ candDigits.getD i 0 + 2 ≤ refDigits.getD i 0) ∨
      (∃ i j, i < chainCount lay ∧ j < chainCount lay ∧ i ≠ j ∧
        candDigits.getD i 0 < refDigits.getD i 0 ∧ candDigits.getD j 0 < refDigits.getD j 0) := by
  rcases word_cases hr hc with he | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, hi, hj⟩
  · exact Or.inl he
  · refine Or.inr (Or.inl ⟨i.val, ?_, hi.2.2.1, ?_⟩)
    · simpa only [normalLayer_chainCount] using (show i.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from i.isLt)
    · intro j hj hji
      have hj' : j < chainCount (WCT9.CanonicalPolicy.normalLayer lay) := by
        rw [normalLayer_chainCount]; exact hj
      exact hi.2.2.2 ⟨j, hj'⟩ (fun h => hji (congrArg Fin.val h))
  · refine Or.inr (Or.inr (Or.inl ⟨i.val, ?_, hi⟩))
    simpa only [normalLayer_chainCount] using (show i.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from i.isLt)
  · refine Or.inr (Or.inr (Or.inr ⟨i.val, j.val, ?_, ?_, ?_, hi, hj⟩))
    · simpa only [normalLayer_chainCount] using (show i.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from i.isLt)
    · simpa only [normalLayer_chainCount] using (show j.val < chainCount (WCT9.CanonicalPolicy.normalLayer lay) from j.isLt)
    · exact fun h => hij (Fin.ext h)

section mono
variable {answers : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace trace' : List Entry}
theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers messages trace a)
    (hsub : ∀ e ∈ trace, e ∈ trace') : ContactAt answers messages trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono hs hsub⟩
theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers messages trace a)
    (hsub : ∀ e ∈ trace, e ∈ trace') : TwoEdgeAt answers messages trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono h1 hsub,
    SigGolfCandidate.T3.Security.WotsExtract.seenRow_mono h2 hsub⟩
theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers messages trace L)
    (hsub : ∀ e ∈ trace, e ∈ trace') : EncodingMatchAt answers messages trace' L := by
  obtain ⟨message, counter, pad, answer, hfit, hm, hne, hd⟩ := h
  exact ⟨message, counter, pad, answer, hfit, hsub _ hm, hne, hd⟩
theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers messages trace a)
    (hsub : ∀ e ∈ trace, e ∈ trace') : MarkerAt answers messages trace' a := by
  obtain ⟨message, counter, pad, answer, digits, hfit, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, pad, answer, digits, hfit, hsub _ hm, hne, hd, hl, hu⟩
end mono
#print axioms referenceInput_ne
#print axioms canonical_word_cases
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
