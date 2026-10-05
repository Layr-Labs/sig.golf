import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.WCT9.QueriesWots

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
def seedSlot (a : ChainAddr) : Nat :=
  if a.key.lay = 0 then a.chain else WCT9.lowerOrdinal a.key.lay a.key.leaf a.chain
def seedTweakP (a : ChainAddr) : BitVec 128 :=
  if a.key.lay = 0 then seedTweak a else WCT9.lowerSeedHeader a.key.lay a.key.tree (seedSlot a / 2)
theorem seedTweakP_top {a : ChainAddr} (h : a.key.lay = 0) : seedTweakP a = seedTweak a := by
  unfold seedTweakP; rw [if_pos h]
theorem seedSlot_top {a : ChainAddr} (h : a.key.lay = 0) : seedSlot a = a.chain := by
  unfold seedSlot; rw [if_pos h]
def slotAddr (a : ChainAddr) : ChainAddr :=
  if a.key.lay = 0 then a else ⟨⟨a.key.lay, a.key.tree, 0⟩, 2 * (seedSlot a / 2)⟩
theorem seedTweak_slotAddr (a : ChainAddr) : seedTweak (slotAddr a) = seedTweakP a := by
  unfold slotAddr seedTweakP
  split_ifs with h
  · rfl
  · unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (seedSlot a / 2) / 2 = seedSlot a / 2 by omega]
def parAddr (a : ChainAddr) : ChainAddr := ⟨a.key, seedSlot a % 2⟩
theorem parAddr_chain_mod (a : ChainAddr) : (parAddr a).chain % 2 = seedSlot a % 2 := Nat.mod_mod _ _
def siblingHalfP (a : ChainAddr) (output : HashOutput) : Digest := siblingHalf (parAddr a) output
def UntouchedP (a : ChainAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ step value, step < 256 → input ≠ chainRow a step value
  | .inr (.inl tweak) => tweak ≠ seedTweakP a
  | _ => True
noncomputable def prefixStep (answers : Answers) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers a ∧ input = chainRow a step value then some (Classical.choose h) else none
noncomputable def maskAt (answers : Answers) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr (.inl tweak) =>
      if tweak = seedTweakP a ∧ 1 ≤ depth answers a then
        (let output := answers (.inr (.inl tweak))
         if seedSlot a % 2 = 0 then ChainGraph.joinOutput 0 (output.extractLsb' 128 128)
         else ChainGraph.joinOutput (output.extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak))
  | .inr (.inr other) => answers (.inr (.inr other))
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask in
theorem Respects.inter {S₁ S₂ : Spec.Domain → Prop} {α : Type} {p : M α} (h₁ : Respects S₁ p) (h₂ : Respects S₂ p) :
    Respects (fun q => S₁ q ∧ S₂ q) p := by
  intro T T' hT
  let T'' : Answers := fun q => if S₁ q then T q else T' q
  have e1 := h₁ T T'' (fun q hq => by simp only [T'', if_pos hq])
  have e2 := h₂ T'' T' (fun q hq => by
    simp only [T'']
    split_ifs with h
    · exact hT q ⟨h, hq⟩
    · rfl)
  exact ⟨e1.1.trans e2.1, e1.2.trans e2.2⟩
open SigGolfCandidate.T3.Security.Wots.Mask in
theorem Respects.mono' {S S' : Spec.Domain → Prop} {α : Type} {p : M α} (h : Respects S p) (hS : ∀ q, S q → S' q) :
    Respects S' p := fun T T' hT => h T T' fun q hq => hT q (hS q hq)
theorem untouchedP_of_untouched (a : ChainAddr) {q : Spec.Domain}
    (h : SigGolfCandidate.T3.Security.Wots.Mask.Untouched a q ∧
      SigGolfCandidate.T3.Security.Wots.Mask.Untouched (slotAddr a) q) : UntouchedP a q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · exact h.1
  · show tweak ≠ seedTweakP a
    rw [← seedTweak_slotAddr]
    exact h.2
  · trivial
open SigGolfCandidate.T3.Security.Wots.Mask in
theorem Respects.untouchedP {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) (a : ChainAddr) :
    Respects (UntouchedP a) p :=
  Respects.mono' (Respects.inter (h a) (h (slotAddr a))) fun _ hq => untouchedP_of_untouched a hq
open SigGolfCandidate.T3.Security.Wots.Mask
theorem referenceDigits_spec (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay ∧ Cost.ValidDigits L.lay (referenceDigits answers L) := by
  unfold referenceDigits
  cases h : referenceSearch answers L with
  | none => exact dummyDigits_spec L.lay
  | some found =>
      obtain ⟨counter, digits⟩ := found
      have hd := (WCT9.layerCounterSearch_some answers L.lay L.tree L.leaf (leafMsg answers L)
        counterLimit 0 counter digits (by decide) h).2.2
      exact ⟨(decode_length_sum hd).1, Cost.validDigits_decode hd⟩
theorem referenceDigits_of_search {answers : Answers} {L : LeafAddr} {counter : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (counter, digits)) : referenceDigits answers L = digits := by
  unfold referenceDigits
  rw [h]
  rfl
theorem topSigned_reference (answers : Answers) (L : LeafAddr) (hl : L.lay = 0) :
    ((referenceSearch answers L).map Prod.snd).getD dummyTop = referenceDigits answers L := by
  unfold referenceDigits
  rw [hl]
  rfl
theorem depth_le_width (answers : Answers) (a : ChainAddr) (hc : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain :=
  (referenceDigits_spec answers a.key).2 a.chain hc
theorem chain_lt_of_depth (answers : Answers) (a : ChainAddr) (hd : 1 ≤ depth answers a) :
    a.chain < chainCount a.key.lay := by
  by_contra hc
  have hlen := (referenceDigits_spec answers a.key).1
  have h0 : depth answers a = 0 := List.getD_eq_default _ _ (by omega)
  omega
theorem depth_le_seven (answers : Answers) (a : ChainAddr) : depth answers a ≤ 7 := by
  by_cases hd : 1 ≤ depth answers a
  · exact (depth_le_width answers a (chain_lt_of_depth answers a hd)).trans (width_le _ _)
  · omega
theorem prefixStep_spec {answers : Answers} {a : ChainAddr} {input : HashInput} {step : Nat}
    (h : prefixStep answers a input = some step) :
    step < depth answers a ∧ ∃ value, input = chainRow a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h
theorem prefixStep_chainRow (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < 256) :
    prefixStep answers a (chainRow a s v) = if s < depth answers a then some s else none := by
  have h7 := depth_le_seven answers a
  split
  · rename_i hlt
    unfold prefixStep
    rw [dif_pos ⟨s, v, hlt, rfl⟩]
    obtain ⟨w, hw, heq⟩ := Classical.choose_spec (⟨s, v, hlt, rfl⟩ :
      ∃ step value, step < depth answers a ∧ chainRow a s v = chainRow a step value)
    exact congrArg some (chainRow_inj hs (by omega) heq).1.symm
  · rename_i hge
    cases hp : prefixStep answers a (chainRow a s v) with
    | none => rfl
    | some step =>
        obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
        have := (chainRow_inj hs (by omega) heq).1
        omega
theorem prefixStep_untouched {answers : Answers} {a : ChainAddr} {input : HashInput}
    (h : UntouchedP a (.inl (.inr input))) : prefixStep answers a input = none := by
  cases hp : prefixStep answers a input with
  | none => rfl
  | some step =>
      obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
      exact absurd heq (h step w (by have := depth_le_seven answers a; omega))
theorem maskAt_public (answers : Answers) (a : ChainAddr) (input : HashInput) :
    maskAt answers a (.inl (.inr input)) = match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl
theorem maskAt_tweak (answers : Answers) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers a (.inr (.inl tweak)) =
      if tweak = seedTweakP a ∧ 1 ≤ depth answers a then
        (if seedSlot a % 2 = 0 then ChainGraph.joinOutput 0 ((answers (.inr (.inl tweak))).extractLsb' 128 128)
         else ChainGraph.joinOutput ((answers (.inr (.inl tweak))).extractLsb' 0 128) 0)
      else answers (.inr (.inl tweak)) := rfl
theorem maskAt_untouched (answers : Answers) (a : ChainAddr) {q : Spec.Domain} (h : UntouchedP a q) :
    maskAt answers a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rw [maskAt_tweak, if_neg (fun h' => h h'.1)]
  · rfl
theorem maskAt_prefix (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < depth answers a) :
    maskAt answers a (.inl (.inr (chainRow a s v))) =
      if s + 1 = depth answers a then ChainGraph.joinOutput (frontierValue answers a) 0 else 0 := by
  have h7 := depth_le_seven answers a
  rw [maskAt_public, prefixStep_chainRow answers a v (by omega), if_pos hs]
  rfl
theorem maskAt_row_ge (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : depth answers a ≤ s)
    (hs' : s < 256) : maskAt answers a (.inl (.inr (chainRow a s v))) = answers (.inl (.inr (chainRow a s v))) := by
  rw [maskAt_public, prefixStep_chainRow answers a v hs', if_neg (by omega)]
theorem maskAt_of_depth_zero (answers : Answers) (a : ChainAddr) (hd : depth answers a = 0) :
    maskAt answers a = answers := by
  funext q
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public]
    cases hp : prefixStep answers a input with
    | none => rfl
    | some step => have := (prefixStep_spec hp).1; omega
  · rw [maskAt_tweak, if_neg (by omega)]
  · rfl
theorem eval_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    evalWithAnswerFn (maskAt answers a) program = evalWithAnswerFn answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).1
theorem queried_maskAt_of_respects (answers : Answers) (a : ChainAddr) {α : Type} {program : M α}
    (h : Respects (UntouchedP a) program) :
    SourceReplay.queried (maskAt answers a) program = SourceReplay.queried answers program :=
  (h _ _ fun _ hq => maskAt_untouched answers a hq).2
section Programs
variable (a : ChainAddr)
theorem respectsP_forestPk (index : Nat) (pairs : List (Digest × Digest)) :
    Respects (UntouchedP a) (ClaudeWCT.WCT9.forestPk index pairs) :=
  Respects.untouchedP (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_forestPk c index pairs) a
theorem respectsP_signForest (index : Nat) (output : HashOutput) :
    Respects (UntouchedP a) (ClaudeWCT.WCT9.signForest index output) :=
  Respects.untouchedP (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_signForest c index output) a
theorem respectsP_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Respects (UntouchedP a) (digest rho message counter) :=
  Respects.untouchedP (fun c => respects_digest c rho message counter) a
theorem respectsP_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (UntouchedP a) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respectsP_digest a _ _ _) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
theorem respectsP_privateMac (region : Region) : Respects (UntouchedP a) (privateMac region) :=
  Respects.untouchedP (fun c => respects_privateMac c region) a
theorem respectsP_privateNonce (message : Message) : Respects (UntouchedP a) (privateNonce message) :=
  Respects.untouchedP (fun c => respects_privateNonce c message) a
theorem respectsP_mask (level index : Nat) : Respects (UntouchedP a) (mask level index) :=
  Respects.untouchedP (fun c => respects_mask c level index) a
theorem respectsP_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 1) :
    Respects (UntouchedP a) (nodeHash tag lay tree heap left right) :=
  Respects.untouchedP (fun c => respects_nodeHash c tag lay tree heap left right ht) a
theorem respectsP_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (UntouchedP a) (buildLevels tag lay tree h leaves) :=
  Respects.untouchedP (fun c => respects_buildLevels c tag lay tree h leaves ht) a
theorem respectsP_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (UntouchedP a) (leafHash lay tree leaf ends) :=
  Respects.untouchedP (fun c => respects_leafHash c lay tree leaf ends) a
end Programs
end Mask
end ClaudeWCT.W9.T3.Security.Wots
