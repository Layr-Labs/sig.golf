import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEvents
import SigGolfCandidate.ClaudeWCT_WCT9_QueriesWots
set_option Elab.async false

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
/-- Queries that neither are a row of chain `a` at a chain step (`< 7`; C2: a lower Merkle node input can equal a
row at step 7, which no chain reaches) nor read `a`'s seed cell. -/
def UntouchedP (a : ChainAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ step value, step < 7 → input ≠ chainRowW a step value
  | .inr (.inl tweak) => tweak ≠ seedTweakP a
  | _ => True
noncomputable def prefixStep (answers : Answers) (a : ChainAddr) (input : HashInput) : Option Nat :=
  if h : ∃ step value, step < depth answers a ∧ input = chainRowW a step value then some (Classical.choose h) else none
/-- Mask of chain `a`: its rows below `depth` answer `0` (the last one answers the frontier, in the half its step
reads, C3). Seeds are evaluations
of their leaf family at every layer (campaign X1 stage B, top leaves since campaign T8D), so no private cell is
blanked. -/
noncomputable def maskAt (answers : Answers) (a : ChainAddr) : Answers
  | .inl (.inr input) =>
      match prefixStep answers a input with
      | some step => if step + 1 = depth answers a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input))
  | .inl (.inl coin) => answers (.inl (.inl coin))
  | .inr c => answers (.inr c)
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
  · intro step value hs heq
    have hu := h.1 step value (by omega)
    unfold chainRowW WCT9.chainInputW at heq
    split at heq
    · exact hu.2 heq
    · exact hu.1 heq
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
        (WCT9.searchLimit L.lay) 0 counter digits (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits L.lay) h).2.2
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
    step < depth answers a ∧ ∃ value, input = chainRowW a step value := by
  unfold prefixStep at h
  split at h
  · rename_i hex
    have he := Option.some.inj h
    subst he
    obtain ⟨value, hlt, heq⟩ := Classical.choose_spec hex
    exact ⟨hlt, value, heq⟩
  · cases h
theorem prefixStep_chainRow (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < 256) :
    prefixStep answers a (chainRowW a s v) = if s < depth answers a then some s else none := by
  have h7 := depth_le_seven answers a
  split
  · rename_i hlt
    unfold prefixStep
    rw [dif_pos ⟨s, v, hlt, rfl⟩]
    obtain ⟨w, hw, heq⟩ := Classical.choose_spec (⟨s, v, hlt, rfl⟩ :
      ∃ step value, step < depth answers a ∧ chainRowW a s v = chainRowW a step value)
    exact congrArg some (chainRowW_inj hs (by omega) heq).1.symm
  · rename_i hge
    cases hp : prefixStep answers a (chainRowW a s v) with
    | none => rfl
    | some step =>
        obtain ⟨hlt, w, heq⟩ := prefixStep_spec hp
        have := (chainRowW_inj hs (by omega) heq).1
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
      | some step => if step + 1 = depth answers a then
            joinHalf (WCT9.chainHigh a.key.lay a.chain step) (frontierValue answers a) 0
          else (0 : HashOutput)
      | none => answers (.inl (.inr input)) := rfl
theorem maskAt_private (answers : Answers) (a : ChainAddr) (c : Coordinate) :
    maskAt answers a (.inr c) = answers (.inr c) := rfl
theorem maskAt_tweak (answers : Answers) (a : ChainAddr) (tweak : BitVec 128) :
    maskAt answers a (.inr (.inl tweak)) = answers (.inr (.inl tweak)) := rfl
theorem maskAt_untouched (answers : Answers) (a : ChainAddr) {q : Spec.Domain} (h : UntouchedP a q) :
    maskAt answers a q = answers q := by
  rcases q with (coin | input) | (tweak | other)
  · rfl
  · rw [maskAt_public, prefixStep_untouched h]
  · rfl
  · rfl
theorem maskAt_prefix (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : s < depth answers a) :
    maskAt answers a (.inl (.inr (chainRowW a s v))) =
      if s + 1 = depth answers a then joinHalf (WCT9.chainHigh a.key.lay a.chain s) (frontierValue answers a) 0
        else 0 := by
  have h7 := depth_le_seven answers a
  rw [maskAt_public, prefixStep_chainRow answers a v (by omega), if_pos hs]
  rfl
theorem maskAt_row_ge (answers : Answers) (a : ChainAddr) {s : Nat} (v : Digest) (hs : depth answers a ≤ s)
    (hs' : s < 256) : maskAt answers a (.inl (.inr (chainRowW a s v))) = answers (.inl (.inr (chainRowW a s v))) := by
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
  · rfl
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
theorem respectsP_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (UntouchedP a) (buildLevels tag lay tree h leaves) :=
  Respects.untouchedP (fun c => respects_buildLevels c tag lay tree h leaves ht) a
theorem respectsP_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (UntouchedP a) (leafHash lay tree leaf ends) :=
  Respects.untouchedP (fun c => respects_leafHash c lay tree leaf ends) a
end Programs
/-! ### C2/C3 (FULL) programs: halves, the packed lower node tweak, the chain-0 high half -/
theorem respects_halfHash' {S : Spec.Domain → Prop} (high : Bool) (input : HashInput)
    (h : S (.inl (.inr (pad64 input)))) : Respects S (WCT9.halfHash high input) := by
  cases high
  · unfold WCT9.halfHash; simp only [Bool.false_eq_true, ↓reduceIte]; exact Respects.shortHash input h
  · unfold WCT9.halfHash WCT9.highHash; simp only [↓reduceIte]
    exact Respects.bind (Respects.publicHash input h) fun _ => Respects.pure' _
theorem respects_chainW' {S : Spec.Domain → Prop} (lay : Layer) (tree leaf i start count : Nat) (v : Digest)
    (h : ∀ step value, start ≤ step → step < start + count →
      S (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i step value))))) :
    Respects S (WCT9.chainW lay tree leaf i start count v) := by
  unfold WCT9.chainW
  exact Respects.foldlM _ _ (fun step hs value => respects_halfHash' _ _ (h step value
    (List.mem_range'_1.mp hs).1 (List.mem_range'_1.mp hs).2)) v
theorem merkleNodeInput_eq_block4 (lay tree heap : Nat) (left right : Digest) :
    WCT9.merkleNodeInput lay tree heap left right = block4 left (WCT9.merkleTweak lay tree heap) 0 right := by
  unfold WCT9.merkleNodeInput block4
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
theorem respects_lowerNodeHash' {S : Spec.Domain → Prop} (lay tree heap : Nat) (left right : Digest)
    (h : S (.inl (.inr (block4 left (WCT9.merkleTweak lay tree heap) 0 right)))) :
    Respects S (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  refine respects_halfHash' _ _ ?_
  rw [merkleNodeInput_eq_block4, pad64_block4]
  exact h
theorem respects_lowerLevel' {S : Spec.Domain → Prop} (lay tree h level : Nat) (nodes : List Digest)
    (hS : ∀ i left right, i < nodes.length / 2 →
      S (.inl (.inr (block4 left (WCT9.merkleTweak lay tree (2 ^ (h - level) + i)) 0 right)))) :
    Respects S (WCT9.lowerLevel lay tree h level nodes) := by
  unfold WCT9.lowerLevel
  exact Respects.mapM _ _ fun i hi => respects_lowerNodeHash' _ _ _ _ _ (hS i _ _ (List.mem_range.mp hi))
theorem respects_lowerLeafHash' {S : Spec.Domain → Prop} (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (h : S (.inl (.inr (pad64 (leafInput lay tree leaf ends))))) :
    Respects S (WCT9.lowerLeafHash lay tree leaf ends) := by
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  exact respects_halfHash' _ _ h
theorem respects_bind_inv' {S : Spec.Domain → Prop} {α β : Type} {p : M α} {f : α → M β} (P : α → Prop)
    (hp : Respects S p) (hP : ∀ T, P (evalWithAnswerFn T p)) (hf : ∀ x, P x → Respects S (f x)) :
    Respects S (p >>= f) := by
  intro T T' hT
  obtain ⟨he, hq⟩ := hp T T' hT
  obtain ⟨he', hq'⟩ := hf (evalWithAnswerFn T' p) (hP T') T T' hT
  refine ⟨?_, ?_⟩
  · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, he]
    exact he'
  · rw [SourceReplay.queried_bind, SourceReplay.queried_bind, hq, he, hq']
theorem respects_foldlM_inv' {S : Spec.Domain → Prop} {β γ : Type} (I : γ → Prop) (l : List β) (f : γ → β → M γ)
    (hpres : ∀ x ∈ l, ∀ s, I s → ∀ T, I (evalWithAnswerFn T (f s x)))
    (hf : ∀ x ∈ l, ∀ s, I s → Respects S (f s x)) : ∀ init, I init → Respects S (l.foldlM f init) := by
  induction l with
  | nil => intro init _; exact Respects.pure' init
  | cons x xs ih =>
      intro init hinit
      rw [List.foldlM_cons]
      exact respects_bind_inv' I (hf x List.mem_cons_self init hinit) (hpres x List.mem_cons_self init hinit)
        fun s hs => ih (fun y hy => hpres y (List.mem_cons_of_mem _ hy))
          (fun y hy => hf y (List.mem_cons_of_mem _ hy)) s hs
theorem getD_append_length_le' {levels : List (List Digest)} {nodes : List Digest} {B : Nat}
    (h1 : ∀ j, (levels.getD j []).length ≤ B) (h2 : nodes.length ≤ B) (j : Nat) :
    ((levels ++ [nodes]).getD j []).length ≤ B := by
  rcases Nat.lt_or_ge j levels.length with hj | hj
  · rw [List.getD_append _ _ _ _ hj]; exact h1 j
  · rw [List.getD_append_right _ _ _ _ hj]
    rcases Nat.eq_or_lt_of_le hj with he | hlt
    · rw [← he, Nat.sub_self]; simpa using h2
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
theorem lowerLevel_length' (answers : Answers) (lay tree h level : Nat) (nodes : List Digest) :
    (evalWithAnswerFn answers (WCT9.lowerLevel lay tree h level nodes)).length = nodes.length / 2 := by
  unfold WCT9.lowerLevel
  rw [Correctness.eval_mapM, List.length_map, List.length_range]
/-- The fold queries of a lower tree (`lowerLevels`, `buildLevelsBelow`): heaps `2 ^ (h - level) + i` with
`level ≥ 1` and `i < 2 ^ h / 2`. -/
def FoldOK (S : Spec.Domain → Prop) (lay tree h : Nat) : Prop :=
  ∀ level i left right, 1 ≤ level → i < 2 ^ h / 2 →
    S (.inl (.inr (block4 left (WCT9.merkleTweak lay tree (2 ^ (h - level) + i)) 0 right)))
theorem respects_lowerFold' {S : Spec.Domain → Prop} {lay tree h : Nat} (hS : FoldOK S lay tree h) (l : List Nat)
    (hl : ∀ x ∈ l, 1 ≤ x) (leaves : List Digest) (hlen : leaves.length ≤ 2 ^ h) :
    Respects S (l.foldlM (fun levels level => do
      let nodes ← WCT9.lowerLevel lay tree h level (levels.getD (level - 1) [])
      pure (levels ++ [nodes])) [leaves]) := by
  refine respects_foldlM_inv' (fun levels : List (List Digest) => ∀ j, (levels.getD j []).length ≤ 2 ^ h) _ _
    ?_ ?_ [leaves] ?_
  · intro level _ levels hI T
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    refine getD_append_length_le' hI ?_
    rw [lowerLevel_length']
    exact le_trans (Nat.div_le_self _ _) (hI _)
  · intro level hlv levels hI
    refine Respects.bind (respects_lowerLevel' _ _ _ _ _ fun i left right hi => hS level i left right (hl level hlv)
      ?_) fun _ => Respects.pure' _
    have := hI (level - 1)
    exact lt_of_lt_of_le hi (Nat.div_le_div_right this)
  · intro j
    cases j with
    | zero => simpa using hlen
    | succ j => simp
theorem respects_lowerLevels' {S : Spec.Domain → Prop} {lay tree h : Nat} (hS : FoldOK S lay tree h)
    (leaves : List Digest) (hlen : leaves.length ≤ 2 ^ h) : Respects S (WCT9.lowerLevels lay tree h leaves) := by
  unfold WCT9.lowerLevels
  exact respects_lowerFold' hS _ (fun x hx => (List.mem_range'_1.mp hx).1) leaves hlen
theorem respects_buildLevelsBelow' {S : Spec.Domain → Prop} {lay tree h : Nat} (hS : FoldOK S lay tree h)
    (tag : Nat) (leaves : List Digest) (hlen : leaves.length ≤ 2 ^ h) :
    Respects S (WCT9.buildLevelsBelow tag lay tree h leaves) := by
  unfold WCT9.buildLevelsBelow
  exact respects_lowerFold' hS _ (fun x hx => (List.mem_range'_1.mp hx).1) leaves hlen
theorem lowerHeap_lt' {h level i : Nat} (hlev : 1 ≤ level) (h7 : h ≤ 7) (hi : i < 2 ^ h / 2) :
    2 ^ (h - level) + i < 128 := by
  have hA : 2 ^ (h - level) ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : 2 ^ h ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) h7
  have h128 : (2 : Nat) ^ 7 = 128 := by norm_num
  rcases Nat.eq_zero_or_pos h with hz | hpos
  · subst hz; simp at hi
  · have hB : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
    omega
theorem untouchedP_of_hdr (a : ChainAddr) (input : HashInput) (h : BitVec 128)
    (hblock : SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, step < 7 → h ≠ chainHeader l tr leaf i step) :
    UntouchedP a (.inl (.inr input)) := by
  intro step value hs heq
  have hb : SigGolfCandidate.T3M.Extract.hdrBlock (chainRowW a step value) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain step) :=
    WCT9.chainInputW_header _ _ _ _ _ _
  rw [heq, hb] at hblock
  exact htag _ _ _ _ _ hs (bytesLE_injective hblock).symm
theorem untouchedP_of_length (a : ChainAddr) (input : HashInput) (hl : input.length ≠ 64) :
    UntouchedP a (.inl (.inr input)) := by
  intro step value _ heq
  apply hl
  rw [heq, chainRowW_length]
theorem pad64_long_length {input : HashInput} (hl : 64 < input.length) : (pad64 input).length ≠ 64 := by
  have : input.length ≤ (pad64 input).length := by
    simp only [pad64, List.length_append, List.length_replicate]; omega
  omega
/-- A Merkle node tweak of the current scheme is no chain header at a chain step (`< 7`): the C4 top label's low word
is `topNodeWord heap < 4096` while a chain header's low word has byte7 193; a lower node word has byte1 `7` while a
chain header at step `< 7` has byte1 `≡ step (mod 8)`. -/
theorem merkleTweak_ne_chainHeader {lay tree heap : Nat} (hh : lay = 0 ∨ heap < 128) (l : Layer)
    (tr leaf i step : Nat) (hs : step < 7) : WCT9.merkleTweak lay tree heap ≠ chainHeader l tr leaf i step := by
  unfold WCT9.merkleTweak
  split_ifs with h0
  · intro he
    have hl := congrArg (fun x : BitVec 128 => (x.extractLsb' 0 64).toNat) he
    have hb := (WCT9.chainHeader_low_band l tr leaf i step).1
    have ht := nodeTweak_top_low tree heap
    have := topNodeWord_lt heap
    unfold tweakLow at ht
    have hn : ((nodeTweak 3 0 tree heap).extractLsb' 0 64).toNat = topNodeWord heap := by
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]; exact ht
    rw [hn] at hl
    omega
  · exact WCT9.lowerTweak_ne_chainHeader (hh.resolve_left h0) _ _ _ _ _ _ _ (by omega)
section ProgramsW
variable (a : ChainAddr)
theorem respectsP_lowerNodeHash (lay tree heap : Nat) (left right : Digest) (hh : lay = 0 ∨ heap < 128) :
    Respects (UntouchedP a) (WCT9.lowerNodeHash lay tree heap left right) :=
  respects_lowerNodeHash' _ _ _ _ _ (untouchedP_of_hdr a _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf i step hs => merkleTweak_ne_chainHeader hh l tr leaf i step hs)
theorem foldOK_untouchedP (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) : FoldOK (UntouchedP a) lay tree h := by
  intro level i left right hlev hi
  refine untouchedP_of_hdr a _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf c step hs => merkleTweak_ne_chainHeader ?_ l tr leaf c step hs
  by_cases h0 : lay = 0
  · exact Or.inl h0
  · exact Or.inr (lowerHeap_lt' hlev (h7 h0) hi)
theorem respectsP_lowerLevels (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (UntouchedP a) (WCT9.lowerLevels lay tree h leaves) :=
  respects_lowerLevels' (foldOK_untouchedP a lay tree h h7) leaves hlen
theorem respectsP_buildLevelsBelow (tag lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (UntouchedP a) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  respects_buildLevelsBelow' (foldOK_untouchedP a lay tree h h7) tag leaves hlen
theorem respectsP_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects (UntouchedP a) (WCT9.lowerLeafHash lay tree leaf ends) :=
  respects_lowerLeafHash' _ _ _ _ (untouchedP_of_length a _ (pad64_long_length
    (SigGolfCandidate.T3.Security.Wots.Enc.leafInput_long lay tree leaf ends hlen)))
end ProgramsW
end Mask
end ClaudeWCT.W9.T3.Security.Wots
