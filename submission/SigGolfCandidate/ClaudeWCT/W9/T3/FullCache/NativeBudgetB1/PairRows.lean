import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.ProducerDecodeV5

namespace ClaudeWCT.W9.T3.PairRows
open OracleComp OracleSpec ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial V_publicSearch public_randomOracle)
open ClaudeWCT.W9.T3.ProducerV5 (producerEncodingDecode)
open SigGolfCandidate.T3.Freshness (Avoids RowQ SearchQ RowQ.searchQ searchQ_digest avoids_pure avoids_bind preserves
  avoids_shortHash_of_ne)
open ClaudeWCT.WCT9 (LayerMsg layerEncodingInput pairEncodingInputP layerCounterSearch)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) : HashInput :=
  pairEncodingInputP lay tree leaf left right (BitVec.ofNat 32 counter) 0
def layerTrial (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) : HashInput :=
  pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))
def msgLeft : LayerMsg → Digest
  | .forest root => root
  | .pair left _ => left
def msgRight : LayerMsg → Digest
  | .forest _ => 0
  | .pair _ right => right
theorem pairTrial_length (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    (pairTrial lay tree leaf left right counter).length = 64 := by
  simp [pairTrial, pairEncodingInputP, bytesLE_length]
theorem pad64_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    pad64 (pairTrial lay tree leaf left right counter) = pairTrial lay tree leaf left right counter := by
  simp [pad64, pairTrial_length]
theorem layerTrial_eq (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    layerTrial lay tree leaf msg counter = pairTrial lay tree leaf (msgLeft msg) (msgRight msg) counter := by
  cases msg with
  | forest root =>
      have h12 : bytesLE 12 (0 : BitVec 96) = List.replicate 12 0 := by decide
      have h16 : bytesLE 16 (0 : Digest) = List.replicate 16 0 := by decide
      simp only [layerTrial, pairTrial, layerEncodingInput, encodingInput, pairEncodingInputP, msgLeft,
        msgRight, pad64, List.length_append, bytesLE_length, h12, h16, List.append_assoc,
        List.replicate_append_replicate]
  | pair left right =>
      exact pad64_pairTrial lay tree leaf left right counter
theorem layerTrial_length (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) :
    (layerTrial lay tree leaf msg counter).length = 64 := by
  rw [layerTrial_eq, pairTrial_length]
theorem pairTrial_coordinates {lay lay' : Layer} {tree tree' leaf leaf' : Nat} {left left' right right' : Digest}
    {counter counter' : Nat} (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (hc : counter < 2 ^ 32) (hc' : counter' < 2 ^ 32)
    (he : pairTrial lay tree leaf left right counter = pairTrial lay' tree' leaf' left' right' counter') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ left = left' ∧ right = right' ∧ counter = counter' := by
  unfold pairTrial pairEncodingInputP at he
  obtain ⟨he, hR⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, hC⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨hL, hH⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨hlay, htree, hleaf⟩ := rowTweak_injective hl hr hl' hr' (bytesLE_injective hH)
  have hC := congrArg BitVec.toNat (bytesLE_injective hC)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at hC
  exact ⟨hlay, htree, hleaf, bytesLE_injective hL, bytesLE_injective hR, hC⟩
theorem pairTrial_injective (lay : Layer) (tree leaf : Nat) (left right : Digest) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (he : pairTrial lay tree leaf left right c = pairTrial lay tree leaf left right c') : c = c' := by
  unfold pairTrial pairEncodingInputP at he
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨he, -⟩ := List.append_inj he (by simp [bytesLE_length])
  obtain ⟨-, hC⟩ := List.append_inj he (by simp [bytesLE_length])
  have hC := congrArg BitVec.toNat (bytesLE_injective hC)
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] using hC
theorem layerTrial_injective (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (he : layerTrial lay tree leaf msg c = layerTrial lay tree leaf msg c') : c = c' := by
  rw [layerTrial_eq, layerTrial_eq] at he
  exact pairTrial_injective lay tree leaf _ _ hc hc' he
@[simp] theorem queryHeader_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    SigGolfCandidate.T3.QuerySpace.queryHeader (pairTrial lay tree leaf left right counter) =
      bytesLE 16 (rowTweak lay tree leaf) := by
  simp [SigGolfCandidate.T3.QuerySpace.queryHeader, pairTrial, pairEncodingInputP, List.append_assoc,
    bytesLE_length]
theorem rowQ_pairTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat) :
    RowQ (pairTrial lay tree leaf left right counter) :=
  ⟨rowTweak lay tree leaf, queryHeader_pairTrial .., rowTweak_marker .., rowTweak_tag .., rowTweak_high ..⟩
theorem pairTrial_ne_of_layer {lay other : Layer} (hne : lay ≠ other) (tree leaf : Nat) (left right : Digest)
    (counter : Nat) (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    pairTrial lay tree leaf left right counter ≠ pairTrial other tree' leaf' left' right' counter' := by
  intro he
  have hh := congrArg SigGolfCandidate.T3.QuerySpace.queryHeader he
  simp only [queryHeader_pairTrial] at hh
  have hw := (append64_inj (bytesLE_injective hh)).2
  have hl := congrArg (fun w : BitVec 64 => w.toNat / 2 ^ 48 % 256) hw
  simp only [hyperWord_toNat] at hl
  have h1 := lay.isLt
  have h2 := other.isLt
  have := Nat.mod_lt (tree * 2 ^ height lay + leaf) (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt (tree' * 2 ^ height other + leaf') (show 0 < 2 ^ 32 by decide)
  exact hne (Fin.ext (by omega))
theorem pairTrial_ne_digestTrial (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : Nat)
    (rho : Digest) (message : Message) (ctr : Nat) :
    pairTrial lay tree leaf left right counter ≠ digestTrial rho message ctr := by
  intro he
  have hh := congrArg SigGolfCandidate.T3.QuerySpace.queryHeader he
  rw [queryHeader_pairTrial, SigGolfCandidate.T3.QuerySpace.queryHeader_digest] at hh
  exact digestHeader_ne_rowTweak _ lay tree leaf (bytesLE_injective hh).symm
theorem layerCounterSearch_public (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, layerCounterSearch lay tree leaf msg counter fuel =
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (layerTrial lay tree leaf msg) (producerEncodingDecode lay)
        (fun c digits => pure (BitVec.ofNat 32 c, digits)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [ClaudeWCT.WCT9.layerCounterSearch, SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, SigGolfCandidate.T3.Sampling.publicHandler,
        ClaudeWCT.WCT9.encodingHash, shortHash, publicHash, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind, layerTrial, producerEncodingDecode]
      apply bind_congr
      intro answer
      cases hd : ClaudeWCT.WCT9.producerDecode lay (ClaudeWCT.WCT9.encodingAnswer lay answer) <;>
        simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]
theorem V_layerCounterSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (hstep : z * (SphincsSecurity.Completeness.failMass (producerEncodingDecode lay) * b +
      (1 - SphincsSecurity.Completeness.failMass (producerEncodingDecode lay))) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    V secret z (layerCounterSearch lay tree leaf msg counter fuel) cache ≤ b := by
  rw [layerCounterSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2 ^ 32)
    (fun c _ => layerTrial_length lay tree leaf msg c)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    hstep fuel counter hlimit cache hfresh
theorem layerCounterSearch_failure (secret : BitVec 256) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl
        (realize secret (layerCounterSearch lay tree leaf msg counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass (producerEncodingDecode lay) ^ fuel := by
  rw [layerCounterSearch_public, public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    fuel counter hlimit cache hfresh
theorem bound_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, Cost.CBound (Cost.CounterResult lay) fuel (layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [Cost.CounterResult])
  | succ fuel ih =>
      intro counter
      unfold ClaudeWCT.WCT9.layerCounterSearch
      refine (ClaudeWCT.WCT9.Cost.bound_encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) 1
        (by cases msg <;> simp [layerEncodingInput, encodingInput, pairEncodingInputP, bytesLE_length])
        (by rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
              layerTrial lay tree leaf msg counter from rfl, layerTrial_length])).bind'
        (l := fuel) (fun answer _ => ?_) (by omega)
      cases hs : ClaudeWCT.WCT9.producerDecode lay answer with
      | none => exact ih (counter + 1)
      | some digits =>
          have hd := ClaudeWCT.WCT9.producerDecode_decode hs
          refine .pure (some (BitVec.ofNat 32 counter, digits)) fuel ?_
          intro other values hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨(decode_length_sum hd).1, (decode_length_sum hd).2, Cost.validDigits_decode hd⟩
theorem layerCounterSearch_none_iff (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat)
    (msg : LayerMsg) :
    ∀ fuel counter,
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) = none ↔
      ∀ offset, offset < fuel → ClaudeWCT.WCT9.producerDecode lay (evalWithAnswerFn answers
        (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (counter + offset))))) = none := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [ClaudeWCT.WCT9.layerCounterSearch]
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.layerCounterSearch, evalWithAnswerFn_bind]
      cases hd : ClaudeWCT.WCT9.producerDecode lay (evalWithAnswerFn answers
        (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd, ih]
          constructor
          · intro hall offset hoff
            cases offset with
            | zero => simpa using hd
            | succ offset =>
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall offset (by omega)
          · intro hall offset hoff
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall (offset + 1) (by omega)
      | some digits =>
          simp only [hd, evalWithAnswerFn_pure, reduceCtorEq, false_iff]
          intro hall
          have := hall 0 (by omega)
          simp only [Nat.add_zero, hd, reduceCtorEq] at this
theorem eval_shortHash_layer (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg)
    (counter : Nat) :
    evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))) =
      ClaudeWCT.WCT9.encodingAnswer lay
        (answers (.inl (.inr (pairTrial lay tree leaf (msgLeft msg) (msgRight msg) counter)))) := by
  rw [ClaudeWCT.WCT9.eval_encodingHash, ← layerTrial_eq]
  rfl
theorem layerCounterSearch_forest_eval (answers : Correctness.Answers) (lay : Layer) (tree leaf : Nat)
    (root : Digest) : ∀ fuel counter,
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf (.forest root) counter fuel) =
        evalWithAnswerFn answers (layerCounterSearch lay tree leaf (.pair root 0) counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      have hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf (.forest root)
            (BitVec.ofNat 32 counter))) =
          evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf (.pair root 0)
            (BitVec.ofNat 32 counter))) := by
        rw [eval_shortHash_layer, eval_shortHash_layer]
        rfl
      simp only [ClaudeWCT.WCT9.layerCounterSearch, evalWithAnswerFn_bind, hs]
      cases hd : ClaudeWCT.WCT9.producerDecode lay (evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf
        (.pair root 0) (BitVec.ofNat 32 counter)))) <;> simp only [hd, ih]
def PairFreshBelow (n : Nat) (cache : RCache) : Prop :=
  ∀ lay : Layer, lay.val < n → ∀ tree leaf left right c, c < 2 ^ 32 →
    cache (pairTrial lay tree leaf left right c) = none
def AllSearchesFreshBC (cache : RCache) : Prop :=
  (∀ rho message c, c < 2 ^ 32 → cache (digestTrial rho message c) = none) ∧ PairFreshBelow 4 cache
@[simp] theorem allSearchesFreshBC_empty : AllSearchesFreshBC ∅ := by
  constructor
  · intro rho message c hc; rfl
  · intro lay hl tree leaf left right c hc; rfl
theorem PairFreshBelow.layerTrial {n : Nat} {cache : RCache} (h : PairFreshBelow n cache) (lay : Layer)
    (hl : lay.val < n) (tree leaf : Nat) (msg : LayerMsg) (c : Nat) (hc : c < 2 ^ 32) :
    cache (layerTrial lay tree leaf msg c) = none := by
  rw [layerTrial_eq]
  exact h lay hl tree leaf _ _ c hc
theorem PairFreshBelow.mono {n m : Nat} {cache : RCache} (h : PairFreshBelow n cache) (hm : m ≤ n) :
    PairFreshBelow m cache :=
  fun lay hl => h lay (by omega)
theorem avoids_layerCounterSearch (secret : BitVec 256) {lay other : Layer} (hne : lay ≠ other)
    (tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    Avoids secret (pairTrial other tree' leaf' left' right' counter')
      (layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold ClaudeWCT.WCT9.layerCounterSearch
      apply avoids_bind
      · apply avoids_shortHash_of_ne
        rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
          layerTrial lay tree leaf msg counter from rfl, layerTrial_eq]
        exact pairTrial_ne_of_layer hne tree leaf _ _ counter tree' leaf' left' right' counter'
      · intro answer
        split
        · exact ih _
        · exact avoids_pure _ _ _
theorem preserves_pairBelow {α : Type} (secret : BitVec 256) (program : M α)
    (h : ∀ target, RowQ target → Avoids secret target program)
    (n : Nat) (cache : RCache) (hc : PairFreshBelow n cache) (result : α × RCache)
    (hr : result ∈ support (roRun secret program cache)) : PairFreshBelow n result.2 := by
  intro lay hl tree leaf left right c hlt
  rw [preserves secret _ program (h _ (rowQ_pairTrial ..)) cache result hr]
  exact hc lay hl tree leaf left right c hlt
theorem preserves_allSearchesBC {α : Type} (secret : BitVec 256) (program : M α)
    (h : ∀ target, SearchQ target → Avoids secret target program)
    (cache : RCache) (hc : AllSearchesFreshBC cache) (result : α × RCache)
    (hr : result ∈ support (roRun secret program cache)) : AllSearchesFreshBC result.2 := by
  constructor
  · intro rho message c hlt
    rw [preserves secret _ program (h _ (searchQ_digest ..)) cache result hr]
    exact hc.1 rho message c hlt
  · exact preserves_pairBelow secret program (fun target ht => h target ht.searchQ) 4 cache hc.2 result hr
theorem avoids_digestSearch_encoding (secret : BitVec 256) (target : HashInput) (ht : RowQ target)
    (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids secret target (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold ClaudeWCT.WCT9.digestSearch
      refine avoids_bind (SigGolfCandidate.T3.Freshness.avoids_digest_encoding secret target ht rho message _) ?_
      intro output
      split
      · exact avoids_pure _ _ _
      · exact ih _
theorem digestSearch_preserves_pairBelow (secret : BitVec 256) (rho : Digest) (message : Message)
    (counter fuel : Nat) (cache : RCache) (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache)) :
    PairFreshBelow 4 result.2 :=
  preserves_pairBelow secret _ (fun target ht => avoids_digestSearch_encoding secret target ht rho message _ _)
    4 cache hc.2 result hr
theorem privateMac_preserves_fresh (secret : BitVec 256) (region : Region) (cache : RCache)
    (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (privateMac region) cache)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret _
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_privateMac secret target ht region) cache hc result hr
theorem privateNonce_preserves_fresh (secret : BitVec 256) (message : Message) (cache : RCache)
    (hc : AllSearchesFreshBC cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret (privateNonce message) cache)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret _
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_privateNonce secret target ht message) cache hc result hr
theorem keygen_fresh_from_empty_bc (secret : BitVec 256) (result : (Digest × Cache) × RCache)
    (hr : result ∈ support (roRun secret keygen ∅)) : AllSearchesFreshBC result.2 :=
  preserves_allSearchesBC secret keygen
    (fun target ht => SigGolfCandidate.T3.Freshness.avoids_keygen secret target ht) ∅
    allSearchesFreshBC_empty result hr
end ClaudeWCT.W9.T3.PairRows

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The selected 256-bit oracle answer, with the canonical per-leaf floor. -/
def decoder (lay : Layer) (floor : Nat) (answer : HashOutput) : Option (List Nat) :=
  CanonicalPolicy.producerDecodeAt lay floor (encodingAnswer lay answer)

theorem search_public (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel =
      publicProgram (searchLoop (layerTrial lay tree leaf msg) (decoder lay floor)
        (fun c digits => pure (BitVec.ofNat 32 c, digits)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [CanonicalPolicy.layerCounterSearchAt, searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query,
        SigGolfCandidate.T3.Sampling.publicHandler,
        encodingHash, shortHash, publicHash, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind, layerTrial, decoder]
      apply bind_congr
      intro answer
      cases hd : CanonicalPolicy.producerDecodeAt lay floor (encodingAnswer lay answer) <;>
        simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]

theorem search_failure (secret : BitVec 256) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (layerTrial lay tree leaf msg c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl (realize secret
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel))).run cache] ≤
      failMass (decoder lay floor) ^ fuel := by
  rw [search_public, public_randomOracle]
  exact probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    fuel counter hlimit cache hfresh

/-- A rejection search with a value-dependent continuation. The invariant tracks
fresh rows of later canonical ancestors/descendants independently of the floor. -/
theorem V_search_bind {β γ δ : Type} (secret : BitVec 256) (z b : ENNReal)
    (inputs : Nat → HashInput) (dec : HashOutput → Option β)
    (result : Nat → β → γ) (next : Option γ → M δ) (weight : β → ENNReal)
    (G : RCache → Prop) (bound : Nat)
    (hinput : ∀ counter, counter < bound → (inputs counter).length = 64)
    (hinj : ∀ left right, left < bound → right < bound →
      inputs left = inputs right → left = right)
    (hG : ∀ cache, G cache → ∀ counter, counter < bound → ∀ answer,
      G (cache.cacheQuery (inputs counter) answer))
    (hnone : ∀ cache, G cache → V secret z (next none) cache ≤ b)
    (hsome : ∀ cache, G cache → ∀ counter, counter < bound → ∀ answer value,
      dec answer = some value →
      V secret z (next (some (result counter value)))
        (cache.cacheQuery (inputs counter) answer) ≤ weight value)
    (hstep : z * (acceptedWeight dec weight + failMass dec * b) ≤ b) :
    ∀ fuel counter, counter + fuel ≤ bound → ∀ cache, G cache →
      (∀ c, counter ≤ c → c < bound → cache (inputs c) = none) →
      V secret z ((publicProgram (searchLoop inputs dec
        (fun c value => pure (result c value)) fuel counter)) >>= next) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache hg _
      simpa only [searchLoop, publicProgram, simulateQ_pure, pure_bind] using hnone cache hg
  | succ fuel ih =>
      intro counter hlimit cache hg hfresh
      rw [publicSearch_succ, bind_assoc, V_publicQuery, hinput counter (by omega)]
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      rw [expectedValue_fresh _ _ (hfresh counter le_rfl (by omega))]
      calc
        _ ≤ z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
            (fun answer => (dec answer).elim b weight) := by
          apply mul_le_mul' le_rfl
          apply expectedValue_mono
          intro answer
          cases hd : dec answer with
          | some value =>
              simp only [pure_bind, Option.elim_some]
              exact hsome cache hg counter (by omega) answer value hd
          | none =>
              simp only [Option.elim_none]
              apply ih (counter + 1) (by omega) _ (hG cache hg counter (by omega) answer)
              intro c hstart hc
              rw [QueryCache.cacheQuery_of_ne]
              · exact hfresh c (by omega) hc
              · intro he
                have := hinj c counter hc (by omega) he
                omega
        _ = z * (acceptedWeight dec weight + failMass dec * b) := by
          rw [uniform_decoder_weight]
        _ ≤ b := hstep

#print axioms search_public
#print axioms search_failure
#print axioms V_search_bind
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem acceptedWeight_mul {β : Type} (dec : HashOutput → Option β)
    (weight : β → ENNReal) (factor : ENNReal) :
    acceptedWeight dec (fun value => factor * weight value) =
      factor * acceptedWeight dec weight := by
  unfold acceptedWeight
  have he (answer : HashOutput) :
      (dec answer).elim 0 (fun value => factor * weight value) =
        factor * (dec answer).elim 0 weight := by
    cases dec answer <;> simp
  simp_rw [he]
  exact ev_const_mul _ _ _

theorem scaled_step {β : Type} (z b factor : ENNReal) (dec : HashOutput → Option β)
    (weight : β → ENNReal)
    (hstep : z * (acceptedWeight dec weight + failMass dec * b) ≤ b) :
    z * (acceptedWeight dec (fun value => factor * weight value) +
      failMass dec * (factor * b)) ≤ factor * b := by
  rw [acceptedWeight_mul]
  have he : z * (factor * acceptedWeight dec weight + failMass dec * (factor * b)) =
      factor * (z * (acceptedWeight dec weight + failMass dec * b)) := by ring
  rw [he]
  exact mul_le_mul' le_rfl hstep

#print axioms acceptedWeight_mul
#print axioms scaled_step
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private theorem expected_finite_sum {α ι : Type} [DecidableEq ι] (law : ProbComp α)
    (s : Finset ι) (f : ι → α → ENNReal) :
    expectedValue law (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, expectedValue law (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectedValue_def]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [expectedValue_add, ih]

/-- Group success-weighted continuation costs by a finite credit label. -/
theorem acceptedWeight_labels {β ι : Type} [Fintype ι] [DecidableEq ι]
    (dec : HashOutput → Option β) (label : β → ι) (weight : ι → ENNReal) :
    acceptedWeight dec (fun value => weight (label value)) =
      ∑ i : ι, Pr[fun answer => ∃ value, dec answer = some value ∧ label value = i |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight i := by
  classical
  have he (answer : HashOutput) :
      (dec answer).elim 0 (fun value => weight (label value)) =
        ∑ i : ι, (if ∃ value, dec answer = some value ∧ label value = i
          then 1 else 0) * weight i := by
    cases hd : dec answer with
    | none => simp
    | some value =>
        simp only [Option.elim_some]
        rw [Finset.sum_eq_single (label value)]
        · rw [if_pos (show ∃ other, some value = some other ∧ label other = label value
            from ⟨value, rfl, rfl⟩), one_mul]
        · intro i _ hi
          have hn : ¬ ∃ other, some value = some other ∧ label other = i := by
            rintro ⟨other, heq, hlabel⟩
            cases heq
            exact hi hlabel.symm
          rw [if_neg hn, zero_mul]
        · simp
  unfold acceptedWeight
  simp_rw [he]
  rw [expected_finite_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectedValue_mul_const, expectedValue_ite_one]

/-- The failure mass is the complement of the total finite labelled mass. -/
theorem failMass_labels {β ι : Type} [Fintype ι] [DecidableEq ι]
    (dec : HashOutput → Option β) (label : β → ι) :
    failMass dec = 1 - ∑ i : ι, Pr[fun answer =>
      ∃ value, dec answer = some value ∧ label value = i |
      ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  have hm : acceptedWeight dec (fun _ => (1 : ENNReal)) + failMass dec = 1 := by
    have h := uniform_decoder_weight dec (fun _ => (1 : ENNReal)) 1
    have he (answer : HashOutput) : (dec answer).elim (1 : ENNReal) (fun _ => 1) = 1 := by
      cases dec answer <;> rfl
    simp_rw [he] at h
    rw [expectedValue_const (by simp)] at h
    simpa only [mul_one] using h.symm
  have hs := acceptedWeight_labels dec label (fun _ => (1 : ENNReal))
  simp only [mul_one] at hs
  rw [hs] at hm
  have hle : (∑ x, Pr[fun answer => ∃ value, dec answer = some value ∧ label value = x |
      ($ᵗ HashOutput : ProbComp HashOutput)]) ≤ 1 := by
    calc
      _ ≤ _ + failMass dec := le_add_right le_rfl
      _ = 1 := hm
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (by simp) hle)
    ((add_comm _ _).trans hm)

#print axioms acceptedWeight_labels
#print axioms failMass_labels
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem acceptedWeight_nat_labels {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat) (weight : Nat → ENNReal)
    (hbound : ∀ answer value, dec answer = some value → credit value < n) :
    acceptedWeight dec (fun value => weight (credit value)) =
      ∑ i : Fin n, Pr[fun answer => ∃ value,
        dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight i.val := by
  classical
  let label : β → Fin n := fun value => Fin.ofNat n (credit value)
  have he : acceptedWeight dec (fun value => weight (credit value)) =
      acceptedWeight dec (fun value => weight (label value).val) := by
    unfold acceptedWeight
    congr 1
    funext answer
    cases hd : dec answer with
    | none => rfl
    | some value =>
        simp only [Option.elim_some, label, Fin.val_ofNat]
        rw [Nat.mod_eq_of_lt (hbound answer value hd)]
  rw [he, acceptedWeight_labels dec label (fun i => weight i.val)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply probEvent_congr'
  · intro answer _
    constructor
    · rintro ⟨value, hd, hi⟩
      refine ⟨value, hd, ?_⟩
      have hv := congrArg Fin.val hi
      simpa only [label, Fin.val_ofNat, Nat.mod_eq_of_lt (hbound answer value hd)] using hv
    · rintro ⟨value, hd, hi⟩
      exact ⟨value, hd, Fin.ext (by
        simp only [label, Fin.val_ofNat, Nat.mod_eq_of_lt (hbound answer value hd), hi, Nat.mod_eq_of_lt i.isLt])⟩
  · rfl

#print axioms acceptedWeight_nat_labels
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def RowsFreshFrom (stage : Nat) (cache : RCache) : Prop :=
  ∀ lay : Layer, stage ≤ lay.val → ∀ tree leaf left right counter,
    counter < 2 ^ 32 → cache (pairTrial lay tree leaf left right counter) = none

theorem RowsFreshFrom.mono {stage next : Nat} {cache : RCache}
    (h : RowsFreshFrom stage cache) (hle : stage ≤ next) : RowsFreshFrom next cache :=
  fun lay hl => h lay (hle.trans hl)

theorem RowsFreshFrom.layer {stage : Nat} {cache : RCache}
    (h : RowsFreshFrom stage cache) (lay : Layer) (hle : stage ≤ lay.val)
    (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) (hc : counter < 2 ^ 32) :
    cache (layerTrial lay tree leaf msg counter) = none := by
  rw [layerTrial_eq]
  exact h lay hle tree leaf _ _ counter hc

theorem RowsFreshFrom.cacheQuery {stage : Nat} {cache : RCache}
    (h : RowsFreshFrom stage cache) (lay : Layer) (hl : lay.val < stage)
    (tree leaf : Nat) (msg : LayerMsg) (counter : Nat) (answer : HashOutput) :
    RowsFreshFrom stage (cache.cacheQuery (layerTrial lay tree leaf msg counter) answer) := by
  intro other ho tree' leaf' left right counter' hc
  rw [QueryCache.cacheQuery_of_ne]
  · exact h other ho tree' leaf' left right counter' hc
  · rw [layerTrial_eq]
    exact pairTrial_ne_of_layer (by intro he; subst other; omega)
      tree' leaf' left right counter' tree leaf _ _ counter

/-- A canonical stage can spend credit on its continuation while preserving all
later layers' fresh rows. No independence of the chosen floor is assumed here. -/
theorem V_layerSearch_bind {α : Type} (secret : BitVec 256) (z b : ENNReal)
    (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg)
    (next : Option (BitVec 32 × List Nat) → M α) (weight : List Nat → ENNReal)
    (hnone : ∀ cache, RowsFreshFrom (lay.val + 1) cache → V secret z (next none) cache ≤ b)
    (hsome : ∀ cache, RowsFreshFrom (lay.val + 1) cache →
      ∀ counter, counter < 2 ^ 32 → ∀ answer digits,
      decoder lay floor answer = some digits →
      V secret z (next (some (BitVec.ofNat 32 counter, digits))) cache ≤ weight digits)
    (hstep : z * (acceptedWeight (decoder lay floor) weight +
      failMass (decoder lay floor) * b) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : RCache) (hfresh : RowsFreshFrom lay.val cache) :
    V secret z (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel >>= next)
      cache ≤ b := by
  rw [search_public]
  apply V_search_bind secret z b _ _ _ next weight (RowsFreshFrom (lay.val + 1)) (2 ^ 32)
    (fun c _ => layerTrial_length lay tree leaf msg c)
    (fun _ _ hl hr he => layerTrial_injective lay tree leaf msg hl hr he)
    (fun cache hg counter _ answer => hg.cacheQuery lay (by omega) tree leaf msg counter answer)
    hnone
    (fun cache hg counter hc answer digits hd => hsome _
      (hg.cacheQuery lay (by omega) tree leaf msg counter answer) counter hc answer digits hd)
    hstep fuel counter hlimit cache (hfresh.mono (by omega))
  intro c _ hc
  exact hfresh.layer lay le_rfl tree leaf msg c hc

#print axioms V_layerSearch_bind
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.Freshness
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem avoids_search (secret : BitVec 256) {lay other : Layer} (hne : lay ≠ other)
    (floor tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (tree' leaf' : Nat) (left' right' : Digest) (counter' : Nat) :
    Avoids secret (pairTrial other tree' leaf' left' right' counter')
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold CanonicalPolicy.layerCounterSearchAt
      apply avoids_bind
      · apply avoids_shortHash_of_ne
        rw [show pad64 (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)) =
          layerTrial lay tree leaf msg counter from rfl, layerTrial_eq]
        exact pairTrial_ne_of_layer hne tree leaf _ _ counter tree' leaf' left' right' counter'
      · intro answer
        split
        · exact ih _
        · exact avoids_pure _ _ _

theorem search_preserves_rows (secret : BitVec 256) (lay : Layer)
    (floor tree leaf : Nat) (msg : LayerMsg) (counter fuel : Nat)
    (cache : RCache) (hfresh : RowsFreshFrom (lay.val + 1) cache)
    (result : Option (BitVec 32 × List Nat) × RCache)
    (hr : result ∈ support (roRun secret
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) cache)) :
    RowsFreshFrom (lay.val + 1) result.2 := by
  intro other ho tree' leaf' left right counter' hc
  rw [preserves secret _ _ (avoids_search secret (by intro he; subst other; omega)
    floor tree leaf msg counter fuel tree' leaf' left right counter') cache result hr]
  exact hfresh other ho tree' leaf' left right counter' hc

#print axioms avoids_search
#print axioms search_preserves_rows
end ClaudeWCT.W9.T3.CanonicalSearch
