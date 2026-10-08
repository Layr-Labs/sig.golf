import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingShort
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeContactCase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.FtsOverflow
import SigGolfCandidate.T3.Secc.LargeCouplingTable

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell runWith_bind)
open ClaudeWCT.W9.T3.Security.FamResidual (observedRun)
open SigGolfCandidate.T3.Security.LargeCoupling (keygen_record)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingTable : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Table
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
noncomputable def keyState (U : Finset HashInput) (q : Nat) (vals : Coord → Digest) (nv : Message → Digest) :
    LargeResidual.State WCoord (Cell U) :=
  discloseStates U q (Sum.elim vals nv) LargeResidual.initial keygenDisclosed
theorem rel_initial :
    Rel U T vals nv τ a q Monitor.initial RouterState.initial (keyState U q vals nv) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) keygenDisclosed
    (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) keygenDisclosed
    (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
  unfold keyState
  refine ⟨rfl, rfl, rfl, by rw [hc]; rfl, by rw [hc]; rfl, rfl, by rw [hc]; exact le_rfl, Nat.zero_le _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact Finset.mem_univ _
  · intro c hck
    rw [discloseStates_candidates, if_neg, hc]
    · simp only [LargeResidual.initial, Finset.card_univ, Nat.sub_zero]
      simp [SphincsSecurity.digestBits]
    · intro hm
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      rw [Sum.inl.inj hdc] at hd
      exact hck (Known.base (Or.inl hd))
  · intro row v hv
    rw [hr] at hv
    cases hv
  · intro row v hv
    rw [hr] at hv
    cases hv
  · intro X hX
    cases hX
  · intro X hX
    cases hX
theorem canonical_split (adversary : AdversaryP) (T : Answers)
    (t : Tagged (Option ForgeryP))
    (ht : t ∈ support (taggedFixed T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
      (Wots.Ref.pureRecord T keygen (∅, ∅)).state)) :
    TaggedSplit adversary (Wots.Ref.combine T t.untag) (Wots.Ref.pureRecord T keygen (∅, ∅)) t
      (Wots.Ref.verdictRecord T t.untag) := by
  obtain ⟨hk, hka⟩ := keygen_record T
  have hval : (Wots.Ref.pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen :=
    Wots.Ref.pureRecord_value T keygen (∅, ∅)
  obtain ⟨ht1, ht2⟩ := taggedFixed_support T _ _ _ hka t ht
  refine ⟨hk, by rw [hval]; exact ht1, ?_, rfl⟩
  have hv := Wots.Ref.fixedRecord_mem_record T
    (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) t.state ht2
    (Wots.Ref.verdictRecord T t.untag)
    (by rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.verdict_hashOnly _ _), mem_support_pure_iff]; rfl)
  rw [hval]
  exact hv.1
noncomputable def verdictContact (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (value : Option ForgeryP × QueryLog Requests) (state : LazyPrivate.State) : Prop :=
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = true
noncomputable def verdictCont (U : Finset HashInput) (a : AuxData) (q : Nat) (pk : Digest)
    (r : Option ((Option ForgeryP × QueryLog Requests) × RouterState)) :
    OracleComp (RWorld U) (Option (Bool × RouterState)) :=
  match r with
  | none => pure none
  | some (result, st) => routeVerdict U a q (GameWith.verdict PaddedGame.checker pk result) st
theorem Coherent.routerWith (hcoh : Coherent U T vals nv τ a) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
    (adversary : AdversaryP) :
    observedRun aux q (Sum.elim vals nv) τ (routerWith U adversary q a) LargeResidual.initial =
      observedRun aux q (Sum.elim vals nv) τ
        (routeInteraction U a (evalWithAnswerFn T keygen).2 q
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) RouterState.initial >>=
            verdictCont U a q (evalWithAnswerFn T keygen).1) (keyState U q vals nv) := by
  unfold LargeResidual.routerWith
  rw [observed_discloseAll]
  have hkv : lookupVal (List.map (fun c => (c, Sum.elim vals nv (Sum.inl c))) keygenDisclosed) = keyValues vals :=
    rfl
  simp only [hkv]
  rw [hcoh.published, hcoh.pk]
  rfl
end Table
section Overflow
/-- FTS seeds of family `f` opened by the signatures of a log (digit 4 words open the seed; T8: at most one per word). -/
@[irreducible] noncomputable def logSeeds (T : Answers) (log : QueryLog Requests) (f : Fin (2 ^ 31) × Fin 9) :
    Finset CanonGraph.WctAddr :=
  Finset.univ.filter fun w => (w.1, w.2.1) = f ∧ ∃ N ∈ WPair.loggedOutputs T log, digestIndex N = w.1 ∧
    WCT9.child N w.2.1 = w.2.2.1 ∧ WCT9.wordDigit (WCT9.rank N w.2.1) w.2.2.2 = 4
theorem mem_logSeeds (T : Answers) (log : QueryLog Requests) (f : Fin (2 ^ 31) × Fin 9) (w : CanonGraph.WctAddr) :
    w ∈ logSeeds T log f ↔ (w.1, w.2.1) = f ∧ ∃ N ∈ WPair.loggedOutputs T log, digestIndex N = w.1 ∧
      WCT9.child N w.2.1 = w.2.2.1 ∧ WCT9.wordDigit (WCT9.rank N w.2.1) w.2.2.2 = 4 := by
  unfold logSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
theorem digitThree_card (r : WCT9.Rank) : (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit r t = 4).card ≤ 2 := by
  have hsum := WCT9.wordStep_count r
  have h1 : 4 * (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit r t = 4).card ≤
      ∑ t : Fin 6, WCT9.wordDigit r t := by
    calc 4 * (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit r t = 4).card
        = ∑ t ∈ Finset.univ.filter (fun t : Fin 6 => WCT9.wordDigit r t = 4), WCT9.wordDigit r t := by
          rw [Finset.sum_congr rfl (fun t ht => (Finset.mem_filter.mp ht).2), Finset.sum_const, smul_eq_mul,
            mul_comm]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega
theorem logSeeds_card (T : Answers) (log : QueryLog Requests) (hno : LogNoOverflow T log)
    (f : Fin (2 ^ 31) × Fin 9) : (logSeeds T log f).card ≤ 100 := by
  set S := (WPair.loggedOutputs T log).toFinset.filter fun out => ClaudeWCT.Bank.WCT.outIdx out = f.1
  have hsub : logSeeds T log f ⊆ S.biUnion fun N =>
      (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit (WCT9.rank N f.2) t = 4).image
        fun t => ((f.1, f.2, WCT9.child N f.2, t) : CanonGraph.WctAddr) := by
    intro w hw
    obtain ⟨hf, N, hN, hidx, hch, hdig⟩ := (mem_logSeeds T log f w).mp hw
    have h1 : w.1 = f.1 := congrArg Prod.fst hf
    have h2 : w.2.1 = f.2 := congrArg Prod.snd hf
    refine Finset.mem_biUnion.mpr ⟨N, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hN, ?_⟩, ?_⟩
    · rw [← h1, ← hidx]; rfl
    · refine Finset.mem_image.mpr ⟨w.2.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← h2]; exact hdig⟩, ?_⟩
      rw [← h2, hch, ← h1]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc _ ≤ ∑ N ∈ S, 2 := Finset.sum_le_sum fun N _ => Finset.card_image_le.trans (digitThree_card _)
    _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * 50 := Nat.mul_le_mul_left _ (hno f.1)
theorem logSeeds_cons (T : Answers) (e : QueryLog Requests) (log : QueryLog Requests) (f : Fin (2 ^ 31) × Fin 9) :
    logSeeds T log f ⊆ logSeeds T (e ++ log) f := by
  intro w hw
  obtain ⟨hf, N, hN, h⟩ := (mem_logSeeds T log f w).mp hw
  refine (mem_logSeeds T _ f w).mpr ⟨hf, N, ?_, h⟩
  rw [WPair.mem_loggedOutputs] at hN ⊢
  obtain ⟨entry, he, hrest⟩ := hN
  exact ⟨entry, List.mem_append_right _ he, hrest⟩
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
/-- The seeds a sign step discloses are opened by the logged signature of that step. -/
theorem signDisclosed_logSeeds (hcoh : Coherent U T vals nv τ a) (published : SigGolfCandidate.T3.Cache)
    (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T)) (request : Security.Request)
    (w : CanonGraph.WctAddr) (hw : (.inr (.inr w) : Coord) ∈ signDisclosed T published request) :
    w ∈ logSeeds T [⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩] (w.1, w.2.1) := by
  unfold signDisclosed at hw
  split_ifs at hw with hc
  swap
  · cases hw
  cases hsd : LargeResidual.signDigest T request.message with
  | none => rw [hsd] at hw; cases hw
  | some cn =>
      obtain ⟨c, N⟩ := cn
      rw [hsd] at hw
      simp only at hw
      split_ifs at hw with hok
      swap
      · cases hw
      obtain ⟨h1, h2, h3⟩ := wctItem_mem_signItemsWith _ N w 0 (Nat.zero_le _) (by rw [wctItem_zero]; exact hw)
      have hdig : WCT9.wordDigit (WCT9.rank N w.2.1) w.2.2.2 = 4 := by
        have := WCT9.wordDigit_le_four (WCT9.rank N w.2.1) w.2.2.2
        omega
      refine (mem_logSeeds T _ _ w).mpr ⟨rfl, N, ?_, h1.symm, h2.symm, hdig⟩
      rw [WPair.mem_loggedOutputs]
      refine ⟨_, List.mem_singleton_self _, assembleSig (nv request.message) N vals (Wots.referenceDigits T), ?_, ?_⟩
      · change evalWithAnswerFn T (FullGame.authenticatedSign published request) = _
        rw [finishOut_real hcoh published hpub request hc, hsd]
        unfold finishOut
        dsimp only
        rw [if_pos hok]
      · unfold CaseC.signedOutput
        have hrho : (assembleSig (nv request.message) N vals (Wots.referenceDigits T)).rho = nv request.message := rfl
        rw [hrho, ← hcoh.privateNonce]
        unfold LargeResidual.signDigest at hsd
        rw [hsd]
        rfl
/-- Router disclosures over a tagged run are covered by the seeds opened in its log. -/
theorem discSeeds_steps (hcoh : Coherent U T vals nv τ a) (published : SigGolfCandidate.T3.Cache)
    (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T)) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    ∀ (state : LazyPrivate.State) (t : Tagged α), t ∈ support (taggedFixed T published program state) →
      ∀ (st : RouterState) (f : Fin (2 ^ 31) × Fin 9),
        DiscSeeds (t.steps.foldl (routerStep U T nv published) st) f ⊆ DiscSeeds st f ∪ logSeeds T t.value.2 f := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro state t ht st f
      rw [taggedFixed_pure, mem_support_pure_iff] at ht
      subst ht
      exact Finset.subset_union_left
  | query_bind input next ih =>
      intro state t ht st f
      rcases input with world | request
      · rw [taggedFixed_world, mem_support_bind_iff] at ht
        obtain ⟨answer, -, ht⟩ := ht
        rw [support_map] at ht
        obtain ⟨last, hl, rfl⟩ := ht
        simp only [List.foldl_cons]
        have hst : DiscSeeds (routerStep U T nv published st (.world ⟨state, .inl world, answer⟩)) f =
            DiscSeeds st f := by
          have hd : (routerStep U T nv published st (.world ⟨state, .inl world, answer⟩)).disclosed = st.disclosed := by
            rcases world with n | X
            · rfl
            · exact RouterState.next_disclosed U st X answer
          unfold DiscSeeds
          rw [hd]
        have := ih answer _ last hl (routerStep U T nv published st (.world ⟨state, .inl world, answer⟩)) f
        rw [hst] at this
        exact this
      · rw [taggedFixed_request, mem_support_bind_iff] at ht
        obtain ⟨block, hb, ht⟩ := ht
        rw [support_map] at ht
        obtain ⟨last, hl, rfl⟩ := ht
        rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.authenticatedSign_hashOnly _ _), mem_support_pure_iff] at hb
        simp only [List.foldl_cons]
        have hih := ih block.value _ last hl (routerStep U T nv published st (.sign request block.value block.events)) f
        intro w hw
        rcases Finset.mem_union.mp (hih hw) with h | h
        · have hd : (routerStep U T nv published st (.sign request block.value block.events)).disclosed =
              st.disclosed ++ signDisclosed T published request := signedState_disclosed T nv published st request
          rw [mem_DiscSeeds, hd, List.mem_append] at h
          rcases h.2 with h2 | h2
          · exact Finset.mem_union_left _ ((mem_DiscSeeds st f w).mpr ⟨h.1, h2⟩)
          · apply Finset.mem_union_right
            have hls := signDisclosed_logSeeds hcoh published hpub request w h2
            have hv : block.value = evalWithAnswerFn T (FullGame.authenticatedSign published request) := by
              rw [hb]; exact Wots.Ref.pureRecord_value _ _ _
            rw [← h.1]
            obtain ⟨hf', N, hN, hrest⟩ := (mem_logSeeds T _ _ w).mp hls
            refine (mem_logSeeds T _ _ w).mpr ⟨hf', N, ?_, hrest⟩
            rw [WPair.mem_loggedOutputs] at hN ⊢
            obtain ⟨entry, he, hrest'⟩ := hN
            rw [List.mem_singleton] at he
            refine ⟨entry, ?_, hrest'⟩
            rw [he, hv]
            exact List.mem_cons_self
        · apply Finset.mem_union_right
          obtain ⟨hf', N, hN, hrest⟩ := (mem_logSeeds T _ _ w).mp h
          refine (mem_logSeeds T _ _ w).mpr ⟨hf', N, ?_, hrest⟩
          rw [WPair.mem_loggedOutputs] at hN ⊢
          obtain ⟨entry, he, hrest'⟩ := hN
          exact ⟨entry, List.mem_cons_of_mem _ he, hrest'⟩
theorem discSeeds_initial (f : Fin (2 ^ 31) × Fin 9) : DiscSeeds RouterState.initial f = ∅ := by
  ext w
  rw [mem_DiscSeeds]
  simp [RouterState.initial]
end Overflow
/-- No index carries more than 50 distinct signed outputs in the log of any game split. -/
def NoOvR (adversary : AdversaryP) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ g i c, CaseC.GameSplit adversary rec g i c → LogNoOverflow A i.value.2
theorem table_contact_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : Coherent (Wots.referenceInputs adversary) T vals nv τ a) :
    Pr[fun rec => ContactR adversary q rec T ∧ NoOvR adversary rec T |
        Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.referenceInputs adversary := Wots.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  rw [hcoh.routerWith, Wots.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 hpub
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictContact (Wots.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon
      value state ∧ FamOK st)
    (verdictCont (Wots.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) (fun r => r.1 = none ∧ r.2.counters.calls ≤ q)
    ?_ ?_ ?_ (fun _ _ _ _ h => h.2) Monitor.initial RouterState.initial (keyState (Wots.referenceInputs adversary) q vals nv) _
      rel_initial (fun _ _ h => by cases h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    have h := hc.1 _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h
    refine ⟨h, fun f => ?_⟩
    have hno : LogNoOverflow T t.value.2 := hc.2 _ _ _ hsplit.untag
    have hsub := discSeeds_steps hcoh (evalWithAnswerFn T keygen).2 hpub _ _ t ht RouterState.initial f
    rw [discSeeds_initial, Finset.empty_union] at hsub
    exact (Finset.card_le_card hsub).trans ((logSeeds_card T _ hno f).trans (by norm_num))
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PaddedGame.verdict_public _ _) mon st ws state hrel hf.2
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.referenceInputs adversary) a q (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    replace hf := hf.1
    unfold verdictContact at hf
    rcases hph with ⟨h1, -, h3⟩ | ⟨-, h2, -⟩ | ⟨-, h2⟩
    · rw [if_pos ⟨h1, h3⟩]
    · rw [hf] at h2; cases h2
    · have h4 := h2.contact
      rw [hf] at h4
      cases h4
  · intro m s v σ hf
    replace hf := hf.1
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    unfold verdictContact at hf
    rw [h.1] at hf
    cases hf
  · intro ws' hws
    exact ⟨rfl, hws⟩
end ClaudeWCT.W9.T3.Security.LargeCoupling
