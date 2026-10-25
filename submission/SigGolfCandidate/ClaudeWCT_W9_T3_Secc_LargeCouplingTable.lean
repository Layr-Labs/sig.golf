import SigGolfCandidate.ClaudeWCT_W9_New_G6_World
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafCore
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeCouplingShort
import SigGolfCandidate.ClaudeWCT_WCT9_Codebook
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeContactCase
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_FtsOverflow
import SigGolfCandidate.ClaudeWCT_WCT9_LowerReveal
import SigGolfCandidate.T3_Secc_LargeCouplingTable
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_LargeFamZeros

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
end Table
section Overflow
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem idx_zero_card (l : List ℕ) :
    ((Finset.range l.length).filter fun i => l.getD i 0 = 0).card = (l.filter (· = 0)).length := by
  induction l with
  | nil => simp
  | cons x t ih =>
      rw [Finset.card_filter, List.length_cons, Finset.sum_range_succ']
      rw [Finset.card_filter] at ih
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih]
      by_cases hx : x = 0
      · simp [List.filter_cons, hx]
      · simp [List.filter_cons, hx]
end Overflow
end ClaudeWCT.W9.T3.Security.LargeCoupling


namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord keygenDisclosed keygenCacheDisclosed lookupVal digestIndex LowerLeaf chainItem layerItems layerPath layerChains treeChild wctItem)
open ClaudeWCT.W9.T3.Security.LargeCoupling (keyValues idx_zero_card)
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
noncomputable local instance instDecidableEqCache_w9largeCouplingTable_initial : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Table
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
noncomputable def keyState (U : Finset HashInput) (q : Nat) (vals : Coord → Digest) (nv : Message → Digest) :
    LargeResidual.State WCoord (Cell U) :=
  discloseStates U q (Sum.elim vals nv) LargeResidual.initial keygenDisclosed
theorem rel_initial :
    Rel U T vals nv τ a q Monitor.initial LargeResidual.RouterState.initial (keyState U q vals nv) := by
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
      exact hck (LargeResidual.Paired.Known.base (Or.inl hd))
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
theorem canonical_split (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (T : Answers)
    (t : Tagged (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP))
    (ht : t ∈ support (taggedFixed T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
      (Wots.Ref.pureRecord T keygen (∅, ∅)).state)) :
    TaggedSplit adversary (Wots.PairedReference.Ref.combine T t.untag) (Wots.Ref.pureRecord T keygen (∅, ∅)) t
      (Wots.PairedReference.Ref.verdictRecord T t.untag) := by
  obtain ⟨hk, hka⟩ := keygen_record T
  have hval : (Wots.Ref.pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen :=
    Wots.Ref.pureRecord_value T keygen (∅, ∅)
  obtain ⟨ht1, ht2⟩ := taggedFixed_support T _ _ _ hka t ht
  refine ⟨hk, by rw [hval]; exact ht1, ?_, rfl⟩
  have hv := Wots.Ref.fixedRecord_mem_record T
    (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) t.state ht2
    (Wots.PairedReference.Ref.verdictRecord T t.untag)
    (by rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.PairedReference.Ref.verdict_hashOnly _ _), mem_support_pure_iff]; rfl)
  rw [hval]
  exact hv.1
noncomputable def verdictContact (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (value : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (state : LazyPrivate.State) : Prop :=
  ((Wots.Ref.pureRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = true
noncomputable def verdictCont (U : Finset HashInput) (a : AuxData) (q : Nat) (pk : Digest)
    (r : Option ((Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × RouterState)) :
    OracleComp (RWorld U) (Option (Bool × RouterState)) :=
  match r with
  | none => pure none
  | some (result, st) => routeVerdict U a q (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker pk result) st
theorem _root_.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.routerWith (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) :
    observedRun aux q (Sum.elim vals nv) τ (routerWith U adversary q a) LargeResidual.initial =
      observedRun aux q (Sum.elim vals nv) τ
        (routeInteraction U a (evalWithAnswerFn T keygen).2 q
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) LargeResidual.RouterState.initial >>=
            verdictCont U a q (evalWithAnswerFn T keygen).1) (keyState U q vals nv) := by
  unfold LargeResidual.Paired.routerWith
  rw [observed_discloseAll]
  have hkv : lookupVal (List.map (fun c => (c, Sum.elim vals nv (Sum.inl c))) keygenDisclosed) = keyValues vals :=
    rfl
  simp only [hkv]
  rw [hcoh.published, hcoh.pk]
  rfl
end Table

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord keygenDisclosed keygenCacheDisclosed lookupVal digestIndex LowerLeaf chainItem layerItems layerPath layerChains treeChild wctItem)
open ClaudeWCT.W9.T3.Security.LargeCoupling (keyValues idx_zero_card)
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
noncomputable local instance instDecidableEqCache_w9largeCouplingTable_families : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def LogNoOverflow (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Prop :=
  ∀j : Fin (2^31),((WPair.Paired.loggedOutputs T log).toFinset.filter fun out => ClaudeWCT.Bank.WCT.outIdx out=j).card≤50
section Overflow
/-- FTS seeds of family `f` opened by the signatures of a log (digit 4 words open the seed; T8: at most one per word). -/
@[irreducible] noncomputable def logSeeds (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (f : Fin (2 ^ 31) × Fin 9) :
    Finset CanonGraph.WctAddr :=
  Finset.univ.filter fun w => (w.1, w.2.1) = f ∧ ∃ N ∈ WPair.Paired.loggedOutputs T log, digestIndex N = w.1 ∧
    SigGolfCandidate.Research.SharedForest.rawChildFromOutput N w.2.1 = w.2.2.1 ∧ WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2 = 4
theorem mem_logSeeds (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (f : Fin (2 ^ 31) × Fin 9) (w : CanonGraph.WctAddr) :
    w ∈ logSeeds T log f ↔ (w.1, w.2.1) = f ∧ ∃ N ∈ WPair.Paired.loggedOutputs T log, digestIndex N = w.1 ∧
      SigGolfCandidate.Research.SharedForest.rawChildFromOutput N w.2.1 = w.2.2.1 ∧ WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2 = 4 := by
  unfold logSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
theorem digitThree_card (r : WCT9.Rank) : (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit r t = 4).card ≤ 1 :=
  WCT9.f8_seedDisclosures_card_le _
theorem logSeeds_card (T : Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (hno : LogNoOverflow T log)
    (f : Fin (2 ^ 31) × Fin 9) : (logSeeds T log f).card ≤ 50 := by
  set S := (WPair.Paired.loggedOutputs T log).toFinset.filter fun out => ClaudeWCT.Bank.WCT.outIdx out = f.1
  have hsub : logSeeds T log f ⊆ S.biUnion fun N =>
      (Finset.univ.filter fun t : Fin 6 => WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N f.2.val) t = 4).image
        fun t => ((f.1, f.2, SigGolfCandidate.Research.SharedForest.rawChildFromOutput N f.2, t) : CanonGraph.WctAddr) := by
    intro w hw
    obtain ⟨hf, N, hN, hidx, hch, hdig⟩ := (mem_logSeeds T log f w).mp hw
    have h1 : w.1 = f.1 := congrArg Prod.fst hf
    have h2 : w.2.1 = f.2 := congrArg Prod.snd hf
    refine Finset.mem_biUnion.mpr ⟨N, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hN, ?_⟩, ?_⟩
    · rw [← h1, ← hidx]; rfl
    · refine Finset.mem_image.mpr ⟨w.2.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← h2]; exact hdig⟩, ?_⟩
      rw [← h2, hch, ← h1]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc _ ≤ ∑ N ∈ S, 1 := Finset.sum_le_sum fun N _ => Finset.card_image_le.trans (digitThree_card _)
    _ = 1 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 1 * 50 := Nat.mul_le_mul_left _ (hno f.1)
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
/-- The seeds a sign step discloses are opened by the logged signature of that step. -/
theorem signDisclosed_logSeeds (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (published : SigGolfCandidate.T3.Cache)
    (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message)) (request : Security.Request)
    (w : CanonGraph.WctAddr) (hw : (.inr (.inr w) : Coord) ∈ signDisclosed T published request) :
    w ∈ logSeeds T [⟨request, evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)⟩] (w.1, w.2.1) := by
  unfold signDisclosed at hw
  split_ifs at hw with hc
  swap
  · cases hw
  cases hsd : LargeResidual.Paired.signDigest T request.message with
  | none => rw [hsd] at hw; cases hw
  | some cn =>
      obtain ⟨c, N⟩ := cn
      rw [hsd] at hw
      simp only at hw
      split_ifs at hw with hok
      swap
      · cases hw
      obtain ⟨h1, h2, h3⟩ := wctItem_mem_signItems T N w 0 (Nat.zero_le _) (by rw [wctItem_zero]; exact hw)
      have hdig : WCT9.wordDigit (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2 = 4 := by
        have := WCT9.wordDigit_le_four (SigGolfCandidate.Research.SharedForest.forestRank N w.2.1.val) w.2.2.2
        omega
      refine (mem_logSeeds T _ _ w).mpr ⟨rfl, N, ?_, h1.symm, h2.symm, hdig⟩
      rw [WPair.Paired.mem_loggedOutputs]
      refine ⟨_, List.mem_singleton_self _, assembleSig (nv request.message) N (ClaudeWCT.W9.T3.Security.LargeResidual.selVals vals) (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T)) (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T)), ?_, ?_⟩
      · change evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) = _
        rw [hsource request hc, hsd]
        unfold finishOut
        dsimp only
        rw [if_pos hok]
      · unfold WPair.Paired.signedOutput
        have hrho : (assembleSig (nv request.message) N (ClaudeWCT.W9.T3.Security.LargeResidual.selVals vals) (Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T)) (Wots.CanonicalRef.referenceLow T (Wots.CanonicalRef.sourceMessages T))).rho = nv request.message := rfl
        rw [hrho, ← hcoh.privateNonce]
        unfold LargeResidual.Paired.signDigest at hsd
        rw [hsd]
        rfl
/-- Router disclosures over a tagged run are covered by the seeds opened in its log. -/
theorem discSeeds_steps (hcoh : LargeResidual.Paired.Coherent U T vals nv τ a) (published : SigGolfCandidate.T3.Cache)
    (hsource : ∀request : Security.Request,request.cache=published →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message)) {α : Type}
    (program : OracleComp PairedOuter.LazyPrivate.Interaction α) :
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
            · exact LargeResidual.RouterState.next_disclosed U st X answer
          unfold DiscSeeds
          rw [hd]
        have := ih answer _ last hl (routerStep U T nv published st (.world ⟨state, .inl world, answer⟩)) f
        rw [hst] at this
        exact this
      · rw [taggedFixed_request, mem_support_bind_iff] at ht
        obtain ⟨block, hb, ht⟩ := ht
        rw [support_map] at ht
        obtain ⟨last, hl, rfl⟩ := ht
        rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.PairedReference.Ref.authenticatedSign_hashOnly _ _), mem_support_pure_iff] at hb
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
            have hls := signDisclosed_logSeeds hcoh published hsource request w h2
            have hv : block.value = evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign published request) := by
              rw [hb]; exact Wots.Ref.pureRecord_value _ _ _
            rw [← h.1]
            obtain ⟨hf', N, hN, hrest⟩ := (mem_logSeeds T _ _ w).mp hls
            refine (mem_logSeeds T _ _ w).mpr ⟨hf', N, ?_, hrest⟩
            rw [WPair.Paired.mem_loggedOutputs] at hN ⊢
            obtain ⟨entry, he, hrest'⟩ := hN
            rw [List.mem_singleton] at he
            refine ⟨entry, ?_, hrest'⟩
            rw [he, hv]
            exact List.mem_cons_self
        · apply Finset.mem_union_right
          obtain ⟨hf', N, hN, hrest⟩ := (mem_logSeeds T _ _ w).mp h
          refine (mem_logSeeds T _ _ w).mpr ⟨hf', N, ?_, hrest⟩
          rw [WPair.Paired.mem_loggedOutputs] at hN ⊢
          obtain ⟨entry, he, hrest'⟩ := hN
          exact ⟨entry, List.mem_cons_of_mem _ he, hrest'⟩
theorem discSeeds_initial (f : Fin (2 ^ 31) × Fin 9) : DiscSeeds LargeResidual.RouterState.initial f = ∅ := by
  ext w
  rw [mem_DiscSeeds]
  simp [LargeResidual.RouterState.initial]
/-- WOTS seeds of leaf `L` revealed by its reference digits (digit `0`). -/
@[irreducible] noncomputable def lowerZeros (T : Answers) (L : LowerLeaf) : Finset ChainGraph.Address :=
  Finset.univ.filter fun a => (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧
    a.leaf.val < 2 ^ height a.layer ∧ a.chain.val < chainCount a.layer ∧
    Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) (SigGolfCandidate.T3.Security.LargeCoupling.wotsAddr a) = 0
theorem mem_lowerZeros (T : Answers) (L : LowerLeaf) (a : ChainGraph.Address) :
    a ∈ lowerZeros T L ↔ (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1 ∧
      a.leaf.val < 2 ^ height a.layer ∧ a.chain.val < chainCount a.layer ∧
      Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) (SigGolfCandidate.T3.Security.LargeCoupling.wotsAddr a) = 0 := by
  unfold lowerZeros
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
/-- Per-leaf zero cap of the canonical reference digits (any answers, real leaves; v6: lower 5, top 9). -/
def LeafZeroCapRef (zcap : Layer → Nat) : Prop :=
  ∀ (T : Answers) (K : Wots.LeafAddr), K.leaf < 2 ^ height K.lay →
    (Finset.univ.filter fun c : Fin (chainCount K.lay) =>
      Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) ⟨K, c.val⟩ = 0).card ≤ zcap K.lay
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- **Per-family disclosure bound (layout-generic).** With a per-leaf zero cap and the family budget
`zcap · members + 3 ≤ famSize`, a family has at most `famSize − 3` revealed seeds. At the v6 flip this replaces the
today-only proof of `lowerZeros_card`. -/
theorem lowerZeros_card_of_caps {zcap : Layer → Nat} (hz : LeafZeroCapRef zcap)
    (hsize : ∀ lay f, zcap lay * CanonGraph.famMembersL lay f + 3 ≤ WCT9.famSize lay f) (T : Answers)
    (L : LowerLeaf) : (lowerZeros T L).card + 3 ≤ WCT9.famSize L.1.1 L.1.2.2.val := by
  obtain ⟨⟨lay, tree, f⟩, hL⟩ := L
  let Z : ChainGraph.Address → Prop := fun a => a.chain.val < chainCount a.layer ∧
    Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) (SigGolfCandidate.T3.Security.LargeCoupling.wotsAddr a) = 0
  have hleaf : ∀ (lay' : Layer) (tree' : Fin (2 ^ 31)) (n : Nat), n < 2 ^ height lay' →
      ∀ S : Finset ChainGraph.Address, (∀ a ∈ S, a.layer = lay' ∧ a.tree = tree' ∧ a.leaf.val = n ∧ Z a) →
        S.card ≤ zcap lay' := by
    intro lay' tree' n hn S hS
    have hpos : 0 < chainCount lay' := by fin_cases lay' <;> decide
    refine le_trans (Finset.card_le_card_of_injOn (t := Finset.univ.filter fun c : Fin (chainCount lay') =>
        Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) ⟨⟨lay', tree'.val, n⟩, c.val⟩ = 0)
      (fun a => (⟨a.chain.val % chainCount lay', Nat.mod_lt _ hpos⟩ : Fin (chainCount lay'))) ?_ ?_)
      (hz T ⟨lay', tree'.val, n⟩ hn)
    · intro a ha
      obtain ⟨hl, ht, hn', hc, hd⟩ := hS a (Finset.mem_coe.mp ha)
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      obtain ⟨al, atr, alf, ach⟩ := a
      simp only at hl ht hn' hc hd ⊢
      subst hl ht hn'
      rw [Nat.mod_eq_of_lt hc]
      exact hd
    · intro a ha b hb hab
      obtain ⟨hla, hta, hna, hca, -⟩ := hS a (Finset.mem_coe.mp ha)
      obtain ⟨hlb, htb, hnb, hcb, -⟩ := hS b (Finset.mem_coe.mp hb)
      rw [hla] at hca
      rw [hlb] at hcb
      have hv := congrArg Fin.val hab
      simp only at hv
      rw [Nat.mod_eq_of_lt hca, Nat.mod_eq_of_lt hcb] at hv
      exact ChainGraph.Address.ext (hla.trans hlb.symm) (hta.trans htb.symm)
        (Fin.ext (hna.trans hnb.symm)) (Fin.ext hv)
  exact le_trans (Nat.add_le_add_right (CanonGraph.famZeros_card_le Z zcap hleaf lay tree f _
    fun a ha => (mem_lowerZeros T ⟨(lay, tree, f), hL⟩ a).mp ha) 3) (hsize lay f.val)
/-- Canonical producer zero caps per leaf (`WCT9.producerZeroCap`): top 7 of 51 (T51; img-v6: 9 of 54), lower 5 of 43. -/
def leafZeroCap (lay : Layer) : Nat := if lay = 0 then 7 else 5
theorem leafZeroCapRef : LeafZeroCapRef leafZeroCap := by
  intro T K _
  set ds := Wots.CanonicalRef.referenceDigits T (Wots.CanonicalRef.sourceMessages T) K with hds
  have hlen : ds.length = chainCount K.lay := Wots.CanonicalRef.referenceDigits_length T (Wots.CanonicalRef.sourceMessages T) K
  have hzero : (ds.filter (· = 0)).length ≤ leafZeroCap K.lay := by
    dsimp only [ds]
    cases hs : Wots.CanonicalRef.referenceSearch T (Wots.CanonicalRef.sourceMessages T) K with
    | none =>
      simp only [Wots.CanonicalRef.referenceDigits,hs,Option.map_none,Option.getD_none,Wots.Leaf.dummyDigits_zero]
      exact Nat.zero_le _
    | some found =>
      obtain ⟨counter,digits,low⟩ := found
      have hd : ∃floor value,WCT9.CanonicalPolicy.producerDecodeAt K.lay floor low value=some digits := by
        obtain ⟨remaining, _, hs0⟩ := Option.bind_eq_some_iff.mp hs
        exact ⟨_,Wots.CanonicalRef.counterSearch_accepted T _ _ _ _ _ _ _ counter digits low hs0⟩
      simp only [Wots.CanonicalRef.referenceDigits,hs,Option.map_some,Option.getD_some]
      obtain ⟨floor,value,hd⟩ := hd
      have hp := WCT9.CanonicalPolicy.producerDecodeAt_spec hd
      by_cases hz : K.lay=0
      · have hb := hp.2.2.1
        simp only [WCT9.canonicalZeroBound, WCT9.producerZeroCap, hz, if_true] at hb
        unfold leafZeroCap; rw [if_pos hz]; omega
      · have hb := hp.2.2.1
        simp only [WCT9.canonicalZeroBound, WCT9.producerZeroCap, hz, if_false] at hb
        unfold leafZeroCap; rw [if_neg hz]; omega
  refine le_trans (Finset.card_le_card_of_injOn
    (t := (Finset.range ds.length).filter fun i => ds.getD i 0 = 0) (fun c => c.val) ?_ ?_) ?_
  · intro c hc
    have hc' := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [hlen]; exact c.isLt), ?_⟩)
    have : Wots.CanonicalRef.depth T (Wots.CanonicalRef.sourceMessages T) ⟨K, c.val⟩ = ds.getD c.val 0 := by
      unfold Wots.CanonicalRef.depth; rfl
    rw [← this]; exact hc'.2
  · intro a _ b _ hab; exact Fin.ext hab
  · rw [idx_zero_card]; exact hzero
theorem leafZeroCap_size (lay : Layer) (f : Nat) :
    leafZeroCap lay * CanonGraph.famMembersL lay f + 3 ≤ WCT9.famSize lay f := by
  unfold leafZeroCap CanonGraph.famMembersL WCT9.famSize WCT9.famGrp
  split_ifs with h
  · have := min_le_left 4 (2 ^ height lay - 4 * f)
    simp only [SigGolfCandidate.T3.topCoefCount]; omega
  · exact le_rfl

/-- At most `famSize − 3` revealed seeds per family (v6 lower: `5 r + 3` coefficients for `r` real members). -/
theorem lowerZeros_card (T : Answers) (L : LowerLeaf) : (lowerZeros T L).card + 3 ≤ WCT9.famSize L.1.1 L.1.2.2.val :=
  lowerZeros_card_of_caps leafZeroCapRef leafZeroCap_size T L
theorem layerItems_seed_lt (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2 ^ 31)) (a : ChainGraph.Address)
    (h : (.inr (.inl a) : Coord) ∈ layerItems digitsOf index) :
    a.chain.val < chainCount a.layer ∧ a.leaf.val < 2 ^ height a.layer := by
  unfold layerItems at h
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at h
  obtain ⟨lay, hc | hc⟩ := h
  · unfold layerChains at hc
    split_ifs at hc with hb
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, hi'⟩ := hc
      obtain ⟨h1, -⟩ := chainItem_seed hi'
      subst h1
      have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
      refine ⟨?_, ?_⟩
      · change (CanonGraph.fin58 i).val < chainCount lay
        rw [show (CanonGraph.fin58 i).val = i from Nat.mod_eq_of_lt hi58]
        exact hi
      · change (route index.val lay).1 < 2 ^ height lay
        simp only [route]
        exact Nat.mod_lt _ (by positivity)
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc with hb
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      exact absurd rfl ((treeChild_not_chain hj).2 a)
    · cases hc
theorem signDisclosed_lowerZeros (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (L : LowerLeaf) (a : ChainGraph.Address) (hL : (a.layer, a.tree, CanonGraph.famSlot a.layer a.leaf) = L.1)
    (h : (.inr (.inl a) : Coord) ∈ signDisclosed A published request) : a ∈ lowerZeros A L := by
  have hd := (signDisclosed_chain A published request _ h).2 a rfl
  have hlt : a.chain.val < chainCount a.layer ∧ a.leaf.val < 2 ^ height a.layer := by
    unfold signDisclosed at h
    split_ifs at h with hcache
    · split at h
      · split_ifs at h with hok
        · unfold LargeResidual.Paired.signItems at h
          rcases List.mem_append.mp h with h | h
          · exact absurd rfl ((ftsItems_not_chain _ _ _ h).2 a)
          · exact layerItems_seed_lt _ _ a h
        · cases h
      · cases h
    · cases h
  exact (mem_lowerZeros A L a).mpr ⟨hL, hlt.2, hlt.1, hd⟩
theorem discLower_initial (L : LowerLeaf) : DiscLower LargeResidual.RouterState.initial L = ∅ := by
  ext w
  rw [mem_DiscLower]
  simp [LargeResidual.RouterState.initial]
theorem discLower_steps (U : Finset HashInput) (T : Answers) (nv : Message → Digest)
    (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) :
    ∀ (st : RouterState) (L : LowerLeaf),
      DiscLower (steps.foldl (routerStep U T nv published) st) L ⊆ DiscLower st L ∪ lowerZeros T L := by
  induction steps with
  | nil => intro st L; exact Finset.subset_union_left
  | cons s rest ih =>
      intro st L w hw
      rw [List.foldl_cons] at hw
      rcases Finset.mem_union.mp (ih _ L hw) with h | h
      · obtain ⟨hL, hd⟩ := (mem_DiscLower _ L w).mp h
        cases s with
        | world e =>
            have he : (routerStep U T nv published st (.world e)).disclosed = st.disclosed := by
              change (routerEvent U st e).disclosed = st.disclosed
              rcases e with ⟨before, (n | X) | c, y⟩
              · rfl
              · exact LargeResidual.RouterState.next_disclosed U st X y
              · rfl
            rw [he] at hd
            exact Finset.mem_union_left _ ((mem_DiscLower st L w).mpr ⟨hL, hd⟩)
        | sign request out events =>
            change (.inr (.inl w) : Coord) ∈ (signedState T nv published st request).disclosed at hd
            rw [signedState_disclosed, List.mem_append] at hd
            rcases hd with hd | hd
            · exact Finset.mem_union_left _ ((mem_DiscLower st L w).mpr ⟨hL, hd⟩)
            · exact Finset.mem_union_right _ (signDisclosed_lowerZeros T published request L w hL hd)
      · exact Finset.mem_union_right _ h
end Overflow

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open ClaudeWCT.W9.T3.Security.LargeResidual (Coord WCoord keygenDisclosed keygenCacheDisclosed lookupVal digestIndex LowerLeaf chainItem layerItems layerPath layerChains treeChild wctItem)
open ClaudeWCT.W9.T3.Security.LargeCoupling (keyValues idx_zero_card)
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
noncomputable local instance instDecidableEqCache_w9largeCouplingTable_contact : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
/-- No index carries more than 50 distinct signed outputs in the log of any game split. -/
def NoOvR (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ g i c, Wots.PairedReference.GameSplit adversary rec g i c → LogNoOverflow A i.value.2
theorem table_contact_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.PairedReference.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : LargeResidual.Paired.Coherent (Wots.PairedReference.referenceInputs adversary) T vals nv τ a)
    (hsource : ∀request : Security.Request,request.cache=(evalWithAnswerFn T keygen).2 →
      evalWithAnswerFn T (PairedOuter.FullGame.authenticatedSign (evalWithAnswerFn T keygen).2 request)=
        finishOut T vals (nv request.message) (LargeResidual.Paired.signDigest T request.message)) :
    Pr[fun rec => ContactR adversary q rec T ∧ NoOvR adversary rec T |
        Wots.Ref.fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.PairedReference.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.PairedReference.referenceInputs adversary := Wots.PairedReference.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  rw [hcoh.routerWith, Wots.PairedReference.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.PairedReference.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 hsource
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictContact (Wots.PairedReference.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon
      value state ∧ FamOK st)
    (verdictCont (Wots.PairedReference.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) (fun r => r.1 = none ∧ r.2.counters.calls ≤ q)
    ?_ ?_ ?_ (fun _ _ _ _ h => h.2) Monitor.initial LargeResidual.RouterState.initial (keyState (Wots.PairedReference.referenceInputs adversary) q vals nv) _
      rel_initial (fun _ _ h => by cases h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    have h := hc.1 _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h
    refine ⟨h, fun f => ?_, fun L => ?_⟩
    · have hno : LogNoOverflow T t.value.2 := hc.2 _ _ _ hsplit.untag
      have hsub := discSeeds_steps hcoh (evalWithAnswerFn T keygen).2 hsource _ _ t ht LargeResidual.RouterState.initial f
      rw [discSeeds_initial, Finset.empty_union] at hsub
      exact (Finset.card_le_card hsub).trans ((logSeeds_card T _ hno f).trans (by norm_num))
    · have hsub := discLower_steps (Wots.PairedReference.referenceInputs adversary) T nv (evalWithAnswerFn T keygen).2 t.steps
        LargeResidual.RouterState.initial L
      rw [discLower_initial, Finset.empty_union] at hsub
      have := lowerZeros_card T L
      exact (Finset.card_le_card hsub).trans (by omega)
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PairedOuter.PaddedGame.verdict_public _ _) mon st ws state hrel hf.2
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.PairedReference.referenceInputs adversary) a q (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
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
    have h := events_over (Wots.PairedReference.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    unfold verdictContact at hf
    rw [h.1] at hf
    cases hf
  · intro ws' hws
    exact ⟨rfl, hws⟩

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
