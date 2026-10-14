import SigGolfCandidate.T3.Secc.PairGuessLazyFree

section

section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Table
end Table
section Inline
noncomputable local instance instDecidableEqCache_pairGuessLazyCouple : DecidableEq T3.Cache := Classical.decEq _
end Inline
section Run
open SecretGuessObservation (fixedRun fixedImpl runWith)
def Consistent (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ x a, mem.rows x = some a → a = rowVal D x) ∧ ∀ m v, mem.nonces m = some v → v = Nn m
theorem consistent_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Consistent D Nn LazyMem.empty :=
  by
  refine ⟨fun x a h => ?_, fun m v h => ?_⟩
  · simp [LazyMem.empty] at h
  · simp [LazyMem.empty] at h
theorem rowStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', Consistent D Nn mem' ∧ rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') := by
  have hreplay : Consistent D Nn (mem.replayRow x isBirth) := by
    unfold LazyMem.replayRow
    split
    · exact hm
    · exact hm
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
      change pure (a, mem.replayRow x isBirth) = _
      rw [hm.1 x a h]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ⟨?_, hm.2⟩, ?_⟩
        · intro y a hy
          change mem.rows.cacheQuery x (rowVal D x) y = some a at hy
          by_cases hyx : y = x
          · subst hyx
            rw [QueryCache.cacheQuery_self] at hy
            exact (Option.some.inj hy).symm
          · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
            exact hm.1 y a hy
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
      · refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (m : Message) :
    ∃ mem', Consistent D Nn mem' ∧ nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, hm, ?_⟩
      change pure (v, mem) = _
      rw [hm.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), ⟨hm.1, ?_⟩, map_pure _ _⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.2 m' v hv
end Run
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Ghost
open SecretGuessObservation (fixedRun fixedImpl runWith)
theorem runL_bind_nonzero {β γ : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (first : OracleComp WSpecL β) (next : β → OracleComp WSpecL γ) (s : WStateL)
    (r : γ × WStateL) (hr : fixedRun E fts (first >>= next) s r ≠ 0) :
    ∃ mid, fixedRun E fts first s mid ≠ 0 ∧ fixedRun E fts (next mid.1) mid.2 r ≠ 0 := by
  unfold fixedRun runWith at hr ⊢
  rw [simulateQ_bind, StateT.run_bind, RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runL_pure_nonzero {β : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (v : β) (s : WStateL) (r : β × WStateL) (hr : fixedRun E fts (pure v) s r ≠ 0) :
    r = (v, s) := by
  unfold fixedRun at hr
  rw [SecretGuessObservation.runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
structure Grows (m m' : LazyMem) : Prop where
  rows : ∀ x a, m.rows x = some a → m'.rows x = some a
  births : ∀ a ∈ m.births, a ∈ m'.births
  trials : ∀ x ∈ m.trials, x ∈ m'.trials
  exposures : ∀ o ∈ m.exposures, o ∈ m'.exposures
theorem Grows.refl (m : LazyMem) : Grows m m := ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
theorem Grows.trans {m1 m2 m3 : LazyMem} (h1 : Grows m1 m2) (h2 : Grows m2 m3) : Grows m1 m3 :=
  ⟨fun x a h => h2.rows x a (h1.rows x a h), fun a h => h2.births a (h1.births a h),
    fun x h => h2.trials x (h1.trials x h), fun o h => h2.exposures o (h1.exposures o h)⟩
def Good (D : digestInputs → HashOutput) (Nn : Message → Digest) (m : LazyMem) : Prop :=
  Consistent D Nn m ∧ ∀ x a, m.rows x = some a → a ∈ m.births ∨ x ∈ m.trials
theorem good_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Good D Nn LazyMem.empty :=
  ⟨consistent_empty D Nn, fun x a h => by simp [LazyMem.empty] at h⟩
theorem replayRow_true (mem : LazyMem) (x : HashInput) : mem.replayRow x true = mem := by
  simp [LazyMem.replayRow]
theorem replayRow_false (mem : LazyMem) (x : HashInput) :
    mem.replayRow x false = { mem with trials := mem.trials ++ [x] } := by
  simp [LazyMem.replayRow]
theorem readRow_true (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a true = { mem with rows := mem.rows.cacheQuery x a, births := mem.births ++ [a] } := by
  simp [LazyMem.readRow]
theorem readRow_false (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a false = { mem with rows := mem.rows.cacheQuery x a, trials := mem.trials ++ [x] } := by
  simp [LazyMem.readRow]
theorem cacheQuery_good (D : digestInputs → HashOutput) (mem : LazyMem) (x : HashInput) (y : HashInput) (b : HashOutput)
    (hy : mem.rows.cacheQuery x (rowVal D x) y = some b) :
    b = rowVal D x ∧ y = x ∨ mem.rows y = some b := by
  by_cases hyx : y = x
  · subst hyx
    rw [QueryCache.cacheQuery_self] at hy
    exact Or.inl ⟨(Option.some.inj hy).symm, rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
    exact Or.inr hy
theorem rowStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') ∧ Good D Nn mem' ∧
      Grows mem mem' ∧ (x ∈ digestInputs → mem'.rows x = some (rowVal D x)) := by
  have hreplay : Good D Nn (mem.replayRow x isBirth) ∧ Grows mem (mem.replayRow x isBirth) := by
    cases isBirth
    · rw [replayRow_false]
      refine ⟨⟨hm.1, fun y a hy => ?_⟩, ⟨fun _ _ h => h, fun _ h => h, fun y h => List.mem_append_left _ h,
        fun _ h => h⟩⟩
      rcases hm.2 y a hy with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · rw [replayRow_true]
      exact ⟨hm, Grows.refl mem⟩
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      have ha := hm.1.1 x a h
      refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun _ => ?_⟩
      · change pure (a, mem.replayRow x isBirth) = _
        rw [ha]
      · rw [hreplay.2.rows x a h, ha]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ?_, ?_, ?_, fun _ => ?_⟩
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
        · cases isBirth
          · rw [readRow_false]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl h
                · exact Or.inr (List.mem_append_left _ h)
          · rw [readRow_true]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl (List.mem_append_left _ h)
                · exact Or.inr h
        · have hrows : ∀ y b, mem.rows y = some b → mem.rows.cacheQuery x (rowVal D x) y = some b := by
            intro y b hy
            have hyx : y ≠ x := by
              rintro rfl
              rw [h] at hy
              cases hy
            rw [QueryCache.cacheQuery_of_ne _ _ hyx]
            exact hy
          cases isBirth
          · rw [readRow_false]
            exact ⟨hrows, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h⟩
          · rw [readRow_true]
            exact ⟨hrows, fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h⟩
        · cases isBirth
          · rw [readRow_false]
            exact QueryCache.cacheQuery_self _ _ _
          · rw [readRow_true]
            exact QueryCache.cacheQuery_self _ _ _
      · refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun h' => absurd h' hx⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (m : Message) :
    ∃ mem', nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') ∧ Good D Nn mem' ∧ Grows mem mem' := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, ?_, hm, Grows.refl mem⟩
      change pure (v, mem) = _
      rw [hm.1.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), map_pure _ _, ⟨⟨hm.1.1, ?_⟩, hm.2⟩,
        ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.1.2 m' v hv
theorem expose_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (o : Option HashOutput) : Good D Nn (mem.expose o) ∧ Grows mem (mem.expose o) :=
  ⟨hm, ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h⟩⟩
end Ghost
end SigGolfCandidate.T3.Security.BPair
end
end

section

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Uniform
theorem evalSPMF_uniform {X : Type} [Fintype X] [Nonempty X] (I : SampleableType X) :
    𝒮[(@uniformSample X I : ProbComp X)] = (liftM (PMF.uniformOfFintype X) : SPMF X) := by
  apply SPMF.ext
  intro x
  rw [SPMF.liftM_apply, PMF.uniformOfFintype_apply, ← SPMF.probOutput_eq_apply, probOutput_evalSPMF]
  exact @probOutput_uniformSample X I _ x
theorem uniform_update {ι β γ : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β] (i : ι)
    (g : β → (ι → β) → SPMF γ) (hg : ∀ a T c, g a (Function.update T i c) = g a T) :
    ((liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g (T i) T) =
      ((liftM (PMF.uniformOfFintype β) : SPMF β) >>= fun a =>
        (liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g a T) := by
  let IT : SampleableType (ι → β) := SampleableType.ofFintype _
  let Ia : SampleableType β := SampleableType.ofFintype _
  let IP : SampleableType ((ι → β) × β) := SampleableType.ofFintype _
  let f : (ι → β) × β → (ι → β) × β := fun p => (Function.update p.1 i p.2, p.1 i)
  have hinv : ∀ p, f (f p) = p := by
    rintro ⟨T, a⟩
    simp only [f, Function.update_self, Function.update_idem, Function.update_eq_self]
  have hf : Function.Bijective f := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨f p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((ι → β) × β) IP ((ι → β) × β) IP _ f hf
  have hp := @FullGame.uniform_product (ι → β) β _ _ IT Ia IP
  rw [← evalSPMF_uniform IT, ← evalSPMF_uniform Ia]
  calc (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T => g (T i) T)
      = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun _ => g (T i) T) := by
        simp only [evalSPMF_uniform Ia, RetainedObservation.lift_bind_const]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g (p.1 i) p.1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hp]
    _ = (𝒮[f <$> (@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 (Function.update p.1 i p.2)) := by
        rw [evalSPMF_map, bind_map_left]
        simp only [f, Function.update_self]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 p.1) := by simp only [hg]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g p.2 p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun a => g a T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := RetainedObservation.bind_comm _ _ _
noncomputable def patch {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) : β :=
  @dite _ (∃ s, e s = a) (Classical.propDecidable _) (fun h => D (Classical.choose h)) (fun _ => T a)
theorem patch_e {α σ β : Type} {e : σ → α} (he : Function.Injective e) (T : α → β) (D : σ → β) (s : σ) :
    patch e T D (e s) = D s := by
  have h : ∃ s', e s' = e s := ⟨s, rfl⟩
  rw [patch, dif_pos h]
  exact congrArg D (he (Classical.choose_spec h))
theorem patch_of {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) (ha : ∀ s, e s ≠ a) :
    patch e T D a = T a := by
  rw [patch, dif_neg (fun h => ha _ (Classical.choose_spec h))]
theorem patch_uniform {α σ β γ : Type} [Fintype α] [Fintype σ] [Fintype β] [Nonempty β] [DecidableEq α]
    [DecidableEq σ] {e : σ → α} (he : Function.Injective e) (IT : SampleableType (α → β))
    (ID : SampleableType (σ → β)) (k : (α → β) → SPMF γ) :
    (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T => 𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>=
      fun D => k (patch e T D)) = 𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= k := by
  let IP : SampleableType ((α → β) × (σ → β)) := SampleableType.ofFintype _
  let Φ : (α → β) × (σ → β) → (α → β) × (σ → β) := fun p => (patch e p.1 p.2, p.1 ∘ e)
  have hinv : ∀ p, Φ (Φ p) = p := by
    rintro ⟨T, D⟩
    refine Prod.ext (funext fun a => ?_) (funext fun s => ?_)
    · change patch e (patch e T D) (T ∘ e) a = T a
      by_cases h : ∃ s, e s = a
      · obtain ⟨s, rfl⟩ := h
        rw [patch_e he]
        rfl
      · have h' : ∀ s, e s ≠ a := fun s hs => h ⟨s, hs⟩
        rw [patch_of e _ _ a h', patch_of e _ _ a h']
    · exact patch_e he T D s
  have hΦ : Function.Bijective Φ := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨Φ p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((α → β) × (σ → β)) IP ((α → β) × (σ → β)) IP _ Φ hΦ
  have hp := @FullGame.uniform_product (α → β) (σ → β) _ _ IT ID IP
  calc _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k (Φ p).1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
        rfl
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k (Φ p).1) := by rw [hp]
    _ = (𝒮[Φ <$> (@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by
        rw [evalSPMF_map, bind_map_left]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T =>
          𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>= fun _ => k T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := by simp only [evalSPMF_uniform ID, RetainedObservation.lift_bind_const]
end Uniform
noncomputable instance instSampleableDigestRows : SampleableType (digestInputs → HashOutput) :=
  SampleableType.ofFintype _
noncomputable instance instSampleableNonceTables : SampleableType (Message → Digest) := SampleableType.ofFintype _
section OmegaPatch
variable {U : Finset HashInput} (hsub : digestInputs ⊆ U)
def digestEmb : digestInputs → U := fun x => ⟨x.1, hsub x.2⟩
theorem digestEmb_injective : Function.Injective (digestEmb hsub) :=
  fun x y h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h')
end OmegaPatch
section Steps
open SecretGuessObservation (forcedRun forcedImpl lazyImpl runWith afterTrial afterDisclosure forcedTrial)
variable (slot : Nat)
theorem rowStep_some (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (a : HashOutput)
    (h : mem.rows x = some a) : rowStep mem x b src = pure (a, mem.replayRow x b) := by
  unfold rowStep
  rw [h]
theorem rowStep_out (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∉ digestInputs) : rowStep mem x b src = pure (0, mem.replayRow x b) := by
  unfold rowStep
  rw [h, if_neg hx]
theorem rowStep_in (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∈ digestInputs) : rowStep mem x b src = (fun a => (a, mem.readRow x a b)) <$> src := by
  unfold rowStep
  rw [h, if_pos hx]
theorem nonceStep_some (mem : LazyMem) (m : Message) (src : PMF Digest) (v : Digest) (h : mem.nonces m = some v) :
    nonceStep mem m src = pure (v, mem) := by
  unfold nonceStep
  rw [h]
theorem nonceStep_none (mem : LazyMem) (m : Message) (src : PMF Digest) (h : mem.nonces m = none) :
    nonceStep mem m src = (fun v => (v, mem.drawNonce m v)) <$> src := by
  unfold nonceStep
  rw [h]
variable (rs : HashInput → PMF HashOutput) (ns : Message → PMF Digest)
end Steps
section Congr
open SecretGuessObservation (forcedRun forcedImpl runWith)
def Agree (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ y : digestInputs, mem.rows y.1 = none → D y = D' y) ∧ ∀ m, mem.nonces m = none → Nn m = Nn' m
theorem rowVal_agree {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (hx : mem.rows x = none) : rowVal D x = rowVal D' x := by
  unfold rowVal
  by_cases hd : x ∈ digestInputs
  · rw [dif_pos hd, dif_pos hd]
    exact h.1 ⟨x, hd⟩ hx
  · rw [dif_neg hd, dif_neg hd]
theorem agree_replay {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (b : Bool) : Agree D D' Nn Nn' (mem.replayRow x b) := by
  cases b
  · rw [replayRow_false]
    exact h
  · rw [replayRow_true]
    exact h
theorem agree_read {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (a : HashOutput) (b : Bool) :
    Agree D D' Nn Nn' (mem.readRow x a b) := by
  have hrows : ∀ y : digestInputs, (mem.rows.cacheQuery x a) y.1 = none → D y = D' y := by
    intro y hy
    by_cases hyx : y.1 = x
    · rw [hyx, QueryCache.cacheQuery_self] at hy
      cases hy
    · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
      exact h.1 y hy
  cases b
  · rw [readRow_false]
    exact ⟨hrows, h.2⟩
  · rw [readRow_true]
    exact ⟨hrows, h.2⟩
theorem agree_draw {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (m : Message) (v : Digest) : Agree D D' Nn Nn' (mem.drawNonce m v) := by
  refine ⟨h.1, fun m' hm' => ?_⟩
  change Function.update mem.nonces m (some v) m' = none at hm'
  by_cases hmm : m' = m
  · rw [hmm, Function.update_self] at hm'
    cases hm'
  · rw [Function.update_of_ne hmm] at hm'
    exact h.2 m' hm'
end Congr
section EagerLazy
open SecretGuessObservation (forcedRun forcedImpl runWith)
noncomputable def rowsLaw : SPMF (digestInputs → HashOutput) := liftM (PMF.uniformOfFintype (digestInputs → HashOutput))
noncomputable def noncesLaw : SPMF (Message → Digest) := liftM (PMF.uniformOfFintype (Message → Digest))
end EagerLazy
end SigGolfCandidate.T3.Security.BPair
end
