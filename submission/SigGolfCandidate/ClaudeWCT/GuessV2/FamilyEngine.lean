import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessBy
import SigGolfCandidate.ClaudeWCT.GuessV2.WCTCoords
import SigGolfCandidate.ClaudeWCT.Arith.Family

/-!
# The FTS seed-family world (campaign X1, stage A)

Hidden values of the case-C world: one coefficient vector `K f : Fin 54 → Digest` per FTS family
`f = (index, coord)` and the step-1..3 labels `g12`. The world's table `GCoord → Digest` is `phi K g12`: the seed
`(a, 0)` is `familyEval (K (famOf a)) (ptOf a)`, the steps are `g12`. The lazy engine keeps today's `State` (its
`allowed` sets record every trial and disclosure); the posterior of family `f` is `famPostA allowed f`, the vectors
whose seeds lie in the allowed sets, and the step labels stay a product table (`labelAllowed`).

* `sampler`: trial and disclosure laws (`trialBy` / `discloseBy` on the two tables).
* `fam_posterior`, `fam_erasure`: the eager world (`hiddenLaw`, then `fixedRun` on `phi K g12`) is the lazy run.
* `Inv`, `Bad`, `hazard`: per-family posteriors are `famPost` with at most 53 known points while at most 51
  seeds per family are retired without a guess (`¬Bad`) and at most one guess was made; then a trial at a fresh seed
  hits with probability at most `(2^128 - budget)⁻¹` (A1's `fam_hazard_prob`), labels as today.
-/

namespace ClaudeWCT.Guess.Fam
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (Digest)
open SphincsSecurity.Concrete SphincsSecurity.Concrete.SecretGuessObservation SphincsSecurity.Concrete.UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

abbrev FamIdx := Fin (2 ^ 31) × Fin 9
abbrev Coefs := Fin 54 → Digest
abbrev LabelIdx := ChainAddr × Fin 3
/-- The family of chain `a`. -/
def famOf (a : ChainAddr) : FamIdx := (a.1, a.2.1)
/-- The evaluation point of chain `a` in its family. -/
def ptOf (a : ChainAddr) : Nat := WCT9.ftsPoint a.2.2.1.val a.2.2.2.val
/-- Member `(j, t)` of family `f`. -/
def member (f : FamIdx) (j : Fin 128) (t : Fin 6) : ChainAddr := (f.1, f.2, j, t)
/-- The seed of chain `a` under coefficient vector `K`. -/
def seedK (K : Coefs) (a : ChainAddr) : Digest := ClaudeWCT.Arith.familyEval (List.ofFn K) (ptOf a)
theorem famOf_member (f : FamIdx) (j : Fin 128) (t : Fin 6) : famOf (member f j t) = f := rfl
theorem member_famOf (a : ChainAddr) : member (famOf a) a.2.2.1 a.2.2.2 = a := rfl
theorem ptOf_member (f : FamIdx) (j : Fin 128) (t : Fin 6) : ptOf (member f j t) = WCT9.ftsPoint j.val t.val := rfl
theorem ftsPoint_lt (j : Fin 128) (t : Fin 6) : WCT9.ftsPoint j.val t.val < 1024 := by
  unfold WCT9.ftsPoint WCT9.ftsOrdinal; omega
theorem ftsPoint_inj {j j' : Fin 128} {t t' : Fin 6} (h : WCT9.ftsPoint j.val t.val = WCT9.ftsPoint j'.val t'.val) :
    j = j' ∧ t = t' := by
  unfold WCT9.ftsPoint WCT9.ftsOrdinal at h
  have := t.isLt; have := t'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
/-- Posterior of family `f`: coefficient vectors whose seeds all lie in the allowed sets. -/
noncomputable def famPostA (allowed : GCoord → Finset Digest) (f : FamIdx) : Finset Coefs :=
  Finset.univ.filter fun K => ∀ j t, seedK K (member f j t) ∈ allowed (member f j t, 0)
theorem mem_famPostA (allowed : GCoord → Finset Digest) (f : FamIdx) (K : Coefs) :
    K ∈ famPostA allowed f ↔ ∀ j t, seedK K (member f j t) ∈ allowed (member f j t, 0) := by
  simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
/-- The step-label table (`(a, q)` is the label at step `q + 1`). -/
def labelAllowed (allowed : GCoord → Finset Digest) (l : LabelIdx) : Finset Digest := allowed (l.1, l.2.succ)
/-- The world's table from the hidden coefficients and labels. -/
def phi (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (c : GCoord) : Digest :=
  if h : c.2 = 0 then seedK (K (famOf c.1)) c.1 else g12 (c.1, c.2.pred h)
theorem phi_seed (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (a : ChainAddr) :
    phi K g12 (a, 0) = seedK (K (famOf a)) a := rfl
theorem phi_label (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (l : LabelIdx) :
    phi K g12 (l.1, l.2.succ) = g12 l := by
  unfold phi
  rw [dif_neg (Fin.succ_ne_zero _)]
  simp
/-- The eager hidden law given the allowed sets. -/
noncomputable def hiddenLaw (allowed : GCoord → Finset Digest) : SPMF (GCoord → Digest) :=
  complete (famPostA allowed) >>= fun K => complete (labelAllowed allowed) >>= fun g12 => pure (phi K g12)
/-- Trial and disclosure laws of the family world. -/
noncomputable def sampler (Memory : Type) : Sampler GCoord Digest Memory where
  trialLaw state c v :=
    if h : c.2 = 0 then trialBy (famPostA state.allowed) (famOf c.1) (fun K => decide (seedK K c.1 = v))
    else trialBy (labelAllowed state.allowed) (c.1, c.2.pred h) (fun x => decide (x = v))
  discloseLaw state c :=
    if h : c.2 = 0 then discloseBy (famPostA state.allowed) (famOf c.1) (fun K => seedK K c.1)
    else discloseBy (labelAllowed state.allowed) (c.1, c.2.pred h) id

/-! ### Restriction lemmas -/

theorem member_ne_of_famOf {f : FamIdx} {a : ChainAddr} (h : famOf a ≠ f) (j : Fin 128) (t : Fin 6) :
    member f j t ≠ a := fun he => h (he ▸ famOf_member f j t)
theorem label_ne_seed (l : LabelIdx) (a : ChainAddr) : ((l.1, l.2.succ) : GCoord) ≠ (a, 0) :=
  fun he => Fin.succ_ne_zero _ (Prod.mk.inj he).2
theorem labelIdx_eq_of_ne {c : GCoord} (hc : c.2 ≠ 0) {l : LabelIdx} (hl : l ≠ (c.1, c.2.pred hc)) :
    ((l.1, l.2.succ) : GCoord) ≠ c := by
  intro he
  apply hl
  have h1 : l.1 = c.1 := congrArg Prod.fst he
  have h2 : l.2.succ = c.2 := congrArg Prod.snd he
  refine Prod.ext h1 ?_
  rw [← Fin.succ_inj, Fin.succ_pred]
  exact h2
theorem label_succ_pred {c : GCoord} (hc : c.2 ≠ 0) : ((c.1, (c.2.pred hc).succ) : GCoord) = c := by
  rw [Fin.succ_pred]
theorem seed_ne_of_famOf {f : FamIdx} {a : ChainAddr} (h : f ≠ famOf a) (j : Fin 128) (t : Fin 6) :
    ((member f j t, 0) : GCoord) ≠ (a, 0) := fun he =>
  member_ne_of_famOf (Ne.symm h) j t (Prod.mk.inj he).1
theorem seed_ne_label (f : FamIdx) (j : Fin 128) (t : Fin 6) {c : GCoord} (hc : c.2 ≠ 0) :
    ((member f j t, 0) : GCoord) ≠ c := fun he => hc ((congrArg Prod.snd he).symm)
theorem famPostA_restrict_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (v : Digest) (hit : Bool) :
    famPostA (restrict allowed (a, 0) v hit) =
      restrictBy (famPostA allowed) (famOf a) (fun K => decide (seedK K a = v)) hit := by
  funext f
  by_cases hf : f = famOf a
  · subst hf
    ext K
    rw [mem_restrictBy_self]
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨fun j t => ?_, ?_⟩
      · have hj := h j t
        by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
        · rw [he, restrict, Function.update_self, Finset.mem_filter] at hj
          rw [he]; exact hj.1
        · rwa [restrict, Function.update_of_ne he] at hj
      · have hj := h a.2.2.1 a.2.2.2
        rw [member_famOf, restrict, Function.update_self, Finset.mem_filter] at hj
        exact hj.2
    · rintro ⟨h, hh⟩ j t
      by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
      · have hm : member (famOf a) j t = a := (Prod.mk.inj he).1
        rw [he, restrict, Function.update_self, Finset.mem_filter]
        have h1 := h j t
        rw [hm] at h1 ⊢
        exact ⟨h1, hh⟩
      · rw [restrict, Function.update_of_ne he]; exact h j t
  · rw [restrictBy_other _ _ _ _ hf]
    ext K
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun j => forall_congr' fun t => ?_
    rw [restrict, Function.update_of_ne (seed_ne_of_famOf hf j t)]
theorem labelAllowed_restrict_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (v : Digest) (hit : Bool) :
    labelAllowed (restrict allowed (a, 0) v hit) = labelAllowed allowed := by
  funext l
  simp only [labelAllowed, restrict, Function.update_of_ne (label_ne_seed l a)]
theorem famPostA_restrict_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (v : Digest)
    (hit : Bool) : famPostA (restrict allowed c v hit) = famPostA allowed := by
  funext f
  ext K
  simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall_congr' fun j => forall_congr' fun t => ?_
  rw [restrict, Function.update_of_ne (seed_ne_label f j t hc)]
theorem labelAllowed_restrict_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (v : Digest)
    (hit : Bool) : labelAllowed (restrict allowed c v hit) =
      restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) hit := by
  funext l
  by_cases hl : l = (c.1, c.2.pred hc)
  · subst hl
    ext x
    rw [mem_restrictBy_self]
    simp only [labelAllowed, label_succ_pred hc, restrict, Function.update_self, Finset.mem_filter]
  · rw [restrictBy_other _ _ _ _ hl]
    simp only [labelAllowed, restrict, Function.update_of_ne (labelIdx_eq_of_ne hc hl)]
theorem famPostA_disclose_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (value : Digest)
    (hv : value ∈ allowed (a, 0)) :
    famPostA (discloseTableValue allowed (a, 0) value) =
      restrictBy (famPostA allowed) (famOf a) (fun K => seedK K a) value := by
  funext f
  by_cases hf : f = famOf a
  · subst hf
    ext K
    rw [mem_restrictBy_self]
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have ha := h a.2.2.1 a.2.2.2
      rw [member_famOf, discloseTableValue, Function.update_self, Finset.mem_singleton] at ha
      refine ⟨fun j t => ?_, ha.symm⟩
      have hj := h j t
      by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
      · have hm : member (famOf a) j t = a := (Prod.mk.inj he).1
        rw [hm, ha]; exact hv
      · rwa [discloseTableValue, Function.update_of_ne he] at hj
    · rintro ⟨h, hh⟩ j t
      by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
      · have hm : member (famOf a) j t = a := (Prod.mk.inj he).1
        rw [he, discloseTableValue, Function.update_self, Finset.mem_singleton, hm, hh]
      · rw [discloseTableValue, Function.update_of_ne he]; exact h j t
  · rw [restrictBy_other _ _ _ _ hf]
    ext K
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun j => forall_congr' fun t => ?_
    rw [discloseTableValue, Function.update_of_ne (seed_ne_of_famOf hf j t)]
theorem labelAllowed_disclose_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (value : Digest) :
    labelAllowed (discloseTableValue allowed (a, 0) value) = labelAllowed allowed := by
  funext l
  simp only [labelAllowed, discloseTableValue, Function.update_of_ne (label_ne_seed l a)]
theorem famPostA_disclose_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (value : Digest) :
    famPostA (discloseTableValue allowed c value) = famPostA allowed := by
  funext f
  ext K
  simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall_congr' fun j => forall_congr' fun t => ?_
  rw [discloseTableValue, Function.update_of_ne (seed_ne_label f j t hc)]
theorem labelAllowed_disclose_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (value : Digest)
    (hv : value ∈ allowed c) :
    labelAllowed (discloseTableValue allowed c value) =
      restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) id value := by
  funext l
  by_cases hl : l = (c.1, c.2.pred hc)
  · subst hl
    ext x
    rw [mem_restrictBy_self]
    simp only [labelAllowed, label_succ_pred hc, discloseTableValue, Function.update_self, Finset.mem_singleton, id]
    constructor
    · rintro rfl; exact ⟨hv, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  · rw [restrictBy_other _ _ _ _ hl]
    simp only [labelAllowed, discloseTableValue, Function.update_of_ne (labelIdx_eq_of_ne hc hl)]
/-- A disclosed seed with positive mass lies in the allowed set. -/
theorem mem_of_discloseBy_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (value : Digest)
    (h : discloseBy (famPostA allowed) (famOf a) (fun K => seedK K a) value ≠ 0) : value ∈ allowed (a, 0) := by
  obtain ⟨K, hK⟩ := discloseBy_nonempty _ _ _ _ h (famOf a)
  simp only [mem_restrictBy_self, mem_famPostA] at hK
  obtain ⟨hK1, hK2⟩ := hK
  have hm := hK1 a.2.2.1 a.2.2.2
  rw [hK2]
  exact hm
theorem mem_of_discloseBy_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (value : Digest)
    (h : discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id value ≠ 0) : value ∈ allowed c := by
  obtain ⟨x, hx⟩ := discloseBy_nonempty _ _ _ _ h (c.1, c.2.pred hc)
  rw [mem_restrictBy_self] at hx
  have hm := hx.1
  simp only [labelAllowed, label_succ_pred hc] at hm
  rw [hx.2]
  exact hm

/-! ### Conditioning the hidden law -/

theorem hiddenLaw_bind_seed {Result : Type} (allowed : GCoord → Finset Digest) (a : ChainAddr) (v : Digest)
    (next : Bool → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (decide (g (a, 0) = v)) g) =
      (trialBy (famPostA allowed) (famOf a) (fun K => decide (seedK K a = v)) >>= fun hit =>
        hiddenLaw (restrict allowed (a, 0) v hit) >>= next hit) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind]
  simp only [famPostA_restrict_seed, labelAllowed_restrict_seed]
  exact bind_trialBy (famPostA allowed) (famOf a) (fun K => decide (seedK K a = v))
    (fun hit K => complete (labelAllowed allowed) >>= fun g12 => next hit (phi K g12))
theorem phi_label' (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (c : GCoord) (hc : c.2 ≠ 0) :
    phi K g12 c = g12 (c.1, c.2.pred hc) := by
  unfold phi
  rw [dif_neg hc]
theorem hiddenLaw_bind_label {Result : Type} (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0)
    (v : Digest) (next : Bool → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (decide (g c = v)) g) =
      (trialBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) >>= fun hit =>
        hiddenLaw (restrict allowed c v hit) >>= next hit) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind]
  simp only [famPostA_restrict_label allowed c hc, labelAllowed_restrict_label allowed c hc]
  calc (complete (famPostA allowed) >>= fun K => complete (labelAllowed allowed) >>= fun g12 =>
          next (decide (phi K g12 c = v)) (phi K g12))
      = (complete (famPostA allowed) >>= fun K =>
          trialBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) >>= fun hit =>
            complete (restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) hit) >>=
              fun g12 => next hit (phi K g12)) := by
        refine bind_congr fun K => ?_
        simp only [phi_label' _ _ c hc]
        exact bind_trialBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v))
          (fun hit g12 => next hit (phi K g12))
    _ = _ := RetainedObservation.bind_comm _ _ _
theorem hiddenLaw_bind_disclose_seed {Result : Type} (allowed : GCoord → Finset Digest) (a : ChainAddr)
    (next : Digest → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (g (a, 0)) g) =
      (discloseBy (famPostA allowed) (famOf a) (fun K => seedK K a) >>= fun value =>
        hiddenLaw (discloseTableValue allowed (a, 0) value) >>= next value) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind, phi_seed]
  refine (bind_discloseBy (famPostA allowed) (famOf a) (fun K => seedK K a)
    (fun value K => complete (labelAllowed allowed) >>= fun g12 => next value (phi K g12))).trans ?_
  refine RetainedObservation.bind_congr _ _ _ fun value hv => ?_
  rw [famPostA_disclose_seed allowed a value (mem_of_discloseBy_seed allowed a value hv),
    labelAllowed_disclose_seed]
theorem hiddenLaw_bind_disclose_label {Result : Type} (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0)
    (next : Digest → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (g c) g) =
      (discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id >>= fun value =>
        hiddenLaw (discloseTableValue allowed c value) >>= next value) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind]
  calc (complete (famPostA allowed) >>= fun K => complete (labelAllowed allowed) >>= fun g12 =>
          next (phi K g12 c) (phi K g12))
      = (complete (famPostA allowed) >>= fun K =>
          discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id >>= fun value =>
            complete (restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) id value) >>=
              fun g12 => next value (phi K g12)) := by
        refine bind_congr fun K => ?_
        simp only [phi_label' _ _ c hc]
        exact bind_discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id (fun value g12 => next value (phi K g12))
    _ = (discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id >>= fun value =>
          complete (famPostA allowed) >>= fun K =>
            complete (restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) id value) >>=
              fun g12 => next value (phi K g12)) := RetainedObservation.bind_comm _ _ _
    _ = _ := by
        refine RetainedObservation.bind_congr _ _ _ fun value hv => ?_
        rw [famPostA_disclose_label allowed c hc,
          labelAllowed_disclose_label allowed c hc value (mem_of_discloseBy_label allowed c hc value hv)]

/-! ### The family world is the lazy run -/

section Erasure
variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
theorem fam_posterior {Result : Type} (environment : Environment auxSpec GCoord Digest Memory)
    (computation : OracleComp (World auxSpec GCoord Digest) Result) (state : State GCoord Digest Memory) :
    (hiddenLaw state.allowed >>= fun g => (fun result => (g, result)) <$> fixedRun environment g computation state) =
      (withRun environment (sampler Memory) computation state >>= fun result =>
        (fun g => (g, result)) <$> hiddenLaw result.2.allowed) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [fixedRun, withRun, runWith_pure, pure_bind, ← bind_pure_comp]
  | query_bind input next ih =>
      rcases input with input | (⟨c, v⟩ | c)
      · simp only [fixedRun, withRun, runWith_query_bind, fixedImpl, withImpl, lazyImpl,
          StateT.run_mk, bind_map_left, map_bind, bind_assoc]
        rw [RetainedObservation.bind_comm]
        exact congrArg ((liftM (environment.auxiliary state input) : SPMF _) >>= ·)
          (funext fun answer => ih answer.1 { state with memory := answer.2 })
      · simp only [fixedRun, withRun, runWith_query_bind, fixedImpl, withImpl, StateT.run_mk, pure_bind,
          bind_map_left, bind_assoc]
        obtain ⟨a, q⟩ := c
        by_cases hq : q = 0
        · subst hq
          rw [hiddenLaw_bind_seed state.allowed a v (fun hit g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next hit)
              (afterTrial environment state (a, 0) v hit))]
          simp only [sampler, dif_pos rfl]
          exact congrArg (trialBy (famPostA state.allowed) (famOf a) (fun K => decide (seedK K a = v)) >>= ·)
            (funext fun hit => ih hit (afterTrial environment state (a, 0) v hit))
        · rw [hiddenLaw_bind_label state.allowed (a, q) hq v (fun hit g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next hit)
              (afterTrial environment state (a, q) v hit))]
          simp only [sampler, dif_neg hq]
          exact congrArg (trialBy (labelAllowed state.allowed) (a, q.pred hq) (fun x => decide (x = v)) >>= ·)
            (funext fun hit => ih hit (afterTrial environment state (a, q) v hit))
      · simp only [fixedRun, withRun, runWith_query_bind, fixedImpl, withImpl, StateT.run_mk, pure_bind,
          bind_map_left, bind_assoc]
        obtain ⟨a, q⟩ := c
        by_cases hq : q = 0
        · subst hq
          rw [hiddenLaw_bind_disclose_seed state.allowed a (fun value g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next value)
              (afterDisclosure environment state (a, 0) value))]
          simp only [sampler, dif_pos rfl]
          exact congrArg (discloseBy (famPostA state.allowed) (famOf a) (fun K => seedK K a) >>= ·)
            (funext fun value => ih value (afterDisclosure environment state (a, 0) value))
        · rw [hiddenLaw_bind_disclose_label state.allowed (a, q) hq (fun value g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next value)
              (afterDisclosure environment state (a, q) value))]
          simp only [sampler, dif_neg hq]
          exact congrArg (discloseBy (labelAllowed state.allowed) (a, q.pred hq) id >>= ·)
            (funext fun value => ih value (afterDisclosure environment state (a, q) value))
end Erasure

/-! ### Marginal laws -/

theorem restrictionWeight_update {C V : Type} [Fintype C] [DecidableEq C] [DecidableEq V]
    (allowed : C → Finset V) (c : C) (S : Finset V) (ha : ∀ c', (allowed c').Nonempty) :
    restrictionWeight allowed (Function.update allowed c S) = (S.card : ℝ≥0∞) / (allowed c).card := by
  unfold restrictionWeight
  have h1 : (∏ x, (Function.update allowed c S x).card) = S.card * ∏ x ∈ Finset.univ.erase c, (allowed x).card := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  have h2 : (∏ x, (allowed x).card) = (allowed c).card * ∏ x ∈ Finset.univ.erase c, (allowed x).card :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ c)).symm
  have hP : (∏ x ∈ Finset.univ.erase c, (allowed x).card) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => (Finset.card_pos.mpr (ha x)).ne'
  rw [h1, h2, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right _ _ (by exact_mod_cast hP) (ENNReal.natCast_ne_top _)
theorem trialBy_true_eq {C V : Type} [Fintype C] [DecidableEq C] [DecidableEq V] (allowed : C → Finset V) (c : C)
    (test : V → Bool) (ha : ∀ c', (allowed c').Nonempty) :
    trialBy allowed c test true = (((allowed c).filter fun x => true = test x).card : ℝ≥0∞) / (allowed c).card := by
  rw [discloseBy_apply, restrictBy, restrictionWeight_update _ _ _ ha]
  congr

/-! ### Invariant, overflow flag, hazard -/

section Hazard
variable {Memory : Type}
/-- Seeds of family `f` that are retired (disclosed or hit). -/
noncomputable def retiredSeeds (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Fin 128 × Fin 6) :=
  Finset.univ.filter fun p => ((member f p.1 p.2, 0) : GCoord) ∈ state.retired
/-- Seeds of family `f` retired without a guess (disclosed by honest signing). -/
noncomputable def freeRetired (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Fin 128 × Fin 6) :=
  (retiredSeeds state f).filter fun p => ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses
theorem mem_retiredSeeds (state : State GCoord Digest Memory) (f : FamIdx) (p : Fin 128 × Fin 6) :
    p ∈ retiredSeeds state f ↔ ((member f p.1 p.2, 0) : GCoord) ∈ state.retired := by
  simp [retiredSeeds]
theorem mem_freeRetired (state : State GCoord Digest Memory) (f : FamIdx) (p : Fin 128 × Fin 6) :
    p ∈ freeRetired state f ↔
      ((member f p.1 p.2, 0) : GCoord) ∈ state.retired ∧ ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses := by
  simp [freeRetired, retiredSeeds]
/-- FTS overflow in the engine: some family has more than 51 seeds retired without a guess. -/
def Bad (state : State GCoord Digest Memory) : Prop := ∃ f, 51 < (freeRetired state f).card
/-- Values excluded from the fresh seeds of family `f` (one per failed guess). -/
noncomputable def missCount (state : State GCoord Digest Memory) (f : FamIdx) : Nat :=
  ∑ p : Fin 128 × Fin 6, if ((member f p.1 p.2, 0) : GCoord) ∈ state.retired then 0
    else 2 ^ 128 - (state.allowed (member f p.1 p.2, 0)).card
/-- Invariant of the family engine. -/
structure Inv (state : State GCoord Digest Memory) : Prop where
  guesses : state.guesses ⊆ state.retired
  fam : ∀ f, (famPostA state.allowed f).Nonempty
  label : ∀ l, (labelAllowed state.allowed l).Nonempty
  labelSize : ∀ l : LabelIdx, ((l.1, l.2.succ) : GCoord) ∉ state.retired →
    2 ^ 128 ≤ (labelAllowed state.allowed l).card + state.probes
  retiredSeed : ∀ a : ChainAddr, ((a, 0) : GCoord) ∈ state.retired → (state.allowed (a, 0)).card ≤ 1
  misses : ∀ f, missCount state f ≤ state.probes
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp
theorem famPostA_univ (f : FamIdx) : famPostA (fun _ => Finset.univ) f = Finset.univ := by
  ext K
  simp [famPostA]
theorem inv_initial (memory : Memory) : Inv (initialState memory : State GCoord Digest Memory) := by
  refine ⟨by simp [initialState], fun f => ?_, fun l => ⟨0, by simp [labelAllowed, initialState]⟩, ?_, ?_, ?_⟩
  · rw [show (initialState memory : State GCoord Digest Memory).allowed = fun _ => Finset.univ from rfl,
      famPostA_univ]
    exact Finset.univ_nonempty
  · intro l _
    simp [labelAllowed, initialState, card_digest]
  · intro a ha
    simp [initialState] at ha
  · intro f
    simp [missCount, initialState, card_digest]
/-- Known pairs `(point, seed)` of family `f`: the retired seeds with their (at most one) allowed value. -/
noncomputable def knownOf (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Nat × Digest) :=
  (retiredSeeds state f).biUnion fun p =>
    (state.allowed (member f p.1 p.2, 0)).image fun v => (WCT9.ftsPoint p.1.val p.2.val, v)
/-- Excluded pairs of family `f`: fresh seeds and the values they can no longer take. -/
noncomputable def missesOf (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Nat × Digest) :=
  (Finset.univ.filter fun p : Fin 128 × Fin 6 => ((member f p.1 p.2, 0) : GCoord) ∉ state.retired).biUnion fun p =>
    (Finset.univ \ state.allowed (member f p.1 p.2, 0)).image fun v => (WCT9.ftsPoint p.1.val p.2.val, v)
theorem seedK_member (K : Coefs) (f : FamIdx) (j : Fin 128) (t : Fin 6) :
    seedK K (member f j t) = ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.ftsPoint j.val t.val) := rfl
set_option linter.constructorNameAsVariable false in
theorem famPostA_eq (state : State GCoord Digest Memory) (hs : Inv state) (f : FamIdx) :
    famPostA state.allowed f = ClaudeWCT.Arith.famPost (m := 53) (knownOf state f) (missesOf state f) := by
  ext K
  rw [mem_famPostA]
  simp only [ClaudeWCT.Arith.famPost, ClaudeWCT.Arith.famAffine, Finset.mem_filter, Finset.mem_univ, true_and,
    knownOf, missesOf, retiredSeeds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff,
    forall_exists_index, and_imp]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨j, t⟩ hp v hv rfl
      have hk := h j t
      exact Finset.card_le_one.mp (hs.retiredSeed _ hp) _ hk _ hv
    · rintro _ ⟨j, t⟩ hp v hv rfl heq
      have heq' : seedK K (member f j t) = v := heq
      exact hv (heq' ▸ h j t)
  · rintro ⟨hknown, hmiss⟩ j t
    by_cases hr : ((member f j t, 0) : GCoord) ∈ state.retired
    · obtain ⟨K0, hK0⟩ := hs.fam f
      simp only [mem_famPostA] at hK0
      have hv := hK0 j t
      have he := hknown (WCT9.ftsPoint j.val t.val, seedK K0 (member f j t)) (j, t) hr _ hv rfl
      rw [← seedK_member] at he
      rw [he]
      exact hv
    · by_contra hn
      exact hmiss (WCT9.ftsPoint j.val t.val, seedK K (member f j t)) (j, t) hr (seedK K (member f j t)) hn rfl
        (seedK_member K f j t).symm
theorem knownOf_card_le (state : State GCoord Digest Memory) (hs : Inv state) (f : FamIdx) :
    (knownOf state f).card ≤ (retiredSeeds state f).card := by
  unfold knownOf
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro p hp
  refine Finset.card_image_le.trans ?_
  exact hs.retiredSeed _ (Finset.mem_filter.mp hp).2
theorem retiredSeeds_card_le (state : State GCoord Digest Memory) (f : FamIdx) :
    (retiredSeeds state f).card ≤ (freeRetired state f).card + state.guesses.card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := retiredSeeds state f)
    (fun p => ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses)
  have hg : ((retiredSeeds state f).filter fun p => ¬((member f p.1 p.2, 0) : GCoord) ∉ state.guesses).card ≤
      state.guesses.card := by
    refine Finset.card_le_card_of_injOn (fun p => ((member f p.1 p.2, 0) : GCoord)) ?_ ?_
    · intro p hp
      simpa using (Finset.mem_filter.mp hp).2
    · rintro ⟨j, t⟩ _ ⟨j', t'⟩ _ he
      simp only [member, Prod.mk.injEq] at he
      obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := he
      rfl
  have hf : freeRetired state f = (retiredSeeds state f).filter fun p =>
      ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses := rfl
  rw [hf]
  omega
theorem missesOf_card_le (state : State GCoord Digest Memory) (hs : Inv state) (f : FamIdx) :
    (missesOf state f).card ≤ state.probes := by
  have h : (missesOf state f).card ≤ missCount state f := by
    unfold missesOf missCount
    refine Finset.card_biUnion_le.trans ?_
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hr : ((member f p.1 p.2, 0) : GCoord) ∈ state.retired
    · simp only [hr, not_true_eq_false, if_false, if_true, le_refl]
    · simp only [hr, not_false_eq_true, if_true, if_false]
      refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_digest]
  exact h.trans (hs.misses f)
theorem notMem_known (state : State GCoord Digest Memory) (a : ChainAddr) (ha : ((a, 0) : GCoord) ∉ state.retired) :
    ptOf a ∉ (knownOf state (famOf a)).image Prod.fst := by
  intro hmem
  obtain ⟨⟨pt, w⟩, hpw, hfst⟩ := Finset.mem_image.mp hmem
  simp only [knownOf, Finset.mem_biUnion, Finset.mem_image] at hpw
  obtain ⟨⟨j, t⟩, hr, w', -, he⟩ := hpw
  simp only [Prod.mk.injEq] at he
  have hp : WCT9.ftsPoint j.val t.val = WCT9.ftsPoint a.2.2.1.val a.2.2.2.val := by
    rw [he.1]; exact hfst
  obtain ⟨rfl, rfl⟩ := ftsPoint_inj hp
  exact ha ((mem_retiredSeeds _ _ _).mp hr)
/-- Hazard of a fresh seed: at most `(2^128 - budget)⁻¹` while `¬Bad`, with at most one guess. -/
theorem hazard_seed (state : State GCoord Digest Memory) (hs : Inv state) (hbad : ¬Bad state)
    (hg : state.guesses.card ≤ 1) (budget : Nat) (hp : state.probes < budget) (a : ChainAddr)
    (ha : ((a, 0) : GCoord) ∉ state.retired) (v : Digest) :
    trialBy (famPostA state.allowed) (famOf a) (fun K => decide (seedK K a = v)) true ≤
      ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ := by
  rw [trialBy_true_eq _ _ _ hs.fam]
  have hfree : (freeRetired state (famOf a)).card ≤ 51 := by
    by_contra h
    exact hbad ⟨famOf a, by omega⟩
  have hknown : (knownOf state (famOf a)).card ≤ 53 :=
    (knownOf_card_le state hs _).trans ((retiredSeeds_card_le state _).trans (by omega))
  have hpts : ∀ p ∈ knownOf state (famOf a), p.1 < 1024 := by
    intro p hp
    simp only [knownOf, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨⟨j, t⟩, -, v, -, rfl⟩ := hp
    exact ftsPoint_lt j t
  have hmpts : ∀ p ∈ missesOf state (famOf a), p.1 < 1024 := by
    intro p hp
    simp only [missesOf, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨⟨j, t⟩, -, v, -, rfl⟩ := hp
    exact ftsPoint_lt j t
  have hb : ptOf a < 1024 := ftsPoint_lt a.2.2.1 a.2.2.2
  have h := ClaudeWCT.Arith.fam_hazard_prob (m := 53) hknown hpts hmpts hb (notMem_known state a ha) v
    ((missesOf_card_le state hs _).trans hp.le)
  rw [← famPostA_eq state hs] at h
  have hf : ((famPostA state.allowed (famOf a)).filter fun K => true = decide (seedK K a = v)) =
      (famPostA state.allowed (famOf a)).filter fun K => ClaudeWCT.Arith.familyEval (List.ofFn K) (ptOf a) = v := by
    apply Finset.filter_congr
    intro K _
    simp [seedK]
  rw [hf]
  exact h
theorem hazard_label (state : State GCoord Digest Memory) (hs : Inv state) (budget : Nat) (hp : state.probes < budget)
    (c : GCoord) (hc : c.2 ≠ 0) (hr : c ∉ state.retired) (v : Digest) :
    trialBy (labelAllowed state.allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) true ≤
      ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ := by
  rw [trialBy_true_eq _ _ _ hs.label]
  have hsize := hs.labelSize (c.1, c.2.pred hc) (by rwa [label_succ_pred hc])
  have hcard : ((labelAllowed state.allowed (c.1, c.2.pred hc)).filter fun x => true = decide (x = v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [Finset.mem_filter, eq_comm (a := true), decide_eq_true_eq] at hx hy
    rw [hx.2, hy.2]
  calc (((labelAllowed state.allowed (c.1, c.2.pred hc)).filter fun x => true = decide (x = v)).card : ℝ≥0∞) /
        (labelAllowed state.allowed (c.1, c.2.pred hc)).card
      ≤ 1 / ((labelAllowed state.allowed (c.1, c.2.pred hc)).card : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ ≤ ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ := by
        rw [one_div]
        apply ENNReal.inv_le_inv.mpr
        exact_mod_cast (show 2 ^ 128 - budget ≤ (labelAllowed state.allowed (c.1, c.2.pred hc)).card by omega)
end Hazard

/-! ### Preservation -/

section Preservation
variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
variable (environment : Environment auxSpec GCoord Digest Memory)
theorem card_restrict_ge (allowed : GCoord → Finset Digest) (c : GCoord) (v : Digest) (hit : Bool) (x : GCoord)
    (h : hit = true → x ≠ c) : (allowed x).card ≤ (restrict allowed c v hit x).card + 1 := by
  cases hit with
  | false => exact restrict_false_card allowed c v x
  | true => rw [restrict, Function.update_of_ne (h rfl)]; omega
theorem trial_seed_mass {state : State GCoord Digest Memory} {a : ChainAddr} {v : Digest} {hit : Bool}
    (h : (sampler Memory).trialLaw state (a, 0) v hit ≠ 0) :
    trialBy (famPostA state.allowed) (famOf a) (fun K => decide (seedK K a = v)) hit ≠ 0 := by
  simpa only [sampler, dite_true] using h
theorem trial_label_mass {state : State GCoord Digest Memory} {c : GCoord} (hc : c.2 ≠ 0) {v : Digest} {hit : Bool}
    (h : (sampler Memory).trialLaw state c v hit ≠ 0) :
    trialBy (labelAllowed state.allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) hit ≠ 0 := by
  simpa only [sampler, dif_neg hc] using h
theorem disclose_seed_mass {state : State GCoord Digest Memory} {a : ChainAddr} {value : Digest}
    (h : (sampler Memory).discloseLaw state (a, 0) value ≠ 0) :
    discloseBy (famPostA state.allowed) (famOf a) (fun K => seedK K a) value ≠ 0 := by
  simpa only [sampler, dite_true] using h
theorem disclose_label_mass {state : State GCoord Digest Memory} {c : GCoord} (hc : c.2 ≠ 0) {value : Digest}
    (h : (sampler Memory).discloseLaw state c value ≠ 0) :
    discloseBy (labelAllowed state.allowed) (c.1, c.2.pred hc) id value ≠ 0 := by
  simpa only [sampler, dif_neg hc] using h
theorem indicator_sum_le_one (f : FamIdx) (c : GCoord) :
    (∑ p : Fin 128 × Fin 6, if ((member f p.1 p.2, 0) : GCoord) = c then 1 else 0) ≤ 1 := by
  rw [← Finset.card_filter]
  apply Finset.card_le_one.mpr
  rintro ⟨j, t⟩ hp ⟨j', t'⟩ hp'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  rw [← hp'] at hp
  simp only [member, Prod.mk.injEq] at hp
  obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := hp
  rfl
theorem inv_afterTrial (state : State GCoord Digest Memory) (hs : Inv state) (c : GCoord) (v : Digest) (hit : Bool)
    (hmass : (sampler Memory).trialLaw state c v hit ≠ 0) : Inv (afterTrial environment state c v hit) := by
  obtain ⟨a, q⟩ := c
  have hret : state.retired ⊆ (afterTrial environment state (a, q) v hit).retired := by
    simp only [afterTrial]; split
    · exact Finset.subset_insert _ _
    · exact le_rfl
  have hhitret : hit = true → ((a, q) : GCoord) ∈ (afterTrial environment state (a, q) v hit).retired := by
    rintro rfl; simp [afterTrial]
  refine ⟨afterTrial_guesses_sub environment state hs.guesses _ v hit, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    change (famPostA (restrict state.allowed (a, q) v hit) f).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [famPostA_restrict_seed]
      exact discloseBy_nonempty _ _ _ _ (trial_seed_mass hmass) f
    · rw [famPostA_restrict_label _ (a, q) hq]
      exact hs.fam f
  · intro l
    change (labelAllowed (restrict state.allowed (a, q) v hit) l).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [labelAllowed_restrict_seed]
      exact hs.label l
    · rw [labelAllowed_restrict_label _ (a, q) hq]
      exact discloseBy_nonempty _ _ _ _ (trial_label_mass hq hmass) l
  · intro l hl
    have hold := hs.labelSize l (fun h => hl (hret h))
    have hge := card_restrict_ge state.allowed (a, q) v hit (l.1, l.2.succ)
      (fun hh he => hl (he ▸ hhitret hh))
    change 2 ^ 128 ≤ (restrict state.allowed (a, q) v hit (l.1, l.2.succ)).card + (state.probes + 1)
    simp only [labelAllowed] at hold
    omega
  · intro a' ha'
    change (restrict state.allowed (a, q) v hit (a', 0)).card ≤ 1
    by_cases hold : ((a', 0) : GCoord) ∈ state.retired
    · exact (Finset.card_le_card (restrict_subset state.allowed (a, q) v hit (a', 0))).trans (hs.retiredSeed a' hold)
    · have hhit : hit = true ∧ ((a', 0) : GCoord) = (a, q) := by
        simp only [afterTrial] at ha'
        split at ha'
        · rename_i hh
          rcases Finset.mem_insert.mp ha' with h | h
          · exact ⟨hh, h⟩
          · exact absurd h hold
        · exact absurd ha' hold
      obtain ⟨rfl, he⟩ := hhit
      rw [he, restrict, Function.update_self]
      apply Finset.card_le_one.mpr
      intro x hx y hy
      simp only [Finset.mem_filter, eq_comm (a := true), decide_eq_true_eq] at hx hy
      rw [hx.2, hy.2]
  · intro f
    change missCount (afterTrial environment state (a, q) v hit) f ≤ state.probes + 1
    have hstep : ∀ p : Fin 128 × Fin 6,
        (if ((member f p.1 p.2, 0) : GCoord) ∈ (afterTrial environment state (a, q) v hit).retired then 0
          else 2 ^ 128 - ((afterTrial environment state (a, q) v hit).allowed (member f p.1 p.2, 0)).card) ≤
        (if ((member f p.1 p.2, 0) : GCoord) ∈ state.retired then 0
          else 2 ^ 128 - (state.allowed (member f p.1 p.2, 0)).card) +
          (if ((member f p.1 p.2, 0) : GCoord) = (a, q) then 1 else 0) := by
      intro p
      split
      · exact Nat.zero_le _
      · rename_i hn
        have hn' : ((member f p.1 p.2, 0) : GCoord) ∉ state.retired := fun h => hn (hret h)
        rw [if_neg hn']
        change 2 ^ 128 - (restrict state.allowed (a, q) v hit (member f p.1 p.2, 0)).card ≤ _
        by_cases he : ((member f p.1 p.2, 0) : GCoord) = (a, q)
        · rw [if_pos he]
          have hge := card_restrict_ge state.allowed (a, q) v hit (member f p.1 p.2, 0)
            (fun hh he' => hn (he' ▸ hhitret hh))
          omega
        · rw [if_neg he, restrict, Function.update_of_ne he]
          omega
    unfold missCount
    refine (Finset.sum_le_sum fun p _ => hstep p).trans ?_
    rw [Finset.sum_add_distrib]
    have := hs.misses f
    have := indicator_sum_le_one f (a, q)
    unfold missCount at *
    omega
theorem inv_afterDisclosure (state : State GCoord Digest Memory) (hs : Inv state) (c : GCoord) (value : Digest)
    (hmass : (sampler Memory).discloseLaw state c value ≠ 0) : Inv (afterDisclosure environment state c value) := by
  obtain ⟨a, q⟩ := c
  have hvmem : value ∈ state.allowed (a, q) := by
    by_cases hq : q = 0
    · subst hq; exact mem_of_discloseBy_seed _ _ _ (disclose_seed_mass hmass)
    · exact mem_of_discloseBy_label _ (a, q) hq _ (disclose_label_mass hq hmass)
  refine ⟨hs.guesses.trans (Finset.subset_insert _ _), ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    change (famPostA (discloseTableValue state.allowed (a, q) value) f).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [famPostA_disclose_seed _ _ _ hvmem]
      exact discloseBy_nonempty _ _ _ _ (disclose_seed_mass hmass) f
    · rw [famPostA_disclose_label _ (a, q) hq]
      exact hs.fam f
  · intro l
    change (labelAllowed (discloseTableValue state.allowed (a, q) value) l).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [labelAllowed_disclose_seed]
      exact hs.label l
    · rw [labelAllowed_disclose_label _ (a, q) hq _ hvmem]
      exact discloseBy_nonempty _ _ _ _ (disclose_label_mass hq hmass) l
  · intro l hl
    have hne : ((l.1, l.2.succ) : GCoord) ≠ (a, q) := fun he => hl (by rw [he]; simp [afterDisclosure])
    have hold := hs.labelSize l (fun h => hl (Finset.mem_insert_of_mem h))
    change 2 ^ 128 ≤ (discloseTableValue state.allowed (a, q) value (l.1, l.2.succ)).card + state.probes
    rw [discloseTableValue, Function.update_of_ne hne]
    exact hold
  · intro a' ha'
    change (discloseTableValue state.allowed (a, q) value (a', 0)).card ≤ 1
    by_cases he : ((a', 0) : GCoord) = (a, q)
    · rw [he, discloseTableValue, Function.update_self, Finset.card_singleton]
    · rw [discloseTableValue, Function.update_of_ne he]
      exact hs.retiredSeed a' ((Finset.mem_insert.mp ha').resolve_left he)
  · intro f
    change missCount (afterDisclosure environment state (a, q) value) f ≤ state.probes
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hs.misses f)
    split
    · exact Nat.zero_le _
    · rename_i hn
      have hne : ((member f p.1 p.2, 0) : GCoord) ≠ (a, q) := fun he => hn (by rw [he]; simp [afterDisclosure])
      have hn' : ((member f p.1 p.2, 0) : GCoord) ∉ state.retired := fun h => hn (Finset.mem_insert_of_mem h)
      rw [if_neg hn']
      change 2 ^ 128 - (discloseTableValue state.allowed (a, q) value (member f p.1 p.2, 0)).card ≤ _
      rw [discloseTableValue, Function.update_of_ne hne]
theorem inv_step (state : State GCoord Digest Memory) (hs : Inv state)
    (input : (World auxSpec GCoord Digest).Domain)
    (result : (World auxSpec GCoord Digest).Range input × State GCoord Digest Memory)
    (hr : (withImpl environment (sampler Memory) input).run state result ≠ 0) : Inv result.2 := by
  rcases withImpl_cases environment (sampler Memory) state input result hr with ⟨memory, h⟩ |
    ⟨c, v, hit, -, hm, h⟩ | ⟨c, value, -, hm, h⟩
  · rw [h]; exact ⟨hs.guesses, hs.fam, hs.label, hs.labelSize, hs.retiredSeed, hs.misses⟩
  · rw [h]; exact inv_afterTrial environment state hs c v hit hm
  · rw [h]; exact inv_afterDisclosure environment state hs c value hm
theorem freeRetired_mono {state state' : State GCoord Digest Memory} (f : FamIdx)
    (hr : state.retired ⊆ state'.retired)
    (hg : ∀ x, x ∈ state'.guesses → x ∈ state.retired → x ∈ state.guesses) :
    freeRetired state f ⊆ freeRetired state' f := by
  intro p hp
  rw [mem_freeRetired] at hp ⊢
  exact ⟨hr hp.1, fun h => hp.2 (hg _ h hp.1)⟩
theorem bad_step (state : State GCoord Digest Memory) (hbad : Bad state)
    (input : (World auxSpec GCoord Digest).Domain)
    (result : (World auxSpec GCoord Digest).Range input × State GCoord Digest Memory)
    (hr : (withImpl environment (sampler Memory) input).run state result ≠ 0) : Bad result.2 := by
  obtain ⟨f, hf⟩ := hbad
  refine ⟨f, lt_of_lt_of_le hf (Finset.card_le_card ?_)⟩
  rcases withImpl_cases environment (sampler Memory) state input result hr with ⟨memory, h⟩ |
    ⟨c, v, hit, -, -, h⟩ | ⟨c, value, -, -, h⟩
  · rw [h]; exact freeRetired_mono f le_rfl fun _ h _ => h
  · rw [h]
    refine freeRetired_mono f ?_ ?_
    · simp only [afterTrial]; split
      · exact Finset.subset_insert _ _
      · exact le_rfl
    · intro x hx hxr
      simp only [afterTrial] at hx
      split at hx
      · rename_i hh
        rcases Finset.mem_insert.mp hx with h | h
        · exact absurd (h ▸ hxr) hh.2
        · exact h
      · exact hx
  · rw [h]
    exact freeRetired_mono f (Finset.subset_insert _ _) fun _ h _ => h
/-- The family world satisfies the abstract hazard with size `2^128`. -/
theorem hazardFam (budget : Nat) :
    Hazard environment (sampler Memory) (2 ^ 128) budget Inv Bad where
  step := inv_step environment
  bad state _ hbad := bad_step environment state hbad
  guesses state hs := hs.guesses
  hazard state hs hbad hg hp c v hc := by
    obtain ⟨a, q⟩ := c
    by_cases hq : q = 0
    · subst hq
      simp only [sampler, dif_pos rfl]
      exact hazard_seed state hs hbad hg budget hp a hc v
    · simp only [sampler, dif_neg hq]
      exact hazard_label state hs budget hp (a, q) hq hc v
end Preservation

/-! ### Erasure and the bounds of the family world -/

section Main
variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
variable (environment : Environment auxSpec GCoord Digest Memory)
theorem hiddenLaw_bind_const {Result : Type} (allowed : GCoord → Finset Digest)
    (hF : ∀ f, (famPostA allowed f).Nonempty) (hL : ∀ l, (labelAllowed allowed l).Nonempty) (X : SPMF Result) :
    (hiddenLaw allowed >>= fun _ => X) = X := by
  unfold hiddenLaw
  rw [complete_of_nonempty _ hF, complete_of_nonempty _ hL]
  simp only [bind_assoc, pure_bind]
  rw [show (fun _ : FamIdx → Coefs => (liftM (uniformTable (labelAllowed allowed) hL) : SPMF _) >>= fun _ => X) =
      fun _ => X from funext fun _ => RetainedObservation.lift_bind_const _ _]
  exact RetainedObservation.lift_bind_const _ _
/-- The eager family world (hidden coefficients and labels, then the fixed run) is the lazy family engine. -/
theorem fam_erasure {Result : Type} (computation : OracleComp (World auxSpec GCoord Digest) Result)
    (state : State GCoord Digest Memory) (hs : Inv state) :
    (hiddenLaw state.allowed >>= fun g => fixedRun environment g computation state) =
      withRun environment (sampler Memory) computation state := by
  have h := congrArg (Functor.map Prod.snd) (fam_posterior environment computation state)
  simp only [map_bind, Functor.map_map, id_map'] at h
  calc _ = (withRun environment (sampler Memory) computation state >>= fun result =>
          (fun _ => result) <$> hiddenLaw result.2.allowed) := h
    _ = (withRun environment (sampler Memory) computation state >>= pure) := by
      apply RetainedObservation.bind_congr
      intro result hr
      have hinv := withRun_preserves environment (sampler Memory) Inv
        (fun st hst input r hr' => inv_step environment st hst input r hr') computation state hs result hr
      rw [map_eq_bind_pure_comp]
      exact hiddenLaw_bind_const _ hinv.fam hinv.label _
    _ = _ := bind_pure _
/-- Pair bound of the family world (`trial_true_le'` is `hazard_seed` / `hazard_label`). -/
theorem fam_pair_le {Result : Type} (computation : OracleComp (World auxSpec GCoord Digest) Result)
    (memory : Memory) (budget : Nat) :
    Pr[fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 |
      withRun environment (sampler Memory) computation (initialState memory)] ≤
      (budget.choose 2 : ℝ≥0∞) * ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ ^ 2 :=
  withRun_pair_le (hazardFam environment budget) computation _ (inv_initial memory) rfl rfl
/-- First-guess forcing bound of the family world. -/
theorem fam_event_le_forced_slot {Result : Type} (computation : OracleComp (World auxSpec GCoord Digest) Result)
    (memory : Memory) (budget : Nat) (event : Result × State GCoord Digest Memory → Prop)
    (payoff : Nat → Result × State GCoord Digest Memory → ℝ≥0∞)
    (hevent : ∀ result, withRun environment (sampler Memory) computation (initialState memory) result ≠ 0 →
      event result → result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 ∧
        ∀ slot < result.2.probes, 1 ≤ payoff slot result) :
    Pr[event | withRun environment (sampler Memory) computation (initialState memory)] ≤
      ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedWithRun environment (sampler Memory) slot computation (initialState memory)] *
            payoff slot result :=
  withRun_event_le_forced_slot (hazardFam environment budget) computation _ (inv_initial memory) rfl rfl event
    payoff hevent
end Main
end ClaudeWCT.Guess.Fam
