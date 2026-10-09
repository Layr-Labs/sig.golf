import SigGolfCandidate.T3.Secc.LargeResidualT3
import SigGolfCandidate.ClaudeWCT.Arith.Family

/-!
# The residual lazy engine with FTS seed families (campaign X1, stream A5)

The T3 engine `SigGolfCandidate.T3.Security.LargeResidual` keeps a product posterior `candidates : Coord → Finset Digest`
and samples hidden labels uniformly from the product box. On the switched W9 spec some observables are FTS seeds:
the seed at `(family, point)` is `familyEval K point` for a hidden coefficient vector `K : Fin 102 → Digest`.

This module keeps the T3 `State` (the `candidates` record every disclosure and every failed guess, seeds included) and
changes the law: the hidden object is `x : Hid Coord = (Plain → Digest) × (∀ f, Coefs (deg f))` (uniform prior), observed
labels are `view x`, and the posterior given `candidates` is uniform on `supp candidates`, the hidden objects whose
labels lie in the candidate sets. Disclosures sample the posterior marginal (`discLaw`, uniform on the candidates for
plain coordinates); a probe's guess on a seed is kept only while its family is undetermined (`Adm`: at most `deg`
disclosed seeds in the family, and the hit is not a seed), and the seed hazard then comes from
`ClaudeWCT.Arith.fam_hazard_prob`. `run_posterior` (exact Bayes) and `residual_potential` keep the T3 statements.
-/

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response response_apply)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Coefficient vectors of a degree-`n` family. -/
abbrev Coefs (n : ℕ) := Fin (n + 1) → Digest

/-- The seed of a family at a point. -/
def ev {n : ℕ} (K : Fin n → Digest) (p : ℕ) : Digest := ClaudeWCT.Arith.familyEval (List.ofFn K) p

/-- Observable coordinates split into plain coordinates (independent uniform labels) and FTS seeds (a family and
an evaluation point below 1024; distinct seeds have distinct `(family, point)`). -/
class Seeds (Coord : Type) where
  Plain : Type
  Fam : Type
  [plainFin : Fintype Plain]
  [plainDec : DecidableEq Plain]
  [famFin : Fintype Fam]
  [famDec : DecidableEq Fam]
  deg : Fam → ℕ
  split : Coord → Plain ⊕ (Fam × ℕ)
  embed : Plain → Coord
  split_embed : ∀ p, split (embed p) = .inl p
  embed_of_split : ∀ c p, split c = .inl p → embed p = c
  point_lt : ∀ c f pt, split c = .inr (f, pt) → pt < 1024
  seed_inj : ∀ c c' fp, split c = .inr fp → split c' = .inr fp → c = c'

instance instSeedsPlainFin {Coord : Type} [h : Seeds Coord] : Fintype (Seeds.Plain Coord) := h.plainFin
instance instSeedsPlainDec {Coord : Type} [h : Seeds Coord] : DecidableEq (Seeds.Plain Coord) := h.plainDec
instance instSeedsFamFin {Coord : Type} [h : Seeds Coord] : Fintype (Seeds.Fam Coord) := h.famFin
instance instSeedsFamDec {Coord : Type} [h : Seeds Coord] : DecidableEq (Seeds.Fam Coord) := h.famDec

/-- Hidden objects: plain labels and family coefficients. -/
abbrev Hid (Coord : Type) [Seeds Coord] :=
  (Seeds.Plain Coord → Digest) × ((f : Seeds.Fam Coord) → Coefs (Seeds.deg f))

section Bayes
variable {Coord : Type} [Seeds Coord]

/-- Observed labels of a hidden object. -/
def view (x : Hid Coord) (c : Coord) : Digest :=
  match Seeds.split c with
  | .inl p => x.1 p
  | .inr fp => ev (x.2 fp.1) fp.2

/-- Hidden objects consistent with the candidate sets. -/
noncomputable def supp (cand : Coord → Finset Digest) : Finset (Hid Coord) :=
  Finset.univ.filter fun x => ∀ c, view x c ∈ cand c

theorem mem_supp (cand : Coord → Finset Digest) (x : Hid Coord) : x ∈ supp cand ↔ ∀ c, view x c ∈ cand c := by
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]

end Bayes

section Cell
variable {X : Type} [DecidableEq X]

/-- The guard identity for the uniform law on a finset. -/
theorem cell_guard (S : Finset X) (P : X → Prop) (x : X) :
    (if P x then cell S x else 0) = ((S.filter P).card / S.card : ℝ≥0∞) * cell (S.filter P) x := by
  rw [cell_apply, cell_apply]
  by_cases hx : x ∈ S.filter P
  · have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hP : P x := (Finset.mem_filter.mp hx).2
    rw [if_pos hP, if_pos hxS, if_pos hx]
    have hpos : ((S.filter P).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨x, hx⟩).ne'
    rw [div_eq_mul_inv, mul_comm ((S.filter P).card : ℝ≥0∞), mul_assoc,
      ENNReal.mul_inv_cancel hpos (ENNReal.natCast_ne_top _), mul_one]
  · rw [if_neg hx, mul_zero]
    by_cases hP : P x
    · rw [if_pos hP, if_neg (fun hxS => hx (Finset.mem_filter.mpr ⟨hxS, hP⟩))]
    · rw [if_neg hP]

theorem tsum_cell_mul (S : Finset X) (x : X) : (∑' y, cell S y) * cell S x = cell S x := by
  by_cases hS : S.Nonempty
  · rw [cell, dif_pos hS]
    simp only [SPMF.liftM_apply, PMF.tsum_coe, one_mul]
  · rw [cell_apply, if_neg (fun hx => hS ⟨x, hx⟩), mul_zero]

/-- The marginal law of `f` under the uniform law on `S`. -/
noncomputable def margOf (S : Finset X) {V : Type} (f : X → V) : SPMF V := cell S >>= fun x => pure (f x)

/-- The elements of `S` on which `f` takes the value `v`. -/
noncomputable def margFilter (S : Finset X) {V : Type} (f : X → V) (v : V) : Finset X := S.filter fun x => f x = v

theorem mem_margFilter (S : Finset X) {V : Type} (f : X → V) (v : V) (x : X) :
    x ∈ margFilter S f v ↔ x ∈ S ∧ f x = v := by
  rw [margFilter, Finset.mem_filter]

theorem margOf_apply (S : Finset X) {V : Type} (f : X → V) (v : V) :
    margOf S f v = ((margFilter S f v).card / S.card : ℝ≥0∞) * ∑' y, cell (margFilter S f v) y := by
  rw [margOf, SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  rw [margFilter, ← cell_guard S (fun x => f x = v) y, SPMF.pure_apply]
  by_cases h : f y = v
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

theorem margOf_mass (S : Finset X) {V : Type} (f : X → V) (v : V) (x : X) :
    margOf S f v * cell (margFilter S f v) x = if f x = v then cell S x else 0 := by
  rw [margOf_apply, mul_assoc, tsum_cell_mul, cell_guard S (fun x => f x = v) x, margFilter]

/-- Conditioning identity: observe `f x`, then sample from the filtered uniform law. -/
theorem bind_margOf {V Result : Type} (S : Finset X) (f : X → V) (next : V → X → SPMF Result) :
    (cell S >>= fun x => next (f x) x) =
      (margOf S f >>= fun v => cell (margFilter S f v) >>= next v) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, margOf_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  rw [tsum_eq_single (f x)]
  · simp only [if_true]
  · intro v hv
    rw [if_neg (Ne.symm hv)]

theorem margOf_nonempty (S : Finset X) {V : Type} (f : X → V) (v : V) (h : margOf S f v ≠ 0) :
    (margFilter S f v).Nonempty := by
  by_contra hn
  rw [margOf_apply, Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero,
    ENNReal.zero_div, zero_mul] at h
  exact h rfl

/-- Bayes for an observation whose likelihood is an indicator times a common weight. -/
theorem bind_cell_observe {Answer Result : Type} (S : Finset X) (hS : S.Nonempty) (resp : X → SPMF Answer)
    (keepP : Answer → X → Prop) (u : Answer → ℝ≥0∞) (hresp : ∀ x a, resp x a = if keepP a x then u a else 0)
    (stopped : SPMF Result) (next : Answer → X → SPMF Result) :
    (cell S >>= fun x => observe (resp x) stopped (fun a => next a x)) =
      observe (cell S >>= resp) stopped (fun a => cell (S.filter (keepP a)) >>= next a) := by
  have hcell : cell S = (liftM (PMF.uniformOfFinset S hS) : SPMF X) := by rw [cell, dif_pos hS]
  have h := posterior_observe (PMF.uniformOfFinset S hS) resp (cell S >>= resp) (fun a => cell (S.filter (keepP a)))
    (by rw [hcell])
    (fun a x => by
      rw [← SPMF.liftM_apply, ← hcell, hresp, SPMF.bind_apply_eq_tsum]
      have hsum : (∑' y, cell S y * resp y a) = u a * ((S.filter (keepP a)).card / S.card : ℝ≥0∞) *
          ∑' y, cell (S.filter (keepP a)) y := by
        rw [mul_assoc, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro y
        rw [hresp, ← cell_guard S (keepP a) y]
        split_ifs <;> simp only [mul_comm, mul_zero, zero_mul]
      rw [hsum, mul_assoc, mul_assoc, tsum_cell_mul, ← cell_guard S (keepP a) x]
      split_ifs <;> simp only [mul_comm, mul_zero, zero_mul])
    stopped next
  rw [← hcell] at h
  exact h

end Cell
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response response_apply Charge
  Request ResidualSpec World Counters State readState probeState stoppedState disclosedState tickState runWith
  runWith_pure runWith_query_bind retain mem_restrict)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Effective
variable {Coord : Type} [Seeds Coord] [Fintype Coord]

/-- The seed coordinates of family `f`. -/
@[irreducible] noncomputable def famSeeds (f : Seeds.Fam Coord) : Finset Coord :=
  Finset.univ.filter fun c => ∃ pt, Seeds.split c = .inr (f, pt)

/-- The seeds of family `f` with a singleton candidate set (disclosed). -/
noncomputable def famKnown (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : Finset Coord :=
  (famSeeds f).filter fun c => (cand c).card = 1

theorem mem_famSeeds (f : Seeds.Fam Coord) (c : Coord) : c ∈ famSeeds f ↔ ∃ pt, Seeds.split c = .inr (f, pt) := by
  unfold famSeeds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_famKnown (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) (c : Coord) :
    c ∈ famKnown cand f ↔ (∃ pt, Seeds.split c = .inr (f, pt)) ∧ (cand c).card = 1 := by
  rw [famKnown, Finset.mem_filter, mem_famSeeds]

/-- A guess `g` is kept by a probe with hit `hit` when its coordinate is still uncertain, differs from the hit's
parent, and, for a seed, its family is undetermined (at most `deg` disclosed seeds) and the hit is not a seed. -/
def Adm (cand : Coord → Finset Digest) (hit : Hit Coord) (g : Coord × Digest) : Prop :=
  2 ≤ (cand g.1).card ∧ (∀ parent, hit = Hit.label parent → g.1 ≠ parent) ∧
    ∀ fp, Seeds.split g.1 = .inr fp → (famKnown cand fp.1).card ≤ Seeds.deg fp.1 ∧
      ∀ parent, hit = Hit.label parent → ∀ fp', Seeds.split parent ≠ .inr fp'

end Effective

/-- The effective probe of the family engine: the guess is dropped unless `Adm`. -/
noncomputable def _root_.SigGolfCandidate.T3.Security.LargeResidual.Probe.effF {Coord : Type} [Seeds Coord]
    [Fintype Coord] (cand : Coord → Finset Digest) (probe : Probe Coord) : Probe Coord :=
  ⟨probe.guess.filter (fun g => decide (Adm cand probe.hit g)), probe.hit⟩

section Laws
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The predictive law of a probe answer. -/
noncomputable def lazyResp (cand : Coord → Finset Digest) (probe : Probe Coord) : SPMF HashOutput :=
  cell (supp cand) >>= fun x => response (view x) probe

/-- The posterior marginal of coordinate `c`. -/
noncomputable def discLaw (cand : Coord → Finset Digest) (c : Coord) : SPMF Digest :=
  margOf (supp cand) fun x => view x c

theorem supp_disclose (cand : Coord → Finset Digest) (c : Coord) (v : Digest) (hv : v ∈ cand c) :
    supp (discloseTableValue cand c v) = margFilter (supp cand) (fun x => view x c) v := by
  ext x
  simp only [mem_supp, mem_margFilter]
  constructor
  · intro h
    have hc := h c
    simp only [discloseTableValue, Function.update_self, Finset.mem_singleton] at hc
    refine ⟨fun c' => ?_, hc⟩
    by_cases hc' : c' = c
    · subst hc'; rw [hc]; exact hv
    · simpa only [discloseTableValue, Function.update_of_ne hc'] using h c'
  · rintro ⟨h, hc⟩ c'
    by_cases hc' : c' = c
    · subst hc'; simp only [discloseTableValue, Function.update_self, Finset.mem_singleton]; exact hc
    · simpa only [discloseTableValue, Function.update_of_ne hc'] using h c'

theorem discLaw_mem (cand : Coord → Finset Digest) (c : Coord) (v : Digest) (h : discLaw cand c v ≠ 0) :
    v ∈ cand c ∧ (supp (discloseTableValue cand c v)).Nonempty := by
  obtain ⟨x, hx⟩ := margOf_nonempty _ _ v h
  have hx' := (mem_margFilter _ _ _ _).mp hx
  have hv : v ∈ cand c := by rw [← hx'.2]; exact (mem_supp cand x).mp hx'.1 c
  exact ⟨hv, by rw [supp_disclose cand c v hv]; exact ⟨x, hx⟩⟩

theorem supp_probeRestrict (cand : Coord → Finset Digest) (probe : Probe Coord) (answer : HashOutput) :
    supp (probe.restrict cand answer) =
      (supp cand).filter fun x => probe.guessMiss (view x) ∧ probe.hit.labelMiss (view x) (low answer) := by
  ext x
  simp only [mem_supp, Finset.mem_filter]
  exact mem_restrict probe cand answer (view x)

theorem lazyResp_nonempty (cand : Coord → Finset Digest) (probe : Probe Coord) (answer : HashOutput)
    (h : lazyResp cand probe answer ≠ 0) :
    probe.hit.answerOk (low answer) ∧ (supp (probe.restrict cand answer)).Nonempty := by
  rw [lazyResp, SPMF.bind_apply_eq_tsum] at h
  obtain ⟨x, hx⟩ : ∃ x, cell (supp cand) x * response (view x) probe answer ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h (ENNReal.tsum_eq_zero.mpr hn)
  have h1 : cell (supp cand) x ≠ 0 := left_ne_zero_of_mul hx
  have h2 : response (view x) probe answer ≠ 0 := right_ne_zero_of_mul hx
  rw [cell_apply] at h1
  have hxs : x ∈ supp cand := by by_contra hn; exact h1 (if_neg hn)
  rw [response_apply] at h2
  have hk : probe.keep (view x) answer := by by_contra hn; exact h2 (if_neg hn)
  have hm := (Hit.miss_iff _ _ _).mp hk.2
  refine ⟨hm.2, x, ?_⟩
  rw [supp_probeRestrict, Finset.mem_filter]
  exact ⟨hxs, hk.1, hm.1⟩

end Laws

section World
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

/-- Observed run of the family engine: labels and table fixed, probes stop when the effective probe hits. -/
noncomputable def observedImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (table row), readState q state row (table row) charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => if (test.effF state.candidates).keep labels (table row) then
          pure (some (table row), probeState state row (test.effF state.candidates) (table row))
        else pure (none, stoppedState state)
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (labels coord), disclosedState q state coord (labels coord) charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)

/-- Lazy run of the family engine: posterior predictive answers and marginals. -/
noncomputable def lazyImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      reply state.rows row >>= fun answer => pure (some answer, readState q state row answer charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => observe (lazyResp state.candidates (test.effF state.candidates))
          (pure (none, stoppedState state))
          (fun answer => pure (some answer, probeState state row (test.effF state.candidates) answer))
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      discLaw state.candidates coord >>= fun value => pure (some value, disclosedState q state coord value charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)

noncomputable def observedRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (observedImpl aux q labels table) computation state

noncomputable def lazyRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (lazyImpl aux q) computation state

/-- Completion of a finished lazy run: hidden object from the posterior, then the residual rows. -/
noncomputable def finish {Result : Type} (result : Option Result × State Coord Cell) :
    SPMF (Option ((Coord → Digest) × (Cell → HashOutput) × Result) × State Coord Cell) :=
  match result.1 with
  | none => pure (none, result.2)
  | some value => cell (supp result.2.candidates) >>= fun x =>
      completeRows result.2.rows >>= fun table => pure (some (view x, table, value), result.2)

private theorem bind_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (next : A → SPMF B) :
    ((if p then left else right) >>= next) = if p then left >>= next else right >>= next := by
  split <;> rfl
private theorem map_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (f : A → B) :
    f <$> (if p then left else right) = if p then f <$> left else f <$> right := by
  split <;> rfl
omit [Seeds Coord] [Fintype Coord] [DecidableEq Coord] in
private theorem observe_response_eq (labels : Coord → Digest) (probe : Probe Coord) {Result : Type}
    (stopped : SPMF Result) (next : HashOutput → SPMF Result) :
    observe (response labels probe) stopped next =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= fun answer =>
        if probe.keep labels answer then next answer else stopped) := by
  rw [observe, response, toPMF_bind_lift]
  simp only [← PMF.monad_bind_eq_bind, evalSPMF_bind, bind_assoc]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, SPMF.toPMF_pure, SPMF.lift_pure, pure_bind]
  · simp only [h, if_false, SPMF.toPMF_failure, SPMF.lift_pure, pure_bind]
omit [Seeds Coord] [Fintype Coord] [DecidableEq Coord] in
private theorem fixedLabels_fresh (labels : Coord → Digest) (cache : ResidualTableCompletion.Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coord) {Result : Type} (stopped : SPMF Result)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) table else stopped) =
        observe (response labels probe) stopped
          (fun answer => completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [bind_fresh cache input hfresh (fun answer table => if probe.keep labels answer then next answer table else stopped),
    observe_response_eq]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true]
  · simp only [h, if_false, completeRows_bind_const]

private theorem bind_fresh_probe (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty)
    (cache : ResidualTableCompletion.Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coord) {Result : Type} (stopped : SPMF Result)
    (next : HashOutput → Hid Coord → (Cell → HashOutput) → SPMF Result) :
    (cell (supp cand) >>= fun x => completeRows cache >>= fun table =>
      if probe.keep (view x) (table input) then next (table input) x table else stopped) =
        observe (lazyResp cand probe) stopped (fun answer =>
          cell (supp (probe.restrict cand answer)) >>= fun x =>
            completeRows (Function.update cache input (some answer)) >>= next answer x) := by
  have hfixed (x : Hid Coord) := fixedLabels_fresh (view x) cache input hfresh probe stopped
    (fun answer table => next answer x table)
  simp_rw [hfixed]
  rw [bind_cell_observe (supp cand) hS (fun x => response (view x) probe) (fun a x => probe.keep (view x) a)
    (fun a => PMF.uniformOfFintype HashOutput a) (fun x a => response_apply (view x) probe a) stopped
    (fun answer x => completeRows (Function.update cache input (some answer)) >>= next answer x)]
  apply observe_congr
  intro answer hanswer
  obtain ⟨hok, -⟩ := lazyResp_nonempty cand probe answer hanswer
  rw [supp_probeRestrict]
  congr 2
  ext x
  simp only [Probe.keep, Hit.miss_iff, hok, and_true]

theorem run_posterior {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell)
    (ha : (supp state.candidates).Nonempty) :
    (cell (supp state.candidates) >>= fun x => completeRows state.rows >>= fun table =>
      retain (view x) table <$> observedRun aux q (view x) table computation state) =
        (lazyRun aux q computation state >>= finish) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [observedRun, lazyRun, runWith_pure, map_pure, pure_bind, retain, Option.map_some, finish]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
            StateT.run_mk, bind_assoc, pure_bind, map_bind, Option.elim_some]
          conv_lhs => enter [2, labels]; rw [RetainedObservation.bind_comm]
          rw [RetainedObservation.bind_comm]
          apply congrArg ((liftM (aux input) : SPMF _) >>= ·)
          funext answer
          exact ih answer state ha
      | inr input =>
          cases input with
          | read row charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              have hread (x : Hid Coord) := bind_read state.rows row
                (fun answer table => retain (view x) table <$>
                  runWith (observedImpl aux q (view x) table) (next answer) (readState q state row answer charge))
              simp_rw [hread]
              rw [RetainedObservation.bind_comm]
              apply congrArg (reply state.rows row >>= ·)
              funext answer
              exact ih answer (readState q state row answer charge) ha
          | probe row test =>
              cases hcache : state.rows row with
              | some answer =>
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, pure_bind, Option.elim_some]
                  have hrows : Function.update state.rows row (some answer) = state.rows := by
                    rw [← hcache, Function.update_eq_self]
                  have h := ih answer (readState q state row answer .call) ha
                  simp only [readState, hrows] at h ⊢
                  exact h
              | none =>
                  change HashOutput → OracleComp (World auxSpec Coord Cell) Result at next
                  dsimp only [OracleSpec.Range, World, ResidualSpec] at ih ⊢
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, observe_bind, pure_bind, Option.elim_none, Option.elim_some, finish]
                  dsimp only [OracleSpec.Range, World, OracleSpec.add_apply_inr, ResidualSpec]
                  simp only [bind_if, pure_bind, Option.elim_none, Option.elim_some, map_if, map_pure, retain,
                    Option.map_none]
                  rw [bind_fresh_probe state.candidates ha state.rows row hcache (test.effF state.candidates)
                    (pure (none, stoppedState state))
                    (fun answer x table => retain (view x) table <$>
                      runWith (observedImpl aux q (view x) table) (next answer)
                        (probeState state row (test.effF state.candidates) answer))]
                  apply observe_congr
                  intro answer hanswer
                  exact ih answer (probeState state row (test.effF state.candidates) answer)
                    (lazyResp_nonempty state.candidates _ answer hanswer).2
          | disclose coord charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              rw [bind_margOf (supp state.candidates) (fun x => view x coord) (fun value x =>
                completeRows state.rows >>= fun table => retain (view x) table <$>
                  runWith (observedImpl aux q (view x) table) (next value)
                    (disclosedState q state coord value charge))]
              apply RetainedObservation.bind_congr
              intro value hvalue
              obtain ⟨hv, hne⟩ := discLaw_mem state.candidates coord value hvalue
              have h := ih value (disclosedState q state coord value charge) hne
              simp only [disclosedState] at h ⊢
              rw [← supp_disclose state.candidates coord value hv]
              exact h
          | tick charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, pure_bind, Option.elim_some]
              exact ih () (tickState q state charge) ha

end World
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Ratio

/-- Updating one factor of a product finset scales its card by the factor's ratio. -/
theorem piFinset_update_card {I : Type} [Fintype I] [DecidableEq I] {α : I → Type} [∀ i, DecidableEq (α i)]
    (B : ∀ i, Finset (α i)) (i₀ : I) (B' : Finset (α i₀)) :
    (Fintype.piFinset (Function.update B i₀ B')).card * (B i₀).card = (Fintype.piFinset B).card * B'.card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i₀) (fun i => (Function.update B i₀ B' i).card),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i₀) (fun i => (B i).card)]
  have hrest : (∏ i ∈ Finset.univ \ {i₀}, (Function.update B i₀ B' i).card) = ∏ i ∈ Finset.univ \ {i₀}, (B i).card := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ i₀ := by simpa using hi
    rw [Function.update_of_ne hne]
  rw [hrest, Function.update_self]
  ring

theorem natCast_div_eq_of_mul_eq {a b c d : ℕ} (h : a * d = b * c) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℝ≥0∞) / b = c / d := by
  rw [ENNReal.div_eq_div_iff (by exact_mod_cast hd) (ENNReal.natCast_ne_top _) (by exact_mod_cast hb)
    (ENNReal.natCast_ne_top _)]
  exact_mod_cast (by rw [mul_comm, h, mul_comm] : d * a = b * c)

variable {X : Type} [DecidableEq X]

theorem probEvent_uniformOfFinset_le (S : Finset X) (hS : S.Nonempty) (P : X → Prop) :
    Pr[P | PMF.uniformOfFinset S hS] ≤ ((S.filter P).card : ℝ≥0∞) / S.card := by
  have hcell : ∀ x, PMF.uniformOfFinset S hS x = cell S x := by
    intro x
    rw [cell, dif_pos hS, SPMF.liftM_apply]
  rw [probEvent_eq_tsum_ite]
  simp only [PMF.probOutput_eq_apply, hcell]
  calc
    _ = ∑' x, ((S.filter P).card / S.card : ℝ≥0∞) * cell (S.filter P) x := by
      apply tsum_congr
      intro x
      exact cell_guard S P x
    _ = ((S.filter P).card / S.card : ℝ≥0∞) * ∑' x, cell (S.filter P) x := ENNReal.tsum_mul_left
    _ ≤ ((S.filter P).card / S.card : ℝ≥0∞) * 1 := by
      gcongr
      by_cases hn : (S.filter P).Nonempty
      · rw [cell, dif_pos hn]
        simp only [SPMF.liftM_apply, PMF.tsum_coe, le_refl]
      · rw [cell, dif_neg hn]
        simp only [SPMF.failure_apply, tsum_zero, zero_le]
    _ = _ := mul_one _

end Ratio

section Product
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The plain part of the candidate box. -/
def plainBox (cand : Coord → Finset Digest) : Seeds.Plain Coord → Finset Digest := fun p => cand (Seeds.embed p)

/-- The family posteriors: coefficient vectors whose seeds lie in the candidate sets. -/
@[irreducible] noncomputable def famSet (cand : Coord → Finset Digest) :
    (f : Seeds.Fam Coord) → Finset (Coefs (Seeds.deg f)) := fun f =>
  Finset.univ.filter fun K => ∀ c pt, Seeds.split c = .inr (f, pt) → ev K pt ∈ cand c

theorem mem_famSet (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) (K : Coefs (Seeds.deg f)) :
    K ∈ famSet cand f ↔ ∀ c pt, Seeds.split c = .inr (f, pt) → ev K pt ∈ cand c := by
  unfold famSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem view_embed (x : Hid Coord) (p : Seeds.Plain Coord) : view x (Seeds.embed p) = x.1 p := by
  unfold view
  rw [Seeds.split_embed]

theorem view_seed (x : Hid Coord) {c : Coord} {f : Seeds.Fam Coord} {pt : ℕ} (h : Seeds.split c = .inr (f, pt)) :
    view x c = ev (x.2 f) pt := by
  unfold view
  rw [h]

theorem mem_supp_iff_prod (cand : Coord → Finset Digest) (x : Hid Coord) :
    x ∈ supp cand ↔ (∀ p, x.1 p ∈ plainBox cand p) ∧ ∀ f, x.2 f ∈ famSet cand f := by
  rw [mem_supp]
  constructor
  · intro h
    refine ⟨fun p => ?_, fun f => (mem_famSet cand f (x.2 f)).mpr fun c pt hc => ?_⟩
    · have := h (Seeds.embed p)
      rwa [view_embed] at this
    · have := h c
      rwa [view_seed x hc] at this
  · rintro ⟨h1, h2⟩ c
    cases hc : Seeds.split c with
    | inl p =>
        have := h1 p
        rw [plainBox, Seeds.embed_of_split c p hc] at this
        unfold view
        rw [hc]
        exact this
    | inr fp =>
        rw [view_seed x (show Seeds.split c = .inr (fp.1, fp.2) from hc)]
        exact (mem_famSet cand fp.1 (x.2 fp.1)).mp (h2 fp.1) c fp.2 hc

theorem supp_eq_prod (cand : Coord → Finset Digest) :
    supp cand = Fintype.piFinset (plainBox cand) ×ˢ Fintype.piFinset (famSet cand) := by
  ext x
  rw [mem_supp_iff_prod, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]

/-- Ratio of a seed observation: the family posterior ratio. -/
theorem seed_ratio (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) {c : Coord} {f : Seeds.Fam Coord}
    {pt : ℕ} (hc : Seeds.split c = .inr (f, pt)) (v : Digest) :
    ((margFilter (supp cand) (fun x => view x c) v).card : ℝ≥0∞) / (supp cand).card =
      (((famSet cand f).filter fun K => ev K pt = v).card : ℝ≥0∞) / (famSet cand f).card := by
  have hfil : margFilter (supp cand) (fun x => view x c) v = Fintype.piFinset (plainBox cand) ×ˢ
      Fintype.piFinset (Function.update (famSet cand) f ((famSet cand f).filter fun K => ev K pt = v)) := by
    ext x
    rw [mem_margFilter, mem_supp_iff_prod, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset,
      view_seed x hc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun f' => ?_⟩
      by_cases hf : f' = f
      · subst hf; rw [Function.update_self, Finset.mem_filter]; exact ⟨h2 f', h3⟩
      · rw [Function.update_of_ne hf]; exact h2 f'
    · rintro ⟨h1, h2⟩
      have hf := h2 f
      rw [Function.update_self, Finset.mem_filter] at hf
      refine ⟨⟨h1, fun f' => ?_⟩, hf.2⟩
      by_cases hf' : f' = f
      · subst hf'; exact hf.1
      · have := h2 f'; rwa [Function.update_of_ne hf'] at this
  have hS' := hS
  rw [supp_eq_prod] at hS'
  have hcard : (supp cand).card ≠ 0 := Finset.card_ne_zero.mpr hS
  have hB : (famSet cand f).card ≠ 0 := by
    obtain ⟨x, hx⟩ := hS
    exact Finset.card_ne_zero.mpr ⟨x.2 f, ((mem_supp_iff_prod cand x).mp hx).2 f⟩
  apply natCast_div_eq_of_mul_eq _ hcard hB
  rw [hfil, supp_eq_prod, Finset.card_product, Finset.card_product, mul_assoc, piFinset_update_card, mul_assoc]

/-- Ratio of a plain observation. -/
theorem plain_ratio (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (p : Seeds.Plain Coord) (v : Digest) :
    ((margFilter (supp cand) (fun x => view x (Seeds.embed p)) v).card : ℝ≥0∞) / (supp cand).card ≤
      ((cand (Seeds.embed p)).card : ℝ≥0∞)⁻¹ := by
  have hfil : margFilter (supp cand) (fun x => view x (Seeds.embed p)) v = Fintype.piFinset
      (Function.update (plainBox cand) p ((plainBox cand p).filter fun w => w = v)) ×ˢ
      Fintype.piFinset (famSet cand) := by
    ext x
    rw [mem_margFilter, mem_supp_iff_prod, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset,
      view_embed]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun p' => ?_, h2⟩
      by_cases hp : p' = p
      · subst hp; rw [Function.update_self, Finset.mem_filter]; exact ⟨h1 p', h3⟩
      · rw [Function.update_of_ne hp]; exact h1 p'
    · rintro ⟨h1, h2⟩
      have hp := h1 p
      rw [Function.update_self, Finset.mem_filter] at hp
      refine ⟨⟨fun p' => ?_, h2⟩, hp.2⟩
      by_cases hp' : p' = p
      · subst hp'; exact hp.1
      · have := h1 p'; rwa [Function.update_of_ne hp'] at this
  have hcard : (supp cand).card ≠ 0 := Finset.card_ne_zero.mpr hS
  have hA : (plainBox cand p).card ≠ 0 := by
    obtain ⟨x, hx⟩ := hS
    exact Finset.card_ne_zero.mpr ⟨x.1 p, ((mem_supp_iff_prod cand x).mp hx).1 p⟩
  have heq : ((margFilter (supp cand) (fun x => view x (Seeds.embed p)) v).card : ℝ≥0∞) / (supp cand).card =
      (((plainBox cand p).filter fun w => w = v).card : ℝ≥0∞) / (plainBox cand p).card := by
    apply natCast_div_eq_of_mul_eq _ hcard hA
    rw [hfil, supp_eq_prod, Finset.card_product, Finset.card_product, mul_comm (Fintype.piFinset _).card,
      mul_assoc, piFinset_update_card]
    ring
  rw [heq, div_eq_mul_inv]
  have h1 : (((plainBox cand p).filter fun w => w = v).card : ℝ≥0∞) ≤ 1 := by
    have : ((plainBox cand p).filter fun w => w = v).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => by
        rw [Finset.mem_filter] at ha hb; rw [ha.2, hb.2]
    exact_mod_cast this
  calc _ ≤ 1 * ((plainBox cand p).card : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := one_mul _

end Product
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response hit_miss_prob)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Posterior
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The evaluation point of a seed coordinate. -/
def ptOf (c : Coord) : ℕ :=
  match Seeds.split c with
  | .inr fp => fp.2
  | .inl _ => 0

theorem ptOf_seed {c : Coord} {f : Seeds.Fam Coord} {pt : ℕ} (h : Seeds.split c = .inr (f, pt)) : ptOf c = pt := by
  unfold ptOf; rw [h]


/-- Disclosed `(point, value)` pairs of family `f`. -/
noncomputable def famKnownPairs (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : Finset (ℕ × Digest) :=
  (famKnown cand f).biUnion fun c => (cand c).image fun v => (ptOf c, v)

/-- Excluded `(point, value)` pairs of the undisclosed seeds of family `f`. -/
noncomputable def famMissPairs (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : Finset (ℕ × Digest) :=
  ((famSeeds f).filter fun c => (cand c).card ≠ 1).biUnion fun c => (Finset.univ \ cand c).image fun v => (ptOf c, v)

/-- Values excluded from the undisclosed seeds of family `f` (the failed guesses charged to the family). -/
noncomputable def famDebt (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) : ℕ :=
  ∑ c ∈ (famSeeds f).filter (fun c => (cand c).card ≠ 1), (2 ^ 128 - (cand c).card)

theorem famSet_eq_famPost (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    famSet cand f = ClaudeWCT.Arith.famPost (m := Seeds.deg f) (famKnownPairs cand f) (famMissPairs cand f) := by
  ext K
  rw [mem_famSet]
  unfold ClaudeWCT.Arith.famPost ClaudeWCT.Arith.famAffine
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
      obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hcs
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc1
      have h1 := h c pt hpt
      rw [hw, Finset.mem_singleton] at h1
      rw [hw, Finset.mem_singleton] at hv
      simp only [ptOf_seed hpt]
      rw [hv]
      exact h1
    · obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hcs, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hcs
      have h1 := h c pt hpt
      simp only [ptOf_seed hpt]
      intro heq
      apply (Finset.mem_sdiff.mp hv).2
      change ev K pt = v at heq
      rw [← heq]
      exact h1
  · rintro ⟨hk, hm⟩ c pt hc
    have hcs : c ∈ famSeeds f := (mem_famSeeds f c).mpr ⟨pt, hc⟩
    by_cases h1 : (cand c).card = 1
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
      have hmem : (pt, w) ∈ famKnownPairs cand f := by
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_filter.mpr ⟨hcs, h1⟩, Finset.mem_image.mpr ⟨w, by rw [hw]; exact Finset.mem_singleton_self w, ?_⟩⟩
        rw [ptOf_seed hc]
      have := hk _ hmem
      rw [hw, Finset.mem_singleton]
      exact this
    · by_contra hn
      have hmem : (pt, ev K pt) ∈ famMissPairs cand f := by
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_filter.mpr ⟨hcs, h1⟩, Finset.mem_image.mpr ⟨ev K pt, ?_, ?_⟩⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
        · rw [ptOf_seed hc]
      exact hm _ hmem rfl

theorem famKnownPairs_card (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    (famKnownPairs cand f).card ≤ (famKnown cand f).card := by
  refine Finset.card_biUnion_le.trans ?_
  calc _ ≤ ∑ c ∈ famKnown cand f, 1 := by
        apply Finset.sum_le_sum
        intro c hc
        exact Finset.card_image_le.trans (Finset.mem_filter.mp hc).2.le
    _ = _ := by simp

theorem card_digest_univ : (Finset.univ : Finset Digest).card = 2 ^ 128 := by
  rw [Finset.card_univ]
  simp [SphincsSecurity.digestBits]

theorem famMissPairs_card (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    (famMissPairs cand f).card ≤ famDebt cand f := by
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro c _
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), card_digest_univ]

theorem famKnownPairs_pt (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    ∀ p ∈ famKnownPairs cand f, ∃ c, (cand c).card = 1 ∧ Seeds.split c = .inr (f, p.1) := by
  intro p hp
  obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
  obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hcs
  exact ⟨c, hc1, by rw [ptOf_seed hpt]; exact hpt⟩

theorem famMissPairs_pt (cand : Coord → Finset Digest) (f : Seeds.Fam Coord) :
    ∀ p ∈ famMissPairs cand f, ∃ c, Seeds.split c = .inr (f, p.1) := by
  intro p hp
  obtain ⟨c, hc, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp (Finset.mem_filter.mp hc).1
  exact ⟨c, by rw [ptOf_seed hpt]; exact hpt⟩

/-- The hazard of an admissible guess: a uniform plain label or an undetermined family seed. -/
theorem guess_ratio_le (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probes : ℕ)
    (hinv : ∀ c, (cand c).card = 1 ∨ 2 ^ 128 - probes ≤ (cand c).card) (hdebt : ∀ f, famDebt cand f ≤ probes)
    (hit : Hit Coord) (g : Coord × Digest) (hadm : Adm cand hit g) :
    ((margFilter (supp cand) (fun x => view x g.1) g.2).card : ℝ≥0∞) / (supp cand).card ≤
      ((2 ^ 128 - probes : ℕ) : ℝ≥0∞)⁻¹ := by
  obtain ⟨h2, -, hseed⟩ := hadm
  have hcard : 2 ^ 128 - probes ≤ (cand g.1).card := by
    rcases hinv g.1 with h | h
    · omega
    · exact h
  cases hsplit : Seeds.split g.1 with
  | inl p =>
      have he : Seeds.embed p = g.1 := Seeds.embed_of_split g.1 p hsplit
      have h := plain_ratio cand hS p g.2
      rw [he] at h
      exact h.trans (ENNReal.inv_le_inv.mpr (by exact_mod_cast hcard))
  | inr fp =>
      obtain ⟨f, pt⟩ := fp
      obtain ⟨hk, -⟩ := hseed (f, pt) hsplit
      rw [seed_ratio cand hS hsplit g.2, famSet_eq_famPost]
      apply ClaudeWCT.Arith.fam_hazard_prob ((famKnownPairs_card cand f).trans hk)
      · intro p hp
        obtain ⟨c, -, hc⟩ := famKnownPairs_pt cand f p hp
        exact Seeds.point_lt c f p.1 hc
      · intro p hp
        obtain ⟨c, hc⟩ := famMissPairs_pt cand f p hp
        exact Seeds.point_lt c f p.1 hc
      · exact Seeds.point_lt g.1 f pt hsplit
      · intro hmem
        obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp hmem
        obtain ⟨c, hc1, hc⟩ := famKnownPairs_pt cand f p hp
        rw [hp1] at hc
        have := Seeds.seed_inj c g.1 (f, pt) hc hsplit
        rw [this] at hc1
        omega
      · exact (famMissPairs_card cand f).trans (hdebt f)

end Posterior
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe response hit_miss_prob response_failure)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Hazard
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- Joint law of the hidden object and a uniform answer. -/
noncomputable def lawF (S : Finset (Hid Coord)) (hS : S.Nonempty) : PMF (Hid Coord × HashOutput) :=
  (PMF.uniformOfFinset S hS).bind fun x => (PMF.uniformOfFintype HashOutput).map fun answer => (x, answer)

theorem lazyResp_failure (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probe : Probe Coord) :
    (lazyResp cand probe).toPMF none = Pr[fun z => ¬probe.keep (view z.1) z.2 | lawF (supp cand) hS] := by
  rw [lazyResp, cell, dif_pos hS, toPMF_bind_lift, PMF.bind_apply]
  change _ = Pr[fun z => ¬probe.keep (view z.1) z.2 |
    (PMF.uniformOfFinset (supp cand) hS) >>= fun x => (fun answer => (x, answer)) <$> PMF.uniformOfFintype HashOutput]
  rw [probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply, probEvent_map]
  apply tsum_congr
  intro x
  rw [response_failure]
  rfl

theorem keep_probF (S : Finset (Hid Coord)) (hS : S.Nonempty) (probe : Probe Coord) :
    Pr[fun z => probe.keep (view z.1) z.2 | lawF S hS] =
      Pr[fun x => probe.guessMiss (view x) | PMF.uniformOfFinset S hS] * (1 - (Fintype.card Digest : ENNReal)⁻¹) := by
  change Pr[fun z => probe.keep (view z.1) z.2 |
    (PMF.uniformOfFinset S hS) >>= fun x => (fun answer => (x, answer)) <$> PMF.uniformOfFintype HashOutput] = _
  rw [probEvent_bind_eq_tsum]
  have hinner (x : Hid Coord) :
      Pr[(fun z : Hid Coord × HashOutput => probe.keep (view z.1) z.2) ∘ (fun answer => (x, answer)) |
        PMF.uniformOfFintype HashOutput] =
      if probe.guessMiss (view x) then 1 - (Fintype.card Digest : ENNReal)⁻¹ else 0 := by
    by_cases hg : probe.guessMiss (view x)
    · rw [if_pos hg, ← hit_miss_prob probe.hit (view x)]
      have he : ((fun z : Hid Coord × HashOutput => probe.keep (view z.1) z.2) ∘ (fun answer => (x, answer))) =
          (fun answer => probe.hit.miss (view x) (low answer)) := by
        funext answer
        simp only [Function.comp_def, Probe.keep, hg, true_and]
      rw [he]
    · rw [if_neg hg]
      have he : ((fun z : Hid Coord × HashOutput => probe.keep (view z.1) z.2) ∘ (fun answer => (x, answer))) =
          (fun _ => False) := by
        funext answer
        simp only [Function.comp_def, Probe.keep, hg, false_and]
      rw [he, probEvent_eq_tsum_ite]
      simp
  simp only [probEvent_map, hinner, PMF.probOutput_eq_apply, mul_ite, mul_zero]
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  simp only [PMF.probOutput_eq_apply, ite_mul, zero_mul]

theorem guessMiss_prob_geF (S : Finset (Hid Coord)) (hS : S.Nonempty) (probe : Probe Coord) (minimum : ENNReal)
    (hmin : ∀ g ∈ probe.guess, Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset S hS] ≤ minimum) :
    1 - minimum ≤ Pr[fun x => probe.guessMiss (view x) | PMF.uniformOfFinset S hS] := by
  cases hg : probe.guess with
  | none =>
      have he : (fun x => probe.guessMiss (view x)) = (fun _ => True) := by
        funext x
        simp only [Probe.guessMiss, hg, Option.mem_def, reduceCtorEq, false_implies, implies_true]
      rw [he, probEvent_eq_tsum_ite]
      simp only [if_true, PMF.probOutput_eq_apply, PMF.tsum_coe]
      exact tsub_le_self
  | some g =>
      have hhit := hmin g (by rw [hg]; rfl)
      have hcompl := probEvent_compl (PMF.uniformOfFinset S hS) (fun x => view x g.1 = g.2)
      rw [probFailure_of_liftM_PMF, tsub_zero] at hcompl
      have hmiss : (fun x => probe.guessMiss (view x)) = (fun x => ¬view x g.1 = g.2) := by
        funext x
        simp only [Probe.guessMiss, hg, Option.mem_def, Option.some.injEq, forall_eq', ne_eq]
      rw [hmiss]
      have heq : Pr[fun x => ¬view x g.1 = g.2 | PMF.uniformOfFinset S hS] =
          1 - Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset S hS] :=
        ENNReal.eq_sub_of_add_eq' (by simp) (by rw [add_comm]; exact hcompl)
      rw [heq]
      exact tsub_le_tsub_left hhit 1

theorem lazyResp_failure_le_hazard (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probe : Probe Coord)
    (probes : Nat)
    (hmin : ∀ g ∈ probe.guess, Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset (supp cand) hS] ≤
      ((2 ^ 128 - probes : Nat) : ENNReal)⁻¹) :
    (lazyResp cand probe).toPMF none ≤ SigGolfCandidate.T3.Security.LargePotential.hazard (2 ^ 128) probes := by
  rw [lazyResp_failure cand hS probe]
  have hcompl := probEvent_compl (lawF (supp cand) hS) (fun z => probe.keep (view z.1) z.2)
  rw [probFailure_of_liftM_PMF, tsub_zero] at hcompl
  have heq : Pr[fun z => ¬probe.keep (view z.1) z.2 | lawF (supp cand) hS] =
      1 - Pr[fun z => probe.keep (view z.1) z.2 | lawF (supp cand) hS] :=
    ENNReal.eq_sub_of_add_eq' (by simp) (by rw [add_comm]; exact hcompl)
  rw [heq, SigGolfCandidate.T3.Security.LargePotential.hazard]
  apply tsub_le_tsub_left _ 1
  rw [keep_probF (supp cand) hS probe, pow_two]
  apply mul_le_mul' (guessMiss_prob_geF (supp cand) hS probe _ hmin)
  apply tsub_le_tsub_left
  have hcard : (Fintype.card Digest : ENNReal) = ((2 ^ 128 : Nat) : ENNReal) := by
    simp [SphincsSecurity.digestBits]
  rw [hcard]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.sub_le _ _)

/-- The hazard of an admissible guess as a probability. -/
theorem guess_prob_le (cand : Coord → Finset Digest) (hS : (supp cand).Nonempty) (probes : ℕ)
    (hinv : ∀ c, (cand c).card = 1 ∨ 2 ^ 128 - probes ≤ (cand c).card) (hdebt : ∀ f, famDebt cand f ≤ probes)
    (hit : Hit Coord) (g : Coord × Digest) (hadm : Adm cand hit g) :
    Pr[fun x => view x g.1 = g.2 | PMF.uniformOfFinset (supp cand) hS] ≤ ((2 ^ 128 - probes : Nat) : ENNReal)⁻¹ :=
  (probEvent_uniformOfFinset_le _ hS _).trans (guess_ratio_le cand hS probes hinv hdebt hit g hadm)

end Hazard
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargePotential (Step Charges StepBound FreeStep MassStep ProbeStep hazard)
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe Charge Request ResidualSpec World
  Counters State readState probeState stoppedState disclosedState tickState runWith runWith_pure runWith_query_bind
  charges initial stop_zero_of_shape support_of_shape stepBound_of_charge observe_stop observe_support
  card_restrict_ge restrict_subset_card restrict_subset)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Debt
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

theorem famDebt_le_of (cand cand' : Coord → Finset Digest) (f : Seeds.Fam Coord)
    (hsub : ∀ c, cand' c ⊆ cand c) (hne : ∀ c, (cand' c).Nonempty)
    (hdrop : ∀ c, (cand c).card ≤ (cand' c).card + 1)
    (hone : ∀ c ∈ famSeeds f, ∀ c' ∈ famSeeds f, cand' c ≠ cand c → cand' c' ≠ cand c' → c = c') :
    famDebt cand' f ≤ famDebt cand f + 1 := by
  unfold famDebt
  set T := (famSeeds f).filter fun c => (cand c).card ≠ 1
  set T' := (famSeeds f).filter fun c => (cand' c).card ≠ 1
  have hTT : T' ⊆ T := by
    intro c hc
    obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hcs, fun h1 => hc1 ?_⟩
    have hle := Finset.card_le_card (hsub c)
    have hpos := (hne c).card_pos
    omega
  have hterm : ∀ c ∈ T', 2 ^ 128 - (cand' c).card ≤ (2 ^ 128 - (cand c).card) + (if cand' c = cand c then 0 else 1) := by
    intro c _
    by_cases heq : cand' c = cand c
    · rw [if_pos heq, heq, add_zero]
    · rw [if_neg heq]
      have := hdrop c
      omega
  calc
    _ ≤ ∑ c ∈ T', ((2 ^ 128 - (cand c).card) + (if cand' c = cand c then 0 else 1)) := Finset.sum_le_sum hterm
    _ = ∑ c ∈ T', (2 ^ 128 - (cand c).card) + ∑ c ∈ T', (if cand' c = cand c then 0 else 1) :=
        Finset.sum_add_distrib
    _ ≤ ∑ c ∈ T, (2 ^ 128 - (cand c).card) + 1 := by
        apply add_le_add (Finset.sum_le_sum_of_subset hTT)
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
        apply Finset.card_le_one.mpr
        intro a ha b hb
        obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
        exact hone a (Finset.mem_filter.mp ha1).1 b (Finset.mem_filter.mp hb1).1 ha2 hb2

theorem famDebt_disclose_le (cand : Coord → Finset Digest) (c0 : Coord) (v : Digest) (f : Seeds.Fam Coord) :
    famDebt (discloseTableValue cand c0 v) f ≤ famDebt cand f := by
  unfold famDebt
  have hsame : ∀ c ∈ (famSeeds f).filter (fun c => (discloseTableValue cand c0 v c).card ≠ 1),
      discloseTableValue cand c0 v c = cand c := by
    intro c hc
    have hc1 := (Finset.mem_filter.mp hc).2
    have hne : c ≠ c0 := by
      rintro rfl
      simp [discloseTableValue] at hc1
    simp only [discloseTableValue, Function.update_of_ne hne]
  rw [Finset.sum_congr rfl (fun c hc => by rw [hsame c hc])]
  apply Finset.sum_le_sum_of_subset
  intro c hc
  obtain ⟨hcs, hc1⟩ := Finset.mem_filter.mp hc
  refine Finset.mem_filter.mpr ⟨hcs, ?_⟩
  rw [← hsame c hc]
  exact hc1

theorem restrict_eq_of_ne (probe : Probe Coord) (cand : Coord → Finset Digest) (answer : HashOutput) (c : Coord)
    (hg : ∀ g ∈ probe.guess, c ≠ g.1) (hp : ∀ parent, probe.hit = Hit.label parent → c ≠ parent) :
    probe.restrict cand answer c = cand c := by
  have hguess : probe.guessRestrict cand c = cand c := by
    unfold Probe.guessRestrict
    cases hgs : probe.guess with
    | none => rfl
    | some g =>
        simp only [eraseTableValue]
        rw [Function.update_of_ne (hg g (by rw [hgs]; rfl))]
  unfold Probe.restrict
  cases hh : probe.hit with
  | target t => simp only [Hit.restrict]; exact hguess
  | label parent =>
      simp only [Hit.restrict, eraseTableValue]
      rw [Function.update_of_ne (hp parent hh)]
      exact hguess

theorem famDebt_probe_le (cand : Coord → Finset Digest) (test : Probe Coord) (answer : HashOutput)
    (hne : ∀ c, ((test.effF cand).restrict cand answer c).Nonempty) (f : Seeds.Fam Coord) :
    famDebt ((test.effF cand).restrict cand answer) f ≤ famDebt cand f + 1 := by
  have hadm : ∀ g ∈ (test.effF cand).guess, Adm cand (test.effF cand).hit g := by
    intro g hg
    simp only [Probe.effF, Option.mem_def, Option.filter_eq_some_iff, decide_eq_true_eq] at hg
    exact hg.2
  apply famDebt_le_of cand _ f (restrict_subset _ cand answer) hne
  · intro c
    have := card_restrict_ge (test.effF cand) cand answer (fun g hg => (hadm g hg).2.1) c
    omega
  · have hchanged : ∀ c, (test.effF cand).restrict cand answer c ≠ cand c →
        (∃ g ∈ (test.effF cand).guess, c = g.1) ∨ ∃ parent, (test.effF cand).hit = Hit.label parent ∧ c = parent := by
      intro c hc
      by_contra hn
      push Not at hn
      exact hc (restrict_eq_of_ne _ cand answer c hn.1 hn.2)
    intro c hc c' hc' hch hch'
    obtain ⟨pt, hpt⟩ := (mem_famSeeds f c).mp hc
    obtain ⟨pt', hpt'⟩ := (mem_famSeeds f c').mp hc'
    rcases hchanged c hch with ⟨g, hg, rfl⟩ | ⟨p, hp, rfl⟩ <;>
      rcases hchanged c' hch' with ⟨g', hg', rfl⟩ | ⟨p', hp', rfl⟩
    · rw [Option.mem_def] at hg hg'; rw [hg] at hg'; cases hg'; rfl
    · exact absurd hpt' (((hadm g hg).2.2 _ hpt).2 _ hp' _)
    · exact absurd hpt (((hadm g' hg').2.2 _ hpt').2 _ hp _)
    · rw [hp] at hp'; cases hp'; rfl

end Debt

section Bound
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

noncomputable def residualStep (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    Step SPMF (World auxSpec Coord Cell) (State Coord Cell) :=
  fun request state => ((lazyImpl aux q request).run).run state

/-- Invariant of the family engine: a consistent posterior, the T3 per-coordinate bound, and family debts within
the probe count. -/
def Inv (state : State Coord Cell) : Prop :=
  (supp state.candidates).Nonempty ∧
    (∀ c, (state.candidates c).card = 1 ∨ 2 ^ 128 - state.counters.probes ≤ (state.candidates c).card) ∧
    ∀ f, famDebt state.candidates f ≤ state.counters.probes

theorem supp_univ : (supp (fun _ : Coord => (Finset.univ : Finset Digest))) = Finset.univ := by
  ext x
  simp only [mem_supp, Finset.mem_univ, implies_true]

theorem initial_inv : Inv (initial : State Coord Cell) := by
  refine ⟨?_, fun c => Or.inr ?_, fun f => ?_⟩
  · change (supp (fun _ : Coord => (Finset.univ : Finset Digest))).Nonempty
    rw [supp_univ]
    exact Finset.univ_nonempty
  · change 2 ^ 128 - 0 ≤ (Finset.univ : Finset Digest).card
    rw [card_digest_univ]
    omega
  · change famDebt (fun _ : Coord => (Finset.univ : Finset Digest)) f ≤ 0
    unfold famDebt
    simp only [card_digest_univ, Nat.sub_self, Finset.sum_const_zero, le_refl]

theorem run_residual {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (program : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :
    SigGolfCandidate.T3.Security.LargePotential.run (residualStep aux q) program state = lazyRun aux q program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rw [SigGolfCandidate.T3.Security.LargePotential.run_pure, lazyRun, runWith_pure]
  | query_bind input next ih =>
      rw [SigGolfCandidate.T3.Security.LargePotential.run_query_bind, lazyRun, runWith_query_bind]
      apply _root_.bind_congr
      intro middle
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none => rfl
      | some answer => exact ih answer after

theorem effF_adm (cand : Coord → Finset Digest) (test : Probe Coord) :
    ∀ g ∈ (test.effF cand).guess, Adm cand (test.effF cand).hit g := by
  intro g hg
  simp only [Probe.effF, Option.mem_def, Option.filter_eq_some_iff, decide_eq_true_eq] at hg
  exact hg.2

theorem residual_step_bound (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (hinv : Inv state) :
    StepBound (residualStep aux q) charges (2 ^ 128) q input state := by
  cases input with
  | inl input =>
      apply stepBound_of_charge q (residualStep aux q) (.inl input) state .none (liftM (aux input) : SPMF _)
        id (fun _ => state)
      · rfl
      · intro a; rfl
  | inr request =>
      cases request with
      | read row charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.read row charge)) state charge
            (reply state.rows row) id (fun a => readState q state row a charge)
          · rfl
          · intro a; rfl
      | disclose coord charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.disclose coord charge)) state charge
            (discLaw state.candidates coord) id (fun v => disclosedState q state coord v charge)
          · rfl
          · intro a; rfl
      | tick charge =>
          apply stepBound_of_charge q (residualStep aux q) (.inr (.tick charge)) state charge
            (pure ()) id (fun _ => tickState q state charge)
          · change pure (some (), tickState q state charge) = _
            rw [pure_bind]
          · intro a; rfl
      | probe row test =>
          cases hcache : state.rows row with
          | some answer =>
              apply stepBound_of_charge q (residualStep aux q) (.inr (.probe row test)) state .call
                (pure answer) id (fun a => readState q state row a .call)
              · change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache, pure_bind]
                rfl
              · intro a; rfl
          | none =>
              right; right; right
              have hstep : residualStep aux q (.inr (.probe row test)) state =
                  observe (lazyResp state.candidates (test.effF state.candidates))
                    (pure (none, stoppedState state))
                    (fun answer => pure (some answer, probeState state row (test.effF state.candidates) answer)) := by
                change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache]
              refine ⟨fun result hresult => ?_, ?_⟩
              · rw [hstep] at hresult
                rcases observe_support _ _ _ result hresult with rfl | ⟨answer, _, rfl⟩
                · simp only [charges, stoppedState, Counters.probe]; omega
                · simp only [charges, probeState, Counters.probe]; omega
              · rw [hstep]
                erw [observe_stop]
                by_cases hp : state.counters.probes < 2 ^ 128
                · exact lazyResp_failure_le_hazard state.candidates hinv.1 _ state.counters.probes
                    (fun g hg => guess_prob_le state.candidates hinv.1 state.counters.probes hinv.2.1 hinv.2.2
                      _ g (effF_adm state.candidates test g hg))
                · have hzero : (((2 ^ 128 - state.counters.probes : Nat) : ENNReal))⁻¹ = ⊤ := by
                    rw [show 2 ^ 128 - state.counters.probes = 0 by omega, Nat.cast_zero, ENNReal.inv_zero]
                  have hh : hazard (2 ^ 128) state.counters.probes = 1 := by
                    simp only [SigGolfCandidate.T3.Security.LargePotential.hazard, hzero]
                    simp
                  change _ ≤ hazard (2 ^ 128) state.counters.probes
                  rw [hh]
                  exact PMF.coe_le_one _ _

theorem support_of_shape' {X R : Type} (p : SPMF X) (g : X → R) (f : X → State Coord Cell)
    (result : Option R × State Coord Cell) (hresult : result ∈ support (p >>= fun a => pure (some (g a), f a))) :
    ∃ a, p a ≠ 0 ∧ result = (some (g a), f a) := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨a, ha, hr⟩ := hresult
  rw [mem_support_pure_iff] at hr
  refine ⟨a, ?_, hr⟩
  rw [mem_support_iff, SPMF.probOutput_eq_apply] at ha
  exact ha

theorem residual_preserve (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (input : (World auxSpec Coord Cell).Domain) (state : State Coord Cell) (hinv : Inv state)
    (answer : (World auxSpec Coord Cell).Range input) (after : State Coord Cell)
    (hafter : (some answer, after) ∈ support (residualStep aux q input state)) : Inv after := by
  have hsame : ∀ after : State Coord Cell, after.candidates = state.candidates →
      after.counters.probes = state.counters.probes → Inv after := by
    intro after hc hp
    unfold Inv
    rw [hc, hp]
    exact hinv
  cases input with
  | inl input =>
      obtain ⟨a, ha⟩ := support_of_shape (liftM (aux input) : SPMF _) id (fun _ => state) _ hafter
      simp only [Prod.mk.injEq] at ha
      rw [ha.2]; exact hinv
  | inr request =>
      cases request with
      | read row charge =>
          obtain ⟨a, ha⟩ := support_of_shape (reply state.rows row) id (fun a => readState q state row a charge) _ hafter
          simp only [Prod.mk.injEq] at ha
          rw [ha.2]
          exact hsame _ rfl (SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes _ _ _)
      | tick charge =>
          change (some answer, after) ∈ support (pure (some (), tickState q state charge) : SPMF _) at hafter
          rw [mem_support_pure_iff, Prod.mk.injEq] at hafter
          rw [hafter.2]
          exact hsame _ rfl (SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes _ _ _)
      | disclose coord charge =>
          obtain ⟨v, hv0, hv⟩ := support_of_shape' (discLaw state.candidates coord) id
            (fun v => disclosedState q state coord v charge) _ hafter
          simp only [Prod.mk.injEq] at hv
          rw [hv.2]
          obtain ⟨-, hne⟩ := discLaw_mem state.candidates coord v hv0
          refine ⟨hne, fun c => ?_, fun f => ?_⟩
          · by_cases hc : c = coord
            · subst hc
              left
              simp only [disclosedState, discloseTableValue, Function.update_self, Finset.card_singleton]
            · simp only [disclosedState, discloseTableValue, Function.update_of_ne hc,
                SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes]
              exact hinv.2.1 c
          · simp only [disclosedState, SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes]
            exact (famDebt_disclose_le _ _ _ f).trans (hinv.2.2 f)
      | probe row test =>
          cases hcache : state.rows row with
          | some cached =>
              change (some answer, after) ∈ support (match state.rows row with
                | some answer => (pure (some answer, readState q state row answer .call) : SPMF _)
                | none => _) at hafter
              rw [hcache, mem_support_pure_iff, Prod.mk.injEq] at hafter
              rw [hafter.2]
              exact hsame _ rfl (SigGolfCandidate.T3.Security.LargeResidual.Counters.charge_probes _ _ _)
          | none =>
              have hstep : residualStep aux q (.inr (.probe row test)) state =
                  observe (lazyResp state.candidates (test.effF state.candidates))
                    (pure (none, stoppedState state))
                    (fun answer => pure (some answer, probeState state row (test.effF state.candidates) answer)) := by
                change (match state.rows row with
                  | some answer => pure (some answer, readState q state row answer .call)
                  | none => _) = _
                rw [hcache]
              rw [hstep] at hafter
              rcases observe_support _ _ _ _ hafter with h | ⟨a, ha, h⟩
              · simp at h
              · simp only [Prod.mk.injEq] at h
                rw [h.2]
                obtain ⟨-, hS'⟩ := lazyResp_nonempty state.candidates _ a ha
                have hne : ∀ c, ((test.effF state.candidates).restrict state.candidates a c).Nonempty := by
                  obtain ⟨x, hx⟩ := hS'
                  exact fun c => ⟨view x c, (mem_supp _ x).mp hx c⟩
                refine ⟨hS', fun c => ?_, fun f => ?_⟩
                · have hge := card_restrict_ge (test.effF state.candidates) state.candidates a
                    (fun g hg => (effF_adm state.candidates test g hg).2.1) c
                  have hle := restrict_subset_card (test.effF state.candidates) state.candidates a c
                  have hpos := (hne c).card_pos
                  simp only [probeState, Counters.probe]
                  rcases hinv.2.1 c with h1 | h2
                  · left; omega
                  · right; omega
                · simp only [probeState, Counters.probe]
                  exact (famDebt_probe_le state.candidates test a hne f).trans (by have := hinv.2.2 f; omega)

theorem residual_potential {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (hq : q ≤ 2 ^ 127) (program : OracleComp (World auxSpec Coord Cell) Result) :
    Pr[fun result => result.1 = none ∧ result.2.counters.calls ≤ q | lazyRun aux q program initial] +
      (∑' result, Pr[= result | lazyRun aux q program initial] * (result.2.counters.mass : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := SigGolfCandidate.T3.Security.LargePotential.run_potential_initial (residualStep aux q) charges q hq Inv
    (fun input state hinv _ answer after hafter => residual_preserve aux q input state hinv answer after hafter)
    (fun input state hinv _ => residual_step_bound aux q input state hinv) program initial initial_inv rfl rfl
  rw [run_residual] at h
  exact h

end Bound
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput low Hit Probe Charge Request ResidualSpec World
  Counters State readState probeState stoppedState disclosedState tickState runWith runWith_pure runWith_query_bind)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Steps
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)

section Observed
variable (labels : Coord → Digest) (table : Cell → HashOutput)
theorem observed_pure {β : Type} (v : β) (s : State Coord Cell) :
    observedRun aux q labels table (pure v) s = pure (some v, s) :=
  runWith_pure _ v s
theorem observed_aux {β : Type} (i : AuxIndex) (k : auxSpec.Range i → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem observed_read {β : Type} (row : Cell) (ch : Charge) (k : HashOutput → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.read row ch))) >>= k) s =
      observedRun aux q labels table (k (table row)) (readState q s row (table row) ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
theorem observed_probe_cached {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (v : HashOutput)
    (h : s.rows row = some v) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      observedRun aux q labels table (k v) (readState q s row v .call) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, h, pure_bind, Option.elim_some]
  rfl
theorem observed_probe_fresh {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (h : s.rows row = none) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      if (test.effF s.candidates).keep labels (table row) then
        observedRun aux q labels table (k (table row)) (probeState s row (test.effF s.candidates) (table row))
      else pure (none, stoppedState s) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, h]
  split_ifs <;> simp only [pure_bind, Option.elim_some, Option.elim_none, observedRun]
theorem observed_disclose {β : Type} (c : Coord) (ch : Charge) (k : Digest → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.disclose c ch))) >>= k) s =
      observedRun aux q labels table (k (labels c)) (disclosedState q s c (labels c) ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
theorem observed_tick {β : Type} (ch : Charge) (k : Unit → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.tick ch))) >>= k) s =
      observedRun aux q labels table (k ()) (tickState q s ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
end Observed

section Lazy
theorem lazy_pure {β : Type} (v : β) (s : State Coord Cell) :
    lazyRun aux q (pure v) s = pure (some v, s) :=
  runWith_pure _ v s
theorem lazy_aux' {β : Type} (i : AuxIndex) (k : auxSpec.Range i → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => lazyRun aux q (k v) s) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem lazy_read {β : Type} (row : Cell) (ch : Charge) (k : HashOutput → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.read row ch))) >>= k) s =
      (reply s.rows row >>= fun y => lazyRun aux q (k y) (readState q s row y ch)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem lazy_probe_cached {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (v : HashOutput)
    (h : s.rows row = some v) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      lazyRun aux q (k v) (readState q s row v .call) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, h, pure_bind, Option.elim_some]
  rfl
theorem lazy_probe_fresh {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (h : s.rows row = none) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      observe (lazyResp s.candidates (test.effF s.candidates)) (pure (none, stoppedState s))
        (fun y => lazyRun aux q (k y) (probeState s row (test.effF s.candidates) y)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, h, observe_bind, pure_bind, Option.elim_none,
    Option.elim_some]
  rfl
theorem lazy_disclose {β : Type} (c : Coord) (ch : Charge) (k : Digest → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.disclose c ch))) >>= k) s =
      (discLaw s.candidates c >>= fun v => lazyRun aux q (k v) (disclosedState q s c v ch)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl
theorem lazy_tick {β : Type} (ch : Charge) (k : Unit → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.tick ch))) >>= k) s =
      lazyRun aux q (k ()) (tickState q s ch) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl
end Lazy
end Steps

section Plain
variable {Coord : Type} [Seeds Coord] [Fintype Coord] [DecidableEq Coord]

/-- The marginal of a plain coordinate is dominated by the uniform law on its candidates. -/
theorem discLaw_le_cell (cand : Coord → Finset Digest) {c : Coord} {p : Seeds.Plain Coord}
    (hc : Seeds.split c = .inl p) (v : Digest) : discLaw cand c v ≤ cell (cand c) v := by
  have he : Seeds.embed p = c := Seeds.embed_of_split c p hc
  rw [discLaw, margOf_apply]
  by_cases hv : v ∈ cand c
  · rw [cell_apply, if_pos hv]
    by_cases hS : (supp cand).Nonempty
    · have h := plain_ratio cand hS p v
      rw [he] at h
      calc _ ≤ ((margFilter (supp cand) (fun x => view x c) v).card / (supp cand).card : ℝ≥0∞) * 1 := by
            gcongr
            by_cases hn : (margFilter (supp cand) (fun x => view x c) v).Nonempty
            · rw [cell, dif_pos hn]; simp only [SPMF.liftM_apply, PMF.tsum_coe, le_refl]
            · rw [cell, dif_neg hn]; simp only [SPMF.failure_apply, tsum_zero, zero_le]
        _ ≤ _ := by rw [mul_one]; exact h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp [margFilter]
  · have hempty : margFilter (supp cand) (fun x => view x c) v = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨hxs, hxv⟩ := (mem_margFilter _ _ _ _).mp hx
      exact hv (hxv ▸ (mem_supp cand x).mp hxs c)
    rw [hempty]
    simp

theorem expectedValue_discLaw_le (cand : Coord → Finset Digest) {c : Coord} {p : Seeds.Plain Coord}
    (hc : Seeds.split c = .inl p) (g : Digest → ENNReal) :
    expectedValue (discLaw cand c) g ≤ expectedValue (cell (cand c)) g := by
  simp only [expectedValue_def]
  apply ENNReal.tsum_le_tsum
  intro v
  rw [SPMF.probOutput_eq_apply, SPMF.probOutput_eq_apply]
  gcongr
  exact discLaw_le_cell cand hc v

end Plain
end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open SigGolfCandidate.T3.Security.LargeResidual (Digest Hit Probe)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Coord : Type} [Seeds Coord] [Fintype Coord]

theorem effF_self (cand : Coord → Finset Digest) (test : Probe Coord)
    (h : ∀ g ∈ test.guess, Adm cand test.hit g) : test.effF cand = test := by
  obtain ⟨guess, hit⟩ := test
  unfold Probe.effF
  cases guess with
  | none => rfl
  | some g =>
      have hg' := h g rfl
      simp only [Option.filter_some, decide_eq_true_eq]
      rw [if_pos hg']

/-- `Adm` for a plain guess: the T3 admissibility. -/
theorem adm_of_plain (cand : Coord → Finset Digest) (hit : Hit Coord) (g : Coord × Digest)
    {p : Seeds.Plain Coord} (hp : Seeds.split g.1 = .inl p) (h2 : 2 ≤ (cand g.1).card)
    (hpar : ∀ parent, hit = Hit.label parent → g.1 ≠ parent) : Adm cand hit g :=
  ⟨h2, hpar, fun fp h => by rw [hp] at h; cases h⟩

end ClaudeWCT.W9.T3.Security.FamResidual
end

section
namespace ClaudeWCT.W9.T3.Security.FamResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SigGolfCandidate.T3.Security.LargeResidual (Digest HashOutput World State runWith runWith_pure runWith_query_bind
  initial)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section NoFail
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Seeds Coord] [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
  (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)

theorem observed_noFail (labels : Coord → Digest) (table : Cell → HashOutput) {R : Type}
    (P : OracleComp (World auxSpec Coord Cell) R) :
    ∀ s, Pr[⊥ | observedRun aux q labels table P s] = 0 := by
  induction P using OracleComp.inductionOn with
  | pure v =>
      intro s
      rw [observedRun, runWith_pure]
      simp
  | query_bind input next ih =>
      intro s
      rw [observedRun, runWith_query_bind, probFailure_bind_eq_add_tsum]
      have h1 : Pr[⊥ | (observedImpl aux q labels table input).run.run s] = 0 := by
        rcases input with i | req
        · simp [observedImpl]
        · cases req with
          | read row ch => simp [observedImpl]
          | probe row test =>
              simp only [observedImpl, OptionT.run_mk, StateT.run_mk]
              split
              · simp
              · split <;> simp
          | disclose c ch => simp [observedImpl]
          | tick ch => simp [observedImpl]
      rw [h1, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro r
      rcases r with ⟨o, s'⟩
      cases o with
      | none => simp
      | some v =>
          simp only [Option.elim_some]
          exact mul_eq_zero_of_right _ (ih v s')

theorem supp_initial_nonempty : (supp (initial : State Coord Cell).candidates).Nonempty := by
  change (supp (fun _ : Coord => (Finset.univ : Finset Digest))).Nonempty
  rw [supp_univ]
  exact Finset.univ_nonempty

theorem lazy_noFail {R : Type} (P : OracleComp (World auxSpec Coord Cell) R) :
    Pr[⊥ | lazyRun aux q P (initial : State Coord Cell)] = 0 := by
  have hS := supp_initial_nonempty (Coord := Coord) (Cell := Cell)
  have hpost := run_posterior aux q P (initial : State Coord Cell) hS
  have h1 : Pr[⊥ | lazyRun aux q P (initial : State Coord Cell) >>= finish] = 0 := by
    rw [← hpost]
    have hc : cell (supp (initial : State Coord Cell).candidates) =
        liftM (PMF.uniformOfFinset (supp (initial : State Coord Cell).candidates) hS) := by
      rw [cell, dif_pos hS]
    have hr : completeRows (initial : State Coord Cell).rows =
        liftM (PMF.uniformOfFintype (Cell → HashOutput)) := completeRows_empty
    rw [hc, hr, probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    rw [probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro table
    rw [probFailure_map, observed_noFail, mul_zero]
  have h2 := probFailure_bind_eq_add_tsum (lazyRun aux q P (initial : State Coord Cell)) finish
  rw [h1] at h2
  exact (add_eq_zero.mp h2.symm).1

end NoFail
end ClaudeWCT.W9.T3.Security.FamResidual
end
