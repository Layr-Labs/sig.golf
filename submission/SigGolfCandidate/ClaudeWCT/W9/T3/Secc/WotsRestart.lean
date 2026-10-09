import SigGolfCandidate.T3.Secc.WotsRestart
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsRestartBase

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount realCheckpointRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem reference_map_eq_mixture_of (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (hl : a.key.lay = 0)
    {Res β : Type}
    (game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) Res)
    (out : Res → SeedResult) (hgame : ∀ R endpoint, out <$> game R endpoint = seedGame adversary q a R endpoint)
    (f : RefSample → β)
    (g : (R : RefTables adversary) → Digest × (Res × (Fin (restDepth a R) → Digest → Option Digest)) → β)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : Res × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1 (game R (evaluate x.1 x.2))
        (fun _ _ => none)).support →
      f (mkSample (restTable (ov a (restDepth a R) R x)) (out res.1)) = g R (evaluate x.1 x.2, res)) :
    (referenceExperiment adversary q).map f =
      (restLaw adversary).bind (fun R =>
        (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)).map (g R)) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
    omega
  rw [reference_eq_bind, PMF.map_bind, restLaw_resample adversary a]
  apply congrArg (restLaw adversary).bind
  funext R
  rw [uniform_prod, PMF.bind_bind]
  simp only [PMF.bind_map]
  simp only [realRun, SphincsSecurity.Concrete.PartialChainEndpoint.completeTables_empty,
    SphincsSecurity.Concrete.EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype (Fin (restDepth a R) → Digest → Digest)).bind
  funext t
  apply congrArg (PMF.uniformOfFintype Digest).bind
  funext s
  have hfix := fixed_seedGame (adversary := adversary) q a htree hleaf R (t, s)
  dsimp only at hfix
  rw [ovSeed_top hl] at hfix
  rw [← hgame, simulateQ_map, PMF.monad_map_eq_map] at hfix
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp, PMF.map_comp]
  exact map_congr_support _ _ _ fun res hres => hfg R (t, s) res hres
theorem reference_prob_eq_of (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (hl : a.key.lay = 0)
    {Res : Type}
    (game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) Res)
    (out : Res → SeedResult) (hgame : ∀ R endpoint, out <$> game R endpoint = seedGame adversary q a R endpoint)
    (E : RefSample → Prop)
    (F : (R : RefTables adversary) → Digest × (Res × (Fin (restDepth a R) → Digest → Option Digest)) → Prop)
    (hEF : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : Res × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1 (game R (evaluate x.1 x.2))
        (fun _ _ => none)).support →
      (E (mkSample (restTable (ov a (restDepth a R) R x)) (out res.1)) ↔ F R (evaluate x.1 x.2, res))) :
    Pr[E | referenceExperiment adversary q] =
      ∑' R, restLaw adversary R * Pr[F R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF Prop => Pr[fun p => p | law])
    (reference_map_eq_mixture_of q a ha hl game out hgame E F (fun R x res hres => propext (hEF R x res hres)))
  simp only [← PMF.monad_map_eq_map, probEvent_map, ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    PMF.probOutput_eq_apply, Function.comp_def] at h
  exact h
theorem reference_expectation_eq_of (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (hl : a.key.lay = 0)
    {Res : Type}
    (game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) Res)
    (out : Res → SeedResult) (hgame : ∀ R endpoint, out <$> game R endpoint = seedGame adversary q a R endpoint)
    (f : RefSample → ENNReal)
    (g : (R : RefTables adversary) → Digest × (Res × (Fin (restDepth a R) → Digest → Option Digest)) → ENNReal)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : Res × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1 (game R (evaluate x.1 x.2))
        (fun _ _ => none)).support →
      f (mkSample (restTable (ov a (restDepth a R) R x)) (out res.1)) = g R (evaluate x.1 x.2, res)) :
    ∑' s, referenceExperiment adversary q s * f s =
      ∑' R, restLaw adversary R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none) r * g R r := by
  have h := congrArg (fun law : PMF ENNReal => ∑' v, law v * v)
    (reference_map_eq_mixture_of q a ha hl game out hgame f g hfg)
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind] at h
  exact h
theorem fixed_pausedSeed (q : Nat) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 24)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) (stop : List Entry → Prop) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
        (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) =
      (liftM (simulateQ (refImpl (restTable (ov a (restDepth a R) R x)))
        (pausedFull stop (referenceGame (restTable (ov a (restDepth a R) R x)) adversary q) [])) :
          PMF (List Entry × SeedResult)) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  unfold pausedSeed
  rw [← QueryImpl.simulateQ_compose, fixed_route a hd R x, ← referenceGame_fill a htree hleaf R x q,
    QueryImpl.simulateQ_compose]
  rfl
theorem coupled_paused (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (R : RefTables adversary)
    (x : Hidden (restDepth a R)) (stop : List Entry → Prop)
    (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support) :
    res.1.1 = (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take res.1.1.length ∧
      (∀ j, j < res.1.1.length → ¬stop ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take j)) ∧
      (stop res.1.1 ∨ res.1.1 = traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 24 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
    omega
  have hfst : res.1 ∈ (simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2)))).support := by
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
      PMF.mem_support_map_iff]
    exact ⟨res, hres, rfl⟩
  rw [fixed_pausedSeed q a htree hleaf R x stop] at hfst
  have hmem := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hfst
  obtain ⟨-, h2, h3, h4⟩ := paused_structure _ stop _ [] res.1 hmem
  simp only [List.nil_append, List.length_nil, Nat.zero_le, true_implies] at h2 h3 h4
  exact ⟨h2, h3, h4⟩
theorem coupled_paused_rows (q : Nat) (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support) :
    (res.1.2, res.2) ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame adversary q a R (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support := by
  rw [← pausedSeed_snd q a R stop, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_map,
    PMF.mem_support_map_iff]
  exact ⟨res, hres, rfl⟩
theorem contactAt_take_mono (T : Answers) (trace : List Entry) (a : ChainAddr) {j k : Nat} (hjk : j ≤ k)
    (h : ContactAt T (trace.take j) a) : ContactAt T (trace.take k) a := by
  obtain ⟨hd, value, answer, hm, hl⟩ := h
  exact ⟨hd, value, answer, (List.take_prefix_take_left hjk).subset hm, hl⟩
theorem contactAt_take_full (T : Answers) (trace : List Entry) (a : ChainAddr) {k : Nat}
    (h : ContactAt T (trace.take k) a) : ContactAt T trace a := by
  obtain ⟨hd, value, answer, hm, hl⟩ := h
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
theorem contactAt_congr {T T' : Answers} (trace : List Entry) (a : ChainAddr) (hd : depth T a = depth T' a)
    (hf : frontierValue T a = frontierValue T' a) : ContactAt T trace a ↔ ContactAt T' trace a := by
  unfold ContactAt
  rw [hd, hf]
theorem fillTable_depth (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) :
    depth (fillTable a R endpoint) a = restDepth a R :=
  (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)
theorem fillTable_frontier (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest)
    (hd : 1 ≤ restDepth a R) : frontierValue (fillTable a R endpoint) a = endpoint := by
  unfold fillTable
  rw [frontierValue_ov]
  obtain ⟨d', hd'⟩ : ∃ d', restDepth a R = d' + 1 := ⟨restDepth a R - 1, by omega⟩
  generalize ovSeed a R endpoint = s0
  revert s0
  rw [hd']
  intro s0
  exact evaluate_const_succ d' endpoint s0
theorem contact_iff_rowsInv (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) (memory : List Entry)
    (observed : Fin (restDepth a R) → Digest → Option Digest) (hinv : RowsInv a memory observed) :
    Contact observed endpoint ↔ ContactAt (fillTable a R endpoint) memory a := by
  by_cases hd0 : restDepth a R = 0
  · unfold Contact ContactAt
    rw [fillTable_depth]
    constructor
    · rintro ⟨i, -, -⟩
      exact absurd i.isLt (by omega)
    · rintro ⟨h, -⟩
      omega
  unfold Contact ContactAt SeenRow
  rw [fillTable_depth, fillTable_frontier a R endpoint (by omega)]
  constructor
  · rintro ⟨i, hi, value, h⟩
    obtain ⟨answer, hm, hl⟩ := (hinv i value endpoint).mp h
    refine ⟨by omega, value, answer, ?_, hl⟩
    rw [show restDepth a R - 1 = i.val by omega]
    exact hm
  · rintro ⟨hd, value, answer, hm, hl⟩
    refine ⟨⟨restDepth a R - 1, by omega⟩, by simp only; omega, value, (hinv _ value endpoint).mpr ⟨answer, hm, hl⟩⟩
end PrefixGame
open PrefixGame in
def ContactAfterStop (Stop : Answers → List Entry → Prop) (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, Stop T (trace.take k) ∧ ¬ContactAt T (trace.take k) a ∧ ContactAt T trace a
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem coupled_contact (q : Nat) (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support) :
    ContactAt (restTable (ov a (restDepth a R) R x)) (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) a ↔
      Contact res.2 (evaluate x.1 (ovSeed a R x.2)) := by
  have hview := sampleView_coupled adversary q a R x (res.1.2, res.2) (coupled_paused_rows q a R x stop res hres)
  have h1 := contactAt_iff_view a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) res.1.2.2 rfl
  rw [hview, runView_contact] at h1
  exact h1
end PrefixGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
/-- The stop predicate on the honest table of chain `a`'s prefix game. -/
def stopAt (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary) (e : Digest)
    (trace : List Entry) : Prop := Stop (fillTable a R e) trace
/-- The paused prefix game. -/
noncomputable def restartGame (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : RefTables adversary) (e : Digest) : OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
  pausedSeed adversary q a R (stopAt Stop a R e) e
def genCAS (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))) : Prop :=
  stopAt Stop a R r.1 r.2.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1 a ∧ Contact r.2.2 r.1
def genStop (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))) : Prop :=
  stopAt Stop a R r.1 r.2.1.1
noncomputable def genCharge (Stop : Answers → List Entry → Prop) (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))) : ENNReal :=
  ((2 * seedCost a R r.2.1.2 : ℕ) : ENNReal) * (if stopAt Stop a R r.1 r.2.1.1 then 1 else 0)
theorem restartGame_snd (q : Nat) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary)
    (e : Digest) : Prod.snd <$> restartGame adversary q a Stop R e = seedGame adversary q a R e :=
  pausedSeed_snd q a R _ e

/-- **Per rest table: contact after the stop, against the stop.** -/
theorem restart_le_R (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : RefTables adversary) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[genStop Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    let aux : Digest → QueryImpl unifSpec PMF := fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl
    let before := fun e => seedBefore adversary q a R (stopAt Stop a R e) e
    let after := fun (_ : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => seedAfter a R middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => stopAt Stop a R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun aux before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun aux (restartGame adversary q a Stop R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project aux before
        (fun _ middle => seedAfter a R middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt Stop a R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support aux before
      after (fun _ _ => none) r hr
    have hc : Pr[genCAS Stop a R | realRun aux (restartGame adversary q a Stop R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun aux before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hs : Pr[fun r => marked r.1 r.2 | realRun aux before (fun _ _ => none)] ≤
        Pr[genStop Stop a R | realRun aux (restartGame adversary q a Stop R) (fun _ _ => none)] := by
      rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_mark_probability aux before after
        (fun _ _ => none) marked, ← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_mono
      intro r _ hm
      exact hm.1
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_le_mark aux before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt Stop a R e) e middle hmiddle result hresult).2)
      (fun r hr _ => (checkpoint_budget q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2).1)
    rw [card_digest] at hkernel
    rw [hc]
    exact hkernel.trans (mul_le_mul' le_rfl hs)

/-- **Per rest table: contact after the stop, against the prefix charge.** -/
theorem charge_le_R (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr) (Stop : Answers → List Entry → Prop)
    (R : RefTables adversary) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) r * genCharge Stop a R r := by
    let before := fun e => seedBefore adversary q a R (stopAt Stop a R e) e
    let after := fun (_ : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => seedAfter a R middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => stopAt Stop a R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
        (fun _ middle => seedAfter a R middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt Stop a R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
      after (fun _ _ => none) r hr
    have hc : Pr[genCAS Stop a R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt Stop a R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_charge (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt Stop a R e) e middle hmiddle result hresult).2)
    rw [card_digest] at hkernel
    rw [hc]
    refine hkernel.trans ?_
    have hexp : (∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) r * genCharge Stop a R r) =
        ∑' r, realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
          (fun _ _ => none) r * genCharge Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) := by
      rw [← hproj, SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
    refine le_of_le_of_eq ?_ hexp.symm
    apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : r ∈ (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).support
    · apply mul_le_mul' le_rfl
      have hch := checkpoint_charge q a R (stopAt Stop a R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2
      by_cases hm : marked r.1 r.2.1
      · rw [if_pos hm, mul_one]
        have hgc : genCharge Stop a R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) =
            ((2 * seedCost a R r.2.2.1.1 : ℕ) : ENNReal) := by
          simp only [genCharge]
          rw [if_pos hm.1, mul_one]
        rw [hgc]
        exact_mod_cast hch
      · rw [if_neg hm, mul_zero]
        exact bot_le
    · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]

/-! ### Couplings with the reference experiment (seed frozen at `ovSeed`) -/

theorem contactAt_ov_fill (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (trace : List Entry) :
    ContactAt (restTable (ov a (restDepth a R) R x)) trace a ↔
      ContactAt (fillTable a R (evaluate x.1 (ovSeed a R x.2))) trace a := by
  have hd : depth (restTable (ov a (restDepth a R) R x)) a = depth (fillTable a R (evaluate x.1 (ovSeed a R x.2))) a := by
    rw [fillTable_depth]; exact (restDepth_eq a _).symm.trans (restDepth_ov a R x)
  by_cases hd0 : restDepth a R = 0
  · unfold ContactAt
    rw [hd, fillTable_depth]
    exact ⟨fun h => absurd h.1 (by omega), fun h => absurd h.1 (by omega)⟩
  · apply contactAt_congr trace a hd
    rw [fillTable_frontier a R _ (by omega), frontierValue_ov]

section Couple
variable (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (Stop : Answers → List Entry → Prop)
  (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace) (R : RefTables adversary)
  (x : Hidden (restDepth a R))
  (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
  (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
    (restartGame adversary q a Stop R (evaluate x.1 (ovSeed a R x.2))) (fun _ _ => none)).support)
include hmask in
theorem blind_frozen (trace : List Entry) :
    Stop (restTable (ov a (restDepth a R) R x)) trace ↔ stopAt Stop a R (evaluate x.1 (ovSeed a R x.2)) trace := by
  show _ ↔ Stop (fillTable a R (evaluate x.1 (ovSeed a R x.2))) trace
  rw [← hmask, maskAt_ov_fill, hmask]
include ha hmask hres
theorem cas_coupled :
    ContactAfterStop Stop (restTable (ov a (restDepth a R) R x))
        (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) a ↔
      genCAS Stop a R (evaluate x.1 (ovSeed a R x.2), res) := by
  obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres
  have hc := coupled_contact q a R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres
  unfold ContactAfterStop genCAS
  simp only [blind_frozen a Stop hmask R x, contactAt_ov_fill a R x]
  rw [first_stop_iff (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2)))
    (fun trace => ContactAt (fillTable a R (evaluate x.1 (ovSeed a R x.2))) trace a)
    h1 h2 h3 (fun j k hjk h => contactAt_take_mono _ _ a hjk h)]
  rw [← contactAt_ov_fill a R x (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2), hc]
theorem stop_coupled :
    (∃ k, Stop (restTable (ov a (restDepth a R) R x))
        ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take k)) ↔
      genStop Stop a R (evaluate x.1 (ovSeed a R x.2), res) := by
  obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres
  simp only [blind_frozen a Stop hmask R x]
  exact first_stop_exists_iff _ h1 h2 h3
theorem charge_coupled :
    ((2 * prefixCount a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) : ℕ) : ENNReal) *
        (if ∃ k, Stop (restTable (ov a (restDepth a R) R x))
          ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take k) then 1 else 0) =
      genCharge Stop a R (evaluate x.1 (ovSeed a R x.2), res) := by
  have hview := sampleView_coupled adversary q a R x (res.1.2, res.2)
    (coupled_paused_rows q a R x (stopAt Stop a R (evaluate x.1 (ovSeed a R x.2))) res hres)
  have hcount : prefixCount a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 :=
    congrArg PrefixView.count hview
  have hstop := stop_coupled q a ha Stop hmask R x res hres
  unfold genCharge
  rw [hcount]
  by_cases hs : stopAt Stop a R (evaluate x.1 (ovSeed a R x.2)) res.1.1
  · rw [if_pos (hstop.mpr hs), if_pos hs]
  · rw [if_neg (fun h => hs (hstop.mp h)), if_neg hs]
end Couple
end PrefixGame

open PrefixGame in
/-- Top chains: contact after the stop, against the stop. -/
theorem reference_contactAfterStop_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) (hl : a.key.lay = 0) (Stop : Answers → List Entry → Prop)
    (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | referenceExperiment adversary q] := by
  have hCAS := reference_prob_eq_of q a ha hl (restartGame adversary q a Stop) Prod.snd
    (fun R e => restartGame_snd q a Stop R e) (fun s => ContactAfterStop Stop s.answers s.trace a) (genCAS Stop a)
    (fun R x res hres => by
      have h := cas_coupled q a ha Stop hmask R x res (by rw [ovSeed_top hl]; exact hres)
      rw [ovSeed_top hl] at h; exact h)
  have hSTOP := reference_prob_eq_of q a ha hl (restartGame adversary q a Stop) Prod.snd
    (fun R e => restartGame_snd q a Stop R e) (fun s => ∃ k, Stop s.answers (s.trace.take k)) (genStop Stop a)
    (fun R x res hres => by
      have h := stop_coupled q a ha Stop hmask R x res (by rw [ovSeed_top hl]; exact hres)
      rw [ovSeed_top hl] at h; exact h)
  rw [hCAS, hSTOP, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro R
  calc (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * (restLaw adversary R * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]))
      = restLaw adversary R * ((1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)])) := by ring
    _ ≤ restLaw adversary R * (((2 * q : ℕ) : ENNReal) * Pr[genStop Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) := mul_le_mul' le_rfl (restart_le_R q hq a Stop R)
    _ = ((2 * q : ℕ) : ENNReal) * (restLaw adversary R * Pr[genStop Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) := by ring
theorem markerAt_maskAt (T : Answers) (trace : List Entry) (a : ChainAddr) (hal : Mask.MaskOK a) :
    MarkerAt (maskAt T a) trace a ↔ MarkerAt T trace a := by
  unfold MarkerAt
  rw [referenceInput_maskAt _ _ hal, referenceDigits_maskAt _ _ hal]
theorem markerAt_take_exists (T : Answers) (trace : List Entry) (a : ChainAddr) :
    (∃ k, MarkerAt T (trace.take k) a) ↔ MarkerAt T trace a := by
  constructor
  · rintro ⟨k, message, counter, pad, answer, digits, hfit, hm, h⟩
    exact ⟨message, counter, pad, answer, digits, hfit, List.mem_of_mem_take hm, h⟩
  · intro h
    exact ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem sourceChain_maskOK (a : ChainAddr) (ha : WotsExtract.SourceChain a) : Mask.MaskOK a :=
  Mask.maskOK_of_lt (by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
    omega)
/-- Top chains: contact after the marker, against the marker. -/
theorem reference_markerFirst_at_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) (hl : a.key.lay = 0) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace a) s.answers s.trace a |
          referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => MarkerAt s.answers s.trace a | referenceExperiment adversary q] := by
  have h := reference_contactAfterStop_le adversary q hq a ha hl (fun T trace => MarkerAt T trace a)
    (fun T trace => markerAt_maskAt T trace a (sourceChain_maskOK a ha))
  simpa only [markerAt_take_exists] using h
open PrefixGame in
/-- Top chains: contact after the stop, against the prefix charge. -/
theorem reference_contactAfterStop_charge (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) (hl : a.key.lay = 0) (Stop : Answers → List Entry → Prop)
    (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ∑' s, referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) := by
  have hCAS := reference_prob_eq_of q a ha hl (restartGame adversary q a Stop) Prod.snd
    (fun R e => restartGame_snd q a Stop R e) (fun s => ContactAfterStop Stop s.answers s.trace a) (genCAS Stop a)
    (fun R x res hres => by
      have h := cas_coupled q a ha Stop hmask R x res (by rw [ovSeed_top hl]; exact hres)
      rw [ovSeed_top hl] at h; exact h)
  have hCHARGE := reference_expectation_eq_of q a ha hl (restartGame adversary q a Stop) Prod.snd
    (fun R e => restartGame_snd q a Stop R e)
    (fun s => ((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0))
    (genCharge Stop a) (fun R x res hres => by
      have h := charge_coupled q a ha Stop hmask R x res (by rw [ovSeed_top hl]; exact hres)
      rw [ovSeed_top hl] at h; exact h)
  rw [hCAS, hCHARGE, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro R
  calc (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * (restLaw adversary R * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]))
      = restLaw adversary R * ((1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)])) := by ring
    _ ≤ restLaw adversary R * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (restartGame adversary q a Stop R) (fun _ _ => none) r * genCharge Stop a R r :=
        mul_le_mul' le_rfl (charge_le_R q hq a Stop R)
end ClaudeWCT.W9.T3.Security.Wots
