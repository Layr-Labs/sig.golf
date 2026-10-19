import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamRef
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamRestart1
set_option Elab.async false

/-! # Family restart, step P5c-4: the lower-chain restart, charged to families (r3-lean-seedfam)

Family port of the normalized lower-chain restart of `WotsLeafRestart` (`Normalized.Restart`, `fill_congr` ..
`source_contactAfterStop_charge`, `markerAt_stopL`, `source_markerFirst_at_le`). The restart of the leaf `a.key`
becomes the restart of the family `FamSum.famOf S a.key` (chain coordinates `FamLift.caOf S a`), the per-chain
error `Core.errC` becomes `FamLift.errCF S`, and the stop invariance under `Leaf.Congr` becomes invariance under
`FamGame.FamCongr`. Leaf-independent parts (`Restart.GDr`, `GDr_snd`, `mixLaw_restart`, `restart_real_cost`,
`casD`, `calls_pos_depth`, `count_coupled`, `lt_ite_iff`, `cas_coupled`, `stop_coupled`, `restart_le_R`,
`charge_le_R`, `markerAt_maskAt`, `markerAt_take_exists`) are reused. -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestart2
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF FamData FamOkS)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptS)
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable local instance : Fintype Coordinate := coordinateFintype

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

/-! ### Lower chains, charged to their family -/

section Restart
variable (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
  (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (Restart.maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' →
    ∀ trace, Stop T' trace ↔ Stop T trace)

include ha hgrp in
/-- **Programmed family congruence after the fill** (the family `famOf S a.key`): coefficient vectors with equal
revealed seeds give family-congruent filled tables. -/
theorem fill_congrF (R : Tables (PairedReference.referenceInputs adversary)) (hd1 : 1 ≤ RawPrefix.restDepth a R)
    (p : PDataF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) (RawPrefix.restDepth a R))
    (K K' : Fin (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) → Digest)
    (hK : seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K =
        seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K')
    (e : Digest) :
    FamGame.FamCongr S
      (sourceMessages (Restart.fillTable a (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay)
        (chainCount (FamSum.famOf S a.key).lay) (S.cnt (FamSum.famOf S a.key).lay)
        (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) (FamSum.famOf S a.key) R
        (K, RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K)) e))
      (FamSum.famOf S a.key)
      (Restart.fillTable a (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay)
        (chainCount (FamSum.famOf S a.key).lay) (S.cnt (FamSum.famOf S a.key).lay)
        (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) (FamSum.famOf S a.key) R
        (K, RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K)) e)
      (Restart.fillTable a (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay)
        (chainCount (FamSum.famOf S a.key).lay) (S.cnt (FamSum.famOf S a.key).lay)
        (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) (FamSum.famOf S a.key) R
        (K', RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K')) e) := by
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  apply RawFam.famCongr_normalizeF (referenceInputs_subset adversary) S ha.1.1 hFok.leaf
  refine RawFam.famCongr_progF (referenceInputs_subset adversary) S hFok (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) R hd1 p.1.1 p.1.2 K K' (fun c hc hd => ?_) e
  have h := congrFun hK c
  unfold seedsR at h
  have hc' : c ∈ RawFam.revSetF S (FamSum.famOf S a.key) R := by
    unfold RawFam.revSetF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hc, hd⟩
  simp only [if_pos hc'] at h
  exact h

include ha hgrp hStopL in
theorem GDr_famF : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' →
    Restart.GDr adversary q Stop T' = Restart.GDr adversary q Stop T := by
  intro T T' hC
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have hS : Stop T' = Stop T := funext fun trace => propext (hStopL T T' hC trace)
  unfold Restart.GDr
  rw [hS, FamGame.referenceGame_fam hC hFok.tree hFok.leaf adversary q]

include hgrp C hws hb ha hmask hStopL in
/-- **Contact after the stop: reference ≤ mixture + error** (lower chains, family charge). -/
theorem lower_cas_le_mixF :
    Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a | PairedReference.referenceExperiment adversary q] ≤
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[Restart.genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] + FamLift.errCF S adversary q a := by
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have h := FamRef.ref_le_mixF S q ha (Restart.GDr adversary q Stop) Prod.snd (Restart.GDr_snd q Stop)
    (fun s => Restart.ContactAfterStop Stop s.answers s.trace a) (Restart.casD Stop a)
    (fun R p K K' hK => by
      funext z
      apply propext
      unfold Restart.casD
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨step, hstep, -⟩ := id h3
        have hC := fill_congrF S hgrp ha R (by omega) p K K' hK z.1
        exact ⟨(hStopL _ _ hC _).mpr h1,
          fun h => h2 ((FamRestartN.contactAt_famCongr hC hFok.leaf hFok.tree _ ha).mp h), h3⟩
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨step, hstep, -⟩ := id h3
        have hC := fill_congrF S hgrp ha R (by omega) p K K' hK z.1
        exact ⟨(hStopL _ _ hC _).mp h1,
          fun h => h2 ((FamRestartN.contactAt_famCongr hC hFok.leaf hFok.tree _ ha).mpr h), h3⟩)
    (fun R z h => by obtain ⟨-, -, step, -⟩ := h; exact step.elim0)
    (GDr_famF S hgrp q ha Stop hStopL)
    (fun R x res hres => Restart.cas_coupled q a ha Stop hmask R x res hres) hgrp C hws hb
  simp only [Restart.mixLaw_restart] at h
  exact h

include hgrp C hws hb ha hmask hStopL in
/-- **The stop: mixture ≤ reference + error** (lower chains, family charge). -/
theorem lower_mix_le_stopF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
  have h := FamRef.mix_le_refF S q ha (Restart.GDr adversary q Stop) Prod.snd (Restart.GDr_snd q Stop)
    (fun s => (∃ k, Stop s.answers (s.trace.take k)) ∧ 1 ≤ Restart.depth s.answers a)
    (fun d R z => 1 ≤ d ∧ Stop (Restart.fillTable a R z.1) z.2.1.1)
    (fun R p K K' hK => by
      funext z
      apply propext
      constructor
      · rintro ⟨hd, h1⟩
        exact ⟨hd, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mpr h1⟩
      · rintro ⟨hd, h1⟩
        exact ⟨hd, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mp h1⟩)
    (fun R z h => by omega)
    (GDr_famF S hgrp q ha Stop hStopL)
    (fun R x res hres => by
      have hdep : Restart.depth (answers (referenceInputs_subset adversary)
          (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) a = RawPrefix.restDepth a R := by
        unfold Restart.depth
        rw [depth_eq (referenceInputs_subset adversary) _ a ha.1, ← RawPrefix.restDepth_eq, RawPrefix.restDepth_ov]
      have hs := Restart.stop_coupled q a ha Stop hmask R x res hres
      show ((∃ k, Stop _ _) ∧ 1 ≤ Restart.depth (answers (referenceInputs_subset adversary)
        (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) a) ↔ _
      rw [hdep]
      exact ⟨fun h => ⟨h.2, hs.mp h.1⟩, fun h => ⟨hs.mpr h.2, h.1⟩⟩) hgrp C hws hb
  simp only [Restart.mixLaw_restart] at h
  exact h.trans (add_le_add (probEvent_mono'' fun s hs => hs.1) le_rfl)

include hgrp C hws hb ha hmask hStopL in
/-- **Lower chains: contact after the stop, against the stop** (family charge). -/
theorem lower_contactAfterStop_leF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) |
          PairedReference.referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a := by
  have hper : ∀ R : Tables (PairedReference.referenceInputs adversary),
      (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    intro R
    by_cases hd : 1 ≤ RawPrefix.restDepth a R
    · have he : (fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r) = Restart.genStop Stop a R :=
        funext fun r => propext ⟨And.right, fun h => ⟨hd, h⟩⟩
      rw [he]
      exact Restart.restart_le_R q hq a ha.1 Stop R
    · have h0 : Pr[Restart.genCAS Stop a R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (Restart.restartGame adversary q a Stop R) (fun _ _ => none)] = 0 := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_eq_zero.mpr fun r => if_neg fun h => hd ?_
        obtain ⟨step, hstep, -⟩ := h.2.2
        omega
      rw [h0, mul_zero, mul_zero]
      exact bot_le
  have hx : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q])
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          (∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)] + FamLift.errCF S adversary q a)) := by
        gcongr
        exact lower_cas_le_mixF S hgrp C hws hb q ha Stop hmask hStopL
    _ = ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ((1 - (q : ENNReal) / 2 ^ 128) *
          ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)])) +
          (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        rw [mul_add, mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * (((2 * q : ℕ) : ENNReal) *
          Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)]) + 1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) :=
        add_le_add (ENNReal.tsum_le_tsum fun R => mul_le_mul' le_rfl (hper R)) (mul_le_mul' hx le_rfl)
    _ = ((2 * q : ℕ) : ENNReal) * ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => 1 ≤ RawPrefix.restDepth a R ∧ Restart.genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)] + (2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a := by
        rw [one_mul, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ((2 * q : ℕ) : ENNReal) * (Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) |
          PairedReference.referenceExperiment adversary q] +
          FamLift.errCF S adversary q a) + (2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a := by
        gcongr
        exact lower_mix_le_stopF S hgrp C hws hb q ha Stop hmask hStopL
    _ = _ := by ring

/-! ### The charge, by layers -/

include hgrp C hws hb ha hmask hStopL in
theorem lower_mix_layer_leF (k : ℕ) :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
          PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
  have h := FamRef.mix_le_refF S q ha (Restart.GDr adversary q Stop) Prod.snd (Restart.GDr_snd q Stop)
    (fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k'))
    (fun d R z => k < 2 * calls (PrefixGame.PrefixQuery a d) z.2.1.2.2 ∧
      Stop (Restart.fillTable a R z.1) z.2.1.1)
    (fun R p K K' hK => by
      funext z
      apply propext
      constructor
      · rintro ⟨hk, h1⟩
        have hd := Restart.calls_pos_depth (a := a)
          (by omega : 0 < calls (PrefixGame.PrefixQuery a (RawPrefix.restDepth a R)) z.2.1.2.2)
        exact ⟨hk, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mpr h1⟩
      · rintro ⟨hk, h1⟩
        have hd := Restart.calls_pos_depth (a := a)
          (by omega : 0 < calls (PrefixGame.PrefixQuery a (RawPrefix.restDepth a R)) z.2.1.2.2)
        exact ⟨hk, (hStopL _ _ (fill_congrF S hgrp ha R hd p K K' hK z.1) _).mp h1⟩)
    (fun R z h => by
      have := h.1
      rw [calls_prefixQuery_zero] at this
      omega)
    (GDr_famF S hgrp q ha Stop hStopL)
    (fun R x res hres => by
      have hc := Restart.count_coupled q ha Stop R x res hres
      have hs := Restart.stop_coupled q a ha Stop hmask R x res hres
      show (k < 2 * prefixCount a (mkSample (answers (referenceInputs_subset adversary)
        (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2) ∧ _) ↔ _
      rw [hc]
      exact and_congr Iff.rfl hs) hgrp C hws hb
  simp only [Restart.mixLaw_restart] at h
  exact h

include hgrp C hws hb ha hmask hStopL in
/-- **The charge: mixture ≤ reference + 2q · error** (lower chains, family charge). -/
theorem lower_mix_charge_leF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none) r * Restart.genCharge Stop a R r ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 * q : ℕ) : ENNReal) * FamLift.errCF S adversary q a := by
  have hmix : ∀ R : Tables (PairedReference.referenceInputs adversary), ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
        (fun _ _ => none) r * Restart.genCharge Stop a R r =
      ∑ k ∈ Finset.range (2 * q), Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    intro R
    have h := expectation_layers (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (Restart.restartGame adversary q a Stop R) (fun _ _ => none))
      (fun r => if Restart.genStop Stop a R r then 2 * seedCost a R r.2.1.2 else 0) (2 * q) (fun r hr => by
        have := Restart.restart_real_cost q a Stop R r hr
        split_ifs <;> omega)
    simp only [Restart.lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun r => ?_
    unfold Restart.genCharge
    congr 1
    show _ = (((if Restart.stopAt Stop a R r.1 r.2.1.1 then 2 * seedCost a R r.2.1.2 else 0 : ℕ)) : ENNReal)
    split_ifs <;> simp
  have href : ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) =
      ∑ k ∈ Finset.range (2 * q), Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
        PairedReference.referenceExperiment adversary q] := by
    have h := expectation_layers (PairedReference.referenceExperiment adversary q)
      (fun s => if ∃ k, Stop s.answers (s.trace.take k) then 2 * prefixCount a s else 0) (2 * q) (fun s hs => by
        have := (LeafView.prefixCount_le_length a s).trans (Core.ref_trace_length_le adversary q s hs)
        split_ifs <;> omega)
    simp only [Restart.lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun s => ?_
    congr 1
    split_ifs <;> simp
  simp only [hmix, href]
  calc ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑ k ∈ Finset.range (2 * q),
        Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)]
      = ∑ k ∈ Finset.range (2 * q), ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ Restart.genStop Stop a R r |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
              (Restart.restartGame adversary q a Stop R) (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range (2 * q),
          (Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
            PairedReference.referenceExperiment adversary q] + FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun k _ => lower_mix_layer_leF S hgrp C hws hb q ha Stop hmask hStopL k
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

include hgrp C hws hb ha hmask hStopL in
/-- **Lower chains: contact after the stop, against the prefix charge** (family charge). -/
theorem lower_contactAfterStop_chargeF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a := by
  have hx : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q])
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          (∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)] + FamLift.errCF S adversary q a)) := by
        gcongr
        exact lower_cas_le_mixF S hgrp C hws hb q ha Stop hmask hStopL
    _ = ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ((1 - (q : ENNReal) / 2 ^ 128) *
          ((2 ^ 128 : ENNReal) * Pr[Restart.genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none)])) +
          (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        rw [mul_add, mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (Restart.restartGame adversary q a Stop R)
            (fun _ _ => none) r * Restart.genCharge Stop a R r +
          1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) :=
        add_le_add (ENNReal.tsum_le_tsum fun R => mul_le_mul' le_rfl (Restart.charge_le_R q hq a ha.1 Stop R))
          (mul_le_mul' hx le_rfl)
    _ ≤ (∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
          (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
          ((2 * q : ℕ) : ENNReal) * FamLift.errCF S adversary q a) +
          1 * ((2 ^ 128 : ENNReal) * FamLift.errCF S adversary q a) := by
        gcongr
        exact lower_mix_charge_leF S hgrp C hws hb q ha Stop hmask hStopL
    _ = _ := by ring
end Restart

/-! ### All source chains -/

section Source
variable (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
  (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (Restart.maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' →
    ∀ trace, Stop T' trace ↔ Stop T trace)
include hgrp C hws hb ha hmask hStopL

/-- **Source chains: contact after the stop, against the stop** (family charge). -/
theorem source_contactAfterStop_leF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) |
          PairedReference.referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a :=
  lower_contactAfterStop_leF S hgrp C hws hb q ha Stop hmask hStopL hq

/-- **Source chains: contact after the stop, against the prefix charge** (family charge). -/
theorem source_contactAfterStop_chargeF (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop Stop s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a :=
  lower_contactAfterStop_chargeF S hgrp C hws hb q ha Stop hmask hStopL hq
end Source

/-! ### Markers -/

/-- Markers are invariant under the family congruence of a source chain's family. -/
theorem markerAt_stopLF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {a : ChainAddr}
    (ha : WotsExtract.SourceChain7 a) :
    ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' → ∀ trace,
      Restart.MarkerAt T' trace a ↔ Restart.MarkerAt T trace a :=
  fun _ _ hC trace => FamRestartN.markerAt_famCongr hC (FamLift.famOk_of_source S hgrp ha.1).leaf trace a

/-- **Markers first, per source chain** (family charge). -/
theorem source_markerFirst_at_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
          s.answers s.trace a | PairedReference.referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => Restart.MarkerAt s.answers s.trace a |
          PairedReference.referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a := by
  have h := source_contactAfterStop_leF (adversary := adversary) S hgrp C hws hb q ha
    (fun T trace => Restart.MarkerAt T trace a)
    (fun T trace => Restart.markerAt_maskAt T trace a (Restart.source_bounds ha).2)
    (markerAt_stopLF S hgrp ha) hq
  simpa only [Restart.markerAt_take_exists] using h

#print axioms fill_congrF
#print axioms GDr_famF
#print axioms source_contactAfterStop_leF
#print axioms source_contactAfterStop_chargeF
#print axioms source_markerFirst_at_leF
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestart2
