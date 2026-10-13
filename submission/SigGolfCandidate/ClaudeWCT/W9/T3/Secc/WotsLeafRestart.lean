import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsRestart

/-! # Restart bounds for lower source chains (campaign X1 stage B, step B3)

`WotsRestart` bounds a first contact after a stop for top source chains, whose seeds are uniform. For lower source
chains (seeds = degree-16 family evaluations) the same bounds hold up to the seed-test error `(2^128 + 2q) · errC a`
(`lower_contactAfterStop_le`, `lower_contactAfterStop_charge`), for stops that are invariant under the leaf
congruence of the chain's leaf (contacts of source chains and markers are, `contactAt_leafCongr`,
`markerAt_leafCongr`). The combined statements for all source chains are `source_contactAfterStop_le` and
`source_contactAfterStop_charge`. -/

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsLeafRestart : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
open SphincsSecurity.QueryCap (recorded counted calls)
open ClaudeWCT.Arith.SideChannel (seedsR)
open ClaudeWCT.W9.T3.Security.Wots.PrefixGame (restartGame genCAS genStop genCharge stopAt restart_le_R
  charge_le_R cas_coupled stop_coupled restartGame_snd)
variable {adversary : AdversaryP}

theorem source_bounds {b : ChainAddr} (hb : WotsExtract.SourceChain b) :
    b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24 := by
  refine ⟨by have := hb.1.1; omega, ?_⟩
  have h1 := hb.1.2
  have h2 : 2 ^ height b.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
    have := SigGolfCandidate.T3.Security.Wots.height_le b.key.lay; omega)
  omega

/-! ### Contacts and markers under leaf congruence -/

section Congr
variable {L : LeafAddr} {T T' : Answers} (hC : LeafCongr L T T') (hLleaf : L.leaf < 2 ^ 24)
  (hLtree : L.tree < 2 ^ 40)
include hC hLleaf

theorem frontierValue_leafCongr {b : ChainAddr} (hb : WotsExtract.SourceChain b) (hLtree : L.tree < 2 ^ 40) :
    frontierValue T' b = frontierValue T b := by
  obtain ⟨hbt, hbl⟩ := source_bounds hb
  by_cases hal : LeafAlias b.key.lay b.key.tree b.key.leaf L
  · have hk : b.key = L := by
      have := hal.eq_of_lt hbt (by omega) hLtree (by omega)
      cases hbk : b.key
      rw [hbk] at this
      exact this
    have hbc := hb.2
    cases b with
    | mk K c =>
      simp only at hk hbc
      subst hk
      exact hC.front c hbc
  · unfold frontierValue honestChainValue
    rw [depth_congr hC hLleaf b, wotsSeed_out hC.toLeafAgree hLleaf hbl hal]
    exact eval_chain_out hC.toLeafAgree (by have := Mask.chainCount_le b.key.lay; have := hb.2; omega)
      (fun h => hal h.1) (by have := Mask.depth_le_seven T b; omega) _

theorem contactAt_leafCongr (hLtree : L.tree < 2 ^ 40) (trace : List Entry) {b : ChainAddr}
    (hb : WotsExtract.SourceChain b) : ContactAt T' trace b ↔ ContactAt T trace b := by
  unfold ContactAt
  rw [depth_congr hC hLleaf b, frontierValue_leafCongr hC hLleaf hb hLtree]

theorem markerAt_leafCongr (trace : List Entry) (b : ChainAddr) : MarkerAt T' trace b ↔ MarkerAt T trace b := by
  unfold MarkerAt referenceInput
  rw [referenceSearch_congr hC hLleaf, leafMsg_congr hC hLleaf, referenceDigits_congr hC hLleaf]
end Congr

/-! ### The paused reference game as an honest body -/

/-- The paused reference game of a table (the honest body of `restartGame`). -/
noncomputable def GDr (adversary : AdversaryP) (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    OracleComp RefWorld (List Entry × SeedResult) :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull (Stop T) (referenceGame T adversary q) []

theorem GDr_snd (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    Prod.snd <$> GDr adversary q Stop T = GDseed adversary q T :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull_snd _ _ _

theorem gameD_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary) :
    gameD a (restDepth a R) R (GDr adversary q Stop) = restartGame adversary q a Stop R := by
  funext e
  rfl

theorem mixLaw_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary) :
    mixLaw a (restDepth a R) R (GDr adversary q Stop) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) := by
  unfold mixLaw
  rw [gameD_restart]

theorem restart_real_cost (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : RefTables adversary)
    (r : Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest)))
    (hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
      (fun _ _ => none)).support) : seedCost a R r.2.1.2 ≤ q := by
  have h := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_map
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
    (fun _ => Prod.snd) (fun _ _ => none)
  simp only [restartGame_snd] at h
  have hm : (r.1, r.2.1.2, r.2.2) ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (seedGame adversary q a R) (fun _ _ => none)).support := by
    rw [h, PMF.mem_support_map_iff]
    exact ⟨r, hr, rfl⟩
  exact seedGame_real_cost adversary q a R _ hm

/-! ### Lower chains -/

section Restart
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', LeafCongr a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)

include ha in
theorem fill_congr (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R) (p : PData a.key (restDepth a R))
    (K K' : Fin (WCT9.famCount a.key.lay) → Digest)
    (hK : seedsR (ptL a.key) (revSet a.key R) K = seedsR (ptL a.key) (revSet a.key R) K') (e : Digest) :
    LeafCongr a.key (PrefixGame.fillTable a (ovL a.key R (K, progF p.1.1 p.1.2 K)) e)
      (PrefixGame.fillTable a (ovL a.key R (K', progF p.1.1 p.1.2 K')) e) := by
  refine leafCongr_prog (source_bounds ha).2 rfl ha.2 R hd1 p.1.1 p.1.2 K K' (fun c hc => ?_) e
  have h := congrFun hK c
  unfold seedsR at h
  have hc' : c ∈ revSet a.key R := by
    unfold revSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc
  simp only [if_pos hc'] at h
  exact h

include ha hStopL in
theorem GDr_leaf : ∀ T T', LeafCongr a.key T T' → GDr adversary q Stop T' = GDr adversary q Stop T := by
  intro T T' hC
  have hS : Stop T' = Stop T := funext fun trace => propext (hStopL T T' hC trace)
  unfold GDr
  rw [hS, referenceGame_leaf hC (source_bounds ha).2 (source_bounds ha).1 adversary q]

/-- The stop-then-contact event of the prefix-game run at depth `d`. -/
def casD (Stop : Answers → List Entry → Prop) (a : ChainAddr) (d : ℕ) (R : RefTables adversary)
    (z : Digest × ((List Entry × SeedResult) × TObs d)) : Prop :=
  Stop (PrefixGame.fillTable a R z.1) z.2.1.1 ∧ ¬ContactAt (PrefixGame.fillTable a R z.1) z.2.1.1 a ∧
    Contact z.2.2 z.1

include ha hmask hStopL in
/-- **Contact after the stop: reference ≤ mixture + error** (lower chains). -/
theorem lower_cas_le_mix :
    Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q] ≤
      ∑' R, restLaw adversary R * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] + errC adversary q a := by
  have h := ref_le_mix q ha (GDr adversary q Stop) Prod.snd (GDr_snd q Stop)
    (fun s => ContactAfterStop Stop s.answers s.trace a) (casD Stop a)
    (fun R p K K' hK => by
      funext z
      apply propext
      have key : Contact z.2.2 z.1 →
          (Stop (PrefixGame.fillTable a (ovL a.key R (K, progF p.1.1 p.1.2 K)) z.1) z.2.1.1 ↔
            Stop (PrefixGame.fillTable a (ovL a.key R (K', progF p.1.1 p.1.2 K')) z.1) z.2.1.1) ∧
          (ContactAt (PrefixGame.fillTable a (ovL a.key R (K, progF p.1.1 p.1.2 K)) z.1) z.2.1.1 a ↔
            ContactAt (PrefixGame.fillTable a (ovL a.key R (K', progF p.1.1 p.1.2 K')) z.1) z.2.1.1 a) := by
        intro hc
        obtain ⟨step, hstep, -⟩ := hc
        have hC := fill_congr ha R (by omega) p K K' hK z.1
        exact ⟨(hStopL _ _ hC _).symm,
          (contactAt_leafCongr hC (source_bounds ha).2 (source_bounds ha).1 _ ha).symm⟩
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨k1, k2⟩ := key h3
        exact ⟨k1.mp h1, fun h => h2 (k2.mpr h), h3⟩
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨k1, k2⟩ := key h3
        exact ⟨k1.mpr h1, fun h => h2 (k2.mp h), h3⟩)
    (fun R z h => by obtain ⟨-, -, step, -⟩ := h; exact step.elim0)
    (GDr_leaf q ha Stop hStopL)
    (fun R x res hres => cas_coupled q a ha Stop hmask R x res hres)
  simp only [mixLaw_restart] at h
  exact h

include ha hmask hStopL in
/-- **The stop: mixture ≤ reference + error** (lower chains). -/
theorem lower_mix_le_stop :
    ∑' R, restLaw adversary R * Pr[fun r => 1 ≤ restDepth a R ∧ genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | referenceExperiment adversary q] + errC adversary q a := by
  have h := mix_le_ref q ha (GDr adversary q Stop) Prod.snd (GDr_snd q Stop)
    (fun s => (∃ k, Stop s.answers (s.trace.take k)) ∧ 1 ≤ depth s.answers a)
    (fun d R z => 1 ≤ d ∧ Stop (PrefixGame.fillTable a R z.1) z.2.1.1)
    (fun R p K K' hK => by
      funext z
      apply propext
      constructor
      · rintro ⟨hd, h1⟩
        exact ⟨hd, (hStopL _ _ (fill_congr ha R hd p K K' hK z.1) _).mpr h1⟩
      · rintro ⟨hd, h1⟩
        exact ⟨hd, (hStopL _ _ (fill_congr ha R hd p K K' hK z.1) _).mp h1⟩)
    (fun R z h => by omega)
    (GDr_leaf q ha Stop hStopL)
    (fun R x res hres => by
      have hdep : depth (restTable (PrefixGame.ov a (restDepth a R) R x)) a = restDepth a R :=
        (restDepth_eq a _).symm.trans (PrefixGame.restDepth_ov a R x)
      have hs := stop_coupled q a ha Stop hmask R x res hres
      show ((∃ k, Stop _ _) ∧ 1 ≤ depth (restTable (PrefixGame.ov a (restDepth a R) R x)) a) ↔ _
      rw [hdep]
      exact ⟨fun h => ⟨h.2, hs.mp h.1⟩, fun h => ⟨hs.mpr h.2, h.1⟩⟩)
  simp only [mixLaw_restart] at h
  exact h.trans (add_le_add (probEvent_mono'' fun s hs => hs.1) le_rfl)

include ha hmask hStopL in
/-- **Lower chains: contact after the stop, against the stop.** -/
theorem lower_contactAfterStop_le (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * errC adversary q a := by
  have hper : ∀ R : RefTables adversary,
      (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun r => 1 ≤ restDepth a R ∧ genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    intro R
    by_cases hd : 1 ≤ restDepth a R
    · have he : (fun r => 1 ≤ restDepth a R ∧ genStop Stop a R r) = genStop Stop a R :=
        funext fun r => propext ⟨And.right, fun h => ⟨hd, h⟩⟩
      rw [he]
      exact restart_le_R q hq a Stop R
    · have h0 : Pr[genCAS Stop a R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (restartGame adversary q a Stop R) (fun _ _ => none)] = 0 := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_eq_zero.mpr fun r => if_neg fun h => hd ?_
        obtain ⟨step, hstep, -⟩ := h.2.2
        omega
      rw [h0, mul_zero, mul_zero]
      exact bot_le
  have hx : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q])
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * (∑' R, restLaw adversary R * Pr[genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none)] + errC adversary q a)) := by
        gcongr
        exact lower_cas_le_mix q ha Stop hmask hStopL
    _ = ∑' R, restLaw adversary R * ((1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none)])) + (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * errC adversary q a) := by
        rw [mul_add, mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ∑' R, restLaw adversary R * (((2 * q : ℕ) : ENNReal) * Pr[fun r => 1 ≤ restDepth a R ∧ genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none)]) + 1 * ((2 ^ 128 : ENNReal) * errC adversary q a) :=
        add_le_add (ENNReal.tsum_le_tsum fun R => mul_le_mul' le_rfl (hper R)) (mul_le_mul' hx le_rfl)
    _ = ((2 * q : ℕ) : ENNReal) * ∑' R, restLaw adversary R * Pr[fun r => 1 ≤ restDepth a R ∧ genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none)] + (2 ^ 128 : ENNReal) * errC adversary q a := by
        rw [one_mul, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ((2 * q : ℕ) : ENNReal) * (Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | referenceExperiment adversary q] +
          errC adversary q a) + (2 ^ 128 : ENNReal) * errC adversary q a := by
        gcongr
        exact lower_mix_le_stop q ha Stop hmask hStopL
    _ = _ := by ring

/-! ### The charge, by layers -/

theorem calls_pos_depth {d : ℕ} {qs : List RefWorld.Domain} (h : 0 < calls (PrefixGame.PrefixQuery a d) qs) :
    1 ≤ d := by
  cases d with
  | zero => rw [calls_prefixQuery_zero] at h; omega
  | succ d => omega

theorem count_coupled (R : RefTables adversary) (x : Hidden (restDepth a R))
    (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (restartGame adversary q a Stop R (evaluate x.1 (PrefixGame.ovSeed a R x.2))) (fun _ _ => none)).support) :
    prefixCount a (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 := by
  have hview := sampleView_coupled adversary q a R x (res.1.2, res.2)
    (ClaudeWCT.W9.T3.Security.Wots.PrefixGame.coupled_paused_rows q a R x
      (stopAt Stop a R (evaluate x.1 (PrefixGame.ovSeed a R x.2))) res hres)
  exact congrArg PrefixView.count hview

include ha hmask hStopL in
theorem lower_mix_layer_le (k : ℕ) :
    ∑' R, restLaw adversary R * Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] ≤
      Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') | referenceExperiment adversary q] +
        errC adversary q a := by
  have h := mix_le_ref q ha (GDr adversary q Stop) Prod.snd (GDr_snd q Stop)
    (fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k'))
    (fun d R z => k < 2 * calls (PrefixGame.PrefixQuery a d) z.2.1.2.2 ∧
      Stop (PrefixGame.fillTable a R z.1) z.2.1.1)
    (fun R p K K' hK => by
      funext z
      apply propext
      constructor
      · rintro ⟨hk, h1⟩
        have hd := calls_pos_depth (a := a) (by omega : 0 < calls (PrefixGame.PrefixQuery a (restDepth a R)) z.2.1.2.2)
        exact ⟨hk, (hStopL _ _ (fill_congr ha R hd p K K' hK z.1) _).mpr h1⟩
      · rintro ⟨hk, h1⟩
        have hd := calls_pos_depth (a := a) (by omega : 0 < calls (PrefixGame.PrefixQuery a (restDepth a R)) z.2.1.2.2)
        exact ⟨hk, (hStopL _ _ (fill_congr ha R hd p K K' hK z.1) _).mp h1⟩)
    (fun R z h => by
      have := h.1
      rw [calls_prefixQuery_zero] at this
      omega)
    (GDr_leaf q ha Stop hStopL)
    (fun R x res hres => by
      have hc := count_coupled q Stop R x res hres
      have hs := stop_coupled q a ha Stop hmask R x res hres
      show (k < 2 * prefixCount a (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) res.1.2) ∧ _) ↔ _
      rw [hc]
      exact and_congr Iff.rfl hs)
  simp only [mixLaw_restart] at h
  exact h

theorem lt_ite_iff (k n : ℕ) (P : Prop) [Decidable P] : k < (if P then n else 0) ↔ k < n ∧ P := by
  split_ifs with h
  · exact ⟨fun hk => ⟨hk, h⟩, And.left⟩
  · exact ⟨fun hk => absurd hk (Nat.not_lt_zero k), fun hk => absurd hk.2 h⟩

include ha hmask hStopL in
/-- **The charge: mixture ≤ reference + 2q · error** (lower chains). -/
theorem lower_mix_charge_le :
    ∑' R, restLaw adversary R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none) r * genCharge Stop a R r ≤
      ∑' s, referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) + ((2 * q : ℕ) : ENNReal) * errC adversary q a := by
  have hmix : ∀ R : RefTables adversary, ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) r * genCharge Stop a R r =
      ∑ k ∈ Finset.range (2 * q), Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ genStop Stop a R r |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
          (fun _ _ => none)] := by
    intro R
    have h := expectation_layers (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (restartGame adversary q a Stop R) (fun _ _ => none))
      (fun r => if genStop Stop a R r then 2 * seedCost a R r.2.1.2 else 0) (2 * q) (fun r hr => by
        have := restart_real_cost q a Stop R r hr
        split_ifs <;> omega)
    simp only [lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun r => ?_
    unfold genCharge
    congr 1
    show _ = (((if stopAt Stop a R r.1 r.2.1.1 then 2 * seedCost a R r.2.1.2 else 0 : ℕ)) : ENNReal)
    split_ifs <;> simp
  have href : ∑' s, referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) =
      ∑ k ∈ Finset.range (2 * q), Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
        referenceExperiment adversary q] := by
    have h := expectation_layers (referenceExperiment adversary q)
      (fun s => if ∃ k, Stop s.answers (s.trace.take k) then 2 * prefixCount a s else 0) (2 * q) (fun s hs => by
        have := (prefixCount_le_length a s).trans (ref_trace_length_le adversary q s hs)
        split_ifs <;> omega)
    simp only [lt_ite_iff] at h
    rw [← h]
    refine tsum_congr fun s => ?_
    congr 1
    split_ifs <;> simp
  simp only [hmix, href]
  calc ∑' R, restLaw adversary R * ∑ k ∈ Finset.range (2 * q),
        Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ genStop Stop a R r |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none)]
      = ∑ k ∈ Finset.range (2 * q), ∑' R, restLaw adversary R *
          Pr[fun r => k < 2 * seedCost a R r.2.1.2 ∧ genStop Stop a R r |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
              (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range (2 * q),
          (Pr[fun s => k < 2 * prefixCount a s ∧ ∃ k', Stop s.answers (s.trace.take k') |
            referenceExperiment adversary q] + errC adversary q a) :=
        Finset.sum_le_sum fun k _ => lower_mix_layer_le q ha Stop hmask hStopL k
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

include ha hmask hStopL in
/-- **Lower chains: contact after the stop, against the prefix charge.** -/
theorem lower_contactAfterStop_charge (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ∑' s, referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * errC adversary q a := by
  have hx : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q])
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * (∑' R, restLaw adversary R * Pr[genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none)] + errC adversary q a)) := by
        gcongr
        exact lower_cas_le_mix q ha Stop hmask hStopL
    _ = ∑' R, restLaw adversary R * ((1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS Stop a R |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none)])) + (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * errC adversary q a) := by
        rw [mul_add, mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun R => ?_
        ring
    _ ≤ ∑' R, restLaw adversary R * ∑' r,
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
            (fun _ _ => none) r * genCharge Stop a R r + 1 * ((2 ^ 128 : ENNReal) * errC adversary q a) :=
        add_le_add (ENNReal.tsum_le_tsum fun R => mul_le_mul' le_rfl (charge_le_R q hq a Stop R))
          (mul_le_mul' hx le_rfl)
    _ ≤ (∑' s, referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
          (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) + ((2 * q : ℕ) : ENNReal) * errC adversary q a) +
          1 * ((2 ^ 128 : ENNReal) * errC adversary q a) := by
        gcongr
        exact lower_mix_charge_le q ha Stop hmask hStopL
    _ = _ := by ring
end Restart

/-! ### All source chains -/

section Source
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', LeafCongr a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)
include ha hmask hStopL

/-- **Source chains: contact after the stop, against the stop.** -/
theorem source_contactAfterStop_le (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * errC adversary q a :=
  lower_contactAfterStop_le q ha Stop hmask hStopL hq

/-- **Source chains: contact after the stop, against the prefix charge.** -/
theorem source_contactAfterStop_charge (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ∑' s, referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * errC adversary q a :=
  lower_contactAfterStop_charge q ha Stop hmask hStopL hq
end Source

/-- Markers are invariant under the leaf congruence of their chain's leaf. -/
theorem markerAt_stopL {a : ChainAddr} (ha : WotsExtract.SourceChain a) :
    ∀ T T', LeafCongr a.key T T' → ∀ trace, MarkerAt T' trace a ↔ MarkerAt T trace a :=
  fun _ _ hC trace => markerAt_leafCongr hC (source_bounds ha).2 trace a

/-- **Source chains: contact after the marker, against the marker.** -/
theorem source_markerFirst_at_le (q : ℕ) (hq : q < 2 ^ 128) (a : ChainAddr) (ha : WotsExtract.SourceChain a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace a) s.answers s.trace a |
          referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => MarkerAt s.answers s.trace a | referenceExperiment adversary q] +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * errC adversary q a := by
  have h := source_contactAfterStop_le (adversary := adversary) q ha (fun T trace => MarkerAt T trace a)
    (fun T trace => markerAt_maskAt T trace a (sourceChain_maskOK a ha))
    (markerAt_stopL ha) hq
  simpa only [markerAt_take_exists] using h

/-! ### Size of the total seed-test error -/

theorem kconst_le (q : ℕ) : (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) ≤ 5 * (q : ℝ) ^ 2 := by
  have h : 2 * ClaudeWCT.Arith.SideChannel.kconst q ≤ 10 * q ^ 2 := by
    unfold ClaudeWCT.Arith.SideChannel.kconst
    rw [Nat.choose_two_right, Nat.choose_two_right]
    have h1 := Nat.div_mul_le_self (3 * q * (3 * q - 1)) 2
    have h2 := Nat.div_mul_le_self (q * (q - 1)) 2
    have h3 : 3 * q * (3 * q - 1) ≤ 9 * q ^ 2 := by
      calc 3 * q * (3 * q - 1) ≤ 3 * q * (3 * q) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = 9 * q ^ 2 := by ring
    have h4 : q * (q - 1) ≤ q ^ 2 := by
      calc q * (q - 1) ≤ q * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = q ^ 2 := by ring
    omega
  have h' : (2 * ClaudeWCT.Arith.SideChannel.kconst q : ℝ) ≤ 10 * (q : ℝ) ^ 2 := by exact_mod_cast h
  linarith

theorem card_digest_real : (Fintype.card Digest : ℝ) = 2 ^ 128 := by
  rw [Fintype.card_bitVec]
  push_cast
  ring

/-- **The total seed-test error is cubic**: `errTot ≤ 0.351 · (q/2^128)^2` for `q ≤ 2718 · 2^106` (campaign T8D: the
leaf sum charges up to 54 chains per test query, the top leaves; it was 43 with lower leaves only; campaign T8E: split
2718 · 2^106, 540 y0 / (1 - y0) = 0.35016). -/
theorem errTot_le_small (q : ℕ) (hs : q ≤ 2718 * 2 ^ 106) :
    errTot adversary q ≤ (351 / 1000 : ENNReal) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  set t : ℝ := ((2 : ℝ) ^ 128)⁻¹ * q with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 2718 / 2 ^ 22 := by
    rw [ht, inv_mul_le_iff₀ (by positivity)]
    have : (q : ℝ) ≤ 2718 * 2 ^ 106 := by exact_mod_cast hs
    linarith
  have hpos : 0 < 1 - t := by linarith
  have hconst : errConst q = 2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q / (1 - t) := by
    unfold errConst
    rw [card_digest_real]
  have hc0 : 0 ≤ errConst q := by rw [hconst]; positivity
  have hreal : errConst q * (54 * q) ≤ 351 / 1000 * ((q : ℝ) / 2 ^ 128) ^ 2 := by
    rw [hconst, div_mul_eq_mul_div, div_le_iff₀ hpos]
    have hk := kconst_le q
    calc 2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) * (54 * q)
        ≤ 2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * (5 * (q : ℝ) ^ 2) * (54 * q) := by gcongr
      _ = 540 * t ^ 3 := by rw [ht]; ring
      _ ≤ 351 / 1000 * t ^ 2 * (1 - t) := by
          have h1 : 0 ≤ 351 / 1000 - 540351 / 1000 * t := by
            have : (540351 / 1000 : ℝ) * (2718 / 2 ^ 22) ≤ 351 / 1000 := by norm_num
            nlinarith
          nlinarith [mul_nonneg (sq_nonneg t) h1]
      _ = 351 / 1000 * ((q : ℝ) / 2 ^ 128) ^ 2 * (1 - t) := by rw [ht]; ring
  have hq1 : (Fintype.card Digest : ℝ)⁻¹ * q < 1 := by
    rw [card_digest_real]
    linarith
  refine (errC_sum_le q hq1).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  exact hreal

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

/-!
# Regrouped seed-test scalar budget

A pair family has 86 real chains rather than the current maximum 54. The
existing 0.351 quadratic bound cannot simply be kept for this new charge.
These are scalar bounds on the proposed charge, not a proof that the
unchanged reference experiment or errTot has been correctly regrouped.
-/
namespace ClaudeWCT.W9.T3.Security.Wots.AdjacentLeafResearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Bound the actual existing side-channel error constant against an 86q
charge, on a slightly smaller small-route window. -/
theorem regrouped_seed_charge_le (q : ℕ) (hs : q ≤ 2710 * 2 ^ 106) :
    ENNReal.ofReal (Leaf.errConst q) * (86 * q) ≤
      (557 / 1000 : ENNReal) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  set t : ℝ := ((2 : ℝ) ^ 128)⁻¹ * q with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 2710 / 2 ^ 22 := by
    rw [ht, inv_mul_le_iff₀ (by positivity)]
    have : (q : ℝ) ≤ 2710 * 2 ^ 106 := by exact_mod_cast hs
    linarith
  have hpos : 0 < 1-t := by linarith
  have hconst : Leaf.errConst q =
      2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q / (1-t) := by
    unfold Leaf.errConst
    rw [Leaf.card_digest_real]
  have hc0 : 0 ≤ Leaf.errConst q := by rw [hconst]; positivity
  have hr : Leaf.errConst q * (86*q) ≤ 557/1000 * ((q : ℝ)/2^128)^2 := by
    rw [hconst,div_mul_eq_mul_div,div_le_iff₀ hpos]
    have hk := Leaf.kconst_le q
    calc 2 * ((2 : ℝ)^128)⁻¹^3 * (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) * (86*q)
        ≤ 2 * ((2 : ℝ)^128)⁻¹^3 * (5*(q : ℝ)^2) * (86*q) := by gcongr
      _ = 860*t^3 := by rw [ht]; ring
      _ ≤ 557/1000*t^2*(1-t) := by
        have h1 : 0 ≤ 557/1000-860557/1000*t := by
          have : (860557/1000 : ℝ)*(2710/2^22) ≤ 557/1000 := by norm_num
          nlinarith
        nlinarith [mul_nonneg (sq_nonneg t) h1]
      _ = 557/1000*((q : ℝ)/2^128)^2*(1-t) := by rw [ht]; ring
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc0,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  exact hr

/-- Direct conditional use: the regrouped errTot must first be proved
bounded by this 86q charge. No such hypothesis is asserted for old errTot. -/
theorem regrouped_seed_error_le {err : ENNReal} (q : ℕ) (hs : q ≤ 2710*2^106)
    (hcharge : err ≤ ENNReal.ofReal (Leaf.errConst q) * (86*q)) :
    err ≤ (557/1000 : ENNReal)*((q : ENNReal)/2^128)^2 :=
  hcharge.trans (regrouped_seed_charge_le q hs)

#print axioms regrouped_seed_charge_le
#print axioms regrouped_seed_error_le
end ClaudeWCT.W9.T3.Security.Wots.AdjacentLeafResearch
