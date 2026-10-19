import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsRestart
set_option Elab.async false

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

/-- The stop-then-contact event of the prefix-game run at depth `d`. -/
def casD (Stop : Answers → List Entry → Prop) (a : ChainAddr) (d : ℕ) (R : RefTables adversary)
    (z : Digest × ((List Entry × SeedResult) × TObs d)) : Prop :=
  Stop (PrefixGame.fillTable a R z.1) z.2.1.1 ∧ ¬ContactAt (PrefixGame.fillTable a R z.1) z.2.1.1 a ∧
    Contact z.2.2 z.1

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

theorem lt_ite_iff (k n : ℕ) (P : Prop) [Decidable P] : k < (if P then n else 0) ↔ k < n ∧ P := by
  split_ifs with h
  · exact ⟨fun hk => ⟨hk, h⟩, And.left⟩
  · exact ⟨fun hk => absurd hk (Nat.not_lt_zero k), fun hk => absurd hk.2 h⟩

end Restart

/-! ### All source chains -/

section Source
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', LeafCongr a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)
include ha hmask hStopL

end Source

/-! ### Size of the total seed-test error -/

theorem kconst_le (q : ℕ) : (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) ≤ 5 * (q : ℝ) ^ 2 := by
  unfold ClaudeWCT.Arith.SideChannel.kconst
  push_cast
  nlinarith [sq_nonneg (q : ℝ)]

theorem card_digest_real : (Fintype.card Digest : ℝ) = 2 ^ 128 := by
  rw [Fintype.card_bitVec]
  push_cast
  ring

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

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable local instance : Fintype Coordinate := coordinateFintype

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
theorem source_bounds {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24 := by
  refine ⟨by have := hb.1.tree_lt; omega, ?_⟩
  have h1 := hb.1.2
  have h2 : 2 ^ height b.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
    have := SigGolfCandidate.T3.Security.Wots.height_le b.key.lay; omega)
  omega

/-! ### Contacts and markers under leaf congruence -/

section Congr
variable {L : LeafAddr} {T T' : Answers} (hC : CanonicalRef.Leaf.Congr (sourceMessages T) L T T') (hLleaf : L.leaf < 2 ^ 24)
  (hLtree : L.tree < 2 ^ 40)
include hC hLleaf

end Congr


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
noncomputable local instance : Fintype Coordinate := coordinateFintype

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame
noncomputable def GDr (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    OracleComp RefWorld (List Entry × SeedResult) :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull (Stop T) (PairedReference.referenceGame T adversary q) []

theorem GDr_snd (q : ℕ) (Stop : Answers → List Entry → Prop) (T : Answers) :
    Prod.snd <$> GDr adversary q Stop T = Core.GDseed adversary q T :=
  SigGolfCandidate.T3.Security.Wots.PrefixGame.pausedFull_snd _ _ _

theorem gameD_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary)) :
    Core.gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (GDr adversary q Stop) = restartGame adversary q a Stop R := by
  funext e
  rfl

theorem mixLaw_restart (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary)) :
    Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (GDr adversary q Stop) =
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
        (fun _ _ => none) := by
  unfold Core.mixLaw
  rw [gameD_restart]

theorem restart_real_cost (q : ℕ) (a : ChainAddr) (Stop : Answers → List Entry → Prop) (R : Tables (PairedReference.referenceInputs adversary))
    (r : Digest × ((List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest)))
    (hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
      (fun _ _ => none)).support) : seedCost a R r.2.1.2 ≤ q := by
  have h := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_map
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (restartGame adversary q a Stop R)
    (fun _ => Prod.snd) (fun _ _ => none)
  simp only [restartGame_snd] at h
  have hm : (r.1, r.2.1.2, r.2.2) ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)).support := by
    rw [h, PMF.mem_support_map_iff]
    exact ⟨r, hr, rfl⟩
  exact seedGame_real_cost (referenceInputs_subset adversary) adversary q a R _ hm

/-! ### Lower chains -/

section Restart
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)

/-- The stop-then-contact event of the prefix-game run at depth `d`. -/
def casD (Stop : Answers → List Entry → Prop) (a : ChainAddr) (d : ℕ) (R : Tables (PairedReference.referenceInputs adversary))
    (z : Digest × ((List Entry × SeedResult) × TObs d)) : Prop :=
  Stop (fillTable a R z.1) z.2.1.1 ∧ ¬ContactAt (fillTable a R z.1) z.2.1.1 a ∧
    Contact z.2.2 z.1

/-! ### The charge, by layers -/

theorem calls_pos_depth {d : ℕ} {qs : List RefWorld.Domain} (h : 0 < calls (PrefixGame.PrefixQuery a d) qs) :
    1 ≤ d := by
  cases d with
  | zero => rw [calls_prefixQuery_zero] at h; omega
  | succ d => omega

include ha in
theorem count_coupled (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
    (res : (List Entry × SeedResult) × (Fin (RawPrefix.restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (restartGame adversary q a Stop R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support) :
    prefixCount a (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 := by
  have hview := sampleView_coupled adversary q a R ha.1 x (res.1.2, res.2)
    (coupled_paused_rows q a R x
      (stopAt Stop a R (evaluate x.1 (RawPrefix.ovSeed a R x.2))) res hres)
  exact congrArg PrefixView.count hview

theorem lt_ite_iff (k n : ℕ) (P : Prop) [Decidable P] : k < (if P then n else 0) ↔ k < n ∧ P := by
  split_ifs with h
  · exact ⟨fun hk => ⟨hk, h⟩, And.left⟩
  · exact ⟨fun hk => absurd hk (Nat.not_lt_zero k), fun hk => absurd hk.2 h⟩

end Restart

/-! ### All source chains -/

section Source
variable (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (Stop : Answers → List Entry → Prop) (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace)
  (hStopL : ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → ∀ trace, Stop T' trace ↔ Stop T trace)
include ha hmask hStopL

end Source


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
def MarkerAt (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  CanonicalRef.MarkerAt T (sourceMessages T) trace a

theorem markerAt_maskAt (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hal : Wots.Mask.MaskOK a) : MarkerAt (maskAt T a) trace a ↔ MarkerAt T trace a := by
  unfold MarkerAt CanonicalRef.MarkerAt maskAt
  simp only [CanonicalRef.referenceInput, CanonicalRef.referenceDigits]
  rw [CanonicalRef.referenceSearch_source_maskAt T a hal,
    CanonicalRef.sourceMessages_maskAt T _ a hal]

theorem markerAt_take_exists (T : Answers) (trace : List Entry) (a : ChainAddr) :
    (∃ k, MarkerAt T (trace.take k) a) ↔ MarkerAt T trace a := by
  constructor
  · rintro ⟨k, message, counter, pad, answer, digits, hfit, hm, h⟩
    exact ⟨message, counter, pad, answer, digits, hfit, List.mem_of_mem_take hm, h⟩
  · intro h
    exact ⟨trace.length, by rw [List.take_length]; exact h⟩

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
