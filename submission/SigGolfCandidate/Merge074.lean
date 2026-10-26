import Mathlib.Tactic
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge020
import SigGolfCandidate.Merge021
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge042
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge066
import SigGolfCandidate.Merge071
import SigGolfCandidate.Merge073

-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsLeafRestart ====
section

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
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsClasses ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallA
theorem hdrBlock_chainRowW (a : ChainAddr) (s : Nat) (v : Digest) :
    Extract.hdrBlock (chainRowW a s v) = bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
  WCT9.chainInputW_header _ _ _ _ _ _
theorem posOf_chainRow (a : ChainAddr) (s : Nat) (v : Digest) (htree : a.key.tree < 2 ^ 31)
    (hleaf : a.key.leaf < 4096) (hc : a.chain < 64) (hs : s < 7) :
    Extract.posOf (chainRowW a s v) = some (.chain a.key.lay a.key.tree a.key.leaf a.chain s) :=
  Extract.posOf_eq ⟨htree, hleaf, hc, hs⟩ (chainRowW_length a s v)
    (hdrBlock_chainRowW a s v)
/-- Pairing stage 1: no chain row of the current scheme (F or G) is a digest query (header block). -/
theorem chainRowW_ne_digest (a : ChainAddr) (s : Nat) (v : Digest) (rho : Digest) (m : Message) (c : BitVec 32) :
    chainRowW a s v ≠ pad64 (digestInput rho m c) := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_chainRowW] at hb
  change _ = SigGolfCandidate.T3M.Extract.hdrBlock _ at hb
  rw [SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest] at hb
  exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hb)
end SmallA
open SigGolfCandidate.T3.Security.Wots.SmallA (sourceChain_bounds)
open ClaudeWCT.W9.T3.Security.Wots.SmallA (chainRowW_ne_digest)
namespace SmallA
theorem chainRowW_ne_encRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : WCT9.LayerMsg)
    (c : BitVec 32) (pad : RowPad) : chainRowW a s v ≠ encRow L m c pad := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h1 : ClaudeWCT.W9.T3M.Extract.hdrBlock (chainRowW a s v) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
    hdrBlock_chainRowW a s v
  rw [h1, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker] at hm
  have := chainHeader_firstByte a.key.lay a.key.tree a.key.leaf a.chain s
  unfold tweakMarker at hm
  omega
theorem encRow_ne_digest (L : LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : RowPad) (rho : Digest)
    (m' : Message) (c' : BitVec 32) : encRow L m c pad ≠ pad64 (digestInput rho m' c') := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h2 : ClaudeWCT.W9.T3M.Extract.hdrBlock (pad64 (digestInput rho m' c')) =
      bytesLE 16 (digestHeader c') :=
    SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest rho m' c'
  rw [h2, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker, digestHeader_marker] at hm
  exact absurd hm (by decide)
end SmallA
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, pad, -, hx⟩ := hE
    exact SmallA.chainRowW_ne_encRow a s v L m c pad hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRowW_ne_digest a s v rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, pad, -, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds ha
    have h7 := Mask.depth_le_seven T a
    have hrow := SmallA.posOf_chainRow a s v htree hleaf hc (by omega)
    rw [hrow] at hpos
    cases hpos
    change OtherChainRow T (chainRowW a s v) at hcls
    obtain ⟨a', s', hpos', hcase⟩ := hcls
    rw [hrow] at hpos'
    simp only [Option.some.injEq, Extract.Pos.chain.injEq] at hpos'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos'
    have ha' : a' = a := by
      obtain ⟨⟨l, t, f⟩, i⟩ := a
      obtain ⟨⟨l', t', f'⟩, i'⟩ := a'
      simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
    subst ha' h5
    rcases hcase with hpad | hge
    · exact hpad v rfl
    · omega
  · exact hP
theorem encodingRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', pad, -, hx⟩ := hE
  exact SmallA.encRow_ne_digest L m' c' pad rho m c hx.symm
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
theorem shortCongruent_prefixRow : ShortCongruent PrefixRow := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [PrefixRow, PrefixRowAt, hdepth]
  · exact Iff.rfl
theorem shortCongruent_otherQuery : ShortCongruent OtherQuery := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  have hcls : ∀ x p, StructuralClass A x p ↔ StructuralClass T x p := by
    intro x p
    cases p <;> simp only [StructuralClass, OtherChainRow, hdepth]
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [OtherQuery, OtherInput, hcls]
  · exact Iff.rfl
noncomputable def refExpect (adversary : AdversaryP) (q : Nat) (f : RefSample → Nat) : ENNReal :=
  ∑' s, referenceExperiment adversary q s * (f s : ENNReal)
theorem reference_class_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    refExpect adversary q prefixClassCount + refExpect adversary q encodingCount + refExpect adversary q otherCount +
      SeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow shortCongruent_otherQuery prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input => prefixRow_digest_disjoint z.2 input)
    (fun z input => encodingRow_digest_disjoint z.2 input) (fun z input => otherQuery_digest_disjoint z.2 input)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference.Classes
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.SmallA (sourceChain_bounds)
open ClaudeWCT.W9.T3.Security.Wots.SmallA (chainRowW_ne_digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, pad, -, hx⟩ := hE
    exact SmallA.chainRowW_ne_encRow a s v L m c pad hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRowW_ne_digest a s v rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, pad, -, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    have hlegacy : SigGolfCandidate.T3.Security.WotsExtract.SourceChain a := ⟨⟨ha.1.tree_lt,ha.1.2⟩,ha.2⟩
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds hlegacy
    have h7 := (CanonicalRef.depth_le T (CanonicalRef.sourceMessages T) a ha.2).trans
      (SigGolfCandidate.T3.Security.Wots.Mask.width_le _ _)
    have hrow := SmallA.posOf_chainRow a s v htree hleaf hc (by omega)
    rw [hrow] at hpos
    cases hpos
    change CanonicalRef.OtherChainRow T (CanonicalRef.sourceMessages T) (chainRowW a s v) at hcls
    obtain ⟨a', s', hpos', hcase⟩ := hcls
    rw [hrow] at hpos'
    simp only [Option.some.injEq, Extract.Pos.chain.injEq] at hpos'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos'
    have ha' : a' = a := by
      obtain ⟨⟨l, t, f⟩, i⟩ := a
      obtain ⟨⟨l', t', f'⟩, i'⟩ := a'
      simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
    subst ha' h5
    rcases hcase with hpad | hge
    · exact hpad v rfl
    · omega
  · exact hP
theorem encodingRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', pad, -, hx⟩ := hE
  exact SmallA.encRow_ne_digest L m' c' pad rho m c hx.symm
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
theorem shortCongruent_prefixRow : ShortCongruent CanonicalRef.Normalized.Contacts.PrefixRow := by
  intro A T hAT input
  have hdepth : CanonicalRef.depth A (CanonicalRef.sourceMessages A) = CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [CanonicalRef.Normalized.Contacts.PrefixRow, CanonicalRef.Normalized.PrefixRowAt, hdepth]
  · exact Iff.rfl

def digestClass : PairedSeccLaw.SampleClass := fun _ input=>IsDigestQuery input
theorem sample_class_budget (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) :
    PairedSeccLaw.sampleCharge (fun z input=>CanonicalRef.Normalized.Contacts.PrefixRow z.2 input) q z +
    PairedSeccLaw.sampleCharge (fun z input=>EncodingRow z.2 input) q z +
    PairedSeccLaw.sampleCharge (fun z input=>OtherQuery z.2 input) q z +
    PairedSeccLaw.sampleCharge digestClass q z ≤ q := by
  let A := CanonicalRef.Normalized.Contacts.PrefixRow z.2
  let B := EncodingRow z.2
  let C := OtherQuery z.2
  let D := IsDigestQuery
  have hab : ∀input,¬(A input ∧ B input) := prefixRow_encodingRow_disjoint z.2
  have hac : ∀input,¬(A input ∧ C input) := prefixRow_otherQuery_disjoint z.2
  have had : ∀input,¬(A input ∧ D input) := prefixRow_digest_disjoint z.2
  have hbc : ∀input,¬(B input ∧ C input) := encodingRow_otherQuery_disjoint z.2
  have hbd : ∀input,¬(B input ∧ D input) := encodingRow_digest_disjoint z.2
  have hcd : ∀input,¬(C input ∧ D input) := otherQuery_digest_disjoint z.2
  have h1 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or A B hab q (QueryRecorded.recordedTrace z.1).events
  have h2 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or (fun input=>A input ∨ B input) C
    (fun input h=>h.1.elim (fun ha=>hac input ⟨ha,h.2⟩) (fun hb=>hbc input ⟨hb,h.2⟩)) q
    (QueryRecorded.recordedTrace z.1).events
  have h3 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or (fun input=>(A input ∨ B input) ∨ C input) D
    (fun input h=>h.1.elim (fun h'=>h'.elim (fun ha=>had input ⟨ha,h.2⟩)
      (fun hb=>hbd input ⟨hb,h.2⟩)) (fun hc=>hcd input ⟨hc,h.2⟩)) q
    (QueryRecorded.recordedTrace z.1).events
  have hle := SigGolfCandidate.T3.Security.SeccLaw.classCharge_le (fun input=>((A input ∨ B input) ∨ C input) ∨ D input) q
    (QueryRecorded.recordedTrace z.1).events
  change SigGolfCandidate.T3.Security.SeccLaw.classCharge A q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge B q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge C q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge D q _ ≤ q
  omega

noncomputable def refExpect (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (f : RefSample → Nat) : ENNReal := ∑'s,referenceExperiment adversary q s*(f s : ENNReal)

theorem prefix_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>CanonicalRef.Normalized.Contacts.PrefixRow z.2 input) :=
  reference_count_le adversary q hq CanonicalRef.Normalized.Contacts.PrefixRow shortCongruent_prefixRow

theorem encoding_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q encodingCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>EncodingRow z.2 input) :=
  reference_count_le adversary q hq EncodingRow shortCongruent_encodingRow

theorem other_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q otherCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>OtherQuery z.2 input) :=
  reference_count_le adversary q hq OtherQuery otherQuery_short

theorem reference_class_budget (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount+refExpect adversary q encodingCount+refExpect adversary q otherCount+
      PairedSeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq CanonicalRef.Normalized.Contacts.PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow otherQuery_short prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input=>prefixRow_digest_disjoint z.2 input)
    (fun z input=>encodingRow_digest_disjoint z.2 input) (fun z input=>otherQuery_digest_disjoint z.2 input)

end ClaudeWCT.W9.T3.Security.Wots.PairedReference.Classes
end
-- ==== merged from T3_Secc_WotsEncodingE1 ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
section Assembly
variable (adversary : AdversaryP) (q : Nat)
theorem tsum_uniform_prod {α β : Type} {iP : Fintype (α × β)} [Nonempty (α × β)] (iA : Fintype α) (iB : Fintype β)
    [Nonempty α] [Nonempty β] (G : α × β → ENNReal) :
    ∑' R, @PMF.uniformOfFintype (α × β) iP _ R * G R =
      ∑' a, @PMF.uniformOfFintype α iA _ a * ∑' b, @PMF.uniformOfFintype β iB _ b * G (a, b) := by
  obtain rfl : iP = @instFintypeProd α β iA iB := Subsingleton.elim _ _
  rw [ENNReal.tsum_prod (f := fun a b => @PMF.uniformOfFintype (α × β) (@instFintypeProd α β iA iB) _ (a, b) *
    G (a, b))]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (by simp) (by simp), mul_assoc]
theorem weighted_le {α : Type} (μ : α → ENNReal) (left right : α → ENNReal) (rate : ENNReal)
    (h : ∀ x, left x ≤ rate * right x) : ∑' x, μ x * left x ≤ rate * ∑' x, μ x * right x := by
  calc _ ≤ ∑' x, μ x * (rate * right x) := ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => mul_left_comm _ _ _
end Assembly
end Enc
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsEncodingMarker ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
theorem unit_neighbors_le_53 (lay : Layer) (word : Encoding lay) (i : ChainIndex lay) :
    (MixedCode.unitNeighbors word i).card ≤ 53 :=
  (MixedCode.unitNeighbors_card_le word i).trans (Nat.sub_le_sub_right (chainCount_le_54 lay) 1)
end Enc
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsEncodingContact ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
noncomputable def contacts (T : Answers) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ ContactAt T trace (chainAt p)).card
theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp
end Enc
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEncodingE1 ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
section Assembly
variable (adversary : AdversaryP) (q : Nat)
theorem restTable_pair (p : FullGame.FullTable) (x : referenceInputs adversary → HashOutput) :
    restTable ((p, x) : RefTables adversary) = eagerAnswers (referenceInputs adversary) p x := by
  rw [restTable]
theorem reference_free_le (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (f g : RefSample → ENNReal)
    (rate : ENNReal)
    (hfg : ∀ (privateTable : FullGame.FullTable) (pub : referenceInputs adversary → HashOutput),
      ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub) → HashOutput)
          (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) adversary q) :
            PMF SeedResult) r *
          f (mkSample (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) r) ≤
      rate * ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub) →
          HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) adversary q) :
            PMF SeedResult) r *
          g (mkSample (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) r)) :
    ∑' s, referenceExperiment adversary q s * f s ≤ rate * ∑' s, referenceExperiment adversary q s * g s := by
  rw [reference_eq_bind, tsum_bind_mul, tsum_bind_mul]
  simp only [tsum_map_mul]
  unfold restLaw
  have iF : Fintype FullGame.FullTable := by unfold FullGame.FullTable; exact Pi.instFintype
  have iU : Fintype (referenceInputs adversary → HashOutput) := Pi.instFintype
  rw [tsum_uniform_prod iF iU, tsum_uniform_prod iF iU]
  simp only [restTable_pair]
  refine weighted_le _ _ _ _ fun privateTable => ?_
  have hU := publicUniverse_sub adversary
  rw [@public_resample (referenceInputs adversary) iX iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * f (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r)),
    @public_resample (referenceInputs adversary) iX iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * g (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r))]
  refine weighted_le _ _ _ _ fun pub => ?_
  exact hfg privateTable pub
theorem reference_cells_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (f g : RefSample → ENNReal) (rate : ENNReal)
    (hfg : ∀ (privateTable : FullGame.FullTable) (pub : referenceInputs adversary → HashOutput),
      ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          f (mkSample (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) r) ≤
      rate * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) adversary q) : PMF SeedResult) r *
          g (mkSample (eagerAnswers (referenceInputs adversary) privateTable (ov (cellKey (eagerAnswers (referenceInputs adversary) privateTable pub)).1 pub y)) r)) :
    ∑' s, referenceExperiment adversary q s * f s ≤ rate * ∑' s, referenceExperiment adversary q s * g s := by
  rw [reference_eq_bind, tsum_bind_mul, tsum_bind_mul]
  simp only [tsum_map_mul]
  unfold restLaw
  have iF : Fintype FullGame.FullTable := by unfold FullGame.FullTable; exact Pi.instFintype
  have iU : Fintype (referenceInputs adversary → HashOutput) := Pi.instFintype
  rw [tsum_uniform_prod iF iU, tsum_uniform_prod iF iU]
  simp only [restTable_pair]
  refine weighted_le _ _ _ _ fun privateTable => ?_
  have hU := publicUniverse_sub adversary
  rw [@public_resample_cells (referenceInputs adversary) _ _ iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * f (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r)),
    @public_resample_cells (referenceInputs adversary) _ _ iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * g (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r))]
  refine weighted_le _ _ _ _ fun pub => ?_
  exact hfg privateTable pub
theorem reference_matchInd_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) :
    ∑' s, referenceExperiment adversary q s * matchInd s ≤
      (7 / ((4 : ENNReal) * 2^128)) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) :=
  reference_free_le adversary q iX matchInd (fun s => (encodingCount s : ENNReal)) _
    (fun privateTable pub => free_match_le adversary q iX (referenceInputs adversary)
      (publicUniverse_sub adversary) privateTable pub)
end Assembly
end Enc
open Enc in
theorem reference_encodingMatch_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => ∃ L, WotsExtract.SourceLeaf7 L ∧ EncodingMatchAt s.answers s.trace L |
        referenceExperiment adversary q] ≤
      (7 / ((4 : ENNReal) * 2^128)) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  refine le_trans ?_ (Enc.reference_matchInd_le adversary q (fun k => Pi.instFintype))
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun s => ?_
  split_ifs with h
  · obtain ⟨L, h7, hm⟩ := h
    have ht31 : L.tree < 2 ^ 31 := lt_of_lt_of_le h7.1
      (Nat.pow_le_pow_right (by decide) (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
    have hpos : ∃ L' : CanonGraph.LeafPos, L'.Source ∧ EncodingMatchAt s.answers s.trace (Enc.leafOf L') := by
      refine ⟨⟨L.lay, ⟨L.tree, ht31⟩, ⟨L.leaf, lt_of_lt_of_le h7.2 ?_⟩⟩, h7, hm⟩
      calc 2 ^ height L.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le L.lay)
        _ = 4096 := by norm_num
    rw [Enc.matchInd, if_pos hpos, mul_one, PMF.probOutput_eq_apply]
  · exact zero_le
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput

theorem reference_expectation (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (f : RefSample → ENNReal) :
    ∑' s, PairedReference.referenceExperiment adversary q s * f s =
      ∑' privateTable, PMF.uniformOfFintype FullGame.FullTable privateTable *
        ∑' pub, PMF.uniformOfFintype (PairedReference.referenceInputs adversary → HashOutput) pub *
          ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary)
            privateTable pub) adversary q) : PMF SeedResult) r *
            f (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) r) := by
  have heq : PairedReference.referenceExperiment adversary q =
      (PMF.uniformOfFintype FullGame.FullTable).bind (fun privateTable =>
        (PMF.uniformOfFintype (PairedReference.referenceInputs adversary → HashOutput)).bind (fun pub =>
          (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary)
            privateTable pub) adversary q) : PMF SeedResult).map
              (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)))) := by
    unfold PairedReference.referenceExperiment PairedReference.referenceComp
    rw [liftM_bind, PrefixGame.liftM_uniform]
    simp only [liftM_bind, PrefixGame.liftM_uniform,liftM_map]
    rfl
  rw [heq,tsum_bind_mul]
  apply tsum_congr
  intro privateTable
  rw [tsum_bind_mul]
  apply congrArg
  apply tsum_congr
  intro pub
  rw [tsum_map_mul]


theorem reference_cells_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (f g : RefSample → ENNReal) (rate : ENNReal)
    (hfg : ∀ (privateTable : FullGame.FullTable) (pub : PairedReference.referenceInputs adversary → HashOutput),
      ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey
          (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
          (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          f (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) r) ≤
      rate * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey
          (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
          (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          g (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable
            (Enc.ov (cellKey (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub)
              (sourceMessages (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub))).cells pub y)) r)) :
    ∑' s, PairedReference.referenceExperiment adversary q s * f s ≤
      rate * ∑' s, PairedReference.referenceExperiment adversary q s * g s := by
  rw [reference_expectation, reference_expectation]
  apply SigGolfCandidate.T3.Security.Wots.Enc.weighted_le
  intro privateTable
  have hU : SeccLaw.publicUniverse ⊆ PairedReference.referenceInputs adversary := Finset.subset_union_left
  rw [public_resample_source hU privateTable
      (fun pub => ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * f (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) r)),
    public_resample_source hU privateTable
      (fun pub => ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * g (mkSample (eagerAnswers (PairedReference.referenceInputs adversary) privateTable pub) r))]
  exact SigGolfCandidate.T3.Security.Wots.Enc.weighted_le _ _ _ _ (hfg privateTable)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEncodingMarker ====
section
-- serialization only (no declarations used): keeps this ~9 GB-private module from building in parallel with WotsLeafSum under the verifier's 2-job / 24 GiB limit



namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
theorem uniform_unit_neighbors (lay : Layer) (W : Encoding lay) (i : ChainIndex lay) :
    Pr[fun ans => ∃ high : Bool, ClaudeWCT.WCT9.verificationAnswer lay high ans ∈
      EncodingTargets.targets lay (MixedCode.unitNeighbors W i) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (371 / 4) / (2 : ENNReal)^128 := by
  classical
  let targets := EncodingTargets.targets lay (MixedCode.unitNeighbors W i)
  have hc : targets.card ≤ chainCount lay - 1 :=
    (EncodingTargets.targets_card _ _).trans (MixedCode.unitNeighbors_card_le W i)
  have hn : targets.card ≤ 53 := by
    have hmax : chainCount lay ≤ 54 := by fin_cases lay <;> decide +kernel
    omega
  have hp : lay ≠ 0 → ∀ d, d ∈ targets → lowerSpare d := by
    intro hl d hd
    obtain ⟨word, _, hword⟩ := (EncodingTargets.mem_targets _ _ _).mp hd
    exact decode_lowerSpare hl hword
  calc _ ≤ (targets.card : ENNReal) * (7 / ((4 : ENNReal) * 2^128)) :=
        ClaudeWCT.WCT9.probability_verification_exists_le lay targets hp
    _ ≤ 53 * (7 / ((4 : ENNReal) * 2^128)) := mul_le_mul' (by exact_mod_cast hn) le_rfl
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
      norm_num
end Enc
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.WCT9.CanonicalRates
open SigGolfCandidate.T3
/-- Both halves of a uniform answer, counted separately (kept outside the `irreducible Finset.univ` section). -/
theorem halves_card (p : Digest → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a : HashOutput => p (a.extractLsb' 0 128)).card +
    (Finset.univ.filter fun a : HashOutput => p (a.extractLsb' 128 128)).card =
      (Finset.univ.filter p).card * (2*2^128) := by
  have hl := SphincsSecurity.Completeness.card_filter_low (n := 256) (w := 128) (by decide) p
  have hh := SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 128) (by decide) p
  dsimp only [Nat.reduceSub] at hl hh
  rw [hl, hh]
  ring

theorem encoding_broad (lay : Layer) :
    (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome).card ≤
      (Finset.univ.filter fun d : Digest => (decode lay d).isSome).card * (2*2^128) := by
  have hsub : (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome) ⊆
      (Finset.univ.filter fun a : HashOutput => (decode lay (a.extractLsb' 0 128)).isSome) ∪
      (Finset.univ.filter fun a : HashOutput => (decode lay (a.extractLsb' 128 128)).isSome) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at ha ⊢
    rw [encodingAnswer_eq] at ha
    split_ifs at ha
    · exact Or.inl ha
    · exact Or.inr ha
  have hh := halves_card (fun d : Digest => (decode lay d).isSome = true)
  exact le_trans (Finset.card_le_card hsub) ((Finset.card_union_le _ _).trans hh.le)
end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open SigGolfCandidate.T3
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false
attribute [local irreducible] Finset.univ Finset.filter
def broadCount (lay : Layer) : Nat :=
  (Finset.univ.filter fun d : Digest => (decode lay d).isSome).card

theorem broad_decoder_card (lay : Layer) : broadCount lay =
    (if lay=0 then SigGolfResearch.NonbinaryTop.Counting.count else EncodingCounting.rawAcceptedCount lay) := by
  unfold broadCount
  rw [← Fintype.card_subtype]
  by_cases hl : lay=0
  · subst lay
    exact Nonbinary.actual_decoder_count
  · rw [Fintype.card_congr (EncodingCounting.acceptedDigestEquiv lay hl), EncodingCounting.accepted_words_count]
    exact (if_neg hl).symm

/-- Crude union bound (both halves): enough for the 1000/1001 rejection estimate. -/
theorem broad_encoding_card (lay : Layer) :
    (Finset.univ.filter fun a : HashOutput => (decode lay (encodingAnswer lay a)).isSome).card ≤
      broadCount lay * (2*2^128) := by
  simpa only [broadCount] using encoding_broad lay


theorem encodingAnswer_normal (lay : Layer) (a : HashOutput) :
    encodingAnswer (CanonicalPolicy.normalLayer lay) a=encodingAnswer lay a := by
  fin_cases lay <;> rfl

theorem verificationAnswer_normal (lay : Layer) (high : Bool) (a : HashOutput) :
    verificationAnswer (CanonicalPolicy.normalLayer lay) high a=verificationAnswer lay high a := by
  fin_cases lay <;> rfl

theorem producer_rejection_broad (lay : Layer) (floor : Nat) :
    1000*2^256 ≤ 1001*(Finset.univ.filter fun a : HashOutput =>
      CanonicalPolicy.producerDecodeOut lay floor a=none).card := by
  classical
  let accepted := Finset.univ.filter fun a : HashOutput => CanonicalPolicy.producerDecodeOut lay floor a ≠ none
  let broad := Finset.univ.filter fun a : HashOutput =>
    (SigGolfCandidate.T3.decode (CanonicalPolicy.normalLayer lay) (encodingAnswer (CanonicalPolicy.normalLayer lay) a)).isSome
  have hsub : accepted ⊆ broad := by
    intro a ha
    obtain ⟨⟨ds,low⟩,hds⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp ha).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,Option.isSome_iff_exists.mpr ⟨ds,?_⟩⟩
    rw [encodingAnswer_normal]
    exact (CanonicalPolicy.producerDecodeAt_spec (CanonicalPolicy.producerDecodeOut_spec hds).2).1
  have hbound : accepted.card ≤ broadCount (CanonicalPolicy.normalLayer lay) * (2*2^128) :=
    (Finset.card_le_card hsub).trans (broad_encoding_card _)
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset HashOutput))
    (fun a => CanonicalPolicy.producerDecodeOut lay floor a = none)
  simp only [Finset.card_univ, Fintype.card_bitVec] at hpart
  change (Finset.univ.filter fun a : HashOutput => CanonicalPolicy.producerDecodeOut lay floor a=none).card + accepted.card = 2^256 at hpart
  have hsmall : 1001 * (broadCount (CanonicalPolicy.normalLayer lay) * (2*2^128)) ≤ 2^256 := by
    rw [broad_decoder_card]
    fin_cases lay <;> norm_num [CanonicalPolicy.normalLayer, EncodingCounting.rawAcceptedCount, SigGolfResearch.NonbinaryTop.Counting.count]
  omega

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open OracleComp OracleSpec ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def UnitNeighborDecode (lay : Layer) (reference : List Nat) (chain : Nat) (output : HashOutput) : Prop :=
  ∃ digits, encodingCanDecode lay output digits ∧
    digits.getD chain 0+1=reference.getD chain 0 ∧
    ∀ j, j ≠ chain → reference.getD j 0 ≤ digits.getD j 0

theorem marker_uniform_raw (lay : Layer) (reference : List Nat) (value : Digest)
    (href : CanonicalPolicy.decode lay value=some reference) (chain : Nat) :
    Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (371/4)/(2:ENNReal)^128 := by
  classical
  let normal := CanonicalPolicy.normalLayer lay
  have href' : decode normal value=some reference := href
  by_cases hc : chain<chainCount normal
  · let W := decodedWord href'
    let i : Fin (MixedCode.Code.n (code normal)) := ⟨chain,hc⟩
    let targets := EncodingTargets.targets normal (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => ∃ high : Bool, verificationAnswer normal high output∈targets |
          ($ᵗ HashOutput : ProbComp HashOutput)] := by
          apply probEvent_mono
          rintro answer - ⟨digits,⟨high,hd⟩,hlow,hrest⟩
          refine ⟨high, ?_⟩
          have hd' : decode normal (verificationAnswer normal high answer)=some digits := by
            rw [verificationAnswer_normal]
            exact hd
          refine (EncodingTargets.source_decoded_target hd' _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid href',decodedWord_valid hd',hlow,?_⟩
          intro j hj
          exact hrest j.val (fun he=>hj (Fin.ext he))
      _ ≤ _ := ClaudeWCT.W9.T3.Security.Wots.Enc.uniform_unit_neighbors normal W i
  · have hz : Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)]=0 := by
      apply probEvent_eq_zero
      rintro answer - ⟨digits,-,hlow,hrest⟩
      have hlen := (decode_length_sum href').1
      rw [List.getD_eq_default reference 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le


open SphincsSecurity.Concrete.UniformTableCompletion

noncomputable def rejectedAt (lay : Layer) (floor : Nat) : Finset HashOutput :=
  Finset.univ.filter fun a => CanonicalPolicy.producerDecodeOut lay floor a=none

theorem probEvent_rejected_le (lay : Layer) (floor : Nat) (p : HashOutput→Prop) :
    Pr[p | cell (rejectedAt lay floor)] ≤ 1001/1000*Pr[p | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [probEvent_eq_tsum_ite,probEvent_eq_tsum_ite,←ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ans=>?_
  split_ifs
  · rw [SPMF.probOutput_eq_apply,cell_apply,probOutput_uniformSample]
    split_ifs
    · have hc : ((1000:ENNReal)*2^256)≤1001*((rejectedAt lay floor).card:ENNReal) := by
        exact_mod_cast producer_rejection_broad lay floor
      calc ((rejectedAt lay floor).card:ENNReal)⁻¹ = 1001/(1001*((rejectedAt lay floor).card:ENNReal)) := by
            rw [ENNReal.div_eq_inv_mul,ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              mul_comm (1001:ENNReal)⁻¹,mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),mul_one]
        _ ≤ 1001/(1000*2^256) := ENNReal.div_le_div_left hc _
        _ = 1001/1000*((Fintype.card HashOutput:Nat):ENNReal)⁻¹ := by
          simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
          rw [ENNReal.div_eq_inv_mul,ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),div_eq_mul_inv]
          ring
    · exact zero_le
  · simp

theorem marker_rejected_le (lay : Layer) (floor : Nat) (reference : List Nat) (value : Digest)
    (href : CanonicalPolicy.decode lay value=some reference) (chain : Nat) :
    Pr[UnitNeighborDecode lay reference chain | cell (rejectedAt lay floor)] ≤ 93/(2:ENNReal)^128 := by
  calc _ ≤ 1001/1000*Pr[UnitNeighborDecode lay reference chain | ($ᵗ HashOutput : ProbComp HashOutput)] :=
      probEvent_rejected_le _ _ _
    _ ≤ 1001/1000*((371/4)/(2:ENNReal)^128) := mul_le_mul' le_rfl (marker_uniform_raw lay reference value href chain)
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
      norm_num

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.WCT9.CanonicalRates
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The LOW path bonus only helps: a word accepted through HIGH is accepted through LOW. -/
theorem producerDecodeAt_true_of_false {lay : Layer} {floor : Nat} {word : Digest} {digits : List Nat}
    (h : CanonicalPolicy.producerDecodeAt lay floor false word = some digits) :
    CanonicalPolicy.producerDecodeAt lay floor true word = some digits := by
  unfold CanonicalPolicy.producerDecodeAt at h ⊢
  cases hd : CanonicalPolicy.decode lay word with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h ⊢
      split_ifs at h with hc
      cases h
      have hb : ∀ d, CanonicalPolicy.pathReward lay false d ≤ CanonicalPolicy.pathReward lay true d := by
        intro d
        simp only [CanonicalPolicy.pathReward, CanonicalPolicy.pathBonus_false]
        omega
      rw [if_pos ⟨hc.1.trans (hb _), hc.2⟩]

/-- Path-aware rejected cell (both layer kinds; top bonus 3, lower bonus 4). Let `word` be accepted at `floor`
through some half, with digits `digits`. A rejected answer that still decodes to `digits` for some witness hint has
HIGH half `word`: if its LOW half were `word`, LOW would pass the producer predicate through the (better) LOW path
and the producer would have selected it (top: the producer prefers a good LOW; lower: the decodable LOW is spare). -/
theorem rejected_canDecode {lay : Layer} {floor : Nat} (hfloor : lay = 0 → floor = CanonicalPolicy.topFloor)
    {word : Digest} {low : Bool} {digits : List Nat}
    (href : CanonicalPolicy.producerDecodeAt lay floor low word = some digits) {a : HashOutput}
    (hrej : CanonicalPolicy.producerDecodeOut lay floor a = none)
    (hdec : encodingCanDecode lay a digits) :
    a.extractLsb' 128 128 = word := by
  obtain ⟨high, hd⟩ := hdec
  have hword : verificationAnswer lay high a = word :=
    canonical_decode_injective hd (CanonicalPolicy.producerDecodeAt_spec href).1
  have hrej' : CanonicalPolicy.producerDecodeAt lay floor (lowSelected lay a) (encodingAnswer lay a) = none := by
    unfold CanonicalPolicy.producerDecodeOut at hrej
    simpa only [Option.map_eq_none_iff] using hrej
  have htrue : CanonicalPolicy.producerDecodeAt lay floor true word = some digits := by
    cases low
    · exact producerDecodeAt_true_of_false href
    · exact href
  have hlowne : a.extractLsb' 0 128 = word → False := by
    intro hlw
    have hsel : lowSelected lay a = true := by
      by_cases hl : lay = 0
      · subst hl
        have hf := hfloor rfl
        subst hf
        have hg : topGood (a.extractLsb' 0 128) := by
          unfold topGood
          rw [hlw, htrue]
          rfl
        simp only [lowSelected, if_true, topChooseLow, decide_eq_true_eq]
        exact Or.inl hg
      · have hdw := (CanonicalPolicy.producerDecodeAt_spec href).1
        simp only [CanonicalPolicy.decode, CanonicalPolicy.normalLayer, if_neg hl] at hdw
        have hspare : lowerSpare (a.extractLsb' 0 128) := by
          rw [hlw]
          exact SigGolfCandidate.T3.decode_lowerSpare (by decide : (1 : Layer) ≠ 0) hdw
        simp [lowSelected, hl, hspare]
    rw [encodingAnswer_eq, hsel, if_pos rfl, hlw, htrue] at hrej'
    cases hrej'
  by_cases hl : lay = 0
  · subst hl
    have hread : verificationAnswer 0 high a = TopChoice.read high a := rfl
    rw [hread] at hword
    unfold TopChoice.read at hword
    split_ifs at hword
    · exact hword
    · exact (hlowne hword).elim
  · rw [verificationAnswer_eq_lower lay hl, verificationLow_lower lay hl] at hword
    split_ifs at hword
    · exact (hlowne hword).elim
    · exact hword

/-- Rejected-cell match bound (path-aware floors): `(1001/1000)/2^128 ≤ (7/4)/2^128`. -/
theorem canDecode_rejected_le {lay : Layer} {floor : Nat} (hfloor : lay = 0 → floor = CanonicalPolicy.topFloor)
    {word : Digest} {low : Bool} {digits : List Nat}
    (href : CanonicalPolicy.producerDecodeAt lay floor low word = some digits) :
    Pr[fun a => encodingCanDecode lay a digits | cell (rejectedAt lay floor)] ≤ 7/((4:ENNReal)*2^128) := by
  classical
  calc _ ≤ Pr[fun a : HashOutput => a.extractLsb' 128 128 = word | cell (rejectedAt lay floor)] := by
        apply probEvent_mono
        intro a ha hdec
        have hmem := SigGolfCandidate.T3.Security.Wots.Enc.Lazy.cell_nonzero_mem
          ((SPMF.mem_support_iff _ _).mp ha)
        have hrej : CanonicalPolicy.producerDecodeOut lay floor a = none := by
          simpa only [rejectedAt, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
        exact rejected_canDecode hfloor href hrej hdec
    _ ≤ 1001/1000*Pr[fun a : HashOutput => a.extractLsb' 128 128 = word |
          ($ᵗ HashOutput : ProbComp HashOutput)] := probEvent_rejected_le _ _ _
    _ = 1001/1000*(1/(2:ENNReal)^128) := by
        congr 1
        rw [probEvent_uniformSample]
        have hc := SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 128) (by decide)
          (fun v : BitVec 128 => v = word)
        have h1 : (Finset.univ.filter fun v : BitVec 128 => v = word).card = 1 := by
          rw [Finset.filter_eq' Finset.univ word]
          simp
        change (Finset.univ.filter fun a : HashOutput => a.extractLsb' 128 128 = word).card = _ at hc
        rw [hc, h1, Fintype.card_bitVec]
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_one]
        rw [show (2:ENNReal)^256 = 2^128*2^128 by rw [← pow_add], ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
          mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, one_div]
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
        ENNReal.toReal_one]
      norm_num

end ClaudeWCT.WCT9.CanonicalRates

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def MarkEntry (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (a : ChainAddr) (entry : Entry) : Prop :=
  ∃ (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) (digits : List Nat),
    Extract.msgFits a.key.lay message ∧ entry.1 = encRow a.key message counter pad ∧
      referenceInput T messages a.key ≠ some (encRow a.key message counter pad) ∧
      WCT9.encodingCanDecode a.key.lay entry.2 digits ∧
      digits.getD a.chain 0 + 1 = (referenceDigits T messages a.key).getD a.chain 0 ∧
      ∀ i, i ≠ a.chain → (referenceDigits T messages a.key).getD i 0 ≤ digits.getD i 0

theorem markerAt_iff (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) (a : ChainAddr) :
    MarkerAt T messages trace a ↔ ∃ entry ∈ trace, MarkEntry T messages a entry := by
  constructor
  · rintro ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩
    exact ⟨_, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
  · rintro ⟨⟨input, answer⟩, hmem, message, counter, pad, digits, hfit, rfl, hne, hd, hlow, hrest⟩
    exact ⟨message, counter, pad, answer, digits, hfit, hmem, hne, hd, hlow, hrest⟩

theorem markEntry_cell_le_raw (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (371/4)/(2:ENNReal)^128 := by
  obtain ⟨value,hvalue⟩ := referenceDigits_decode T messages a.key
  apply le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.marker_uniform_raw a.key.lay
    (referenceDigits T messages a.key) value hvalue a.chain)
  rintro answer - ⟨message,counter,pad,digits,hfit,he,hne,hd,hlow,hrest⟩
  exact ⟨digits,hd,hlow,hrest⟩

theorem markEntry_cell_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      93/(2:ENNReal)^128 := by
  refine (markEntry_cell_le_raw T messages x a).trans (ENNReal.div_le_div_right ?_ _)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem markEntry_rejected_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (a : ChainAddr) (remaining : Nat) :
    Pr[fun ans => MarkEntry T messages a (x,ans) | cell (rejectedAnswers a.key.lay remaining)] ≤
      93/(2:ENNReal)^128 := by
  obtain ⟨value,hvalue⟩ := referenceDigits_decode T messages a.key
  apply le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.marker_rejected_le a.key.lay
    (WCT9.CanonicalPolicy.threshold a.key.lay.val remaining)
    (referenceDigits T messages a.key) value hvalue a.chain)
  rintro answer - ⟨message,counter,pad,digits,hfit,he,hne,hd,hlow,hrest⟩
  exact ⟨digits,hd,hlow,hrest⟩

theorem markEntry_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (k : CellKey) (e : k.cells) (p : CanonGraph.LeafPos × Fin 58) :
    Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
      MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      93/(2:ENNReal)^128 := by
  by_cases hp : p.1=e.val.1.1
  · refine (probEvent_mono fun ans _ h => h.2).trans ?_
    unfold cellInit
    split_ifs
    · rw [Lazy.probEvent_cell_univ]
      exact markEntry_cell_le T messages _ _
    · split
      · rw [Lazy.probEvent_cell_univ]
        exact markEntry_cell_le T messages _ _
      · have h := markEntry_rejected_le T messages (Enc.encInput e.val) (Enc.chainAt p) ‹Nat›
        rw [show (Enc.chainAt p).key.lay=e.val.1.1.lay from by rw [←hp]; rfl] at h
        exact h
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
    rintro ans - ⟨hsrc,message,counter,pad,digits,hfit,he,hrest⟩
    exact hp (Enc.encInput_leaf hsrc.1 (he.trans rfl :
      Enc.encInput e.val=encRow (Enc.leafOf p.1) message counter pad)).symm

theorem markEntry_sum_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (k : CellKey) (e : k.cells) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      5022/(2:ENNReal)^128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T messages (Enc.chainAt p) (Enc.encInput e.val,ans) | cell (cellInit k e)] ≤
      if p.1=e.val.1.1 then (if p.2.val<54 then 93/(2:ENNReal)^128 else 0) else 0 := by
    intro p
    split_ifs with hp hc
    · exact markEntry_init_le T messages k e p
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsource,-⟩
      have hcount := chainCount_le_54 p.1.lay
      have hchain : p.2.val < chainCount p.1.lay := hsource.2
      omega
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨hsrc,message,counter,pad,digits,hfit,he,hrest⟩
      exact hp (Enc.encInput_leaf hsrc.1 (he.trans rfl :
        Enc.encInput e.val=encRow (Enc.leafOf p.1) message counter pad)).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans ?_
  rw [Fintype.sum_prod_type,Finset.sum_eq_single e.val.1.1 (fun L _ hL=>by simp [hL]) (by simp)]
  simp only [if_true]
  have hn : (Finset.univ.filter (fun i : Fin 58 => i.val<54)).card=54 := by decide
  rw [←Finset.sum_filter,Finset.sum_const,hn,nsmul_eq_mul,←mul_div_assoc]
  gcongr
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem layerCounterSearch_first (T : Answers) (lay : Layer) (floor tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel start k (digits : List Nat × Bool), k<fuel →
      (∀i<k,WCT9.CanonicalPolicy.producerDecodeOut lay floor (T (.inl (.inr
        (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (start+i)))))))=none) →
      WCT9.CanonicalPolicy.producerDecodeOut lay floor (T (.inl (.inr
        (pad64 (WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (start+k)))))))=some digits →
      evalWithAnswerFn T (WCT9.CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg start fuel)=
        some (BitVec.ofNat 32 (start+k),digits) := by
  intro fuel
  induction fuel with
  | zero => intro start k digits hk; omega
  | succ fuel ih =>
      intro start k digits hk hprev hvalid
      simp only [WCT9.CanonicalPolicy.layerCounterSearchAt,evalWithAnswerFn_bind,eval_publicHash]
      rcases k with _ | k
      · simp only [Nat.add_zero] at hvalid ⊢
        rw [hvalid]
        rfl
      · have h0 := hprev 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [h0]
        have h := ih (start+1) k digits (by omega)
          (fun i hi=>by rw [show start+1+i=start+(i+1) by omega];exact hprev (i+1) (by omega))
          (by rw [show start+1+k=start+(k+1) by omega];exact hvalid)
        rw [show start+(k+1)=start+1+k by omega]
        exact h

theorem reached_valid_reference {T : Answers} {messages : LeafAddr→WCT9.LayerMsg}
    {L : LeafAddr} {input : HashInput} (hr : Reached T messages L input)
    {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    {digits : List Nat × Bool}
    (hv : WCT9.CanonicalPolicy.producerDecodeOut L.lay
      (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (T (.inl (.inr input)))=some digits) :
    referenceInput T messages L=some input := by
  obtain ⟨c,⟨hc,oldRemaining,hctx',hprev⟩,rfl⟩ := hr
  rw [hctx] at hctx'
  cases hctx'
  have hs : searchOf T messages L remaining=some (BitVec.ofNat 32 c,digits) := by
    unfold searchOf
    have h := layerCounterSearch_first T L.lay _ L.tree L.leaf (messages L)
      (WCT9.searchLimit L.lay) 0 c digits hc
      (fun i hi=>by rw [Nat.zero_add,←encRow_zero]; rw [←decodeRow_answer];exact hprev i hi)
      (by rw [Nat.zero_add,←encRow_zero];exact hv)
    simpa only [Nat.zero_add] using h
  have href : referenceSearch T messages L=some (BitVec.ofNat 32 c,digits) := by
    exact Option.bind_eq_some_iff.mpr ⟨remaining,hctx,hs⟩
  unfold referenceInput
  rw [href]
  rfl

theorem referenceInput_eq_of_noncell (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x)
    (L : CanonGraph.LeafPos) (hsource : L.Source) (message : WCT9.LayerMsg)
    (counter : BitVec 32) (pad : RowPad) (hfit : Extract.msgFits L.lay message)
    (he : x=encRow (Enc.leafOf L) message counter pad) :
    referenceInput T messages (Enc.leafOf L)=some x := by
  let entry : Enc.EncIndex := Enc.encIdx L hsource message counter pad hfit
  have hin : Enc.encInput entry=x := (Enc.encInput_encIdx L hsource message counter pad hfit).trans he.symm
  have hleaf : Enc.leafOf entry.1.1=Enc.leafOf L := rfl
  have hnc : ¬(entry∈freeSet T messages ∨ entry∈rejectedSet T messages) :=
    fun hc=>hx ⟨entry,hc,hin⟩
  have hreached : Reached T messages (Enc.leafOf L) x := by
    by_contra hfree
    apply hnc
    left
    change ¬Reached T messages (Enc.leafOf entry.1.1) (Enc.encInput entry)
    rw [hin,hleaf]
    exact hfree
  obtain ⟨c,hreach,hxrow⟩ := hreached
  obtain ⟨hc,remaining,hctx,hprev⟩ := hreach
  cases hs : decodeRow T (Enc.leafOf L) (WCT9.CanonicalPolicy.threshold L.lay.val remaining)
      (messages (Enc.leafOf L)) c with
  | none =>
      exact False.elim (hnc (Or.inr
        ⟨c,remaining,⟨hc,remaining,hctx,hprev⟩,hin.trans hxrow,hctx,hs⟩))
  | some ds =>
      have hvalid : WCT9.CanonicalPolicy.producerDecodeOut L.lay
          (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (T (.inl (.inr x)))=some ds := by
        rw [decodeRow_answer,←hxrow] at hs
        exact hs
      have href := reached_valid_reference ⟨c,⟨hc,remaining,hctx,hprev⟩,hxrow⟩ hctx hvalid
      exact href


theorem markEntry_noncell (T : Answers) (messages : LeafAddr→WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x)
    (p : CanonGraph.LeafPos×Fin 58) :
    ¬(WotsExtract.SourceChain7 (Enc.chainAt p) ∧
      MarkEntry T messages (Enc.chainAt p) (x,T (.inl (.inr x)))) := by
  rintro ⟨hsrc,message,counter,pad,digits,hfit,he,hne,hdec,rest⟩
  exact hne (he ▸ referenceInput_eq_of_noncell T messages x hx p.1 hsrc.1
    message counter pad hfit he)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Enc
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def MatchEntry (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (entry : Entry) : Prop :=
  ∃ (L : CanonGraph.LeafPos) (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad),
    L.Source ∧ Extract.msgFits L.lay message ∧ entry.1 = encRow (Enc.leafOf L) message counter pad ∧
      referenceInput T messages (Enc.leafOf L) ≠ some (encRow (Enc.leafOf L) message counter pad) ∧
      referenceSearch T messages (Enc.leafOf L) ≠ none ∧
      WCT9.encodingCanDecode L.lay entry.2 (referenceDigits T messages (Enc.leafOf L))

theorem matchEntry_cell_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (e : Enc.EncIndex) :
    Pr[fun ans => MatchEntry T messages (Enc.encInput e,ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      7/((4:ENNReal)*2^128) := by
  apply le_trans (probEvent_mono ?_) (WCT9.probability_encodingCanDecode_le e.1.1.lay
    (referenceDigits T messages (Enc.leafOf e.1.1)))
  rintro answer - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs,hdec⟩
  have hL := Enc.encInput_leaf hsource he
  subst hL
  exact hdec

private theorem bind_at_some {α β : Type} (o : Option α) (f : α → Option β)
    {a : α} {b : β} (ho : o = some a) (h : o.bind f = some b) : f a = some b := by
  subst o
  exact h

theorem referenceSearch_producerDecode (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    {c : BitVec 32} {digits : List Nat} {low : Bool} (hs : referenceSearch T messages L=some (c,digits,low)) :
    WCT9.CanonicalPolicy.producerDecodeOut L.lay (WCT9.CanonicalPolicy.threshold L.lay.val remaining)
      (T (.inl (.inr (encRow L (messages L) c 0))))=some (digits,low) := by
  have hs' : searchOf T messages L remaining=some (c,digits,low) := by
    exact bind_at_some _ _ hctx hs
  have h := counterSearch_decode T L.lay _ L.tree L.leaf (messages L)
    (WCT9.searchLimit L.lay) 0 c (digits,low) hs'
  rw [eval_publicHash,←encRow_zero] at h
  exact h

/-- Path-aware floors: the reference word was accepted through the half the producer selected. -/
theorem reference_accepted (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) {remaining : Nat} (hctx : referenceContext T messages L=some remaining)
    (hs : referenceSearch T messages L≠none) :
    ∃ (word : Digest) (low : Bool), WCT9.CanonicalPolicy.producerDecodeAt L.lay
      (WCT9.CanonicalPolicy.threshold L.lay.val remaining) low word=some (referenceDigits T messages L) := by
  obtain ⟨⟨c,digits,low⟩,hfound⟩ := Option.ne_none_iff_exists'.mp hs
  have href : referenceDigits T messages L=digits := by
    simp only [referenceDigits,hfound,Option.map_some,Option.getD_some]
  rw [href]
  exact ⟨_,_,(WCT9.CanonicalPolicy.producerDecodeOut_spec (referenceSearch_producerDecode T messages L hctx hfound)).2⟩

theorem threshold_top_floor (lay : Layer) (remaining : Nat) :
    lay = 0 → WCT9.CanonicalPolicy.threshold lay.val remaining = WCT9.CanonicalPolicy.topFloor := by
  rintro rfl
  simp [WCT9.CanonicalPolicy.threshold]

theorem matchEntry_init_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (e : (cellKey T messages).cells) :
    Pr[fun ans => MatchEntry T messages (Enc.encInput e.val,ans) |
      cell (cellInit (cellKey T messages) e)] ≤ 7/((4:ENNReal)*2^128) := by
  unfold cellInit
  split_ifs
  · rw [Lazy.probEvent_cell_univ]
    exact matchEntry_cell_le T messages e.val
  · split
    · rw [Lazy.probEvent_cell_univ]
      exact matchEntry_cell_le T messages e.val
    · rename_i hctx
      by_cases hs : referenceSearch T messages (Enc.leafOf e.val.1.1) = none
      · apply le_trans (le_of_eq (probEvent_eq_zero ?_)) zero_le
        rintro ans - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs',hd⟩
        have hL := Enc.encInput_leaf hsource he
        subst hL
        exact hs' hs
      · obtain ⟨word,low,hword⟩ := reference_accepted T messages (Enc.leafOf e.val.1.1) hctx hs
        refine le_trans (probEvent_mono ?_) (WCT9.CanonicalRates.canDecode_rejected_le
          (threshold_top_floor e.val.1.1.lay _) hword)
        rintro ans - ⟨L,message,counter,pad,hsource,hfit,he,hne,hs',hd⟩
        have hL := Enc.encInput_leaf hsource he
        subst hL
        exact hd

theorem matchEntry_noncell (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (x : HashInput) (hx : ¬Lazy.IsCell Enc.encInput (cellKey T messages).cells x) :
    ¬MatchEntry T messages (x,T (.inl (.inr x))) := by
  rintro ⟨L,message,counter,pad,hsource,hfit,he,hne,hselected,hdecode⟩
  exact hne (he ▸ referenceInput_eq_of_noncell T messages x hx L hsource message counter pad hfit he)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Enc
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def markerCount (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  Lazy.marks (fun p : CanonGraph.LeafPos × Fin 58 => fun entry =>
    WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T messages (Enc.chainAt p) entry) trace

noncomputable def matchCount (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  Lazy.marks (fun _ : Unit => MatchEntry T messages) trace

theorem lazy_marker_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    [Fintype (cellKey T messages).cells] [DecidableEq (cellKey T messages).cells]
    {α : Type} (program : OracleComp RefWorld α) :
    ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (markerCount T messages result.1.2.toList:ENNReal) ≤
      (5022/(2:ENNReal)^128) *
        ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal) := by
  refine (Lazy.lazy_marks_init_le Enc.encInput (cellKey T messages).cells Enc.encInput_injective
    T (fun p : CanonGraph.LeafPos × Fin 58 => fun entry =>
      WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T messages (Enc.chainAt p) entry)
    _ (cellInit (cellKey T messages)) (cellInit_nonempty _)
    (fun e => markEntry_sum_init_le T messages _ e)
    (fun x hx p => markEntry_noncell T messages x hx p) program).trans ?_
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  exact_mod_cast Enc.cellCount_le_encoding _ _

theorem lazy_match_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    [Fintype (cellKey T messages).cells] [DecidableEq (cellKey T messages).cells]
    {α : Type} (program : OracleComp RefWorld α) :
    ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (matchCount T messages result.1.2.toList:ENNReal) ≤
      (7/((4:ENNReal)*2^128)) *
        ∑' result, Pr[=result | (simulateQ (Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal) := by
  refine (Lazy.lazy_marks_init_le Enc.encInput (cellKey T messages).cells Enc.encInput_injective
    T (fun _ : Unit => MatchEntry T messages) _ (cellInit (cellKey T messages)) (cellInit_nonempty _)
    (fun e => by simpa using matchEntry_init_le T messages e)
    (fun x hx _ => matchEntry_noncell T messages x hx) program).trans ?_
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  exact_mod_cast Enc.cellCount_le_encoding _ _

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem referenceDigits_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (leaf : LeafAddr) (hl : WotsExtract.SourceLeaf7 leaf) :
    referenceDigits T' messages' leaf=referenceDigits T messages leaf := by
  unfold referenceDigits
  rw [(source_reference_congr T T' messages messages' hm hd hl).2]

theorem referenceInput_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (leaf : LeafAddr) (hl : WotsExtract.SourceLeaf7 leaf) :
    referenceInput T' messages' leaf=referenceInput T messages leaf := by
  unfold referenceInput
  rw [(source_reference_congr T T' messages messages' hm hd hl).2,hm leaf hl]

theorem markEntry_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (entry : Entry) :
    MarkEntry T' messages' a entry ↔ MarkEntry T messages a entry := by
  unfold MarkEntry
  rw [referenceInput_decisions hm hd a.key ha.1, referenceDigits_decisions hm hd a.key ha.1]

theorem matchEntry_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (entry : Entry) :
    MatchEntry T' messages' entry ↔ MatchEntry T messages entry := by
  unfold MatchEntry
  apply exists_congr
  intro leaf
  apply exists_congr
  intro message
  apply exists_congr
  intro counter
  apply exists_congr
  intro pad
  by_cases hl : leaf.Source
  · have hs : WotsExtract.SourceLeaf7 (Enc.leafOf leaf) := hl
    rw [referenceInput_decisions hm hd _ hs, referenceDigits_decisions hm hd _ hs,
      (source_reference_congr T T' messages messages' hm hd hs).2]
  · simp only [hl,false_and]

theorem markerCount_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (trace : List Entry) :
    markerCount T' messages' trace=markerCount T messages trace := by
  apply congrArg (fun mark => SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks mark trace)
  funext p entry
  apply propext
  by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
  · exact and_congr_right fun _ => markEntry_decisions hm hd _ hs entry
  · simp [hs]

theorem matchCount_decisions {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
    (hd : DecisionsAgree T T' messages) (trace : List Entry) :
    matchCount T' messages' trace=matchCount T messages trace := by
  apply congrArg (fun mark => SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks mark trace)
  funext p entry
  exact propext (matchEntry_decisions hm hd entry)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cells_count_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (count : Answers → (LeafAddr → WCT9.LayerMsg) → List Entry → Nat) (rate : ENNReal)
    (hcount : ∀ {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg},
      (∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf) →
      DecisionsAgree T T' messages → ∀ trace, count T' messages' trace=count T messages trace)
    (hlazy : ∀ (T : Answers) (messages : LeafAddr → WCT9.LayerMsg)
        (program : OracleComp RefWorld (Option (Bool × Nat))),
      ∑' result, Pr[=result | (simulateQ (SigGolfCandidate.T3.Security.Wots.Enc.Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
        (SphincsSecurity.QueryPause.traced SigGolfCandidate.T3.Security.Wots.Enc.Lazy.obs program)).run (cellInit (cellKey T messages))] *
        (count T messages result.1.2.toList:ENNReal) ≤ rate *
        ∑' result, Pr[=result | (simulateQ (SigGolfCandidate.T3.Security.Wots.Enc.Lazy.lazyImpl Enc.encInput (cellKey T messages).cells T)
          (SphincsSecurity.QueryPause.traced SigGolfCandidate.T3.Security.Wots.Enc.Lazy.obs program)).run (cellInit (cellKey T messages))] *
          (((result.1.2.toList.filter fun entry => decide (EncodingInput entry.1)).length:Nat):ENNReal)) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub)
          (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable
          (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          (count (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
            (sourceMessages (eagerAnswers U privateTable pub))).cells pub y))
            (sourceMessages (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
              (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)))
            (traceOf (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub)
              (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r.2) : ENNReal) ≤
      rate * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub)
          (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable
          (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable
            (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) : ENNReal) := by
  have hleft := cell_transfer adversary q U hU privateTable pub
      (fun s => (count s.answers (sourceMessages s.answers) s.trace : ENNReal))
      (fun tr => (count (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr : ENNReal))
      (fun y hy r => by
        dsimp only [mkSample]
        rw [hcount (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)])
  simp only [mkSample] at hleft
  rw [hleft, cell_transfer adversary q U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y _ r => encodingCount_mkSample _ r)]
  exact hlazy _ _ _
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem reference_markerCount_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s *
      (markerCount s.answers (sourceMessages s.answers) s.trace : ENNReal) ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  apply reference_cells_le adversary q
  intro privateTable pub
  exact cells_count_le adversary q (PairedReference.referenceInputs adversary)
    Finset.subset_union_left privateTable pub markerCount _
    (fun hm hd trace => markerCount_decisions hm hd trace)
    (fun T messages program => lazy_marker_le T messages program)

theorem reference_matchCount_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s *
      (matchCount s.answers (sourceMessages s.answers) s.trace : ENNReal) ≤
      (7/((4:ENNReal)*2^128)) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  apply reference_cells_le adversary q
  intro privateTable pub
  exact cells_count_le adversary q (PairedReference.referenceInputs adversary)
    Finset.subset_union_left privateTable pub matchCount _
    (fun hm hd trace => matchCount_decisions hm hd trace)
    (fun T messages program => lazy_match_le T messages program)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem markerCount_marks_eq (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) :
    markerCount T messages trace = (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
      WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt T messages trace (Enc.chainAt p)).card := by
  unfold markerCount SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [markerAt_iff]
  constructor
  · rintro ⟨e,he,hs,hm⟩
    exact ⟨hs,e,he,hm⟩
  · rintro ⟨hs,e,he,hm⟩
    exact ⟨e,he,hs,hm⟩

theorem reference_marker_sum_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkerAt s.answers (sourceMessages s.answers) s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  refine le_trans (le_of_eq ?_) (reference_markerCount_le adversary q)
  simp only [probEvent_eq_tsum_ite,PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  rw [markerCount_marks_eq,Finset.card_filter,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

theorem matchCount_pos {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace : List Entry}
    {L : LeafAddr} (hsource : WotsExtract.SourceLeaf7 L)
    (hs : referenceSearch T messages L ≠ none) (hm : EncodingMatchAt T messages trace L) :
    1 ≤ matchCount T messages trace := by
  obtain ⟨message,counter,pad,answer,hfit,hmem,hne,-,hdecode⟩ := hm
  have ht31 : L.tree < 2^31 := lt_of_lt_of_le hsource.1
    (Nat.pow_le_pow_right (by decide) (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
  have hl12 : L.leaf < 4096 := lt_of_lt_of_le hsource.2 (by
    calc 2^height L.lay ≤ 2^12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le L.lay)
         _ = 4096 := by norm_num)
  unfold matchCount SigGolfCandidate.T3.Security.Wots.Enc.Lazy.marks
  apply Nat.succ_le_of_lt
  apply Finset.card_pos.mpr
  refine ⟨(),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  refine ⟨(encRow L message counter pad,answer),hmem,?_⟩
  exact ⟨⟨L.lay,⟨L.tree,ht31⟩,⟨L.leaf,hl12⟩⟩,message,counter,pad,hsource,hfit,rfl,hne,hs,hdecode⟩

theorem reference_encodingMatch_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ L, WotsExtract.SourceLeaf7 L ∧
      referenceSearch s.answers (sourceMessages s.answers) L ≠ none ∧
      EncodingMatchAt s.answers (sourceMessages s.answers) s.trace L |
        PairedReference.referenceExperiment adversary q] ≤
      (7/((4:ENNReal)*2^128)) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (encodingCount s : ENNReal) := by
  refine le_trans ?_ (reference_matchCount_le adversary q)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro s
  split_ifs with h
  · obtain ⟨L,hsource,hs,hm⟩ := h
    rw [PMF.probOutput_eq_apply]
    exact le_mul_of_one_le_right' (by exact_mod_cast matchCount_pos hsource hs hm)
  · exact zero_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsEncodingContact ====
section


namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp

theorem contact_mono {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace trace' : List Entry} {a : ChainAddr}
    (h : CanonicalRef.ContactAt T messages trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    CanonicalRef.ContactAt T messages trace' a := by
  obtain ⟨hd, v, ans, hm, hv⟩ := h
  exact ⟨hd, v, ans, hsub _ hm, hv⟩
def ContactFirstAt (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T messages (trace.take k) a ∧ ¬MarkerAt T messages (trace.take k) a ∧ MarkerAt T messages trace a
def CFK (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Prop :=
  ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactFirstAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)
noncomputable def contacts (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)).card
theorem contacts_mono (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) {trace trace' : List Entry} (hsub : ∀ e ∈ trace, e ∈ trace') :
    contacts T messages trace ≤ contacts T messages trace' := by
  unfold contacts
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, contact_mono hp.2 hsub⟩
noncomputable def costL (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 93 * contacts T messages hist else 0) + costL T messages F (hist ++ [e]) rest
theorem costL_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) :
    ∀ (trace hist : List Entry), costL T messages F hist trace ≤ 93 * trace.length * contacts T messages (hist ++ trace) := by
  intro trace
  induction trace with
  | nil => intro hist; simp [costL]
  | cons e rest ih =>
      intro hist
      unfold costL
      have h1 : contacts T messages hist ≤ contacts T messages (hist ++ e :: rest) :=
        contacts_mono T messages (fun x hx => List.mem_append_left _ hx)
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have h3 : (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 93 * contacts T messages hist else 0) ≤ 93 * contacts T messages hist := by
        split_ifs <;> omega
      rw [List.length_cons]
      nlinarith
theorem cfk_new {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {h : List Entry} {e : Entry} (hold : ¬ CFK T messages h) (hnew : CFK T messages (h ++ [e])) :
    ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
      MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) e ∧ ¬ MarkerAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := by
  obtain ⟨p, hs, k, hc, hnm, hm⟩ := hnew
  by_cases hk : k ≤ h.length
  · rw [List.take_append_of_le_length hk] at hc hnm
    have hnot : ¬ MarkerAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := fun hmh => hold ⟨p, hs, k, hc, hnm, hmh⟩
    refine ⟨p, hs, contact_mono hc (fun x hx => List.mem_of_mem_take hx), ?_, hnot⟩
    obtain ⟨entry, hmem, hme⟩ := (markerAt_iff T messages _ _).mp hm
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact absurd ((markerAt_iff T messages _ _).mpr ⟨entry, hmem, hme⟩) hnot
    · exact hme
  · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)] at hnm
    exact absurd hm hnm
noncomputable def cfCharge (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x then 93 * contacts T messages h.toList else 0
  | _ => 0
theorem costL_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    costL T messages F h.toList (Lazy.obs input answer * tail).toList =
      cfCharge T messages F h input + costL T messages F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, cfCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, costL, cfCharge]
  · simp [Lazy.obs, cfCharge]
theorem cfk_nil (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) : ¬ CFK T messages [] := by
  rintro ⟨p, -, k, -, -, hm⟩
  obtain ⟨entry, hmem, -⟩ := (markerAt_iff T messages _ _).mp hm
  simp at hmem
section Step
variable [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, Fintype k] [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, DecidableEq k]
theorem cf_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 93 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T input).run allowed] *
        (if CFK T messages (h * Lazy.obs input result.1).toList then (1 : ENNReal) else 0) ≤
      (if CFK T messages h.toList then (1 : ENNReal) else 0) + (2 ^ 128 : ENNReal)⁻¹ * (cfCharge T messages F h input : ENNReal) := by
  classical
  by_cases hold : CFK T messages h.toList
  · rw [if_pos hold]
    refine le_trans ?_ le_self_add
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (indicator_le_one _)).trans ?_
    exact Lazy.tsum_probOutput_mul_le_self _ _
  rw [if_neg hold, zero_add]
  rcases input with (n | x) | u
  · rw [Lazy.lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
  · by_cases hx : Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x
    · rw [Lazy.lazyImpl_cell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_map_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, cfCharge, if_pos hx]
      set e₀ := Lazy.cellOf ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx with he₀
      have hx₀ : ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val = x := Lazy.cellOf_input ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx
      by_cases hq : ∃ ans₀, (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        refine le_trans (le_of_eq ?_) zero_le
        apply ENNReal.tsum_eq_zero.mpr
        intro ans
        by_cases hne : ans = ans₀
        · subst hne
          rw [if_neg, mul_zero]
          intro hnew
          obtain ⟨p, -, -, hme, hnm⟩ := cfk_new hold hnew
          rw [← hx₀] at hme
          exact hnm ((markerAt_iff T messages _ _).mpr ⟨_, hans₀, hme⟩)
        · rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne), zero_mul]
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        let S := Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
          WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages h.toList (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)
        calc _ = Pr[fun ans => CFK T messages (h.toList ++ [(x, ans)]) | cell (init e₀)] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ans => ?_
              split_ifs <;> simp
          _ ≤ Pr[fun ans => ∃ p ∈ S, MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] := by
              apply probEvent_mono
              intro ans _ hnew
              obtain ⟨p, hs, hcon, hme, -⟩ := cfk_new hold hnew
              refine ⟨p, ?_, hme⟩
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hs, hcon⟩
          _ ≤ ∑ p ∈ S, Pr[fun ans => MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] :=
              probEvent_exists_finset_le_sum S _ _
          _ ≤ ∑ p ∈ S, 93 / (2 : ENNReal) ^ 128 := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hsrc : WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := by
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
                exact hp.1
              rw [← hx₀]
              exact (probEvent_mono fun ans _ h => ⟨hsrc, h⟩).trans (hcell e₀ p)
          _ = (2 ^ 128 : ENNReal)⁻¹ * ((93 * contacts T messages h.toList : Nat) : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              unfold contacts
              push_cast
              rw [div_eq_mul_inv]
              ring
    · rw [Lazy.lazyImpl_other ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_pure_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      rw [if_neg]
      · exact zero_le
      · intro hnew
        obtain ⟨p, hs, -, hme, -⟩ := cfk_new hold hnew
        exact hother x hx p ⟨hs, hme⟩
  · rw [Lazy.lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
theorem lazy_cf_le {α : Type} (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 93 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (C : OracleComp RefWorld α) :
    ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T) (SphincsSecurity.QueryPause.traced Lazy.obs C)).run
        init] * (if CFK T messages z.1.2.toList then (1 : ENNReal) else 0) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
        (SphincsSecurity.QueryPause.traced Lazy.obs C)).run init] *
          (costL T messages F [] z.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_history_potential_le Lazy.obs (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
    (fun h st => Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h st)
    (fun h st hc input result hr =>
      Lazy.consistent_step ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_injective T init h st hc input result hr)
    (fun C' h st hc => by
      rw [← Lazy.lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail (Lazy.aux T)
        (Lazy.aux_neverFail T) _ st (hc.nonempty ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F hinit)))
    (fun h _ => if CFK T messages h.toList then (1 : ENNReal) else 0) (2 ^ 128 : ENNReal)⁻¹
    (fun h tail => costL T messages F h.toList tail.toList) (cfCharge T messages F)
    (fun h => by simp [costL]) (fun h input answer tail => costL_step T messages F h input answer tail)
    (fun h st hc input => cf_step T messages F init hcell hother h st hc input)
    C 1 init (Lazy.consistent_one ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init)
  simp only [one_mul] at key
  rw [if_neg (by simpa using cfk_nil T messages), zero_add] at key
  simpa using key
end Step

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
variable {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
  (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
  (hd : DecisionsAgree T T' messages)
  (hnon : ∀ query, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc query → T' query=T query)
include hm hd hnon

theorem frontier_decisions (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.frontierValue T' messages' a=CanonicalRef.frontierValue T messages a := by
  have hs : WCT9.wotsSeed T' a.key.lay a.key.tree a.key.leaf a.chain =
      WCT9.wotsSeed T a.key.lay a.key.tree a.key.leaf a.chain :=
    ClaudeWCT.W9.T3.Security.Wots.Mask.wotsSeed_congr_cells _ _ _ fun p => hnon (.inr (.inl _)) trivial
  -- C3 (#866): the frontier is the chain of the current scheme.
  unfold CanonicalRef.frontierValue CanonicalRef.depth ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
  rw [referenceDigits_decisions hm hd a.key ha.1,hs]
  exact (ClaudeWCT.W9.T3.Security.Wots.Enc.respects_chainW _ _ _ _ _ _ _).eval_eq hnon

theorem contact_decisions (trace : List Entry) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.ContactAt T' messages' trace a ↔ CanonicalRef.ContactAt T messages trace a := by
  unfold CanonicalRef.ContactAt
  rw [frontier_decisions hm hd hnon a ha]
  unfold CanonicalRef.depth
  rw [referenceDigits_decisions hm hd a.key ha.1]

omit hnon in
theorem marker_decisions (trace : List Entry) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.MarkerAt T' messages' trace a ↔ CanonicalRef.MarkerAt T messages trace a := by
  rw [markerAt_iff,markerAt_iff]
  exact exists_congr fun e => and_congr_right fun _ => markEntry_decisions hm hd a ha e

theorem cfk_decisions (trace : List Entry) : CFK T' messages' trace ↔ CFK T messages trace := by
  unfold CFK ContactFirstAt
  refine exists_congr fun p => and_congr_right fun hp => exists_congr fun k => ?_
  rw [contact_decisions hm hd hnon _ _ hp,marker_decisions hm hd _ _ hp,
    marker_decisions hm hd _ _ hp]

theorem contacts_decisions (trace : List Entry) : contacts T' messages' trace=contacts T messages trace := by
  unfold contacts
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_congr_right fun hp => contact_decisions hm hd hnon trace _ hp
end Congr

noncomputable def cfInd (s : RefSample) : ENNReal := if CFK s.answers (sourceMessages s.answers) s.trace then 1 else 0
noncomputable def cfCost (s : RefSample) : ENNReal :=
  ((93*s.trace.length*contacts s.answers (sourceMessages s.answers) s.trace:Nat):ENNReal)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cells_cf_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfInd (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfCost (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) := by
  have hleft := cell_transfer adversary q U hU privateTable pub cfInd
      (fun tr => if CFK (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr then (1:ENNReal) else 0)
      (fun y hy r => by
        unfold cfInd mkSample
        rw [propext (cfk_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _)])
  have hright := cell_transfer adversary q U hU privateTable pub cfCost
      (fun tr => ((93*tr.length*contacts (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr:Nat):ENNReal))
      (fun y hy r => by
        unfold cfCost mkSample
        rw [contacts_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _])
  rw [hleft,hright]
  refine (lazy_cf_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells
    (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))))
    (cellInit_nonempty _)
    (fun e p => markEntry_init_le _ _ _ e p)
    (fun x hx p => markEntry_noncell _ _ x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  have := costL_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells z.1.2.toList []
  rw [List.nil_append] at this
  exact_mod_cast this

theorem reference_cfInd_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact reference_cells_le adversary q cfInd cfCost _
    (fun privateTable pub => cells_cf_le adversary q (PairedReference.referenceInputs adversary)
      Finset.subset_union_left privateTable pub)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem chainAt_injective : Function.Injective Enc.chainAt := by
  rintro ⟨⟨lay, tree, leaf⟩, i⟩ ⟨⟨lay', tree', leaf'⟩, i'⟩ h
  simp only [Enc.chainAt, Enc.leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hl⟩, hi⟩ := h
  have : tree = tree' := Fin.ext ht
  have : leaf = leaf' := Fin.ext hl
  have : i = i' := Fin.ext hi
  subst tree leaf i
  rfl
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, Enc.chainAt p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3M.Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
theorem contacts_le_contactCount (s : RefSample) : contacts s.answers (sourceMessages s.answers) s.trace ≤ Normalized.Contacts.contactCount s := by
  unfold contacts Normalized.Contacts.contactCount
  refine Finset.card_le_card_of_injOn (fun p => Enc.chainAt p) ?_ (fun p _ p' _ h => chainAt_injective h)
  intro p hp
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
  rw [Finset.mem_coe, Finset.mem_filter, Normalized.Contacts.mem_sourceChains7]
  exact hp
theorem cfCost_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s ≤
      ((93 * q : Nat) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : PairedReference.referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := PairedReference.reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold cfCost
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) (contacts_le_contactCount s)
theorem reference_contactFirst_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        ∃ k, CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧ ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] ≤
      93 * ((q : ENNReal) / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) := by
  calc _ ≤ ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun s => ?_
        split_ifs with h
        · obtain ⟨a, ha, hcf⟩ := h
          obtain ⟨p, rfl⟩ := exists_chainAt ha
          rw [cfInd, if_pos ⟨p, ha, hcf⟩, mul_one, PMF.probOutput_eq_apply]
        · exact zero_le
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s := reference_cfInd_le adversary q
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (((93 * q : Nat) : ENNReal) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal)) :=
        mul_le_mul' le_rfl (cfCost_le adversary q)
    _ = _ := by
        push_cast
        rw [div_eq_mul_inv]
        ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
end
-- ==== merged from T3_Secc_WotsSmallTransport ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace SmallT
open _root_.SigGolfCandidate.T3.Security.Wots.Ref
structure TraceEvent where
  holds : Answers → List Entry → Prop
  mono : ∀ {T : Answers} {trace trace' : List Entry}, holds T trace → (∀ e ∈ trace, e ∈ trace') → holds T trace'
  transfer : ∀ {A T : Answers} {trace : List Entry}, ShortAgree A T →
    (∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1))) → holds A trace → holds T trace
end SmallT
open SmallT
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsSmallTransport ====
section

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace SmallT
open ClaudeWCT.W9.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
open SigGolfCandidate.T3.Security.Wots.Ref (ShortAgree cap_recorded_le chargeSum cut eagerSide eval_congr_queried fixedRecord
  pmf_probEvent_mono pureRecord pureRecord_value entriesOf_congr fillAnswers_empty fixedRecord_counted fixedRecord_hashOnly
  fixedRecord_mem_record recorded_bind agrees_empty chargeSum_append cut_cached cut_shortAgree pureRecord_charge
  pureRecord_inputs ticks_recorded verdict_recorded_fixed embed traceOf_append calls_append traceOf_replicate_tick calls_replicate_tick traceOf_map_embed calls_map_embed_public)
theorem wotsPrimitiveSrc_transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : WotsExtract.WotsPrimitiveSrc A trace) : WotsExtract.WotsPrimitiveSrc T trace := by
  have hdepth : depth A = depth T := funext (depth_short hAT)
  have hfront : frontierValue A = frontierValue T := funext (frontierValue_short hAT)
  have hrefi : referenceInput A = referenceInput T := funext (referenceInput_short hAT)
  have hrefd : referenceDigits A = referenceDigits T := funext (referenceDigits_short hAT)
  rcases h with ⟨L, hsrc, hL⟩ | hS | ⟨a, hsrc, ha⟩ | ⟨a, b, hsa, hsb, hab, ha, hb⟩ | ⟨a, hsrc, ha, hc⟩
  · refine Or.inl ⟨L, hsrc, ?_⟩
    simpa only [EncodingMatchAt, hrefi, hrefd] using hL
  · refine Or.inr (Or.inl ?_)
    obtain ⟨position, input, answer, hmem, hpos, hbounded, hsource, hclass, hhit⟩ := hS
    refine ⟨position, input, answer, hmem, hpos, hbounded, hsource, ?_, ?_⟩
    · cases position <;> simpa only [StructuralClass, OtherChainRow, hdepth] using hclass
    · rw [← honestInput_short hAT position hbounded]
      obtain ⟨hne, heq⟩ := hhit
      refine ⟨hne, ?_⟩
      rw [← htrace (input, answer) hmem, ← hAT.public _ (honestInput_length A position)]
      exact heq
  · refine Or.inr (Or.inr (Or.inl ⟨a, hsrc, ?_⟩))
    simpa only [TwoEdgeAt, hdepth, hfront] using ha
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hsa, hsb, hab, ?_, ?_⟩)))
    · simpa only [ContactAt, hdepth, hfront] using ha
    · simpa only [ContactAt, hdepth, hfront] using hb
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hsrc, ?_, ?_⟩)))
    · simpa only [MarkerAt, hrefi, hrefd] using ha
    · simpa only [ContactAt, hdepth, hfront] using hc
def srcEvent : TraceEvent where
  holds := WotsExtract.WotsPrimitiveSrc
  mono := fun h hsub => WotsExtract.WotsPrimitiveSrc.mono h hsub
  transfer := fun hAT htrace h => wotsPrimitiveSrc_transfer hAT htrace h
def VerifierEv (Ev : TraceEvent) (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    Ev.holds answers (entriesOf answers (queried answers (verifyP message publicKey witness)))
def CaseABEvAt (Ev : TraceEvent) (adversary : AdversaryP) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  ∀ generated interaction checked, GameSplit adversary result generated interaction checked →
    ∀ forgery, interaction.value.1 = some forgery → VerifierEv Ev answers generated.value.1 forgery
def CaseABEv (Ev : TraceEvent) (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  CaseABEvAt Ev adversary (QueryRecorded.recordedTrace z.1) z.2
def GoodEv (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  result.value = true ∧ chargeSum result.events ≤ q ∧ CaseABEvAt Ev adversary result answers
def PsiEv (Ev : TraceEvent) (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) : Prop :=
  evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true ∧
    Ev.holds T (entriesOf T (SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result)))
theorem psiEv_of_verifierEv (Ev : TraceEvent) (A T : Answers) (publicKey : Digest)
    (result : Option ForgeryP × QueryLog Requests) (hshort : ShortAgree A T)
    (hverdict : ∀ query ∈ SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result),
      A query = T query)
    (haccept : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true)
    (hab : ∀ forgery, result.1 = some forgery → VerifierEv Ev A publicKey forgery) :
    PsiEv Ev T publicKey result := by
  refine ⟨haccept, ?_⟩
  obtain ⟨forgery, hf, hcheck, hsub⟩ := verdict_accepts T publicKey result haccept
  obtain ⟨-, m', w', hof', -, hqsub⟩ := PaddedExtraction.check_accepting T publicKey result.2 forgery hcheck
  obtain ⟨m, w, hof, -, hprim⟩ := hab forgery hf
  have hofT : PaddedExtraction.WitnessOf T publicKey forgery m w := by
    cases forgery with
    | witness message witness => exact hof
    | signature message signature =>
        obtain ⟨hm, hw⟩ := hof
        refine ⟨hm, ?_⟩
        rw [← hw]
        symm
        apply (eval_congr_queried _ A T fun query hq => hverdict query (hsub query ?_)).1
        simp only [checkForgeryP, SourceReplay.queried_bind]
        exact List.mem_append_left _ hq
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hofT hof'
  have hagree : ∀ query ∈ SourceReplay.queried T (verifyP m publicKey w), A query = T query :=
    fun query hq => hverdict query (hsub query (hqsub query hq))
  have hq := (eval_congr_queried _ A T hagree).2
  have he : entriesOf A (SourceReplay.queried A (verifyP m publicKey w)) =
      entriesOf T (SourceReplay.queried T (verifyP m publicKey w)) := by
    rw [hq]
    exact entriesOf_congr A T _ hagree
  change Ev.holds A (entriesOf A (SourceReplay.queried A (verifyP m publicKey w))) at hprim
  rw [he] at hprim
  have hprimT := Ev.transfer hshort (fun e he' => ?_) hprim
  · exact Ev.mono hprimT (WotsExtract.entriesOf_mono fun query hq' => hsub query (hqsub query hq'))
  · obtain ⟨hmem, -⟩ := WotsExtract.mem_entriesOf_iff.mp (show (e.1, e.2) ∈ _ from he')
    exact hagree _ hmem
theorem goodEv_imp (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers)
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi : interaction ∈ support (fixedInteraction adversary T))
    (hgood : GoodEv Ev adversary q (combine T interaction) (cut (combine T interaction).state T)) :
    PsiEv Ev T (evalWithAnswerFn T keygen).1 interaction.value ∧
      keygenCharge T + chargeSum interaction.events +
        verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value ≤ q := by
  have hg0val : (pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen := pureRecord_value T keygen (∅, ∅)
  have hg0 : pureRecord T keygen (∅, ∅) ∈ support (fixedRecord T keygen (∅, ∅)) := by
    rw [fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
  obtain ⟨hg0rec, hag0⟩ := fixedRecord_mem_record T keygen (∅, ∅) (agrees_empty T) _ hg0
  unfold fixedInteraction at hi
  rw [← hg0val] at hi
  obtain ⟨hirec, hagi⟩ := fixedRecord_mem_record T _ _ hag0 interaction hi
  have hci : verdictRecord T interaction ∈ support (fixedRecord T (GameWith.verdict PaddedGame.checker
      (pureRecord T keygen (∅, ∅)).value.1 interaction.value) interaction.state) := by
    rw [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), mem_support_pure_iff, hg0val]
    rfl
  obtain ⟨hcirec, -⟩ := fixedRecord_mem_record T _ interaction.state hagi _ hci
  have hsplit : GameSplit adversary (combine T interaction) (pureRecord T keygen (∅, ∅)) interaction
      (verdictRecord T interaction) := ⟨hg0rec, hirec, hcirec, rfl⟩
  obtain ⟨hwin, hcharge, hab⟩ := hgood
  have hacc : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1
      interaction.value) = true := by
    rw [← pureRecord_value]
    exact hwin
  rw [hg0val] at hcirec
  have hknown := FirstHit.recorded_query_known _ (verdict_hashOnly _ _) interaction.state _ hcirec
  have hinputs : (verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
      SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) :=
    pureRecord_inputs T _ interaction.state
  have hverdict : ∀ query ∈ SourceReplay.queried T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value),
      cut (verdictRecord T interaction).state T query = T query := by
    intro query hq
    rw [← hinputs] at hq
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hq
    apply cut_cached
    intro x hx
    have hk := (hknown event hevent).1
    rcases event with ⟨before, input, answer⟩
    change input = .inl (.inr x) at hx
    subst hx
    change (verdictRecord T interaction).state.2 x = some answer at hk
    rw [hk]
    rfl
  refine ⟨psiEv_of_verifierEv Ev (cut (verdictRecord T interaction).state T) T _ interaction.value
    (cut_shortAgree _ _) hverdict hacc ?_, ?_⟩
  · intro forgery hf
    have h := hab _ interaction _ hsplit forgery hf
    rw [hg0val] at h
    exact h
  · have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hv : chargeSum (verdictRecord T interaction).events =
        verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value :=
      pureRecord_charge T _ (verdict_hashOnly _ _) interaction.state
    have hc : chargeSum (combine T interaction).events = chargeSum (pureRecord T keygen (∅, ∅)).events +
        (chargeSum interaction.events + chargeSum (verdictRecord T interaction).events) := by
      simp only [combine, chargeSum_append]
    omega
theorem offlineEv_le (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun x => PsiEv Ev T (evalWithAnswerFn T keygen).1 x.1 ∧
        keygenCharge T + x.2 + verdictCharge T (evalWithAnswerFn T keygen).1 x.1 ≤ q |
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | offlineRun T adversary q] := by
  refine le_trans ?_ (cap_recorded_le RefCharged (refImpl T) (offlineGame T adversary) q
    (fun queries => Ev.holds T (traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted, simulateQ_map, probEvent_map]
  unfold offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PaddedGame.verdict_public _ _), pure_bind]
  rw [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  rintro ⟨result, queries⟩ - ⟨⟨hacc, hprim⟩, hcharge⟩
  refine ⟨?_, ?_⟩
  · change Ev.holds T (traceOf T (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))))
    rw [traceOf_append, traceOf_append, traceOf_replicate_tick, traceOf_map_embed]
    exact Ev.mono hprim (fun e he => List.mem_append_right _ (List.mem_append_right _ he))
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))) ≤ q
    rw [calls_append, calls_append, calls_replicate_tick, calls_map_embed_public T _ (PaddedGame.verdict_public _ _)]
    unfold verdictCharge at hcharge
    simp only at hcharge
    omega
theorem fixed_gameEv_le (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun result => GoodEv Ev adversary q result (cut result.state T) |
        fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | offlineRun T adversary q] := by
  rw [fixed_game_eq, probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi hgood => goodEv_imp Ev adversary q T interaction hi hgood) ?_
  have hcount := fixedRecord_counted T (FullGame.loggedWith (FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅, ∅)).state
  rw [interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offlineEv_le Ev adversary q T)
  rw [← hcount, probEvent_map]
  rfl
theorem caseABEv_le_recorded (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 | recordedCompleted adversary] := by
  calc _ ≤ Pr[fun z => GoodEv Ev adversary q (QueryRecorded.recordedTrace z.1) z.2 |
        SeccLaw.completedExperiment adversary q hq] := by
        apply SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, hab⟩ := hev
        have hr := (SeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨hwin.1, ?_, hab⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [completed_map, MonitoredPrivate.event_lift]
theorem eagerEv_le_reference (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) :
    Pr[fun pair => GoodEv Ev adversary q pair.1 (cut pair.1.state pair.2) |
        eagerSide (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | referenceComp adversary q] := by
  unfold eagerSide referenceComp
  apply Ref.probEvent_bind_mono
  intro privateTable
  apply Ref.probEvent_bind_mono
  intro publicTable
  rw [probEvent_map, probEvent_map, fillAnswers_empty]
  exact fixed_gameEv_le Ev adversary q _
theorem caseABEv_le_reference (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | referenceExperiment adversary q] := by
  refine (caseABEv_le_recorded Ev adversary q hq).trans ?_
  rw [recorded_eq_eager adversary (GoodEv Ev adversary q)]
  refine (eagerEv_le_reference Ev adversary q).trans (le_of_eq ?_)
  unfold referenceExperiment
  rw [MonitoredPrivate.event_lift]
end SmallT
abbrev CaseABSrc (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  SmallT.CaseABEv SmallT.srcEvent adversary z
theorem caseABSrc_le_reference (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => WotsExtract.WotsPrimitiveSrc sample.answers sample.trace | referenceExperiment adversary q] :=
  SmallT.caseABEv_le_reference SmallT.srcEvent adversary q hq
theorem completed_split_src (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hcomp : BPB.SignerComplete z.2) :
    CaseABSrc adversary z ∨ CaseC.CaseCFreshPinned adversary z ∨ CaseC.CaseCSignedPinned adversary z := by
  by_cases hab : CaseABSrc adversary z
  · exact Or.inl hab
  right
  unfold CaseABSrc SmallT.CaseABEv SmallT.CaseABEvAt at hab
  push Not at hab
  obtain ⟨generated, interaction, checked, hsplit, forgery, hf, hnot⟩ := hab
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  set result := QueryRecorded.recordedTrace z.1 with hresult
  have hrs : ∀ input answer, SourceReplay.known result.state input = some answer → z.2 input = answer := ha
  have hsplit' := hsplit
  obtain ⟨hg, hi, hc, heq⟩ := hsplit'
  have hstate : result.state = checked.state := by rw [heq]
  have hvalue : result.value = checked.value := by rw [heq]
  have hgext : SourceReplay.Extends generated.state result.state :=
    (SourceReplay.run_extends _ generated.state (interaction.value, interaction.state)
      (FirstHit.recorded_support _ _ _ hi)).trans hsplit.extends
  have hgen : evalWithAnswerFn z.2 keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hrs input answer (SourceReplay.known_mono generated.state result.state hgext hk))
  have hpk : generated.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → z.2 input = answer := by
    rw [← hstate]; exact hrs
  have hwin : checked.value = true := by rw [← hvalue]; exact hclean.1
  obtain ⟨hlen, forgery', hf', hfresh, message, witness, hof, hconc⟩ :=
    PaddedExtraction.verdict_recorded generated.value.1 interaction.value interaction.state checked hc z.2 hac hpk hwin
  have hff : forgery' = forgery := Option.some.inj (hf'.symm.trans hf)
  subst hff
  have hvd : evalWithAnswerFn z.2 (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value) =
      true := by
    rw [(SourceReplay.resolves_of_run _ (Ref.verdict_hashOnly _ _) interaction.state (checked.value, checked.state)
      (FirstHit.recorded_support _ _ _ hc)).eval z.2 hac]
    exact hwin
  obtain ⟨forgery'', hf'', hcheck, -⟩ := Ref.verdict_accepts z.2 _ _ hvd
  obtain ⟨-, message', witness', hof', hv, -⟩ := PaddedExtraction.check_accepting z.2 _ _ forgery'' hcheck
  have hff' : forgery'' = forgery' := Option.some.inj (hf''.symm.trans hf')
  subst hff'
  obtain ⟨rfl, rfl⟩ := Ref.witnessOf_unique hof' hof
  obtain ⟨N, hdc, hN, -, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_src z.2 message' generated.value.1 witness' hpk hv
  rcases hcase with hprim | ⟨hgood, hfts⟩
  · exact absurd ⟨message', witness', hof', hv, hprim⟩ hnot
  obtain ⟨N', hdc', hN', hevent, hS', -⟩ := hconc
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  have hCat : BPB.CaseCAt z.2 message' witness' result.events := by
    refine ⟨N', hdc, hN, ?_, hS, hgood, hfts, hcomp⟩
    obtain ⟨prior, hp⟩ := hevent
    refine ⟨prior, ?_⟩
    rw [heq]
    exact List.mem_append_right _ (List.mem_append_right _ hp)
  by_cases hsigned : BPB.SignedDigest interaction.value.2 message' witness'
  · exact Or.inr ⟨generated, interaction, checked, hsplit, hpk, hlen, _, hf', hfresh, message', witness',
      hof', hsigned, hCat⟩
  · exact Or.inl ⟨generated, interaction, checked, hsplit, hpk, hlen, _, hf', hfresh, message', witness',
      hof', hsigned, hCat⟩
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen ClaudeWCT.W9.T3M.Paired.verifyP ClaudeWCT.W9.T3M.Paired.expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinateF PairedOuter.GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
open ClaudeWCT.W9.T3.Security.Wots.PairedReference ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
open SigGolfCandidate.T3.Security.Wots.Ref (ShortAgree cap_recorded_le chargeSum cut eagerSide eval_congr_queried fixedRecord
  pmf_probEvent_mono pureRecord pureRecord_value entriesOf_congr fillAnswers_empty fixedRecord_counted fixedRecord_hashOnly
  fixedRecord_mem_record recorded_bind agrees_empty chargeSum_append cut_cached cut_shortAgree pureRecord_charge
  pureRecord_inputs ticks_recorded verdict_recorded_fixed embed traceOf_append calls_append traceOf_replicate_tick calls_replicate_tick traceOf_map_embed calls_map_embed_public)
def CheckerEv (Ev : TraceEvent) (answers : Answers) (publicKey : Digest)
    (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)
    (forgery : ClaudeWCT.W9.T3M.Final.Paired.ForgeryP) : Prop :=
  evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey log forgery) = true ∧
    Ev.holds answers (entriesOf answers (queried answers
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey log forgery)))
def CaseABEvAt (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  ∀ generated interaction checked, PairedReference.GameSplit adversary result generated interaction checked →
    ∀ forgery, interaction.value.1 = some forgery → CheckerEv Ev answers generated.value.1 interaction.value.2 forgery
def CaseABEv (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  CaseABEvAt Ev adversary (QueryRecorded.recordedTrace z.1) z.2
def GoodEv (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  result.value = true ∧ chargeSum result.events ≤ q ∧ CaseABEvAt Ev adversary result answers
def PsiEv (Ev : TraceEvent) (T : Answers) (publicKey : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Prop :=
  evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) = true ∧
    Ev.holds T (entriesOf T (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result)))
theorem psiEv_of_checkerEv (Ev : TraceEvent) (A T : Answers) (publicKey : Digest)
    (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (hshort : ShortAgree A T)
    (hverdict : ∀ query ∈ SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result),
      A query = T query)
    (haccept : evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker publicKey result) = true)
    (hab : ∀ forgery, result.1 = some forgery → CheckerEv Ev A publicKey result.2 forgery) :
    PsiEv Ev T publicKey result := by
  refine ⟨haccept, ?_⟩
  obtain ⟨forgery, hf, hcheck, hsub⟩ := PairedReference.Ref.verdict_accepts T publicKey result haccept
  obtain ⟨_,hprim⟩ := hab forgery hf
  have hagree : ∀ query ∈ SourceReplay.queried T
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery), A query = T query :=
    fun query hq => hverdict query (hsub query hq)
  have hq := (eval_congr_queried _ A T hagree).2
  have he : entriesOf A (SourceReplay.queried A
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery)) =
      entriesOf T (SourceReplay.queried T
      (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery)) := by
    rw [hq]
    exact entriesOf_congr A T _ hagree
  change Ev.holds A (entriesOf A (SourceReplay.queried A
    (ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP publicKey result.2 forgery))) at hprim
  rw [he] at hprim
  have hprimT := Ev.transfer hshort (fun e he' => ?_) hprim
  · exact Ev.mono hprimT (WotsExtract.entriesOf_mono hsub)
  · obtain ⟨hmem, -⟩ := WotsExtract.mem_entriesOf_iff.mp (show (e.1,e.2) ∈ _ from he')
    exact hagree _ hmem

theorem goodEv_imp (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers)
    (interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests))
    (hi : interaction ∈ support (PairedReference.Ref.fixedInteraction adversary T))
    (hgood : GoodEv Ev adversary q (PairedReference.Ref.combine T interaction) (cut (PairedReference.Ref.combine T interaction).state T)) :
    PsiEv Ev T (evalWithAnswerFn T keygen).1 interaction.value ∧
      SigGolfCandidate.T3.Security.Wots.keygenCharge T + chargeSum interaction.events +
        PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value ≤ q := by
  have hg0val : (pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen := pureRecord_value T keygen (∅, ∅)
  have hg0 : pureRecord T keygen (∅, ∅) ∈ support (fixedRecord T keygen (∅, ∅)) := by
    rw [fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
  obtain ⟨hg0rec, hag0⟩ := fixedRecord_mem_record T keygen (∅, ∅) (agrees_empty T) _ hg0
  unfold PairedReference.Ref.fixedInteraction at hi
  rw [← hg0val] at hi
  obtain ⟨hirec, hagi⟩ := fixedRecord_mem_record T _ _ hag0 interaction hi
  have hci : PairedReference.Ref.verdictRecord T interaction ∈ support (fixedRecord T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker
      (pureRecord T keygen (∅, ∅)).value.1 interaction.value) interaction.state) := by
    rw [fixedRecord_hashOnly T _ (PairedReference.Ref.verdict_hashOnly _ _), mem_support_pure_iff, hg0val]
    rfl
  obtain ⟨hcirec, -⟩ := fixedRecord_mem_record T _ interaction.state hagi _ hci
  have hsplit : PairedReference.GameSplit adversary (PairedReference.Ref.combine T interaction) (pureRecord T keygen (∅, ∅)) interaction
      (PairedReference.Ref.verdictRecord T interaction) := ⟨hg0rec, hirec, hcirec, rfl⟩
  obtain ⟨hwin, hcharge, hab⟩ := hgood
  have hacc : evalWithAnswerFn T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1
      interaction.value) = true := by
    rw [← pureRecord_value]
    exact hwin
  rw [hg0val] at hcirec
  have hknown := FirstHit.recorded_query_known _ (PairedReference.Ref.verdict_hashOnly _ _) interaction.state _ hcirec
  have hinputs : (PairedReference.Ref.verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
      SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) :=
    pureRecord_inputs T _ interaction.state
  have hverdict : ∀ query ∈ SourceReplay.queried T
      (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value),
      cut (PairedReference.Ref.verdictRecord T interaction).state T query = T query := by
    intro query hq
    rw [← hinputs] at hq
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hq
    apply cut_cached
    intro x hx
    have hk := (hknown event hevent).1
    rcases event with ⟨before, input, answer⟩
    change input = .inl (.inr x) at hx
    subst hx
    change (PairedReference.Ref.verdictRecord T interaction).state.2 x = some answer at hk
    rw [hk]
    rfl
  refine ⟨psiEv_of_checkerEv Ev (cut (PairedReference.Ref.verdictRecord T interaction).state T) T _ interaction.value
    (cut_shortAgree _ _) hverdict hacc ?_, ?_⟩
  · intro forgery hf
    have h := hab _ interaction _ hsplit forgery hf
    rw [hg0val] at h
    exact h
  · have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = SigGolfCandidate.T3.Security.Wots.keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hv : chargeSum (PairedReference.Ref.verdictRecord T interaction).events =
        PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value :=
      pureRecord_charge T _ (PairedReference.Ref.verdict_hashOnly _ _) interaction.state
    have hc : chargeSum (PairedReference.Ref.combine T interaction).events = chargeSum (pureRecord T keygen (∅, ∅)).events +
        (chargeSum interaction.events + chargeSum (PairedReference.Ref.verdictRecord T interaction).events) := by
      simp only [PairedReference.Ref.combine, chargeSum_append]
    omega
theorem offlineEv_le (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun x => PsiEv Ev T (evalWithAnswerFn T keygen).1 x.1 ∧
        SigGolfCandidate.T3.Security.Wots.keygenCharge T + x.2 + PairedReference.Ref.verdictCharge T (evalWithAnswerFn T keygen).1 x.1 ≤ q |
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (PairedReference.offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | PairedReference.offlineRun T adversary q] := by
  refine le_trans ?_ (cap_recorded_le RefCharged (refImpl T) (PairedReference.offlineGame T adversary) q
    (fun queries => Ev.holds T (traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted, simulateQ_map, probEvent_map]
  unfold PairedReference.offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PairedOuter.PaddedGame.verdict_public _ _), pure_bind]
  rw [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  rintro ⟨result, queries⟩ - ⟨⟨hacc, hprim⟩, hcharge⟩
  refine ⟨?_, ?_⟩
  · change Ev.holds T (traceOf T (List.replicate (SigGolfCandidate.T3.Security.Wots.keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))))
    rw [traceOf_append, traceOf_append, traceOf_replicate_tick, traceOf_map_embed]
    exact Ev.mono hprim (fun e he => List.mem_append_right _ (List.mem_append_right _ he))
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (SigGolfCandidate.T3.Security.Wots.keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (PairedOuter.GameWith.verdict PairedOuter.PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))) ≤ q
    rw [calls_append, calls_append, calls_replicate_tick, calls_map_embed_public T _ (PairedOuter.PaddedGame.verdict_public _ _)]
    unfold PairedReference.Ref.verdictCharge at hcharge
    simp only at hcharge
    omega
theorem fixed_gameEv_le (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun result => GoodEv Ev adversary q result (cut result.state T) |
        fixedRecord T (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | PairedReference.offlineRun T adversary q] := by
  rw [PairedReference.Ref.fixed_game_eq, probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi hgood => goodEv_imp Ev adversary q T interaction hi hgood) ?_
  have hcount := fixedRecord_counted T (PairedOuter.FullGame.loggedWith (PairedOuter.FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅, ∅)).state
  rw [PairedReference.Ref.interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offlineEv_le Ev adversary q T)
  rw [← hcount, probEvent_map]
  rfl
theorem caseABEv_le_recorded (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 | PairedReference.Ref.recordedCompleted adversary] := by
  calc _ ≤ Pr[fun z => GoodEv Ev adversary q (QueryRecorded.recordedTrace z.1) z.2 |
        PairedSeccLaw.completedExperiment adversary q hq] := by
        apply SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, hab⟩ := hev
        have hr := (PairedSeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PairedOuter.PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨hwin.1, ?_, hab⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> PairedSeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [PairedReference.Ref.completed_map, MonitoredPrivate.event_lift]
theorem eagerEv_le_reference (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun pair => GoodEv Ev adversary q pair.1 (cut pair.1.state pair.2) |
        eagerSide (PairedReference.referenceInputs adversary) (PairedOuter.GameWith.idealGame PairedOuter.PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | PairedReference.referenceComp adversary q] := by
  unfold eagerSide PairedReference.referenceComp
  apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
  intro privateTable
  apply SigGolfCandidate.T3.Security.Wots.Ref.probEvent_bind_mono
  intro publicTable
  rw [probEvent_map, probEvent_map, fillAnswers_empty]
  exact fixed_gameEv_le Ev adversary q _
theorem caseABEv_le_reference (Ev : TraceEvent) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | PairedReference.referenceExperiment adversary q] := by
  refine (caseABEv_le_recorded Ev adversary q hq).trans ?_
  rw [PairedReference.Ref.recorded_eq_eager adversary (GoodEv Ev adversary q)]
  refine (eagerEv_le_reference Ev adversary q).trans (le_of_eq ?_)
  unfold PairedReference.referenceExperiment
  rw [MonitoredPrivate.event_lift]

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open CanonicalRef
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem wotsPrimitiveSrc_transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : CanonicalExtract.WotsPrimitiveSrc A (CanonicalRef.sourceMessages A) trace) :
    CanonicalExtract.WotsPrimitiveSrc T (CanonicalRef.sourceMessages T) trace := by
  have hdepth : CanonicalRef.depth A (CanonicalRef.sourceMessages A) = CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  have hfront : CanonicalRef.frontierValue A (CanonicalRef.sourceMessages A) = CanonicalRef.frontierValue T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.frontierValue_short hAT)
  have hrefi : CanonicalRef.referenceInput A (CanonicalRef.sourceMessages A) = CanonicalRef.referenceInput T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.referenceInput_short hAT)
  have hrefd : CanonicalRef.referenceDigits A (CanonicalRef.sourceMessages A) = CanonicalRef.referenceDigits T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.referenceDigits_short hAT)
  rcases h with ⟨L, hsrc, hL⟩ | hS | ⟨a, hsrc, ha⟩ | ⟨a, b, hsa, hsb, hab, ha, hb⟩ | ⟨a, hsrc, ha, hc⟩
  · refine Or.inl ⟨L, hsrc, ?_⟩
    have hns : CanonicalRef.NotSearched A (CanonicalRef.sourceMessages A) =
        CanonicalRef.NotSearched T (CanonicalRef.sourceMessages T) := by
      funext L' x
      unfold CanonicalRef.NotSearched
      rw [CanonicalRef.referenceSearch_short hAT, CanonicalRef.sourceMessages_short hAT]
    simpa only [CanonicalRef.EncodingMatchAt, hrefi, hrefd, hns] using hL
  · refine Or.inr (Or.inl ?_)
    obtain ⟨position, input, answer, hmem, hpos, hbounded, hsource, hclass, hmain, hhit⟩ := hS
    refine ⟨position, input, answer, hmem, hpos, hbounded, hsource, ?_, hmain, ?_⟩
    · cases position <;> simpa only [CanonicalRef.StructuralClass, CanonicalRef.OtherChainRow, hdepth] using hclass
    · rw [← Ref.honestInput_short hAT position hbounded]
      obtain ⟨hne, heq⟩ := hhit
      refine ⟨hne, ?_⟩
      rw [← htrace (input, answer) hmem, ← hAT.public _ (Ref.honestInput_length A position)]
      exact heq
  · refine Or.inr (Or.inr (Or.inl ⟨a, hsrc, ?_⟩))
    simpa only [CanonicalRef.TwoEdgeAt, hdepth, hfront] using ha
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hsa, hsb, hab, ?_, ?_⟩)))
    · simpa only [CanonicalRef.ContactAt, hdepth, hfront] using ha
    · simpa only [CanonicalRef.ContactAt, hdepth, hfront] using hb
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hsrc, ?_, ?_⟩)))
    · simpa only [CanonicalRef.MarkerAt, hrefi, hrefd] using ha
    · simpa only [CanonicalRef.ContactAt, hdepth, hfront] using hc

def srcEvent : TraceEvent where
  holds := fun T => CanonicalExtract.WotsPrimitiveSrc T (CanonicalRef.sourceMessages T)
  mono := fun h hsub => CanonicalExtract.WotsPrimitiveSrc.mono h hsub
  transfer := fun hAT htrace h => wotsPrimitiveSrc_transfer hAT htrace h

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem structuralHitSrc_paired {T : Answers} {trace : List Entry} {inputs : Finset HashInput}
    (h : StructuralHitSrc T (CanonicalRef.sourceMessages T) trace)
    (hin : ∀ entry ∈ trace, entry.1 ∈ inputs) : PairedReference.StructuralHitIn inputs T trace := by
  obtain ⟨p,x,a,hmem,hpos,hb,hsrc,hcls,hmain,hhit⟩ := h
  cases p with
  | chain lay tree leaf i step =>
    exact ⟨_,x,a,hmem,hin _ hmem,hpos,hb,hsrc,hcls,
      by unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_chain]; exact hhit⟩
  | leaf lay tree leaf =>
    exact ⟨_,x,a,hmem,hin _ hmem,hpos,hb,hsrc,hcls,
      by unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_leaf]; exact hhit⟩
  | node lay tree level node =>
    exact ⟨_,x,a,hmem,hin _ hmem,hpos,hb,hsrc,hcls,
      by unfold Extract.Paired.HashHitAt; rw [Extract.Paired.proj_node]; exact hhit⟩
  | forest | wctChain | wctLeaf | wctNode => exact hmain.elim
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def StructuralHitTrace (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧
    Extract.posOf input = some position ∧ Extract.Paired.Bounded position ∧
    WotsExtract.PosSource position ∧
    CanonicalRef.StructuralClass answers (CanonicalRef.sourceMessages answers) input position ∧
    Extract.Paired.HashHitAt answers position (Extract.Paired.honestInput answers position) input

theorem StructuralHitTrace.mono {T : Answers} {trace trace' : List Entry}
    (h : StructuralHitTrace T trace) (hsub : ∀ entry ∈ trace, entry ∈ trace') : StructuralHitTrace T trace' := by
  obtain ⟨p,x,a,hm,hp,hb,hs,hc,hh⟩ := h
  exact ⟨p,x,a,hsub _ hm,hp,hb,hs,hc,hh⟩

theorem StructuralHitTrace.toHitIn {T : Answers} {trace : List Entry} {inputs : Finset HashInput}
    (h : StructuralHitTrace T trace) (hin : ∀ entry ∈ trace, entry.1 ∈ inputs) : StructuralHitIn inputs T trace := by
  obtain ⟨p,x,a,hm,hp,hb,hs,hc,hh⟩ := h
  exact ⟨p,x,a,hm,hin _ hm,hp,hb,hs,hc,hh⟩

theorem structuralHitTrace_transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : StructuralHitTrace A trace) : StructuralHitTrace T trace := by
  have hdepth : CanonicalRef.depth A (CanonicalRef.sourceMessages A) =
      CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  obtain ⟨p,x,a,hm,hp,hb,hs,hc,hh⟩ := h
  refine ⟨p,x,a,hm,hp,hb,hs,?_,?_⟩
  · cases p <;> simpa only [CanonicalRef.StructuralClass,CanonicalRef.OtherChainRow,hdepth] using hc
  · rw [← honestInput_short hAT p hb]
    obtain ⟨hne,heq⟩ := hh
    refine ⟨hne,?_⟩
    rw [← htrace (x,a) hm,← hAT.public _ (honestInput_length A p)]
    exact heq

theorem ftsHitIn_structuralHitTrace {T : Answers} {qs : List Spec.Domain}
    (h : Extract.Paired.FtsHitIn T qs) : StructuralHitTrace T (entriesOf T qs) := by
  obtain ⟨p,x,hfts,hb,hq,hh,hs⟩ := h
  -- #866: `SameHeader` is `length ∧ hdrKey`; `posOf_sameHeader` is its paired `posOf_key_eq`.
  have hp : Extract.posOf x = some p := Extract.Paired.posOf_sameHeader T p hb.legacy x hs
  refine ⟨p,x,_,SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf hq,hp,hb,?_,?_,hh⟩
  · cases p with
    | chain | leaf | node | forest => exact hfts.elim
    | wctChain | wctLeaf => exact hb.legacy
    | wctNode => exact hb.legacy
  · cases p <;> first | exact hfts.elim | trivial

end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open SigGolfCandidate.T3.Security.Wots.SmallT (TraceEvent)
def combinedEvent : TraceEvent where
  holds := fun T trace => CanonicalExtract.WotsPrimitiveSrc T (CanonicalRef.sourceMessages T) trace ∨
    PairedReference.StructuralHitTrace T trace
  mono := fun h hsub => h.elim (fun hp => Or.inl (hp.mono hsub)) (fun hs => Or.inr (hs.mono hsub))
  transfer := fun hAT htrace h => h.elim
    (fun hp => Or.inl (wotsPrimitiveSrc_transfer hAT htrace hp))
    (fun hs => Or.inr (PairedReference.structuralHitTrace_transfer hAT htrace hs))
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_Final ====
section

section
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
theorem reference_trace_length_le (adversary : AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (referenceExperiment adversary q).support) : s.trace.length ≤ q := by
  rw [reference_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, hrun, rfl⟩ := hs
  have h1 := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hrun
  have h2 : run ∈ support (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) := by
    revert h1
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl (restTable R))
      (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) run
  have hcount : (run.1, SphincsSecurity.QueryCap.calls RefCharged run.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (restTable R) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨run, h2, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (restTable R) adversary q) _ hcount
  refine le_trans ?_ hle
  show (traceOf (restTable R) run.2).length ≤ _
  have hf := traceOf_filter_length (restTable R) (fun _ => True) run.2
  simp only [decide_true, List.filter_true] at hf
  rw [hf]
  unfold SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨x, rfl, -⟩ := hq
  trivial
theorem prefixClassCount_le_length (s : RefSample) : prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  have hsize : ∀ c : ChainAddr, WotsExtract.SourceChain c → c.key.tree < 2 ^ 40 ∧ c.key.leaf < 2 ^ 24 := by
    intro c hc
    refine ⟨by have := hc.1.1; omega, ?_⟩
    have h1 := hc.1.2
    have h2 : 2 ^ height c.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le c.key.lay; omega)
    omega
  unfold ContactAt
  rw [depth_maskAt_all T a b (Mask.maskOK_of_lt (hsize a ha).2),
    frontierValue_maskAt_bounded T a b (hsize a ha) (hsize b hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRowW a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; rw [hm]
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (prefixRowAt_unique (answers := T) ha hb ⟨_, va, by omega, rfl⟩ ⟨_, vb, by omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(mem_sourceChains b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
/-- `(2^128 + 2q) T / ((1 - x) 2^128) = (1 + 2x) / (1 - x) · T`. -/
theorem big_div_mul (q : Nat) (T : ENNReal) :
    ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * T / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) =
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * T := by
  have h1 : (2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
  have e : ∀ y : ENNReal, ((2 : ENNReal) ^ 128 + ((2 * q : ℕ) : ENNReal)) * T * (y * ((2 : ENNReal) ^ 128)⁻¹) =
      y * T * ((2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹) + 2 * ((q : ENNReal) * ((2 : ENNReal) ^ 128)⁻¹) * y * T := by
    intro y
    push_cast
    ring
  rw [e, h1]
  ring
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]
theorem probEvent_le_six {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] + Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p] := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  exact probEvent_or_le _ _ _
theorem probEvent_le_six_split {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) (a b : ENNReal) (hab : a + b = 1) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] +
      (a * (Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p]) +
        b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]) := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  calc Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]
      = (a + b) * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := by rw [hab, one_mul]
    _ = a * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] +
          b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := add_mul _ _ _
    _ ≤ _ := by
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      exact probEvent_or_le _ _ _
end SmallP
open SmallP
end SigGolfCandidate.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
end SmallR
open SmallR
end SigGolfCandidate.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
open SigGolfCandidate.T3.Security.Wots.SmallP (mem_take_succ probEvent_le_six)
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a
theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : MarkerAt T trace a) (hc : ContactAt T trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, MarkerAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, MarkerAt T (trace.take k) a ∧ ∀ j < k, ¬MarkerAt T (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, ContactAt T (trace.take k) a ∧ ∀ j < k, ¬ContactAt T (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, pad, answer, digits, -, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, pad, answer, digits, hfit, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, pad, answer, digits, hfit, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact ClaudeWCT.W9.T3.Security.Wots.SmallA.chainRowW_ne_encRow _ _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩
theorem primitive_cases (T : Answers) (trace : List Entry) (h : WotsExtract.WotsPrimitiveSrc T trace) :
    (∃ L, WotsExtract.SourceLeaf7 L ∧ EncodingMatchAt T trace L) ∨ WotsExtract.StructuralHitSrc T trace ∨
      (∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt T trace a) ∨
      (∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧ ContactAt T trace a ∧
        ContactAt T trace b) ∨
      (∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst T trace a) ∨
      (∃ a, WotsExtract.SourceChain7 a ∧ ContactFirst T trace a) := by
  rcases h with h | h | h | h | ⟨a, ha, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases markerContact_split T trace a hm hc with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, h'⟩))))
def chainOf (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨⟨p.1.lay, p.1.tree.val, p.1.leaf.val⟩, p.2.val⟩
theorem exists_chainOf {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, chainOf p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
end SmallP
def TwoContactsBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
      ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
    (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
      (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
    (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * Leaf.errTot adversary q
/-- Selected-half contact rate is at most 93; the uniform marker sum is at most 54*93 = 5022. -/
def ContactFirstBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ SmallP.ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
    93 * ((q : ENNReal) / 2 ^ 128) * refExpect adversary q contactCount
def MarkerSumBound (adversary : AdversaryP) (q : Nat) : Prop :=
  ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
    (5022 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount
noncomputable def prefixCoeffW9 (q : Nat) : ENNReal :=
  (88 / 1000 : ENNReal) *
    (((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
        (1 - (q : ENNReal) / 2 ^ 128) +
      4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      2 * 93 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)) +
    (912 / 1000 : ENNReal) * 2 / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeffW9 (q : Nat) : ENNReal :=
  7 / 4 + (88 / 1000 : ENNReal) * 2 * 5022 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
/-- Coefficient of the total seed-test error `Leaf.errTot` in the small-route primitive bound (campaign X1 B3). -/
noncomputable def errCoeffW9 (q : Nat) : ENNReal :=
  (88 / 1000 : ENNReal) *
    ((1 + twoEdgeRate q * q) / (1 - (q : ENNReal) / 2 ^ 128) +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) +
      93 * ((q : ENNReal) / 2 ^ 128) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))) +
    (912 / 1000 : ENNReal) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))
theorem chainOf_injective : Function.Injective SmallP.chainOf := by
  rintro ⟨⟨l, t, f⟩, c⟩ ⟨⟨l', t', f'⟩, c'⟩ h
  simp only [SmallP.chainOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hf⟩, hc⟩ := h
  rw [Fin.ext ht, Fin.ext hf, Fin.ext hc]
set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_le (adversary : AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, Leaf.errC adversary q (SmallP.chainOf p) ≤ Leaf.errTot adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, Leaf.errC adversary q (SmallP.chainOf p) =
      ∑ a ∈ Finset.univ.image SmallP.chainOf, Leaf.errC adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image SmallP.chainOf, Leaf.errC adversary q a ≤
      ∑ a ∈ (Finset.univ.image SmallP.chainOf).filter WotsExtract.SourceChain, Leaf.errC adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · unfold Leaf.errC
      rw [dif_neg h]
  have h3 : (Finset.univ.image SmallP.chainOf).filter WotsExtract.SourceChain ⊆ sourceChains := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (mem_sourceChains a).mpr ha.2
  rw [h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
/-- Together with 248/100000, this rate gives the scalar closing coefficient 196327/100000. -/
noncomputable def classRateW9 : ENNReal := 196079 / 100000
theorem inv_one_sub_leW9 (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ 4194304 / 4193304 := by
  calc (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ (4193304 / 4194304 : ENNReal)⁻¹ :=
        ENNReal.inv_le_inv.mpr (SeccClosingW9.one_sub_x_ge_of_small q hs)
    _ = 4194304 / 4193304 := ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))
theorem prefixCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : prefixCoeffW9 q ≤ classRateW9 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  unfold prefixCoeffW9 classRateW9
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ (1 - x),
    ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (88 / 1000 : ENNReal) * (((3 / 2 : ENNReal) + 4 * x + 2 * x ^ 2) * u + 4 * x * u ^ 2 + 2 * 93 * x * u) +
        (912 / 1000 : ENNReal) * 2 * u
      ≤ (88 / 1000 : ENNReal) *
          (((3 / 2 : ENNReal) + 4 * (1000 / 4194304 : ENNReal) + 2 * ((1000 / 4194304 : ENNReal))^2) * (4194304/4193304) +
            4 * (1000 / 4194304 : ENNReal) * (4194304/4193304)^2 + 2 * 93 * (1000 / 4194304 : ENNReal) * (4194304/4193304)) +
          (912 / 1000 : ENNReal) * 2 * (4194304/4193304) := by
        gcongr
    _ ≤ 196079 / 100000 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        norm_num
theorem encodingCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : encodingCoeffW9 q ≤ classRateW9 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  unfold encodingCoeffW9 classRateW9
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x)]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (7 / 4 : ENNReal) + (88 / 1000 : ENNReal) * 2 * 5022 * x * u
      ≤ 7 / 4 + (88 / 1000 : ENNReal) * 2 * 5022 * (1000 / 4194304 : ENNReal) * (4194304/4193304) := by gcongr
    _ ≤ 196079 / 100000 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem errCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : errCoeffW9 q ≤ 2 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  have e1 : twoEdgeRate q * q = ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) +
      2 * ((q : ENNReal) / 2 ^ 128) ^ 2) * ((q : ENNReal) / 2 ^ 128) := by
    unfold twoEdgeRate
    simp only [div_eq_mul_inv]
    ring
  have e2 : (2 / 2 ^ 128 : ENNReal) * q = 2 * ((q : ENNReal) / 2 ^ 128) := by
    simp only [div_eq_mul_inv]
    ring
  unfold errCoeffW9
  rw [e1, e2]
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  simp only [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (88 / 1000 : ENNReal) * ((1 + (3 / 2 + 4 * x + 2 * x ^ 2) * x) * u +
        (2 * x * (1 + 2 * x) * u ^ 2 + (1 + 2 * x) * u) + (1 + 2 * x) * u  + 93 * x * ((1 + 2 * x) * u)) +
        912 / 1000 * ((1 + 2 * x) * u)
      ≤ (88 / 1000 : ENNReal) *
          ((1 + (3 / 2 + 4 * (1000 / 4194304 : ENNReal) + 2 * (1000 / 4194304 : ENNReal) ^ 2) * (1000 / 4194304 : ENNReal)) *
              (4194304 / 4193304) +
            (2 * (1000 / 4194304 : ENNReal) * (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304) ^ 2 +
              (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304)) +
            (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304) +
            93 * (1000 / 4194304 : ENNReal) * ((1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304))) +
          912 / 1000 * ((1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304)) := by
        gcongr
    _ ≤ 2 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem one_le_classRateW9 : (1 : ENNReal) ≤ classRateW9 := by
  unfold classRateW9
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem digestRate_leW9 : 1 + SeccClosingW9.cacheRate ≤ classRateW9 := by
  unfold classRateW9
  rw [SeccClosingW9.cacheRate_def]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem excess_leW9 (q : Nat) :
    (q : ENNReal) * SeccClosingW9.excessRate / 2 ^ 128 ≤ (247 / 100000) * ((q : ENNReal) / 2 ^ 128) := by
  rw [SeccClosingW9.excessRate_def]
  simp only [div_eq_mul_inv]
  exact le_of_eq (by ring)
theorem nearTerm_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    nearTerm q ≤ (1501 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 + (1 / 100000) * ((q : ENNReal) / 2 ^ 128) := by
  have hg := SeccClosingW9.div_sub_le_of_small q hs
  unfold nearTerm nearPrice SigGolfCandidate.T3.Security.Wots.signRatio
  rw [SeccClosingW9.cacheRate_def, ← div_eq_mul_inv (q : ENNReal)]
  have hinner : (150 : ENNReal) * q / 2 ^ 128 + 63 * ((201 * q : ℕ) : ENNReal) * ((2 : ENNReal) ^ 25)⁻¹ / 2 ^ 128 +
      63 * (2 : ENNReal)⁻¹ ^ 700 =
      (150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * ((q : ENNReal) / 2 ^ 128) + 63 * (2 : ENNReal)⁻¹ ^ 700 := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hinner]
  generalize (q : ENNReal) / 2 ^ 128 = x at hg ⊢
  generalize (q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal) = g at hg ⊢
  calc g * ((150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700)
      ≤ (4194304 / 4193304 * x) * ((150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (4194304 / 4193304 * (150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (4194304 / 4193304 * (63 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
    _ ≤ (1501 / 10) * x ^ 2 + (1 / 100000) * x := by
        gcongr
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          norm_num
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          norm_num
theorem pairTerm_leW9 (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    BPair.pairTerm q ≤ (6 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  have hg := SeccClosingW9.div_sub_le_of_small q hs
  have hc : (q.choose 2 : ENNReal) ≤ (1 / 2 : ENNReal) * ((q : ENNReal) * q) := by
    have hc2 : ((q.choose 2 * 2 : Nat) : ENNReal) ≤ ((q * q : Nat) : ENNReal) :=
      Nat.cast_le.mpr (by rw [Nat.choose_two_right]; exact (Nat.div_mul_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
    calc (q.choose 2 : ENNReal) = (1 / 2 : ENNReal) * ((q.choose 2 * 2 : Nat) : ENNReal) := by
          push_cast
          rw [one_div, mul_comm, mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      _ ≤ (1 / 2 : ENNReal) * ((q * q : Nat) : ENNReal) := mul_le_mul' le_rfl hc2
      _ = (1 / 2 : ENNReal) * ((q : ENNReal) * q) := by push_cast; rfl
  unfold BPair.pairTerm
  calc (q.choose 2 : ENNReal) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2
      ≤ ((1 / 2 : ENNReal) * ((q : ENNReal) * q)) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2 := by gcongr
    _ = (1 / 2 : ENNReal) * ((q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal)) ^ 2 := by simp only [div_eq_mul_inv, mul_pow]; ring
    _ ≤ (1 / 2 : ENNReal) * (4194304 / 4193304 * ((q : ENNReal) / 2 ^ 128)) ^ 2 := by gcongr
    _ = ((1 / 2 : ENNReal) * (4194304 / 4193304 : ENNReal) ^ 2) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        rw [mul_pow]; ring
    _ ≤ (6 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        gcongr
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
end SmallR
/-- The clean win splits into cases A/B, case C without FTS overflow, signer incompleteness, and the FTS overflow
event (campaign X1 stage A; bounded by `fts_overflow_le`). -/
theorem cleanWin_le_cases (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z ∧ WPair.NoOverflow adversary z |
        SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ClaudeWCT.W9.T3.Security.FtsOverflow z.1 |
        SeccLaw.completedExperiment adversary q hq] := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) ((probEvent_or_le _ _ _).trans
    (add_le_add ((probEvent_or_le _ _ _).trans (add_le_add (probEvent_or_le _ _ _) le_rfl)) le_rfl))
  intro z hz hclean
  by_cases hov : ClaudeWCT.W9.T3.Security.FtsOverflow z.1
  · exact Or.inr ⟨hclean, hov⟩
  by_cases hcomp : BPB.SignerComplete z.2
  · rcases completed_split_src adversary q hq z hz hclean hcomp with h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hclean, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hclean, h, WPair.noOverflow_of_outIdx adversary z fun g i c hs =>
        ClaudeWCT.W9.T3.Security.logNoOverflow_of_not_ftsOverflow adversary q hq z hz hov g i c hs⟩))
    · exact absurd h (CaseC.caseCSignedPinned_impossible adversary q hq z hz hclean)
  · exact Or.inl (Or.inr hcomp)
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Secc
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security (QueryRecorded.CleanWin)
open ClaudeWCT.W9.T3.Security.SeccClosingW9 (budgetSplit largeBound)
open ClaudeWCT.W9.T3M.Final (AdversaryP SecurityP)
def LargeRouteBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment adversary q hq] ≤
      largeBound q
/-- The small case-C bound from the near and pair bounds on runs without FTS overflow (campaign X1 stage A). -/
theorem caseCSmallBound_of
    (hnear : ClaudeWCT.W9.T3.Security.CaseC.NearBoundOn ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
      ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.WPair.NoOverflow
      ClaudeWCT.W9.T3.Security.Wots.nearTerm)
    (hpair : ClaudeWCT.W9.T3.Security.WPair.PairGuessBoundNO SigGolfCandidate.T3.Security.BPair.pairTerm) :
    ClaudeWCT.W9.T3.Security.Wots.CaseCSmallBound :=
  ClaudeWCT.W9.T3.Security.CaseC.caseC_small_bound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
    ClaudeWCT.W9.T3.Security.CaseC.caseCSplitInterface ClaudeWCT.W9.T3.Security.WPair.NoOverflow
    ClaudeWCT.W9.T3.Security.Wots.nearTerm SigGolfCandidate.T3.Security.BPair.pairTerm
    ClaudeWCT.Numerics.WCTPrice.wct_excessBound_2_32 hnear hpair
end ClaudeWCT.W9.T3.Secc
end

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (LeafAddr entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sourceMessages_lower (answers : Answers) (index : Nat) (hidx : index < 2^31)
    (n : Nat) (hn : 1 ≤ n) (hn4 : n < 4) :
    CanonicalRef.sourceMessages answers (routeLeaf index (Fin.ofNat 4 (n-1))) =
      WCT9.LayerMsg.pair
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).1
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).2 := by
  have hl : (Fin.ofNat 4 (n-1) : Layer).val < 3 := by
    rw [Extract.ofNat_val (n-1) (by omega)]; omega
  have hm : CanonicalRef.sourceMessages answers (routeLeaf index (Fin.ofNat 4 (n-1))) =
      leafMsg answers (routeLeaf index (Fin.ofNat 4 (n-1))) := by
    unfold CanonicalRef.sourceMessages leafMsg
    simp only [routeLeaf, hl, dite_true]
  rw [hm, WotsExtract.leafMsg_route answers index _ hidx]
  exact Extract.honestMsg_lower answers index n hn (by omega)

theorem sourceMessages_bottom (answers : Answers) (index : Nat) (hidx : index < 2^31) :
    CanonicalRef.sourceMessages answers (routeLeaf index 3) =
      WCT9.LayerMsg.pair (CanonicalRef.forestCommitment answers index).1
        (CanonicalRef.forestCommitment answers index).2 := by
  have hroute : (route index 3).2 * 2 ^ height 3 + (route index 3).1 = index := by
    change index / 64 * 64 + (index / 1) % 64 = index
    rw [Nat.div_one]
    omega
  simp only [CanonicalRef.sourceMessages, routeLeaf, show ¬ (3 : Layer).val < 3 by decide,
    dite_false, hroute, Nat.mod_eq_of_lt hidx]

theorem layers_source_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2^31)
    (msg : WCT9.LayerMsg) (hfit : Extract.msgFits 3 msg)
    (h : evalWithAnswerFn answers (layersCanonicalBC w index 4 msg) = some (Extract.honestRoot answers 0 0)) :
    WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
      (entriesOf answers (queried answers (layersCanonicalBC w index 4 msg))) ∨
    ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) w index lay) ∧
      msg = WCT9.LayerMsg.pair (CanonicalRef.forestCommitment answers index).1
        (CanonicalRef.forestCommitment answers index).2) := by
  have hs := layersCanonicalBC_wots_walk answers (CanonicalRef.sourceMessages answers) w index hidx
    (fun lay => CanonicalRef.sourceMessages_fit answers (routeLeaf index lay))
    (sourceMessages_lower answers index hidx) 4 (by decide) le_rfl msg hfit h
  rcases hs with hp | ⟨hg, hm⟩
  · exact Or.inl hp
  · right
    refine ⟨fun lay => hg lay lay.isLt, ?_⟩
    change msg = CanonicalRef.sourceMessages answers (routeLeaf index 3) at hm
    exact hm.trans (sourceMessages_bottom answers index hidx)
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (entriesOf_mono)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_source_walk (answers : Answers) (message : Message) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (Paired.verifyP message pk w) = true) :
    ∃ output : HashOutput,
      (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : Spec.Domain) ∈
        queried answers (Paired.verifyP message pk w) ∧
      output.toNat / 2^242 % 16384 < 791 ∧
      (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
      (WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
          (entriesOf answers (queried answers (Paired.verifyP message pk w))) ∨
        ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) w (WCT9.digestIndex output) lay) ∧
          evalWithAnswerFn answers (SharedV3.forest w (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) =
            CanonicalRef.forestCommitment answers (WCT9.digestIndex output) ∧
          ∀ q ∈ queried answers (SharedV3.forest w (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))),
            q ∈ queried answers (Paired.verifyP message pk w))) := by
  obtain ⟨output, top, hd, hf, hl, hqD, hqF, hqL⟩ := Paired.verifyP_split answers message pk w hv
  obtain ⟨hcounter, houtput, hquery⟩ := Paired.digestP_success answers message w output hd
  obtain ⟨hgate, hrank, hforest, hforestQ⟩ := Paired.ftsP_success answers w output top hf
  refine ⟨output, hcounter, houtput, hqD _ ?_, hgate, hrank, ?_⟩
  · rw [hquery]
    exact List.mem_singleton_self _
  · have hidx : WCT9.digestIndex output < 2^31 := Nat.mod_lt _ (by norm_num)
    rcases layers_source_walk answers w (WCT9.digestIndex output) hidx (.pair top.1 top.2) trivial
      (hpk ▸ hl) with hp | ⟨hg, hmsg⟩
    · exact Or.inl (hp.mono (entriesOf_mono hqL))
    · refine Or.inr ⟨hg, hforest.trans ?_, ?_⟩
      · exact Prod.ext (WCT9.LayerMsg.pair.inj hmsg).1 (WCT9.LayerMsg.pair.inj hmsg).2
      · intro q hq
        exact hqF q (hforestQ ▸ hq)
end ClaudeWCT.W9.T3.Security.CanonicalExtract
/-! r3h HonestN: the honest expand output is `witEncN` (img-v6 nonce pads). -/
namespace ClaudeWCT.W9.T3M.Extract.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] T3M.Paired.witEncN

theorem forest_openings_shape_N (answers : Answers) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (ho : ForestOpenings answers (T3M.Paired.witEncN output w) (digestIndex output)
      (rawChildFromOutput output) (fun coord => embed (forestRank output coord.val))) :
    w.signature.forest = (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 := by
  apply T3M.Paired.forest_eq_of_coordinates
  · intro coord i
    rw [buildForest_coordinateValues]
    have hc := ((ho.2 coord).2.1 i).1
    change V3.reveal (T3M.Paired.witEncN output w) coord.val i.val
      (wordDigit (forestRank output coord.val) i) =
      ClaudeWCT.WCT9.chainValue answers (digestIndex output) coord.val
        (rawChildFromOutput output coord).val (forestRank output coord.val) i at hc
    have hr : V3.reveal (T3M.Paired.witEncN output w) coord.val i.val
        (wordDigit (forestRank output coord.val) i) =
        T3M.Paired.coordinateValues w.signature.forest coord i := by
      unfold V3.reveal
      split
      · exact T3M.Paired.wleafValue_witEncN output w coord i
      · exact T3M.Paired.wchainValue_witEncN output w coord i
    exact hr.symm.trans hc
  · intro coord level hl
    rw [buildForest_coordinatePath answers output coord level hl]
    have hp := SharedV3.physical_lt coord.val (rawChildFromOutput output coord).val
      (rawChildFromOutput output coord).isLt
    have hmax : level≤SharedV3.lastLevel coord.val+1 := by
      by_cases he : coord.val < 8 ∧ coord.val % 2 = 0
      · simp only [if_pos he] at hl
        simp [SharedV3.lastLevel, SharedV3.first, he]
        omega
      · simp only [if_neg he] at hl
        simp [SharedV3.lastLevel, SharedV3.first, he]
        omega
    have hc := (ho.2 coord).2
    by_cases hle : level≤SharedV3.lastLevel coord.val
    · have hl6 : level<6 := by
        unfold SharedV3.lastLevel at hle
        split_ifs at hle <;> omega
      have hs := PathStepGood.sibling_eq answers (T3M.Paired.witEncN output w)
        (digestIndex output) coord.val (SharedV3.physical coord.val (rawChildFromOutput output coord).val)
        level hp hl6 _ (hc.2.1 level hle)
      rw [T3M.Paired.wsibling_witEncN output w coord level (by omega)] at hs
      exact hs
    · have he : level=SharedV3.lastLevel coord.val+1 := by omega
      subst level
      rw [←T3M.Paired.wtopOther_witEncN output w coord]
      exact hc.2.2
end ClaudeWCT.W9.T3M.Extract.Paired

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (LeafAddr)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Paired.witEncN CanonicalRef.sourceMessages

theorem good_shape_witEncN (answers : Answers) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay) :
    ∀ lay, HonestHint answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay → ∃ digits, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay)) (w.counters lay)))) =
      some digits ∧ w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 digits) := by
  exact good_shape_readout answers (CanonicalRef.sourceMessages answers) (WCT9.digestIndex output)
    (Paired.witEncN output w) w.signature w.counters hg (PairedNonce.wbcCtr_witEncN output w)
    (fun lay => sourceMessages_pair answers (routeLeaf (WCT9.digestIndex output) lay))
    (Paired.wvalueFor_witEncN output w) (Paired.wpath_witEncN output w)
end ClaudeWCT.W9.T3.Security.CanonicalExtract


namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoveredMessage_top_source (answers : Answers) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (index : Nat) (input : WCT9.LayerMsg) (result : RecoveredLayers) (messages : Layer → WCT9.LayerMsg)
    (hinput : input = messages 3)
    (hlower : ∀ n, n < 3 → messages (Fin.ofNat 4 n) =
      .pair (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).1
        (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).2)
    (hselections : ∀ lay : Layer, evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1
        (recoveredMessage answers sig index 4 input result.digits lay) 0 (WCT9.searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true))
    (hshape : ∀ lay : Layer, lay ≠ 0 → ∃ digits,
      WCT9.CanonicalPolicy.decode lay (evalWithAnswerFn answers (WCT9.encodingHash lay
        (WCT9.layerEncodingInput lay (route index lay).2 (route index lay).1 (messages lay)
          (result.counters.getD lay.val 0)))) = some digits ∧
      sig.layers lay = piecesSignature lay
        (WCT9.wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    recoveredMessage answers sig index 4 input result.digits 0 = messages 0 := by
  have step (lay : Layer) (hl : lay ≠ 0)
      (hm : recoveredMessage answers sig index 4 input result.digits lay = messages lay) :
      sig.layers lay = piecesSignature lay
        (WCT9.wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) ∧
      Cost.ValidDigits lay (result.digits.getD lay.val []) := by
    have hs := hselections lay
    rw [hm] at hs
    have hlim := WCT9.searchLimit_le lay
    have hp := (canonical_search_some' answers lay (hintFloor sig.policyHints lay)
      (route index lay).2 (route index lay).1 (messages lay) (WCT9.searchLimit lay) 0
      (result.counters.getD lay.val 0) (result.digits.getD lay.val []) (result.lows.getD lay.val true)
      (by unfold counterLimit at hlim; omega) hs).2.2.2
    have hd := (WCT9.CanonicalPolicy.producerDecodeAt_spec hp).1
    obtain ⟨ds, hds, hfields⟩ := hshape lay hl
    have heq := Option.some.inj (hds.symm.trans hd)
    subst ds
    exact ⟨hfields, canonical_decode_valid hd⟩
  have h3 := step 3 (by decide) (by change input = messages 3; exact hinput)
  have h2 := step 2 (by decide) (by
    change WCT9.LayerMsg.pair
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).1
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).2 = messages 2
    have hp := recoveredPair_of_pieces answers sig index 3 (by decide) _ h3.2 h3.1
    change evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 3
      (result.digits.getD 3 [])) = WCT9.builtPair answers 3 (route index 3).2 at hp
    rw [hp]
    exact (hlower 2 (by decide)).symm)
  have h1 := step 1 (by decide) (by
    change WCT9.LayerMsg.pair
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).1
      (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).2 = messages 1
    have hp := recoveredPair_of_pieces answers sig index 2 (by decide) _ h2.2 h2.1
    change evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 2
      (result.digits.getD 2 [])) = WCT9.builtPair answers 2 (route index 2).2 at hp
    rw [hp]
    exact (hlower 1 (by decide)).symm)
  change WCT9.LayerMsg.pair
    (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).1
    (evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).2 = messages 0
  have hp := recoveredPair_of_pieces answers sig index 1 (by decide) _ h1.2 h1.1
  change evalWithAnswerFn answers (WCT9.recoverLayerPair (mainSignature sig) index 1
    (result.digits.getD 1 [])) = WCT9.builtPair answers 1 (route index 1).2 at hp
  rw [hp]
  exact (hlower 0 (by decide)).symm

theorem expanded_canonical_selections (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay)
    (hf : evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest) =
        forestCommitment answers (WCT9.digestIndex output)) :
    ∃ (digits : List (List Nat)) (lows : List Bool),
      policyHintsValid w.signature.policyHints digits lows = true ∧
      (∀ lay, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (hintFloor w.signature.policyHints lay) (route (WCT9.digestIndex output) lay).2
        (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        0 (WCT9.searchLimit lay)) = some (w.counters lay, digits.getD lay.val [], lows.getD lay.val true)) ∧
      ∀ lay, w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (digits.getD lay.val [])) := by
  obtain ⟨_, counter, result, c, _, hr, hvalid, hsig, _, hcs, hhigh⟩ := Paired.expandN_selections answers message pk sig output w he
  have hs := recoverHintedLayers_selections answers (fillTopSignature sig 0) (WCT9.digestIndex output)
    (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4 le_rfl _ result hr
  let input : WCT9.LayerMsg := .pair
    (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
    (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2
  have hsel : ∀ lay, evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor w.signature.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers w.signature (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val [],
          result.lows.getD lay.val true) := by
    intro lay
    have hx := hs.2.2.2 lay lay.isLt
    change evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers (fillTopSignature sig 0) (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = _ at hx
    rw [recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt 0] at hx
    rw [hsig, hints_retained, recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt c]
    exact hx
  have hshape0 := good_shape_witEncN answers output w hg
  have hi : WCT9.digestIndex output < 2^31 := Nat.mod_lt _ (by decide)
  have lower : ∀ n, n < 3 → CanonicalRef.sourceMessages answers
      (routeLeaf (WCT9.digestIndex output) (Fin.ofNat 4 n)) =
      .pair (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).1
        (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).2 := by
    intro n hn
    have hm := sourceMessages_lower answers (WCT9.digestIndex output) hi (n+1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel, Extract.honestPair_eq] using hm
  have hin : input = CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 3) := by
    dsimp only [input]
    rw [hf, sourceMessages_bottom answers _ hi]
  have hshapeL : ∀ lay : Layer, lay ≠ 0 → ∃ ds, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        (result.counters.getD lay.val 0)))) = some ds ∧
      w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 ds) := by
    intro lay hl
    simpa only [hcs lay] using hshape0 lay (honestHint_lower answers _ _ _ hl)
  have htop := recoveredMessage_top_source answers w.signature (WCT9.digestIndex output) input result
    (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay)) hin lower hsel hshapeL
  -- The expander's hint is the producer's choice at the (source) top row.
  have hhint0 : HonestHint answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) 0 := by
    have hs0 := hsel 0
    rw [htop] at hs0
    have hlim := WCT9.searchLimit_le 0
    have hlow := (canonical_search_some' answers 0 (hintFloor w.signature.policyHints 0)
      (route (WCT9.digestIndex output) 0).2 (route (WCT9.digestIndex output) 0).1
      (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0)) (WCT9.searchLimit 0) 0
      (result.counters.getD 0 0) (result.digits.getD 0 []) (result.lows.getD 0 true)
      (by unfold counterLimit at hlim; omega) hs0).2.2.1
    obtain ⟨-, hpad, hhi⟩ := hg 0
    obtain ⟨left, right, hm⟩ := sourceMessages_pair answers (routeLeaf (WCT9.digestIndex output) 0)
    unfold HonestHint
    rw [PairedNonce.wbcCtr_witEncN, hpad, hhi, Paired.wtopHigh_witEncN, hhigh]
    have hrow : pad64 (layerEncodingInputP 0 (route (WCT9.digestIndex output) 0).2
        (route (WCT9.digestIndex output) 0).1 (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0))
        (w.counters 0) 0 (wbcRight (Paired.witEncN output w)) 1) =
        pad64 (WCT9.layerEncodingInput 0 (route (WCT9.digestIndex output) 0).2 (route (WCT9.digestIndex output) 0).1
          (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 0)) (w.counters 0)) := by
      rw [hm]; rfl
    rw [hrow, hcs 0, hlow]
    exact WCT9.verificationAnswer_honest 0 _
  have hshape' : ∀ lay, ∃ ds, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        (result.counters.getD lay.val 0)))) = some ds ∧
      w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 ds) := by
    intro lay
    by_cases hl : lay = 0
    · subst hl
      simpa only [hcs 0] using hshape0 0 hhint0
    · exact hshapeL lay hl
  have hall := recoveredSelections_canonical answers w.signature (WCT9.digestIndex output)
    input result (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    hin lower hsel hshape'
  refine ⟨result.digits, result.lows, ?_, ?_, fun lay => (hall lay).2⟩
  · rw [hsig, hints_retained]
    exact hvalid
  · intro lay
    rw [hcs lay]
    exact (hall lay).1
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_canonical_or_collision (answers : Answers) (message : Message) (pk : Digest)
    (wb : ClaudeWCT.W9.T3M.WBytes) (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (Paired.verifyP message pk wb) = true) :
    ∃ output : HashOutput,
      (wdc wb).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
      (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
        queried answers (Paired.verifyP message pk wb) ∧
      output.toNat / 2^242 % 16384 < 791 ∧
      (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
      (WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
          (entriesOf answers (queried answers (Paired.verifyP message pk wb))) ∨
        Extract.Paired.FtsHitIn answers (queried answers (Paired.verifyP message pk wb)) ∨
        ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
          Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))) := by
  obtain ⟨output,hc,hd,hq,hgate,hrank,hcases⟩ := verifyP_source_walk answers message pk wb hpk hv
  refine ⟨output,hc,hd,hq,hgate,hrank,?_⟩
  rcases hcases with hp | ⟨hg,hforest,hsub⟩
  · exact Or.inl hp
  · rcases Extract.Paired.forest_extract answers wb (WCT9.digestIndex output)
        (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))
        (WCT9.digestIndex_lt output) (Extract.Paired.branchCompatible_output output) hforest with ho | hh
    · exact Or.inr (Or.inr ⟨hg,ho⟩)
    · exact Or.inr (Or.inl ((Extract.Paired.forest_hit_fts answers wb (WCT9.digestIndex output)
        (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))
        (WCT9.digestIndex_lt output) hh).mono hsub))
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_canonical_selections (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    ∃ (digits : List (List Nat)) (lows : List Bool),
      policyHintsValid w.signature.policyHints digits lows = true ∧
      (∀ lay, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (hintFloor w.signature.policyHints lay) (route (WCT9.digestIndex output) lay).2
        (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        0 (WCT9.searchLimit lay)) = some (w.counters lay,digits.getD lay.val [],lows.getD lay.val true)) ∧
      ∀ lay, w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (digits.getD lay.val [])) := by
  obtain ⟨result,hs,hrho,hhints,hforest,hpieces,hdigest,hcounters⟩ :=
    signFromOutput_components answers cache rho counter output w he
  have facts := searchPreparedLayers_some answers cache (WCT9.digestIndex output) _ _ result hs
  have hi : WCT9.digestIndex output<2^31 := WCT9.digestIndex_lt output
  refine ⟨result.digits, result.lows, ?_, ?_, ?_⟩
  · rw [hhints]
    exact facts.hints_valid
  · intro lay
    rw [hhints,hcounters lay]
    have hx := facts.hinted_searches lay
    rw [buildForest_commitment] at hx
    have hm : CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay) =
        (if lay=3 then .pair (forestCommitment answers (WCT9.digestIndex output)).1
          (forestCommitment answers (WCT9.digestIndex output)).2 else
          let lower : Layer := Fin.ofNat 4 (lay.val+1)
          .pair (WCT9.builtPair answers lower (route (WCT9.digestIndex output) lower).2).1
            (WCT9.builtPair answers lower (route (WCT9.digestIndex output) lower).2).2) := by
      by_cases h3 : lay = 3
      · subst lay
        exact sourceMessages_bottom answers _ hi
      · have hl : lay.val < 3 := by
          have hn : lay.val ≠ 3 := fun h => h3 (Fin.ext h)
          have := lay.isLt
          omega
        have he : (Fin.ofNat 4 lay.val : Layer) = lay := Fin.ext (Nat.mod_eq_of_lt lay.isLt)
        have hx := sourceMessages_lower answers _ hi (lay.val+1) (by omega) (by omega)
        simpa only [if_neg h3,Nat.add_sub_cancel,he,Extract.honestPair_eq] using hx
    rw [hm]
    exact hx
  · intro lay
    rw [hpieces lay,facts.honest_pieces hcache hi lay]
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expanded_eq_signer_signature (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w signed : SigGolfCandidate.Research.SharedForest.Witness) (counter : BitVec 32)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (Paired.witEncN output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (signFromOutput cache sig.rho counter output) = some signed) :
    w.signature = signed.signature := by
  have hforest := Extract.Paired.forest_openings_shape_N answers output w ho
  obtain ⟨_, _, _, c, _, _, _, hsig, _, _⟩ := Paired.expandN_selections answers message pk sig output w he
  have hforestSig : sig.forest = w.signature.forest := by rw [hsig];rfl
  have hf : evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest) =
      forestCommitment answers (WCT9.digestIndex output) := by
    rw [hforestSig,hforest]
    exact recoverForest_commitment answers _ _ _
  obtain ⟨da,la,hva,hsa,hpa⟩ := expanded_canonical_selections answers message pk sig output w he hg hf
  obtain ⟨db,lb,hvb,hsb,hpb⟩ := signFromOutput_canonical_selections answers cache hcache sig.rho counter output signed hs
  obtain ⟨_,_,hrho,_,hfs,_,_,_⟩ := signFromOutput_components answers cache sig.rho counter output signed hs
  apply signature_unique_of_selections answers (WCT9.digestIndex output)
    (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    w.signature signed.signature w.counters signed.counters da db la lb _ (hforest.trans hfs.symm)
    hva hvb hsa hsb hpa hpb
  rw [hsig,nonce_retained,hrho]

 theorem same_nonce_signed_wire (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig signedSig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEncN output w)
      (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (Paired.witEncN output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload cache message) = some signedSig)
    (hrho : sig.rho = signedSig.rho) :
    SharedCodec.sigBC sig = SharedCodec.sigBC signedSig := by
  obtain ⟨counter,N,signed,hd,hsigned,hsig⟩ := signPayload_components answers cache message signedSig hs
  obtain ⟨_,_,hnonce,_,_,_,_,_⟩ := signFromOutput_components answers cache
    (evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message)) counter N signed hsigned
  have hr : sig.rho = evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message) :=
    hrho.trans ((congrArg (fun s : SigGolfCandidate.Research.SharedForest.Signature => s.rho) hsig).symm.trans hnonce)
  obtain ⟨_,ec,_,c,hed,_,_,hw,_,_⟩ := Paired.expandN_selections answers message pk sig output w he
  rw [hr,hd] at hed
  have hout : N=output := congrArg Prod.snd (Option.some.inj hed)
  subst N
  have heq := expanded_eq_signer_signature answers cache hcache message pk sig output w signed counter he hg ho
    (by rw [hr];exact hsigned)
  calc
    SharedCodec.sigBC sig = SharedCodec.sigBC (fillTopSignature sig c) := (SharedCodec.sigBC_fillTopSignature sig c).symm
    _ = SharedCodec.sigBC w.signature := by rw [hw]
    _ = SharedCodec.sigBC signedSig := by rw [heq,hsig]
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem fresh_witness_not_signed_digest (log : QueryLog Requests) (message : Message)
    (wb : WBytes) (rho : Digest) (hfresh : Final.Paired.Fresh log (.witness message wb)) :
    ¬ SignedDigest log message rho := by
  rintro ⟨entry,hin,hm,sig,he,_⟩
  exact hfresh ⟨entry,hin,hm,by rw [he];rfl⟩

theorem fresh_signature_not_signed_digest (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = cacheRegion (maskedTop answers)) (log : QueryLog Requests)
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (authenticatedSign published entry.1))
    (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hfresh : Final.Paired.Fresh log (.signature message sig))
    (he : evalWithAnswerFn answers (T3M.Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, CanonicalExtract.Good answers (CanonicalRef.sourceMessages answers)
      (T3M.Paired.witEncN output w) (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (T3M.Paired.witEncN output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val))) :
    ¬ SignedDigest log message sig.rho := by
  rintro ⟨entry,hin,hm,signed,hsigned,hrho⟩
  have hreply := hlog entry hin
  rw [hsigned,eval_authenticatedSign] at hreply
  have hsource : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload published message) = some signed := by
    by_cases hc : entry.1.cache = published
    · rw [if_pos hc,hc,hm] at hreply
      exact hreply.symm
    · rw [if_neg hc] at hreply
      cases hreply
  have hwire := CanonicalExtract.same_nonce_signed_wire answers published hcache message pk sig signed output w
    he hg ho hsource hrho.symm
  apply hfresh
  refine ⟨entry,hin,hm,?_⟩
  rw [hsigned,Option.map_some,hwire]
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (entriesOf_mono)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem checkForgery_canonical_or_collision (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = cacheRegion (maskedTop answers)) (pk : Digest)
    (hpk : pk = Extract.honestRoot answers 0 0) (log : QueryLog Final.Paired.Requests)
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (WPair.Paired.authenticatedSign published entry.1))
    (forgery : Final.Paired.ForgeryP)
    (haccept : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true) :
    WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
        (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) ∨
      Extract.Paired.FtsHitIn answers (queried answers (Final.Paired.checkForgeryP pk log forgery)) ∨
      ∃ (message : Message) (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
        Final.Paired.WitnessOf answers pk forgery message wb ∧
        (wdc wb).toNat < WCT9.digestVerifyWindow ∧
        evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
        (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
          queried answers (Final.Paired.checkForgeryP pk log forgery) ∧
        output.toNat / 2^242 % 16384 < 791 ∧
        (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
        (∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
        Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
          (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) ∧
        ¬ WPair.Paired.SignedDigest log message (wrho wb) := by
  obtain ⟨hfresh,message,wb,hw,hv,hsub⟩ := Final.Paired.check_accepting answers pk log forgery haccept
  obtain ⟨output,hc,hd,hq,hgate,hrank,hcases⟩ :=
    verifyP_canonical_or_collision answers message pk wb hpk hv
  rcases hcases with hp | hh | ⟨hg,ho⟩
  · exact Or.inl (hp.mono (entriesOf_mono hsub))
  · exact Or.inr (Or.inl (hh.mono hsub))
  · refine Or.inr (Or.inr ⟨message,wb,output,hw,hc,hd,hsub _ hq,hgate,hrank,hg,ho,?_⟩)
    cases forgery with
    | witness sourceMessage sourceWitness =>
        obtain ⟨hm,hb⟩ := hw
        subst sourceMessage sourceWitness
        exact WPair.Paired.fresh_witness_not_signed_digest log message wb (wrho wb) hfresh
    | signature sourceMessage sig =>
        obtain ⟨hm,he⟩ := hw
        subst sourceMessage
        obtain ⟨N,w,hn,rfl⟩ := Paired.expandB_some answers message pk sig wb he
        have hout : N = output := (Paired.expandN_digest answers message pk sig N w hn).symm.trans hd
        subst N
        rw [Paired.expandN_nonce answers message pk sig output w hn]
        exact WPair.Paired.fresh_signature_not_signed_digest answers published hcache log hlog
          message pk sig output w hfresh hn hg ho
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.CanonicalExtract
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def FreshForestAt (answers : Answers) (pk : Digest) (log : QueryLog Final.Paired.Requests)
    (forgery : Final.Paired.ForgeryP) : Prop :=
  ∃ (message : Message) (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
        Final.Paired.WitnessOf answers pk forgery message wb ∧
        (wdc wb).toNat < WCT9.digestVerifyWindow ∧
        evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
        (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
          queried answers (Final.Paired.checkForgeryP pk log forgery) ∧
        output.toNat / 2^242 % 16384 < 791 ∧
        (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
        (∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
        Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
          (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) ∧
        ¬ WPair.Paired.SignedDigest log message (wrho wb)

def FreshForestCase (adversary : Final.Paired.AdversaryP)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked ∧
    generated.value.1 = Extract.honestRoot z.2 0 0 ∧
    generated.value.2.region = Correctness.cacheRegion (Correctness.maskedTop z.2) ∧
    (∀ entry ∈ interaction.value.2,
      entry.2 = evalWithAnswerFn z.2 (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    ∃ forgery, interaction.value.1 = some forgery ∧
      evalWithAnswerFn z.2 (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) = true ∧
      FreshForestAt z.2 generated.value.1 interaction.value.2 forgery

theorem completed_split_canonical (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) :
    CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z := by
  by_cases hab : CaseABEv combinedEvent adversary z
  · exact Or.inl hab
  right
  unfold CaseABEv CaseABEvAt at hab
  push Not at hab
  obtain ⟨generated,interaction,checked,hsplit,forgery,hf,hnot⟩ := hab
  obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  obtain ⟨_,hpk,hcache,hlog,hverdict⟩ := hsplit.facts z.2 ha hclean.1
  obtain ⟨forgery',hf',hcheck,_⟩ := PairedReference.Ref.verdict_accepts z.2 _ _ hverdict
  have heq : forgery' = forgery := Option.some.inj (hf'.symm.trans hf)
  subst forgery'
  rcases CanonicalExtract.checkForgery_canonical_or_collision z.2 generated.value.2 hcache
      generated.value.1 hpk interaction.value.2 hlog forgery hcheck with hp | hh | hgood
  · exact (hnot ⟨hcheck,Or.inl hp⟩).elim
  · exact (hnot ⟨hcheck,Or.inr (PairedReference.ftsHitIn_structuralHitTrace hh)⟩).elim
  · exact ⟨generated,interaction,checked,hsplit,hpk,hcache,hlog,forgery,hf,hcheck,hgood⟩
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem cleanWin_le_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv combinedEvent adversary z |
        PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z |
        PairedSeccLaw.completedExperiment adversary q hq] := by
  rw [← PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) (probEvent_or_le _ _ _)
  intro z hz hclean
  rcases completed_split_canonical adversary q hq z hz hclean with hab | hf
  · exact Or.inl ⟨hclean,hab⟩
  · exact Or.inr ⟨hclean,hf⟩
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem checker_forest_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true) :
    ∀ query ∈ queried answers (SharedV3.forest w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))),
      query ∈ queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  obtain ⟨_,m',w',hw',hv,hq⟩ := Final.Paired.check_accepting answers pk log forgery hcheck
  obtain ⟨rfl,rfl⟩ := PairedReference.Ref.witnessOf_unique hw hw'
  obtain ⟨out,top,hd',hf,_,_,hqF,_⟩ := Paired.verifyP_split answers message pk w hv
  obtain ⟨_,hout,_⟩ := Paired.digestP_success answers message w out hd'
  have he : out = output := hout.symm.trans hd
  rw [he] at hf hqF
  obtain ⟨_,_,_,hforestQ⟩ := Paired.ftsP_success answers w output top hf
  intro query hquery
  exact hq query (hqF query (hforestQ ▸ hquery))

theorem checker_slot_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))
    (k : Fin 9) (t : Fin 6) (p : Fin 4) (hp : p.val = 4-WPair.Paired.deficit output k t) :
    (.inl (.inr (Guess.honestProbe answers (WPair.Paired.chainOf output k t,p))) : Spec.Domain) ∈
      queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  apply checker_forest_queries answers pk log forgery message w output hw hd hcheck
  rw [WPair.Paired.honestProbe_slot]
  have hp' : p.val = 4-WCT9.digit (WCT9.embed (forestRank output k.val)) t := hp
  rw [hp']
  apply Extract.Paired.active_slot_queried answers w (WCT9.digestIndex output)
    (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) (WCT9.digestIndex_lt output) ho
  have hplt := p.isLt
  omega

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def FullCovered (answers : Answers) (log : QueryLog Final.Paired.Requests) (output : HashOutput) : Prop :=
  ∀ k t, WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs answers log) output k t

def NearGuess (answers : Answers) (log : QueryLog Final.Paired.Requests)
    (output : HashOutput) (trace : List SigGolfCandidate.T3.Security.Wots.Entry) : Prop :=
  ∃ (k : Fin 9) (t : Fin 6) (cell : Guess.GCoord),
    cell.1 = WPair.Paired.chainOf output k t ∧
    cell.2.val = 4-WPair.Paired.deficit output k t ∧
    WPair.Paired.GuessedIn answers log trace cell ∧
    ∀ k' t', (k',t') ≠ (k,t) →
      WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs answers log) output k' t'

def PairGuessIn (answers : Answers) (log : QueryLog Final.Paired.Requests)
    (trace : List SigGolfCandidate.T3.Security.Wots.Entry) : Prop :=
  ∃ cell cell' : Guess.GCoord, cell.1 ≠ cell'.1 ∧
    WPair.Paired.GuessedIn answers log trace cell ∧ WPair.Paired.GuessedIn answers log trace cell'

theorem checker_coverage_cases (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) :
    FullCovered answers log output ∨
      NearGuess answers log output (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) ∨
      PairGuessIn answers log (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) := by
  let trace := entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))
  let slot (k : Fin 9) (t : Fin 6) (ha : 1 ≤ WPair.Paired.deficit output k t) : Guess.GCoord :=
    (WPair.Paired.chainOf output k t,⟨4-WPair.Paired.deficit output k t,by omega⟩)
  have make (k : Fin 9) (t : Fin 6) (ha : 1 ≤ WPair.Paired.deficit output k t)
      (hu : ¬WPair.Paired.ChainCovered (WPair.Paired.loggedOutputs answers log)
        (WPair.Paired.chainOf output k t) (4-WPair.Paired.deficit output k t)) :
      WPair.Paired.GuessedIn answers log trace (slot k t ha) := by
    refine ⟨hu,answers (.inl (.inr (Guess.honestProbe answers (slot k t ha)))),?_⟩
    exact WotsExtract.mem_entriesOf (checker_slot_queries answers pk log forgery message w output
      hw hd hcheck ho k t (slot k t ha).2 rfl)
  rcases WPair.Paired.caseC_slots (WPair.Paired.loggedOutputs answers log) output with
    hall | ⟨k,t,ha,hu,hrest⟩ | ⟨k,t,k',t',hne,ha,hu,ha',hu'⟩
  · exact Or.inl hall
  · exact Or.inr (Or.inl ⟨k,t,slot k t ha,rfl,rfl,make k t ha hu,hrest⟩)
  · exact Or.inr (Or.inr ⟨slot k t ha,slot k' t' ha',WPair.Paired.chainOf_ne hne,
      make k t ha hu,make k' t' ha' hu'⟩)
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The fully covered fresh-forest case, restricted to complete source tables. -/
def FullForestEvent (adversary : Final.Paired.AdversaryP) (q : Nat)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  y.1=true ∧ countOf y.2≤q ∧
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    interaction.value.2.length≤2^32 ∧
    (∀ entry∈interaction.value.2,entry.2=evalWithAnswerFn A
      (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    (∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature) ∧
    ∃ (forgery : Final.Paired.ForgeryP) (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
      interaction.value.1=some forgery ∧
      evalWithAnswerFn A (digest (wrho w) message (wdc w))=output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) ∧
      output.toNat/2^242%16384<791 ∧
      (∀ k : Fin 9,rawForestRank output k.val<563) ∧
      ¬WPair.Paired.SignedDigest interaction.value.2 message (wrho w) ∧
      FullCovered A interaction.value.2 output

theorem paired_recordMatches (published : SigGolfCandidate.T3.Cache) (request : Request) :
    Prod.fst <$> ClaudeWCT.Bank.Paired.bankSpec.authenticatedRecord
      ClaudeWCT.Bank.Paired.payAfterDigest published request =
        PairedOuter.FullGame.authenticatedSign published request :=
  ClaudeWCT.Bank.Paired.record_erasure published request

theorem paired_bank_search (rho : Digest) (message : Message) :
    ClaudeWCT.Bank.Paired.bankSpec.search rho message 0 ClaudeWCT.Bank.Paired.bankSpec.limit =
      sharedDigestSearch rho message 0 WCT9.digestAttemptLimit :=
  (ClaudeWCT.Bank.Paired.digestSearch_public rho message WCT9.digestAttemptLimit 0).symm

theorem paired_bank_covered (X : List HashOutput) (N : HashOutput)
    (h : ∀ k t, WPair.Paired.SlotCovered X N k t) :
    ClaudeWCT.Bank.Paired.bankSpec.covered X N := by
  apply (ClaudeWCT.Bank.Paired.covered_source X N).mpr
  exact h

theorem full_event_potential (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    1≤ClaudeWCT.Bank.Paired.bankSpec.potential q b.2 := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hcover⟩ := hfull
  obtain ⟨prior,hprior⟩ := hsplit.checker_event A hA forgery hforgery _ hquery
  have hevent := hsplit.checked_mem hprior
  change evalWithAnswerFn A (digest (wrho w) message (wdc w))=N at hN
  have hevent' : (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),N⟩ :
      FirstHit.QueryEvent)∈b.2.2.events := by
    change (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),
      evalWithAnswerFn A (digest (wrho w) message (wdc w))⟩ : FirstHit.QueryEvent)∈_ at hevent
    rwa [hN] at hevent
  apply PairedBankLink.full_potential ClaudeWCT.Bank.Paired.bankSpec
    ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches
    ClaudeWCT.Bank.Paired.payHashOnly ClaudeWCT.Bank.Paired.payRho ClaudeWCT.Bank.Paired.payAvoids
    paired_bank_search paired_bank_covered adversary q hq b hb A hA hcount
    generated interaction checked hsplit hlen
    (pad64 (digestInput (wrho w) message (wdc w))) N ⟨wrho w,message,wdc w,rfl⟩ prior hevent'
  · exact WPair.Paired.fresh_digest_not_signer_eval A generated.value.2 interaction.value.2 hsig
      message (wrho w) (wdc w) hcomp hfresh
  · change ClaudeWCT.Bank.Paired.admissible N=true
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
  · exact hcover

theorem completed_full_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W => ClaudeWCT.Bank.Paired.price W-(1023/1024 : ENNReal))≤rate) :
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      (CaseC.theta+1/64)/2^128 * PairedSeccLaw.expectedCharge adversary q hq
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) +
      (q : ENNReal)*rate/2^128 := by
  apply PairedBankLink.completed_event_le_shared ClaudeWCT.Bank.Paired.bankSpec
    ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches ClaudeWCT.Bank.Paired.payNotDigest
    ClaudeWCT.Bank.Paired.payAvoids (FullForestEvent adversary q) adversary q hq rate hrate
  intro b hb tables hfull
  exact full_event_potential adversary q hq b hb _
    (fun input answer hk => SigGolfCandidate.T3.Security.SeccLaw.completeWith_agrees _ tables input answer hk) hfull
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem full_event_target_covered (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    b.2.1.dead=false ∧ ∃ N∈b.2.1.targets, ClaudeWCT.Bank.Paired.admissible N=true ∧
      ClaudeWCT.Bank.Paired.Covered b.2.1.exposures N := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hcover⟩ := hfull
  obtain ⟨prior,hprior⟩ := hsplit.checker_event A hA forgery hforgery _ hquery
  have hevent := hsplit.checked_mem hprior
  change evalWithAnswerFn A (digest (wrho w) message (wdc w))=N at hN
  have hevent' : (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),N⟩ :
      FirstHit.QueryEvent)∈b.2.2.events := by
    change (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),
      evalWithAnswerFn A (digest (wrho w) message (wdc w))⟩ : FirstHit.QueryEvent)∈_ at hevent
    rwa [hN] at hevent
  have hadm : ClaudeWCT.Bank.Paired.admissible N=true := by
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
  have hc : b.2.1.dead=false ∧ N∈b.2.1.targets ∧
      ClaudeWCT.Bank.Paired.bankSpec.covered b.2.1.exposures N := by
    apply PairedBankLink.full_target_covered ClaudeWCT.Bank.Paired.bankSpec
      ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches
      ClaudeWCT.Bank.Paired.payHashOnly ClaudeWCT.Bank.Paired.payRho ClaudeWCT.Bank.Paired.payAvoids
      paired_bank_search paired_bank_covered adversary q hq b hb A hA hcount
      generated interaction checked hsplit hlen
      (pad64 (digestInput (wrho w) message (wdc w))) N ⟨wrho w,message,wdc w,rfl⟩ prior hevent'
    · exact WPair.Paired.fresh_digest_not_signer_eval A generated.value.2 interaction.value.2 hsig
        message (wrho w) (wdc w) hcomp hfresh
    · change ClaudeWCT.Bank.Paired.admissible N=true
      rw [ClaudeWCT.Bank.Paired.admissible_source]
      simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
    · exact hcover
  
  exact ⟨hc.1,N,hc.2.1,hadm,hc.2.2⟩

theorem full_event_flexible_potential (theta : ENNReal)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    1≤ClaudeWCT.Bank.Paired.flexiblePotential theta q b.2 := by
  obtain ⟨halive,N,hN,hadm,hcov⟩ := full_event_target_covered adversary q hq b hb A hA hfull
  exact ClaudeWCT.Bank.Paired.flexible_potential_win theta q b.2 halive hfull.2.1
    (Or.inr ⟨N,hN,hadm,hcov⟩)

theorem completed_flexible_full_bound (theta rate : ENNReal)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W => ClaudeWCT.Bank.Paired.price W-theta)≤rate) :
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      (theta+1/1024)/2^128 * PairedSeccLaw.expectedCharge adversary q hq
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) +
      (q : ENNReal)*rate/2^128 := by
  rw [PairedBankLink.completed_event_eq]
  have he := congrArg (fun law : PMF (Bool × QueryRecorded.State) =>
    expectedValue law (PairedBankLink.completedWeight (FullForestEvent adversary q)))
      (PairedBankLink.recordedExperiment_eq ClaudeWCT.Bank.Paired.bankSpec
        ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches adversary q hq)
  rw [PMF.monad_map_eq_map,CaseC.expectedValue_pmf_map] at he
  rw [he]
  refine (ClaudeWCT.Bank.Paired.flexible_event_le theta rate hrate (PairedBankLink.rest adversary) q
    (PairedBankLink.completedWeight (FullForestEvent adversary q)) (fun _ => probEvent_le_one) ?_).trans ?_
  · intro b hb hnonzero
    by_cases hex : ∃ tables, FullForestEvent adversary q (b.1,b.2.2)
        (SigGolfCandidate.T3.Security.SeccLaw.completeWith (lazyOf b.2.2) tables)
    · obtain ⟨tables,ht⟩ := hex
      exact full_event_flexible_potential theta adversary q hq b hb _
        (fun input answer hk => SigGolfCandidate.T3.Security.SeccLaw.completeWith_agrees _ tables input answer hk) ht
    · exfalso
      apply hnonzero
      unfold PairedBankLink.completedWeight
      simp only [probEvent_eq_tsum_ite]
      have hfalse : ∀ tables, ¬FullForestEvent adversary q (b.1,b.2.2)
          (SigGolfCandidate.T3.Security.SeccLaw.completeWith (lazyOf b.2.2) tables) :=
        fun tables ht => hex ⟨tables,ht⟩
      simp [hfalse]
  · exact add_le_add (mul_le_mul' le_rfl
      (PairedBankLink.expectedBirths_le_shared ClaudeWCT.Bank.Paired.bankSpec
        ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches adversary q hq)) le_rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The remaining fresh-forest cases, with a predicate on the actual checker trace. -/
def PartialForestEvent
    (Q : Answers → QueryLog Final.Paired.Requests → HashOutput → List Entry → Prop)
    (adversary : Final.Paired.AdversaryP) (q : Nat)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  y.1=true ∧ countOf y.2≤q ∧
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    interaction.value.2.length≤2^32 ∧
    (∀ entry∈interaction.value.2,entry.2=evalWithAnswerFn A
      (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    (∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature) ∧
    ∃ (forgery : Final.Paired.ForgeryP) (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
      interaction.value.1=some forgery ∧
      evalWithAnswerFn A (digest (wrho w) message (wdc w))=output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) ∧
      output.toNat/2^242%16384<791 ∧
      (∀ k : Fin 9,rawForestRank output k.val<563) ∧
      ¬WPair.Paired.SignedDigest interaction.value.2 message (wrho w) ∧
      Q A interaction.value.2 output
        (entriesOf A (queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery)))

abbrev NearForestEvent := PartialForestEvent NearGuess
abbrev PairForestEvent := PartialForestEvent (fun A log _ => PairGuessIn A log)

def IncompleteForestEvent (adversary : Final.Paired.AdversaryP)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    ¬∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature

theorem completed_forest_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1)
    (hfresh : FreshForestCase adversary z) :
    FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 := by
  obtain ⟨generated,interaction,checked,hsplit,hpk,hcache,hsig,forgery,hforgery,hcheck,
    message,w,N,hw,hctr,hN,hquery,hgate,hranks,hgood,hopen,hfresh⟩ := hfresh
  by_cases hcomp : ∀ message, ∃ signature, evalWithAnswerFn z.2
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature
  · obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
    obtain ⟨_,_,_,_,hverdict⟩ := hsplit.facts z.2 ha hclean.1
    have hlen : interaction.value.2.length≤2^32 := by
      simp only [PairedOuter.GameWith.verdict,hforgery,PairedOuter.PaddedGame.checker,
        evalWithAnswerFn_bind,evalWithAnswerFn_pure,Bool.and_eq_true,decide_eq_true_eq] at hverdict
      exact hverdict.1
    rcases checker_coverage_cases z.2 generated.value.1 interaction.value.2 forgery
      message w N hw hN hcheck hopen with hc | hc | hc
    · exact Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩
    · exact Or.inr (Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨generated,interaction,checked,hsplit,hcomp⟩))

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem completed_forest_le_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] := by
  have h := Ref.pmf_probEvent_mono (PairedSeccLaw.completedExperiment adversary q hq)
    (fun z hz (h : QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z) =>
      completed_forest_cases adversary q hq z hz h.1 h.2)
  refine h.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ = _ := by ac_rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem GameSplit.unique_log_events {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool}
    {generated generated' : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction interaction' : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked checked' : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked)
    (h' : GameSplit adversary result generated' interaction' checked') :
    generated=generated' ∧ interaction=interaction' ∧ checked.events=checked'.events := by
  have hev : result.events=generated'.events++(interaction'.events++checked'.events) := by rw [h'.2.2.2]
  obtain ⟨hg,hi⟩ := PairedBankLink.split_unique adversary result generated' h'.1 interaction' h'.2.1
    checked'.events hev generated interaction checked h
  refine ⟨hg,hi,?_⟩
  have hev' : result.events=generated.events++(interaction.events++checked.events) := by rw [h.2.2.2]
  rw [hg,hi] at hev'
  exact List.append_cancel_left (List.append_cancel_left (hev'.symm.trans hev))

theorem GameSplit.checker_entries {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (A : Answers) (hA : CaseC.Agrees A result.state)
    (forgery : Final.Paired.ForgeryP) (hf : interaction.value.1=some forgery) :
    ∀ entry∈SigGolfCandidate.T3.Security.Wots.entriesOf A
      (queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery)),
      entry∈BPair.publicEntries checked.events := by
  rintro ⟨input,answer⟩ he
  obtain ⟨hq,ha⟩ := SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf_iff.mp he
  obtain ⟨prior,hprior⟩ := h.checker_event A hA forgery hf _ hq
  have hm := SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hprior
  rwa [ha] at hm
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_pair_implies (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hpair : PairForestEvent adversary q (z.1.1,z.1.2.2) z.2) :
    WPair.Paired.PairGuess adversary z := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hpair⟩ := hpair
  intro generated' interaction' checked' hsplit'
  obtain ⟨_,hi,hc⟩ := hsplit.unique_log_events hsplit'
  rw [←hi,←hc]
  obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  have hsub := hsplit.checker_entries z.2 ha forgery hforgery
  obtain ⟨cell,cell',hne,hg,hg'⟩ := hpair
  exact ⟨cell,cell',hne,WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell hg,
    WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell' hg'⟩

theorem completed_pair_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ BPair.pairTerm q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans (WPair.Paired.pair_guess_bound_budget adversary q hq)
  intro z hz h
  exact ⟨h.1.2.1,completed_pair_implies adversary q hq z hz h.1,h.2⟩
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_near_implies (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hnear : NearForestEvent adversary q (z.1.1,z.1.2.2) z.2)
    (generated' interaction' checked')
    (hsplit' : PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1)
      generated' interaction' checked') :
    WPair.Paired.NearIn z.2 interaction'.value.2 (BPair.publicEntries checked'.events) := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hnear⟩:=hnear
  obtain ⟨_,hi,hc⟩:=hsplit.unique_log_events hsplit'
  rw [←hi,←hc]
  obtain ⟨_,ha⟩:=PairedSeccLaw.completed_agrees adversary q hq z hz
  have hsub:=hsplit.checker_entries z.2 ha forgery hforgery
  obtain ⟨k,t,cell,hcell,hdepth,hguess,hcover⟩:=hnear
  refine ⟨hlen,WPair.Paired.cacheCompleteLog_of_complete z.2 generated.value.2
    interaction.value.2 hsig hcomp,message,wrho w,wdc w,N,cell,?_,?_,hfresh,
    WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell hguess,k,t,hcover⟩
  · apply hsub
    rw [←hN]
    exact SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf hquery
  · rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks

variable {P : Type} [Fintype P] [SampleableType P]

theorem completed_near_bound (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,WPair.Paired.NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.near_bound_budget S hproducer hadmissible hmono hcovered rate hrate adversary q hq)
  intro z hz h
  exact ⟨h.1.2.1,fun generated interaction checked hs=>
    ⟨completed_near_implies adversary q hq z hz h.1 generated interaction checked hs,
      h.2 generated interaction checked hs⟩⟩

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

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
theorem prefixClassCount_le_length (s : RefSample) : Contacts.prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  unfold ContactAt maskAt CanonicalRef.ContactAt
  rw [CanonicalRef.depth_source_maskAt T a b (source_bounds ha).2,
    CanonicalRef.frontierValue_source_maskAt T a b (source_bounds ha) (source_bounds hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain7 b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRowW a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; exact congrArg some hm.symm
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (Contacts.prefixRowAt_unique (answers := T) ha hb ⟨_, va, by change depth T a - 1 < depth T a; omega, rfl⟩ ⟨_, vb, by change depth T b - 1 < depth T b; omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ Contacts.contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold Contacts.contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(Contacts.mem_sourceChains7 b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
/-- `(2^128 + 2q) T / ((1 - x) 2^128) = (1 + 2x) / (1 - x) · T`. -/
theorem big_div_mul (q : Nat) (T : ENNReal) :
    ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * T / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) =
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * T := by
  have h1 : (2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
  have e : ∀ y : ENNReal, ((2 : ENNReal) ^ 128 + ((2 * q : ℕ) : ENNReal)) * T * (y * ((2 : ENNReal) ^ 128)⁻¹) =
      y * T * ((2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹) + 2 * ((q : ENNReal) * ((2 : ENNReal) ^ 128)⁻¹) * y * T := by
    intro y
    push_cast
    ring
  rw [e, h1]
  ring
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem probEvent_le_six_split {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) (a b : ENNReal) (hab : a + b = 1) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] +
      (a * (Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p]) +
        b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]) := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  calc Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]
      = (a + b) * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := by rw [hab, one_mul]
    _ = a * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] +
          b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := add_mul _ _ _
    _ ≤ _ := by
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      exact probEvent_or_le _ _ _

noncomputable def prefixCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  w *
    (((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
        (1 - (q : ENNReal) / 2 ^ 128) +
      4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      2 * 93 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)) +
    v * 2 / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  7 / 4 + w * 2 * 5022 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
/-- Coefficient of the total seed-test error `Leaf.errTot` in the small-route primitive bound (campaign X1 B3). -/
noncomputable def errCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  w *
    ((1 + twoEdgeRate q * q) / (1 - (q : ENNReal) / 2 ^ 128) +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) +
      93 * ((q : ENNReal) / 2 ^ 128) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))) +
    v * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))

theorem weighted_union_le {α : Type} (law : PMF α)
    (E Failed Match Structural TwoEdge TwoContacts MarkerFirst ContactFirst : α → Prop)
    (q : Nat) (w v EP EE EO error : ENNReal) (hwv : w+v=1)
    (hsplit : ∀ s, E s → Failed s ∨ Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s)
    (hmatch : Pr[Match | law] ≤ 7/(4*2^128) * EE)
    (hstruct : Pr[Structural | law] ≤ (2^128:ENNReal)⁻¹ * EO)
    (hedge : Pr[TwoEdge | law] ≤ (twoEdgeRate q * EP + (1+twoEdgeRate q*q)*error)/(1-(q:ENNReal)/2^128))
    (htwo : Pr[TwoContacts | law] ≤
      (4*((q:ENNReal)/2^128)/2^128)*EP/(1-(q:ENNReal)/2^128)^2 +
      (2*((q:ENNReal)/2^128)*(1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)^2 +
        (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128))*error)
    (hmarker : Pr[MarkerFirst | law] ≤
      2*((q:ENNReal)/2^128)/(1-(q:ENNReal)/2^128)*((5022/2^128)*EE) +
      (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)*error)
    (hcontact : Pr[ContactFirst | law] ≤
      93*((q:ENNReal)/2^128)*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)))
    (hany : Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s | law] ≤
      ((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)) :
    Pr[E | law] ≤ Pr[Failed | law] + prefixCoeff q w v/2^128*EP +
      encodingCoeff q w v/2^128*EE + (2^128:ENNReal)⁻¹*EO + errCoeff q w v*error := by
  have h0 : Pr[E | law] ≤ Pr[Failed | law] +
      Pr[fun s => Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s | law] :=
    (probEvent_mono'' hsplit).trans (probEvent_or_le _ _ _)
  have h1 := probEvent_le_six_split law
    (fun s => Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s)
    Match Structural TwoEdge TwoContacts MarkerFirst ContactFirst (fun _ h => h) w v hwv
  refine (h0.trans (add_le_add le_rfl h1)).trans ?_
  calc _ ≤ Pr[Failed | law] +
      ((7/(4*2^128):ENNReal)*EE + (2^128:ENNReal)⁻¹*EO +
      (w*((twoEdgeRate q*EP+(1+twoEdgeRate q*q)*error)/(1-(q:ENNReal)/2^128) +
      ((4*((q:ENNReal)/2^128)/2^128)*EP/(1-(q:ENNReal)/2^128)^2 +
      (2*((q:ENNReal)/2^128)*(1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)^2 +
        (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128))*error) +
      (2*((q:ENNReal)/2^128)/(1-(q:ENNReal)/2^128)*((5022/2^128)*EE) +
      (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)*error) +
      93*((q:ENNReal)/2^128)*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128))) +
      v*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)))) := by
        gcongr
    _ = _ := by
      unfold prefixCoeff encodingCoeff errCoeff twoEdgeRate
      simp only [div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (by norm_num : (4:ENNReal)≠0)) (Or.inl (by norm_num : (4:ENNReal)≠⊤))]
      ring
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

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
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, Enc.chainAt p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3M.Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩

theorem chainOf_injective : Function.Injective Enc.chainAt := by
  rintro ⟨⟨l, t, f⟩, c⟩ ⟨⟨l', t', f'⟩, c'⟩ h
  simp only [Enc.chainAt, Enc.leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hf⟩, hc⟩ := h
  rw [Fin.ext ht, Fin.ext hf, Fin.ext hc]
set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, Core.errC adversary q (Enc.chainAt p) ≤ Contacts.errTot adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, Core.errC adversary q (Enc.chainAt p) =
      ∑ a ∈ Finset.univ.image Enc.chainAt, Core.errC adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image Enc.chainAt, Core.errC adversary q a ≤
      ∑ a ∈ (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7, Core.errC adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · unfold Core.errC
      rw [dif_neg h]
  have h3 : (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7 ⊆ Contacts.sourceChains7 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (Contacts.mem_sourceChains7 a).mpr ha.2
  rw [h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]

def MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
 ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   ¬CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) trace a

def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
 ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   ¬CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) trace a

def ReferenceFailed (s : RefSample) : Prop :=
 ∃ L, WotsExtract.SourceLeaf7 L ∧
   CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L = none

def EncodingMatch (s : RefSample) : Prop :=
 ∃ L, WotsExtract.SourceLeaf7 L ∧
   CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L ≠ none ∧
   CanonicalRef.EncodingMatchAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace L

def Structural (s : RefSample) : Prop :=
 CanonicalExtract.StructuralHitSrc s.answers (CanonicalRef.sourceMessages s.answers) s.trace ∨
   PairedReference.StructuralHitTrace s.answers s.trace

def TwoEdge (s : RefSample) : Prop :=
 ∃ a, WotsExtract.SourceChain7 a ∧ CanonicalRef.TwoEdgeAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a

def TwoContacts (s : RefSample) : Prop :=
 ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
   CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a ∧
   CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace b

def MarkerFirstEvent (s : RefSample) : Prop := ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a
def ContactFirstEvent (s : RefSample) : Prop := ∃ a, WotsExtract.SourceChain7 a ∧ ContactFirst s.answers s.trace a

def Combined (s : RefSample) : Prop :=
 CanonicalExtract.WotsPrimitiveSrc s.answers (CanonicalRef.sourceMessages s.answers) s.trace ∨
   PairedReference.StructuralHitTrace s.answers s.trace
/-- Stage 2 (C3, #866): `RowPad` is a triple (the row tweak's high word is a witness pad), so this is #866's
`SmallA.chainRowW_ne_encRow` (chain headers and row tweaks differ in their marker byte). -/
theorem chainRowW_ne_encRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : WCT9.LayerMsg)
    (c : BitVec 32) (pad : RowPad) : chainRowW a s v ≠ encRow L m c pad :=
  ClaudeWCT.W9.T3.Security.Wots.SmallA.chainRowW_ne_encRow a s v L m c pad

theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) trace a) (hc : CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧ ∀ j < k, ¬CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧ ∀ j < k, ¬CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, pad, answer, digits, -, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, pad, answer, digits, hfit, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, pad, answer, digits, hfit, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact chainRowW_ne_encRow _ _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩

theorem combined_cases (s : RefSample) (h : Combined s) :
 ReferenceFailed s ∨ EncodingMatch s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s := by
 rcases h with hp | hs
 · rcases hp with hm | hs | he | ht | ⟨a,ha,hm,hc⟩
   · obtain ⟨L,hL,hm⟩ := hm
     by_cases hf : CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L = none
     · exact Or.inl ⟨L,hL,hf⟩
     · exact Or.inr (Or.inl ⟨L,hL,hf,hm⟩)
   · exact Or.inr (Or.inr (Or.inl (Or.inl hs)))
   · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
   · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
   · rcases markerContact_split s.answers s.trace a hm hc with hm | hc
     · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a,ha,hm⟩)))))
     · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a,ha,hc⟩)))))
 · exact Or.inr (Or.inr (Or.inl (Or.inr hs)))

theorem structural_reference_le (adversary : Final.Paired.AdversaryP) (q : Nat)
 (hstruct : Pr[fun s => PairedReference.StructuralHitIn (PairedReference.referenceInputs adversary) s.answers s.trace |
   PairedReference.referenceExperiment adversary q] ≤
   (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
     (2^142:ENNReal)⁻¹) :
 Pr[Structural | PairedReference.referenceExperiment adversary q] ≤
   (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
     (2^142:ENNReal)⁻¹ := by
 refine le_trans (SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono _ fun s hs h => ?_) hstruct
 have hin := PairedReference.reference_trace_mem adversary q s hs
 exact h.elim (fun h => CanonicalExtract.structuralHitSrc_paired h hin)
   (fun h => PairedReference.StructuralHitTrace.toHitIn h hin)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nonstructural_contact (s : RefSample)
 (h : TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s) :
 ∃a∈Contacts.sourceChains7,CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a := by
 rcases h with ⟨a,ha,hd,_,middle,_,h2⟩ | ⟨a,_,ha,_,_,hc,_⟩ | ⟨a,ha,_,_,_,hc⟩ | ⟨a,ha,_,⟨hd,value,answer,hm,hl⟩,_,_⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,by omega,middle,h2⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hc⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hc⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hd,value,answer,List.mem_of_mem_take hm,hl⟩

theorem nonstructural_reference_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
 Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s |
   PairedReference.referenceExperiment adversary q] ≤
 ∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.contactCount s:ENNReal) := by
 rw [probEvent_eq_tsum_ite]
 apply ENNReal.tsum_le_tsum
 intro s
 split_ifs with h
 · obtain ⟨a,ha,hc⟩ := nonstructural_contact s h
   rw [PMF.probOutput_eq_apply]
   apply le_mul_of_one_le_right'
   have hp : 0 < Contacts.contactCount s := Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hc⟩⟩
   exact_mod_cast hp
 · exact zero_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem GameSplit.keygen_value {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (A : Answers) (ha:∀input answer,SourceReplay.known result.state input=some answer → A input=answer) :
    evalWithAnswerFn A keygen=generated.value := by
  obtain ⟨hg,hi,hc,heq⟩:=h
  have hs:result.state=checked.state:=by rw[heq]
  have hiext:SourceReplay.Extends interaction.state result.state:=by
    rw[hs]
    exact SourceReplay.run_extends _ interaction.state (checked.value,checked.state)
      (FirstHit.recorded_support _ _ _ hc)
  have hgext:SourceReplay.Extends generated.state result.state:=
    (SourceReplay.run_extends _ generated.state (interaction.value,interaction.state)
      (FirstHit.recorded_support _ _ _ hi)).trans hiext
  exact (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅,∅)
    (generated.value,generated.state) (FirstHit.recorded_support _ _ _ hg)).eval A
    (fun input answer hk=>ha input answer (SourceReplay.known_mono _ _ hgext hk))
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (lazyOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_incomplete_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138 := by
  refine (Ref.pmf_probEvent_mono (PairedSeccLaw.completedExperiment adversary q hq) ?_).trans
    (PairedSearchTable.completed_signer_failure adversary q hq)
  intro z hz hevent hcomplete
  obtain ⟨generated,interaction,checked,hsplit,hbad⟩:=hevent
  obtain ⟨_,ha⟩:=PairedSeccLaw.completed_agrees adversary q hq z hz
  have hk:=hsplit.keygen_value z.2 ha
  apply hbad
  intro message
  obtain ⟨sig,hsig⟩:=hcomplete message
  rw[hk] at hsig
  refine ⟨sig,?_⟩
  unfold SigGolfCandidate.Research.SharedForest.sign at hsig
  rw[evalWithAnswerFn_bind] at hsig
  split_ifs at hsig with hm
  · simp only[evalWithAnswerFn_pure,reduceCtorEq] at hsig
  · exact hsig

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_near_le_other (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*WPair.Paired.Counted.referenceOther adversary q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.Counted.completed_event_le_other adversary q hq
      (fun A log entries=>WPair.Paired.NearIn A log entries ∧ ¬WPair.Paired.OverflowIn A log)
      (fun A T log entries h hp=>⟨WPair.Paired.nearIn_short h log entries hp.1,
        fun ho=>hp.2 (WPair.Paired.overflowIn_short h.symm log ho)⟩)
      (fun A log entries entries' hsub hp=>⟨WPair.Paired.nearIn_mono A log entries entries' hsub hp.1,hp.2⟩)
      (fun _ _ _ hp=>hp.2) ?_)
  · intro z hz h
    exact ⟨h.1.2.1,fun generated interaction checked hs=>
      ⟨completed_near_implies adversary q hq z hz h.1 generated interaction checked hs,
        h.2 generated interaction checked hs⟩⟩
  · intro A log entries hp
    obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=hp.1
    exact ⟨cell,hguess⟩

theorem completed_near_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    (1-(q:ℝ)/2^128)*(Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧
      WPair.Paired.NoOverflow adversary z | PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      (WPair.Paired.Counted.referenceOther adversary q).toReal/2^128 := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using WPair.Paired.Counted.hazard_normalized
    (n:=2^128) (q:=q) (by omega) (WPair.Paired.Counted.referenceOther_ne_top adversary q)
    (completed_near_le_other adversary q hq)
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem referenceSearch_complete (answers : Answers) (hgood : ContextGood answers)
    (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) :
    referenceSearch answers (sourceMessages answers) L ≠ none := by
  let cache : SigGolfCandidate.T3.Cache := ⟨0,fun _=>0⟩
  exact referenceSearch_complete_of_routes answers cache
    (fun index hi => searchPreparedLayers_complete answers hgood cache index hi _ _) L hL
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.CanonicalSearch
attribute [local instance] Classical.propDecidable

theorem reference_failed_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
    Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139 := by
  refine (SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono _ ?_).trans
    (PairedSearchTable.context_failure adversary q)
  rintro s _ ⟨L,hL,hs⟩ hgood
  exact CanonicalRef.referenceSearch_complete s.answers hgood L hL hs
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable

def PartialForestNoOverflow (adversary : Final.Paired.AdversaryP) (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  (NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨ PairForestEvent adversary q (z.1.1,z.1.2.2) z.2) ∧
    WPair.Paired.NoOverflow adversary z

theorem completed_partial_le_other (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*WPair.Paired.Counted.referenceOther adversary q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.Counted.completed_event_le_other adversary q hq
      (fun A log entries=>(∃cell,WPair.Paired.GuessedIn A log entries cell) ∧ ¬WPair.Paired.OverflowIn A log)
      (fun A T log entries h hp=>⟨by
        obtain ⟨cell,hcell⟩:=hp.1
        exact ⟨cell,WPair.Paired.guessedIn_short h log entries cell hcell⟩,
        fun ho=>hp.2 (WPair.Paired.overflowIn_short h.symm log ho)⟩)
      (fun A log entries entries' hsub hp=>⟨by
        obtain ⟨cell,hcell⟩:=hp.1
        exact ⟨cell,WPair.Paired.guessedIn_mono A log entries entries' hsub cell hcell⟩,hp.2⟩)
      (fun _ _ _ hp=>hp.2) (fun _ _ _ hp=>hp.1))
  intro z hz h
  refine ⟨h.1.elim (fun hn=>hn.2.1) (fun hp=>hp.2.1),?_⟩
  intro generated interaction checked hs
  refine ⟨?_,h.2 generated interaction checked hs⟩
  rcases h.1 with hn | hp
  · obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=
      completed_near_implies adversary q hq z hz hn generated interaction checked hs
    exact ⟨cell,hguess⟩
  · obtain ⟨cell,cell',hne,hg,hg'⟩:=completed_pair_implies adversary q hq z hz hp generated interaction checked hs
    exact ⟨cell,hg⟩

theorem completed_partial_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    (1-(q:ℝ)/2^128)*(Pr[PartialForestNoOverflow adversary q |
      PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      (WPair.Paired.Counted.referenceOther adversary q).toReal/2^128 := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using WPair.Paired.Counted.hazard_normalized
    (n:=2^128) (q:=q) (by omega) (WPair.Paired.Counted.referenceOther_ne_top adversary q)
    (completed_partial_le_other adversary q hq)

variable {P : Type} [Fintype P] [SampleableType P]
theorem completed_partial_bound (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,WPair.Paired.NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128)+BPair.pairTerm q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans ((probEvent_or_le _ _ _).trans (add_le_add
    (completed_near_bound S hproducer hadmissible hmono hcovered rate hrate adversary q hq)
    (completed_pair_bound adversary q hq)))
  intro z hz h
  exact h.1.elim (fun hn=>Or.inl ⟨hn,h.2⟩) (fun hp=>Or.inr ⟨hp,h.2⟩)
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def Nonstructural (s : RefSample) : Prop := EncodingMatch s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem cleanWin_le_union_cases_of_split (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (hsplit : ∀ z, z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
    Pr[fun s=>combinedEvent.holds s.answers s.trace | PairedReference.referenceExperiment adversary q] +
    Pr[fun z=>FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] := by
  rw [←PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  have hs : Pr[fun z=>QueryRecorded.CleanWin q z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun z=>
      (QueryRecorded.CleanWin q z.1 ∧ CaseABEv combinedEvent adversary z) ∨
      FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
      PartialForestNoOverflow adversary q z ∨
      IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 ∨
      (QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z) |
        PairedSeccLaw.completedExperiment adversary q hq] := by
    apply Ref.pmf_probEvent_mono
    intro z hz hclean
    rcases Classical.em (WPair.Paired.NoOverflow adversary z) with hno | hno
    · rcases hsplit z hz hclean with hab | hf
      · exact Or.inl ⟨hclean,hab⟩
      · rcases completed_forest_cases adversary q hq z hz hclean hf with hfull | hnear | hpair | hinc
        · exact Or.inr (Or.inl hfull)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hnear,hno⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr hpair,hno⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hinc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hclean,hno⟩)))
  refine hs.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add (caseABEv_le_reference combinedEvent adversary q hq) (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _)))
    _ = _ := by ac_rfl
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem queryRatio_lt_one (q : Nat) (hq : q<2^128) : (q:ENNReal)/2^128<1 := by
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)),one_mul]
  exact_mod_cast hq

theorem denominator_ne_zero (q : Nat) (hq : q<2^128) : 1-(q:ENNReal)/2^128≠0 :=
  ne_of_gt (tsub_pos_iff_lt.mpr (queryRatio_lt_one q hq))

theorem prefixCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) :
    prefixCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold prefixCoeff
  finiteness

theorem encodingCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) :
    encodingCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold encodingCoeff
  finiteness

theorem errCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) :
    errCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold errCoeff twoEdgeRate
  finiteness

theorem denominator_toReal (q : Nat) (hq : q<2^128) :
    (1-(q:ENNReal)/2^128).toReal=1-(q:ℝ)/2^128 := by
  rw [ENNReal.toReal_sub_of_le (le_of_lt (queryRatio_lt_one q hq)) (by simp)]
  simp

theorem prefixCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1) :
    (prefixCoeff q w v).toReal=canonicalPrefix ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  have hvw : v.toReal=1-w.toReal := by
    have h:=congrArg ENNReal.toReal hwv
    rw [ENNReal.toReal_add hw hv] at h
    simp only [ENNReal.toReal_one] at h
    linarith
  unfold prefixCoeff canonicalPrefix
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,denominator_toReal q hq,hvw]
  ring

theorem encodingCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) :
    (encodingCoeff q w v).toReal=canonicalEncoding ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  unfold encodingCoeff canonicalEncoding
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,denominator_toReal q hq]
  ring

theorem errCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1) :
    (errCoeff q w v).toReal=canonicalError ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  have hvw : v.toReal=1-w.toReal := by
    have h:=congrArg ENNReal.toReal hwv
    rw [ENNReal.toReal_add hw hv] at h
    simp only [ENNReal.toReal_one] at h
    linarith
  unfold errCoeff twoEdgeRate canonicalError
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one,denominator_toReal q hq,hvw]
  ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceExperiment

theorem query_card_lt_one (q : Nat) (hq : q<2^128) : (Fintype.card Digest:ℝ)⁻¹*q<1 := by
  have hcard : (Fintype.card Digest:ℝ)=2^128 := by rw [Fintype.card_bitVec];norm_num
  rw [hcard]
  have hq' : (q:ℝ)<2^128 := by exact_mod_cast hq
  rw [mul_comm,←div_eq_mul_inv]
  exact (div_lt_one (by positivity)).2 hq'

theorem kconst_le (q : Nat) : (ClaudeWCT.Arith.SideChannel.kconst q:ℝ)≤5*(q:ℝ)^2 := by
  unfold ClaudeWCT.Arith.SideChannel.kconst
  push_cast
  nlinarith [sq_nonneg (q:ℝ)]

theorem errConst_nonneg (q : Nat) (hq : q<2^128) : 0≤Core.errConst q := by
  have hd : 0<1-(Fintype.card Digest:ℝ)⁻¹*q := sub_pos.mpr (query_card_lt_one q hq)
  unfold Core.errConst
  positivity

/-- With the one-sided side-channel constant (`kconst q = q²`, r3-lean-seedfam) the seed error is `2·54 = 108`
instead of `540` (`10·54`): the per-test charge `C` enters as `2 C y³ / (1 - y)`. -/
theorem kconst_le_sq (q : Nat) : (ClaudeWCT.Arith.SideChannel.kconst q:ℝ)≤(q:ℝ)^2 := by
  unfold ClaudeWCT.Arith.SideChannel.kconst
  push_cast
  nlinarith [sq_nonneg (q:ℝ)]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceExperiment

noncomputable def prefixMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  ∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)
noncomputable def encodingMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  ∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open PairedReference.Classes
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def prefixMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount
noncomputable def encodingMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q encodingCount
noncomputable def otherMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q PairedReference.otherCount
noncomputable def digestMass (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) : ENNReal :=
  PairedSeccLaw.expectedCharge adversary q hq PairedReference.Classes.digestClass

theorem masses_finite (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    prefixMass adversary q≠⊤ ∧ encodingMass adversary q≠⊤ ∧ otherMass adversary q≠⊤ ∧
      digestMass adversary q hq≠⊤ := by
  have hf := ne_top_of_le_ne_top (ENNReal.natCast_ne_top q) (PairedReference.Classes.reference_class_budget adversary q hq)
  change prefixMass adversary q+encodingMass adversary q+otherMass adversary q+digestMass adversary q hq≠⊤ at hf
  rcases ENNReal.add_ne_top.mp hf with ⟨hpeo,hm⟩
  rcases ENNReal.add_ne_top.mp hpeo with ⟨hpe,ho⟩
  exact ⟨(ENNReal.add_ne_top.mp hpe).1,(ENNReal.add_ne_top.mp hpe).2,ho,hm⟩

theorem masses_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    (prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
      (otherMass adversary q).toReal/2^128+(digestMass adversary q hq).toReal/2^128≤(q:ℝ)/2^128 := by
  have hf:=masses_finite adversary q hq
  have h:=ENNReal.toReal_mono (ENNReal.natCast_ne_top q) (PairedReference.Classes.reference_class_budget adversary q hq)
  change (prefixMass adversary q+encodingMass adversary q+otherMass adversary q+digestMass adversary q hq).toReal≤(q:ENNReal).toReal at h
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hf.1,hf.2.1⟩,hf.2.2.1⟩) hf.2.2.2,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hf.1,hf.2.1⟩) hf.2.2.1,ENNReal.toReal_add hf.1 hf.2.1,ENNReal.toReal_natCast] at h
  simpa only [add_div] using div_le_div_of_nonneg_right h (show (0:ℝ)≤2^128 by positivity)

theorem full_probability_real (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤)
    (hmin:1/1024≤theta) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate) :
    (Pr[fun z=>FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
        theta.toReal*((digestMass adversary q hq).toReal/2^128)+(q:ℝ)/2^128*rate.toReal := by
  have h := completed_flexible_full_bound (theta-1/1024) rate adversary q hq hrate
  rw [tsub_add_cancel_of_le hmin] at h
  have hcls : (fun (_ : PairedOuter.PaddedGame.TraceResult × SigGolfCandidate.T3.Correctness.Answers) =>
      CreationGame.publicClass CaseC.IsDigestInput)=PairedReference.Classes.digestClass := by
    funext z input
    apply propext
    rcases input with (coin | x) | priv
    · exact ⟨fun h => h.elim, fun ⟨_,_,_,h⟩ => by cases h⟩
    · constructor
      · rintro ⟨rho,m,ctr,rfl⟩;exact ⟨rho,m,ctr,rfl⟩
      · rintro ⟨rho,m,ctr,h⟩;cases h;exact ⟨rho,m,ctr,rfl⟩
    · exact ⟨fun h => h.elim, fun ⟨_,_,_,h⟩ => by cases h⟩
  rw [hcls] at h
  change _≤theta/2^128*digestMass adversary q hq+(q:ENNReal)*rate/2^128 at h
  have hm: digestMass adversary q hq≠⊤ := (masses_finite adversary q hq).2.2.2
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast] at hreal
  convert hreal using 1 <;> ring

theorem partial_probability_real (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      ((378+1/1024)/(2*(1-(q:ℝ)/2^128))+1/(2*(1-(q:ℝ)/2^128)^2))*((q:ℝ)/2^128)^2 := by
  have hqN : q<2^128 := by omega
  have hN : (0:ℝ)<2^128 := by positivity
  have hqr : (q:ℝ)<2^128 := by exact_mod_cast hqN
  have hd : 0<(2:ℝ)^128-q := sub_pos.mpr hqr
  have hsub : ((2^128-q:Nat):ℝ)=(2:ℝ)^128-q := by rw [Nat.cast_sub (by omega),Nat.cast_pow,Nat.cast_ofNat]
  have hsub0 : ((2^128-q:Nat):ENNReal)≠0 := by exact_mod_cast (by omega : 2^128-q≠0)
  have hchoose : (q.choose 2:ℝ)≤(q:ℝ)^2/2 := by
    have hc : q.choose 2*2≤q*q := by
      rw [Nat.choose_two_right]
      exact (Nat.div_mul_le_self _ 2).trans (Nat.mul_le_mul_left q (Nat.sub_le q 1))
    have hc' : (q.choose 2:ℝ)*2≤(q:ℝ)*q := by exact_mod_cast hc
    nlinarith
  have hprod : ((q*(q-1):Nat):ℝ)≤(q:ℝ)^2 := by
    have hp : q*(q-1)≤q*q := Nat.mul_le_mul_left q (Nat.sub_le q 1)
    simpa only [pow_two] using (show ((q*(q-1):Nat):ℝ)≤(q:ℝ)*q by exact_mod_cast hp)
  have hr := ENNReal.toReal_mono (by unfold BPair.pairTerm;finiteness) h
  simp (disch:=finiteness) only [BPair.pairTerm,ENNReal.toReal_add,ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,ENNReal.toReal_one] at hr
  rw [hsub] at hr
  refine hr.trans ?_
  calc
    _ ≤ ((2:ℝ)^128-q)⁻¹*(q:ℝ)^2*(378+1/1024)/(2*2^128)+
      ((q:ℝ)^2/2)*(((2:ℝ)^128-q)⁻¹)^2 := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hd.le)) (by norm_num)
      · exact mul_le_mul_of_nonneg_right hchoose (sq_nonneg _)
    _ = _ := by
      have hdy : 1-(q:ℝ)/2^128≠0 := ne_of_gt (sub_pos.mpr ((div_lt_one hN).2 hqr))
      field_simp [ne_of_gt hd,hdy]
      <;> ring

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_probability_real_of (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:1/1024≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139)
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+(710/1000)*((q:ℝ)/2^128)^2+1/2^136 := by
  have hf := full_probability_real theta rate htheta hratefin hmin adversary q hq hrate
  have hinc := ENNReal.toReal_mono (by finiteness) hincomplete
  have hov := ENNReal.toReal_mono (by finiteness) hoverflow
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hinc hov
  have hevent {α:Type} (law:PMF α) (P:α→Prop) : Pr[P|law]≠⊤ := ne_top_of_le_ne_top (by simp) probEvent_le_one
  have h:=ENNReal.toReal_mono (by exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩)
    (cleanWin_le_union_cases_of_split adversary q hq hsplit)
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (hevent _ _) (hevent _ _)] at h
  have habs : (1:ℝ)/2^139+1/2^138+1/2^137≤1/2^136 := by norm_num
  nlinarith

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_outer_ennreal (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128)) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hevent : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]≠⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,Nat.cast_pow,Nat.cast_ofNat]
  convert h using 1 <;> norm_num <;> ring

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem checker_active_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))
    (k : Fin 9) (t : Fin 6) (p : Fin 4) (hp : p.val = 4-WCT9.wordDigit (forestRank output k.val) t) :
    (.inl (.inr (Extract.Paired.honestInput answers (.wctChain (WCT9.digestIndex output) k.val
      (rawChildFromOutput output k).val t.val p.val))) : Spec.Domain) ∈
      queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  have h := checker_slot_queries answers pk log forgery message w output hw hd hcheck ho k t p hp
  rw [WPair.Paired.honestProbe_slot] at h
  exact h
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem ftsHitIn_false (A : Answers) (K : LargeResidual.Coord → Prop) (qs : List Spec.Domain)
    (h : Extract.Paired.FtsHitIn A qs) (hclear : AllClear A K qs) : False := by
  obtain ⟨p,x,hfts,hb,hq,hh,hs⟩ := h
  -- #866: `SameHeader` is `length ∧ hdrKey`; `posOf_sameHeader` is its paired `posOf_key_eq`.
  have hp : Extract.posOf x = some p := Extract.Paired.posOf_sameHeader A p hb.legacy x hs
  apply paired_hit_false A K qs p x hq hp hb _ hh hclear
  cases p with
  | chain | leaf | node | forest => exact hfts.elim
  | wctChain | wctLeaf | wctNode => exact hb.legacy

theorem checker_bankFresh (A : Answers) (published : SigGolfCandidate.T3.Cache) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (hgen : evalWithAnswerFn A keygen = (pk,published))
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn A (PairedOuter.FullGame.authenticatedSign published entry.1))
    (hcheck : evalWithAnswerFn A (Final.Paired.checkForgeryP pk log forgery) = true)
    (hcomplete : ∀ m, ∃ sig, evalWithAnswerFn A (SigGolfCandidate.Research.SharedForest.signPayload published m) = some sig)
    (hsource : ∀ L, WotsExtract.SourceLeaf7 L →
      Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L ≠ none)
    (hclear : AllClear A (LargeResidual.Paired.Known (Disclosed A published))
      (queried A (Final.Paired.checkForgeryP pk log forgery))) :
    BankFresh A published log (queried A (Final.Paired.checkForgeryP pk log forgery)) := by
  have hpk : pk = Extract.honestRoot A 0 0 := by
    have h := Extract.keygen_pk A
    change (evalWithAnswerFn A keygen).1 = Extract.honestRoot A 0 0 at h
    rw [hgen] at h
    exact h
  have hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop A) := by
    have h := (Correctness.keygen_correct A).2.1
    rw [hgen] at h
    exact h
  rcases CanonicalExtract.checkForgery_canonical_or_collision A published hcache pk hpk log hlog forgery hcheck
    with hprim | hhit | ⟨m,w,N,hw,hdc,hd,hdq,hgate,hrank,hgood,hopen,hfresh⟩
  · exact (wotsPrimitive_false A published _ hsource hprim hclear).elim
  · exact (ftsHitIn_false A _ _ hhit hclear).elim
  refine ⟨m,wrho w,wdc w,N,?_,hdq,?_,?_,?_⟩
  · exact hd
  · change ClaudeWCT.Bank.Paired.admissible N = true
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨hgate,?_⟩
    simpa only [ranksAccepted,List.all_eq_true,List.mem_finRange,forall_true_left,decide_eq_true_eq] using hrank
  · intro k t s hs
    exact Wots.PairedSmallT.checker_active_queries A pk log forgery m w N hw hd hcheck hopen k t s hs
  · exact WPair.Paired.fresh_digest_not_signer_eval A published log hlog m (wrho w) (wdc w) hcomplete hfresh
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cert_of_clean (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z)
    (hcomp : SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2)
    (hcontext : ContextGood z.2) : CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 := by
  apply cert_of_clean_of_checker adversary q hq z hz hwin hno
  intro published pk log forgery hgen hlog hcheck hclear
  apply checker_bankFresh z.2 published pk log forgery hgen hlog hcheck _ _ hclear
  · intro message
    obtain ⟨sig,hsig⟩ := hcomp message
    rw [hgen] at hsig
    refine ⟨sig,?_⟩
    unfold SigGolfCandidate.Research.SharedForest.sign at hsig
    rw [evalWithAnswerFn_bind] at hsig
    split_ifs at hsig with hm
    · simp only [evalWithAnswerFn_pure,reduceCtorEq] at hsig
    · exact hsig
  · exact Wots.CanonicalRef.referenceSearch_complete z.2 hcontext
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_noOvR_failure (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137 := by
  simpa only [one_div] using! FtsOverflow.Paired.cleanWin_logOverflow_le adversary q hq

theorem clean_le_contact_cert (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z=>CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
      1/(2:ENNReal)^139+1/(2:ENNReal)^138+1/(2:ENNReal)^137 := by
  rw [←PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  have hs : Pr[fun z=>QueryRecorded.CleanWin q z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun z=> ContactNO adversary q z ∨
        (CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) ∨
        ¬ContextGood z.2 ∨ ¬SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2 ∨
        (QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) |
        PairedSeccLaw.completedExperiment adversary q hq] := by
    apply Wots.Ref.pmf_probEvent_mono
    intro z hz hclean
    by_cases hno : NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2
    swap
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hclean,hno⟩)))
    by_cases hcontext : ContextGood z.2
    swap
    · exact Or.inr (Or.inr (Or.inl hcontext))
    by_cases hcomp : SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2
    swap
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcomp)))
    by_cases hcontact : Contact adversary q z
    · exact Or.inl ⟨hcontact,hno⟩
    · exact Or.inr (Or.inl ⟨cert_of_clean adversary q hq z hz hclean hcontact hcomp hcontext,hno⟩)
  refine hs.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _)))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl
      (add_le_add (Wots.PairedSearchTable.completed_context_failure adversary q hq)
        (add_le_add (Wots.PairedSearchTable.completed_signer_failure adversary q hq)
          (clean_noOvR_failure adversary q hq))))
    _ = _ := by ac_rfl
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem large_clean_closing (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : (3:ℝ)/2500≤(q:ℝ)/2^128)
    (hclean : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      ENNReal.ofReal (2*((q:ℝ)/2^128)-((q:ℝ)/2^128)^2)+
      (q:ENNReal)*ENNReal.ofReal ((993/1000)*((q:ℝ)/2^128))/2^128+
      ((2 ^ 142 : ENNReal)⁻¹+(2 ^ 142 : ENNReal)⁻¹)+
      1/(2:ENNReal)^139+1/(2:ENNReal)^138+1/(2:ENNReal)^137) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply Wots.PairedSmallT.clean_outer_ennreal adversary q hq
  let y : ℝ := (q:ℝ)/2^128
  have hy : 0≤y := by dsimp [y];positivity
  have hhalf : y≤1/2 := by
    have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
    dsimp [y]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^128)).2
    calc
      (q:ℝ) ≤ 2^127 := hqr
      _ = (1/2:ℝ)*2^128 := by norm_num
  have hpoly : 0≤2*y-y^2 := by nlinarith
  have hrate : 0≤(993/1000:ℝ)*y := mul_nonneg (by norm_num) hy
  have hr := ENNReal.toReal_mono (by finiteness) hclean
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,ENNReal.toReal_one,ENNReal.toReal_inv] at hr
  -- top-nonce layer (r3-lean-nonsec): the large route carries 2·Pr[CapFail] ≤ 2·(2^142)⁻¹
  change _ ≤ ENNReal.toReal (ENNReal.ofReal (2*y-y^2))+
    (q:ℝ)*ENNReal.toReal (ENNReal.ofReal ((993/1000)*y))/2^128+(((2:ℝ)^142)⁻¹+((2:ℝ)^142)⁻¹)+
    1/2^139+1/2^138+1/2^137 at hr
  rw [ENNReal.toReal_ofReal hpoly,ENNReal.toReal_ofReal hrate] at hr
  have hmul : (q:ℝ)*((993/1000)*y)/2^128=y*((993/1000)*y) := by dsimp [y];ring
  rw [hmul] at hr
  have hc := ContinuousPricing.large_closing_real_cap777 y ((993/1000)*y) hlow le_rfl
  have he : ((2:ℝ)^142)⁻¹+((2:ℝ)^142)⁻¹+1/2^139+1/2^138+1/2^137≤1/2^131 := by norm_num
  have hp1 : 0≤y*((1:ℝ)/2^25) := mul_nonneg hy (by positivity)
  have hp2 : 0≤y*((1:ℝ)/2^50) := mul_nonneg hy (by positivity)
  change _+ (y/2^18+1/2^700+1/2^152+y/2^128)≤2*y
  linarith

end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem large_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : (3:ℝ)/2500≤(q:ℝ)/2^128) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hhalf : (q:ℝ)/2^128≤1/2 := by
    have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^128)).2
    calc
      (q:ℝ) ≤ 2^127 := hqr
      _ = (1/2:ℝ)*2^128 := by norm_num
  have hexc := ClaudeWCT.Bank.Paired.excess_large_certified ((q:ℝ)/2^128) hlow hhalf
  have hexc' : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-ENNReal.ofReal (Flexible.budgetRate q-1/1024))≤
      ENNReal.ofReal ((993/1000)*((q:ℝ)/2^128)) := by
    simpa only [Flexible.budgetRate,mul_div_assoc] using hexc
  apply large_clean_closing adversary q hq hlow
  exact (clean_le_contact_cert adversary q hq).trans
    (add_le_add (add_le_add (add_le_add
      (contact_cert_bound_of_excess adversary q hq _ hexc') le_rfl) le_rfl) le_rfl)
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Secc.Paired
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_FinalG ====
section

/-! # The live small route parametrized by the seed-error bound (r3-lean-seedfam, family closing for `g ≤ 7`)

`SeedErrorBound`: on the small window `y = q/2^128 ≤ 3/2500`, `errTot ≤ (733/1000) y²`. It holds for every per-test
chain charge `C ≤ 305` once `errTot ≤ 2 C y³ / (1 - y)` (the one-sided side-channel constant, `kconst q = q²`):
`seedErrorBound_of_charge`. Today's leaf families (`C = 54`, `errTot_toReal_sharp`) satisfy it
(`seedErrorBound_current`); `g = 7` lower families (`C = 43·7 = 301`) need `errTot ≤ 602 y³/(1-y)` from the family
restart. Copies of the Paired small-route chain (`…G`) use the weighted error `799/1000` (`grouped_weighted_error`)
and the middle closing `grouped_middle_closing` (`767/1000 + 799/1000`); the large route is unchanged.
`t3_securityP_of_seedError` : `SeedErrorBound → SecurityP`, and `t3_securityP_kappa2` instantiates it today.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open ENNReal SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
/-- The seed-error hypothesis of the small route. -/
def SeedErrorBound : Prop :=
  ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 → (q : ℝ) / 2 ^ 128 ≤ 3 / 2500 →
    (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2

/-- Any per-test chain charge `C ≤ 305` with `errTot ≤ 2 C y³/(1-y)` gives the seed-error bound. -/
theorem seedErrorBound_of_charge (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 305)
    (h : ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 →
      (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤
        2 * C * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128)) : SeedErrorBound :=
  fun adversary q hq hy => (h adversary q hq).trans (grouped_seed_error C _ hC0 hC (by positivity) hy)

/-- `g = 7`: the family restart must deliver `errTot ≤ 602 y³/(1-y)`. -/
theorem seedErrorBound_g7
    (h : ∀ (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat), q < 2 ^ 128 →
      (CanonicalRef.Normalized.Contacts.errTot adversary q).toReal ≤
        602 * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128)) : SeedErrorBound :=
  seedErrorBound_of_charge 301 (by norm_num) (by norm_num) fun adversary q hq =>
    (h adversary q hq).trans (le_of_eq (by ring))
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_probability_real_ofG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:1/1024≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142))
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+(778/1000)*((q:ℝ)/2^128)^2+1/2^136 := by
  have hf := full_probability_real theta rate htheta hratefin hmin adversary q hq hrate
  have hinc := ENNReal.toReal_mono (by finiteness) hincomplete
  have hov := ENNReal.toReal_mono (by finiteness) hoverflow
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hinc hov
  have hevent {α:Type} (law:PMF α) (P:α→Prop) : Pr[P|law]≠⊤ := ne_top_of_le_ne_top (by simp) probEvent_le_one
  have h:=ENNReal.toReal_mono (by exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩)
    (cleanWin_le_union_cases_of_split adversary q hq hsplit)
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (hevent _ _) (hevent _ _)] at h
  -- top-nonce layer (r3-lean-nonsec): the primitive constant carries Pr[CapFail] ≤ 1/2^142
  have habs : (1:ℝ)/2^139+1/2^142+1/2^138+1/2^137≤1/2^136 := by norm_num
  nlinarith


end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem middle_clean_closingG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : 1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh : (q:ℝ)/2^128≤3/2500)
    (rate : ℝ) (hrate : rate≤1153/1000000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (99847/50000)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(778/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hquad := paired_partial_denominatorRC _ _ hhigh (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := grouped_middle_closingRC ((q:ℝ)/2^128) rate hlow hhigh hrate
  linarith

theorem tiny_clean_closingG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive : 1≤q) (hhigh : (q:ℝ)/2^128≤1/2^28)
    (rate : ℝ) (hrate : rate≤18/5000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (249/125)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(778/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hsmall : (q:ℝ)/2^128≤3/2500 := hhigh.trans (by norm_num)
  have hlow : 1/(2:ℝ)^128≤(q:ℝ)/2^128 := div_le_div_of_nonneg_right (by exact_mod_cast hpositive) (by positivity)
  have hquad := paired_partial_denominatorRC _ _ hsmall (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := tiny_class_budgetRC _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := tiny_closing_rows18 ((q:ℝ)/2^128) rate hlow hhigh hrate
  nlinarith [sq_nonneg ((q:ℝ)/2^128)]

theorem clean_outer_ennrealG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128)) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hevent : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]≠⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,Nat.cast_pow,Nat.cast_ofNat]
  convert h using 1 <;> norm_num <;> ring




end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_partial_certifiedG (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(378+1/1024)/(2*2^128)+BPair.pairTerm q := by
  apply completed_partial_bound ClaudeWCT.Bank.Paired.nearLawSpec
    ClaudeWCT.Bank.Paired.nearLawSpec_producer rfl ClaudeWCT.Bank.Paired.nearCovered_mono
    (fun X N h => by
      obtain ⟨k,t,h⟩:=h
      exact WPair.Paired.nearCovered_bank X N k t h)
    378 ClaudeWCT.Bank.Paired.nearLawSpec_mean adversary q hq

theorem excess_middle_actualG :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((99847:ENNReal)/50000-1/1024))≤1153/1000000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_middle_certified
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

theorem excess_tiny_actualG :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((249:ENNReal)/125-1/1024))≤18/5000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_tiny_certified
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

end ClaudeWCT.W9.T3.Secc.Paired
end
-- ==== merged from ClaudeWCT_WCT9_SeedFamG ====
section

/-!
# `g`-leaf lower seed families (opus-crumbs retune; g = 4..7 under study, 16 in the original plan), scheme side, additive

Every group of `g` consecutive leaves of a lower tree shares one GF(2^128) polynomial family of
`lowerFamCoefCount g = 5g + 3` coefficients. Coefficient `j` of family `f` has ordinal `(5g+3)·f + j` and is read with
the existing carry packing `packedSecret (lowerSeedPair lay tree)` (ordinal `k` is half `k % 2` of private pair
`k / 2`; the carry is threaded across families, so a family with an odd first ordinal starts with the high half left by
the previous one). The seed of chain `i` of leaf `L` is the family of `L / g` evaluated at
`groupedPoint g L i = (L % g)·43 + i + 1` (points `1 ..= 43 g`, `< 1024` for `g ≤ 23`, distinct within a family).

These definitions sit alongside `lowerCoefs` / `buildLeafPF` / `buildTreeP` (Core.lean); nothing existing is changed.
Installing them is the one-line switch `buildTreeP ↦ buildTreePG` in `signLayersBC` (see the porter notes).
-/

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness

/-- Point stride per leaf of a family (the lower chain count). -/
def lowerFamStride : Nat := 43
/-- Coefficients per lower family of `g` leaves: 5 revealed seeds per leaf, plus 3. -/
def lowerFamCoefCount (g : Nat) : Nat := 5 * g + 3
/-- The family of a lower leaf. -/
def lowerFamOf (g leaf : Nat) : Nat := leaf / g
/-- Ordinal of coefficient `j` of family `fam` (the packed-half index in `lowerSeedPair lay tree`). -/
def lowerFamCoefOrdinal (g fam j : Nat) : Nat := lowerFamCoefCount g * fam + j
/-- Evaluation point of chain `chain` of leaf `leaf` in its family. -/
def groupedPoint (g leaf chain : Nat) : Nat := leaf % g * lowerFamStride + chain + 1

/-- The `5g + 3` coefficients of family `fam` (carry threaded through `packedSecret`). -/
def lowerCoefsG (g : Nat) (lay : Layer) (tree fam : Nat) (carry : Digest) : M (List Digest × Digest) :=
  (List.range (lowerFamCoefCount g)).foldlM (fun (state : List Digest × Digest) j => do
    let (coef, carry) ← packedSecret (lowerSeedPair lay tree) (lowerFamCoefOrdinal g fam j) state.2
    pure (state.1 ++ [coef], carry)) ([], carry)

/-- The seed of chain `chain` of leaf `leaf` from its family's coefficients. -/
def lowerFamilySeedG (g : Nat) (coefs : List Digest) (leaf chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval coefs (groupedPoint g leaf chain)

/-- A lower leaf from its family's coefficients (no private query: the family is built once per `g` leaves). -/
def buildLeafPG (g : Nat) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest) :
    M (Digest × List Digest) := do
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let value ← chainW lay tree leaf i 0 digit (lowerFamilySeedG g coefs leaf i)
      let last ← chainW lay tree leaf i digit (maxDigit lay i - digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  let root ← lowerLeafHash lay tree leaf state.1
  pure (root, state.2)

/-- Lower tree of layer `lay ≥ 1` with `g`-leaf families: the family is (re)built at every leaf `≡ 0 (mod g)`, the
coefficients are kept for the next `g - 1` leaves, and the packing carry is threaded across families. -/
def buildTreePG (g : Nat) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × List Digest × Digest) leaf => do
      let (coefs, carry) ← if leaf % g = 0 then
          lowerCoefsG g lay tree (lowerFamOf g leaf) state.2.2.2
        else pure (state.2.2.1, state.2.2.2)
      let (root, values) ← buildLeafPG g lay tree leaf (if leaf = selected then digits else []) coefs
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), coefs, carry)) ([], [], [], 0)
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure (levels, state.2.1)

/-- `signLayersBC` with `g`-leaf lower families (the only change: `buildTreePG g`). -/
def signLayersBCG (g : Nat) (cache : Cache) (index : Nat) : Nat → LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreePG g lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := topPair lay levels
        let some previous ← signLayersBCG g cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))

/-! ### Security-facing view (answers-level), alongside `famCoefN` / `wotsSeed` (Correctness.lean). -/

/-- Coefficient `j` of lower family `fam`: the packed half `(5g+3)·fam + j` of `lowerSeedPair lay tree`. -/
def lowerFamCoefNG (g : Nat) (answers : Answers) (lay : Layer) (tree fam j : Nat) : Digest :=
  seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree (lowerFamCoefOrdinal g fam j / 2)))
    (lowerFamCoefOrdinal g fam j)
/-- The lower WOTS seed of chain `i` of leaf `leaf` under `g`-leaf families. -/
def lowerSeedG (g : Nat) (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval
    (List.ofFn fun j : Fin (lowerFamCoefCount g) => lowerFamCoefNG g answers lay tree (lowerFamOf g leaf) j.val)
    (groupedPoint g leaf i)

/-! ### Arithmetic facts -/

theorem groupedPoint_pos (g leaf chain : Nat) : 1 ≤ groupedPoint g leaf chain := by
  unfold groupedPoint; omega

/-- Points stay at most `43 g`. -/
theorem groupedPoint_le {g : Nat} (hg : 0 < g) (leaf chain : Nat) (hc : chain < lowerFamStride) :
    groupedPoint g leaf chain ≤ 43 * g := by
  have hm := Nat.mod_lt leaf hg
  unfold groupedPoint lowerFamStride at *
  have : leaf % g * 43 ≤ (g - 1) * 43 := Nat.mul_le_mul_right _ (by omega)
  have : (g - 1) * 43 + 43 = 43 * g := by
    rcases g with _ | g
    · omega
    · simp only [Nat.add_sub_cancel]; ring
  omega

/-- Points are below `1024` (the `gfMulPt` / `HornRun` domain `< 2^10`) for `g ≤ 23`. -/
theorem groupedPoint_lt_1024 {g : Nat} (hg : 0 < g) (hg23 : g ≤ 23) (leaf chain : Nat) (hc : chain < lowerFamStride) :
    groupedPoint g leaf chain < 1024 :=
  lt_of_le_of_lt (groupedPoint_le hg leaf chain hc) (by omega)

/-- Points are distinct within a family: equal family and equal point give equal leaf and chain. -/
theorem groupedPoint_inj {g leaf leaf' chain chain' : Nat} (hg : 0 < g) (hc : chain < lowerFamStride)
    (hc' : chain' < lowerFamStride) (hf : lowerFamOf g leaf = lowerFamOf g leaf')
    (hp : groupedPoint g leaf chain = groupedPoint g leaf' chain') : leaf = leaf' ∧ chain = chain' := by
  unfold groupedPoint lowerFamOf lowerFamStride at *
  have h1 := Nat.div_add_mod leaf g
  have h2 := Nat.div_add_mod leaf' g
  have hm := Nat.mod_lt leaf hg
  have hm' := Nat.mod_lt leaf' hg
  have hmod : leaf % g = leaf' % g := by omega
  refine ⟨?_, by omega⟩
  rw [← h1, ← h2, hf, hmod]

/-- Coefficient ordinals are distinct across families. -/
theorem lowerFamCoefOrdinal_inj {g f f' j j' : Nat} (hj : j < lowerFamCoefCount g) (hj' : j' < lowerFamCoefCount g)
    (h : lowerFamCoefOrdinal g f j = lowerFamCoefOrdinal g f' j') : f = f' ∧ j = j' := by
  unfold lowerFamCoefOrdinal at h
  rcases Nat.lt_or_ge f f' with hlt | hge
  · exfalso
    have : lowerFamCoefCount g * f + lowerFamCoefCount g ≤ lowerFamCoefCount g * f' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rcases Nat.lt_or_ge f' f with hlt' | hge'
    · exfalso
      have : lowerFamCoefCount g * f' + lowerFamCoefCount g ≤ lowerFamCoefCount g * f := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt'
      omega
    · have hff : f = f' := by omega
      subst hff
      exact ⟨rfl, by omega⟩

/-- A family's chain slots `(leaf in family, chain)` revealing at most 5 per leaf reveal at most `5g`, so `|S| + 3`
fits the `5g + 3` coefficients. -/
theorem lowerFam_revealed_card_le {g : Nat} (S : Finset (Fin g × Fin 43))
    (h : ∀ l : Fin g, (S.filter fun p => p.1 = l).card ≤ 5) : S.card + 3 ≤ lowerFamCoefCount g := by
  have hs : S.card = ∑ l : Fin g, (S.filter fun p => p.1 = l).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.1)
  have hle : ∑ l : Fin g, (S.filter fun p => p.1 = l).card ≤ ∑ _l : Fin g, 5 := Finset.sum_le_sum fun l _ => h l
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  unfold lowerFamCoefCount
  omega

/-- Private-pair queries of one lower tree with `g · nf` leaves: the even ordinals below `(5g+3)·nf`, i.e.
`⌈(5g+3)·nf / 2⌉`. For `g = 4`: L1 (32 families) 368 (was 512), L2/L3 (16) 184 (was 256). -/
theorem lowerFam_pairs_g4 : (23 * 32 + 1) / 2 = 368 ∧ (23 * 16 + 1) / 2 = 184 := by decide

end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamProg ====
section

/-! # Family decomposition of the rest tables, any layer and group size (r3-lean-seedfam, port step R1)

The family analogue of the leaf decomposition (`Normalized.RawLeaf.ovL` / `rdL` / `restLaw_resampleL`). A family of
shape `(g, w, n)` — `g` leaves of `w` chains, `n` coefficients — at `F = (lay, tree, fam)` covers the leaves `g·fam + l`
(`l < g`); its data are the `n` coefficient halves (ordinals `n·fam + j` of `lowerSeedPair lay tree`) and the used halves
of the step-0 rows of its `g w` chains (`GChainW g w = Fin g × Fin w`). `ovF F R (K, f)` overrides them, `rdF` reads
them back, and the rest-table law is invariant under resampling them (`restLaw_resampleF`).
Instances: lower 7-leaf families `(7, 43, 38)` (`5·7 + 3`), top 4-leaf families `(4, 54, 4 r + 3)` (`r` reveals per top
leaf); `(1, 43, 8)` and `(1, 54, 24)` are today's leaf families.

Hypothesis `FamOk g w b n F`: `0 < g`, `w < 2^24`, the leaves of `F` below `2^24`, its tree below `2^40`, its ordinals' pair
indices below `2^32` (header injectivity).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype

/-- A lower seed family: layer, tree and family index (`leaf / g`). -/
structure FamAddr where
  lay : Layer
  tree : Nat
  fam : Nat
  deriving DecidableEq

/-- Leaf `l` of family `F`. -/
def famLeaf (g : Nat) (F : FamAddr) (l : Fin g) : LeafAddr := ⟨F.lay, F.tree, g * F.fam + l.val⟩
/-- Chain `c = (l, i)` of family `F`. -/
def chainOfF (g w : Nat) (F : FamAddr) (c : GChainW g w) : ChainAddr := ⟨famLeaf g F c.1, c.2.val⟩

/-- Admissible family: `n ≤ b` coefficients at ordinals `b·fam + j`. -/
structure FamOk (g w b n : Nat) (F : FamAddr) : Prop where
  pos : 0 < g
  width : w < 2 ^ 24
  leaf : g * F.fam + g ≤ 2 ^ 24
  tree : F.tree < 2 ^ 40
  pair : b * F.fam + b ≤ 2 ^ 33
  size : n ≤ b

/-- Ordinal of coefficient `j` of family `F` (ordinal base `b` per family). -/
def ordF (b : Nat) {n : Nat} (F : FamAddr) (j : Fin n) : Nat := b * F.fam + j
/-- Tweak of the cell holding coefficient `j` of `F`. -/
def cellHdrF (b : Nat) {n : Nat} (F : FamAddr) (j : Fin n) : BitVec 128 :=
  WCT9.lowerSeedHeader F.lay F.tree (ordF b F j / 2)

/-- Lower `g`-leaf families use the scheme's ordinals `WCT9.lowerFamCoefOrdinal`. -/
theorem ordF_lower (g : Nat) (F : FamAddr) (j : Fin (WCT9.lowerFamCoefCount g)) :
    ordF (WCT9.lowerFamCoefCount g) F j = WCT9.lowerFamCoefOrdinal g F.fam j := rfl

variable {g w b n : Nat} {F : FamAddr}

theorem ordF_pair_lt (hF : FamOk g w b n F) (j : Fin n) : ordF b F j / 2 < 2 ^ 32 := by
  have h1 := j.isLt
  have h2 := hF.pair
  have h3 := hF.size
  unfold ordF
  omega

theorem cellHdrF_inj (hF : FamOk g w b n F) {j j' : Fin n} (h : cellHdrF b F j = cellHdrF b F j') :
    ordF b F j / 2 = ordF b F j' / 2 := by
  unfold cellHdrF WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordF_pair_lt hF j), Nat.mod_eq_of_lt (ordF_pair_lt hF j')] at this

theorem ordF_inj {j j' : Fin n} (h1 : ordF b F j / 2 = ordF b F j' / 2)
    (h2 : ordF b F j % 2 = ordF b F j' % 2) : j = j' := by
  apply Fin.ext; unfold ordF at h1 h2; omega

/-- The coefficient of `F` stored in half `bit` of the cell with tweak `tw`, if any. -/
noncomputable def slotAtF (b n : Nat) (F : FamAddr) (tw : BitVec 128) (bit : Nat) : Option (Fin n) :=
  if h : ∃ j : Fin n, cellHdrF b F j = tw ∧ ordF b F j % 2 = bit then some (Classical.choose h)
  else none

theorem slotAtF_some {tw : BitVec 128} {bit : Nat} {j : Fin n} (h : slotAtF b n F tw bit = some j) :
    cellHdrF b F j = tw ∧ ordF b F j % 2 = bit := by
  unfold slotAtF at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem slotAtF_self (hF : FamOk g w b n F) (j : Fin n) :
    slotAtF b n F (cellHdrF b F j) (ordF b F j % 2) = some j := by
  have hex : ∃ j' : Fin n, cellHdrF b F j' = cellHdrF b F j ∧ ordF b F j' % 2 = ordF b F j % 2 :=
    ⟨j, rfl, rfl⟩
  unfold slotAtF
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [ordF_inj (cellHdrF_inj hF h1) h2]

/-- `priv` with `F`'s coefficient halves replaced by `K`. -/
noncomputable def ovPrivF (b n : Nat) (F : FamAddr) (priv : FullGame.FullTable) (K : Fin n → Digest) :
    FullGame.FullTable
  | .inl tw => ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw))))
  | .inr x => priv (.inr x)

theorem ovPrivF_inl (priv : FullGame.FullTable) (K : Fin n → Digest) (tw : BitVec 128) :
    ovPrivF b n F priv K (.inl tw) = ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))) := rfl

theorem ovPrivF_cell (hF : FamOk g w b n F) (priv : FullGame.FullTable) (K : Fin n → Digest)
    (j : Fin n) : halfOf (ordF b F j % 2) (ovPrivF b n F priv K (.inl (cellHdrF b F j))) = K j := by
  rw [ovPrivF_inl]
  unfold halfOf
  by_cases h0 : ordF b F j % 2 = 0
  · rw [if_pos h0]
    have hs := slotAtF_self hF j
    rw [h0] at hs
    rw [hs, low, ChainGraph.joinOutput_low]
    rfl
  · rw [if_neg h0]
    have hs := slotAtF_self hF j
    rw [show ordF b F j % 2 = 1 by omega] at hs
    rw [hs, high, ChainGraph.joinOutput_high]
    rfl

/-! ### Step-0 rows of the family's chains -/

theorem famLeaf_lt (hF : FamOk g w b n F) (l : Fin g) : (famLeaf g F l).leaf < 2 ^ 24 := by
  have := l.isLt; have := hF.leaf
  unfold famLeaf; simp only; omega

/-- Step-0 rows of distinct family chains are distinct. -/
theorem chainRowF_zero_inj (hF : FamOk g w b n F) {c c' : GChainW g w} {v v' : Digest}
    (h : chainRowW (chainOfF g w F c) 0 v = chainRowW (chainOfF g w F c') 0 v') : c = c' ∧ v = v' := by
  have hc := c.2.isLt; have hc' := c'.2.isLt
  have hw := hF.width
  obtain ⟨hal, hcc, -, hv⟩ := chainInputW_eq_chainRowW (a := chainOfF g w F c')
    (by unfold chainOfF; simp only; omega) (by unfold chainOfF; simp only; omega) (by omega) (by omega) h
  have hL := hal.eq_of_lt hF.tree (lt_trans (famLeaf_lt hF c.1) (by norm_num)) hF.tree
    (lt_trans (famLeaf_lt hF c'.1) (by norm_num))
  have hleaf := congrArg LeafAddr.leaf hL
  unfold chainOfF famLeaf at hleaf hcc
  simp only at hleaf hcc
  have e1 : c.1 = c'.1 := Fin.ext (by omega)
  exact ⟨Prod.ext e1 (Fin.ext hcc), hv⟩

/-- If `input` is the step-0 row of a chain of `F` at `v`, that `(c, v)`. -/
noncomputable def zeroOfF (g w : Nat) (F : FamAddr) (input : HashInput) : Option (GChainW g w × Digest) :=
  if h : ∃ p : GChainW g w × Digest, input = chainRowW (chainOfF g w F p.1) 0 p.2 then some (Classical.choose h) else none

theorem zeroOfF_some {input : HashInput} {p : GChainW g w × Digest} (h : zeroOfF g w F input = some p) :
    input = chainRowW (chainOfF g w F p.1) 0 p.2 := by
  unfold zeroOfF at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem zeroOfF_chainRow (hF : FamOk g w b n F) (c : GChainW g w) (v : Digest) :
    zeroOfF g w F (chainRowW (chainOfF g w F c) 0 v) = some (c, v) := by
  cases h : zeroOfF g w F (chainRowW (chainOfF g w F c) 0 v) with
  | none =>
      unfold zeroOfF at h
      rw [dif_pos ⟨(c, v), rfl⟩] at h
      cases h
  | some p =>
      have he := zeroOfF_some h
      obtain ⟨h1, h2⟩ := chainRowF_zero_inj hF he
      rw [show p = (c, v) from Prod.ext h1.symm h2.symm]

/-- The used half of family chain `c`'s step-0 row. -/
def zhF (g w : Nat) (F : FamAddr) (c : GChainW g w) : Bool := zh (famLeaf g F c.1) c.2.val

/-! ### Override and readback in the normalized tables -/

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

/-- Family data: the `5g + 3` coefficients and the step-0 row functions of the `43 g` chains. -/
abbrev FamData (g w n : Nat) := (Fin n → Digest) × (GChainW g w → Digest → Digest)

/-- `pub` with the used halves of `F`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubF (g w : Nat) (F : FamAddr) (pub : U → HashOutput) (f : GChainW g w → Digest → Digest) :
    U → HashOutput := fun x =>
  match zeroOfF g w F x.val with
  | some p => joinHalf (zhF g w F p.1) (f p.1 p.2) (WCT9.halfOf (!zhF g w F p.1) (pub x))
  | none => pub x

noncomputable def ovF (g w b n : Nat) (F : FamAddr) (R : Tables U) (y : FamData g w n) : Tables U :=
  (ovPrivF b n F R.1 y.1, ovPubF g w F R.2 y.2)

noncomputable def rdF (g w b n : Nat) (F : FamAddr) (R : Tables U) : FamData g w n :=
  (fun j => halfOf (ordF b F j % 2) (R.1 (.inl (cellHdrF b F j))),
    fun c v => WCT9.halfOf (zhF g w F c) (R.2 ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩))

include hU in
theorem ovPubF_zero (hF : FamOk g w b n F) (pub : U → HashOutput) (f : GChainW g w → Digest → Digest) (c : GChainW g w)
    (v : Digest) :
    ovPubF g w F pub f ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩ =
      joinHalf (zhF g w F c) (f c v)
        (WCT9.halfOf (!zhF g w F c) (pub ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩)) := by
  unfold ovPubF
  simp only [zeroOfF_chainRow hF]

include hU in
theorem rdF_ovF (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) : rdF hU g w b n F (ovF g w b n F R y) = y := by
  obtain ⟨K, f⟩ := y
  unfold rdF ovF
  refine Prod.ext ?_ ?_
  · funext j
    exact ovPrivF_cell hF R.1 K j
  · funext c v
    simp only
    rw [ovPubF_zero hU hF, halfOf_joinHalf]

include hU in
theorem ovF_ovF_rdF (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) :
    ovF g w b n F (ovF g w b n F R y) (rdF hU g w b n F R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨K, f⟩ := y
  unfold ovF rdF
  simp only
  refine Prod.ext ?_ ?_
  · funext coord
    rcases coord with tw | x
    · show ovPrivF b n F (ovPrivF b n F priv K) _ (.inl tw) = priv (.inl tw)
      rw [ovPrivF_inl, ovPrivF_inl]
      have e0 : ((slotAtF b n F tw 0).map (fun j => halfOf (ordF b F j % 2) (priv (.inl (cellHdrF b F j))))).getD
          (low (ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))))) = low (priv (.inl tw)) := by
        cases h : slotAtF b n F tw 0 with
        | none => simp only [Option.map_none, Option.getD_none, h, low, ChainGraph.joinOutput_low]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAtF_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1, if_true]
      have e1 : ((slotAtF b n F tw 1).map (fun j => halfOf (ordF b F j % 2) (priv (.inl (cellHdrF b F j))))).getD
          (high (ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))))) = high (priv (.inl tw)) := by
        cases h : slotAtF b n F tw 1 with
        | none => simp only [Option.map_none, Option.getD_none, h, high, ChainGraph.joinOutput_high]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAtF_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1]
            rfl
      rw [e0, e1]
      exact ChainGraph.joinOutput_parts _
    · rfl
  · funext x
    dsimp only
    unfold ovPubF
    cases hp : zeroOfF g w F x.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hx : x = ⟨chainRowW (chainOfF g w F p.1) 0 p.2, RawPrefix.chainRowW_mem hU _ _ _⟩ :=
          Subtype.ext (zeroOfF_some hp)
        subst hx
        simp only [halfOf_not_joinHalf, joinHalf_halfOf]

include hU in
/-- **Resampling a family's coefficients and step-0 rows preserves the rest-table law.** -/
theorem restLaw_resampleF (hF : FamOk g w b n F) {β : Type} (Φ : Tables U → PMF β) :
    (PMF.uniformOfFintype (Tables U)).bind Φ =
      (PMF.uniformOfFintype (Tables U)).bind
        (fun R => (PMF.uniformOfFintype (FamData g w n)).bind (fun y => Φ (ovF g w b n F R y))) := by
  have : Nonempty (FamData g w n) := ⟨(fun _ => 0, fun _ _ => 0)⟩
  have h := uniform_resample (Ω := Tables U) (X := fun _ => FamData g w n) (fun _ => 0)
    (fun _ R y => ovF g w b n F R y) (fun _ R => rdF hU g w b n F R) (fun R y => rdF_ovF hU hF R y)
    (fun R y => ovF_ovF_rdF hU hF R y) (fun _ _ => rfl)
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (Tables U)).bind
  funext R
  rw [PMF.bind_map]
  rfl

/-- After the override the coefficient cell half of `j` reads `K j`. -/
theorem raw_ovF_cell (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) (j : Fin n) :
    halfOf (ordF b F j % 2) ((ovF g w b n F R y).1 (.inl (cellHdrF b F j))) = y.1 j :=
  ovPrivF_cell hF R.1 y.1 j

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamCongr ====
section

/-! # Family restart, step P1/P3a: the abstract family scheme and family agreement (r3-lean-seedfam)

`FamScheme`: the scheme-side interface of the family restart. Per layer, `grp lay` consecutive leaves share one family
of `cnt lay` coefficients; coefficient `j` of family `f` is the packed half `cnt·f + j` of `lowerSeedPair lay tree`, and
the WOTS seed of chain `i` of leaf `leaf` is the family of `leaf / grp` evaluated at `(leaf % grp)·chainCount + i + 1`.
Today's scheme is the instance `leafScheme` (`grp = 1`, `cnt = famCount`); the switched scheme will be lower
`grp = 7, cnt = 38` and top `grp = 4, cnt = 4 r + 3`.

`FamOut S F`: queries outside family `F`'s chain rows (all `grp` leaves, steps `< 7`) and coefficient cells;
`FamAgree S F T T'`: agreement there and on the other halves of `F`'s cells; `wotsSeed_outF`: seeds of leaves outside
`F` are unchanged under `FamAgree`. (Family analogues of `Leaf.LeafOut` / `LeafAgree` / `wotsSeed_out`.)
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The scheme-side interface of the family restart. Per layer: `grp` leaves per family, ordinal base `cnt` (family `f`
owns ordinals `cnt·f + j`, `j < size lay f ≤ cnt`; the last family of a tree may be shorter), point stride `stride`
(`≥ chainCount`; lower 43, top 64). -/
structure FamScheme where
  grp : Layer → Nat
  cnt : Layer → Nat
  size : Layer → Nat → Nat
  stride : Layer → Nat
  /-- Evaluation point of chain `i` of leaf `leaf` (chains `≥ chainCount` may use a separate junk region). -/
  point : Layer → Nat → Nat → Nat
  grp_pos : ∀ lay, 0 < grp lay
  cnt_le : ∀ lay, cnt lay ≤ 512
  size_le : ∀ lay f, size lay f ≤ cnt lay
  point_eq : ∀ lay leaf i, i < chainCount lay → point lay leaf i = (leaf % grp lay) * stride lay + i + 1
  seed : ∀ (T : Answers) (lay : Layer) (tree leaf i : Nat), WCT9.wotsSeed T lay tree leaf i =
    ClaudeWCT.Arith.familyEval (List.ofFn fun j : Fin (size lay (leaf / grp lay)) =>
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair lay tree ((cnt lay * (leaf / grp lay) + j) / 2)))
        (cnt lay * (leaf / grp lay) + j)) (point lay leaf i)

/-- The scheme of the `Correctness` layout (`famGrp`, `famBase`, `famSize`, `famStride`, `famPoint`); valid for any
layout, so after the v6 flip it is the v6 scheme. -/
def layoutScheme : FamScheme where
  grp := WCT9.famGrp
  cnt := WCT9.famBase
  size := WCT9.famSize
  stride := WCT9.famStride
  point := WCT9.famPoint
  grp_pos := WCT9.famGrp_pos
  cnt_le lay := (WCT9.famBase_le lay).trans (by norm_num)
  size_le := WCT9.famSize_le_base
  point_eq lay leaf i hi := by unfold WCT9.famPoint; rw [if_pos (Or.inr hi)]
  seed T lay tree leaf i := by
    rw [WCT9.wotsSeed_fam]
    rfl

variable (S : FamScheme)

/-- Ordinal of coefficient `j` of family `F`. -/
def ordS (F : FamAddr) (j : Nat) : Nat := S.cnt F.lay * F.fam + j

/-- Queries outside family `F`: its chain rows (every leaf of the family, steps `< 7`) and its coefficient cells. -/
def FamOut (F : FamAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ l : Fin (S.grp F.lay), ∀ c step value, c < chainCount F.lay → step < 7 →
      input ≠ chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ step value
  | .inr (.inl tweak) => ∀ j, j < S.cnt F.lay → tweak ≠ WCT9.lowerSeedHeader F.lay F.tree (ordS S F j / 2)
  | _ => True

/-- Chain addresses whose `Untouched` classes cover `FamOut F`. -/
def coverAddrsF (F : FamAddr) : List ChainAddr :=
  (List.finRange (S.grp F.lay)).flatMap (fun l =>
      (List.range (chainCount F.lay)).map (fun c => (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr))) ++
    (List.range (S.cnt F.lay)).map (fun j => (⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩ : ChainAddr))

theorem famOut_of_cover {F : FamAddr} {q : Spec.Domain} (h : ∀ c ∈ coverAddrsF S F, Untouched c q) :
    FamOut S F q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro l c step value hc hs heq
    have hmem : (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr) ∈ coverAddrsF S F :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_finRange l,
        List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩⟩)
    have hu := h _ hmem step value (by omega)
    unfold chainRowW WCT9.chainInputW at heq
    split at heq
    · exact hu.2 heq
    · exact hu.1 heq
  · intro j hj heq
    apply h ⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    show tweak = seedTweak _
    rw [heq]
    unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (ordS S F j / 2) / 2 = ordS S F j / 2 by omega]
  · trivial

/-- A program respecting every chain's `Untouched` class respects `FamOut F`. -/
theorem respects_famOut {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) (F : FamAddr) :
    Respects (FamOut S F) p :=
  Respects.mono' (Leaf.respects_cover h (coverAddrsF S F)) fun _ hq => famOut_of_cover S hq

/-- `T'` agrees with `T` outside `F` and on the other halves of `F`'s coefficient cells. -/
structure FamAgree (F : FamAddr) (T T' : Answers) : Prop where
  out : ∀ q, FamOut S F q → T' q = T q
  half : ∀ o, (∃ j, j < S.cnt F.lay ∧ o / 2 = ordS S F j / 2) → (∀ j, j < S.cnt F.lay → o ≠ ordS S F j) →
    WCT9.seedHalf (evalWithAnswerFn T' (WCT9.lowerSeedPair F.lay F.tree (o / 2))) o =
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair F.lay F.tree (o / 2))) o

/-- `(lay, tree, leaf)` is a leaf of family `F` up to the header aliasing of the tree index. -/
def FamAlias (F : FamAddr) (lay : Layer) (tree leaf : Nat) : Prop :=
  lay = F.lay ∧ tree % 2 ^ 40 = F.tree % 2 ^ 40 ∧ leaf / S.grp F.lay = F.fam

/-- Ordinal pair indices stay below `2^32` for leaves below `2^24` (`cnt ≤ 512`). -/
theorem ord_pair_lt (S : FamScheme) (lay : Layer) {leaf j : Nat} (hleaf : leaf < 2 ^ 24) (hj : j < S.cnt lay) :
    (S.cnt lay * (leaf / S.grp lay) + j) / 2 < 2 ^ 32 := by
  have h1 := S.cnt_le lay
  have h2 : leaf / S.grp lay ≤ leaf := Nat.div_le_self _ _
  have h3 : S.cnt lay * (leaf / S.grp lay) ≤ 512 * leaf :=
    (Nat.mul_le_mul_right _ h1).trans (Nat.mul_le_mul_left _ h2)
  omega

section Agree
variable {S} {F : FamAddr} {T T' : Answers} (hC : FamAgree S F T T')
include hC

theorem eval_outF {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    evalWithAnswerFn T' p = evalWithAnswerFn T p :=
  h.eval_eq hC.out

/-- **Seeds of leaves outside `F` are unchanged** (they read other cells, or the other halves of `F`'s cells). -/
theorem wotsSeed_outF (hF : F.fam * S.grp F.lay < 2 ^ 24) {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24)
    (hna : ¬FamAlias S F lay tree leaf) (i : Nat) :
    WCT9.wotsSeed T' lay tree leaf i = WCT9.wotsSeed T lay tree leaf i := by
  rw [S.seed, S.seed]
  congr 2
  funext j
  set o := S.cnt lay * (leaf / S.grp lay) + j.val with ho
  have hj : j.val < S.cnt lay := lt_of_lt_of_le j.isLt (S.size_le _ _)
  have ho2 : o / 2 < 2 ^ 32 := ord_pair_lt S lay hleaf hj
  by_cases hcell : ∃ j', j' < S.cnt F.lay ∧ WCT9.lowerSeedHeader lay tree (o / 2) =
      WCT9.lowerSeedHeader F.lay F.tree (ordS S F j' / 2)
  · obtain ⟨j', hj', he⟩ := hcell
    unfold WCT9.lowerSeedHeader at he
    obtain ⟨-, hl, ht, hp, -⟩ := header_fields he
    have hlay : lay = F.lay := Fin.ext (by
      rwa [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
        Nat.mod_eq_of_lt (lt_trans F.lay.isLt (by decide))] at hl)
    have hFl : F.fam < 2 ^ 24 := by
      have := S.grp_pos F.lay
      have : F.fam ≤ F.fam * S.grp F.lay := Nat.le_mul_of_pos_right _ this
      omega
    have hoF : ordS S F j' / 2 < 2 ^ 32 := by
      have h1 := S.cnt_le F.lay
      have : S.cnt F.lay * F.fam ≤ 512 * F.fam := Nat.mul_le_mul_right _ h1
      unfold ordS; omega
    rw [Nat.mod_eq_of_lt ho2, Nat.mod_eq_of_lt hoF] at hp
    have hpair : WCT9.lowerSeedPair lay tree (o / 2) = WCT9.lowerSeedPair F.lay F.tree (o / 2) := by
      unfold WCT9.lowerSeedPair privatePair
      rw [header_congr (by rw [hlay]) ht rfl]
    rw [hpair]
    subst hlay
    apply hC.half o ⟨j', hj', hp⟩
    intro j'' hj'' hoe
    apply hna
    refine ⟨rfl, ht, ?_⟩
    -- equal ordinals: same family
    unfold ordS at hoe
    rw [ho] at hoe
    rcases Nat.lt_trichotomy (leaf / S.grp F.lay) F.fam with hlt | heq | hgt
    · exfalso
      have : S.cnt F.lay * (leaf / S.grp F.lay) + S.cnt F.lay ≤ S.cnt F.lay * F.fam := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · exact heq
    · exfalso
      have : S.cnt F.lay * F.fam + S.cnt F.lay ≤ S.cnt F.lay * (leaf / S.grp F.lay) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hgt
      omega
  · have hq : T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) =
        T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) :=
      hC.out _ (fun j' hj' he => hcell ⟨j', hj', he⟩)
    unfold WCT9.lowerSeedPair privatePair privateHash
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change WCT9.seedHalf ((T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
        (T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o =
      WCT9.seedHalf ((T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
        (T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o
    rw [hq]
end Agree

end ClaudeWCT.W9.T3.Security.Wots.FamRestart
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamProg2 ====
section

/-! # Family restart, step P2b: the family override against a `FamScheme` (r3-lean-seedfam)

Family analogues of `Normalized.RawLeaf.{raw_ovL_zero, raw_ovL_pub, raw_ovL_tweak, famCoef_ovL, wotsSeed_ovL,
leafAgree_ovL, search_ovL, referenceSearch_ovL, depth_ovL, restDepth_ovL}`: for a family `F` of a scheme `S`
(`g = S.grp F.lay` leaves of `chainCount F.lay` chains, `n = S.cnt F.lay` coefficients), the override
`ovF g w b n F R (K, f)` makes the family read `K` (seeds `familyEval K` at `l·w + c + 1`), agrees with `R` outside the
family (`famAgree_ovF`), and leaves every reference depth unchanged.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable {g w b n : Nat} {F : FamAddr}

include hU in
theorem raw_ovF_zero (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) (c : GChainW g w) (v : Digest) :
    raw (ovF g w b n F R y) (.inl (.inr (chainRowW (chainOfF g w F c) 0 v))) =
      joinHalf (zhF g w F c) (y.2 c v) (WCT9.halfOf (!zhF g w F c) (raw R (.inl (.inr (chainRowW (chainOfF g w F c) 0 v))))) := by
  rw [RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _),
    RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _)]
  exact ovPubF_zero hU hF R.2 y.2 c v

theorem raw_ovF_pub (R : Tables U) (y : FamData g w n) (input : HashInput) (h : zeroOfF g w F input = none) :
    raw (ovF g w b n F R y) (.inl (.inr input)) = raw R (.inl (.inr input)) := by
  by_cases hm : input ∈ U
  · rw [RawPrefix.raw_mem _ _ hm, RawPrefix.raw_mem _ _ hm]
    show ovPubF g w F R.2 y.2 ⟨input, hm⟩ = R.2 ⟨input, hm⟩
    unfold ovPubF
    simp only [h]
  · rw [RawPrefix.raw_nonmem _ _ hm, RawPrefix.raw_nonmem _ _ hm]

theorem slotAtF_none {tw : BitVec 128} {bit : Nat} (h : ∀ j : Fin n, cellHdrF b F j = tw → ordF b F j % 2 ≠ bit) :
    slotAtF b n F tw bit = none := by
  unfold slotAtF
  rw [dif_neg]
  rintro ⟨j, h1, h2⟩
  exact h j h1 h2

theorem raw_ovF_tweak (R : Tables U) (y : FamData g w n) (tw : BitVec 128) (h : ∀ j : Fin n, cellHdrF b F j ≠ tw) :
    raw (ovF g w b n F R y) (.inr (.inl tw)) = raw R (.inr (.inl tw)) := by
  rw [RawPrefix.raw_private, RawPrefix.raw_private]
  show ovPrivF b n F R.1 y.1 (.inl tw) = R.1 (.inl tw)
  rw [ovPrivF_inl, slotAtF_none (fun j hj => absurd hj (h j)), slotAtF_none (fun j hj => absurd hj (h j))]
  exact ChainGraph.joinOutput_parts _

/-- The family coefficient `j` read through the scheme's packed half after the override is `K j`. -/
theorem famCoef_ovF (hF : FamOk g w b n F) (R : Tables U) (K : Fin n → Digest) (f : GChainW g w → Digest → Digest)
    (j : Fin n) :
    WCT9.seedHalf (evalWithAnswerFn (raw (ovF g w b n F R (K, f))) (WCT9.lowerSeedPair F.lay F.tree (ordF b F j / 2)))
      (ordF b F j) = K j := by
  rw [eval_lowerSeedPair]
  have hc := ovPrivF_cell hF R.1 K j
  rw [show ovPrivF b n F R.1 K (.inl (cellHdrF b F j)) = raw (ovF g w b n F R (K, f)) (.inr (.inl (cellHdrF b F j))) from rfl]
    at hc
  unfold halfOf at hc
  unfold WCT9.seedHalf
  unfold cellHdrF at hc
  split_ifs with h1 h2 h2
  · rw [if_pos h1] at hc; exact hc
  · rw [if_neg h1] at hc; exact hc

/-- A family cell with the header of pair index `o / 2` has ordinal pair `o / 2`. -/
theorem cellHdrF_eq_hdr (hF : FamOk g w b n F) (j' : Fin n) {o : Nat} (ho : o / 2 < 2 ^ 32)
    (h : cellHdrF b F j' = WCT9.lowerSeedHeader F.lay F.tree (o / 2)) : ordF b F j' / 2 = o / 2 := by
  unfold cellHdrF WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordF_pair_lt hF j'), Nat.mod_eq_of_lt ho] at this

variable (S : FamScheme)

/-- Admissible family of a scheme. -/
abbrev FamOkS (F : FamAddr) : Prop := FamOk (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F

/-- **Seed readout after the override**: leaf `l` of `F`, chain `c`, reads `familyEval K` at `l·w + c + 1`. -/
theorem wotsSeed_ovF (hF : FamOkS S F) (R : Tables U) (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f))) F.lay F.tree
        (S.grp F.lay * F.fam + l) c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (l.val * S.stride F.lay + c + 1) := by
  rw [S.seed]
  have hg := S.grp_pos F.lay
  have hdiv : (S.grp F.lay * F.fam + l) / S.grp F.lay = F.fam := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt l.isLt, Nat.zero_add]
  have hmod : (S.grp F.lay * F.fam + l) % S.grp F.lay = l := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l.isLt]
  rw [S.point_eq _ _ _ hc, hdiv, hmod]
  congr 2
  funext j
  exact famCoef_ovF hF R K f j

/-- The family override changes nothing outside `F`'s own halves and step-0 rows. -/
theorem famAgree_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) :
    FamAgree S F (raw R) (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) := by
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (k | input) | (tw | x)
    · rfl
    · apply raw_ovF_pub
      cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
      | none => rfl
      | some p => exact absurd (zeroOfF_some hz) (hq p.1.1 p.1.2 0 p.2 p.1.2.isLt (by omega))
    · exact raw_ovF_tweak R y tw (fun j he => hq j (lt_of_lt_of_le j.isLt (S.size_le _ _)) he.symm)
    · rfl
  · obtain ⟨j, hj, hoj⟩ := ho
    rw [eval_lowerSeedPair, eval_lowerSeedPair]
    have ho2 : o / 2 < 2 ^ 32 := by
      rw [hoj]; have := hF.pair; unfold ordS; omega
    have hnone : slotAtF (S.cnt F.lay) (S.size F.lay F.fam) F (WCT9.lowerSeedHeader F.lay F.tree (o / 2)) (o % 2) = none := by
      apply slotAtF_none
      intro j' h1 h2
      have e1 := cellHdrF_eq_hdr hF j' ho2 h1
      apply hno j' (lt_of_lt_of_le j'.isLt (S.size_le _ _))
      unfold ordF at e1 h2
      unfold ordS at hoj ⊢
      omega
    rw [RawPrefix.raw_private, RawPrefix.raw_private]
    show WCT9.seedHalf ((ovPrivF (S.cnt F.lay) (S.size F.lay F.fam) F R.1 y.1 (.inl (WCT9.lowerSeedHeader F.lay F.tree (o / 2)))).extractLsb' 0 128,
      (ovPrivF (S.cnt F.lay) (S.size F.lay F.fam) F R.1 y.1 (.inl (WCT9.lowerSeedHeader F.lay F.tree (o / 2)))).extractLsb' 128 128) o = _
    rw [ovPrivF_inl]
    unfold WCT9.seedHalf
    split_ifs with h0
    · rw [h0] at hnone
      rw [hnone, ChainGraph.joinOutput_low]
      rfl
    · rw [show o % 2 = 1 by omega] at hnone
      rw [hnone, ChainGraph.joinOutput_high]
      rfl

theorem search_ovF (hF : FamOkS S F) (R : Tables U) (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))
    (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages K remaining =
      CanonicalRef.searchOf (raw R) zeroMessages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_outF (famAgree_ovF S hF R y)
    (respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F)

theorem referenceSearch_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (K : LeafAddr) :
    CanonicalRef.referenceSearch (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages K =
      CanonicalRef.referenceSearch (raw R) zeroMessages K :=
  CanonicalRef.referenceSearch_congr (fun K remaining _ => search_ovF S hF R y K remaining) K

theorem depth_ovF (hF : FamOkS S F) (R : Tables U) (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))
    (a : ChainAddr) :
    CanonicalRef.depth (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages a =
      CanonicalRef.depth (raw R) zeroMessages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_ovF S hF]

theorem restDepth_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (a : ChainAddr) :
    RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) = RawPrefix.restDepth a R := by
  rw [RawPrefix.restDepth_eq, RawPrefix.restDepth_eq, depth_ovF S hF]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamFill ====
section

/-! # Family restart, step P2c: the prefix-game fill with a family overridden (r3-lean-seedfam)

Family analogues of the `Fill` section of `Normalized.RawLeaf` (WotsLeafProg): the chain `a = chainOfF F ca` of
family `F` is filled (`fillTable a (ovF … X) e`); the other step-0 rows of the family read `X.2`, private cells read the
override, every reference depth is unchanged, and the family seeds read `familyEval X.1`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf (fillTable raw_ov_const)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable

/-- Seeds depend on the answers only through the private cells of their layer and tree (any `FamScheme`). -/
theorem wotsSeed_congr_cellsS (S : FamScheme) {T T' : Answers} {lay : Layer} (tree leaf i : Nat)
    (h : ∀ p, T (.inr (.inl (WCT9.lowerSeedHeader lay tree p))) = T' (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i := by
  rw [S.seed, S.seed]
  congr 2
  funext j
  rw [eval_lowerSeedPair, eval_lowerSeedPair, h]

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable (S : FamScheme) {F : FamAddr}

section Fill
variable (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hU hF haF hd1

theorem fill_pubF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (input : HashInput)
    (h : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), c ≠ ca → ∀ v,
      input ≠ chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inl (.inr input)) =
      match PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
      | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) e
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (raw R (.inl (.inr input))))
      | none => raw R (.inl (.inr input)) := by
  have hdX := restDepth_ovF S hF R X a
  unfold fillTable RawPrefix.fill
  rw [raw_ov_const hU a (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega), hdX]
  cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
  | some p =>
    simp only
    have hin := PrefixGame.rowOf_some hp
    obtain ⟨⟨step, hs⟩, v⟩ := p
    simp only at hin ⊢
    subst hin
    congr 1
    by_cases hz : step = 0
    · subst hz
      have hrow : chainRowW a 0 v = chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F ca) 0 v := by rw [haF]
      have h0 : WCT9.chainHigh a.key.lay a.chain 0 = zhF (S.grp F.lay) (chainCount F.lay) F ca := by subst haF; rfl
      rw [h0, hrow, raw_ovF_zero hU hF]
      exact halfOf_not_joinHalf _ _ _
    · congr 1
      rw [raw_ovF_pub]
      cases hzo : zeroOfF (S.grp F.lay) (chainCount F.lay) F (chainRowW a step v) with
      | none => rfl
      | some q =>
          have he := zeroOfF_some hzo
          have hw := hF.width
          have hc1 := q.1.2.isLt
          obtain ⟨-, -, hs', -⟩ := chainInputW_eq_chainRowW (a := chainOfF (S.grp F.lay) (chainCount F.lay) F q.1)
            (by subst haF; unfold chainOfF; simp only; have := ca.2.isLt; omega)
            (by unfold chainOfF; simp only; omega)
            (by have := RawPrefix.restDepth_le a R; omega) (by omega) he
          exact absurd hs' hz
  | none =>
    simp only
    have hc := (PrefixGame.rowOf_none_iff a input).mp hp
    apply raw_ovF_pub
    cases hzo : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
    | none => rfl
    | some q =>
        have he := zeroOfF_some hzo
        by_cases hqa : q.1 = ca
        · exfalso
          apply hc
          refine ⟨0, q.2, hd1, ?_⟩
          rw [he, hqa, haF]
        · exact absurd he (h q.1 hqa q.2)

theorem fill_privF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (coord : Coordinate) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inr coord) =
      raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) (.inr coord) := by
  unfold fillTable RawPrefix.fill
  exact RawPrefix.raw_ov_private a _ _ _

theorem fill_zeroF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest)
    (c : GChainW (S.grp F.lay) (chainCount F.lay)) (hca : c ≠ ca) (v : Digest) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e
        (.inl (.inr (chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v))) =
      joinHalf (zhF (S.grp F.lay) (chainCount F.lay) F c) (X.2 c v)
        (WCT9.halfOf (!zhF (S.grp F.lay) (chainCount F.lay) F c)
          (raw R (.inl (.inr (chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v))))) := by
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.raw_ov_nonprefix, raw_ovF_zero hU hF]
  rw [PrefixGame.rowOf_none_iff]
  rintro ⟨step, value, hs, he⟩
  have hw := hF.width
  have hc1 := c.2.isLt
  obtain ⟨hal, hc, -, -⟩ := chainInputW_eq_chainRowW (a := a)
    (by unfold chainOfF; simp only; omega) (by subst haF; unfold chainOfF; simp only; have := ca.2.isLt; omega)
    (by omega) (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega) he
  apply hca
  subst haF
  have hL := hal.eq_of_lt hF.tree (lt_trans (famLeaf_lt hF c.1) (by norm_num)) hF.tree
    (lt_trans (famLeaf_lt hF ca.1) (by norm_num))
  have hleaf := congrArg LeafAddr.leaf hL
  unfold chainOfF famLeaf at hleaf hc
  simp only at hleaf hc
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext hc)

theorem famAgree_fill (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) :
    FamAgree S F (raw R) (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e) := by
  have hA := famAgree_ovF S hF R X
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (k | input) | coord
    · rfl
    · rw [fill_pubF hU S hF ca haF R hd1 X e input (fun c _ v he => hq c.1 c.2 0 v c.2.isLt (by omega) he)]
      cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
      | none => rfl
      | some p =>
          exfalso
          have hin := PrefixGame.rowOf_some hp
          apply hq ca.1 ca.2 p.1 p.2 ca.2.isLt (by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega)
          rw [hin]; exact congrArg (fun b => chainRowW b p.1.val p.2) haF
    · rw [fill_privF hU S hF ca haF R hd1]
      exact hA.out _ hq
  · rw [eval_lowerSeedPair, eval_lowerSeedPair] at *
    have := hA.half o ho hno
    rw [eval_lowerSeedPair, eval_lowerSeedPair] at this
    rw [fill_privF hU S hF ca haF R hd1]
    exact this

theorem depth_fillF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (b : ChainAddr) :
    CanonicalRef.depth (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e) zeroMessages b =
      CanonicalRef.depth (raw R) zeroMessages b := by
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.depth_ov _ (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega),
    depth_ovF S hF]

theorem wotsSeed_fillF (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (e : Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) e) F.lay F.tree
        (S.grp F.lay * F.fam + l) c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (l.val * S.stride F.lay + c + 1) := by
  rw [← wotsSeed_ovF S hF R K f l c hc]
  apply wotsSeed_congr_cellsS S
  intro p
  exact fill_privF hU S hF ca haF R hd1 (K, f) e _

theorem fill_frontier_selfF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) :
    CanonicalRef.frontierValue (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e)
      zeroMessages a = e := by
  have hdX := restDepth_ovF S hF R X a
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.frontierValue_ov hU]
  obtain ⟨d', hd'⟩ : ∃ d', RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) = d' + 1 :=
    ⟨RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) - 1, by omega⟩
  generalize RawPrefix.ovSeed a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e = s0
  revert s0
  rw [hd']
  intro s0
  exact PrefixGame.evaluate_const_succ d' e s0
end Fill

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamGame ====
section

/-! # Family restart, step P3b: family congruence leaves the honest reference game unchanged (r3-lean-seedfam)

Port of the leaf route (`WotsLeafCongr` legacy helpers + normalized `CanonicalRef.Leaf.Congr`, and the game part of
`WotsLeafProg`: `referenceGame_leaf`) from one WOTS leaf to a family `F` of `grp` leaves sharing one seed polynomial,
against the abstract `FamScheme` interface.

* `FamRestart`: family `respects` lemmas (`respectsF_*`), `famOut_chainInput`, and the legacy-namespace helpers
  `eval_chain_outF`, `wotsEnd_outF`, `wotsRoot_outF`, `wotsTree_layF`, `honestForest_outF`, `leafMsg_layF`,
  `referenceSearch_layF`, `depth_layF`.
* `CanonicalRef.FamGame`: `FamCongr S messages F T T'` (`FamAgree` plus rows/front of every chain of every leaf of `F`),
  `wotsEnd/Value/Root/Tree_congrF`, `sourceMessages_congrF`, the signer/keygen invariance and
  **`referenceGame_fam`**.

Aliasing split: a leaf either `FamAlias`es `F` — then it is the family member `famLeaf F (leaf % grp)` up to the
`2^40` tree aliasing, and the one-leaf lemmas `Mask.chainW_alias` / `wotsSeed_alias` / `sourceLeaf_alias` apply to that
member — or not, and then `wotsSeed_outF` / `eval_chain_outF` apply.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

variable (S : FamScheme)

/-! ## Family members and aliasing -/

/-- Leaves of an admissible family are below `2^24`. -/
theorem famLeaf_lt {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) (l : Fin (S.grp F.lay)) :
    (famLeaf (S.grp F.lay) F l).leaf < 2 ^ 24 := by
  show S.grp F.lay * F.fam + l.val < 2 ^ 24
  have := l.isLt
  omega

theorem famBound_lt {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    F.fam * S.grp F.lay < 2 ^ 24 := by
  have := S.grp_pos F.lay
  rw [Nat.mul_comm]
  omega

/-- A family-aliasing leaf is (up to tree aliasing) the member `leaf % grp` of the family. -/
theorem famAlias_member {F : FamAddr} {lay : Layer} {tree leaf : Nat} (h : FamAlias S F lay tree leaf) :
    ∃ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) ∧
      (famLeaf (S.grp F.lay) F l).leaf = leaf := by
  have hleq : (famLeaf (S.grp F.lay) F ⟨leaf % S.grp F.lay, Nat.mod_lt _ (S.grp_pos _)⟩).leaf = leaf := by
    show S.grp F.lay * F.fam + leaf % S.grp F.lay = leaf
    rw [← h.2.2, Nat.div_add_mod]
  exact ⟨⟨leaf % S.grp F.lay, Nat.mod_lt _ (S.grp_pos _)⟩, ⟨h.1, h.2.1, by rw [hleq]⟩, hleq⟩

/-- A small leaf aliasing a member of the family family-aliases the family. -/
theorem famAlias_of_leafAlias {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {lay : Layer}
    {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) {l : Fin (S.grp F.lay)}
    (h : LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l)) : FamAlias S F lay tree leaf := by
  refine ⟨h.1, h.2.1, ?_⟩
  have h2 : leaf % 2 ^ 32 = (S.grp F.lay * F.fam + l.val) % 2 ^ 32 := h.2.2
  have hl := famLeaf_lt S hF l
  change S.grp F.lay * F.fam + l.val < 2 ^ 24 at hl
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  rw [h2, Nat.mul_add_div (S.grp_pos _), Nat.div_eq_of_lt l.isLt, Nat.add_zero]

theorem leafAlias_famLay {F : FamAddr} {lay : Layer} {tree leaf : Nat} {l : Fin (S.grp F.lay)}
    (h : LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l)) : lay = F.lay := h.1

/-! ## Programs respecting `FamOut` -/

section Programs
variable (F : FamAddr)
theorem respectsF_signForest (index : Nat) (output : HashOutput) :
    Respects (FamOut S F) (ClaudeWCT.WCT9.signForest index output) :=
  respects_famOut S (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_signForest c index output) F
theorem respectsF_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (FamOut S F) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respects_famOut S (fun c => respects_digest c _ _ _) F) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
theorem respectsF_privateMac (region : Region) : Respects (FamOut S F) (privateMac region) :=
  respects_famOut S (fun c => respects_privateMac c region) F
theorem respectsF_privateNonce (message : Message) : Respects (FamOut S F) (privateNonce message) :=
  respects_famOut S (fun c => respects_privateNonce c message) F
theorem respectsF_mask (level index : Nat) : Respects (FamOut S F) (mask level index) :=
  respects_famOut S (fun c => respects_mask c level index) F
theorem respectsF_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (FamOut S F) (buildLevels tag lay tree h leaves) :=
  respects_famOut S (fun c => respects_buildLevels c tag lay tree h leaves ht) F
theorem respectsF_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (FamOut S F) (leafHash lay tree leaf ends) :=
  respects_famOut S (fun c => respects_leafHash c lay tree leaf ends) F
theorem respectsF_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (fuel counter : Nat) :
    Respects (FamOut S F) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) :=
  respects_famOut S (fun c => respects_layerCounterSearch c lay tree leaf msg fuel counter) F
theorem famOut_ftsQuery {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    FamOut S F q :=
  famOut_of_cover S fun c _ => ClaudeWCT.WCT9.Wots.ftsQuery_untouched c h
/-- Chain rows outside `F` (a leaf not aliasing the family, or a chain index beyond the leaves' chains). -/
theorem famOut_chainInput (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {lay : Layer} {tree leaf i s : Nat}
    (v : Digest) (hleaf : leaf < 2 ^ 24) (hi : i < 2 ^ 24) (hs : s < 256)
    (hna : ¬(FamAlias S F lay tree leaf ∧ i < chainCount F.lay)) :
    FamOut S F (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i s v)))) := by
  intro l c step value hc hstep heq
  rw [pad64_chainInputW] at heq
  have hc' : c < 2 ^ 24 := by have := chainCount_le F.lay; simp only [Nat.reducePow]; omega
  obtain ⟨hal, rfl, -, -⟩ :=
    chainInputW_eq_chainRowW (a := ⟨famLeaf (S.grp F.lay) F l, c⟩) hi hc' hs (by omega) heq
  exact hna ⟨famAlias_of_leafAlias S hF hleaf hal, hc⟩
theorem respectsF_topPath (cache : Cache) (leaf : Nat) : Respects (FamOut S F) (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ => Respects.bind (respectsF_mask S F _ _) fun _ => Respects.pure' _
theorem famOut_of_hdr (input : HashInput) (h : BitVec 128)
    (hblock : SigGolfCandidate.T3M.Extract.hdrBlock input = SphincsSecurity.bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, step < 7 → h ≠ chainHeader l tr leaf i step) :
    FamOut S F (.inl (.inr input)) := by
  intro l c step value _ hs heq
  have hb : SigGolfCandidate.T3M.Extract.hdrBlock (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ step value) =
      SphincsSecurity.bytesLE 16 (chainHeader (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree
        (famLeaf (S.grp F.lay) F l).leaf c step) :=
    WCT9.chainInputW_header _ _ _ _ _ _
  rw [heq, hb] at hblock
  exact htag _ _ _ _ _ hs (SphincsSecurity.bytesLE_injective hblock).symm
theorem famOut_of_length (input : HashInput) (hl : input.length ≠ 64) : FamOut S F (.inl (.inr input)) := by
  intro l c step value _ _ heq
  apply hl
  rw [heq, chainRowW_length]
theorem foldOK_famOut (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) : Mask.FoldOK (FamOut S F) lay tree h := by
  intro level i left right hlev hi
  refine famOut_of_hdr S F _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader ?_ l tr leaf c step hs
  by_cases h0 : lay = 0
  · exact Or.inl h0
  · exact Or.inr (Mask.lowerHeap_lt' hlev (h7 h0) hi)
theorem respectsF_lowerLevels (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (FamOut S F) (WCT9.lowerLevels lay tree h leaves) :=
  Mask.respects_lowerLevels' (foldOK_famOut S F lay tree h h7) leaves hlen
/-! Top-nonce layer (r3-lean-nonsec): the img-v6 top tree leaves the family classes untouched. -/
theorem respectsF_topNodeHashN (heap n : Nat) (left right : Digest) :
    Respects (FamOut S F) (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  apply Respects.projHash
  rw [Mask.pad64_topNodeInput_block4]
  exact famOut_of_hdr S F _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ _ right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs
theorem respectsF_topNonceSearch (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Respects (FamOut S F) (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respectsF_topNodeHashN S F _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respectsF_topNodeHashN S F _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respectsF_topNonceSearch h heap left right fuel (n + 1)
theorem respectsF_buildTopLevels (leaves : List Digest) : Respects (FamOut S F) (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · rw [← WCT9.lowerNodeHash_top]
    exact Mask.respects_lowerNodeHash' _ _ _ _ _ (famOut_of_hdr S F _ _
      (SigGolfCandidate.T3M.Extract.hdrBlock_block4 _ _ 0 _)
      fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs)
  · unfold topNodeAt
    exact Respects.map _ (respectsF_topNonceSearch S F _ _ _ _ _ _)
theorem respectsF_buildLevelsBelowW (tag lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (FamOut S F) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  Mask.respects_buildLevelsBelow' (foldOK_famOut S F lay tree h h7) tag leaves hlen
theorem respectsF_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects (FamOut S F) (WCT9.lowerLeafHash lay tree leaf ends) :=
  Mask.respects_lowerLeafHash' _ _ _ _ (famOut_of_length S F _ (Mask.pad64_long_length
    (SigGolfCandidate.T3.Security.Wots.Enc.leafInput_long lay tree leaf ends hlen)))
end Programs

/-! ## Legacy-namespace helpers under `FamAgree` -/

section Agree
variable {S} {F : FamAddr} {T T' : Answers} (hC : FamAgree S F T T')
  (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC

theorem queried_outF {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    SourceReplay.queried T' p = SourceReplay.queried T p :=
  h.queried_eq hC.out

include hF in
theorem eval_chain_outF {lay : Layer} {tree leaf i : Nat} (hleaf : leaf < 2 ^ 24) (hi : i < 2 ^ 24)
    (hna : ¬(FamAlias S F lay tree leaf ∧ i < chainCount F.lay)) {start count : Nat} (hc : start + count ≤ 256)
    (v : Digest) :
    evalWithAnswerFn T' (WCT9.chainW lay tree leaf i start count v) =
      evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count v) := by
  apply eval_outF hC
  exact Mask.respects_chainW' _ _ _ _ _ _ _ fun step value _ hhi =>
    famOut_chainInput S F hF value hleaf hi (by omega) hna

include hF in
theorem wotsEnd_outF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬FamAlias S F lay tree leaf)
    (i : Nat) (hi : i < chainCount lay) : WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_outF hC (famBound_lt S hF) hleaf hna]
  exact eval_chain_outF hC hF hleaf (by have := chainCount_le lay; simp only [Nat.reducePow]; omega)
    (fun h => hna h.1) (by have := width_le lay i; omega) _

include hF in
theorem wotsRoot_outF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬FamAlias S F lay tree leaf) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_outF hC hF hleaf hna i (List.mem_range.mp hi))]
  exact eval_outF hC (respectsF_lowerLeafHash S F _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))

include hF in
theorem wotsTree_layF {lay : Layer} (hl : lay ≠ F.lay) (tree : Nat) :
    WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_outF hC hF
    (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega) (fun h => hl h.1))]
  split_ifs
  · exact eval_outF hC (respectsF_buildTopLevels S F _)
  · exact eval_outF hC (respectsF_lowerLevels S F _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))

theorem honestForest_outF (index : Nat) : Extract.honestTop T' index = Extract.honestTop T index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hC.out _ (famOut_ftsQuery S F hq))

include hF in
/-- Messages of leaves on `F`'s layer come from the layer above (or the forest), which `F` does not touch. -/
theorem leafMsg_layF {K : LeafAddr} (hK : K.lay = F.lay) : leafMsg T' K = leafMsg T K := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [wotsTree_layF hC hF (fun he => by
      have := congrArg Fin.val he
      rw [← hK] at this
      simp only at this
      omega)]
  · rw [honestForest_outF hC]

include hF in
theorem referenceSearch_layF {K : LeafAddr} (hK : K.lay = F.lay) :
    referenceSearch T' K = referenceSearch T K := by
  unfold referenceSearch
  rw [leafMsg_layF hC hF hK]
  exact eval_outF hC (respectsF_layerCounterSearch S F _ _ _ _ _ _)

include hF in
theorem depth_layF {a : ChainAddr} (ha : a.key.lay = F.lay) : depth T' a = depth T a := by
  unfold depth referenceDigits
  rw [referenceSearch_layF hC hF ha]
end Agree

end ClaudeWCT.W9.T3.Security.Wots.FamRestart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
variable (S : FamScheme)

/-- Family congruence: `FamAgree`, plus agreement on the rows of every chain of every REAL leaf of `F` (index below
`2 ^ height F.lay`; the last family of a tree may have phantom members) from its signed digit on, and on every such
chain's frontier value. -/
structure FamCongr (messages : LeafAddr → WCT9.LayerMsg) (F : FamAddr) (T T' : Answers) : Prop
    extends FamAgree S F T T' where
  rows : ∀ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay → ∀ c, c < chainCount F.lay → ∀ s v,
    CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ s v))) =
      T (.inl (.inr (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ s v)))
  front : ∀ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay → ∀ c, c < chainCount F.lay →
    CanonicalRef.frontierValue T' messages ⟨famLeaf (S.grp F.lay) F l, c⟩ =
      CanonicalRef.frontierValue T messages ⟨famLeaf (S.grp F.lay) F l, c⟩

variable {S} {messages : LeafAddr → WCT9.LayerMsg} {F : FamAddr} {T T' : Answers}

theorem searchOf_congrF (hC : FamAgree S F T T') (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf T' messages K remaining = CanonicalRef.searchOf T messages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_outF hC (respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F)

theorem referenceSearch_congrF (hC : FamAgree S F T T') (K : LeafAddr) :
    CanonicalRef.referenceSearch T' messages K = CanonicalRef.referenceSearch T messages K :=
  CanonicalRef.referenceSearch_congr (fun K r _ => searchOf_congrF hC K r) K

theorem depth_congrF (hC : FamAgree S F T T') (a : ChainAddr) :
    CanonicalRef.depth T' messages a = CanonicalRef.depth T messages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_congrF hC]

section Chains
variable (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC

/-- A member's own chains: from the frontier on, the rows agree. -/
theorem eval_chainF {L : LeafAddr} (hL : ∃ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay ∧ famLeaf (S.grp F.lay) F l = L) {c count : Nat}
    (hc : c < chainCount L.lay) (hd : CanonicalRef.depth T messages ⟨L, c⟩ ≤ count) (hcount : count ≤ 256) :
    evalWithAnswerFn T' (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T' L.lay L.tree L.leaf c)) =
      evalWithAnswerFn T (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T L.lay L.tree L.leaf c)) := by
  obtain ⟨l, hr, rfl⟩ := hL
  obtain ⟨e, rfl⟩ : ∃ e, count = CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ + e :=
    ⟨count - CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩, by omega⟩
  have hd' : CanonicalRef.depth T' messages ⟨famLeaf (S.grp F.lay) F l, c⟩ =
      CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ :=
    depth_congrF hC.toFamAgree ⟨famLeaf (S.grp F.lay) F l, c⟩
  rw [eval_chainW_add', eval_chainW_add' T, Nat.zero_add]
  have hf := hC.front l hr c hc
  unfold CanonicalRef.frontierValue honestChainValueW at hf
  simp only at hf
  rw [hd'] at hf
  rw [hf]
  refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
  refine Mask.respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW]
  exact hC.rows l hr c hc step value hlo (by omega)

include hF in
theorem wotsEnd_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) (i : Nat) (hi : i < chainCount lay) :
    WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  have hleaf : leaf < 2 ^ 24 := by have := height_pow_le lay; omega
  by_cases hfa : FamAlias S F lay tree leaf
  · obtain ⟨l, hal, hll⟩ := famAlias_member S hfa
    have hr : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 : S.grp F.lay * F.fam + l.val = leaf := hll
      rw [h1, ← leafAlias_famLay S hal]
      exact hreal
    generalize hL : famLeaf (S.grp F.lay) F l = L at hal hll
    have hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24 := ⟨hleaf, hll ▸ hleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsEnd
    rw [Mask.chainW_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb,
      show maxDigit lay i = maxDigit L.lay i by rw [hal.1]]
    exact eval_chainF hC ⟨l, hr, hL⟩ hi' (CanonicalRef.depth_le T messages ⟨L, i⟩ hi')
      (by have := width_le L.lay i; omega)
  · exact wotsEnd_outF hC.toFamAgree hF hleaf hfa i hi

include hF in
theorem wotsValue_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) (digits : List Nat) (i : Nat)
    (hi : i < chainCount lay) (hdig : digits.getD i 0 ≤ 256)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) →
      CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    WCT9.wotsValue T' lay tree leaf digits i = WCT9.wotsValue T lay tree leaf digits i := by
  have hleaf : leaf < 2 ^ 24 := by have := height_pow_le lay; omega
  by_cases hfa : FamAlias S F lay tree leaf
  · obtain ⟨l, hal, hll⟩ := famAlias_member S hfa
    have hr : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 : S.grp F.lay * F.fam + l.val = leaf := hll
      rw [h1, ← leafAlias_famLay S hal]
      exact hreal
    have hdl := halias l hal
    generalize hL : famLeaf (S.grp F.lay) F l = L at hal hll hdl
    have hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24 := ⟨hleaf, hll ▸ hleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsValue
    rw [Mask.chainW_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb]
    exact eval_chainF hC ⟨l, hr, hL⟩ hi' hdl hdig
  · unfold WCT9.wotsValue
    rw [wotsSeed_outF hC.toFamAgree (famBound_lt S hF) hleaf hfa]
    exact eval_chain_outF hC.toFamAgree hF hleaf
      (by have := chainCount_le lay; simp only [Nat.reducePow]; omega) (fun h => hfa h.1) (by omega) _

include hF in
theorem wotsRoot_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_congrF hC hF hreal i (List.mem_range.mp hi))]
  exact eval_outF hC.toFamAgree (respectsF_lowerLeafHash S F _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))

include hF in
theorem wotsTree_congrF (lay : Layer) (tree : Nat) : WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_congrF hC hF (List.mem_range.mp hleaf))]
  split_ifs
  · exact eval_outF hC.toFamAgree (respectsF_buildTopLevels S F _)
  · exact eval_outF hC.toFamAgree (respectsF_lowerLevels S F _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))
end Chains

theorem famOut_of_coverP {q : Spec.Domain} (h : ∀ c ∈ coverAddrsF S F, UntouchedP c q) : FamOut S F q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro l c step value hc hs heq
    exact h ⟨famLeaf (S.grp F.lay) F l, c⟩ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_finRange l,
      List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩⟩)) step value hs heq
  · intro j hj heq
    apply h ⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    rw [heq]
    unfold seedTweakP seedSlot seedTweak WCT9.lowerOrdinal WCT9.lowerSeedHeader
    simp only
    split <;> simp [Nat.mul_div_cancel_left]
  · trivial

variable (S) in
theorem respects_famOutP {α : Type} {p : M α} (h : ∀ c, Respects (UntouchedP c) p) (F : FamAddr) :
    Respects (FamOut S F) p :=
  Respects.mono' (ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf.respects_coverP h (coverAddrsF S F))
    fun _ hq => famOut_of_coverP hq

theorem buildForest_outF (hC : FamAgree S F T T') (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    ExecEq T T' (buildForest index selected words) (buildForest index selected words) := by
  have h := respects_famOutP S (fun a => CanonicalRef.respectsP_buildForest a index selected words) F
  exact ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem forestCommitment_outF (hC : FamAgree S F T T') (index : Nat) :
    CanonicalRef.forestCommitment T' index = CanonicalRef.forestCommitment T index := by
  have h := congrArg Prod.snd (buildForest_outF hC index (forestSelectionFromOutput 0) (forestWordsFromOutput 0)).1
  simpa only [buildForest_commitment] using h

theorem sourceMessages_congrF (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    CanonicalRef.sourceMessages T' = CanonicalRef.sourceMessages T := by
  funext K
  unfold CanonicalRef.sourceMessages
  split
  · unfold Extract.honestPair
    rw [wotsTree_congrF hC hF]
  · rw [forestCommitment_outF hC.toFamAgree]
end Congr

section Game
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
variable {S : FamScheme} {messages : LeafAddr → LayerMsg} {F : FamAddr} {T T' : Answers}

section Pieces
variable (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC hF

theorem eval_signTop_fam (cache : Cache) (leaf : Nat) (hleaf : leaf < 2 ^ height 0) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias 0 0 leaf (famLeaf (S.grp F.lay) F l) →
      ∀ i, i < chainCount F.lay → CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    evalWithAnswerFn T' (signTop cache leaf digits) = evalWithAnswerFn T (signTop cache leaf digits) := by
  have hv : (List.range (chainCount 0)).map (WCT9.wotsValue T' 0 0 leaf digits) =
      (List.range (chainCount 0)).map (WCT9.wotsValue T 0 0 leaf digits) := by
    apply List.map_congr_left
    intro i hi
    apply wotsValue_congrF hC hF hleaf digits i (List.mem_range.mp hi)
    · have := hvalid i (List.mem_range.mp hi)
      have := width_le 0 i
      omega
    · intro l hal
      exact halias l hal i (leafAlias_famLay S hal ▸ List.mem_range.mp hi)
  rw [Mask.eval_signTop_wots T' cache leaf digits hvalid, Mask.eval_signTop_wots T cache leaf digits hvalid, hv,
    eval_outF hC.toFamAgree (respectsF_topPath S F _ _)]

theorem wotsPieces_congrF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ height lay)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) →
      ∀ i, i < chainCount F.lay → CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    wotsPieces T' lay tree leaf digits = wotsPieces T lay tree leaf digits := by
  unfold wotsPieces
  rw [wotsTree_congrF hC hF]
  congr 1
  apply List.map_congr_left
  intro i hi
  apply wotsValue_congrF hC hF hleaf digits i (List.mem_range.mp hi)
  · have := hvalid i (List.mem_range.mp hi); have := width_le lay i; omega
  · intro l hal
    exact halias l hal i (leafAlias_famLay S hal ▸ List.mem_range.mp hi)

theorem fixedPrepared_pieces_congrF (index : Nat) (hi : index < 2 ^ 31) (lay : Layer) (hlay : lay ≠ 0)
    {counter : BitVec 32} {digits : List Nat} {low : Bool}
    (hsearch : CanonicalRef.referenceSearch T messages (sourceLeaf index lay) = some (counter, digits, low))
    (htree : F.tree < 2 ^ 40) :
    preparedPieces lay (route index lay).1 (fixedPrepared T' index lay) digits =
      preparedPieces lay (route index lay).1 (fixedPrepared T index lay) digits := by
  have hv := CanonicalRef.Mask.source_digits_valid T messages lay hsearch rfl
  have hp (X : Answers) : preparedPieces lay (route index lay).1 (fixedPrepared X index lay) digits =
      wotsPieces X lay (route index lay).2 (route index lay).1 digits := by
    unfold fixedPrepared
    rw [← eval_buildTreePrefixes_result X hlay _ _ (route_leaf_bound index lay)]
    exact preparedPieces_result X hlay _ _ digits hv (route_leaf_bound index lay)
  rw [hp, hp]
  apply wotsPieces_congrF hC hF (route_leaf_bound index lay) digits hv
  intro l hal i _
  exact CanonicalRef.Mask.sourceLeaf_alias T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ hi hsearch htree
    (famLeaf_lt S hF l) hal
end Pieces

theorem searchPreparedLayers_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index < 2 ^ 31)
    (forest : PairRoot) (hforest : LayerMsg.pair forest.1 forest.2 = sourceMessages T (sourceLeaf index 3)) :
    let prepared := (⟨fixedPrepared T index 1, fixedPrepared T index 2, fixedPrepared T index 3⟩ : PreparedRoots)
    let prepared' := (⟨fixedPrepared T' index 1, fixedPrepared T' index 2, fixedPrepared T' index 3⟩ : PreparedRoots)
    ExecEq T T' (searchPreparedLayers cache index prepared forest)
      (searchPreparedLayers cache index prepared' forest) := by
  let messages := sourceMessages T
  have hlevels (lay : Layer) : (fixedPrepared T' index lay).levels = (fixedPrepared T index lay).levels := by
    dsimp only [fixedPrepared]
    rw [wotsTree_congrF hC hF]
  have hs (lay : Layer) (remaining : Nat)
      (_hc : referenceContext T messages (sourceLeaf index lay) = some remaining) :
      ExecEq T T' (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay))
        (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay)) :=
    let h := respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F
    ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩
  have h0 : LayerMsg.pair (topPair 1 (fixedPrepared T index 1).levels).1
      (topPair 1 (fixedPrepared T index 1).levels).2 = messages (sourceLeaf index 0) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 0 (by decide)]; rfl
  have h1 : LayerMsg.pair (topPair 2 (fixedPrepared T index 2).levels).1
      (topPair 2 (fixedPrepared T index 2).levels).2 = messages (sourceLeaf index 1) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 1 (by decide)]; rfl
  have h2 : LayerMsg.pair (topPair 3 (fixedPrepared T index 3).levels).1
      (topPair 3 (fixedPrepared T index 3).levels).2 = messages (sourceLeaf index 2) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 2 (by decide)]; rfl
  have h3 : LayerMsg.pair forest.1 forest.2 = messages (sourceLeaf index 3) := hforest
  have hc0 : referenceContext T messages (sourceLeaf index 0) = some WCT9.CanonicalPolicy.totalCredit := rfl
  dsimp only
  unfold searchPreparedLayers
  dsimp only
  rw [hlevels 1, hlevels 2, hlevels 3, h0, h1, h2, h3]
  refine ExecEq.bind (hs 0 WCT9.CanonicalPolicy.totalCredit hc0) ?_
  intro found0 hr0
  cases found0 with
  | none => exact ExecEq.pure' _ _ _
  | some found0 =>
    rcases found0 with ⟨counter0, digits0, low0⟩
    have href0 := referenceSearch_of_run hc0 hr0
    have hc1 : referenceContext T messages (sourceLeaf index 1) =
        some (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0 digits0) := by
      apply context_parent_success (leaf := sourceLeaf index 1) (by change 1 ≠ 0; decide)
      · rw [sourceLeaf_parent index 1 (by decide)]; exact hc0
      · rw [sourceLeaf_parent index 1 (by decide)]; exact href0
    dsimp only
    split
    · exact ExecEq.pure' _ _ _
    · refine ExecEq.bind (hs 1 _ hc1) ?_
      intro found1 hr1
      cases found1 with
      | none => exact ExecEq.pure' _ _ _
      | some found1 =>
        rcases found1 with ⟨counter1, digits1, low1⟩
        have href1 := referenceSearch_of_run hc1 hr1
        have hc2 : referenceContext T messages (sourceLeaf index 2) =
            some (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0
              digits0) 1 low1 digits1) := by
          apply context_parent_success (leaf := sourceLeaf index 2) (by change 2 ≠ 0; decide)
          · rw [sourceLeaf_parent index 2 (by decide)]; exact hc1
          · rw [sourceLeaf_parent index 2 (by decide)]; exact href1
        dsimp only
        split
        · exact ExecEq.pure' _ _ _
        · refine ExecEq.bind (hs 2 _ hc2) ?_
          intro found2 hr2
          cases found2 with
          | none => exact ExecEq.pure' _ _ _
          | some found2 =>
            rcases found2 with ⟨counter2, digits2, low2⟩
            have href2 := referenceSearch_of_run hc2 hr2
            have hc3 : referenceContext T messages (sourceLeaf index 3) =
                some (CanonicalPolicy.nextResidual
                  (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0
                    digits0) 1 low1 digits1) 2 low2 digits2) := by
              apply context_parent_success (leaf := sourceLeaf index 3) (by change 3 ≠ 0; decide)
              · rw [sourceLeaf_parent index 3 (by decide)]; exact hc2
              · rw [sourceLeaf_parent index 3 (by decide)]; exact href2
            dsimp only
            split
            · exact ExecEq.pure' _ _ _
            · refine ExecEq.bind (hs 3 _ hc3) ?_
              intro found3 hr3
              cases found3 with
              | none => exact ExecEq.pure' _ _ _
              | some found3 =>
                rcases found3 with ⟨counter3, digits3, low3⟩
                have href3 := referenceSearch_of_run hc3 hr3
                have hv0 := CanonicalRef.Mask.source_digits_valid T messages 0 href0 rfl
                have ht : ExecEq T T' (signTop cache (route index 0).1 digits0)
                    (signTop cache (route index 0).1 digits0) := by
                  have hlt : (route index (0 : Layer)).1 < 2 ^ height (0 : Layer) := route_leaf_bound index (0 : Layer)
                  refine ⟨eval_signTop_fam hC hF cache _ hlt _ hv0 ?_, ?_⟩
                  · intro l hal i _
                    apply CanonicalRef.Mask.sourceLeaf_alias T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ hi href0
                      htree (famLeaf_lt S hF l)
                    rw [SigGolfCandidate.T3.route_top_tree index hi]
                    exact hal
                  · rw [SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop,
                      SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop]
                refine ExecEq.bind ht ?_
                intro top _
                apply ExecEq.pure_eq
                rw [fixedPrepared_pieces_congrF hC hF index hi 1 (by decide) href1 htree,
                  fixedPrepared_pieces_congrF hC hF index hi 2 (by decide) href2 htree,
                  fixedPrepared_pieces_congrF hC hF index hi 3 (by decide) href3 htree]

theorem execEq_outF (hC : FamAgree S F T T') {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    ExecEq T T' p p :=
  ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem signFromOutput_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    ExecEq T T' (signFromOutput cache rho counter output) (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine ExecEq.bind (buildForest_outF hC.toFamAgree _ _ _) ?_
  intro forest hforest
  refine ExecEq.bind_effect (Mask.queried_length_prepareRoots_congr _ _ _) ?_
  simp only [prepareRoots_result]
  refine ExecEq.bind (searchPreparedLayers_famEq hC htree hF cache _ (digestIndex_lt output) forest.2 ?_) ?_
  · rw [← hforest, buildForest_commitment, sourceMessages_route_bottom T _ (digestIndex_lt output)]
  · intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem signPayload_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    ExecEq T T'
      (SigGolfCandidate.Research.SharedForest.signPayload cache message)
      (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateNonce S F _)) ?_
  intro rho _
  refine ExecEq.bind (execEq_outF hC.toFamAgree
    (respects_famOutP S (fun a => CanonicalRef.respectsP_sharedDigestSearch a _ _ _ _) F)) ?_
  intro selected _
  cases selected with
  | none => exact ExecEq.pure' _ _ _
  | some selected =>
    rcases selected with ⟨counter, output⟩
    refine ExecEq.bind (signFromOutput_famEq hC htree hF _ _ _ _) ?_
    intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem authenticatedSign_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    ExecEq T T'
      (PairedOuter.FullGame.authenticatedSign published request)
      (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateMac S F _)) ?_
  intro tag _
  split
  · exact signPayload_famEq hC htree hF _ _
  · exact ExecEq.pure' _ _ _

theorem keygen_famEq (hC : FamCongr S (sourceMessages T) F T T')
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    ExecEq T T' SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygen := by
  have hp : ExecEq T T' keygenPayload keygenPayload := by
    refine ⟨?_, ?_⟩
    · rw [Wots.Mask.eval_keygenPayload_wots, Wots.Mask.eval_keygenPayload_wots, wotsTree_congrF hC hF]
      exact eval_outF hC.toFamAgree (respects_famOut S (fun c => Wots.Mask.respects_keygenRest c _) F)
    · refine Wots.Mask.queried_length_keygenPayload_congr (S := FamOut S F)
        (fun L => respects_famOut S (fun c => Wots.Mask.respects_buildTopLevels c L) F) T' T hC.out ?_
      rw [(SigGolfCandidate.T3.Correctness.eval_buildTopTree T').trans (WCT9.wotsTree_top T').symm,
        (SigGolfCandidate.T3.Correctness.eval_buildTopTree T).trans (WCT9.wotsTree_top T).symm,
        wotsTree_congrF hC hF]
  unfold SigGolfCandidate.T3.keygen
  refine ExecEq.bind hp ?_
  rintro ⟨pk, region⟩ _
  exact ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateMac S F _)) fun _ _ => ExecEq.pure' _ _ _

/-- **Family congruence of the reference game.** If `T'` agrees with `T` outside family `F` (and on the other halves
of its cells), and on the rows of all of `F`'s chains from their signed digits on and on their frontier values, the
honest reference game is unchanged. -/
theorem referenceGame_fam (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame T' adversary q = PairedReference.referenceGame T adversary q :=
  PairedReference.referenceGame_congr _ _ (keygen_famEq hC hF).1 (keygen_famEq hC hF).2
    (fun cache request => (authenticatedSign_famEq hC htree hF cache request).1)
    (fun cache request => (authenticatedSign_famEq hC htree hF cache request).2) adversary q
end Game

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamTest ====
section

/-! # Family restart, step P4a: the seed-test program of a family (r3-lean-seedfam)

Family port of the per-leaf test program (`WotsLeafTest`: `Leaf.TParams/tY/fY/prefAns/isTestQ`,
`Normalized.Test.{publicAt, withPublic, pubAns, testImpl, evalT_testRun, tdepth_testImpl, enT_testImpl}` and the
`RawLeaf` route part, plus `WotsLeafCore.{PData, mkP, tY_mkP, evaluate_tY}`), with the chains of a leaf
`Fin (chainCount L.lay)` replaced by the chains `GChainW g w` of a family `F` of `g` leaves of `w` chains.

* `FamRestart`: `TParamsF`, `tYF`, `fYF`, `prefAnsF`, `isTestQF`, `PDataF`, `mkPF`, `tYF_mkPF`, `evaluate_tYF`.
* `CanonicalRef.Normalized.FamTest`: `publicAtF`, `withPublicF`, `pubAnsF`, `testImplF`, `evalT_pubAnsF`,
  `testImpl_bridgeF`, `evalT_testRunF`, `tdepth_testImplF`, `enT_testImplF`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF zeroOfF zhF)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable

/-- Parameters of the family test program: row functions and labels of the family's step-0 rows (`g`, `lab`), of
chain `a`'s prefix tables (`gt`, `labt`), and the revealed seeds `r`. -/
structure TParamsF (G W d : Nat) where
  g : GChainW G W → Digest → Digest
  lab : GChainW G W → Digest
  gt : Fin d → Digest → Digest
  labt : Fin d → Digest
  r : GChainW G W → Digest

section Defs
variable {G W : Nat} (d : Nat) (Rev : Finset (GChainW G W)) (aF : Free Rev) (P : TParamsF G W d)

/-- Chain `a`'s prefix tables, row `0` programmed at the seed `s` (the other rows at `0`). -/
def tYF (s : Digest) : Fin d → Digest → Digest :=
  fun i => Function.update (P.gt i) (if i.val = 0 then s else 0) (P.labt i)

/-- Step-0 rows of the family's chains: revealed chains programmed at `r`, unrevealed ones at `y`. -/
noncomputable def fYF (y : Free Rev → Digest) : GChainW G W → Digest → Digest :=
  fun c => Function.update (P.g c) (if hc : c ∈ Rev then P.r c else y ⟨c, hc⟩) (P.lab c)

/-- Answer to a prefix query of chain `a`: row `0` is a test on `a`'s seed. -/
noncomputable def prefAnsF (p : Fin d × Digest) : OracleComp (TSpec (Free Rev) Digest) Digest :=
  if p.1.val = 0 then (fun b => if b then P.labt p.1 else P.gt p.1 p.2) <$> testQ (aF, p.2)
  else pure (Function.update (P.gt p.1) 0 (P.labt p.1) p.2)
end Defs

theorem evalT_prefAnsF {G W d : Nat} {Rev : Finset (GChainW G W)} (aF : Free Rev) (P : TParamsF G W d)
    (y : Free Rev → Digest) (p : Fin d × Digest) :
    evalT y (prefAnsF d Rev aF P p) = PMF.pure (tYF d P (y aF) p.1 p.2) := by
  unfold prefAnsF tYF
  split_ifs with h0
  · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]
  · rfl

/-- Queries answered by a test: chain `a`'s prefix row `0`, and step-0 rows of unrevealed chains of the family. -/
noncomputable def isTestQF (G W : Nat) (F : FamAddr) (a : ChainAddr) (d : Nat) (Rev : Finset (GChainW G W)) :
    RefWorld.Domain → Prop
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => p.1.val = 0
      | none =>
          match zeroOfF G W F input with
          | some cv => cv.1 ∉ Rev
          | none => False
  | _ => False

/-- The free parameters of the programmed world: the family's step-0 row functions and labels, `a`'s prefix tables
and labels. -/
abbrev PDataF (G W d : Nat) :=
  ((GChainW G W → Digest → Digest) × (GChainW G W → Digest)) × ((Fin d → Digest → Digest) × (Fin d → Digest))
/-- Test-program parameters from the free parameters and the revealed seeds. -/
def mkPF {G W d : Nat} (p : PDataF G W d) (r : GChainW G W → Digest) : TParamsF G W d :=
  ⟨p.1.1, p.1.2, p.2.1, p.2.2, r⟩

theorem tYF_mkPF {G W d : Nat} (p : PDataF G W d) (r r' : GChainW G W → Digest) :
    tYF d (mkPF p r) = tYF d (mkPF p r') := rfl

/-- The endpoint of the programmed prefix tables: independent of the seed they are programmed at. -/
theorem evaluate_tYF {G W d : Nat} (hd : 1 ≤ d) (P : TParamsF G W d) (σ : Digest) :
    evaluate (tYF d P σ) σ = evaluate (tYF d P 0) 0 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [evaluate]
  have h1 : Fin.tail (tYF (d' + 1) P σ) = Fin.tail (tYF (d' + 1) P 0) := by
    funext i v
    simp only [Fin.tail, tYF, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega)]
  have h2 : tYF (d' + 1) P σ 0 σ = tYF (d' + 1) P 0 0 0 := by
    simp only [tYF, Fin.val_zero, if_true, Function.update_self]
  rw [h1, h2]

end ClaudeWCT.W9.T3.Security.Wots.FamRestart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTest
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf chainOfF zeroOfF zhF)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.Arith.SideChannel (TSpec coinQ testQ evalT answerImpl Free enT exT tdepth)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec observedImpl record evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The public table `B` with the used halves of the family's step-0 rows replaced by `f`. -/
noncomputable def publicAtF (G W : Nat) (F : FamAddr) (B : Answers) (f : GChainW G W → Digest → Digest)
    (input : HashInput) : HashOutput :=
  match zeroOfF G W F input with
  | some cv => joinHalf (zhF G W F cv.1) (f cv.1 cv.2) (WCT9.halfOf (!zhF G W F cv.1) (B (.inl (.inr input))))
  | none => B (.inl (.inr input))
noncomputable def withPublicF (G W : Nat) (F : FamAddr) (B : Answers) (f : GChainW G W → Digest → Digest) : Answers
  | .inl (.inr input) => publicAtF G W F B f input
  | .inl (.inl coin) => B (.inl (.inl coin))
  | .inr coordinate => B (.inr coordinate)

section Defs
variable (G W : Nat) (F : FamAddr) (a : ChainAddr) (d : Nat) (B : Answers)
  (Rev : Finset (GChainW G W)) (aF : Free Rev) (P : TParamsF G W d)
/-- Answer to any other public query: step-0 rows of unrevealed chains of the family are tests. -/
noncomputable def pubAnsF (input : HashInput) : OracleComp (TSpec (Free Rev) Digest) HashOutput :=
  match zeroOfF G W F input with
  | some cv =>
      if hc : cv.1 ∈ Rev then
        pure (joinHalf (zhF G W F cv.1) (Function.update (P.g cv.1) (P.r cv.1) (P.lab cv.1) cv.2)
          (WCT9.halfOf (!zhF G W F cv.1) (B (.inl (.inr input)))))
      else (fun b => joinHalf (zhF G W F cv.1) (if b then P.lab cv.1 else P.g cv.1 cv.2)
          (WCT9.halfOf (!zhF G W F cv.1) (B (.inl (.inr input))))) <$> testQ (⟨cv.1, hc⟩, cv.2)
  | none => pure (B (.inl (.inr input)))

/-- The test-program implementation of the prefix game's oracle world (family version). -/
noncomputable def testImplF : QueryImpl RefWorld (StateT (TObs d) (OracleComp (TSpec (Free Rev) Digest)))
  | .inl (.inl n) => StateT.lift (coinQ n)
  | .inl (.inr input) =>
      match PrefixGame.rowOf a d input with
      | some p => StateT.mk fun obs =>
          (fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
            (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
              record obs p w)) <$> prefAnsF d Rev aF P p
      | none => StateT.lift (pubAnsF G W F d B Rev P input)
  | .inr _ => pure ()
end Defs

section Bridge
variable {G W : Nat} {F : FamAddr} {a : ChainAddr} {d : Nat} (B : Answers)
  {Rev : Finset (GChainW G W)} (aF : Free Rev) (P : TParamsF G W d)

theorem evalT_pubAnsF (y : Free Rev → Digest) (input : HashInput) :
    evalT y (pubAnsF G W F d B Rev P input) = PMF.pure (publicAtF G W F B (fYF d Rev P y) input) := by
  unfold pubAnsF publicAtF
  cases hz : zeroOfF G W F input with
  | none => rfl
  | some cv =>
    simp only
    unfold fYF
    split_ifs with hc
    · rfl
    · rw [evalT_map, ClaudeWCT.Arith.SideChannel.evalT_testQ, PMF.pure_map, ite_decide_update]

/-- Per-query identification of the test program, run against `y`, with the programmed prefix-game world. -/
theorem testImpl_bridgeF (y : Free Rev → Digest) (q : RefWorld.Domain) :
    (StateT.mk fun s => evalT y ((testImplF G W F a d B Rev aF P q).run s) : StateT (TObs d) PMF _) =
      simulateQ (observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tYF d P (y aF)))
        (Route.routeImpl a d B (withPublicF G W F B (fYF d Rev P y)) q) := by
  rcases q with (n | input) | u
  · funext s
    simp only [testImplF, Route.routeImpl, simulateQ_spec_query, StateT.run_lift]
    show evalT y (ClaudeWCT.Arith.SideChannel.coinQ n >>= fun a => pure (a, s)) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl n).map (fun answer => (answer, s))
    rw [ClaudeWCT.Arith.SideChannel.evalT_bind, ClaudeWCT.Arith.SideChannel.evalT_coinQ]
    rfl
  · funext s
    simp only [testImplF, Route.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [simulateQ_map, simulateQ_spec_query]
        show evalT y ((fun w => (joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) w
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (B (.inl (.inr input)))),
            record s p w)) <$> prefAnsF d Rev aF P p) = _
        rw [evalT_map, evalT_prefAnsF, PMF.pure_map]
        change _ = StateT.run (_ <$> observedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (Sum.inr p)) s
        rw [StateT.run_map]
        change _ = (fun x => _) <$> PMF.pure _
        rw [PMF.monad_map_eq_map, PMF.pure_map]
    | none =>
        simp only [simulateQ_pure, StateT.run_lift]
        show evalT y (pubAnsF G W F d B Rev P input >>= fun a => pure (a, s)) = _
        rw [ClaudeWCT.Arith.SideChannel.evalT_bind, evalT_pubAnsF B P y input, PMF.pure_bind]
        rfl
  · funext s
    rfl

/-- **Bridge.** The family test program run against `y` is the prefix-game run in the world programmed at `y`. -/
theorem evalT_testRunF (y : Free Rev → Digest) {α : Type} (Gm : OracleComp RefWorld α) (obs : TObs d) :
    evalT y ((simulateQ (testImplF G W F a d B Rev aF P) Gm).run obs) =
      observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tYF d P (y aF))
        (simulateQ (Route.routeImpl a d B (withPublicF G W F B (fYF d Rev P y))) Gm) obs := by
  unfold evalT observedRun
  rw [ClaudeWCT.Arith.SideChannel.simulateQ_run_stateT, ← QueryImpl.simulateQ_compose]
  congr 2
  funext q
  rw [QueryImpl.apply_compose]
  exact testImpl_bridgeF B aF P y q
end Bridge

section Counts
variable {G W : Nat} {F : FamAddr} {a : ChainAddr} {d : Nat} (B : Answers) {Rev : Finset (GChainW G W)}
  (aF : Free Rev) (P : TParamsF G W d)

theorem tdepth_testImplF (q : RefWorld.Domain) (s : TObs d) :
    tdepth ((testImplF G W F a d B Rev aF P q).run s) ≤ if RefCharged q then 1 else 0 := by
  rcases q with (n | input) | u
  · simp only [testImplF, StateT.run_lift]
    rw [if_neg (by simp [RefCharged])]
    refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
    rw [Nat.add_zero, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _) from
      (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.tdepth_coin]
    simp [ClaudeWCT.Arith.SideChannel.tdepth_pure]
  · rw [if_pos (by simp [RefCharged])]
    cases hp : PrefixGame.rowOf a d input with
    | some p =>
        simp only [testImplF, hp, StateT.run_mk]
        refine (tdepth_map_le _ _).trans ?_
        unfold prefAnsF
        split_ifs with h0
        · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
        · exact Nat.zero_le _
    | none =>
        simp only [testImplF, hp, StateT.run_lift]
        refine (ClaudeWCT.Arith.SideChannel.tdepth_bind_le _ _ 0 fun _ => le_rfl).trans ?_
        rw [Nat.add_zero]
        unfold pubAnsF
        cases hz : zeroOfF G W F input with
        | none => exact Nat.zero_le _
        | some cv =>
            simp only
            split_ifs with hc
            · exact Nat.zero_le _
            · exact (tdepth_map_le _ _).trans (le_of_eq (tdepth_testQ _))
  · exact Nat.zero_le _

theorem enT_testImplF (y : Free Rev → Digest) (q : RefWorld.Domain) (s : TObs d) :
    enT y ((testImplF G W F a d B Rev aF P q).run s) = if isTestQF G W F a d Rev q then 1 else 0 := by
  rcases q with (n | input) | u
  · rw [if_neg (by simp [isTestQF])]
    simp only [testImplF, StateT.run_lift]
    rw [ClaudeWCT.Arith.SideChannel.enT_bind, show coinQ n = (coinQ n >>= pure : OracleComp (TSpec (Free Rev) Digest) _)
      from (bind_pure _).symm, ClaudeWCT.Arith.SideChannel.enT_coin]
    simp [ClaudeWCT.Arith.SideChannel.enT_pure, ClaudeWCT.Arith.SideChannel.exT_const]
  · cases hp : PrefixGame.rowOf a d input with
    | some p =>
        have hT : isTestQF G W F a d Rev (.inl (.inr input)) ↔ p.1.val = 0 := by simp only [isTestQF, hp]
        simp only [testImplF, hp, StateT.run_mk]
        rw [enT_map]
        unfold prefAnsF
        split_ifs with h0 h1 h1
        · rw [enT_map, enT_testQ]
        · exact absurd (hT.mpr h0) h1
        · exact absurd (hT.mp h1) h0
        · rfl
    | none =>
        simp only [testImplF, hp, StateT.run_lift]
        rw [ClaudeWCT.Arith.SideChannel.enT_bind,
          show (fun x => enT y (pure (x, s) : OracleComp (TSpec (Free Rev) Digest) _)) = fun _ => (0 : ℝ) from rfl,
          ClaudeWCT.Arith.SideChannel.exT_const, add_zero]
        unfold pubAnsF
        cases hz : zeroOfF G W F input with
        | none =>
            rw [if_neg (by simp only [isTestQF, hp, hz]; exact id)]
            rfl
        | some cv =>
            have hT : isTestQF G W F a d Rev (.inl (.inr input)) ↔ cv.1 ∉ Rev := by simp only [isTestQF, hp, hz]
            simp only
            split_ifs with hc h1 h1
            · exact absurd hc (hT.mp h1)
            · rfl
            · rw [enT_map, enT_testQ]
            · exact absurd (hT.mpr hc) h1
  · rw [if_neg (by simp [isTestQF])]
    rfl
end Counts

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTest

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame (FamCongr sourceMessages_congrF)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
  (fillTable raw_ov_const otherHalf_fill high_fill_nonprefix)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable

/-- A row of chain `a` at a step `s < 256` that is a step-0 row of family chain `c` is step 0 of a chain with the
same layer and parity, hence read through the same half. -/
theorem chainHigh_of_zeroOfF {G W : Nat} {F : FamAddr} {a : ChainAddr} {s : Nat} {v : Digest} (hs : s < 256)
    (hac : a.chain < 2 ^ 24) (hW : W < 2 ^ 24)
    {cv : GChainW G W × Digest} (hz : zeroOfF G W F (chainRowW a s v) = some cv) :
    WCT9.chainHigh a.key.lay a.chain s = zhF G W F cv.1 := by
  have he := zeroOfF_some hz
  obtain ⟨hh, -⟩ := chainInputW_fields he
  obtain ⟨hl, -, -, hi, hst⟩ := chainHeader_fields hh
  have hs0 : s = 0 := by simp only [Nat.zero_mod] at hst; omega
  have hcc : (chainOfF G W F cv.1).chain = cv.1.2.val := rfl
  have hpar : a.chain % 2 = cv.1.2.val % 2 := by simp only [Nat.reducePow] at hi; omega
  have hl' : a.key.lay = F.lay := hl
  subst hs0
  -- img-v6 (r3-lean-nonsec): top G-ness depends on the chain index, so pin the index (both are < 2^24)
  have hcv := cv.1.2.isLt
  have heq : a.chain = cv.1.2.val := by
    rw [hcc] at hi
    simp only [Nat.reducePow] at hi
    omega
  rw [show zhF G W F cv.1 = WCT9.chainHigh F.lay cv.1.2.val 0 from rfl, hl', heq]

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

/-- The real (in-tree) family chains revealed (depth `0`) in `R`; phantom chains are never revealed. -/
noncomputable def revSetF (S : FamScheme) (F : FamAddr) (R : Tables U) :
    Finset (GChainW (S.grp F.lay) (chainCount F.lay)) :=
  Finset.univ.filter fun c => S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay ∧
    CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0

/-- The family seed of chain `c = (l, i)` for coefficients `K` (point `l·stride + i + 1`). -/
noncomputable def seedOfF {m G W : Nat} (st : Nat) (K : Fin m → Digest) (c : GChainW G W) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn K) (c.1.val * st + c.2.val + 1)
/-- Step-0 rows of the family's chains programmed at the family seeds. -/
noncomputable def progFF {m G W : Nat} (st : Nat) (g : GChainW G W → Digest → Digest) (Lab : GChainW G W → Digest)
    (K : Fin m → Digest) : GChainW G W → Digest → Digest :=
  fun c => Function.update (g c) (seedOfF st K c) (Lab c)

section Pairing
variable {G W b n : Nat} {F : FamAddr}
include hU

/-- Pairing stage 1: the family override keeps the half of a step-0 row of the family that its chain does not
read. -/
theorem otherZ_ovF (hF : FamOk G W b n F) (R : Tables U) (X : FamData G W n) (input : HashInput)
    {cv : GChainW G W × Digest} (hz : zeroOfF G W F input = some cv) :
    WCT9.halfOf (!zhF G W F cv.1) (raw (ovF G W b n F R X) (.inl (.inr input))) =
      WCT9.halfOf (!zhF G W F cv.1) (raw R (.inl (.inr input))) := by
  rw [zeroOfF_some hz, raw_ovF_zero hU hF, halfOf_not_joinHalf]

/-- C3: the half of a chain-`a` row that the prefix game keeps from the rest table is unchanged by the family
override. -/
theorem otherHalf_ovF (hF : FamOk G W b n F) (R : Tables U) (X : FamData G W n) (a : ChainAddr) (s : Nat)
    (v : Digest) (hs : s < 256) (hac : a.chain < 2 ^ 24) :
    WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw (ovF G W b n F R X) (.inl (.inr (chainRowW a s v)))) =
      WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain s) (raw R (.inl (.inr (chainRowW a s v)))) := by
  cases hz : zeroOfF G W F (chainRowW a s v) with
  | none => rw [raw_ovF_pub R X _ hz]
  | some cv => rw [chainHigh_of_zeroOfF hs hac hF.width hz, otherZ_ovF hU hF R X _ hz]
end Pairing

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame (FamCongr sourceMessages_congrF)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
  (fillTable raw_ov_const otherHalf_fill high_fill_nonprefix)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable (S : FamScheme) {F : FamAddr}

section Program
variable (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hU hF haF hd1

theorem fill_pub_indepF (X X' : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest)
    (input : HashInput)
    (h : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), c ≠ ca → ∀ v,
      input ≠ chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inl (.inr input)) =
      fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X') e
        (.inl (.inr input)) := by
  rw [fill_pubF hU S hF ca haF R hd1 X e input h, fill_pubF hU S hF ca haF R hd1 X' e input h]

/-- The seed of a member chain after the fill: the family seed `seedOfF`. -/
theorem wotsSeed_fill_memF (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (e : Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) e)
        (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree (famLeaf (S.grp F.lay) F l).leaf c =
      seedOfF (S.stride F.lay) K ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)) :=
  wotsSeed_fillF hU S hF ca haF R hd1 K f e l c hc

/-- **Programmed family congruence.** With the step-0 rows of the family's chains programmed at the family seeds
(`progFF`), the filled tables for two coefficient vectors agreeing on the seeds of the real revealed (depth-0)
chains are family congruent. -/
theorem famCongr_progF (g : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest)
    (Lab : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) (K K' : Fin (S.size F.lay F.fam) → Digest)
    (hKK : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
        seedOfF (S.stride F.lay) K c = seedOfF (S.stride F.lay) K' c) (e : Digest) :
    FamCongr S zeroMessages F
      (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K, progFF (S.stride F.lay) g Lab K)) e)
      (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K', progFF (S.stride F.lay) g Lab K')) e) := by
  set T := fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
    (K, progFF (S.stride F.lay) g Lab K)) e with hT
  set T' := fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
    (K', progFF (S.stride F.lay) g Lab K')) e with hT'
  have hA := famAgree_fill hU S hF ca haF R hd1 (K, progFF (S.stride F.lay) g Lab K) e
  have hA' := famAgree_fill hU S hF ca haF R hd1 (K', progFF (S.stride F.lay) g Lab K') e
  have hda : CanonicalRef.depth (raw R) zeroMessages a = RawPrefix.restDepth a R := (RawPrefix.restDepth_eq a R).symm
  have hnz : ∀ (L : LeafAddr) (c s : Nat) (v : Digest), s ≠ 0 → s < 256 →
      ∀ c' : GChainW (S.grp F.lay) (chainCount F.lay), ∀ v',
        chainRowW ⟨L, c⟩ s v ≠ chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c') 0 v' := by
    intro L c s v hs hs256 c' v' he
    have := (chainHeader_fields (chainInputW_fields he).1).2.2.2.2
    omega
  refine ⟨⟨fun q hq => (hA'.out q hq).trans (hA.out q hq).symm, fun o ho hno =>
    (hA'.half o ho hno).trans (hA.half o ho hno).symm⟩, ?_, ?_⟩
  · intro l hl c hc s v hs hs256
    rw [depth_fillF hU S hF ca haF R hd1 _ e] at hs
    by_cases hs0 : s = 0
    · subst hs0
      have hca : ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)) ≠ ca := by
        intro hca
        have : CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ = RawPrefix.restDepth a R := by
          rw [← hda, haF, ← hca]; rfl
        omega
      have hrev := hKK (l, ⟨c, hc⟩) hl
        (by show CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ = 0; omega)
      rw [show (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr) =
        chainOfF (S.grp F.lay) (chainCount F.lay) F (l, ⟨c, hc⟩) from rfl]
      rw [hT, hT', fill_zeroF hU S hF ca haF R hd1 _ e _ hca, fill_zeroF hU S hF ca haF R hd1 _ e _ hca]
      simp only [progFF]
      rw [hrev]
    · exact fill_pub_indepF hU S hF ca haF R hd1 _ _ e _ (fun c' _ v' => hnz _ c s v hs0 hs256 c' v')
  · intro l hl c hc
    by_cases hca : ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)) = ca
    · have hb : (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr) = a := by rw [haF, ← hca]; rfl
      rw [hb, fill_frontier_selfF hU S hF ca haF R hd1, fill_frontier_selfF hU S hF ca haF R hd1]
    · unfold CanonicalRef.frontierValue honestChainValueW
      simp only
      rw [depth_fillF hU S hF ca haF R hd1 _ e, depth_fillF hU S hF ca haF R hd1 _ e,
        wotsSeed_fill_memF hU S hF ca haF R hd1 _ _ e l c hc, wotsSeed_fill_memF hU S hF ca haF R hd1 _ _ e l c hc]
      rcases Nat.eq_zero_or_pos (CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩) with h0 | hpos
      · rw [h0, hKK (l, ⟨c, hc⟩) hl h0, chainW_zero']
        simp only [evalWithAnswerFn_pure]
      · obtain ⟨k, hk⟩ : ∃ k, CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ = 1 + k :=
          ⟨CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩ - 1, by omega⟩
        rw [hk, eval_chainW_add', eval_chainW_add' T]
        have hlab : ∀ X : Fin (S.size F.lay F.fam) → Digest,
            evalWithAnswerFn (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
              (X, progFF (S.stride F.lay) g Lab X)) e)
              (WCT9.chainW (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree
                (famLeaf (S.grp F.lay) F l).leaf c 0 1
                (seedOfF (S.stride F.lay) X ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay)))) =
              Lab (l, ⟨c, hc⟩) := by
          intro X
          rw [eval_chainW_one', pad64_chainInputW]
          rw [show WCT9.chainInputW (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree
              (famLeaf (S.grp F.lay) F l).leaf c 0
              (seedOfF (S.stride F.lay) X ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay))) =
            chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F (l, ⟨c, hc⟩)) 0
              (seedOfF (S.stride F.lay) X ((l, ⟨c, hc⟩) : GChainW (S.grp F.lay) (chainCount F.lay))) from rfl,
            fill_zeroF hU S hF ca haF R hd1 _ e (l, ⟨c, hc⟩) hca]
          rw [show WCT9.chainHigh (famLeaf (S.grp F.lay) F l).lay c 0 =
            zhF (S.grp F.lay) (chainCount F.lay) F (l, ⟨c, hc⟩) from rfl, halfOf_joinHalf]
          simp only [progFF, Function.update_self]
        rw [hlab K', hlab K]
        have hk256 : 0 + 1 + k ≤ 256 := by
          have := CanonicalRef.Mask.depth_le_seven (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, c⟩; omega
        refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
        refine Mask.respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
        rw [pad64_chainInputW]
        exact (fill_pub_indepF hU S hF ca haF R hd1 _ _ e _
          (fun c' _ v' => hnz _ c step value (by omega) (by omega) c' v')).symm
end Program

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame (FamCongr sourceMessages_congrF)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
  (fillTable otherHalf_fill high_fill_nonprefix)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable (S : FamScheme) {F : FamAddr}

theorem famOut_encodingF (e : Wots.Enc.EncIndex) : FamOut S F (.inl (.inr (Wots.Enc.encInput e))) := by
  intro l c step value _ _ he
  have hn := nonEnc_chainRow ⟨famLeaf (S.grp F.lay) F l, c⟩ step value
  apply hn
  rw [← he]
  exact Wots.Enc.encInput_encHeader e

/-- Family agreement survives the normalization of the encoding rows. -/
theorem famAgree_normalizeF {R R' : Tables U}
    (hC : FamAgree S F (raw R) (raw R')) (hm : sourceMessages (raw R') = sourceMessages (raw R)) :
    FamAgree S F (answers hU R) (answers hU R') := by
  refine ⟨?_, ?_⟩
  · intro query hq
    rcases query with (coin | input) | coordinate
    · exact hC.out _ hq
    · by_cases hu : input ∈ U
      · rw [show answers hU R' (.inl (.inr input)) = (normalize hU R').2 ⟨input, hu⟩ from RawPrefix.raw_mem _ _ hu,
          show answers hU R (.inl (.inr input)) = (normalize hU R).2 ⟨input, hu⟩ from RawPrefix.raw_mem _ _ hu]
        change MessageSwap.table zeroMessages (sourceMessages (raw R')) _ _ hU R'.2 ⟨input, hu⟩ =
          MessageSwap.table zeroMessages (sourceMessages (raw R)) _ _ hU R.2 ⟨input, hu⟩
        have ht : MessageSwap.table zeroMessages (sourceMessages (raw R')) zeroMessages_fit
            (sourceMessages_fit (raw R')) hU =
            MessageSwap.table zeroMessages (sourceMessages (raw R)) zeroMessages_fit (sourceMessages_fit (raw R)) hU := by
          congr 1
        rw [ht]
        by_cases he : ∃ e, Wots.Enc.encInput e = input
        · obtain ⟨e, rfl⟩ := he
          rw [MessageSwap.table_at, MessageSwap.table_at]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ (famOut_encodingF S _)).trans (RawPrefix.raw_mem _ _ _))
        · push_neg at he
          rw [MessageSwap.table_other _ _ _ _ _ _ _ he, MessageSwap.table_other _ _ _ _ _ _ _ he]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ hq).trans (RawPrefix.raw_mem _ _ _))
      · rw [show answers hU R' (.inl (.inr input)) = (0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu,
          show answers hU R (.inl (.inr input)) = (0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu]
    · exact hC.out _ hq
  · intro o ho hno
    rw [Wots.Leaf.eval_lowerSeedPair, Wots.Leaf.eval_lowerSeedPair,
      nonEnc hU R' _ (by trivial), nonEnc hU R _ (by trivial)]
    simpa only [Wots.Leaf.eval_lowerSeedPair] using hC.half o ho hno

/-- Real members of a family whose tree is in range are source leaves. -/
theorem sourceLeaf_memF (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay) (l : Fin (S.grp F.lay))
    (hl : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay) :
    WotsExtract.SourceLeaf7 (famLeaf (S.grp F.lay) F l) :=
  ⟨htb, hl⟩

/-- Family congruence survives the normalization (messages switch from `zeroMessages` to the source messages). -/
theorem famCongr_normalizeF (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {R R' : Tables U}
    (hC : FamCongr S zeroMessages F (raw R) (raw R')) :
    FamCongr S (sourceMessages (answers hU R)) F (answers hU R) (answers hU R') := by
  have hm := sourceMessages_congrF hC hF
  have hmn : sourceMessages (answers hU R') = sourceMessages (answers hU R) := by
    rw [messages, messages, hm]
  refine ⟨famAgree_normalizeF hU S hC.toFamAgree hm, ?_, ?_⟩
  · intro l hl c hc step value hs hstep
    rw [depth_eq hU R ⟨famLeaf (S.grp F.lay) F l, c⟩ (sourceLeaf_memF S htb l hl)] at hs
    rw [answers_chainRow, answers_chainRow]
    exact hC.rows l hl c hc step value hs hstep
  · intro l hl c hc
    rw [← hmn, frontier_eq hU R' ⟨famLeaf (S.grp F.lay) F l, c⟩ (sourceLeaf_memF S htb l hl), hmn,
      frontier_eq hU R ⟨famLeaf (S.grp F.lay) F l, c⟩ (sourceLeaf_memF S htb l hl)]
    exact hC.front l hl c hc

section Route
attribute [local irreducible] raw normalize answers RawPrefix.fill ovF

theorem normalized_public_congrF {R R' : Tables U}
    (hC : FamAgree S F (raw R) (raw R')) (hm : sourceMessages (raw R') = sourceMessages (raw R))
    (input : HashInput) (heq : raw R' (.inl (.inr input)) = raw R (.inl (.inr input))) :
    answers hU R' (.inl (.inr input)) = answers hU R (.inl (.inr input)) := by
  by_cases hn : Wots.Enc.NonEnc (.inl (.inr input))
  · rw [nonEnc hU R' _ hn, nonEnc hU R _ hn, heq]
  · apply (famAgree_normalizeF hU S hC hm).out
    intro l c step value hc hs he
    have hne := nonEnc_chainRow ⟨famLeaf (S.grp F.lay) F l, c⟩ step value
    apply hn
    rw [he]
    exact hne

/-- **Programmed route.** The prefix-game routing of the family-programmed table at `K` equals the routing of the
table at `K'` with the family's step-0 rows publicly programmed at `K` (`FamTest.withPublicF`), when `K` and `K'`
give the same seeds on the real revealed chains. -/
theorem route_programmedF (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd : 1 ≤ RawPrefix.restDepth a R)
    (g : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest)
    (Lab : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) (K K' : Fin (S.size F.lay F.fam) → Digest)
    (hKK : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
        seedOfF (S.stride F.lay) K c = seedOfF (S.stride F.lay) K' c) (e : Digest) :
    Route.routeImpl a (RawPrefix.restDepth a R)
      (answers hU (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K, progFF (S.stride F.lay) g Lab K)))
      (answers hU (RawPrefix.fill a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K, progFF (S.stride F.lay) g Lab K)) e)) =
    Route.routeImpl a (RawPrefix.restDepth a R)
      (answers hU (RawPrefix.fill a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
        (K', progFF (S.stride F.lay) g Lab K')) e))
      (FamTest.withPublicF (S.grp F.lay) (chainCount F.lay) F
        (answers hU (RawPrefix.fill a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K', progFF (S.stride F.lay) g Lab K')) e))
        (progFF (S.stride F.lay) g Lab K)) := by
  have hC := famCongr_progF hU S hF ca haF R hd g Lab K K' hKK e
  have hac : a.chain < 2 ^ 24 := by
    have h1 : a.chain = ca.2.val := by rw [haF]; rfl
    have h2 := ca.2.isLt
    have h3 := ClaudeWCT.W9.T3M.Extract.chainCount_le F.lay
    omega
  have hm := sourceMessages_congrF hC hF.leaf
  funext query
  rcases query with (coin | input) | coord
  · simp only [Route.routeImpl]
  · simp only [Route.routeImpl]
    cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
    | some p =>
      simp only
      congr 1
      funext v
      congr 1
      have hp7 : (p.1 : Nat) < 256 := by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega
      rw [PrefixGame.rowOf_some hp, answers_chainRow, answers_chainRow,
        otherHalf_fill hU a _ e _ _ hp7, otherHalf_ovF hU hF _ _ _ _ _ hp7 hac, otherHalf_ovF hU hF _ _ _ _ _ hp7 hac]
    | none =>
      simp only [FamTest.withPublicF, FamTest.publicAtF]
      congr 1
      cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
      | none =>
        simp only
        symm
        apply normalized_public_congrF hU S hC.toFamAgree hm
        exact (fill_pub_indepF hU S hF ca haF R hd _ _ e input (by
          intro c hca v he
          rw [he, zeroOfF_chainRow hF] at hz
          cases hz)).symm
      | some cv =>
        simp only
        have hca : cv.1 ≠ ca := by
          intro he
          apply PrefixGame.rowOf_none hp (⟨0, hd⟩, cv.2)
          rw [zeroOfF_some hz, he, ← haF]
        have hpX : PrefixGame.rowOf a (RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay)
            (S.size F.lay F.fam) F R (K', progFF (S.stride F.lay) g Lab K'))) input = none := by
          rw [restDepth_ovF S hF R _ a]; exact hp
        rw [zeroOfF_some hz] at hpX
        have hzX := hz
        rw [zeroOfF_some hz] at hzX
        rw [zeroOfF_some hz, answers_chainRow, answers_chainRow,
          high_fill_nonprefix hU a _ e _ hpX, otherZ_ovF hU hF _ _ _ hzX]
        exact fill_zeroF hU S hF ca haF R hd _ e cv.1 hca cv.2
  · simp only [Route.routeImpl]
end Route

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamCaps ====
section

/-! # Family restart: the reveal caps (r3-lean-seedfam)

`FamCaps S`: the policy fact behind `revSet_card_le`, per leaf (every leaf's reference digits have at most `zcap lay`
zeros: lower 5, top 7 in T51 (9 in #938's v6); `famCount - 3` today) and the coefficient budget of every family
(`zcap · members + 3 ≤ size`, members = `min grp (2^height − grp·f)`, so the short last family is covered).
`leafCaps` instantiates it for today's scheme from `Core.revSet_card_le`. -/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
attribute [local instance] Classical.propDecidable

/-- Real members of family `f` of layer `lay`. -/
def famMembers (S : FamScheme) (lay : Layer) (f : Nat) : Nat := min (S.grp lay) (2 ^ height lay - S.grp lay * f)

/-- Reveal caps of a family scheme. -/
structure FamCaps (S : FamScheme) where
  zcap : Layer → Nat
  zeros_le : ∀ {U : Finset HashInput} (R : Tables U) (L : LeafAddr),
    (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0).card ≤ zcap L.lay
  size_ge : ∀ lay f, zcap lay * famMembers S lay f + 3 ≤ S.size lay f

/-- Caps of the `Correctness` layout with today's producer: top 7 (T51; #938: 9), lower 5 revealed seeds per leaf;
the family budgets `7 · 4 + 3 = 31` (top) and `5 r + 3 = famSize` (lower, `r` real members). -/
def layoutCaps : FamCaps layoutScheme where
  zcap lay := if lay = 0 then 7 else 5
  zeros_le R L := by
    have h := Core.revSet_card_le_cap L R
    unfold Core.revSet at h
    exact h
  size_ge lay f := by
    show (if lay = 0 then 7 else 5) * min (WCT9.famGrp lay) (2 ^ height lay - WCT9.famGrp lay * f) + 3 ≤
      WCT9.famSize lay f
    unfold WCT9.famGrp WCT9.famSize
    split_ifs with h
    · -- T51: 4-leaf top families, 7 · 4 + 3 = 31 = topCoefCount (img-v6: 9 · 4 + 3 = 39)
      have := min_le_left 4 (2 ^ height lay - 4 * f)
      simp only [SigGolfCandidate.T3.topCoefCount]; omega
    · exact le_rfl

end ClaudeWCT.W9.T3.Security.Wots.FamRestart
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamCore ====
section

/-! # Family restart, step P4b: frozen/mix law decomposition and per-table restart error (r3-lean-seedfam)

Family port of `WotsLeafCore` (namespace `CanonicalRef.Normalized.Core`, the normalized per-leaf part): the leaf `L`
becomes a family `F` of a scheme `S : FamScheme`, chain `a = chainOfF g w F ca`, the leaf data `LeafData L` becomes
`FamData g w (S.size F.lay F.fam)`, the leaf override `ovL` becomes `ovF`, the points `ptL` become `gptS stride`.
The laws `Core.gameD / frozenLaw / mixLaw` do not depend on the leaf and are reused.

* `KstF`, `seedsR_KstF`, `ePF`, `TstF`, `testRunF`;
* `GD_progF`, `frozen_pointF`, `route_withPublic_congrF`, `mix_pointF`, `ovSeed_ovF`;
* `revSetF_card_le` (from `FamCaps S`);
* `frozen_decompF`, `frozen_decompYF`, `mix_decompYF`;
* `tdepth_testRunF`, `errRF`, `frozen_le_mix_RF`, `mix_le_frozen_RF`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF

/-- Coefficients interpolating the revealed seeds `r` (a canonical choice). -/
noncomputable def KstF (S : FamScheme) (F : FamAddr) (R : Tables U) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) : Fin (S.size F.lay F.fam) → Digest :=
  if h : ∃ K, seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = r then h.choose else 0

theorem seedsR_KstF (S : FamScheme) (F : FamAddr) (R : Tables U) (K : Fin (S.size F.lay F.fam) → Digest) :
    seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K := by
  unfold KstF
  rw [dif_pos ⟨K, rfl⟩]
  exact (⟨K, rfl⟩ : ∃ K', seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K).choose_spec

/-- The endpoint of the programmed prefix tables. -/
def ePF {G W d : Nat} (p : PDataF G W d) : Digest := evaluate (tYF d (mkPF p 0) 0) 0

/-- The canonical honest table: coefficients `KstF r`, the family's step-0 rows programmed at their seeds. -/
noncomputable def TstF (S : FamScheme) (F : FamAddr) (a : ChainAddr) (R : Tables U)
    (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) : Answers :=
  answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (KstF S F R r, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R r))) (ePF p))

/-- The family test program. -/
noncomputable def testRunF {S : FamScheme} {F : FamAddr} {a : ChainAddr} {R : Tables U} {Res : Type}
    (GD : Answers → OracleComp RefWorld Res) (aF : Free (RawFam.revSetF S F R)) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) :
    OracleComp (TSpec (Free (RawFam.revSetF S F R)) Digest) (Res × TObs (RawPrefix.restDepth a R)) :=
  (simulateQ (FamTest.testImplF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (TstF hU S F a R p r) (RawFam.revSetF S F R) aF (mkPF p r))
    (GD (TstF hU S F a R p r))).run (fun _ _ => none)

/-- The seed of chain `a = chainOfF ca` after the family override is the family seed. -/
theorem ovSeed_ovF (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (K : Fin (S.size F.lay F.fam) → Digest) (f : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest)
    (s : Digest) : RawPrefix.ovSeed a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) s = RawFam.seedOfF (S.stride F.lay) K ca := by
  unfold RawPrefix.ovSeed
  subst haF
  exact RawFam.wotsSeed_ovF S hF R K f ca.1 ca.2.val ca.2.isLt

section Points
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca)
include hF htb haF hd1 hG

theorem GD_progF (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) :
    GD (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))) =
      GD (TstF hU S F a R p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
  unfold TstF
  apply Eq.symm
  apply hG
  apply RawFam.famCongr_normalizeF hU S htb hF.leaf
  apply RawFam.famCongr_progF hU S hF ca haF R hd1
  intro c hl hc
  have h := congrFun (seedsR_KstF S F R K) c
  have hc' : c ∈ (RawFam.revSetF S F R) := by
    simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hl, hc⟩
  simpa only [seedsR, if_pos hc', RawFam.seedOfF, gptS] using h.symm

include haca

theorem frozen_pointF (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (tYF (RawPrefix.restDepth a R) (mkPF p 0) (RawFam.seedOfF (S.stride F.lay) K ca))
      (simulateQ (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)))
        (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))
        (GD (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))) (fun _ _ => none) =
    evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
  rw [GD_progF hU S hF htb ca haF R hd1 GD hG K p]
  unfold testRunF
  rw [FamTest.evalT_testRunF]
  have hfy : fYF (RawPrefix.restDepth a R) (RawFam.revSetF S F R) (mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) =
      RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K := by
    funext c
    unfold fYF RawFam.progFF mkPF
    simp only
    split_ifs with hc
    · unfold seedsR; rw [if_pos hc]; rfl
    · rfl
  have hya : seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K aF = RawFam.seedOfF (S.stride F.lay) K ca := by
    show RawFam.seedOfF (S.stride F.lay) K aF.1 = RawFam.seedOfF (S.stride F.lay) K ca
    rw [haca]
  rw [hfy, hya, tYF_mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) 0]
  have hKK : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
      RawFam.seedOfF (S.stride F.lay) K c = RawFam.seedOfF (S.stride F.lay) (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) c := by
    intro c hl hc
    have h := congrFun (seedsR_KstF S F R K) c
    have hc' : c ∈ (RawFam.revSetF S F R) := by
      simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hl, hc⟩
    simpa only [seedsR, if_pos hc', RawFam.seedOfF, gptS] using h.symm
  rw [RawFam.route_programmedF hU S hF ca haF R hd1 p.1.1 p.1.2 K _ hKK (ePF p)]
  simp only [TstF]
end Points

/-- Routing only reads the public programming `f` off chain `ca` (chain `a`'s step-0 row is a prefix row). -/
theorem route_withPublic_congrF {G W : Nat} {F : FamAddr} {a : ChainAddr} {ca : GChainW G W}
    (haF : a = chainOfF G W F ca) {d : Nat} (hd : 1 ≤ d) (B : Answers) (f f' : GChainW G W → Digest → Digest)
    (hf : ∀ c : GChainW G W, c ≠ ca → f c = f' c) :
    Route.routeImpl a d B (FamTest.withPublicF G W F B f) = Route.routeImpl a d B (FamTest.withPublicF G W F B f') := by
  funext query
  rcases query with (coin | input) | coord
  · simp only [Route.routeImpl]
  · simp only [Route.routeImpl]
    cases hp : PrefixGame.rowOf a d input with
    | some p => rfl
    | none =>
      simp only [FamTest.withPublicF, FamTest.publicAtF]
      congr 1
      cases hz : RawFam.zeroOfF G W F input with
      | none => rfl
      | some cv =>
        simp only
        rw [hf cv.1 (by
          intro he
          apply PrefixGame.rowOf_none hp (⟨0, hd⟩, cv.2)
          rw [RawFam.zeroOfF_some hz, he, ← haF])]
  · simp only [Route.routeImpl]

section Mix
attribute [local irreducible] TstF
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca)
include hF htb haF hd1 hG haca

theorem mix_pointF (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (s : Digest) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (tYF (RawPrefix.restDepth a R) (mkPF p 0) s)
      (simulateQ (Route.routeImpl a (RawPrefix.restDepth a R) (answers hU (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)))
        (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))
        (GD (answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) (ePF p))))) (fun _ _ => none) =
    evalT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
  rw [GD_progF hU S hF htb ca haF R hd1 GD hG K p]
  unfold testRunF
  rw [FamTest.evalT_testRunF]
  have hya : seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s aF = s := by unfold seedsH; rw [if_pos rfl]
  rw [hya, tYF_mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) 0]
  have hKK : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), S.grp F.lay * F.fam + c.1.val < 2 ^ height F.lay →
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) = 0 →
      RawFam.seedOfF (S.stride F.lay) K c = RawFam.seedOfF (S.stride F.lay) (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) c := by
    intro c hl hc
    have h := congrFun (seedsR_KstF S F R K) c
    have hc' : c ∈ (RawFam.revSetF S F R) := by
      simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hl, hc⟩
    simpa only [seedsR, if_pos hc', RawFam.seedOfF, gptS] using h.symm
  rw [RawFam.route_programmedF hU S hF ca haF R hd1 p.1.1 p.1.2 K _ hKK (ePF p)]
  have hbase : answers hU (RawPrefix.fill a (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K),
      RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) (ePF p)) =
      TstF hU S F a R p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) := by unfold TstF; rfl
  rw [hbase]
  rw [route_withPublic_congrF haF hd1 (TstF hU S F a R p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) (RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)
    (fYF (RawPrefix.restDepth a R) (RawFam.revSetF S F R) (mkPF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s))]
  intro c hca
  funext v
  unfold fYF RawFam.progFF mkPF
  simp only
  split_ifs with hc
  · unfold seedsR; rw [if_pos hc]; rfl
  · have hne : (⟨c, hc⟩ : Free (RawFam.revSetF S F R)) ≠ aF := by
      intro he
      apply hca
      rw [← haca, ← he]
    unfold seedsH
    rw [if_neg hne]
    rfl
end Mix

/-- **Reveal cap of a family**: only the real members' depth-0 chains are revealed, each real member contributes at most
`zcap`, and the coefficient budget covers `zcap · members + 3`. -/
theorem revSetF_card_le {S : FamScheme} (C : FamCaps S) (F : FamAddr) (R : Tables U) :
    (RawFam.revSetF S F R).card + 3 ≤ S.size F.lay F.fam := by
  set realL : Finset (Fin (S.grp F.lay)) :=
    Finset.univ.filter fun l => S.grp F.lay * F.fam + l.val < 2 ^ height F.lay with hreal
  set Z : Fin (S.grp F.lay) → Finset (GChainW (S.grp F.lay) (chainCount F.lay)) := fun l =>
    (Finset.univ.filter fun i : Fin (chainCount F.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨famLeaf (S.grp F.lay) F l, i⟩ = 0).map
      ⟨fun i => (l, i), fun i j h => by simpa using h⟩ with hZ
  have hsub : RawFam.revSetF S F R ⊆ realL.biUnion Z := by
    intro c hc
    simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_biUnion]
    refine ⟨c.1, ?_, ?_⟩
    · rw [hreal, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc.1⟩
    · rw [hZ]
      exact Finset.mem_map.mpr ⟨c.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2⟩, rfl⟩
  have hZc : ∀ l, (Z l).card ≤ C.zcap F.lay := by
    intro l
    rw [hZ]
    simp only [Finset.card_map]
    convert C.zeros_le R (famLeaf (S.grp F.lay) F l) <;> rfl
  have hrc : realL.card ≤ famMembers S F.lay F.fam := by
    unfold famMembers
    refine le_min ?_ ?_
    · exact (Finset.card_filter_le _ _).trans (by simp)
    · have hs : realL.map Fin.valEmbedding ⊆ Finset.range (2 ^ height F.lay - S.grp F.lay * F.fam) := by
        intro x hx
        rw [Finset.mem_map] at hx
        obtain ⟨l, hl, rfl⟩ := hx
        rw [hreal, Finset.mem_filter] at hl
        rw [Finset.mem_range, Fin.valEmbedding_apply]
        omega
      have := Finset.card_le_card hs
      rwa [Finset.card_map, Finset.card_range] at this
  calc (RawFam.revSetF S F R).card + 3 ≤ (realL.biUnion Z).card + 3 :=
        Nat.add_le_add_right (Finset.card_le_card hsub) 3
    _ ≤ (∑ l ∈ realL, (Z l).card) + 3 := Nat.add_le_add_right Finset.card_biUnion_le 3
    _ ≤ (∑ _l ∈ realL, C.zcap F.lay) + 3 := Nat.add_le_add_right (Finset.sum_le_sum fun l _ => hZc l) 3
    _ = C.zcap F.lay * realL.card + 3 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ C.zcap F.lay * famMembers S F.lay F.fam + 3 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hrc) 3
    _ ≤ S.size F.lay F.fam := C.size_ge F.lay F.fam

section Decomp
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca)
include hF htb haF hd1 hG haca

/-- **Frozen law, decomposed** (family version). -/
theorem frozen_decompF :
    (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind (fun y => Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD) =
      (PMF.uniformOfFintype (Fin (S.size F.lay F.fam) → Digest)).bind (fun K => (PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))).bind
        (fun p => (evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))).map
          (fun res => (ePF p, res)))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hfr : ∀ f, Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD =
      (PMF.uniformOfFintype (Fin (RawPrefix.restDepth a R) → Digest → Digest)).bind (fun t =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (Core.gameD hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca))) (fun _ _ => none)).map
          (fun res => (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca), res))) := by
    intro f
    unfold Core.frozenLaw
    rw [show PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R)) =
      PMF.uniformOfFintype ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × Digest) from rfl, uniform_prod_bind]
    congr 1
    funext t
    simp only [ovSeed_ovF S hF ca haF R K f]
    exact uniform_bind_const _
  simp only [hfr]
  rw [uniform_program (fun c : (GChainW (S.grp F.lay) (chainCount F.lay)) => RawFam.seedOfF (S.stride F.lay) K c)]
  conv_rhs => rw [show PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) = PMF.uniformOfFintype
    ((((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest) × ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest)) ×
      ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × (Fin (RawPrefix.restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  rw [uniform_program (fun i : Fin (RawPrefix.restDepth a R) => if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (RawPrefix.restDepth a R) => Function.update (q.1 i) (if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0) (q.2 i)) =
      tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca) := rfl
  have he : evaluate (tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca)) (RawFam.seedOfF (S.stride F.lay) K ca) = ePF (gl, q) :=
    evaluate_tYF hd1 _ _
  rw [ht, he]
  unfold Core.gameD
  have hp := frozen_pointF hU S hF htb ca haF R hd1 GD hG aF haca K (gl, q)
  exact congrArg (PMF.map _) hp

/-- **Frozen law with the family data, decomposed.** -/
theorem frozen_decompYF :
    (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z))) =
      (PMF.uniformOfFintype (Fin (S.size F.lay F.fam) → Digest)).bind (fun K => (PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))).bind
        (fun p => (evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))).map
          (fun res => (((K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)), (ePF p, res))))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hfr : ∀ f, Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD =
      (PMF.uniformOfFintype (Fin (RawPrefix.restDepth a R) → Digest → Digest)).bind (fun t =>
        (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (Core.gameD hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca))) (fun _ _ => none)).map
          (fun res => (evaluate t (RawFam.seedOfF (S.stride F.lay) K ca), res))) := by
    intro f
    unfold Core.frozenLaw
    rw [show PMF.uniformOfFintype (Hidden (RawPrefix.restDepth a R)) =
      PMF.uniformOfFintype ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × Digest) from rfl, uniform_prod_bind]
    congr 1
    funext t
    simp only [ovSeed_ovF S hF ca haF R K f]
    exact uniform_bind_const _
  simp only [hfr, PMF.map_bind, PMF.map_comp]
  rw [uniform_program (fun c : (GChainW (S.grp F.lay) (chainCount F.lay)) => RawFam.seedOfF (S.stride F.lay) K c)]
  conv_rhs => rw [show PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) = PMF.uniformOfFintype
    ((((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest) × ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest)) ×
      ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × (Fin (RawPrefix.restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  rw [uniform_program (fun i : Fin (RawPrefix.restDepth a R) => if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (RawPrefix.restDepth a R) => Function.update (q.1 i) (if i.val = 0 then RawFam.seedOfF (S.stride F.lay) K ca else 0) (q.2 i)) =
      tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca) := rfl
  have he : evaluate (tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) (RawFam.seedOfF (S.stride F.lay) K ca)) (RawFam.seedOfF (S.stride F.lay) K ca) = ePF (gl, q) :=
    evaluate_tYF hd1 _ _
  rw [ht, he]
  unfold Core.gameD
  have hp := frozen_pointF hU S hF htb ca haF R hd1 GD hG aF haca K (gl, q)
  exact congrArg (PMF.map _) hp

/-- **Mixture law with the family data, decomposed.** -/
theorem mix_decompYF :
    (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z))) =
      (PMF.uniformOfFintype (Fin (S.size F.lay F.fam) → Digest)).bind (fun K => (PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))).bind
        (fun p => (PMF.uniformOfFintype Digest).bind (fun s =>
          (evalT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))).map
            (fun res => (((K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)), (ePF p, res)))))) := by
  rw [uniform_prod_bind]
  congr 1
  funext K
  have hmx : ∀ f, Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD =
      (PMF.uniformOfFintype Digest).bind (fun s => (PMF.uniformOfFintype (Fin (RawPrefix.restDepth a R) → Digest → Digest)).bind
        (fun t => (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl t
          (Core.gameD hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) GD (evaluate t s)) (fun _ _ => none)).map
          (fun res => (evaluate t s, res)))) := by
    intro f
    unfold Core.mixLaw
    simp only [SphincsSecurity.Concrete.PartialChainEndpoint.realRun,
      SphincsSecurity.Concrete.PartialChainEndpoint.completeTables_empty,
      SphincsSecurity.Concrete.EndpointPreimageDensity.real, PMF.bind_bind, PMF.bind_map,
      PMF.map_comp, Function.comp_def]
    rw [PMF.bind_comm]
  simp only [hmx, PMF.map_bind, PMF.map_comp]
  rw [uniform_program (fun c : (GChainW (S.grp F.lay) (chainCount F.lay)) => RawFam.seedOfF (S.stride F.lay) K c)]
  conv_rhs => rw [show PMF.uniformOfFintype (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) = PMF.uniformOfFintype
    ((((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest → Digest) × ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest)) ×
      ((Fin (RawPrefix.restDepth a R) → Digest → Digest) × (Fin (RawPrefix.restDepth a R) → Digest))) from rfl, uniform_prod_bind]
  congr 1
  funext gl
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext s
  rw [uniform_program (fun i : Fin (RawPrefix.restDepth a R) => if i.val = 0 then s else 0)]
  congr 1
  funext q
  have ht : (fun i : Fin (RawPrefix.restDepth a R) => Function.update (q.1 i) (if i.val = 0 then s else 0) (q.2 i)) =
      tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) s := rfl
  have he : evaluate (tYF (RawPrefix.restDepth a R) (mkPF (gl, q) 0) s) s = ePF (gl, q) := evaluate_tYF hd1 _ _
  rw [ht, he]
  unfold Core.gameD
  have hp := mix_pointF hU S hF htb ca haF R hd1 GD hG aF haca K (gl, q) s
  exact congrArg (PMF.map _) hp
end Decomp

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF

open ClaudeWCT.Arith.SideChannel (tdepth prT amLen)
section PerR
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : (GChainW (S.grp F.lay) (chainCount F.lay)))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ (RawPrefix.restDepth a R))
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)

include hGq in
theorem tdepth_testRunF (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (r : (GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) :
    tdepth (testRunF hU GD aF p r) ≤ q :=
  ClaudeWCT.Arith.SideChannel.tdepth_simulate_le _ RefCharged
    (fun qu s => FamTest.tdepth_testImplF (F := F) (a := a) (TstF hU S F a R p r) aF _ qu s) _ q _ (hGq _)

/-- The per-rest-table error of the family restart: `2 δ K(q) E_{p,K}[amLen]`. -/
noncomputable def errRF : ℝ :=
  ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K : Fin (S.size F.lay F.fam) → Digest,
    (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ * ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
      (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        amLen (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))))

variable (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
include hF htb haF hd1 hG haca hGq C hws hb

theorem frozen_le_mix_RF (E : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam) → Digest × (Res × TObs (RawPrefix.restDepth a R)) → Prop)
    (hE : ∀ (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (K K' : Fin (S.size F.lay F.fam) → Digest),
      seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' →
        E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) = E (K', RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K')) :
    Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] ≤
      Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] +
        ENNReal.ofReal (errRF hU (a := a) R GD aF q) := by
  rw [frozen_decompYF hU S hF htb ca haF R hd1 GD hG aF haca, mix_decompYF hU S hF htb ca haF R hd1 GD hG aF haca]
  set A : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R) → ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) → (Res × TObs (RawPrefix.restDepth a R)) → Prop :=
    fun p r res => E (KstF S F R r, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R r)) (ePF p, res) with hAdef
  have hA : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      (fun res => E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) (ePF p, res)) = A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) := by
    intro K p
    funext res
    simp only [hAdef]
    rw [hE p K _ (seedsR_KstF S F R K).symm]
  simp only [prob_uniform_bind, prob_pmf_map, Function.comp_def]
  simp only [prob_evalT]
  simp only [hA]
  have hRev : ((RawFam.revSetF S F R)).card + 3 ≤ S.size F.lay F.fam := revSetF_card_le C F R
  have hpt : Function.Injective (gptS (S.stride F.lay) (g := S.grp F.lay) (w := chainCount F.lay)) :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_injective hws
  have hsmall : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), gptS (S.stride F.lay) c < 1024 := ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_lt hb
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
          (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
        ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
          prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
            (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) by
    simp only [sum_inv_ofReal _ (fun _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _)]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg (by positivity)
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))]
  set cK : ℝ := (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ with hcK
  set cp : ℝ := (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ with hcp
  set cD : ℝ := (Fintype.card Digest : ℝ)⁻¹ with hcD
  set Cc : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC
  set x := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hx
  set z := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (s : Digest) =>
    prT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hz
  set m := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    amLen (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hm
  have hcK0 : 0 ≤ cK := by positivity
  have hcp0 : 0 ≤ cp := by positivity
  have hcD0 : 0 ≤ cD := by positivity
  have hz0 : ∀ K p s, 0 ≤ z K p s := fun _ _ _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s)) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) by
    have h1 : ∀ K p, ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s) =
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) := fun K p => sum_inv_ofReal (z K p) (hz0 K p)
    simp only [h1]
    have h2 : ∀ K, ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) =
        ENNReal.ofReal (∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) := fun K =>
      sum_inv_ofReal (fun p => ∑ s : Digest, cD * z K p s)
        (fun p => Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s))
    simp only [h2]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))]
  have hY : 0 ≤ ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s :=
    Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))
  have hZ : 0 ≤ errRF hU (a := a) R GD aF q := by
    unfold errRF
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (mul_nonneg hcp0 ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
      (Nat.cast_nonneg _)) (ClaudeWCT.Arith.SideChannel.amLen_nonneg _)
  rw [← ENNReal.ofReal_add hY hZ]
  apply ENNReal.ofReal_le_ofReal
  have key : ∀ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K, x K p ≤
      ∑ K, (∑ s, z K p s) / Fintype.card Digest + Cc * ∑ K, m K p := fun p =>
    ClaudeWCT.Arith.SideChannel.family_test_le hpt hsmall hRev aF (A p)
      (fun r => testRunF hU GD aF p r) q (fun r => tdepth_testRunF hU R GD aF q hGq p r)
  have e1 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * x K p =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, x K p := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, (∑ s, z K p s) / Fintype.card Digest := by
    simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun s _ => by
      rw [hcD]; ring
  have e3 : errRF hU (a := a) R GD aF q = ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * (Cc * ∑ K, m K p) := by
    unfold errRF
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by rw [hcK, hcp, hC]; ring
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (key p) (mul_nonneg hcK0 hcp0)

theorem mix_le_frozen_RF (E : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam) → Digest × (Res × TObs (RawPrefix.restDepth a R)) → Prop)
    (hE : ∀ (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (K K' : Fin (S.size F.lay F.fam) → Digest),
      seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' →
        E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) = E (K', RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K')) :
    Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.mixLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] ≤
      Pr[fun w => E w.1 w.2 | (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => (Core.frozenLaw hU a (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) GD).map (fun z => (y, z)))] +
        ENNReal.ofReal (errRF hU (a := a) R GD aF q) := by
  rw [frozen_decompYF hU S hF htb ca haF R hd1 GD hG aF haca, mix_decompYF hU S hF htb ca haF R hd1 GD hG aF haca]
  set A : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R) → ((GChainW (S.grp F.lay) (chainCount F.lay)) → Digest) → (Res × TObs (RawPrefix.restDepth a R)) → Prop :=
    fun p r res => E (KstF S F R r, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 (KstF S F R r)) (ePF p, res) with hAdef
  have hA : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      (fun res => E (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K) (ePF p, res)) = A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) := by
    intro K p
    funext res
    simp only [hAdef]
    rw [hE p K _ (seedsR_KstF S F R K).symm]
  simp only [prob_uniform_bind, prob_pmf_map, Function.comp_def]
  simp only [prob_evalT]
  simp only [hA]
  have hRev : ((RawFam.revSetF S F R)).card + 3 ≤ S.size F.lay F.fam := revSetF_card_le C F R
  have hpt : Function.Injective (gptS (S.stride F.lay) (g := S.grp F.lay) (w := chainCount F.lay)) :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_injective hws
  have hsmall : ∀ c : (GChainW (S.grp F.lay) (chainCount F.lay)), gptS (S.stride F.lay) c < 1024 := ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_lt hb
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
          (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
        ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
          prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
            (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) by
    simp only [sum_inv_ofReal _ (fun _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _)]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg (by positivity)
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))]
  set cK : ℝ := (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ with hcK
  set cp : ℝ := (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ with hcp
  set cD : ℝ := (Fintype.card Digest : ℝ)⁻¹ with hcD
  set Cc : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC
  set x := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    prT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hx
  set z := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) (s : Digest) =>
    prT (seedsH (gptS (S.stride F.lay)) (RawFam.revSetF S F R) aF K s) (A p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))
      (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hz
  set m := fun (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) =>
    amLen (testRunF hU GD aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) with hm
  have hcK0 : 0 ≤ cK := by positivity
  have hcp0 : 0 ≤ cp := by positivity
  have hcD0 : 0 ≤ cD := by positivity
  have hz0 : ∀ K p s, 0 ≤ z K p s := fun _ _ _ => ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _
  rw [show (∑ K : Fin (S.size F.lay F.fam) → Digest, (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ≥0∞)⁻¹ *
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s)) =
      ENNReal.ofReal (∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) by
    have h1 : ∀ K p, ∑ s : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (z K p s) =
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) := fun K p => sum_inv_ofReal (z K p) (hz0 K p)
    simp only [h1]
    have h2 : ∀ K, ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ s : Digest, cD * z K p s) =
        ENNReal.ofReal (∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s) := fun K =>
      sum_inv_ofReal (fun p => ∑ s : Digest, cD * z K p s)
        (fun p => Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s))
    simp only [h2]
    exact sum_inv_ofReal _ (fun K => Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (Finset.sum_nonneg fun s _ => mul_nonneg hcD0 (hz0 K p s)))]
  have hY : 0 ≤ ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * x K p :=
    Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (Finset.sum_nonneg fun p _ => mul_nonneg hcp0
      (ClaudeWCT.Arith.SideChannel.prT_nonneg _ _ _))
  have hZ : 0 ≤ errRF hU (a := a) R GD aF q := by
    unfold errRF
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun K _ => mul_nonneg hcK0 (mul_nonneg hcp0 ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
      (Nat.cast_nonneg _)) (ClaudeWCT.Arith.SideChannel.amLen_nonneg _)
  rw [← ENNReal.ofReal_add hY hZ]
  apply ENNReal.ofReal_le_ofReal
  have key : ∀ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K, (∑ s, z K p s) / Fintype.card Digest ≤
      ∑ K, x K p + Cc * ∑ K, m K p := fun p =>
    ClaudeWCT.Arith.SideChannel.family_test_ge hpt hsmall hRev aF (A p)
      (fun r => testRunF hU GD aF p r) q (fun r => tdepth_testRunF hU R GD aF q hGq p r)
  have e1 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * x K p =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, x K p := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), cp * ∑ s : Digest, cD * z K p s =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * ∑ K, (∑ s, z K p s) / Fintype.card Digest := by
    simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun s _ => by
      rw [hcD]; ring
  have e3 : errRF hU (a := a) R GD aF q = ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) * (Cc * ∑ K, m K p) := by
    unfold errRF
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by rw [hcK, hcp, hC]; ring
  rw [e2, e1, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (key p) (mul_nonneg hcK0 hcp0)

end PerR

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamCore
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamSum1 ====
section

/-! # Family restart, step P5a: family test counts and their allocation (r3-lean-seedfam)

Family analogues of `Normalized.Core.{StepZeroUnrev, NL, isTestQ_iff, NL_mkSample, sum_NL_le}` (WotsLeafSum):
a test query of family `F` is a step-0 row of one of its unrevealed chains (phantom chains of a short last family are
always unrevealed); every trace entry is a test query of at most one family, and is charged to the source chains of
that family only, at most `grp · chainCount` of them (`sum_NL_leF`: today `54`, v6 `max(4·54, 7·43) = 301`).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized (depth_eq)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SphincsSecurity.QueryCap (recorded counted calls)
open SigGolfCandidate.T3.Security.Wots.Mask (chainCount_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable (S : FamScheme)

/-- The family of a leaf. -/
def famOf (L : LeafAddr) : FamAddr := ⟨L.lay, L.tree, L.leaf / S.grp L.lay⟩

/-- Member `l` of `F` is a real (in-tree) leaf. -/
def RealM (F : FamAddr) (l : Nat) : Prop := S.grp F.lay * F.fam + l < 2 ^ height F.lay

/-- `input` is the step-0 row of an unrevealed chain of family `F` in `T` (phantom chains count as unrevealed). -/
def StepZeroUnrevF (F : FamAddr) (T : Answers) (input : HashInput) : Prop :=
  ∃ c : GChainW (S.grp F.lay) (chainCount F.lay),
    (¬RealM S F c.1.val ∨ CanonicalRef.depth T (sourceMessages T) (chainOfF (S.grp F.lay) (chainCount F.lay) F c) ≠ 0) ∧
      ∃ v, input = chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v

/-- Number of test queries of family `F` in a reference sample. -/
noncomputable def NLF (F : FamAddr) (s : RefSample) : ℕ :=
  (s.trace.filter fun e => decide (StepZeroUnrevF S F s.answers e.1)).length

/-- Test count charged to chain `a`: its family's. -/
noncomputable def NLaF (a : ChainAddr) (s : RefSample) : ℕ := NLF S (famOf S a.key) s

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

theorem zeroOfF_none_ne {g w b n : Nat} {F : FamAddr} (hF : FamOk g w b n F) {input : HashInput}
    (h : zeroOfF g w F input = none) (c : GChainW g w) (v : Digest) : input ≠ chainRowW (chainOfF g w F c) 0 v := by
  rintro rfl
  rw [zeroOfF_chainRow hF] at h
  cases h

theorem isTestQF_iff {F : FamAddr} (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (T : Answers)
    (hT : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), RealM S F c.1.val →
      CanonicalRef.depth T (sourceMessages T) (chainOfF (S.grp F.lay) (chainCount F.lay) F c) =
        CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c))
    (hreal : RealM S F ca.1.val) (query : RefWorld.Domain) :
    isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (revSetF S F R) query ↔
      ∃ x, query = .inl (.inr x) ∧ StepZeroUnrevF S F T x := by
  have hda : CanonicalRef.depth (raw R) zeroMessages a = RawPrefix.restDepth a R := (RawPrefix.restDepth_eq a R).symm
  have hw := hF.width
  rcases query with (k | input) | u
  · simp [isTestQF]
  · simp only [isTestQF, Sum.inl.injEq, Sum.inr.injEq, exists_eq_left']
    unfold StepZeroUnrevF
    cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
    | some p =>
        have hin := PrefixGame.rowOf_some hp
        simp only
        constructor
        · intro h0
          refine ⟨ca, Or.inr ?_, p.2, ?_⟩
          · rw [hT ca hreal, ← haF, hda]
            have := p.1.isLt
            omega
          · rw [hin, ← haF, show p.1.val = 0 from h0]
        · rintro ⟨c, -, v, he⟩
          rw [hin] at he
          have h1 : (p.1 : ℕ) < 256 := by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega
          have hc1 := c.2.isLt
          have hca1 := ca.2.isLt
          obtain ⟨-, -, hs, -⟩ := chainInputW_eq_chainRowW (a := chainOfF (S.grp F.lay) (chainCount F.lay) F c)
            (by subst haF; unfold chainOfF; simp only; omega) (by unfold chainOfF; simp only; omega) h1 (by omega) he
          exact hs
    | none =>
        simp only
        cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
        | none =>
            simp only [false_iff, not_exists, not_and]
            intro c _ v he
            exact zeroOfF_none_ne hF hz c v he
        | some cv =>
            simp only
            have he := zeroOfF_some hz
            constructor
            · intro hc
              refine ⟨cv.1, ?_, cv.2, he⟩
              by_cases hr : RealM S F cv.1.1.val
              · right
                rw [hT cv.1 hr]
                intro h0
                apply hc
                unfold revSetF
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hr, h0⟩
              · exact Or.inl hr
            · rintro ⟨c, hc, v, he'⟩
              rw [he] at he'
              obtain ⟨h1, -⟩ := chainRowF_zero_inj hF he'
              subst h1
              unfold revSetF
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
              intro hr h0
              rcases hc with hc | hc
              · exact hc hr
              · exact hc (by rw [hT cv.1 hr]; exact h0)
  · simp [isTestQF]

include hU in
theorem NL_mkSampleF {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
    {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (hreal : RealM S F ca.1.val)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) (run : SeedResult) :
    NLF S F (mkSample (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) run) =
      calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (revSetF S F R)) run.2 := by
  unfold NLF mkSample
  simp only
  rw [traceOf_filter_length]
  have hT : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), RealM S F c.1.val →
      CanonicalRef.depth (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
        (sourceMessages (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
          (chainOfF (S.grp F.lay) (chainCount F.lay) F c) =
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) := by
    intro c hc
    rw [depth_eq hU _ _ (sourceLeaf_memF S htb c.1 hc), RawPrefix.depth_ov a (by have := RawPrefix.restDepth_le a R; omega)]
  congr 1
  funext query
  exact propext (isTestQF_iff S hF ca haF R _ hT hreal query).symm

/-- Step-0 rows determine their family (families of source leaves; trees below `2^40`, leaves below `2^32`). -/
theorem stepZero_fam_unique (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {L L' : LeafAddr}
    (hL : WotsExtract.SourceLeaf L) (hL' : WotsExtract.SourceLeaf L') {T T' : Answers} {input : HashInput}
    (h : StepZeroUnrevF S (famOf S L) T input) (h' : StepZeroUnrevF S (famOf S L') T' input) :
    famOf S L = famOf S L' := by
  obtain ⟨c, -, v, rfl⟩ := h
  obtain ⟨c', -, v', he⟩ := h'
  have hb : ∀ K : LeafAddr, WotsExtract.SourceLeaf K → K.tree < 2 ^ 40 ∧ K.leaf < 2 ^ 12 := fun K hK => by
    refine ⟨by have := hK.1; omega, ?_⟩
    have h1 := hK.2
    have h2 : 2 ^ height K.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3.Security.Wots.height_le K.lay)
    omega
  have hmem : ∀ (K : LeafAddr) (l : Fin (S.grp K.lay)), WotsExtract.SourceLeaf K →
      S.grp K.lay * (K.leaf / S.grp K.lay) + l.val < 2 ^ 32 := by
    intro K l hK
    have := (hb K hK).2; have := l.isLt; have := hgrp K.lay
    have : S.grp K.lay * (K.leaf / S.grp K.lay) ≤ K.leaf := Nat.mul_div_le _ _
    omega
  have hc1 := c.2.isLt; have hc2 := c'.2.isLt
  have hw1 := chainCount_le (famOf S L).lay; have hw2 := chainCount_le (famOf S L').lay
  obtain ⟨hal, -, -, -⟩ := chainInputW_eq_chainRowW (a := chainOfF _ _ (famOf S L') c')
    (by unfold chainOfF; simp only [Nat.reducePow]; omega) (by unfold chainOfF; simp only [Nat.reducePow]; omega)
    (by omega) (by omega) he
  have hE := hal.eq_of_lt (show L.tree < 2 ^ 40 from (hb L hL).1)
    (show S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val < 2 ^ 32 from hmem L c.1 hL)
    (show L'.tree < 2 ^ 40 from (hb L' hL').1)
    (show S.grp L'.lay * (L'.leaf / S.grp L'.lay) + c'.1.val < 2 ^ 32 from hmem L' c'.1 hL')
  have hlay : L.lay = L'.lay := by have h0 := congrArg LeafAddr.lay hE; exact h0
  have htree : L.tree = L'.tree := by have h0 := congrArg LeafAddr.tree hE; exact h0
  have hleaf : S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val =
      S.grp L'.lay * (L'.leaf / S.grp L'.lay) + c'.1.val := by have h0 := congrArg LeafAddr.leaf hE; exact h0
  rw [← hlay] at hleaf
  have hg := S.grp_pos L.lay
  have hc : c.1.val < S.grp L.lay := c.1.isLt
  have hc' : c'.1.val < S.grp L.lay := by
    have h := c'.1.isLt
    have hgg : S.grp (famOf S L').lay = S.grp L.lay := by show S.grp L'.lay = S.grp L.lay; rw [hlay]
    omega
  have e1 : (S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val) / S.grp L.lay = L.leaf / S.grp L.lay := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e2 : (S.grp L.lay * (L'.leaf / S.grp L.lay) + c'.1.val) / S.grp L.lay = L'.leaf / S.grp L.lay := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hc', Nat.zero_add]
  have hfam : L.leaf / S.grp L.lay = L'.leaf / S.grp L'.lay := by
    rw [← hlay, ← e1, ← e2, hleaf]
  unfold famOf
  rw [hfam, hlay, htree]

/-- Source chains of one family: at most `grp · chainCount`. -/
theorem card_famChains_le (F : FamAddr) :
    (SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => famOf S a.key = F).card ≤
      S.grp F.lay * chainCount F.lay := by
  classical
  have hinj : ∀ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains.filter (fun a => famOf S a.key = F),
      ∀ a' ∈ SigGolfCandidate.T3.Security.Wots.sourceChains.filter (fun a => famOf S a.key = F),
      ((a.key.leaf % S.grp F.lay, a.chain) : Nat × Nat) = (a'.key.leaf % S.grp F.lay, a'.chain) → a = a' := by
    intro a ha a' ha' he
    simp only [Finset.mem_filter] at ha ha'
    have h1 := congrArg FamAddr.lay ha.2; have h2 := congrArg FamAddr.tree ha.2; have h3 := congrArg FamAddr.fam ha.2
    have h1' := congrArg FamAddr.lay ha'.2; have h2' := congrArg FamAddr.tree ha'.2
    have h3' := congrArg FamAddr.fam ha'.2
    unfold famOf at h1 h2 h3 h1' h2' h3'
    simp only at h1 h2 h3 h1' h2' h3'
    simp only [Prod.mk.injEq] at he
    have e1 : a.key.leaf = S.grp F.lay * F.fam + a.key.leaf % S.grp F.lay := by
      rw [← h1, ← h3]; exact (Nat.div_add_mod _ _).symm
    have e2 : a'.key.leaf = S.grp F.lay * F.fam + a'.key.leaf % S.grp F.lay := by
      rw [← h1', ← h3']; exact (Nat.div_add_mod _ _).symm
    have hl : a.key.leaf = a'.key.leaf := by rw [e1, e2, he.1]
    have hk : a.key = a'.key := by
      cases ha0 : a.key; cases ha0' : a'.key
      rw [ha0] at h1 h2 hl; rw [ha0'] at h1' h2' hl
      simp only at h1 h2 hl h1' h2'
      rw [h1, ← h1', h2, ← h2', hl]
    cases a; cases a'
    simp only at hk he
    rw [hk, he.2]
  calc (SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => famOf S a.key = F).card
      ≤ ((Finset.range (S.grp F.lay)) ×ˢ (Finset.range (chainCount F.lay))).card := by
        apply Finset.card_le_card_of_injOn (fun a => (a.key.leaf % S.grp F.lay, a.chain))
        · intro a ha
          simp only [Finset.mem_filter, Finset.coe_filter, Set.mem_setOf_eq] at ha
          have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp ha.1
          have h1 := congrArg FamAddr.lay ha.2
          unfold famOf at h1; simp only at h1
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          exact ⟨Nat.mod_lt _ (S.grp_pos _), h1 ▸ hs.2⟩
        · intro a ha a' ha' he
          exact hinj a (by simpa using ha) a' (by simpa using ha') he
    _ = S.grp F.lay * chainCount F.lay := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- **Per-sample allocation:** every trace entry is a test of at most one family, charged to at most `Cmax` source
chains (`Cmax ≥ grp · chainCount` on every layer). -/
theorem sum_NL_leF (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : Nat) (hC : ∀ lay, S.grp lay * chainCount lay ≤ Cmax)
    (s : RefSample) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLaF S a s ≤ Cmax * s.trace.length := by
  classical
  let test : FamAddr → Entry → Prop := fun F e =>
    StepZeroUnrevF S F s.answers e.1 ∧ ∃ L, WotsExtract.SourceLeaf L ∧ famOf S L = F
  have hcongr : ∀ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLaF S a s =
      (s.trace.filter fun e => decide (test (famOf S a.key) e)).length := by
    intro a ha
    have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp ha
    unfold NLaF NLF
    congr 1
    apply List.filter_congr
    intro e _
    simp only [test, decide_eq_decide]
    exact ⟨fun h => ⟨h, a.key, hs.1, rfl⟩, fun h => h.1⟩
  rw [Finset.sum_congr rfl hcongr]
  exact ClaudeWCT.Arith.SideChannel.GroupedFamily.sum_charge_le SigGolfCandidate.T3.Security.Wots.sourceChains
    (fun a => famOf S a.key) test Cmax
    (fun e F F' h h' => by
      obtain ⟨h1, L, hL, rfl⟩ := h
      obtain ⟨h1', L', hL', rfl⟩ := h'
      exact stepZero_fam_unique S hgrp hL hL' h1 h1')
    (fun F => (card_famChains_le S F).trans (hC F.lay)) s.trace

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamLift ====
section

/-! # Family restart, steps P4c/P5b: the lift over the rest tables and the seed-error charge (r3-lean-seedfam)

Family port of `WotsLeafLift` (normalized part: `selfF`, `errAR`, `restLaw_resampleL_tsum`, `resample_ind`,
`frozen_le_mix`, `mix_le_frozen`) and of the normalized charge of `WotsLeafSum` (`enT_testRun_rec`, `tcount`,
`errR_le_count`, `count_frozen`, `frozenCount`, `errAR_sum_le`, `reference_map_NL`, `frozenCount_eq`, `errC`,
`errC_le`, `errC_sum_le`). The leaf `L` becomes a family `F` of a scheme `S`, chain `a = chainOfF ca`, the leaf
resampling becomes `RawFam.restLaw_resampleF`, and the per-leaf allocation `54` becomes `Cmax ≥ grp · chainCount`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype

/-- The chain `a = chainOfF ca` as an unrevealed chain of its family (depth `≥ 1`). -/
def selfFF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U)
    (hd1 : 1 ≤ RawPrefix.restDepth a R) : Free (RawFam.revSetF S F R) :=
  ⟨ca, by
    simp only [RawFam.revSetF, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro _ h
    rw [RawPrefix.restDepth_eq, haF] at hd1
    omega⟩

/-- Per rest table error of the family restart (zero at depth `0`). -/
noncomputable def errARF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) {Res : Type}
    (GD : Answers → OracleComp RefWorld Res) (q : ℕ) (R : Tables U) : ℝ≥0∞ :=
  if hd1 : 1 ≤ RawPrefix.restDepth a R then
    ENNReal.ofReal (FamCore.errRF hU (a := a) R GD (selfFF S ca haF R hd1) q) else 0

include hU in
theorem restLaw_resampleF_tsum {g w b n : Nat} {F : FamAddr} (hF : RawFam.FamOk g w b n F)
    (Φ : Tables U → ℝ≥0∞) :
    ∑' R, Core.restLaw U R * Φ R =
      ∑' R, Core.restLaw U R * ∑' y, PMF.uniformOfFintype (FamData g w n) y * Φ (RawFam.ovF g w b n F R y) := by
  unfold Core.restLaw
  have h := RawFam.restLaw_resampleF hU hF (fun R => PMF.pure R)
  simp only [PMF.bind_pure] at h
  conv_lhs => rw [h]
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  congr 1
  funext R
  congr 1
  rw [show (PMF.uniformOfFintype (FamData g w n)).bind (fun y => PMF.pure (RawFam.ovF g w b n F R y)) =
    (PMF.uniformOfFintype (FamData g w n)).map (RawFam.ovF g w b n F R) from rfl,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]

theorem revSetF_ovF (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) :
    RawFam.revSetF S F (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) =
      RawFam.revSetF S F R := by
  unfold RawFam.revSetF
  congr 1
  funext c
  rw [RawFam.depth_ovF S hF R y]

section Lift
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → GD T' = GD T)
  (q : ℕ) (hGq : ∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
  (E : (d : ℕ) → Tables U → Digest × (Res × TObs d) → Prop)
  (hE : ∀ (R : Tables U) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
      (K K' : Fin (S.size F.lay F.fam) → Digest),
    seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K = seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K' →
      E (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K, RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K)) =
        E (RawPrefix.restDepth a R) (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R
          (K', RawFam.progFF (S.stride F.lay) p.1.1 p.1.2 K')))
  (hE0 : ∀ R z, ¬E 0 R z)

include hU hF in
/-- Resampling the family data, the event and the law at the resampled table. -/
theorem resample_indF (Law : (d : ℕ) → Tables U → PMF (Digest × (Res × TObs d))) :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Law (RawPrefix.restDepth a R) R] =
      ∑' R, Core.restLaw U R * Pr[fun w => E (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R w.1) w.2 |
        (PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
          (fun y => (Law (RawPrefix.restDepth a R)
            (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)).map
              (fun z => (y, z)))] := by
  rw [restLaw_resampleF_tsum hU hF (fun R => Pr[E (RawPrefix.restDepth a R) R | Law (RawPrefix.restDepth a R) R])]
  refine tsum_congr fun R => ?_
  congr 1
  rw [prob_bind]
  refine tsum_congr fun y => ?_
  congr 1
  rw [prob_pmf_map, RawFam.restDepth_ovF S hF R y a]
  rfl

include hU hF htb haF hG hGq C hws hb hE hE0

/-- **Frozen ≤ mixture + error** (family version). -/
theorem frozen_le_mixF :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD] ≤
      ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.mixLaw hU a (RawPrefix.restDepth a R) R GD] +
        ∑' R, Core.restLaw U R * errARF hU S ca haF GD q R := by
  rw [resample_indF hU S hF (a := a) E (fun d R => Core.frozenLaw hU a d R GD),
    resample_indF hU S hF (a := a) E (fun d R => Core.mixLaw hU a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ RawPrefix.restDepth a R
  · unfold errARF
    rw [dif_pos hd1]
    exact FamCore.frozen_le_mix_RF hU hF htb ca haF R hd1 GD hG (selfFF S ca haF R hd1) rfl q hGq C hws hb
      (fun y z => E (RawPrefix.restDepth a R)
        (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun p K K' h => hE R p K K' h)
  · have h0 : RawPrefix.restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : Tables U) (z : Digest × (Res × TObs d)), ¬E d R' z := by
      intro d hd
      subst hd
      exact hE0
    rw [Core.prob_zero_of_depth h0 (fun y z => E (RawPrefix.restDepth a R)
      (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun w => hF0' _ h0 _ w.2)]
    exact bot_le

/-- **Mixture ≤ frozen + error** (family version). -/
theorem mix_le_frozenF :
    ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.mixLaw hU a (RawPrefix.restDepth a R) R GD] ≤
      ∑' R, Core.restLaw U R * Pr[E (RawPrefix.restDepth a R) R | Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD] +
        ∑' R, Core.restLaw U R * errARF hU S ca haF GD q R := by
  rw [resample_indF hU S hF (a := a) E (fun d R => Core.frozenLaw hU a d R GD),
    resample_indF hU S hF (a := a) E (fun d R => Core.mixLaw hU a d R GD), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  by_cases hd1 : 1 ≤ RawPrefix.restDepth a R
  · unfold errARF
    rw [dif_pos hd1]
    exact FamCore.mix_le_frozen_RF hU hF htb ca haF R hd1 GD hG (selfFF S ca haF R hd1) rfl q hGq C hws hb
      (fun y z => E (RawPrefix.restDepth a R)
        (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun p K K' h => hE R p K K' h)
  · have h0 : RawPrefix.restDepth a R = 0 := by omega
    have hF0' : ∀ (d : ℕ), d = 0 → ∀ (R' : Tables U) (z : Digest × (Res × TObs d)), ¬E d R' z := by
      intro d hd
      subst hd
      exact hE0
    rw [Core.prob_zero_of_depth h0 (fun y z => E (RawPrefix.restDepth a R)
      (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) z)
      (fun w => hF0' _ h0 _ w.2)]
    exact bot_le
end Lift

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open ClaudeWCT.Arith.SideChannel (exT enT amLen tdepth)
open SphincsSecurity.QueryCap (recorded counted calls)

/-- Expected number of tests = expected number of test queries in the recorded list (family version). -/
theorem enT_testRun_recF {S : FamScheme} {F : FamAddr} {a : ChainAddr} {R : Tables U} {Res : Type}
    (G0 : Answers → OracleComp RefWorld Res) (aF : Free (RawFam.revSetF S F R))
    (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
    (r : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) (y : Free (RawFam.revSetF S F R) → Digest) :
    enT y (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) =
      exT y (fun out => (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
          (RawFam.revSetF S F R)) out.1.2 : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) := by
  unfold FamCore.testRunF
  rw [enT_simulate y _ (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R))
      (fun q s => FamTest.enT_testImplF (F := F) (a := a) (FamCore.TstF hU S F a R p r) aF _ y q s),
    counted_recorded, simulateQ_map, StateT.run_map, exT_map']
  rfl

section ErrR
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
  {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → recorded (G0 T') = recorded (G0 T))
  (aF : Free (RawFam.revSetF S F R)) (haca : aF.1 = ca) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)

/-- The family test-query count of a run. -/
noncomputable def tcountF (out : (Res × List RefWorld.Domain) × TObs (RawPrefix.restDepth a R)) : ℕ :=
  calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R)) out.1.2

include hGq C hws hb in
/-- **The family error is charged to the expected test count.** -/
theorem errR_le_countF :
    FamCore.errRF hU (a := a) R (fun T => recorded (G0 T)) aF q * (1 - (Fintype.card Digest : ℝ)⁻¹ * q) ≤
      2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q *
        ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), ∑ K : Fin (S.size F.lay F.fam) → Digest,
          (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
            ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
              exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
                (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
                (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
                  (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
  have hRev : (RawFam.revSetF S F R).card + 3 ≤ S.size F.lay F.fam := FamCore.revSetF_card_le C F R
  have hpt : Function.Injective (gptS (S.stride F.lay) (g := S.grp F.lay) (w := chainCount F.lay)) :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_injective hws
  have hsmall : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), gptS (S.stride F.lay) c < 1024 :=
    ClaudeWCT.Arith.SideChannel.GroupedFamily.gptS_lt hb
  set C' : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q with hC'
  set cK : ℝ := (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹
  set cp : ℝ := (Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹
  have hC0 : 0 ≤ C' := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3))
    (Nat.cast_nonneg _)
  have hcK : 0 ≤ cK := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcp : 0 ≤ cp := inv_nonneg.mpr (Nat.cast_nonneg _)
  have e1 : FamCore.errRF hU (a := a) R (fun T => recorded (G0 T)) aF q =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (C' * cK * cp) *
        ∑ K : Fin (S.size F.lay F.fam) → Digest, amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
          (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
    unfold FamCore.errRF
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => by ring
  have e2 : ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R),
      ∑ K : Fin (S.size F.lay F.fam) → Digest, cK * (cp *
        exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
          (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
          (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) =
      ∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R), (cK * cp) *
        ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun K _ => ?_
    rw [enT_testRun_recF]
    unfold tcountF
    ring
  rw [e1, e2, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hf := ClaudeWCT.Arith.SideChannel.family_amLen_le hpt hsmall hRev
    (fun r => FamCore.testRunF hU (fun T => recorded (G0 T)) aF p r) q
    (fun r => FamCore.tdepth_testRunF hU R (fun T => recorded (G0 T)) aF q hGq p r)
  calc C' * cK * cp * (∑ K : Fin (S.size F.lay F.fam) → Digest,
        amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) *
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)
      = C' * cK * cp * ((∑ K : Fin (S.size F.lay F.fam) → Digest,
          amLen (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) *
          (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) := by ring
    _ ≤ C' * cK * cp * ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) :=
        mul_le_mul_of_nonneg_left hf (mul_nonneg (mul_nonneg hC0 hcK) hcp)
    _ = C' * ((cK * cp) * ∑ K : Fin (S.size F.lay F.fam) → Digest,
          enT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
            (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
        ring

include hF htb haF hd1 hG haca in
/-- The expected test count of the decomposed frozen law (family version). -/
theorem count_frozenF :
    ENNReal.ofReal (∑ p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R),
        ∑ K : Fin (S.size F.lay F.fam) → Digest,
          (Fintype.card (Fin (S.size F.lay F.fam) → Digest) : ℝ)⁻¹ *
            ((Fintype.card (PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)) : ℝ)⁻¹ *
              exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
                (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
                (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p
                  (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)))) =
      ∑' z, ((PMF.uniformOfFintype (FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))).bind
        (fun y => Core.frozenLaw hU a (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)
          (fun T => recorded (G0 T)))) z *
          (tcountF (S := S) (F := F) (a := a) R z.2 : ℝ≥0∞) := by
  rw [FamCore.frozen_decompF hU S hF htb ca haF R hd1 (fun T => recorded (G0 T)) hG aF haca]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  have hx : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      ∑' out, evalT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) out *
          (tcountF (S := S) (F := F) (a := a) R out : ℝ≥0∞) =
      ENNReal.ofReal (exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K))) := by
    intro K p
    rw [ClaudeWCT.Arith.SideChannel.ofReal_exT _ (fun _ => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  simp only [hx, tsum_fintype, PMF.uniformOfFintype_apply]
  rw [Finset.sum_comm]
  have hnn : ∀ (K : Fin (S.size F.lay F.fam) → Digest) (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R)),
      0 ≤ exT (seedsY (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)
        (fun out => (tcountF (S := S) (F := F) (a := a) R out : ℝ))
        (FamCore.testRunF hU (fun T => recorded (G0 T)) aF p (seedsR (gptS (S.stride F.lay)) (RawFam.revSetF S F R) K)) :=
    fun K p => ClaudeWCT.Arith.SideChannel.exT_nonneg _ (fun _ => Nat.cast_nonneg _) _
  rw [ENNReal.ofReal_sum_of_nonneg (fun K _ => Finset.sum_nonneg fun p _ => mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hnn K p)))]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hnn K p))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)), ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
    ← inv_card_eq_ofReal, ← inv_card_eq_ofReal]
end ErrR

section Charge
variable {S : FamScheme} {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca)
  {Res : Type} (G0 : Answers → OracleComp RefWorld Res)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) F T T' → recorded (G0 T') = recorded (G0 T)) (q : ℕ)
  (hGq : ∀ T, OracleComp.IsQueryBoundP (recorded (G0 T)) RefCharged q)
  (C : FamCaps S) (hws : chainCount F.lay ≤ S.stride F.lay)
  (hb : (S.grp F.lay - 1) * S.stride F.lay + chainCount F.lay < 1024)
  (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1)

/-- The rest-table-averaged expected family test count of the frozen law. -/
noncomputable def frozenCountF (GD : Answers → OracleComp RefWorld (Res × List RefWorld.Domain)) : ℝ≥0∞ :=
  ∑' R, Core.restLaw U R * ∑' z, Core.frozenLaw hU a (RawPrefix.restDepth a R) R GD z *
    (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (RawFam.revSetF S F R)) z.2.1.2 : ℝ≥0∞)

include hF htb haF hG hGq C hws hb hq in
theorem errAR_sum_leF :
    ∑' R, Core.restLaw U R * errARF hU S ca haF (fun T => recorded (G0 T)) q R ≤
      ENNReal.ofReal (2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
        (1 - (Fintype.card Digest : ℝ)⁻¹ * q)) *
        frozenCountF hU (S := S) (F := F) (a := a) (fun T => recorded (G0 T)) := by
  set C' : ℝ := 2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * ClaudeWCT.Arith.SideChannel.kconst q /
    (1 - (Fintype.card Digest : ℝ)⁻¹ * q) with hC'
  have hpos : 0 < 1 - (Fintype.card Digest : ℝ)⁻¹ * q := by linarith
  let Ψd : ℕ → Tables U → ℝ≥0∞ := fun d R' =>
    ∑' z, Core.frozenLaw hU a d R' (fun T => recorded (G0 T)) z *
      (calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a d (RawFam.revSetF S F R')) z.2.1.2 : ℝ≥0∞)
  have hres := restLaw_resampleF_tsum hU hF (fun R => Ψd (RawPrefix.restDepth a R) R)
  unfold frozenCountF
  change _ ≤ ENNReal.ofReal C' * ∑' R, Core.restLaw U R * Ψd (RawPrefix.restDepth a R) R
  rw [hres, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun R => ?_
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  unfold errARF
  split_ifs with hd1
  · have hy : ∀ y, Ψd (RawPrefix.restDepth a
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y))
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) =
        ∑' z, Core.frozenLaw hU a (RawPrefix.restDepth a R)
          (RawFam.ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)
          (fun T => recorded (G0 T)) z * (tcountF (S := S) (F := F) (a := a) R z.2 : ℝ≥0∞) := by
      intro y
      rw [RawFam.restDepth_ovF S hF R y a]
      simp only [Ψd, revSetF_ovF S hF R y]
      rfl
    simp only [hy]
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind,
      ← count_frozenF hU hF htb ca haF R hd1 G0 hG (selfFF S ca haF R hd1) rfl]
    rw [← ENNReal.ofReal_mul (by
      rw [hC']; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr
        (Nat.cast_nonneg _)) 3)) (Nat.cast_nonneg _)) hpos.le)]
    apply ENNReal.ofReal_le_ofReal
    have h := errR_le_countF hU (a := a) R G0 (selfFF S ca haF R hd1) q hGq C hws hb
    rw [hC', div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact h
  · exact bot_le
end Charge

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

section Ref
variable (S : FamScheme) {F : FamAddr} (hF : FamOkS S F)
  (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
  {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (hreal : FamSum.RealM S F ca.1.val)

include hF htb haF hreal in
theorem reference_map_NLF (q : ℕ) (ha : WotsExtract.SourceChain7 a) :
    (PairedReference.referenceExperiment adversary q).map (FamSum.NLF S F) =
      (Core.restLaw (PairedReference.referenceInputs adversary)).bind (fun R =>
        (Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R (Core.GDseed adversary q)).map
          (fun z => calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
            (RawFam.revSetF S F R)) z.2.1.2)) := by
  rw [reference_map_eq_frozen adversary q a ha (FamSum.NLF S F)
    (fun R z => calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R)
      (RawFam.revSetF S F R)) z.2.1.2)
    (fun R x res _ => FamSum.NL_mkSampleF S (referenceInputs_subset adversary) hF htb ca haF hreal R x res.1)]
  change _ = (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind _
  apply congrArg (PMF.uniformOfFintype (Tables (PairedReference.referenceInputs adversary))).bind
  funext R
  unfold Core.frozenLaw
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp, Core.seedGame_eq_gameD]
  rfl

include hF htb haF hreal in
/-- **The frozen family count is the reference family count.** -/
theorem frozenCount_eqF (q : ℕ) (ha : WotsExtract.SourceChain7 a) :
    frozenCountF (referenceInputs_subset adversary) (S := S) (F := F) (a := a) (Core.GDseed adversary q) =
      ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLF S F s : ℝ≥0∞) := by
  have e1 : ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLF S F s : ℝ≥0∞) =
      ∑' n, ((PairedReference.referenceExperiment adversary q).map (FamSum.NLF S F)) n * (n : ℝ≥0∞) := by
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rw [e1, reference_map_NLF S hF htb ca haF hreal q ha,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind]
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  rfl
end Ref

/-- Family chain coordinates of a chain `a` in its family `famOf S a.key`: member `leaf % grp`, chain `a.chain`. -/
def caOf (S : FamScheme) (a : ChainAddr) (hac : a.chain < chainCount a.key.lay) :
    GChainW (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) :=
  (⟨a.key.leaf % S.grp a.key.lay, Nat.mod_lt _ (S.grp_pos _)⟩, ⟨a.chain, hac⟩)

theorem chainOf_caOf (S : FamScheme) (a : ChainAddr) (hac : a.chain < chainCount a.key.lay) :
    a = chainOfF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) (FamSum.famOf S a.key)
      (caOf S a hac) := by
  obtain ⟨⟨lay, tree, leaf⟩, c⟩ := a
  simp only [chainOfF, famLeaf, caOf, FamSum.famOf, Nat.div_add_mod]

theorem real_caOf (S : FamScheme) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) :
    FamSum.RealM S (FamSum.famOf S a.key) (caOf S a ha.2).1.val := by
  unfold FamSum.RealM
  show S.grp a.key.lay * (a.key.leaf / S.grp a.key.lay) + a.key.leaf % S.grp a.key.lay < 2 ^ height a.key.lay
  rw [Nat.div_add_mod]
  exact ha.1.2

/-- **Admissibility of the family of a source leaf** (group size at most `2^20`). -/
theorem famOk_of_source (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {L : LeafAddr}
    (hL : WotsExtract.SourceLeaf7 L) : FamOkS S (FamSum.famOf S L) := by
  have hleaf : L.leaf < 2 ^ 12 := by
    have h1 := hL.2
    have h2 : 2 ^ height L.lay ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3.Security.Wots.height_le L.lay)
    omega
  have hdiv : L.leaf / S.grp L.lay ≤ L.leaf := Nat.div_le_self _ _
  have hmd : S.grp L.lay * (L.leaf / S.grp L.lay) ≤ L.leaf := Nat.mul_div_le _ _
  have hg := hgrp L.lay
  have hcnt : S.cnt L.lay * (L.leaf / S.grp L.lay) ≤ 512 * 4096 :=
    Nat.mul_le_mul (S.cnt_le L.lay) (by omega)
  have hc := S.cnt_le L.lay
  refine ⟨S.grp_pos _, ?_, ?_, ?_, ?_, S.size_le _ _⟩
  · have := chainCount_le L.lay
    show chainCount L.lay < 2 ^ 24
    omega
  · show S.grp L.lay * (L.leaf / S.grp L.lay) + S.grp L.lay ≤ 2 ^ 24
    omega
  · show L.tree < 2 ^ 40
    have := hL.tree_lt
    omega
  · show S.cnt L.lay * (L.leaf / S.grp L.lay) + S.cnt L.lay ≤ 2 ^ 33
    omega

/-- The seed-game body is invariant under family congruence. -/
theorem GDseed_fam (S : FamScheme) {F : FamAddr} (hF : FamOkS S F) (q : ℕ) (T T' : Answers)
    (h : FamGame.FamCongr S (sourceMessages T) F T T') : Core.GDseed adversary q T' = Core.GDseed adversary q T := by
  unfold Core.GDseed
  rw [FamGame.referenceGame_fam h hF.tree hF.leaf adversary q]

/-- **The per-chain seed-test error of the family restart** (every source chain, charged to its family). -/
noncomputable def errCF (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ)
    (a : ChainAddr) : ℝ≥0∞ :=
  if h : WotsExtract.SourceChain7 a then
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
      errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (caOf S a h.2) (chainOf_caOf S a h.2)
        (Core.GDseed adversary q) q R
  else 0

theorem errC_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) (a : ChainAddr) :
    errCF S adversary q a ≤ ENNReal.ofReal (Core.errConst q) *
      ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) := by
  unfold errCF
  split_ifs with h
  · have hF := famOk_of_source S hgrp h.1
    unfold FamSum.NLaF
    rw [← frozenCount_eqF S hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2) (real_caOf S h) q h]
    exact errAR_sum_leF (referenceInputs_subset adversary) hF h.1.1 (caOf S a h.2) (chainOf_caOf S a h.2)
      (fun T => PairedReference.referenceGame T adversary q) (fun T T' h' => GDseed_fam S hF q T T' h') q
      (fun T => Core.GDseed_queryBound q T) C (hws _) (hb _) hq
  · exact bot_le

/-- **Total seed-test error of the family restart**: `Cmax ≥ grp · chainCount` on every layer. -/
theorem errC_sum_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : ℕ)
    (hC : ∀ lay, S.grp lay * chainCount lay ≤ Cmax) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) (hq : (Fintype.card Digest : ℝ)⁻¹ * q < 1) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errCF S adversary q a ≤
      ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
  calc ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, errCF S adversary q a
      ≤ ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, ENNReal.ofReal (Core.errConst q) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (FamSum.NLaF S a s : ℝ≥0∞) :=
        Finset.sum_le_sum fun a _ => errC_leF S hgrp C hws hb q hq a
    _ = ENNReal.ofReal (Core.errConst q) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine tsum_congr fun s => ?_
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
        refine mul_le_mul' le_rfl ?_
        calc ∑' s, PairedReference.referenceExperiment adversary q s *
              ((∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s : ℕ) : ℝ≥0∞)
            ≤ ∑' s, PairedReference.referenceExperiment adversary q s * ((Cmax : ℝ≥0∞) * q) := by
              refine ENNReal.tsum_le_tsum fun s => ?_
              by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
              · refine mul_le_mul' le_rfl ?_
                have h1 := FamSum.sum_NL_leF S hgrp Cmax hC s
                have h2 := Core.ref_trace_length_le adversary q s hs
                have : ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamSum.NLaF S a s ≤ Cmax * q := by
                  calc _ ≤ Cmax * s.trace.length := h1
                    _ ≤ Cmax * q := Nat.mul_le_mul_left Cmax h2
                exact_mod_cast this
              · rw [(PMF.apply_eq_zero_iff _ s).mpr hs, zero_mul, zero_mul]
          _ = (Cmax : ℝ≥0∞) * q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamLift
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamRestart1 ====
section

/-! # Family restart, step P5c-1: contacts and markers under family congruence (r3-lean-seedfam)

Family analogues of `Normalized.Restart.{frontierValue_leafCongr, contactAt_leafCongr, markerAt_leafCongr, fill_congr,
GDr_leaf}` (WotsLeafRestart): the honest events of every SOURCE chain are invariant under `FamGame.FamCongr`; a source
chain in the family is a real member (its leaf is in the tree). -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestartN
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart (source_bounds)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
variable {S : FamScheme} {F : FamAddr} {T T' : Answers}
  (hC : FamGame.FamCongr S (sourceMessages T) F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
  (hFtree : F.tree < 2 ^ 40)
include hC hF

include hFtree in
theorem frontierValue_famCongr {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    CanonicalRef.frontierValue T' (sourceMessages T') b = CanonicalRef.frontierValue T (sourceMessages T) b := by
  rw [FamGame.sourceMessages_congrF hC hF]
  obtain ⟨hbt, hbl⟩ := source_bounds hb
  by_cases hal : FamAlias S F b.key.lay b.key.tree b.key.leaf
  · obtain ⟨l, hla, hleq⟩ := famAlias_member S hal
    have hlt := famLeaf_lt S hF l
    have hk : b.key = famLeaf (S.grp F.lay) F l := by
      have := hla.eq_of_lt hbt (by omega) hFtree (by omega)
      cases hbk : b.key
      rw [hbk] at this
      exact this
    have hreal : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 := hb.1.2
      rw [hk] at h1
      exact h1
    have hbc : b.chain < chainCount F.lay := by have := hb.2; rwa [hal.1] at this
    cases b with
    | mk K c =>
      simp only at hk hbc
      subst hk
      exact hC.front l hreal c hbc
  · unfold CanonicalRef.frontierValue ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
    rw [FamGame.depth_congrF hC.toFamAgree b, wotsSeed_outF hC.toFamAgree (famBound_lt S hF) hbl hal]
    exact eval_chain_outF hC.toFamAgree hF hbl (by have := Mask.chainCount_le b.key.lay; have := hb.2; omega)
      (fun h => hal h.1) (by have := CanonicalRef.Mask.depth_le_seven T (sourceMessages T) b; omega) _

include hFtree in
theorem contactAt_famCongr (trace : List Entry) {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    CanonicalRef.ContactAt T' (sourceMessages T') trace b ↔ CanonicalRef.ContactAt T (sourceMessages T) trace b := by
  unfold CanonicalRef.ContactAt
  rw [FamGame.sourceMessages_congrF hC hF]
  rw [FamGame.depth_congrF hC.toFamAgree b]
  have hf := frontierValue_famCongr hC hF hFtree hb
  rw [FamGame.sourceMessages_congrF hC hF] at hf
  rw [hf]

theorem markerAt_famCongr (trace : List Entry) (b : ChainAddr) :
    CanonicalRef.MarkerAt T' (sourceMessages T') trace b ↔ CanonicalRef.MarkerAt T (sourceMessages T) trace b := by
  unfold CanonicalRef.MarkerAt CanonicalRef.referenceInput CanonicalRef.referenceDigits
  rw [FamGame.sourceMessages_congrF hC hF, FamGame.referenceSearch_congrF hC.toFamAgree]

end Congr

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestartN
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamRef ====
section

/-! # Family restart, steps P5c-2/3: reference against the mixture, prefix views (r3-lean-seedfam)

Family port of the normalized part of `WotsLeafRef` (`testRun_map`, `errR_map`, `errAR_map`, `errAR_GD`, `ref_hyps`,
`errC_eq`, `ref_prob_eq_frozen`, `ref_le_mix`, `mix_le_ref`) and of the normalized `WotsLeafView`
(`view_prob_le`, `view_prob_ge`, `view_count_le`). A source chain `a` is charged to its family `famOf S a.key`
(coordinates `caOf S a`), the per-chain error `Core.errC` becomes `FamLift.errCF`. The leaf-independent parts
(`Core.reference_map_eq_frozen_of`, `LeafView.reference_prob_view`, `LeafView.mixLaw_seed`, `LeafView.runView_eq`)
are reused.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open SphincsSecurity.QueryCap (recorded counted calls)

theorem testRun_mapF {S : FamScheme} {F : FamAddr} {a : ChainAddr} {R : Tables U} {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (RawFam.revSetF S F R))
    (p : PDataF (S.grp F.lay) (chainCount F.lay) (RawPrefix.restDepth a R))
    (r : GChainW (S.grp F.lay) (chainCount F.lay) → Digest) :
    FamCore.testRunF hU (fun T => out <$> GD T) aF p r =
      (fun x => (out x.1, x.2)) <$> FamCore.testRunF hU GD aF p r := by
  simp only [FamCore.testRunF, simulateQ_map, StateT.run_map]

theorem errR_mapF {S : FamScheme} {F : FamAddr} {a : ChainAddr} (R : Tables U) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (aF : Free (RawFam.revSetF S F R)) (q : ℕ) :
    FamCore.errRF hU (a := a) R (fun T => out <$> GD T) aF q = FamCore.errRF hU (a := a) R GD aF q := by
  unfold FamCore.errRF
  simp only [testRun_mapF, ClaudeWCT.W9.T3.Security.Wots.Leaf.amLen_map]

theorem errAR_mapF (S : FamScheme) {F : FamAddr} {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) {Res Res' : Type}
    (GD : Answers → OracleComp RefWorld Res) (out : Res → Res') (q : ℕ) (R : Tables U) :
    FamLift.errARF hU S ca haF (fun T => out <$> GD T) q R = FamLift.errARF hU S ca haF GD q R := by
  unfold FamLift.errARF
  split_ifs with hd1
  · rw [errR_mapF]
  · rfl

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
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
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawFam.ovF
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
noncomputable local instance : Fintype Coordinate := coordinateFintype
open SphincsSecurity.QueryCap (recorded counted calls)
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

section Ref
variable (S : FamScheme) (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  {Res : Type} (GD : Answers → OracleComp RefWorld Res) (out : Res → SeedResult)
  (hout : ∀ T, out <$> GD T = Core.GDseed adversary q T)

include ha hout in
theorem errAR_GDF (R : Tables (PairedReference.referenceInputs adversary)) :
    FamLift.errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (FamLift.caOf S a ha.2)
        (FamLift.chainOf_caOf S a ha.2) GD q R =
      FamLift.errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (FamLift.caOf S a ha.2)
        (FamLift.chainOf_caOf S a ha.2) (Core.GDseed adversary q) q R := by
  rw [← errAR_mapF (referenceInputs_subset adversary) S (FamLift.caOf S a ha.2) (FamLift.chainOf_caOf S a ha.2)
    GD out q R]
  rw [show (fun T => out <$> GD T) = Core.GDseed adversary q from funext hout]

include ha hout in
/-- Query bound of the refined body, admissibility and tree bound of the family of a source chain. -/
theorem ref_hypsF (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) :
    (∀ T, OracleComp.IsQueryBoundP (GD T) RefCharged q) ∧ FamOkS S (FamSum.famOf S a.key) ∧
      (FamSum.famOf S a.key).tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits (FamSum.famOf S a.key).lay := by
  refine ⟨fun T => ?_, FamLift.famOk_of_source S hgrp ha.1, ha.1.1⟩
  have h := Core.GDseed_queryBound (adversary := adversary) q T
  rw [← hout T, OracleComp.isQueryBoundP_map_iff] at h
  exact h

include ha hout in
theorem errC_eqF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        FamLift.errARF (referenceInputs_subset adversary) S (F := FamSum.famOf S a.key) (FamLift.caOf S a ha.2)
          (FamLift.chainOf_caOf S a ha.2) GD q R = FamLift.errCF S adversary q a := by
  unfold FamLift.errCF
  rw [dif_pos ha]
  simp only [errAR_GDF S q ha GD out hout]

variable (E : RefSample → Prop)
  (F : (d : ℕ) → Tables (PairedReference.referenceInputs adversary) → Digest × (Res × TObs d) → Prop)
  (hF : ∀ (R : Tables (PairedReference.referenceInputs adversary))
      (p : PDataF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay) (RawPrefix.restDepth a R))
      (K K' : Fin (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam) → Digest),
    seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K =
        seedsR (gptS (S.stride (FamSum.famOf S a.key).lay)) (RawFam.revSetF S (FamSum.famOf S a.key) R) K' →
      F (RawPrefix.restDepth a R) (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay)
          (S.cnt (FamSum.famOf S a.key).lay) (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam)
          (FamSum.famOf S a.key) R (K, RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K)) =
        F (RawPrefix.restDepth a R) (RawFam.ovF (S.grp (FamSum.famOf S a.key).lay) (chainCount (FamSum.famOf S a.key).lay)
          (S.cnt (FamSum.famOf S a.key).lay) (S.size (FamSum.famOf S a.key).lay (FamSum.famOf S a.key).fam)
          (FamSum.famOf S a.key) R (K', RawFam.progFF (S.stride (FamSum.famOf S a.key).lay) p.1.1 p.1.2 K')))
  (hF0 : ∀ R z, ¬F 0 R z)
  (hG : ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' → GD T' = GD T)
  (hEF : ∀ (R : Tables (PairedReference.referenceInputs adversary)) (x : Hidden (RawPrefix.restDepth a R))
      (res : Res × TObs (RawPrefix.restDepth a R)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (Core.gameD (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD
          (evaluate x.1 (RawPrefix.ovSeed a R x.2))) (fun _ _ => none)).support →
      (E (mkSample (answers (referenceInputs_subset adversary) (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
          (out res.1)) ↔
        F (RawPrefix.restDepth a R) R (evaluate x.1 (RawPrefix.ovSeed a R x.2), res)))
  (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)

include ha hout hEF in
theorem ref_prob_eq_frozenF :
    Pr[E | PairedReference.referenceExperiment adversary q] =
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[F (RawPrefix.restDepth a R) R |
          Core.frozenLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD] := by
  have h := congrArg (fun law : PMF Prop => Pr[fun p => p | law])
    (Core.reference_map_eq_frozen_of q ha GD out hout E (fun R z => F (RawPrefix.restDepth a R) R z)
      (fun R x res hres => propext (hEF R x res hres)))
  simp only [← PMF.monad_map_eq_map, probEvent_map, ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    PMF.probOutput_eq_apply, Function.comp_def] at h
  exact h

include ha hout hF hF0 hG hEF hgrp C hws hb

/-- **Reference ≤ mixture + error** (every source chain, charged to its family). -/
theorem ref_le_mixF :
    Pr[E | PairedReference.referenceExperiment adversary q] ≤
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[F (RawPrefix.restDepth a R) R |
          Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD] +
        FamLift.errCF S adversary q a := by
  obtain ⟨hGq, hFok, htb⟩ := ref_hypsF S q ha GD out hout hgrp
  rw [ref_prob_eq_frozenF q ha GD out hout E F hEF, ← errC_eqF S q ha GD out hout]
  exact FamLift.frozen_le_mixF (referenceInputs_subset adversary) S hFok htb (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) GD hG q hGq C (hws _) (hb _) F hF hF0

/-- **Mixture ≤ reference + error** (every source chain, charged to its family). -/
theorem mix_le_refF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        Pr[F (RawPrefix.restDepth a R) R |
          Core.mixLaw (referenceInputs_subset adversary) a (RawPrefix.restDepth a R) R GD] ≤
      Pr[E | PairedReference.referenceExperiment adversary q] + FamLift.errCF S adversary q a := by
  obtain ⟨hGq, hFok, htb⟩ := ref_hypsF S q ha GD out hout hgrp
  rw [ref_prob_eq_frozenF q ha GD out hout E F hEF, ← errC_eqF S q ha GD out hout]
  exact FamLift.mix_le_frozenF (referenceInputs_subset adversary) S hFok htb (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) GD hG q hGq C (hws _) (hb _) F hF hF0
end Ref

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun)
open SphincsSecurity.QueryCap (recorded counted calls)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
open ClaudeWCT.W9.T3.Security.Wots.Leaf (prob_pmf_map prob_bind runViewD)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers PairedReference.referenceGame PairedReference.offlineGame
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}

section View
variable (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
  (hws : ∀ lay, chainCount lay ≤ S.stride lay)
  (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
  (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a)
  (E : PrefixView → Prop) (hE0 : ∀ z : Digest × (SeedResult × ClaudeWCT.W9.T3.Security.Wots.Leaf.TObs 0),
    ¬E (runViewD a 0 z))
include hgrp C hws hb ha hE0

/-- **Prefix view, reference ≤ mixture + error** (family charge). -/
theorem view_prob_leF :
    Pr[fun s => E (sampleView a s) | PairedReference.referenceExperiment adversary q] ≤
      ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => E (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] +
        FamLift.errCF S adversary q a := by
  rw [LeafView.reference_prob_view q ha E]
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have h := FamLift.frozen_le_mixF (referenceInputs_subset adversary) S hFok ha.1.1 (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) (Core.GDseed adversary q) (fun T T' h' => FamLift.GDseed_fam S hFok q T T' h') q
    (Core.GDseed_queryBound q) C (hws _) (hb _) (fun d _ z => E (runViewD a d z)) (fun _ _ _ _ _ => rfl)
    (fun _ z => hE0 z)
  simpa only [LeafView.mixLaw_seed, ← LeafView.runView_eq, FamLift.errCF, dif_pos ha] using h

/-- **Prefix view, mixture ≤ reference + error** (family charge). -/
theorem view_prob_geF :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => E (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] ≤
      Pr[fun s => E (sampleView a s) | PairedReference.referenceExperiment adversary q] +
        FamLift.errCF S adversary q a := by
  rw [LeafView.reference_prob_view q ha E]
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  have h := FamLift.mix_le_frozenF (referenceInputs_subset adversary) S hFok ha.1.1 (FamLift.caOf S a ha.2)
    (FamLift.chainOf_caOf S a ha.2) (Core.GDseed adversary q) (fun T T' h' => FamLift.GDseed_fam S hFok q T T' h') q
    (Core.GDseed_queryBound q) C (hws _) (hb _) (fun d _ z => E (runViewD a d z)) (fun _ _ _ _ _ => rfl)
    (fun _ z => hE0 z)
  simpa only [LeafView.mixLaw_seed, ← LeafView.runView_eq, FamLift.errCF, dif_pos ha] using h
end View

/-- **Expected prefix counts, mixture ≤ reference + q · error** (family charge). -/
theorem view_count_leF (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (C : FamCaps S)
    (hws : ∀ lay, chainCount lay ≤ S.stride lay)
    (hb : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024)
    (q : ℕ) {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) :
    ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R)
          (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ℝ≥0∞) +
        q * FamLift.errCF S adversary q a := by
  have hmix : ∀ R : Tables (PairedReference.referenceInputs adversary), ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞) =
      ∑ k ∈ Finset.range q, Pr[fun r => (fun v : PrefixView => k < v.count) (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] :=
    fun R => ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers _ (fun r => seedCost a R r.2.1) q
      (fun r hr => seedGame_real_cost (referenceInputs_subset adversary) adversary q a R r hr)
  have href : ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ℝ≥0∞) =
      ∑ k ∈ Finset.range q, Pr[fun s => (fun v : PrefixView => k < v.count) (sampleView a s) |
        PairedReference.referenceExperiment adversary q] :=
    ClaudeWCT.W9.T3.Security.Wots.Leaf.expectation_layers _ (prefixCount a) q (fun s hs =>
      (LeafView.prefixCount_le_length a s).trans (Core.ref_trace_length_le adversary q s hs))
  simp only [hmix, href]
  calc ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
        ∑ k ∈ Finset.range q, Pr[fun r => k < (runView a R r).count |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
      = ∑ k ∈ Finset.range q, ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R *
          Pr[fun r => k < (runView a R r).count |
            realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
              (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)] := by
        simp only [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ k ∈ Finset.range q, (Pr[fun s => k < (sampleView a s).count |
          PairedReference.referenceExperiment adversary q] + FamLift.errCF S adversary q a) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact view_prob_geF S hgrp C hws hb q ha (fun v => k < v.count) (fun z h => by
          simp only [runViewD, ClaudeWCT.W9.T3.Security.Wots.Leaf.calls_prefixQuery_zero] at h
          omega)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRef
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamRestart2 ====
section

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

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestart2
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamTot ====
section

/-! # Family restart, step P6a: the total family seed-test error (r3-lean-seedfam)

`errTotF S adversary q := ∑ over source chains of errCF` (family analogue of `Contacts.errTot`), bounded by the charge
`Cmax` (`errTotF_le`), in reals `errTotF ≤ 2·Cmax·y³/(1-y)` with the one-sided side-channel constant
(`errTotF_toReal`), hence the small-route seed-error hypothesis for `Cmax ≤ 305` (`seedErrorBoundF`; v6: `Cmax = 301`,
`errTotF ≤ 602 y³/(1-y)`). -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Total family seed-test error over the source chains. -/
noncomputable def errTotF (S : FamScheme) (adversary : Final.Paired.AdversaryP) (q : Nat) : ℝ≥0∞ :=
  ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, FamLift.errCF S adversary q a

/-- Scheme-wide hypotheses of the family restart. -/
structure FamHyps (S : FamScheme) (Cmax : Nat) where
  caps : FamCaps S
  grp_le : ∀ lay, S.grp lay ≤ 2 ^ 20
  charge : ∀ lay, S.grp lay * chainCount lay ≤ Cmax
  width : ∀ lay, chainCount lay ≤ S.stride lay
  points : ∀ lay, (S.grp lay - 1) * S.stride lay + chainCount lay < 1024

theorem errTotF_le {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (adversary : Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2 ^ 128) :
    errTotF S adversary q ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) :=
  FamLift.errC_sum_leF S H.grp_le Cmax H.charge H.caps H.width H.points q
    (CanonicalWeighted.query_card_lt_one q hq)

theorem errTotF_toReal {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (adversary : Final.Paired.AdversaryP)
    (q : Nat) (hq : q < 2 ^ 128) :
    (errTotF S adversary q).toReal ≤ 2 * Cmax * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128) := by
  have h0 := CanonicalWeighted.errConst_nonneg q hq
  have hle := errTotF_le H adversary q hq
  have h := ENNReal.toReal_mono (by finiteness) hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0, ENNReal.toReal_natCast] at h
  have hd : 0 < 1 - (q : ℝ) / 2 ^ 128 := by
    have hq' : (q : ℝ) < 2 ^ 128 := by exact_mod_cast hq
    exact sub_pos.mpr ((div_lt_one (by positivity)).2 hq')
  have hn : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hk := CanonicalWeighted.kconst_le_sq q
  have hm : 0 ≤ (Cmax : ℝ) * (q : ℝ) := mul_nonneg (Nat.cast_nonneg _) hn
  have hc : 0 ≤ 2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) 128)) 3)
  unfold Core.errConst at h
  have hcard : (Fintype.card Digest : ℝ) = 2 ^ 128 := by rw [Fintype.card_bitVec]; norm_num
  rw [hcard] at h
  have hrat : ((2 : ℝ) ^ 128)⁻¹ * (q : ℝ) = (q : ℝ) / 2 ^ 128 := by ring
  rw [hrat] at h
  calc (errTotF S adversary q).toReal
      ≤ (2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * (ClaudeWCT.Arith.SideChannel.kconst q : ℝ) / (1 - (q : ℝ) / 2 ^ 128)) *
          ((Cmax : ℝ) * q) := h
    _ ≤ (2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * ((q : ℝ) ^ 2) / (1 - (q : ℝ) / 2 ^ 128)) * ((Cmax : ℝ) * q) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hc) hd.le) hm
    _ = _ := by ring

/-- The family seed-error hypothesis of the small route (`errTotF ≤ (733/1000) y²` on `y ≤ 3/2500`) for `Cmax ≤ 305`. -/
theorem seedErrorBoundF {S : FamScheme} {Cmax : Nat} (H : FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (hy : (q : ℝ) / 2 ^ 128 ≤ 3 / 2500) :
    (errTotF S adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2 :=
  (errTotF_toReal H adversary q hq).trans
    (grouped_seed_error Cmax _ (Nat.cast_nonneg _) (by exact_mod_cast hC) (by positivity) hy)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamContacts ====
section

/-! # Family restart, step P6a: the normalized contacts layer charged to family errors (r3-lean-seedfam)

Family port of the normalized `Contacts` (`twoEdgeAt_cost_le`, `contactAt_cost_le`, `reference_twoEdge_le`,
`reference_contacts_cost_le`): the per-chain error `Core.errC` becomes `FamLift.errCF S`, the total `Contacts.errTot`
becomes `FamTot.errTotF S` (summed over `sourceChains`; it agrees with the sum over `Contacts.sourceChains7` since
`errCF` vanishes off `SourceChain7`, `errTot7F_eq`). The leaf-independent parts (`twoEdge_mix_R`, `contact_mix_R`,
`twoEdgeAt_iff_sample`, `contactAt_iff_sample`, `prefixCount_sum_le`, `expected_contactCount`) are reused.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamContacts
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun realRun
  idealRun lazyRun TwoEdgeEvent Contact)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceGame PairedReference.offlineGame

/-- Family total over `sourceChains7` (the index set of the leaf consumers). -/
noncomputable def errTot7F (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ℝ≥0∞ :=
  ∑ a ∈ Normalized.Contacts.sourceChains7, FamLift.errCF S adversary q a

/-- `errCF` vanishes off `SourceChain7`, so the totals over `sourceChains7` and `sourceChains` agree. -/
theorem errTot7F_eq (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    errTot7F S adversary q = FamTot.errTotF S adversary q := by
  unfold errTot7F FamTot.errTotF Normalized.Contacts.sourceChains7
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : WotsExtract.SourceChain7 a
  · rw [if_pos h]
  · rw [if_neg h, FamLift.errCF, dif_neg h]

theorem errTot7F_le {S : FamScheme} {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    errTot7F S adversary q ≤ ENNReal.ofReal (Core.errConst q) * ((Cmax : ℝ≥0∞) * q) := by
  rw [errTot7F_eq]
  exact FamTot.errTotF_le H adversary q hq

section PerChain
variable {S : FamScheme} {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
include H

/-- Per chain, two-edge cost with the family seed-test error. -/
theorem twoEdgeAt_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] ≤
      twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a := by
  have hv := FamRef.view_prob_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
    PrefixView.TwoEdge (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := FamRef.view_count_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
  simp only [runView_twoEdge] at hv
  rw [Normalized.Contacts.twoEdgeAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ twoEdgeRate q * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (twoEdgeRate q)]
    exact mul_le_mul' le_rfl (Normalized.Contacts.twoEdge_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => (sampleView a s).TwoEdge | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ twoEdgeRate q * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

/-- Per chain, contact cost with the family seed-test error. -/
theorem contactAt_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] ≤
      (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
        (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a := by
  have hv := FamRef.view_prob_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
    PrefixView.Contact (fun z h => by
    have := h.1; simp [Leaf.runViewD] at this)
  have hc := FamRef.view_count_leF (adversary := adversary) S H.grp_le H.caps H.width H.points q ha
  simp only [runView_contact] at hv
  rw [Normalized.Contacts.contactAt_iff_sample]
  set M := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * Pr[fun r => Contact r.2.2 r.1 |
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R) (fun _ _ => none)]
  set C := ∑' R, Core.restLaw (PairedReference.referenceInputs adversary) R * ∑' r,
      realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (seedGame (referenceInputs_subset adversary) adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ℝ≥0∞)
  have hMC : (1 - (q : ENNReal) / 2 ^ 128) * M ≤ (2 / 2 ^ 128) * C := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro R
    rw [mul_left_comm, mul_left_comm (2 / 2 ^ 128 : ENNReal)]
    exact mul_le_mul' le_rfl (Normalized.Contacts.contact_mix_R adversary q hq a R)
  have hx1 : (1 - (q : ENNReal) / 2 ^ 128) ≤ 1 := tsub_le_self
  calc (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => (sampleView a s).Contact | PairedReference.referenceExperiment adversary q]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (M + FamLift.errCF S adversary q a) := mul_le_mul' le_rfl hv
    _ ≤ (1 - (q : ENNReal) / 2 ^ 128) * M + FamLift.errCF S adversary q a := by
        rw [mul_add]; exact add_le_add le_rfl (mul_le_of_le_one_left bot_le hx1)
    _ ≤ (2 / 2 ^ 128) * C + FamLift.errCF S adversary q a := add_le_add hMC le_rfl
    _ ≤ (2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (prefixCount a s : ENNReal) +
          q * FamLift.errCF S adversary q a) + FamLift.errCF S adversary q a :=
        add_le_add (mul_le_mul' le_rfl hc) le_rfl
    _ = _ := by ring

/-- **Two-edge bound, family charge.** -/
theorem reference_twoEdge_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      (twoEdgeRate q * (∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal)) +
        (1 + twoEdgeRate q * q) * FamTot.errTotF S adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [← errTot7F_eq]
  have hunion : Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] := by
    refine le_trans (le_of_eq ?_) (probEvent_exists_finset_le_sum Normalized.Contacts.sourceChains7
      (PairedReference.referenceExperiment adversary q)
      (fun a s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a))
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Normalized.Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Normalized.Contacts.mem_sourceChains7 a).mp ha, h⟩
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
          CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q] * (1 - (q : ENNReal) / 2 ^ 128)
      ≤ (∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q]) * (1 - (q : ENNReal) / 2 ^ 128) :=
        mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ Normalized.Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a |
            PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Normalized.Contacts.sourceChains7, (twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => twoEdgeAt_cost_leF H adversary q hq a ((Normalized.Contacts.mem_sourceChains7 a).mp ha)
    _ = twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ Normalized.Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) +
          (1 + twoEdgeRate q * q) * errTot7F S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal) +
          (1 + twoEdgeRate q * q) * errTot7F S adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast Normalized.Contacts.prefixCount_sum_le s

/-- **Expected contact count bound, family charge.** -/
theorem reference_contacts_cost_leF (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 2 ^ 128) :
    ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) ≤
      ((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal)) +
        (1 + (2 / 2 ^ 128) * q) * FamTot.errTotF S adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [Normalized.Contacts.expected_contactCount, ← errTot7F_eq]
  calc (∑ a ∈ Normalized.Contacts.sourceChains7, Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
          PairedReference.referenceExperiment adversary q]) * (1 - (q : ENNReal) / 2 ^ 128)
      = ∑ a ∈ Normalized.Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => CanonicalRef.ContactAt s.answers (sourceMessages s.answers) s.trace a |
            PairedReference.referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Normalized.Contacts.sourceChains7, ((2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          (prefixCount a s : ENNReal) + (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => contactAt_cost_leF H adversary q hq a ((Normalized.Contacts.mem_sourceChains7 a).mp ha)
    _ = (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s *
          ((∑ a ∈ Normalized.Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot7F S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.prefixClassCount s : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * errTot7F S adversary q := by
        apply add_le_add _ le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast Normalized.Contacts.prefixCount_sum_le s
end PerChain

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamContacts
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamV6 ====
section

/-! # The v6 seed families as an interface (r3-lean-seedfam; for the scheme / top-bytes porters)

The family restart (WotsFam*.lean) is proved for any `FamScheme S` with reveal caps `FamCaps S`. For the v6 images
(opus-crumbs img-v6, `scripts/check_seeds_v6.py`) the scheme side must discharge exactly two statements:

* `V6SeedSpec` — the WOTS seeds are family evaluations:
  - TOP (layer 0): 4-leaf families, 39 coefficients at ordinals `39·(leaf/4) + i` (carry-packed halves of
    `lowerSeedPair 0 tree`), points `((leaf & 3) << 6) + j + 1 = (leaf % 4)·64 + j + 1 ≤ 256`;
  - LOWER: 7-leaf families, ordinals `38·(leaf/7) + i`, `5·r + 3` coefficients (`r = 7`, or the remainder `2` for L1 /
    `1` for L2, L3 in the last family), points `(leaf % 7)·43 + j + 1 ≤ 301`;
* `V6ZeroSpec` — every leaf's reference digits have at most 9 (top) / 5 (lower) zeros (`producerZeroCap`).

From them, `v6Scheme` / `v6Caps` are the `FamScheme` / `FamCaps` the port consumes. Facts used by the restart and the
closing are proved here: points distinct and `< 1024` (top `≤ 256`), per-test charge `4·54 = 216` (top) and
`7·43 = 301` (lower) `≤ 305` (the live closing bound, `FinalG`), degree `38` top (`39` coefficients), and the reveal budget
`9·4 + 3 = 39` (top), `5·r + 3` (lower).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart.V6
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open ClaudeWCT.Arith.SideChannel.GroupedFamily (gptS gptS_injective gptS_lt)
attribute [local instance] Classical.propDecidable

/-- Leaves per family. -/
def grp (lay : Layer) : Nat := if lay = 0 then 4 else 7
/-- Ordinal base per family. -/
def cnt (lay : Layer) : Nat := if lay = 0 then 39 else 38
/-- Point stride. -/
def stride (lay : Layer) : Nat := if lay = 0 then 64 else 43
/-- Coefficients of family `f` (the last lower family is short). -/
def size (lay : Layer) (f : Nat) : Nat := if lay = 0 then 39 else 5 * min 7 (2 ^ height lay - 7 * f) + 3
/-- Evaluation point: chains below `chainCount` at `(leaf % grp)·stride + i + 1`; the unused address slots
`chainCount ≤ i < 58` in a separate junk region above `grp·stride` (lower `302 + l·15 + (i − 43)`), so all points of a
family are distinct and `< 1024`. The images never compute junk seeds. -/
def point (lay : Layer) (leaf i : Nat) : Nat :=
  if i < chainCount lay then (leaf % grp lay) * stride lay + i + 1
  else grp lay * stride lay + (leaf % grp lay) * (58 - chainCount lay) + (i - chainCount lay) + 1
/-- Zero-digit cap per leaf. -/
def zcap (lay : Layer) : Nat := if lay = 0 then 7 else 5

/-- **Scheme obligation 1**: WOTS seeds are v6 family evaluations. -/
def V6SeedSpec : Prop :=
  ∀ (T : Answers) (lay : Layer) (tree leaf i : Nat), WCT9.wotsSeed T lay tree leaf i =
    ClaudeWCT.Arith.familyEval (List.ofFn fun j : Fin (size lay (leaf / grp lay)) =>
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair lay tree ((cnt lay * (leaf / grp lay) + j) / 2)))
        (cnt lay * (leaf / grp lay) + j)) (point lay leaf i)

/-- **Scheme obligation 2**: per-leaf zero-digit caps of the reference digits. -/
def V6ZeroSpec : Prop :=
  ∀ {U : Finset HashInput} (R : Tables U) (L : LeafAddr),
    (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0).card ≤ zcap L.lay

theorem size_le (lay : Layer) (f : Nat) : size lay f ≤ cnt lay := by
  unfold size cnt
  split_ifs
  · exact le_rfl
  · have : min 7 (2 ^ height lay - 7 * f) ≤ 7 := min_le_left _ _
    omega

/-- The v6 family scheme (given the seed obligation). -/
def v6Scheme (h : V6SeedSpec) : FamScheme where
  grp := grp
  cnt := cnt
  size := size
  stride := stride
  point := point
  grp_pos lay := by unfold grp; split_ifs <;> decide
  cnt_le lay := by unfold cnt; split_ifs <;> decide
  size_le := size_le
  point_eq lay leaf i hi := by unfold point; rw [if_pos hi]
  seed := h

/-- The v6 reveal caps (given the zero obligation). -/
def v6Caps (hs : V6SeedSpec) (hz : V6ZeroSpec) : FamCaps (v6Scheme hs) where
  zcap := zcap
  zeros_le R L := hz R L
  size_ge lay f := by
    show zcap lay * min (grp lay) (2 ^ height lay - grp lay * f) + 3 ≤ size lay f
    unfold zcap grp size
    split_ifs
    · have : min 4 (2 ^ height lay - 4 * f) ≤ 4 := min_le_left _ _
      omega
    · exact le_rfl

/-! ### Facts used by the restart and the closing -/

/-- Points of the family chains `(l, c)` are `gptS (stride lay) (l, c)`; top points stay `≤ 256`. -/
theorem top_point_le (l : Fin 4) (c : Fin 54) : gptS 64 (l, c) ≤ 256 := by
  unfold gptS; have := l.isLt; have := c.isLt; omega

theorem top_points_injective : Function.Injective (gptS 64 (g := 4) (w := 54)) := gptS_injective (by decide)
theorem lower_points_injective : Function.Injective (gptS 43 (g := 7) (w := 43)) := gptS_injective le_rfl
theorem top_points_lt (c : Fin 4 × Fin 54) : gptS 64 c < 1024 := gptS_lt (by decide) c
theorem lower_points_lt (c : Fin 7 × Fin 43) : gptS 43 c < 1024 := gptS_lt (by decide) c

/-- `((leaf & 3) << 6) + j + 1 = (leaf % 4)·64 + j + 1`. -/
theorem top_point_bits (leaf j : Nat) : ((leaf &&& 3) <<< 6) + j + 1 = (leaf % 4) * 64 + j + 1 := by
  rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod leaf 2]

/-- Per-test charges (chains per family) against the live closing bound `305` (`FinalG.seedErrorBound_of_charge`). -/
theorem charges : 4 * 54 = 216 ∧ 216 ≤ 305 ∧ 7 * 43 = 301 ∧ 301 ≤ 305 := by decide

/-- Top: 39 coefficients (degree 38) and the reveal budget `9·4 + 3 = 39`. -/
theorem top_budget : cnt 0 = 39 ∧ size 0 0 = 39 ∧ 9 * 4 + 3 = 39 := by decide

/-- Reveal bound of a top family: at most 9 revealed seeds per leaf leave 3 free degrees. -/
theorem top_revealed_card_le (Rev : Finset (Fin 4 × Fin 54)) (h : ∀ l : Fin 4, (Rev.filter fun c => c.1 = l).card ≤ 9) :
    Rev.card + 3 ≤ 39 := by
  have := ClaudeWCT.Arith.SideChannel.GroupedFamily.revealed_card_leW (g := 4) (w := 54) (r := 9) Rev h
  omega

end ClaudeWCT.W9.T3.Security.Wots.FamRestart.V6
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_WotsFamHyps ====
section

/-! # Family restart hypotheses for today's scheme and for v6 (r3-lean-seedfam)

`layoutHyps : FamHyps layoutScheme 301` (the scheme of the `Correctness` layout) and
`v6Hyps hs hz : FamHyps (v6Scheme hs) 301` (v6: lower 7-leaf, top 4-leaf families); with `seedErrorBoundF` the v6 seed
error is `≤ 602 y³/(1-y) ≤ (733/1000) y²` on the live small window. -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
open SigGolfCandidate.T3
open ClaudeWCT.W9.T3.Security.Wots.FamRestart

theorem chainCount_cases (lay : Layer) : chainCount lay = if lay = 0 then 51 else 43 := by
  fin_cases lay <;> rfl

/-- The scheme of the `Correctness` layout (v6 lower 7-leaf families, top per-leaf until the top port): charge
`max(1 · 51, 7 · 43) = 301`. -/
def layoutHyps : FamHyps layoutScheme 301 where
  caps := layoutCaps
  grp_le lay := by show WCT9.famGrp lay ≤ 2 ^ 20; unfold WCT9.famGrp; split_ifs <;> norm_num
  charge lay := by
    show WCT9.famGrp lay * chainCount lay ≤ 301
    unfold WCT9.famGrp; rw [chainCount_cases]; split_ifs <;> decide
  width lay := WCT9.famStride_ge lay
  points lay := by
    show (WCT9.famGrp lay - 1) * WCT9.famStride lay + chainCount lay < 1024
    unfold WCT9.famGrp WCT9.famStride; rw [chainCount_cases]; split_ifs <;> decide

/-- v6: lower 7-leaf (stride 43), top 4-leaf (stride 64) families, charge `max(4·51, 7·43) = 301`. -/
def v6Hyps (hs : V6.V6SeedSpec) (hz : V6.V6ZeroSpec) : FamHyps (V6.v6Scheme hs) 301 where
  caps := V6.v6Caps hs hz
  grp_le lay := by show V6.grp lay ≤ 2 ^ 20; unfold V6.grp; split_ifs <;> norm_num
  charge lay := by
    show V6.grp lay * chainCount lay ≤ 301
    unfold V6.grp; rw [chainCount_cases]; split_ifs <;> decide
  width lay := by
    show chainCount lay ≤ V6.stride lay
    unfold V6.stride; rw [chainCount_cases]; split_ifs <;> decide
  points lay := by
    show (V6.grp lay - 1) * V6.stride lay + chainCount lay < 1024
    unfold V6.grp V6.stride; rw [chainCount_cases]; split_ifs <;> decide

/-- v6 small-route seed error: `errTotF ≤ (733/1000) y²` on `y ≤ 3/2500` (via `602 y³/(1-y)`). -/
theorem v6_seedError (hs : V6.V6SeedSpec) (hz : V6.V6ZeroSpec) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q < 2 ^ 128) (hy : (q : ℝ) / 2 ^ 128 ≤ 3 / 2500) :
    (errTotF (V6.v6Scheme hs) adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2 :=
  seedErrorBoundF (v6Hyps hs hz) (by norm_num) adversary q hq hy

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
end
-- ==== merged from ClaudeWCT_W9_T3_Secc_FinalFam ====
section

/-! # The live security theorem through the family seed-error charge (r3-lean-seedfam, P6b)

Copies of the Final.lean blocks that charge the WOTS seed test per chain (`Core.errC`, `Contacts.errTot`, the
per-chain restart `Restart.source_contactAfterStop_charge` / `source_markerFirst_at_le`), suffixed `Fam`, with the
family charge `FamLift.errCF S` / `FamTot.errTotF S` for any `FamScheme S` with `H : FamTot.FamHyps S Cmax`
(`FamRestart2.*F`, `FamContacts.*F`). The closing is FinalG's (`799/1000`, `grouped_middle_closing`) with the seed
error `FamTot.seedErrorBoundF H hC` (`Cmax ≤ 305`); the large route is `LargeCoupling.Paired.large_bound`.
`t3_securityP_fam S Cmax H hC : SecurityP`; `t3_securityP_layout` instantiates the scheme's layout (v6). -/

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
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL

/-- Other contacts are invariant under the family congruence of a source chain's family. -/
theorem otherContact_stopLFam (S : FamScheme) (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (a : ChainAddr)
    (ha : WotsExtract.SourceChain7 a) :
    ∀ T T', FamGame.FamCongr S (sourceMessages T) (FamSum.famOf S a.key) T T' → ∀ trace,
      OtherContact a T' trace ↔ OtherContact a T trace := by
  intro T T' hC trace
  have hFok := FamLift.famOk_of_source S hgrp ha.1
  unfold OtherContact
  exact exists_congr fun b => and_congr_right fun hb => and_congr_right fun _ =>
    FamRestartN.contactAt_famCongr hC hFok.leaf hFok.tree trace hb

theorem reference_twoContacts_le_rawFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (((2 * q : ℕ) : ENNReal) *
          (((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) +
              (1 + (2 / 2 ^ 128) * q) * FamTot.errTotF S adversary q) /
            (1 - (q : ENNReal) / 2 ^ 128)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q) /
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hne : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hpos (by simp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
        PairedReference.referenceExperiment adversary q] := by
    refine le_trans ?_ (probEvent_exists_finset_le_sum Contacts.sourceChains7 (PairedReference.referenceExperiment adversary q)
        (fun a s => ContactAfterStop (OtherContact a) s.answers s.trace a))
    apply pmf_probEvent_mono
    rintro s - ⟨a, b, ha, hb, hab, hca, hcb⟩
    rcases twoContacts_cases s.answers s.trace a b ha hb hab hca hcb with h | h
    · exact ⟨a, (Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · exact ⟨b, (Contacts.mem_sourceChains7 b).mpr hb, h⟩
  have hcharge := fun a (ha : a ∈ Contacts.sourceChains7) =>
    FamRestart2.source_contactAfterStop_chargeF (adversary := adversary) S H.grp_le H.caps H.width H.points q
      ((Contacts.mem_sourceChains7 a).mp ha) (OtherContact a)
      (otherContact_maskAt a ((Contacts.mem_sourceChains7 a).mp ha))
      (otherContact_stopLFam S H.grp_le a ((Contacts.mem_sourceChains7 a).mp ha)) hq
  have halloc : ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) ≤
      ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) := by
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
    · rw [← Finset.mul_sum]
      have hpoint : ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0) ≤
          ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
        calc ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
              (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
            ≤ ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul' le_rfl
              by_cases h : ∃ k, OtherContact a s.answers (s.trace.take k)
              · rw [if_pos h]
                exact_mod_cast otherContact_take_count s a h
              · rw [if_neg h]
                exact bot_le
          _ = ((2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              rw [← Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
          _ ≤ ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply mul_le_mul' _ le_rfl
              have h1 := Contacts.prefixCount_sum_le s
              have h2 := prefixClassCount_le_length s
              have h3 := Core.ref_trace_length_le adversary q s hs
              exact_mod_cast (by omega : 2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s ≤ 2 * q)
      calc PairedReference.referenceExperiment adversary q s * ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
          ≤ PairedReference.referenceExperiment adversary q s * (((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal)) :=
            mul_le_mul' le_rfl hpoint
        _ = ((2 * q : ℕ) : ENNReal) * (PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal)) := by ring
    · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  calc Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] *
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
      ≤ (∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a | PairedReference.referenceExperiment adversary q]) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Contacts.sourceChains7, (∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => hcharge a ha
    _ = ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← FamContacts.errTot7F_eq]
        rfl
    _ ≤ ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q := add_le_add halloc le_rfl
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (FamContacts.reference_contacts_cost_leF H adversary q hq)) le_rfl

theorem reference_twoContacts_leFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) *
          (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * FamTot.errTotF S adversary q := by
  refine (reference_twoContacts_le_rawFam S H adversary q hq).trans (le_of_eq ?_)
  rw [ENNReal.add_div, big_div_mul]
  set E := ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)
  set T := FamTot.errTotF S adversary q
  set y := 1 - (q : ENNReal) / 2 ^ 128
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt), pow_two, ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt)]
  push_cast
  ring

set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_leFam (S : FamScheme) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) ≤ FamTot.errTotF S adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) =
      ∑ a ∈ Finset.univ.image Enc.chainAt, FamLift.errCF S adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image Enc.chainAt, FamLift.errCF S adversary q a ≤
      ∑ a ∈ (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7, FamLift.errCF S adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · rw [FamLift.errCF, dif_neg h]
  have h3 : (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7 ⊆ Contacts.sourceChains7 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (Contacts.mem_sourceChains7 a).mpr ha.2
  rw [← FamContacts.errTot7F_eq, h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)

theorem reference_markerFirst_sum_le_ofFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q] ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal)) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((5022 / 2 ^ 128 : ENNReal) * (∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal))) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * FamTot.errTotF S adversary q := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
          FamLift.errCF S adversary q (Enc.chainAt p) := by
    intro p
    by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
    · simp only [hs, true_and]
      have hC := FamRestart2.source_markerFirst_at_leF (adversary := adversary) S H.grp_le H.caps H.width H.points
        q hq (Enc.chainAt p) hs
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (Enc.chainAt p)) s.answers s.trace
        (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set EC := FamLift.errCF S adversary q (Enc.chainAt p)
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs, ← big_div_mul, ENNReal.div_add_div_same]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM + ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * EC := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := exists_chainAt ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, (2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            FamLift.errCF S adversary q (Enc.chainAt p)) :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
              PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            ∑ p : CanonGraph.LeafPos × Fin 58, FamLift.errCF S adversary q (Enc.chainAt p) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hMS) (mul_le_mul' le_rfl (sum_errC_chainOf_leFam S adversary q))

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem reference_primitive_leFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128)
 (w v : ENNReal) (hwv : w+v=1) :
 Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
 Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] + (2^142:ENNReal)⁻¹ +
 prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
 encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
 (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
 errCoeff q w v*FamTot.errTotF S adversary q := by
 -- top-nonce layer (r3-lean-nonsec): the structural bound carries Pr[CapFail] ≤ (2^142)⁻¹; fold it into the
 -- other-mass argument of weighted_union_le as (2^128)⁻¹ * (EO + 2^128 * (2^142)⁻¹).
 have hcancel : ∀ x : ENNReal, (2^128:ENNReal)⁻¹ * (x + 2^128 * (2^142:ENNReal)⁻¹) =
     (2^128:ENNReal)⁻¹ * x + (2^142:ENNReal)⁻¹ := fun x => by
   rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
 have key : Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
     Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] +
     prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
     encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
     (2^128:ENNReal)⁻¹*((∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) + 2^128 * (2^142:ENNReal)⁻¹) +
     errCoeff q w v*FamTot.errTotF S adversary q := by
  refine weighted_union_le (PairedReference.referenceExperiment adversary q)
    Combined ReferenceFailed EncodingMatch Structural TwoEdge TwoContacts MarkerFirstEvent ContactFirstEvent
    q w v _ _ _ _ hwv combined_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact CanonicalRef.reference_encodingMatch_le adversary q
  · rw [hcancel]
    exact structural_reference_le adversary q (PairedReference.reference_structural_in_le adversary q)
  · exact FamContacts.reference_twoEdge_leF H adversary q hq
  · exact Restart.reference_twoContacts_leFam S H adversary q hq
  · exact Restart.reference_markerFirst_sum_le_ofFam S H adversary q hq (CanonicalRef.reference_marker_sum_le adversary q)
  · exact (CanonicalRef.Contact93.reference_contactFirst_le adversary q).trans
      (mul_le_mul' le_rfl (FamContacts.reference_contacts_cost_leF H adversary q hq))
  · exact (nonstructural_reference_le adversary q).trans (FamContacts.reference_contacts_cost_leF H adversary q hq)
 refine key.trans (le_of_eq ?_)
 rw [hcancel]
 ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem errTotF_ne_topFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128) :
    FamTot.errTotF S adversary q≠⊤ :=
  ne_top_of_le_ne_top (by finiteness) (FamTot.errTotF_le H adversary q hq)

theorem primitive_real_of_rawFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q<2^128)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hp:prefixMass adversary q≠⊤) (he:encodingMass adversary q≠⊤)
    (eventProbability otherMass : ENNReal) (ho:otherMass≠⊤)
    (hraw : eventProbability ≤ 1/(2:ENNReal)^139+(2^142:ENNReal)⁻¹+
      prefixCoeff q w v/2^128*prefixMass adversary q+
      encodingCoeff q w v/2^128*encodingMass adversary q+
      (2^128:ENNReal)⁻¹*otherMass+errCoeff q w v*FamTot.errTotF S adversary q)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤1061/1000) :
    eventProbability.toReal ≤
      theta*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
      otherMass.toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc1:=prefixCoeff_ne_top q hq w v hw hv
  have hc2:=encodingCoeff_ne_top q hq w v hw
  have hc3:=errCoeff_ne_top q hq w v hw hv
  have hfin:=errTotF_ne_topFam S H adversary q hq
  have h:=ENNReal.toReal_mono (by finiteness) hraw
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_inv,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    prefixCoeff_toReal q hq w v hw hv hwv,encodingCoeff_toReal q hq w v hw,
    errCoeff_toReal q hq w v hw hv hwv] at h
  have he0 : 0≤canonicalError ((q:ℝ)/2^128) w.toReal := by
    rw [←errCoeff_toReal q hq w v hw hv hwv]
    exact ENNReal.toReal_nonneg
  have hseed := FamTot.seedErrorBoundF H hC adversary q hq hy
  have herr:=grouped_weighted_error ((q:ℝ)/2^128) (FamTot.errTotF S adversary q).toReal
    (canonicalError ((q:ℝ)/2^128) w.toReal) he0 herror hseed
  have hp' := mul_le_mul_of_nonneg_right hprefix (show 0≤(prefixMass adversary q).toReal/2^128 by positivity)
  have he' := mul_le_mul_of_nonneg_right hencoding (show 0≤(encodingMass adversary q).toReal/2^128 by positivity)
  simp only [div_eq_mul_inv] at h hp' he' herr ⊢
  nlinarith

theorem primitive_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤1061/1000) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      theta*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hqN : q<2^128 := by omega
  have hf := PairedSmallT.masses_finite adversary q hq
  have hraw := (reference_primitive_leFam S H adversary q hqN w v hwv).trans
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hfailed le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
  exact primitive_real_of_rawFam S H hC adversary q hqN hy w v hw hv hwv hf.1 hf.2.1
    _ (PairedSmallT.otherMass adversary q) hf.2.2.1 hraw theta hprefix hencoding herror

theorem primitive_middle_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99847/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc := middle_coefficients_t ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failureFam S H hC adversary q hq hy (1023/50000) (48977/50000)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

theorem primitive_tiny_real_of_failureFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) := by
  have hc := tiny_coefficients_t ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failureFam S H hC adversary q hq (hy.trans (by norm_num)) (3/100) (97/100)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

theorem primitive_middle_realFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99847/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) :=
  primitive_middle_real_of_failureFam S H hC adversary q hq hy (reference_failed_le adversary q)

theorem primitive_tiny_realFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(778/1000)*((q:ℝ)/2^128)^2+(1/2^139+1/2^142) :=
  primitive_tiny_real_of_failureFam S H hC adversary q hq hy (reference_failed_le adversary q)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem middle_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow:1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh:(q:ℝ)/2^128≤3/2500) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennrealG adversary q hq
  apply middle_clean_closingG adversary q hq hlow hhigh (1153/1000000) le_rfl ?_
    (completed_partial_certifiedG adversary q hq)
  have hp:=CanonicalWeighted.primitive_middle_realFam S H hC adversary q hq hhigh
  have h:=clean_probability_real_ofG adversary q hq (completed_split_canonical adversary q hq)
    (99847/50000) (1153/1000000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤99847/50000))
    excess_middle_actualG (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem tiny_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤1/2^28) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennrealG adversary q hq
  apply tiny_clean_closingG adversary q hq hpositive hhigh (18/5000) le_rfl ?_
    (completed_partial_certifiedG adversary q hq)
  have hp:=CanonicalWeighted.primitive_tiny_realFam S H hC adversary q hq hhigh
  have h:=clean_probability_real_ofG adversary q hq (completed_split_canonical adversary q hq)
    (249/125) (18/5000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤249/125))
    excess_tiny_actualG (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem small_boundFam (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 305) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤3/2500) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  by_cases ht:(q:ℝ)/2^128≤1/2^28
  · exact tiny_boundFam S H hC adversary q hq hpositive ht
  · exact middle_boundFam S H hC adversary q hq (le_of_lt (lt_of_not_ge ht)) hhigh

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme layoutScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- **The live security theorem through the family seed-error charge**: any family scheme with the family-restart
hypotheses and per-test charge `Cmax ≤ 305`. -/
theorem t3_securityP_fam (S : FamScheme) (Cmax : Nat)
    (H : ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.FamHyps S Cmax) (hC : Cmax ≤ 305) :
    ClaudeWCT.W9.T3M.Final.Paired.SecurityP := by
  apply PairedOuter.PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  by_cases hsmall : (q:ℝ)/2^128 ≤ 3/2500
  · exact Wots.PairedSmallT.small_boundFam S H hC adversary q hq hpositive hsmall
  · exact LargeCoupling.Paired.large_bound adversary q hq (le_of_not_ge hsmall)

/-- **The live security theorem of the v6 scheme** (the `Correctness` layout: lower 7-leaf families, charge 301). -/
theorem t3_securityP_layout : ClaudeWCT.W9.T3M.Final.Paired.SecurityP :=
  t3_securityP_fam layoutScheme 301 ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.layoutHyps
    (by norm_num)

end ClaudeWCT.W9.T3.Secc.Paired
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsLayout ====
section

section


namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
/-! ### T51 top layer (verify image T51_T152_g791_c0hi, generator t51/verify/py/gen_t51v.py --c0hi)
Groups `q` in dispatch (= chain) order:
* `q < 9`: the radix-6 triples g0..g8 (chains `3q .. 3q+2`, largest digit 5, 216 ranks); cells `cell6`, shared
  bodies `body6` (chain-A rung ladder, chain B, chain C, next dispatch);
* `9 ≤ q < 16`: #938's radix-5 groups q9..q15 (chains 27..47, largest digit 4, 125 ranks), #938's code with the
  leaf-slot immediates moved by `-16` (endpad leaf); q15's last dispatch is #938's dispatch into group 8;
* `q = 16`: the radix-7 pair (chains 48 = A, 49 = B, largest digit 6, 49 ranks `k = d48 + 7 d49`, no chain C);
  cells in #938's q8 column `1024 (125 - k) + 676`, bodies `body7Tab` (ladder, chain 49, checksum dispatch);
* `q = 17`: the radix-6 checksum chain 50 (largest digit 5), arms `ckArm d` (d = 0..5). -/
/-- Largest digit of the chains of top group `q` (T51): r6 groups 5, #938's r5 groups 4, the r7 pair 6, the
checksum chain (group 17) 5. -/
def mx (q : Nat) : Nat := if q<9 then 5 else if q<16 then 4 else if q=16 then 6 else 5
/-- Top chain `i`'s block in the top chain area (even pairing, charge 86: pair `p = (2p, 2p+1)` at `104 (26 - p)`,
G chain at `+16`, F chain at `+40`; `= W9.T3M.chainSlot 0 i`). -/
def topSlot (i : Nat) : Nat := 104*(26-i/2)+16+24*(i%2)
/-- Top chain format (T51): chain `i` is G (value first) iff it is even and `i ≤ 50` (`= T3.topIsG`). -/
def topG (i : Nat) : Bool := decide (i%2=0 ∧ i ≤ 50)
def off (i : Nat) : Word := BitVec.ofNat 64 (topSlot i)-BitVec.ofNat 64 1664
/-- T51 endpad top leaf: `end_0` at 25216 (tp + 512), the tweak at 25232, `end_i` at `25232 + 16 i` (i ≥ 1). -/
def slot (i : Nat) : Nat := if i=0 then 25216 else 25232+16*i
/-- Target of chain `i`'s terminal hash: chain 0 (c0hi) writes its last 32-byte answer at `slot 0 - 16 = 25200`
(the HIGH half lands on `end_0`); every other chain at its slot. -/
def termSlot (i : Nat) : Nat := if i=0 then 25200 else slot i
def slotOffset (a : Nat) : Nat := a-24704
def rungR (d : Nat) (sl : Option Nat) (p : Nat) : Result :=
  T3M.rungRB d (sl.map slotOffset) p
def copyN (rb : Reg) (o : Word) (sl tgt : Nat) (g : Bool := false) : Result :=
  T3M.copyNB rb o (slotOffset sl) tgt g
def copyFH (rb : Reg) (o : Word) (sl p : Nat) (g : Bool := false) : Result :=
  T3M.copyFHB rb o (slotOffset sl) p g
def headRH (rb : Reg) (o : Word) (d : Nat) (sl : Option Nat) (p i : Nat) (g : Bool := false) : Result :=
  T3M.headRHB rb o d (sl.map slotOffset) p i g
def emptyR (p : Nat) : Result := ⟨SymState.init,.c (pcOf p),.fuel,0,0⟩
/-- T51 top target (the checksum digit is `topT - sum`). -/
def topT : Nat := 152
/-- r6 group `g` dispatches through table B (`s2 - 256 raw`: g1, g2, g3, g8) or table A (`256 raw + s2`: g4..g7). -/
def r6B (g : Nat) : Bool := decide (g<4 ∨ g=8)
def r6Off (g : Nat) : Nat := 40+6*(g%4)
/-- The 8-bit field value of rank `k` in r6 group `g` (g0: raw = rank + 40). -/
def rawOf6 (g k : Nat) : Nat := if g=0 then k+40 else k
/-- Cell of r6 group `g` for field value `raw`: g0 base-free column `512 (raw - 3) + 326`, table B rows
`3327 - raw`, table A rows `3328 + raw` (offset `r6Off g` inside the 64-word rows). -/
def cell6 (g raw : Nat) : Nat :=
  if g=0 then 512*(raw-3)+326 else if r6B g then 64*(3327-raw)+r6Off g else 64*(3328+raw)+r6Off g
def body6Tab : List Nat := [185001,185713,129188,98758,127558,72868,190819,185085,101958,77988,51748,26182,185855,102854,118948,76964,26405,21062,102982,123044,122020,26277,21285,805,128454,51782,26917,21797,14918,10788,126243,26788,21157,933,10822,1105,186537,189172,187130,186439,130112,51877,190320,188404,188532,128582,27044,46628,189804,190279,185216,52388,21668,25381,191093,185673,52644,46662,967,16165,130212,27078,21924,1317,10917,11557,52678,46757,25893,16677,13860,5925,189353,187049,191988,191722,132863,72357,187305,189097,187634,187719,52005,47268,191846,188656,188926,72485,21958,41508,191785,127140,72997,47524,1351,20261,132902,52517,25124,15908,11428,13894,76453,47558,41542,20773,13989,6437,191913,187500,189038,184942,132941,76581,188270,185129,186986,184791,67108,50724,185289,186341,187206,77093,25158,41637,190945,188585,92965,50758,15942,24357,132980,67142,25253,16037,11684,14500,93477,50853,42148,24869,14756,11084,185769,189225,186727,186213,133019,97061,190633,188073,188005,189947,67237,51364,188841,185960,190577,97573,25764,42404,186086,117284,101157,51620,16548,40484,133058,67748,26020,16804,11718,14790,101669,51654,42438,40518,21324,11596,186481,191401,185577,190426,133097,113188,191587,189993,187877,118180,68004,67365,130300,72228,121380,113222,26054,45604,73124,122276,113828,67877,16838,40613,133136,68038,50981,20004,15141,21836,114084,71461,45638,41124,22052,12069,189865,187247,190889,76324,133175,114118,188773,190761,77220,184832,71204,71973,185449,92708,93348,117319,51493,45733,93604,93383,117541,72265,20038,41380,133214,71238,66084,20133,15653,22086,118053,73161,46244,41414,22181,22821,189545,189609,191529,96804,184867,118215,190121,186862,97700,97444,71333,75557,191453,100900,97479,121415,66118,46500,101796,101540,121637,76069,20644,44580,186584,71844,66213,20900,19237,22692,122149,76361,46534,44614,22948,23372,191017,187759,103588,123334,122311,72100,188457,124068,123462,188231,77257,66724,128164,124358,188329,72134,49700,20934,126534,188999,75300,66980,44709,15013,125476,87588,49734,45220,22982,9764,75334,67014,24100,15524,9798,4644]
def body7Tab : List Nat := [26148,21028,711,14884,11045,8740,268]
def body6 (g dB dC : Nat) : Nat := body6Tab.getD (36*g+6*dB+dC) 0
def baseTab : List Nat := [184791,130112,98124,184908,129996,130212,185013,185050,133292,186153,185147,122700,711,186183,77482,185310,133324,186281,102698,83032,133356,186311,77610,84056,268,93382,132863,185676,127564,133388,185779,185818,122828,133420,186409,98252,123212,805,186665,77738,127692,133452,186921,102826,103513,133484,187100,77910,104537,1105,97478,186442,98636,127820,186552,186584,98764,123340,186695,187433,101964,186794,186829,187689,78122,127948,186954,187817,102954,108633,187068,187847,78250,118314,1804,187206,132902,102092,187323,187357,132941,102220,187465,133516,187945,187562,187599,933,187975,97834,187725,133548,188128,103082,118442,133580,188201,97962,118570,2129,98504,132980,188091,128332,133612,133019,188233,123468,133644,188337,188367,123596,967,188472,98090,128460,133676,188596,103210,118698,133708,188502,98218,119082,2316,101574,188857,102348,128588,184873,188999,102732,123724,189110,189142,102860,123852,189244,189277,98602,128716,189369,189401,103338,119210,189483,189515,98730,122410,2572,189621,133058,102988,189738,189772,133097,103116,189880,189915,188626,103244,190014,1317,188713,101930,190140,190174,188743,103722,122538,190288,188896,102058,190378,190403,102600,133136,190506,190543,185184,133175,190648,190685,185257,188969,190782,124236,1351,189662,190917,128844,185385,190049,191041,191068,185417,190249,191155,191183,191208,117958,133214,191311,128972,185513,191414,103372,124364,185545,191557,103756,126540,191659,191692,102186,129356,185641,191816,103850,122666,185897,191930,191960,122794,2829,192036,192077,192116,192153,192187,192219,192258,192295,192330,192362,192392,192429,192464,192497,192527,192555,192589,192621,192651,192678,192703,192735,192765,192793,192818,192841,133253,103884,192958,192992,193024,193063,193100,193135,193167,193197,193234,193269,193302,193332,193360,193394,193426,193456,193483,193508,193540,193570,193598,193623,193646,193687,193726,193763,193797,193829,193868,193905,193940,193972,194002,194039,194074,194107,194137,194165,194199,194231,194261,194288,194313,194345,194375,194403,194428,194451,194492,194531,194568,194602,194634,194673,194710,194745,194777,194807,194844,194879,194912,194942,194970,195004,195036,195066,195093,195118,195150,195180,195208,195233,195256,195297,195336,195373,195407,195439,195478,195515,195550,195582,195612,195649,195684,195717,195747,195775,195809,195841,195871,195898,195923,195955,195985,196013,196038,196061,196102,196141,196178,196212,196244,196283,196320,196355,196387,196417,196454,196489,196522,196552,196580,196614,196646,196676,196703,196728,196760,196790,196818,196843,196866,196907,196946,196983,197017,197049,197088,197125,197160,197192,197222,197259,197294,197327,197357,197385,197419,197451,197481,197508,197533,197565,197595,197623,197648,197671,197712,197751,197788,197822,197854,197893,197930,197965,197997,198027,198064,198099,198132,198162,198190,198224,198256,198286,198313,198338,198370,198400,198428,198453,254621,254661,254699,254734,254768,254806,254842,254875,254907,254942,254975,255005,255034,255068,255100,255129]
def base (q dB dC : Nat) : Nat :=
  if q<9 then body6 q dB dC else if q<16 then baseTab.getD (25*q+5*dB+dC) 0
  else if q=16 then body7Tab.getD dB 0 else baseTab.getD (425+4*dB+dC) 0
def partLen (q d : Nat) : Nat :=
  if d=mx q then 4 else if d+1=mx q then 5 else 4+2*(mx q-d)
def pcB (q dB dC : Nat) : Nat := base q dB dC+2*mx q+1
def pcC (q dB dC : Nat) : Nat := pcB q dB dC+partLen q dB
/-- r6 bodies omit chain C's copy when chains B and C both have the largest digit (C is buffer-safe). -/
def skipBody (q dB dC : Nat) : Bool := decide (q<9 ∧ dB=mx q ∧ dC=mx q)
/-- End of the body (next dispatch). The r7 pair (q = 16) has no chain C: its checksum dispatch is at `pcC`. -/
def pcX (q dB dC : Nat) : Nat :=
  if q=16 then pcC q dB dC else pcC q dB dC+partLen q dC-(if skipBody q dB dC then 4 else 0)
def entOff (q : Nat) : Nat :=
  if q=0 then 1315 else if q=1 then 1350 else if q=2 then 548 else if q=3 then 582
  else if q=4 then 804 else if q=5 then 838 else if q=6 then 1444 else if q=7 then 1478
  else if q=8 then 676 else if q=9 then 64 else if q=10 then 710 else if q=11 then 932
  else if q=12 then 966 else if q=13 then 1276 else if q=14 then 1532 else if q=15 then 764 else 1188
/-- First cell word of rank `k` in group `q`: r6 cells, #938's r5 column `1024 (125 - k) + entOff q`, the r7 pair in
#938's q8 column (`entOff 8 = 676`). -/
def cellW (q k : Nat) : Nat :=
  if q<9 then cell6 q (rawOf6 q k) else if q<16 then 1024*(125-k)+entOff q
  else if q=16 then 1024*(125-k)+entOff 8 else 0
def entW (q k : Nat) : Nat := cellW q k + (if q=9 ∧ k%2=0 then 1 else 0)
def inl (q : Nat) : Bool := decide (q=9 ∨ (13 ≤ q ∧ q ≤ 15))
def leadOff (q : Nat) : Nat := 1
def leadPc (q k : Nat) : Nat := entW q k+leadOff q
def kdig (q k j : Nat) : Nat := k/(mx q+1)^j%(mx q+1)
def kss (q k : Nat) : Nat := kdig q k 0+kdig q k 1+kdig q k 2
def rowInl (q k : Nat) : Bool := inl q || decide (9≤q ∧ q<16 ∧ 3≤kss q k)
def gbase (q k : Nat) : Nat :=
  if rowInl q k then
    (if kdig q k 0=mx q then leadPc q k+3-2*mx q
     else if kdig q k 0+1=mx q then leadPc q k+2-2*kdig q k 0
     else leadPc q k+3-2*kdig q k 0)
  else base q (kdig q k 1) (kdig q k 2)
/-- Shared-body groups: the r6 groups and the r7 pair. -/
def sharedG (q : Nat) : Bool := decide (q<9 ∨ q=16)
def skipA (q k : Nat) : Bool := decide (q=0 ∧ kdig q k 0=mx q)
def skipB (q k : Nat) : Bool := (rowInl q k || sharedG q) && decide (kdig q k 0=mx q ∧ kdig q k 1=mx q)
def skipC (q k : Nat) : Bool := (rowInl q k || decide (q<9)) && decide (kdig q k 1=mx q ∧ kdig q k 2=mx q)
/-- Start of chain B. Shared-body groups keep chain B's copy in the body; a buffer-safe chain B is jumped over (+4). -/
def gB (q k : Nat) : Nat :=
  if sharedG q then gbase q k+2*mx q+1+(if skipB q k then 4 else 0)
  else gbase q k+2*mx q+1-(if skipA q k then 4 else 0)
def gC (q k : Nat) : Nat := gB q k+partLen q (kdig q k 1)-(if skipB q k then 4 else 0)
/-- End of the group's code for rank `k` (the next dispatch); the r7 pair has no chain C. -/
def gX (q k : Nat) : Nat :=
  if q=16 then gC q k else gC q k+partLen q (kdig q k 2)-(if skipC q k then 4 else 0)
def headJD (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) o)).set .x12 (addC (addC (.reg rb) o) (gOut g))).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,5,5⟩
def headJDTerm (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg rb) o)).set .x25 (hLoad i d),
    [(kAt rb o 16,hLoad i d)],
    [.valid (kAt rb o 16) 8]⟩,.c (pcOf tgt),.jump,4,4⟩
def headJDF (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) : Result :=
  {headJD rb o tgt i d g with stop:=.fuel,steps:=4,cycles:=4}
def headJDTermF (rb : Reg) (o : Word) (tgt i d : Nat) : Result :=
  {headJDTerm rb o tgt i d with stop:=.fuel,steps:=3,cycles:=3}
def s8R (n p : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (addC (.reg .x24) (-BitVec.ofNat 64 n)),[],[]⟩,.c (pcOf (p+1)),.fuel,1,1⟩
/-- T51 group 0's first cell word `addi s8,zero,T-kss`. -/
def guardR (k : Nat) : Result :=
  ⟨⟨RegFile.init.set .x24 (.c (BitVec.ofNat 64 topT-BitVec.ofNat 64 (kss 0 k))),[],[]⟩,
    .c (pcOf (cellW 0 k+1)),.fuel,1,1⟩
def bge9R (p : Nat) : Result :=
  ⟨SymState.init,.ite .ge (.reg .x16) (.c 0) (.c (BitVec.ofNat 64 (0x1000+4*p-4096))) (.c (pcOf (p+1))),.branch,1,1⟩
def tailR (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 1 else 0
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (addC (.reg .x4) (BitVec.ofNat 64 (slotOffset a)))
      | none => RegFile.init), [], []⟩, .c (pcOf (p + n)), .ecall, n, n⟩
def headRHT (rb : Reg) (o : Word) (d sl p i : Nat) : Result :=
  {headRH rb o d (some sl) p i with pc:=.c (pcOf (p+4)),steps:=4,cycles:=4}
def shift12 (w : Reg) (b : Nat) : E :=
  if b<12 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (12-b)))
  else .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b-12)))
def dispatchR (q : Nat) : Result :=
  let sh := shift12 (if q<9 then .x16 else .x17) (if q<9 then 7*q else 7*q-64)
  let a := .bin .and sh (.reg .x6)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c (BitVec.ofNat 64 (2^64+4*entOff q-4096)))) (.c (~~~1#64)),.jump,3,3⟩
def dispatch9R : Result :=
  let a := .bin .and (.bin .sll (.reg .x17) (.c (BitVec.ofNat 64 13))) (.reg .x6)
  ⟨⟨RegFile.init.set .x14 a,[],[]⟩,
    .bin .and (.bin .add a (.c 256)) (.c (~~~1#64)),.jump,3,3⟩
/-- Field source of the dispatch into r6 group `h` (1..8): g1 = a6 bits 8..15 (no shift), g2..g6 = a6 >> 8(h-1),
g7 = a7 >> 40 (bits 112..119), g8 = a7 >> 48 (bits 120..127); masked with t4 = 0xFF00. -/
def r6Src (h : Nat) : E :=
  if h=1 then .reg .x16 else if h<7 then .bin .srl (.reg .x16) (.c (BitVec.ofNat 64 (8*h-8)))
  else if h=7 then .bin .srl (.reg .x17) (.c 40#64) else .bin .srl (.reg .x17) (.c 48#64)
/-- `a4 = s2 - 256 raw` (table B) or `256 raw + s2` (table A). -/
def r6A (h : Nat) : E :=
  if r6B h then .bin .sub (.reg .x18) (.bin .and (r6Src h) (.reg .x29))
  else .bin .add (.bin .and (r6Src h) (.reg .x29)) (.reg .x18)
/-- The jalr immediate of the dispatch into r6 group `h` (sign-extended): 4 (64 row0 + off - 212992). -/
def r6Imm (h : Nat) : Word :=
  if r6B h then BitVec.ofNat 64 (2^64+4*r6Off h-256) else BitVec.ofNat 64 (4*r6Off h)
def r6DispR (h : Nat) : Result :=
  ⟨⟨RegFile.init.set .x14 (r6A h),[],[]⟩,.bin .and (.bin .add (r6A h) (.c (r6Imm h))) (.c (~~~1#64)),.jump,
    (if h=1 then 3 else 4),(if h=1 then 3 else 4)⟩
/-- T51: the r6 mask word `0xFF00` is loaded by group 0's bodies (`ld t4,-288(s1)`: verify data word 16). -/
def maskE : E := .ld (.bin .add (.reg .x2) (.c (BitVec.ofNat 64 16)))
def g0A : E := .bin .sub (.c 856064#64) (.bin .and (.reg .x16) maskE)
/-- Group 0's next dispatch `ld t4,-288(s1); lui s2,209; and a4,a6,t4; sub a4,s2,a4; jalr -72(a4)` (into g1). -/
def g0DispR : Result :=
  ⟨⟨((RegFile.init.set .x29 maskE).set .x18 (.c 856064#64)).set .x14 g0A,[],
    [.valid ⟨some (.reg .x2),BitVec.ofNat 64 16⟩ 8]⟩,
    .bin .and (.bin .add g0A (.c (BitVec.ofNat 64 (2^64-72)))) (.c (~~~1#64)),.jump,5,5⟩
/-! ### T51 checksum chain 50
The r7 pair's bodies end with `addi a4,s8,89; slli a4,a4,11; jalr 1168(a4)`: with s8 = T - sum(d0..d49) it lands on
word `44836 + 512 s8`; `ckArm d` (d = s8 in 0..5) holds chain 50's code for digit d followed by the final tail at
`ckTail d` (#938's tail without its sum check); every other reachable s8 (sum <= 231) lands on a zero word. -/
def ckE : E := .bin .sll (.bin .add (.reg .x24) (.c 89#64)) (.c 11#64)
def ckDispR : Result :=
  ⟨⟨RegFile.init.set .x14 ckE,[],[]⟩,.bin .and (.bin .add ckE (.c 1168#64)) (.c (~~~1#64)),.jump,3,3⟩
def ckArm (d : Nat) : Nat := 44836+512*d
def ckTail (d : Nat) : Nat := ckArm d+partLen 17 d
/-- Landing word of the checksum dispatch for data digit sum `ds` (s8 = topT - ds). -/
def ckWord (ds : Nat) : Nat := 44836+512*topT-512*ds
/-- The dispatch at the end of top group `q`: q = 0 the 5-word g1 dispatch (mask/table setup), r6 groups into the
next r6 group, g8 into q9 (#938's dispatch9), q9..q14 into q+1, q15 into the r7 pair (#938's dispatch into group 8),
the r7 pair into the checksum arms. -/
def nextDispR (q : Nat) : Result :=
  if q=0 then g0DispR else if q<8 then r6DispR (q+1) else if q=8 then dispatch9R
  else if q<15 then dispatchR (q+1) else if q=15 then dispatchR 8 else ckDispR
def rungsOK (q d0 sl p : Nat) : Bool :=
  (List.range' d0 (mx q-d0)).all fun m =>
    rOK (vrun (p+2*(m-d0)) 3)
      (rungR m (if m+1=mx q then some sl else none) (p+2*(m-d0)))
def tailsOK (q sl p : Nat) : Bool :=
  (List.range (mx q)).all fun m =>
    rOK (vrun (p+2*m+1) 2) (tailR (if m+1=mx q then some sl else none) (p+2*m+1))
def partOK (q i d p : Nat) (skip : Bool := false) : Bool :=
  if d=mx q then (if skip then rOK (vrun p 0) (emptyR p) else rOK (vrun p 4) (copyFH .x8 (off i) (slot i) p (topG i)))
  else rOK (vrun p 8)
      (if d+1=mx q then headRHT .x8 (off i) d (slot i) p i
       else headRH .x8 (off i) d none p i (topG i)) &&
    rungsOK q (d+1) (slot i) (p+5)
def s8Check (q k : Nat) : Bool :=
  (if q=0 then rOK (vrun (entW 0 k) 1) (guardR k) else rOK (vrun (entW q k) 1) (s8R (kss q k) (entW q k))) &&
  (if q=9 ∧ k%2=0 then rOK (vrun (cellW 9 k) 1) (bge9R (cellW 9 k)) else true)
def dispatchOK (q dB dC : Nat) : Bool :=
  if q<17 then rOK (vrun (pcX q dB dC) 5) (nextDispR q) else true
/-- A shared body: chain A's rung ladder (tails and rungs; its terminal step targets `termSlot`), chain B, chain C
(absent for the r7 pair), the next dispatch. -/
def blockCheck (q dB dC : Nat) : Bool :=
  tailsOK q (termSlot (3*q)) (base q dB dC) &&
  rungsOK q 0 (termSlot (3*q)) (base q dB dC) &&
  partOK q (3*q+1) dB (pcB q dB dC) &&
  (decide (q=16) || partOK q (3*q+2) dC (pcC q dB dC) (skipBody q dB dC)) && dispatchOK q dB dC
def inlineCheck (q k : Nat) : Bool :=
  let dA := kdig q k 0
  s8Check q k &&
  (if dA=mx q then
    (if skipA q k then rOK (vrun (leadPc q k) 0) (emptyR (leadPc q k))
     else rOK (vrun (leadPc q k) 4) (copyFH .x8 (off (3*q)) (slot (3*q)) (leadPc q k) (topG (3*q))))
   else
    rOK (vrun (leadPc q k) (if dA+1=mx q then 3 else 4))
      (if dA+1=mx q then headJDTermF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
       else headJDF .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA (topG (3*q))) &&
    rOK (vrun (gbase q k+2*dA+1) 2)
      (tailR (if dA+1=mx q then some (termSlot (3*q)) else none) (gbase q k+2*dA+1)) &&
    rungsOK q (dA+1) (termSlot (3*q)) (gbase q k+2*(dA+1))) &&
  partOK q (3*q+1) (kdig q k 1) (gB q k) (skipB q k) && partOK q (3*q+2) (kdig q k 2) (gC q k) (skipC q k) &&
  rOK (vrun (gX q k) 5) (nextDispR q)
def entCheck (q k : Nat) : Bool :=
  if rowInl q k then inlineCheck q k else
  let dA := kdig q k 0
  if dA=mx q then
    (if q=0 then rOK (vrun (leadPc q k) 1) (T3M.skipJB (gB q k))
     else rOK (vrun (leadPc q k) 7) (copyN .x8 (off (3*q)) (slot (3*q)) (gB q k) (topG (3*q))))
  else rOK (vrun (leadPc q k) 7)
    (if dA+1=mx q then headJDTerm .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA
     else headJD .x8 (off (3*q)) (gbase q k+2*dA+1) (3*q) dA (topG (3*q)))
/-- Live shared blocks: every block of an r6 group; the r7 pair's 7 bodies (`x = dB`); for #938's non-inline r5
groups only the blocks with `dB + dC < 3` (a row with `kss ≥ 3` is inline; the dead blocks are not checked). -/
def liveBlock (q x : Nat) : Bool :=
  if q=16 then blockCheck 16 x 0
  else if q<9 ∨ x/(mx q+1)+x%(mx q+1) < 3 then blockCheck q (x/(mx q+1)) (x%(mx q+1)) else true
/-- Number of ranks of group `q` (`216` r6, `125` r5, `49` the r7 pair). -/
def nRank (q : Nat) : Nat := if q=16 then 49 else (mx q+1)^3
/-- Number of shared-body indices of group `q` (`(mx+1)^2`; the r7 pair: 7, indexed by `dB`). -/
def nBlock (q : Nat) : Nat := if q=16 then 7 else (mx q+1)^2
def tripleCheck (q : Nat) : Bool :=
  ((List.range (nRank q)).all fun k => entCheck q k && s8Check q k) &&
  ((List.range (nBlock q)).all (liveBlock q))
def inlineGroupCheck (q lo n : Nat) : Bool := (List.range' lo n).all fun k => inlineCheck q k
/-! ### T51 guards -/
/-- The word at `p` is zero (an illegal instruction: fetch faults). -/
def zeroAt (p : Nat) : Bool := (lcode p).head? == some 0#32
def raw6Valid (g raw : Nat) : Bool := if g=0 then decide (40≤raw) else decide (raw<216)
/-- Invalid r6 fields (g = 0: raw 3..39; g >= 1: raw 216..255) land on zero words (g = 0, raw < 3: below the code). -/
def guard6Check (g raw : Nat) : Bool := raw6Valid g raw || (g=0 && decide (raw<3)) || zeroAt (cell6 g raw)
def guard6All (g : Nat) : Bool := (List.range 256).all (guard6Check g)
/-- Invalid r7 ranks 49..125 land on zero words (126, 127 land below the code). -/
def r7GuardCheck (k : Nat) : Bool := decide (k<49) || zeroAt (cellW 16 k)
def r7GuardAll : Bool := (List.range 126).all r7GuardCheck
/-- Reachable checksum landings (data sum <= 231) outside the 6 arms are zero words. -/
def ckGuardCheck (ds : Nat) : Bool := decide (topT-5≤ds ∧ ds≤topT) || zeroAt (ckWord ds)
def ckGuardAll : Bool := (List.range 232).all ckGuardCheck
def ckArmCheck (d : Nat) : Bool := partOK 17 50 d (ckArm d)
def ckArmAll : Bool := (List.range 6).all ckArmCheck
theorem piece_steps45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<257181) (s : MachineState) (hpc : s.pc=pcOf p)
    (ho : ∀o∈r.st.obl,o.holds s) :
    Steps Images.verifyImage s r.steps r.cycles (r.toState s) := by
  exact symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)
theorem piece_ecall45 {p f : Nat} {r : Result} (h : vrun p f=some r)
    (hp : p<257181) (s : MachineState) (ho : ∀o∈r.st.obl,o.holds s)
    (hst : r.stop=.ecall) :
    fetch Images.verifyImage (r.toState s)=some (.base .ECALL) := by
  exact symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst
end SigGolfCandidate.T3M.Nonbinary
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsSem ====
section

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
structure NCtx where
  w : ClaudeWCT.W9.T3M.WBytes
  tree : Nat
  leaf : Nat
  S3 : Nat
  digits : Nat → Nat
  ret : Nat
namespace NCtx
/-- Charge 86: chain `i`'s block (`= WIT + chainBlock 0 i` for `S3 = 14128`). -/
def blk (c : NCtx) (i : Nat) : Nat := c.S3 - 1664 + topSlot i
/-- Address of the supplied value (G: block start, F: block + 48). -/
def vAt (c : NCtx) (i : Nat) : Nat := c.blk i + 48 * (i % 2)
/-- Hash destination of an interior step (G: block - 16, so the high half lands on the value; F: block + 48). -/
def oAt (c : NCtx) (i : Nat) : Nat := c.blk i + 64 * (i % 2) - 16
/-- The two pads (G: +32, +48; F: +0, +32). -/
def pad0At (c : NCtx) (i : Nat) : Nat := c.blk i + 32 - 32 * (i % 2)
def pad1At (c : NCtx) (i : Nat) : Nat := c.blk i + 48 - 16 * (i % 2)
def dig (c : NCtx) (i : Nat) : Nat := c.digits i
/-- Campaign T51: largest digit of top chain `i` (`= T3.maxDigit 0 i`): r6 groups q < 9 (chains 0..26) 5, r5 groups
9 <= q < 16 (chains 27..47) 4, the r7 pair (group 16, chains 48/49) 6, the checksum chain 50 (`mx 17`) 5. -/
def topMax (i : Nat) : Nat := if i < 50 then mx (i / 3) else mx 17
def last (i : Nat) : Nat := topMax i - 1
/-- The half of the step-`m` answer the image keeps (`= WCT9.chainHigh 0 i m`): G chains keep the high half on
interior steps; campaign T51 (PIN v1): chain 0 keeps it on its terminal step too (answer at `slot 0 - 16`). -/
def topHigh (i m : Nat) : Bool := topG i && (decide (m + 1 < topMax i) || decide (i = 0))
def «prefix» (c : NCtx) : Nat := 128 + 193 * 2 ^ 56 + ((c.tree * 2 ^ 12 + c.leaf) % 2 ^ 32) * 2 ^ 16
def w0 (c : NCtx) (i : Nat) : Nat := c.prefix + i
def w1 (c : NCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad0At i - Verify.WIT)
def pad1 (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad1At i - Verify.WIT)
def padHeader (c : NCtx) (i : Nat) : Word := (ClaudeWCT.W9.T3M.wdig c.w (c.blk i - Verify.WIT + 16)).extractLsb' 64 64
def val (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.vAt i - Verify.WIT)
def ok (c : NCtx) : Prop :=
  c.tree = 0 ∧ c.leaf < 4096 ∧ c.S3 % 8 = 0 ∧ Verify.WIT + 8336 + 1664 ≤ c.S3 ∧ c.S3 + 2064 ≤ 0x5000 ∧
    c.ret < 209920
def known (c : NCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x30, 7), (.x28, BitVec.ofNat 64 (c.prefix + 385)), (.x8, BitVec.ofNat 64 c.S3), (.x2, BitVec.ofNat 64 0xffbde0), (.x4, 24704)]
/-- Rank of top group `q`: the digit triple in radix `mx q + 1`; group 16 (the r7 pair, chains 48 and 49) has only two
digits, `d48 + 7 d49`. -/
def kOf (c : NCtx) (q : Nat) : Nat :=
  if q = 16 then c.dig 48 + 7*c.dig 49 else
  c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2)
def qb (c : NCtx) (i : Nat) : Nat := gbase (i/3) (c.kOf (i/3))
def qB (c : NCtx) (i : Nat) : Nat := gB (i/3) (c.kOf (i/3))
def qC (c : NCtx) (i : Nat) : Nat := gC (i/3) (c.kOf (i/3))
def qX (c : NCtx) (i : Nat) : Nat := gX (i/3) (c.kOf (i/3))
def entPc (c : NCtx) (q : Nat) : Nat := entW q (c.kOf q)
/-- Buffer-safe chain (`= WCT9.safeZeroCopy 0`): its value already sits in its leaf slot. The checksum chain 50 is
never buffer-safe (its arm always copies). -/
def bufferSafe (c : NCtx) (i : Nat) : Prop :=
  c.dig i = topMax i ∧
    (i = 0 ∨ (0 < i ∧ i % 3 ≠ 0 ∧ i ≠ 50 ∧ c.dig (i-1) = topMax (i-1)))
instance (c : NCtx) (i : Nat) : Decidable (c.bufferSafe i) := by
  unfold bufferSafe; infer_instance
/-- End of the leaf-buffer bytes written by chains `1 .. i-1` (endpad leaf: chain `j >= 1` writes `[slot j, slot j +
16)` (copy) or `[slot j, slot j + 32)` (terminal hash, junk high half on `slot (j+1)`)). -/
def bufferEnd (c : NCtx) (i : Nat) : Nat :=
  slot i + (if 1 < i ∧ c.dig (i-1) ≠ topMax (i-1) then 16 else 0)
def bufferOrig (c : NCtx) (s0 : MachineState) : Prop :=
  ∀ i, i < 51 → ∀ k < 2, OrigW c.w s0 (slot i + 8*k)
def bufferVal (c : NCtx) (i : Nat) : Digest :=
  if c.bufferSafe i then ClaudeWCT.W9.T3M.wdig c.w (slot i - Verify.WIT) else c.val i
/-- Start of chain `i`. Campaign T51: chains `i < 50` sit in group `i / 3` (lead chain in the cell, B/C in the body;
group 16 = the r7 pair, chain 48 lead, chain 49 = its chain B); the checksum chain 50 starts at its arm
`ckArm d50`. -/
def startPc (c : NCtx) (i : Nat) : Nat :=
  if i < 50 then (if i%3=0 then leadPc (i/3) (c.kOf (i/3)) else if i%3=1 then c.qB i else c.qC i)
  else ckArm (c.dig 50)
def rungPc (c : NCtx) (i m : Nat) : Nat :=
  if i%3=0 ∧ i < 50 then c.qb i+2*m
  else c.startPc i + (if c.dig i = last i then 2 else 3) + 2*(m-c.dig i)
/-- End of chain `i`. Chain 49 (the r7 pair's chain B) ends at `qC 49` (= the checksum dispatch); the checksum chain 50
(never buffer-safe) ends at the final tail `ckTail d50`. -/
def endPc (c : NCtx) (i : Nat) : Nat :=
  if i < 50 then (if i%3=0 then c.qB i else if i%3=1 then c.qC i else c.qX i)
  else ckTail (c.dig 50)
/-- Bytes written before chain `i` (charge 86): the leaf buffer (chains `1 .. i-1` from `slot 1` on; chain 0 at most
`[slot 0 - 16, slot 0 + 16)`, never the tweak `[slot 0 + 16, slot 1)`), the pairs `p < i / 2` (the F chain of pair `p`
spills its junk 16 bytes into pair `p - 1`, chain 1 past the area), and the G half `[pair, pair + 40)` of pair `i / 2`
when `i` is odd. -/
def Wr (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  (slot 1 ≤ A ∧ A < c.bufferEnd i) ∨ (0 < i ∧ slot 0 - 16 ≤ A ∧ A < slot 0 + 16) ∨
    (c.S3 + 104 * (27 - i / 2) ≤ A + 1664 ∧ A < c.S3 + 1160) ∨
    (i % 2 = 1 ∧ c.S3 + 104 * (26 - i / 2) ≤ A + 1664 ∧ A + 1664 < c.S3 + 104 * (26 - i / 2) + 40)
/-- Chain `i`'s own writes: its header word and the 32-byte destination of its interior steps. -/
def WrIn (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 24) ∨ (c.oAt i ≤ A ∧ A < c.oAt i + 32)
def Orig0 (c : NCtx) (s0 : MachineState) : Prop :=
  ((∀ i, i < 51 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ c.bufferOrig s0) ∧ Verify.DataOK s0
def Base (c : NCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
def ChainIn (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i ∧ s.pc = pcOf (c.startPc i)
def HdrOk (c : NCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 8 = 128 + i ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i
def StepInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i ∧
    c.HdrOk i s ∧ DigAt s (c.vAt i) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    (m < last i → s.getReg .x12 = BitVec.ofNat 64 (c.oAt i)) ∧ s.pc = pcOf (c.rungPc i m)
def PreHash (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i ∧ DigAt t (c.vAt i) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = last i then termSlot i else c.oAt i) ∧
    t.pc = pcOf (c.rungPc i m + (if m = last i then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)
def EndInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 ∧ s.pc = pcOf (c.endPc i)
theorem topSlot_props (i : Nat) (hi : i < 51) : topSlot i % 8 = 0 ∧ 16 ≤ topSlot i ∧ topSlot i + 64 ≤ 2808 := by
  unfold topSlot; omega
theorem topG_eq (i : Nat) : topG i = T3.topIsG i := by simp [topG, T3.topIsG]
theorem topG_isG (i : Nat) : topG i = ClaudeWCT.WCT9.isG 0 i := by rw [ClaudeWCT.WCT9.isG_top_eq, topG_eq]
theorem topG_lt (i : Nat) (hi : i < 51) : topG i = decide (i % 2 = 0) := by
  unfold topG; by_cases h : i % 2 = 0 <;> simp [h] <;> omega
theorem topSlot_eq (i : Nat) : topSlot i = ClaudeWCT.W9.T3M.chainSlot 0 i := by
  unfold topSlot ClaudeWCT.W9.T3M.chainSlot; simp only [Fin.val_zero, if_true]; split <;> omega
theorem blk_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    c.blk i % 8 = 0 ∧ Verify.WIT + 8352 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x5000 := by
  obtain ⟨-, -, h64, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold blk Verify.WIT at *; refine ⟨?_, ?_, ?_⟩ <;> omega
/-- Chain `i`'s block lies in pair `i / 2` (`[pair, pair + 104)` with `pair = S3 - 1664 + 104 (26 - i / 2)`). -/
theorem blk_eq (c : NCtx) (i : Nat) (hi : i < 51) :
    c.blk i = c.S3 - 1664 + 104 * (26 - i / 2) + 16 + 24 * (i % 2) := by
  unfold blk topSlot; omega
theorem vAt_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    c.vAt i % 8 = 0 ∧ c.vAt i = c.blk i + 48 * (i % 2) := by
  have hb := c.blk_props hc i hi
  unfold vAt; omega
theorem oAt_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    c.oAt i % 8 = 0 ∧ Verify.WIT + 8336 ≤ c.oAt i ∧ c.oAt i + 32 ≤ 0x5000 ∧
      c.oAt i + 16 = c.blk i + 64 * (i % 2) := by
  have hb := c.blk_props hc i hi
  unfold oAt; omega
theorem oAt_G (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (hg : topG i = true) : c.oAt i + 16 = c.vAt i := by
  have hb := c.blk_props hc i hi
  rw [topG_lt i hi] at hg; simp at hg
  unfold oAt vAt; omega
theorem oAt_F (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (hg : topG i = false) : c.oAt i = c.vAt i := by
  have hb := c.blk_props hc i hi
  rw [topG_lt i hi] at hg; simp at hg
  unfold oAt vAt; omega
/-- `topMax` is the scheme's top `maxDigit` (T51: 5 / 4 / 6 / 5). -/
theorem topMax_eq (i : Nat) : topMax i = maxDigit 0 i := by
  unfold topMax mx maxDigit
  simp only [ite_true]
  split_ifs <;> omega
theorem topHigh_eq (i m : Nat) : topHigh i m = ClaudeWCT.WCT9.chainHigh 0 i m := by
  rw [ClaudeWCT.WCT9.chainHigh_top_eq]
  unfold topHigh T3.topChainHigh
  rw [topG_eq, topMax_eq]
/-- Campaign T51 (endpad leaf): `slot 0 = 25216` (end_0), the tweak at 25232, `slot i = 25232 + 16 i` for `i >= 1`
(the checksum chain's 32-byte terminal HASH output ends at 26064). -/
theorem slot_props (i : Nat) (hi : i < 51) : slot i % 16 = 0 ∧ 25216 ≤ slot i ∧ slot i + 32 ≤ 26064 := by
  unfold slot; split <;> omega
theorem slot0 : slot 0 = 25216 := rfl
theorem slot1 : slot 1 = 25248 := rfl
theorem slot_pos (i : Nat) (hi : 0 < i) : slot i = 25232 + 16 * i := by
  unfold slot; rw [if_neg (by omega)]
theorem slot_succ (i : Nat) (hi : 0 < i) : slot (i + 1) = slot i + 16 := by
  rw [slot_pos i hi, slot_pos (i + 1) (by omega)]; ring
/-- Destination of chain `i`'s terminal hash (`termSlot`, ChainsLayout): its leaf slot; chain 0 (high half kept)
writes at `slot 0 - 16`, so its junk low half lands on the dead L1 leaf-buffer tail and the leaf tweak
`[slot 0 + 16, slot 1)` is untouched. -/
theorem termSlot_props (i : Nat) (hi : i < 51) :
    termSlot i % 16 = 0 ∧ 25200 ≤ termSlot i ∧ termSlot i + 32 ≤ 26064 ∧ (i = 0 → termSlot i + 16 = slot 0) ∧
      (0 < i → termSlot i = slot i) := by
  unfold termSlot slot; split_ifs <;> omega
theorem base_off (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S3 + (off i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold off blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S3 + topSlot i - 1664 = c.S3 - 1664 + topSlot i by
    omega]
theorem base_off0 (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) :
    BitVec.ofNat 64 c.S3 + off i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold off blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S3 + topSlot i - 1664 = c.S3 - 1664 + topSlot i by
    omega]
/-- The hash destination register of an interior step (`gOut`). -/
theorem oAt_eval (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 51) (x : Word) (hx : x = BitVec.ofNat 64 (c.blk i)) :
    x + gOut (topG i) = BitVec.ofNat 64 (c.oAt i) := by
  have hb := c.blk_props hc i hi
  subst hx
  rw [topG_lt i hi]
  unfold oAt
  by_cases h : i % 2 = 0
  · simp only [h, decide_true]
    rw [show gOut true = BitVec.ofNat 64 18446744073709551600 by unfold gOut; rfl, BitVec.ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show c.blk i + 18446744073709551600 = (c.blk i + 64 * 0 - 16) + 2^64 by
      omega, Nat.add_mod_right]
  · simp only [h, decide_false]
    rw [show gOut false = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
    congr 1; omega
theorem prefix_props (c : NCtx) : c.prefix % 2 ^ 16 = 128 ∧ c.prefix < 2 ^ 64 := by
  have h := Nat.mod_lt (c.tree * 2 ^ 12 + c.leaf) (by norm_num : 0 < 2 ^ 32)
  unfold «prefix»
  constructor <;> omega
theorem w0_lt (c : NCtx) (i m : Nat) (hi : i < 51) (hm : m < 256) : c.w0 i + 2 ^ 8 * m < 2 ^ 64 := by
  have h := Nat.mod_lt (c.tree * 2 ^ 12 + c.leaf) (by norm_num : 0 < 2 ^ 32)
  unfold w0 «prefix»; omega
theorem w0_header (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 51) (hm : m < 8) :
    BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) = (chainHeader 0 c.tree c.leaf i m).extractLsb' 0 64 := by
  rw [chainHeader_low_bounded _ _ _ _ _ (by omega) hm
    (by rw [hc.1]; decide +kernel) hc.2.1]
  congr 1
  simp only [w0, «prefix», packedPrefix, packedHi, show height 0 = 12 from rfl, Fin.val_zero,
    Nat.zero_mul, Nat.add_zero]
  ring
set_option maxRecDepth 20000 in
theorem chain_hashInput (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 51) (hm : m < 8) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.pad0At i) (c.pad0 i)) (hp1 : DigAt t (c.pad1At i) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i)
    (hv : DigAt t (c.vAt i) v) :
    hashInput t = toQ (chainInputL 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i)) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputL_length _ _ _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputL, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two]
  rw [topG_lt i hi]
  by_cases hg : i % 2 = 0
  · have ev : c.vAt i = c.blk i := by unfold vAt; omega
    have e0 : c.pad0At i = c.blk i + 32 := by unfold pad0At; omega
    have e1 : c.pad1At i = c.blk i + 48 := by unfold pad1At; omega
    rw [ev] at hv; rw [e0] at hp0; rw [e1] at hp1
    rw [if_pos (by simpa using hg)]
    rw [hv.1, hv.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp0.1, hp0.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hp1.1, hp1.2, w0_header c hc i m hi hm]
    rfl
  · have h1 : i % 2 = 1 := by omega
    have ev : c.vAt i = c.blk i + 48 := by unfold vAt; omega
    have e0 : c.pad0At i = c.blk i := by unfold pad0At; omega
    have e1 : c.pad1At i = c.blk i + 32 := by unfold pad1At; omega
    rw [ev] at hv; rw [e0] at hp0; rw [e1] at hp1
    rw [if_neg (by simpa using hg)]
    rw [hp0.1, hp0.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_header c hc i m hi hm]
    rfl
/-- On the top layer the format of chain `i` is `topG i` (`= WCT9.isG 0 i`). -/
theorem chainInputL_top (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest) :
    chainInputL 0 tree leaf i step p0 p1 headerPad v (topG i) =
      ClaudeWCT.W9.T3M.chainInputPW 0 tree leaf i step p0 p1 headerPad v := by
  unfold chainInputL ClaudeWCT.W9.T3M.chainInputPW; rw [topG_isG]
theorem orig_frame {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : i < 51) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := c.blk_props hc i hi
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1.1 i hi k hk
/-- No chain processed before chain `i` (nor a buffer write) touched chain `i`'s block. -/
theorem notWr_block (c : NCtx) (hc : c.ok) {i A : Nat} (hi : i < 51) (h1 : c.blk i ≤ A) (h2 : A < c.blk i + 64) :
    ¬ c.Wr i A := by
  have hb := c.blk_props hc i hi
  have he := c.blk_eq i hi
  have hlo := hc.2.2.2.1
  unfold Wr
  rw [slot0, slot1]
  omega
theorem dig_at {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i A : Nat} (hi : i < 51) (hA1 : c.blk i ≤ A) (hA2 : A + 16 ≤ c.blk i + 64)
    (hA8 : (A - c.blk i) % 8 = 0) (hW0 : ¬ W A) (hW1 : ¬ W (A + 8)) :
    DigAt t A (ClaudeWCT.W9.T3M.wdig c.w (A - Verify.WIT)) := by
  have hb := c.blk_props hc i hi
  have e0 : c.blk i + 8 * ((A - c.blk i) / 8) = A := by omega
  have e1 : c.blk i + 8 * ((A - c.blk i) / 8 + 1) = A + 8 := by omega
  have o0 := orig_frame hF h0 hc hi (k := (A - c.blk i) / 8) (by omega) (by rw [e0]; exact hW0)
  have o1 := orig_frame hF h0 hc hi (k := (A - c.blk i) / 8 + 1) (by omega) (by rw [e1]; exact hW1)
  rw [e0] at o0; rw [e1] at o1
  exact DigAt_origW o0 o1 (by omega)
theorem pads_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : i < 51) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.pad0At i) (c.pad0 i) ∧ DigAt t (c.pad1At i) (c.pad1 i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ A, c.blk i ≤ A → A < c.blk i + 64 → (A < c.blk i + 16 ∨ c.blk i + 24 ≤ A) →
      (i % 2 = 0 → c.blk i + 16 ≤ A) → (i % 2 = 1 → A < c.blk i + 48) → ¬ c.WrIn i A := by
    intro A h1 h2 h3 h4 h5 hw
    rcases hw with hw | hw | hw
    · exact c.notWr_block hc hi h1 h2 hw
    · omega
    · unfold oAt at hw; omega
  unfold pad0 pad1
  have e0 : c.pad0At i = c.blk i + 32 - 32 * (i % 2) := rfl
  have e1 : c.pad1At i = c.blk i + 48 - 16 * (i % 2) := rfl
  rw [e0, e1]
  refine ⟨dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))
      (nW _ (by omega) (by omega) (by omega) (by omega) (by omega)),
    dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))
      (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))⟩
theorem val_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : i < 51)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.vAt i) (c.val i) := by
  have hb := c.blk_props hc i hi
  unfold val
  have ev : c.vAt i = c.blk i + 48 * (i % 2) := rfl
  rw [ev]
  exact dig_at hF h0 hc hi (by omega) (by omega) (by omega) (c.notWr_block hc hi (by omega) (by omega))
    (c.notWr_block hc hi (by omega) (by omega))
theorem topMax_bounds (i : Nat) : 3 ≤ topMax i ∧ topMax i ≤ 7 := by
  unfold topMax mx; split_ifs <;> omega
theorem topMax_mx (i : Nat) (hi : i < 50) : topMax i = mx (i / 3) := by
  unfold topMax; rw [if_pos hi]
theorem topMax_ck : topMax 50 = mx 17 := rfl
theorem topMax_r6 (i : Nat) (hi : i < 27) : topMax i = 5 := by
  unfold topMax mx; rw [if_pos (by omega), if_pos (by omega)]
theorem topMax_r5 (i : Nat) (h1 : 27 ≤ i) (hi : i < 48) : topMax i = 4 := by
  unfold topMax mx; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
theorem topMax_r7 (i : Nat) (h1 : 48 ≤ i) (hi : i < 50) : topMax i = 6 := by
  unfold topMax mx; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
theorem topMax_50 : topMax 50 = 5 := rfl
theorem last_bounds (i : Nat) : 2 ≤ last i ∧ last i ≤ 6 := by
  have := topMax_bounds i; unfold last; omega
theorem rungPc_succ (c : NCtx) (i m : Nat) (hd : c.dig i ≤ m) :
    c.rungPc i (m+1) = c.rungPc i m+2 := by
  unfold rungPc; split_ifs <;> omega
def DigitsOk (c : NCtx) : Prop := ∀i,i<51 → c.dig i ≤ topMax i
/-- Digits of the triple groups `q < 16` (chains `3q .. 3q+2 < 48`). -/
theorem dig_group_le (c : NCtx) (hd : c.DigitsOk) (q k : Nat) (hq : q<16) (hk : k<3) :
    c.dig (3*q+k) ≤ mx q := by
  have h := hd (3*q+k) (by omega)
  rwa [topMax_mx _ (by omega), show (3*q+k)/3=q by omega] at h
theorem kOf_triple (c : NCtx) (q : Nat) (hq : q<16) :
    c.kOf q = c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2) := by
  unfold kOf; rw [if_neg (by omega)]
theorem kOf_lt (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.kOf q < (mx q+1)^3 := by
  have h0 := c.dig_group_le hd q 0 hq (by decide +kernel)
  have h1 := c.dig_group_le hd q 1 hq (by decide +kernel)
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  simp only [Nat.add_zero] at h0
  rw [c.kOf_triple q hq]
  unfold mx at *
  split_ifs at * <;> omega
theorem kOf_digits (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.kOf q%(mx q+1)=c.dig (3*q) ∧
    c.kOf q/(mx q+1)%(mx q+1)=c.dig (3*q+1) ∧
    c.kOf q/(mx q+1)^2=c.dig (3*q+2) := by
  have h0 := c.dig_group_le hd q 0 hq (by decide +kernel)
  have h1 := c.dig_group_le hd q 1 hq (by decide +kernel)
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  simp only [Nat.add_zero] at h0
  rw [c.kOf_triple q hq]
  unfold mx at *
  split_ifs at * <;> exact ⟨by omega,by omega,by omega⟩
/-- The r7 pair (group 16): rank `d48 + 7 d49 < 49`. -/
theorem kOf16_lt (c : NCtx) (hd : c.DigitsOk) : c.kOf 16 < 49 := by
  have h0 := hd 48 (by omega); have h1 := hd 49 (by omega)
  rw [topMax_r7 48 (by omega) (by omega)] at h0; rw [topMax_r7 49 (by omega) (by omega)] at h1
  unfold kOf; rw [if_pos rfl]; omega
theorem kdig_kOf16 (c : NCtx) (hd : c.DigitsOk) :
    kdig 16 (c.kOf 16) 0=c.dig 48 ∧ kdig 16 (c.kOf 16) 1=c.dig 49 ∧ kdig 16 (c.kOf 16) 2=0 := by
  have h0 := hd 48 (by omega); have h1 := hd 49 (by omega)
  rw [topMax_r7 48 (by omega) (by omega)] at h0; rw [topMax_r7 49 (by omega) (by omega)] at h1
  have hm : mx 16 = 6 := rfl
  have hk : c.kOf 16 = c.dig 48 + 7*c.dig 49 := by unfold kOf; rw [if_pos rfl]
  unfold kdig; rw [hm, hk]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Nat.reduceAdd, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;> omega
theorem kdig_kOf (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<16) :
    kdig q (c.kOf q) 0=c.dig (3*q) ∧ kdig q (c.kOf q) 1=c.dig (3*q+1) ∧ kdig q (c.kOf q) 2=c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hd q hq
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  unfold kdig
  simp only [pow_zero,Nat.div_one,pow_one]
  refine ⟨k1,k2,?_⟩
  rw [k3]; exact Nat.mod_eq_of_lt (by omega)
theorem bufferEnd_bounds (c : NCtx) (i : Nat) :
    slot i ≤ c.bufferEnd i ∧ c.bufferEnd i ≤ slot i + 16 := by
  unfold bufferEnd; split <;> omega

theorem bufferEnd_mono (c : NCtx) (i : Nat) : c.bufferEnd i ≤ c.bufferEnd (i+1) := by
  have h := c.bufferEnd_bounds i
  have h' := c.bufferEnd_bounds (i+1)
  by_cases h0 : i = 0
  · subst h0; rw [slot0] at h; rw [slot1] at h'; omega
  · have := slot_succ i (by omega); omega

theorem Wr_mono (c : NCtx) (i : Nat) :
    ∀ A, c.Wr i A → c.Wr (i+1) A := by
  intro A h
  have hm := c.bufferEnd_mono i
  unfold Wr at *
  rcases h with h | h | h | h
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; left; omega

/-- Chain `i`'s own writes are among the writes before chain `i + 1`. -/
theorem WrIn_next (c : NCtx) (hc : c.ok) (i A : Nat) (hi : i < 51) (h : c.WrIn i A) : c.Wr (i+1) A := by
  have hlo := hc.2.2.2.1
  rcases h with h | h | h
  · exact c.Wr_mono i A h
  · have he := c.blk_eq i hi
    unfold Wr; right; right
    by_cases h2 : i % 2 = 0
    · right; omega
    · left; omega
  · have he := c.blk_eq i hi
    unfold oAt at h
    unfold Wr; right; right
    by_cases h2 : i % 2 = 0
    · right; omega
    · left; omega

theorem Wr_copy (c : NCtx) (i A : Nat)
    (hlo : slot i ≤ A) (hhi : A < slot i + 16) : c.Wr (i+1) A := by
  have h := c.bufferEnd_bounds (i+1)
  unfold Wr slot at *
  split_ifs at * <;> omega

/-- Chain `i`'s terminal hash (32 bytes at `termSlot i`) is among the writes before chain `i + 1`. -/
theorem Wr_hash (c : NCtx) (i A : Nat) (hn : c.dig i ≠ topMax i)
    (hlo : termSlot i ≤ A) (hhi : A < termSlot i + 32) : c.Wr (i+1) A := by
  by_cases h0 : i = 0
  · subst h0
    unfold Wr; right; left
    unfold termSlot at hlo hhi; rw [slot0] at *; simp at hlo hhi; omega
  · have he : c.bufferEnd (i+1) = slot (i+1)+16 := by
      simp [bufferEnd, hn, show 1 < i + 1 by omega]
    unfold termSlot at hlo hhi; rw [if_neg h0] at hlo hhi
    have hs := slot_succ i (by omega)
    have hs1 : slot 1 ≤ slot i := by unfold slot; split_ifs <;> omega
    unfold Wr; left; omega

theorem bufferSafe_end (c : NCtx) (i : Nat) (hs : c.bufferSafe i) :
    c.bufferEnd i = slot i := by
  rcases hs.2 with h | h
  · simp [bufferEnd, h]
  · simp [bufferEnd, h.2.2.2]

theorem bufferSafe_protected (c : NCtx) (i A : Nat) (hs : c.bufferSafe i)
    (hb : c.S3 + 1160 ≤ slot 0) (ha : slot i ≤ A) : ¬ c.Wr i A := by
  rw [Wr, c.bufferSafe_end i hs]
  by_cases hi : i = 0
  · subst hi; rw [slot0, slot1] at *; omega
  · have h1 := slot_pos i (by omega)
    rw [slot0, slot1] at *; omega

theorem bufferVal_at {c : NCtx} {s0 t : MachineState} (h0 : c.bufferOrig s0)
    {i : Nat} (hi : i < 51) (hs : c.bufferSafe i)
    (hb : c.S3 + 1160 ≤ slot 0) (hF : Frame s0 t (c.Wr i)) :
    DigAt t (slot i) (c.bufferVal i) := by
  have hp := slot_props i hi
  have o0 := h0 i hi 0 (by omega)
  have o1 := h0 i hi 1 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1
  have f0 := hF (slot i) (by omega) (c.bufferSafe_protected i _ hs hb (by omega))
  have f1 := hF (slot i+8) (by omega) (c.bufferSafe_protected i _ hs hb (by omega))
  have t0 : OrigW c.w t (slot i) := by unfold OrigW at *; rw [f0]; exact o0
  have t1 : OrigW c.w t (slot i+8) := by unfold OrigW at *; rw [f1]; exact o1
  rw [bufferVal, if_pos hs]
  exact DigAt_origW t0 t1 (by unfold Verify.WIT; omega)


theorem bufferSafe_source (c : NCtx) (digits : List Nat)
    (hd : ∀ j, j < 51 → digits.getD j 0 = c.dig j)
    (i : Nat) (hi : i < 51) : c.bufferSafe i ↔ ClaudeWCT.WCT9.safeZeroCopy 0 digits i := by
  unfold bufferSafe ClaudeWCT.WCT9.safeZeroCopy
  rw [hd i hi, topMax_eq]
  by_cases hz : i = 0
  · simp [hz]
  · rw [hd (i-1) (by omega), topMax_eq]
    simp [hz]
theorem bufferSlot_source (i : Nat) :
    slot i - Verify.WIT = ClaudeWCT.W9.T3M.leafBufferSlot 0 i := by
  simp only [slot, ClaudeWCT.W9.T3M.leafBufferSlot, ClaudeWCT.W9.T3M.leafBufferBase, Verify.WIT, if_true]
  split_ifs <;> simp_all <;> omega
theorem bufferVal_source (c : NCtx) (digits : List Nat)
    (hd : ∀ j, j < 51 → digits.getD j 0 = c.dig j)
    (hS : c.S3 = 14128) (i : Nat) (hi : i < 51) :
    c.bufferVal i = ClaudeWCT.W9.T3M.wvalueFor c.w 0 digits i := by
  unfold bufferVal ClaudeWCT.W9.T3M.wvalueFor
  simp only [← c.bufferSafe_source digits hd i hi, bufferSlot_source]
  split
  · rfl
  · unfold val ClaudeWCT.W9.T3M.wvalue
    apply congrArg (ClaudeWCT.W9.T3M.wdig c.w)
    have hv : ClaudeWCT.W9.T3M.valueOff 0 i = 48 * (i % 2) := by
      unfold ClaudeWCT.W9.T3M.valueOff; rw [← topG_isG, topG_lt i hi]
      by_cases h : i % 2 = 0 <;> simp [h] <;> omega
    rw [hv]
    simp only [vAt, blk, hS, ClaudeWCT.W9.T3M.chainBlock, ClaudeWCT.W9.T3M.layerBase,
      ClaudeWCT.W9.T3M.pathSlots, Matrix.cons_val_zero, Verify.WIT, ← topSlot_eq]
    omega

theorem bufferVal_nonmax (c : NCtx) (i : Nat) (h : c.dig i ≠ topMax i) :
    c.bufferVal i = c.val i := by simp [bufferVal, bufferSafe, h]

/-- Digit `j` of group `i / 3`'s rank is chain `3 (i / 3) + j`'s digit (the r7 pair: two digits). -/
theorem kdig_chain (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 50) :
    kdig (i/3) (c.kOf (i/3)) (i%3) = c.dig i := by
  by_cases h16 : i/3 = 16
  · rw [h16]
    have : i = 48 ∨ i = 49 := by omega
    rcases this with h | h
    · rw [h]; exact (c.kdig_kOf16 hds).1
    · rw [h]; exact (c.kdig_kOf16 hds).2.1
  · obtain ⟨k0,k1,k2⟩ := c.kdig_kOf hds (i/3) (by omega)
    have : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
    rcases this with h | h | h
    · rw [h, k0, show 3*(i/3) = i by omega]
    · rw [h, k1, show 3*(i/3)+1 = i by omega]
    · rw [h, k2, show 3*(i/3)+2 = i by omega]
theorem rungPc_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 51) (hd : c.dig i < topMax i) :
    c.rungPc i (last i) + 3 = c.endPc i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last; omega
  by_cases h50 : i < 50
  · have hmq := topMax_mx i h50
    have hdq : c.dig i < mx (i/3) := hmq ▸ hd
    have hlq : last i + 1 = mx (i/3) := hmq ▸ hl
    have hk := c.kdig_chain hds i h50
    by_cases h0 : i%3=0
    · rw [h0] at hk
      have hskipA : skipA (i/3) (c.kOf (i/3))=false := by simp [skipA, hk, Nat.ne_of_lt hdq]
      have hskipB : skipB (i/3) (c.kOf (i/3))=false := by simp [skipB, hk, Nat.ne_of_lt hdq]
      simp only [rungPc,endPc,qb,qB,h0,h50,and_self,if_true,gB,hskipA,hskipB,Bool.false_eq_true,if_false,
        Nat.sub_zero,Nat.add_zero]
      split_ifs <;> omega
    · by_cases h1 : i%3=1
      · rw [h1] at hk
        have hskip : skipB (i/3) (c.kOf (i/3))=false := by simp [skipB, hk, Nat.ne_of_lt hdq]
        simp only [rungPc,endPc,startPc,h0,h1,h50,false_and,if_true,if_false,qC,gC,hskip,Bool.false_eq_true,
          Nat.sub_zero,hk]
        change c.qB i + (if c.dig i=last i then 2 else 3) + 2*(last i-c.dig i)+3 = c.qB i+partLen (i/3) (c.dig i)
        unfold partLen
        rw [if_neg (Nat.ne_of_lt hdq)]
        split_ifs <;> omega
      · have h2 : i%3=2 := by omega
        rw [h2] at hk
        have h16 : i/3 ≠ 16 := by omega
        have hskip : skipC (i/3) (c.kOf (i/3))=false := by simp [skipC, hk, Nat.ne_of_lt hdq]
        simp only [rungPc,endPc,startPc,h0,h1,h50,false_and,if_true,if_false,qX,gX,h16,hskip,Bool.false_eq_true,
          Nat.sub_zero,hk]
        change c.qC i + (if c.dig i=last i then 2 else 3) + 2*(last i-c.dig i)+3 = c.qC i+partLen (i/3) (c.dig i)
        unfold partLen
        rw [if_neg (Nat.ne_of_lt hdq)]
        split_ifs <;> omega
  · have hi50 : i = 50 := by omega
    subst hi50
    have h5 : topMax 50 = 5 := topMax_50
    simp only [rungPc,endPc,startPc,h50,and_false,if_false,if_true,Nat.sub_zero,ckTail]
    unfold partLen
    simp only [mx,show ¬ (17:Nat)<9 by decide,show ¬ (17:Nat)<16 by decide,show ¬ (17:Nat)=16 by decide,if_false]
    have hd5 : c.dig 50 < 5 := by omega
    simp only [if_neg (Nat.ne_of_lt hd5)]
    unfold last at *
    rw [h5] at *
    split_ifs <;> omega
theorem posE_eval (c : NCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i m : Nat) (hm : m ≤ last i) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hm3 : m ≤ 6 := by have := last_bounds i; omega
  interval_cases m
  · rfl
  · exact kr .x7 1 (by simp [known]) (by decide +kernel)
  · exact kr .x13 2 (by simp [known]) (by decide +kernel)
  · exact kr .x19 3 (by simp [known]) (by decide +kernel)
  · exact kr .x20 4 (by simp [known]) (by decide +kernel)
  · exact kr .x21 5 (by simp [known]) (by decide +kernel)
  · exact kr .x26 6 (by simp [known]) (by decide +kernel)
theorem w0_low (c : NCtx) (i m : Nat) (hi : i < 51) (hm : m < 256) :
    (BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m)).toNat % 2 ^ 8 = 128 + i ∧
      (BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m)).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt c i m hi hm)]
  have hp := c.prefix_props
  unfold w0; constructor <;> omega
theorem w0_low0 (c : NCtx) (i : Nat) (hi : i < 51) :
    (BitVec.ofNat 64 (c.w0 i)).toNat % 2 ^ 8 = 128 + i ∧
      (BitVec.ofNat 64 (c.w0 i)).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 := by
  have := w0_low c i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this
/-- The `jal` from a cell into its shared body: lead chains of the non-inline rows (r6 groups, the r5 table rows, the
r7 pair's chain 48). -/
def tableJump (c : NCtx) (i : Nat) : Nat := if (i%3=0 ∧ i<50) ∧ rowInl (i/3) (c.kOf (i/3))=false then 1 else 0
/-- Cycles of chain `i` at digit `d`. As R6: a buffer-safe chain costs its table jump (chain 0's r6 cell `jal`, 1
cycle; every other buffer-safe chain is skipped in place). -/
def chainCost (c : NCtx) (i d : Nat) : Nat :=
  if d=topMax i then (if c.bufferSafe i then c.tableJump i else 4+c.tableJump i)
  else 4+c.tableJump i+9*(topMax i-d)-(if d+1=topMax i then 1 else 0)
def chainsCost (c : NCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => c.chainCost j (c.dig j)).sum
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
-- ==== merged from T3M_Verify_Nonbinary_TopCost ====
section

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.WCT9
set_option maxHeartbeats 1200000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

private theorem cost_kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q < 16) :
    kss q (c.kOf q) = c.dig (3*q) + c.dig (3*q+1) + c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q hq
  simp only [kss,k1,k2,k3]

private theorem sum_flags (P : Nat → Prop) [DecidablePred P] (L : List Nat) :
    (L.map fun i => if P i then 1 else 0).sum = (L.filter fun i => decide (P i)).length := by
  induction L with
  | nil => simp
  | cons i L ih => by_cases h : P i <;> simp [h, ih, Nat.add_comm]

def bufferCredit (c : NCtx) : Nat :=
  ((List.range 51).map fun i => if c.bufferSafe i then 1 else 0).sum

def exactCredit (c : NCtx) : Nat :=
  ((List.range 51).map fun i => if c.dig i + 1 = topMax i then 1 else 0).sum

def jumps (c : NCtx) : Nat := ((List.range 51).map c.tableJump).sum

theorem chainCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 51) :
    c.chainCost i (c.dig i) + 9*c.dig i +
      (if c.dig i + 1 = topMax i then 1 else 0) +
      4*(if c.bufferSafe i then 1 else 0) = 4 + 9*topMax i + c.tableJump i := by
  have hm := topMax_bounds i
  have hd := hds i (by omega)
  by_cases hs : c.bufferSafe i
  · have hd := hs.1
    simp [chainCost, hs, hd]
    omega
  · unfold chainCost
    split_ifs <;> omega

private theorem sum_map_add (L : List Nat) (f g : Nat → Nat) :
    (L.map fun i => f i + g i).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Campaign T51: the 51 chains' capacity is `4·51 + 9·236 = 2328` plus the table jumps. -/
theorem chainsCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) :
    c.chainsCost 0 51 + 9*((List.range 51).map c.dig).sum + c.exactCredit + 4*c.bufferCredit =
      2328 + c.jumps := by
  have H : ∀ L : List Nat, (∀ i ∈ L, i < 51) →
      (L.map fun j => c.chainCost j (c.dig j)).sum + 9*(L.map c.dig).sum +
        (L.map fun i => if c.dig i + 1 = topMax i then 1 else 0).sum +
        4*(L.map fun i => if c.bufferSafe i then 1 else 0).sum =
      (L.map fun i => 4 + 9*topMax i).sum + (L.map c.tableJump).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons i L ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := c.chainCost_buffer_balance hds i (hL i (by simp))
      have h2 := ih (fun j hj => hL j (by simp [hj]))
      omega
  have hcap : ((List.range 51).map fun i => 4 + 9*topMax i).sum = 2328 := by decide +kernel
  have := H (List.range 51) (fun i hi => List.mem_range.mp hi)
  rw [hcap] at this
  unfold chainsCost exactCredit bufferCredit jumps
  rw [List.range'_eq_map_range, List.map_map]
  simp only [Function.comp_def, Nat.zero_add]
  exact this

private theorem sum_range_three' (f : Nat → Nat) (n : Nat) :
    ((List.range (3*n)).map f).sum = ((List.range n).map fun q => f (3*q) + f (3*q+1) + f (3*q+2)).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1) = 3*n+1+1+1 by ring, List.range_succ, List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih,
      Nat.add_assoc, Nat.reduceAdd]
    omega

/-- Campaign T51: the r6 groups 0..8 and the r7 pair (group 16) always take their table jump; of the kept r5 groups
only the penalised rows 10, 11, 12 can (digit sum below 3); the checksum chain 50 never does. -/
theorem jumps_source (c : NCtx) (hds : c.DigitsOk) (digits : List Nat)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.jumps = 10 + dispatchPenalty 0 digits := by
  have h51 : c.jumps = ((List.range (3*17)).map c.tableJump).sum := rfl
  have hq : ∀ q ∈ List.range 17, c.tableJump (3*q) + c.tableJump (3*q+1) + c.tableJump (3*q+2) =
      (if q < 9 ∨ q = 16 then 1 else 0) +
        (if (q = 10 ∨ q = 11 ∨ q = 12) ∧
          digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3 then 1 else 0) := by
    intro q hq
    have hq := List.mem_range.mp hq
    have h1 : c.tableJump (3*q+1) = 0 := by
      unfold tableJump; rw [if_neg (by omega)]
    have h2 : c.tableJump (3*q+2) = 0 := by
      unfold tableJump; rw [if_neg (by omega)]
    rw [h1, h2]
    by_cases h16 : q = 16
    · subst h16
      unfold tableJump
      simp [rowInl, inl]
    · rw [hd (3*q) (by omega), hd (3*q+1) (by omega), hd (3*q+2) (by omega),
        ← cost_kss_kOf c hds q (by omega)]
      unfold tableJump
      rw [show 3*q/3 = q by omega]
      simp only [show (3*q)%3 = 0 by omega, show 3*q < 50 by omega, and_self, true_and, rowInl, inl]
      generalize kss q (c.kOf q) = x
      interval_cases q <;> simp <;> omega
  rw [h51, sum_range_three', List.map_congr_left hq]
  have hsplit := sum_map_add (List.range 17) (fun q => if q < 9 ∨ q = 16 then 1 else 0)
    (fun q => if (q = 10 ∨ q = 11 ∨ q = 12) ∧
      digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3 then 1 else 0)
  have h10 : ((List.range 17).map fun q => if q < 9 ∨ q = 16 then 1 else 0).sum = 10 := by decide +kernel
  rw [hsplit, h10]
  unfold dispatchPenalty topDispatchPenalty
  rw [if_pos rfl, sum_flags]

theorem bufferCredit_source (c : NCtx) (digits : List Nat)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.bufferCredit = savedCopies 0 digits := by
  unfold bufferCredit savedCopies
  rw [sum_flags, show chainCount 0 = 51 from rfl]
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [decide_eq_decide]
  exact c.bufferSafe_source digits hd i hi'

theorem jumps_le_thirteen (c : NCtx) : c.jumps ≤ 13 := by
  have h : ∀ i, c.tableJump i ≤
      (if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0) := by
    intro i
    unfold tableJump
    by_cases hj : (i%3=0 ∧ i<50) ∧ rowInl (i/3) (c.kOf (i/3))=false
    · rw [if_pos hj]
      have hh : inl (i/3) = false := by
        have hh := hj.2
        simp only [rowInl, Bool.or_eq_false_iff] at hh
        exact hh.1
      simp [hj.1.1, hj.1.2, hh]
    · rw [if_neg hj]
      exact Nat.zero_le _
  have H : ∀ L : List Nat, (L.map c.tableJump).sum ≤
      (L.map fun i => if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0).sum := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h i) ih
  have H0 := H (List.range 51)
  have he : ((List.range 51).map fun i => if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0).sum=13 := by
    decide +kernel
  simpa [jumps, he] using H0

theorem chainsCost_any (c : NCtx) (hds : c.DigitsOk) : c.chainsCost 0 51 ≤ 2341 := by
  have hb := c.chainsCost_buffer_balance hds
  have hj := c.jumps_le_thirteen
  omega

/-- Campaign T51 cost law of the 51 chains at an accepted word (digit sum 152):
`2328 + 10 + penalty - 9·152 = 970 + penalty`. -/
theorem chainsCost_accepted (c : NCtx) (hds : c.DigitsOk) (v : Digest) (digits : List Nat)
    (hdec : decode 0 v = some digits)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.chainsCost 0 51 + topCredit v + 4*savedCopies 0 digits = 970 + dispatchPenalty 0 digits := by
  obtain ⟨-, -, ⟨hs1, -⟩, rfl⟩ := decode_top_some hdec
  have hlen : (dataDigits 0 v ++ [target 0 - (dataDigits 0 v).sum]).length = 51 := by
    simp [dataDigits_top_length]
  have hmap : (List.range 51).map c.dig = dataDigits 0 v ++ [target 0 - (dataDigits 0 v).sum] := by
    apply List.ext_getElem
    · simp [hlen]
    · intro n h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [← hd n (by simpa using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
      rfl
  have hsum : ((List.range 51).map c.dig).sum = 152 := by
    rw [hmap, List.sum_append]
    simp only [List.sum_cons, List.sum_nil]
    have : target 0 = 152 := rfl
    omega
  have hex : c.exactCredit = topCredit v := by
    unfold exactCredit topCredit
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [hd i hi', topMax_eq]
  have hb := c.chainsCost_buffer_balance hds
  have hj := c.jumps_source hds _ hd
  have hc := c.bufferCredit_source _ hd
  rw [hsum, hex, hc, hj] at hb
  omega

end SigGolfCandidate.T3M.Nonbinary.NCtx
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsDispatchArith ====
section

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem land_mask12 (n k : Nat) (hk : k≤7) :
    n &&& (4096*(2^k-1))=4096*(n/4096%2^k) := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_and,show (4096 : Nat)=2^12 by norm_num,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases h : 12≤j
  · simp only [h,decide_true,Bool.true_and,show j-12+12=j by omega]
    by_cases hj : j-12<k <;> simp [hj]
  · simp [h]
theorem field_shl12 (W s k : Nat) (hs : s≤12) (hk : k≤7) :
    W*2^s%2^64/4096%2^k=W/2^(12-s)%2^k := by
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow,show (4096 : Nat)=2^12 by norm_num,
    Nat.testBit_div_two_pow,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_mul_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and,show j+12<64 by omega,show s≤j+12 by omega]
    rw [show j+12-s=j+(12-s) by omega]
  · simp [hj]
def shiftWord12 (W : Word) (b : Nat) : Word := if b<12 then W<<<(12-b) else W>>>(b-12)
theorem word_mask12 (W : Word) (b : Nat) (hb : b<64) :
    shiftWord12 W b &&& 520192#64=BitVec.ofNat 64 (4096*(W.toNat/2^b%128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,show (520192#64).toNat=4096*(2^7-1) by rfl,land_mask12 _ _ (by decide +kernel)]
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4096*(W.toNat/2^b%128)<2^64 by omega)]
  apply congrArg (fun x => 4096*x)
  unfold shiftWord12
  split_ifs with h
  · simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    rw [field_shl12 _ _ _ (by omega) (by decide +kernel),show 12-(12-b)=b by omega]
    rfl
  · simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [Nat.div_div_eq_div_mul,
      show 2^(b-12)*4096=2^b by rw [show (4096 : Nat)=2^12 by rfl,←pow_add];congr 1;omega]
    rfl
theorem shift12_eval (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w=W)
    (b : Nat) (hb : b<64) : (shift12 w b).eval s=shiftWord12 W b := by
  unfold shift12 shiftWord12
  split_ifs with h <;> simp only [E.eval,BinOp.eval,hw,BitVec.toNat_ofNat]
  · rw [Nat.mod_eq_of_lt (show 12-b<2^64 by omega),Nat.mod_eq_of_lt (show 12-b<64 by omega)]
  · rw [Nat.mod_eq_of_lt (show b-12<2^64 by omega),Nat.mod_eq_of_lt (show b-12<64 by omega)]
theorem sub127_xor : ∀ f, f<128 → 127-f=127 ^^^ f := by decide +kernel
theorem not_field (X : Word) (b : Nat) (hb : b+7 ≤ 64) :
    (~~~X).toNat/2^b%128=127-X.toNat/2^b%128 := by
  rw [sub127_xor _ (Nat.mod_lt _ (by decide +kernel))]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, show (128:Nat)=2^7 by norm_num, show (127:Nat)=2^7-1 by norm_num,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]
  by_cases hj : j<7
  · simp [hj, show j+b<64 by omega]
  · simp [hj]
theorem entOff_le (q : Nat) (hq : q<17) : entOff q ≤ 1532 := by interval_cases q <;> decide +kernel
theorem entOff_ge (q : Nat) : 64 ≤ entOff q := by
  by_cases h : q<17
  · interval_cases q <;> decide +kernel
  · simp only [entOff, if_neg (show q≠0 by omega), if_neg (show q≠1 by omega),
      if_neg (show q≠2 by omega), if_neg (show q≠3 by omega), if_neg (show q≠4 by omega),
      if_neg (show q≠5 by omega), if_neg (show q≠6 by omega), if_neg (show q≠7 by omega),
      if_neg (show q≠8 by omega), if_neg (show q≠9 by omega), if_neg (show q≠10 by omega),
      if_neg (show q≠11 by omega), if_neg (show q≠12 by omega), if_neg (show q≠13 by omega),
      if_neg (show q≠14 by omega), if_neg (show q≠15 by omega)]
    decide +kernel
theorem dispatch_value (W : Word) (b q : Nat) (hb : b<64) (hq : q<17) :
    ((shiftWord12 W b &&& 520192#64)+BitVec.ofNat 64 (2^64+4*entOff q-4096)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096*(W.toNat/2^b%128)+2^64+4*entOff q-4096) := by
  have he := entOff_le q hq
  rw [word_mask12 W b hb,ofNat_add_ofNat,even_andNot1' _ (by omega)]
  apply congrArg (BitVec.ofNat 64); omega
/-- T51: #938's r5 groups 9..15 keep their cell column `1024 (125 - k) + entOff q`. -/
theorem cell_value (q k : Nat) (hq : q<16) (h9 : 9≤q) (hk : k ≤ 124) :
    BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)=pcOf (cellW q k) := by
  have he := entOff_le q (by omega)
  unfold pcOf cellW; rw [if_neg (by omega), if_pos hq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
/-- T51: the r7 pair (group 16) is reached by #938's dispatch into group 8 (`entOff 8 = 676`): rank `k < 49` lands
on its cell `cellW 16 k = 1024 (125 - k) + 676`. -/
theorem cell_value_pair (k : Nat) (hk : k ≤ 124) :
    BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff 8-4096)=pcOf (cellW 16 k) := by
  unfold pcOf cellW entOff
  simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault125_value (q : Nat) (hq : q<17) :
    BitVec.ofNat 64 (4096*(127-125)+2^64+4*entOff q-4096)=pcOf (entOff q) := by
  have he := entOff_le q hq
  unfold pcOf
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault_value (q k : Nat) (hq : q<17) (hk : 127 ≤ k) (hk' : k<128) :
    (BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)).toNat<0x1000 ∨
      0x1000+4*257280 ≤ (BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff q-4096)).toNat := by
  have he := entOff_le q hq
  have hl := entOff_ge q
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault126_value (q : Nat) (hq : q<17) (he : 1024≤entOff q) :
    BitVec.ofNat 64 (4096*(127-126)+2^64+4*entOff q-4096)=pcOf (entOff q-1024) := by
  have hu := entOff_le q hq
  unfold pcOf
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega
theorem fault126_low (q : Nat) (he : entOff q<1024) :
    (BitVec.ofNat 64 (4096*(127-126)+2^64+4*entOff q-4096)).toNat<0x1000 := by
  simp only [BitVec.toNat_ofNat]
  omega
theorem g9_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 13).toNat) &&& 520192#64)+256#64) &&& ~~~1#64 =
      BitVec.ofNat 64 (8192*(W.toNat%64)+256) := by
  have hm : ((W <<< (BitVec.ofNat 64 13).toNat) &&& 520192#64) = BitVec.ofNat 64 (8192*(W.toNat%64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (520192#64).toNat=4096*(2^7-1) by rfl,land_mask12 _ _ (by decide +kernel)]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hw := W.isLt
    rw [show (13 : Nat) % 2^64 = 13 by rfl]
    rw [Nat.mod_eq_of_lt (show 8192*(W.toNat%64) < 2^64 by omega)]
    have : W.toNat*2^13%2^64/4096%2^7 = 2*(W.toNat%64) := by
      rw [show (2:Nat)^64 = 2^13*2^51 by norm_num, Nat.mul_comm, Nat.mul_mod_mul_left,
        show (2:Nat)^13*(W.toNat%2^51) = 4096*(2*(W.toNat%2^51)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      omega
    rw [this]; ring
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
theorem g9_cell (u : Nat) (hu : u ≤ 62) : BitVec.ofNat 64 (8192*(63-u)+256)=pcOf (cellW 9 (2*u)) := by
  unfold pcOf cellW entOff; norm_num; congr 1; omega
theorem g9_fault : (BitVec.ofNat 64 (8192*(63-63)+256)).toNat<0x1000 := by decide +kernel
theorem prologue_value (W : Word) :
    (((W <<< (BitVec.ofNat 64 12).toNat) &&& 520192#64)+BitVec.ofNat 64 (1168)) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096*(W.toNat%128)+1168) := by
  have hm := word_mask12 W 0 (by decide +kernel)
  simp only [shiftWord12, show (0 : Nat) < 12 from by omega, if_true,
    Nat.sub_zero, Nat.pow_zero, Nat.div_one] at hm
  change ((W <<< 12 &&& 520192#64) + BitVec.ofNat 64 (1168)) &&& ~~~1#64 = _
  rw [hm, ofNat_add_ofNat, even_andNot1' _ (by omega)]
/-! ### T51 dispatch arithmetic (ported from R6)
g0 (prologue): `slli a4,a6,56; srli a4,a4,45; jalr -744(a4)` lands on `cell6 0 raw` (raw = a6 % 256 >= 3), below the
code start (raw = 1, 2) or far above it (raw = 0).  r6 groups 1..8: `a4 = field & 0xFF00 = 256 raw`, table B
(g1..g3, g8) `s2 - a4`, table A `a4 + s2`, `jalr` to `cell6 h raw`.  Checksum: `((s8 + 89) << 11) + 1168` with
`s8 = T - ds` (T = 152, ds <= 231) lands on `ckWord ds`. -/
/-- The g0 dispatch shift pair `slli a4,a6,56; srli a4,a4,45`: `2048 * (a6 % 256)`. -/
theorem g0_shift (W : Word) : (W <<< 56) >>> 45 = BitVec.ofNat 64 (2048 * (W.toNat % 256)) := by
  apply BitVec.eq_of_toNat_eq
  have hW := W.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2048 * (W.toNat % 256) < 2^64 by omega)]
  rw [show (2:Nat)^64 = 2^56 * 2^8 by norm_num, Nat.mul_comm W.toNat, Nat.mul_mod_mul_left,
    show (2:Nat)^56 = 2^45 * 2048 by norm_num, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  norm_num
/-- The g0 dispatch target (jalr -744) for a field value `raw >= 1`. -/
theorem g0_target (W : Word) (raw : Nat) (hr : W.toNat % 256 = raw) (h1 : 1 ≤ raw) :
    (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64 = BitVec.ofNat 64 (2048 * raw - 744) := by
  have hr' : raw < 256 := by omega
  have e : BitVec.ofNat 64 (2048 * raw) + BitVec.ofNat 64 (2^64-744) = BitVec.ofNat 64 (2048 * raw - 744) := by
    rw [ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [g0_shift, hr, e, even_andNot1' _ (by omega)]
theorem g0_cell (raw : Nat) (h3 : 3 ≤ raw) : BitVec.ofNat 64 (2048 * raw - 744) = pcOf (cell6 0 raw) := by
  unfold pcOf cell6; simp only [if_true]; congr 1; omega
theorem g0_low (raw : Nat) (h3 : raw < 3) : (BitVec.ofNat 64 (2048 * raw - 744)).toNat < 0x1000 := by
  simp only [BitVec.toNat_ofNat]; omega
/-- Field value 0: the target `2^64 - 744` lies far above the code. -/
theorem g0_target0 (W : Word) (hr : W.toNat % 256 = 0) :
    0x1000 + 4 * 257280 ≤ ((((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64).toNat := by
  rw [g0_shift, hr, Nat.mul_zero, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  simp only [BitVec.toNat_ofNat]; omega
theorem land_mask8 (n : Nat) : n &&& (256*(2^8-1)) = 256*(n/256%2^8) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (256 : Nat)=2^8 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : 8 ≤ j
  · simp only [h, decide_true, Bool.true_and, show j-8+8=j by omega]
    by_cases hj : j-8<8 <;> simp [hj]
  · simp [h]
/-- `X &&& 0xFF00 = 256 * (X / 2^8 % 256)`. -/
theorem word_ff00 (X : Word) : X &&& 65280#64 = BitVec.ofNat 64 (256 * (X.toNat / 2^8 % 256)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : X.toNat / 2^8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  rw [BitVec.toNat_and, show (65280#64).toNat = 256*(2^8-1) by rfl, land_mask8, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 256 * (X.toNat / 2^8 % 256)) (by omega)]
  norm_num
/-- `(X >>> s) &&& 0xFF00 = 256 * (X / 2^(s+8) % 256)`. -/
theorem field_ff00 (X : Word) (s : Nat) :
    (X >>> s) &&& 65280#64 = BitVec.ofNat 64 (256 * (X.toNat / 2^(s+8) % 256)) := by
  rw [word_ff00, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
theorem s2_sub (r : Nat) (hr : r < 256) :
    856064#64 - BitVec.ofNat 64 (256*r) = BitVec.ofNat 64 (856064-256*r) := by
  rw [BitVec.sub_eq_iff_eq_add, ofNat_add_ofNat]
  congr 1; omega
/-- Table B target (r6 groups 1..3): `s2 - 256 raw + (4 off - 256)`. -/
theorem tabB_target (r o : Nat) (hr : r < 256) (ho : o < 64) :
    ((856064#64 - BitVec.ofNat 64 (256*r)) + BitVec.ofNat 64 (2^64+4*o-256)) &&& ~~~1#64 =
      pcOf (64*(3327-r)+o) := by
  rw [s2_sub r hr, ofNat_add_ofNat]
  have e : BitVec.ofNat 64 (856064-256*r+(2^64+4*o-256)) = BitVec.ofNat 64 (856064-256*r+4*o-256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [e, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega
/-- Table A target (r6 groups 4..7): `256 raw + s2 + 4 off`. -/
theorem tabA_target (r o : Nat) (hr : r < 256) (ho : o < 64) :
    ((BitVec.ofNat 64 (256*r) + 856064#64) + BitVec.ofNat 64 (4*o)) &&& ~~~1#64 =
      pcOf (64*(3328+r)+o) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf; congr 1; omega
theorem ck_s8 (ds : Nat) (hd : ds ≤ 231) :
    (BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) + 89#64 = BitVec.ofNat 64 (241-ds) := by
  rw [BitVec.ofNat_sub_ofNat, ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [topT, BitVec.toNat_ofNat]
  omega
/-- The checksum dispatch target `(((s8 + 89) << 11) + 1168) & ~1` for s8 = T - ds, ds <= 231. -/
theorem ck_target (ds : Nat) (hd : ds ≤ 231) :
    ((((BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) + 89#64) <<< 11) + 1168#64) &&& ~~~1#64 =
      pcOf (ckWord ds) := by
  have e2 : BitVec.ofNat 64 (241-ds) <<< 11 = BitVec.ofNat 64 (2048*(241-ds)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega
  rw [ck_s8 ds hd, e2, ofNat_add_ofNat, even_andNot1' _ (by omega)]
  unfold pcOf ckWord topT; congr 1; omega
/-- The r6 field read by the dispatch into group `h` (1..8): bits `8h..8h+7` (h < 7), `112..119` (g7),
`120..127` (g8) (`= T3.r6Shift h`). -/
def r6Pos (h : Nat) : Nat := if h=7 then 112 else if h=8 then 120 else 8*h
theorem cell6_tab (h r : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) :
    cell6 h r = if r6B h then 64*(3327-r)+r6Off h else 64*(3328+r)+r6Off h := by
  unfold cell6; rw [if_neg (by omega)]
theorem r6Off_lt (h : Nat) : r6Off h < 64 := by unfold r6Off; omega
end SigGolfCandidate.T3M.Nonbinary
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsCheckParts ====
section

namespace SigGolfCandidate.T3M.Nonbinary
/-- Join bounded kernel computations without normalizing an entire closed code window. -/
theorem check_range_add {p : Nat → Bool} {lo left right : Nat}
    (hleft : (List.range' lo left).all p = true)
    (hright : (List.range' (lo + left) right).all p = true) :
    (List.range' lo (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl

theorem tripleCheck_join {q : Nat}
    (hent : (List.range' 0 (nRank q)).all (fun k => entCheck q k && s8Check q k) = true)
    (hblock : (List.range' 0 (nBlock q)).all (liveBlock q) = true) :
    tripleCheck q = true := by
  unfold tripleCheck
  rw [List.range_eq_range', List.range_eq_range', hent, hblock]
  rfl
end SigGolfCandidate.T3M.Nonbinary
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart0 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_0_part_0 : (List.range' 0 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_8 : (List.range' 8 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_16 : (List.range' 16 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_24 : (List.range' 24 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_32 : (List.range' 32 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_40 : (List.range' 40 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_48 : (List.range' 48 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_56 : (List.range' 56 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_64 : (List.range' 64 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_72 : (List.range' 72 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_80 : (List.range' 80 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_88 : (List.range' 88 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_96 : (List.range' 96 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_104 : (List.range' 104 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_112 : (List.range' 112 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_120 : (List.range' 120 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_128 : (List.range' 128 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_136 : (List.range' 136 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_144 : (List.range' 144 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_152 : (List.range' 152 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_160 : (List.range' 160 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_168 : (List.range' 168 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_176 : (List.range' 176 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_184 : (List.range' 184 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_192 : (List.range' 192 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_200 : (List.range' 200 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0_part_208 : (List.range' 208 8).all (fun k => entCheck 0 k && s8Check 0 k) = true := by decide +kernel
private theorem tripleEnt_0 : (List.range' 0 216).all (fun k => entCheck 0 k && s8Check 0 k) = true := by
  exact (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 0 8 208 tripleEnt_0_part_0 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 8 8 200 tripleEnt_0_part_8 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 16 8 192 tripleEnt_0_part_16 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 24 8 184 tripleEnt_0_part_24 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 32 8 176 tripleEnt_0_part_32 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 40 8 168 tripleEnt_0_part_40 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 48 8 160 tripleEnt_0_part_48 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 56 8 152 tripleEnt_0_part_56 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 64 8 144 tripleEnt_0_part_64 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 72 8 136 tripleEnt_0_part_72 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 80 8 128 tripleEnt_0_part_80 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 88 8 120 tripleEnt_0_part_88 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 96 8 112 tripleEnt_0_part_96 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 104 8 104 tripleEnt_0_part_104 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 112 8 96 tripleEnt_0_part_112 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 120 8 88 tripleEnt_0_part_120 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 128 8 80 tripleEnt_0_part_128 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 136 8 72 tripleEnt_0_part_136 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 144 8 64 tripleEnt_0_part_144 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 152 8 56 tripleEnt_0_part_152 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 160 8 48 tripleEnt_0_part_160 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 168 8 40 tripleEnt_0_part_168 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 176 8 32 tripleEnt_0_part_176 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 184 8 24 tripleEnt_0_part_184 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 192 8 16 tripleEnt_0_part_192 (@check_range_add (fun k => entCheck 0 k && s8Check 0 k) 200 8 8 tripleEnt_0_part_200 tripleEnt_0_part_208))))))))))))))))))))))))))
private theorem tripleBlock_0_part_0 : (List.range' 0 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_4 : (List.range' 4 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_8 : (List.range' 8 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_12 : (List.range' 12 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_16 : (List.range' 16 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_20 : (List.range' 20 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_24 : (List.range' 24 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_28 : (List.range' 28 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0_part_32 : (List.range' 32 4).all (liveBlock 0) = true := by decide +kernel
private theorem tripleBlock_0 : (List.range' 0 36).all (liveBlock 0) = true := by
  exact (@check_range_add (liveBlock 0) 0 4 32 tripleBlock_0_part_0 (@check_range_add (liveBlock 0) 4 4 28 tripleBlock_0_part_4 (@check_range_add (liveBlock 0) 8 4 24 tripleBlock_0_part_8 (@check_range_add (liveBlock 0) 12 4 20 tripleBlock_0_part_12 (@check_range_add (liveBlock 0) 16 4 16 tripleBlock_0_part_16 (@check_range_add (liveBlock 0) 20 4 12 tripleBlock_0_part_20 (@check_range_add (liveBlock 0) 24 4 8 tripleBlock_0_part_24 (@check_range_add (liveBlock 0) 28 4 4 tripleBlock_0_part_28 tripleBlock_0_part_32))))))))
theorem tripleCheck_0 : tripleCheck 0=true := by
  exact @tripleCheck_join 0 tripleEnt_0 tripleBlock_0
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_1_part_0 : (List.range' 0 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_8 : (List.range' 8 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_16 : (List.range' 16 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_24 : (List.range' 24 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_32 : (List.range' 32 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_40 : (List.range' 40 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_48 : (List.range' 48 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_56 : (List.range' 56 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_64 : (List.range' 64 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_72 : (List.range' 72 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_80 : (List.range' 80 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_88 : (List.range' 88 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_96 : (List.range' 96 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_104 : (List.range' 104 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_112 : (List.range' 112 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_120 : (List.range' 120 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_128 : (List.range' 128 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_136 : (List.range' 136 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_144 : (List.range' 144 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_152 : (List.range' 152 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_160 : (List.range' 160 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_168 : (List.range' 168 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_176 : (List.range' 176 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_184 : (List.range' 184 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_192 : (List.range' 192 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_200 : (List.range' 200 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1_part_208 : (List.range' 208 8).all (fun k => entCheck 1 k && s8Check 1 k) = true := by decide +kernel
private theorem tripleEnt_1 : (List.range' 0 216).all (fun k => entCheck 1 k && s8Check 1 k) = true := by
  exact (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 0 8 208 tripleEnt_1_part_0 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 8 8 200 tripleEnt_1_part_8 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 16 8 192 tripleEnt_1_part_16 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 24 8 184 tripleEnt_1_part_24 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 32 8 176 tripleEnt_1_part_32 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 40 8 168 tripleEnt_1_part_40 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 48 8 160 tripleEnt_1_part_48 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 56 8 152 tripleEnt_1_part_56 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 64 8 144 tripleEnt_1_part_64 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 72 8 136 tripleEnt_1_part_72 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 80 8 128 tripleEnt_1_part_80 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 88 8 120 tripleEnt_1_part_88 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 96 8 112 tripleEnt_1_part_96 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 104 8 104 tripleEnt_1_part_104 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 112 8 96 tripleEnt_1_part_112 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 120 8 88 tripleEnt_1_part_120 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 128 8 80 tripleEnt_1_part_128 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 136 8 72 tripleEnt_1_part_136 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 144 8 64 tripleEnt_1_part_144 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 152 8 56 tripleEnt_1_part_152 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 160 8 48 tripleEnt_1_part_160 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 168 8 40 tripleEnt_1_part_168 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 176 8 32 tripleEnt_1_part_176 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 184 8 24 tripleEnt_1_part_184 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 192 8 16 tripleEnt_1_part_192 (@check_range_add (fun k => entCheck 1 k && s8Check 1 k) 200 8 8 tripleEnt_1_part_200 tripleEnt_1_part_208))))))))))))))))))))))))))
private theorem tripleBlock_1_part_0 : (List.range' 0 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_4 : (List.range' 4 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_8 : (List.range' 8 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_12 : (List.range' 12 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_16 : (List.range' 16 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_20 : (List.range' 20 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_24 : (List.range' 24 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_28 : (List.range' 28 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1_part_32 : (List.range' 32 4).all (liveBlock 1) = true := by decide +kernel
private theorem tripleBlock_1 : (List.range' 0 36).all (liveBlock 1) = true := by
  exact (@check_range_add (liveBlock 1) 0 4 32 tripleBlock_1_part_0 (@check_range_add (liveBlock 1) 4 4 28 tripleBlock_1_part_4 (@check_range_add (liveBlock 1) 8 4 24 tripleBlock_1_part_8 (@check_range_add (liveBlock 1) 12 4 20 tripleBlock_1_part_12 (@check_range_add (liveBlock 1) 16 4 16 tripleBlock_1_part_16 (@check_range_add (liveBlock 1) 20 4 12 tripleBlock_1_part_20 (@check_range_add (liveBlock 1) 24 4 8 tripleBlock_1_part_24 (@check_range_add (liveBlock 1) 28 4 4 tripleBlock_1_part_28 tripleBlock_1_part_32))))))))
theorem tripleCheck_1 : tripleCheck 1=true := by
  exact @tripleCheck_join 1 tripleEnt_1 tripleBlock_1
end SigGolfCandidate.T3M.Nonbinary
end
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart1 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_2_part_0 : (List.range' 0 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_8 : (List.range' 8 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_16 : (List.range' 16 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_24 : (List.range' 24 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_32 : (List.range' 32 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_40 : (List.range' 40 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_48 : (List.range' 48 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_56 : (List.range' 56 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_64 : (List.range' 64 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_72 : (List.range' 72 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_80 : (List.range' 80 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_88 : (List.range' 88 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_96 : (List.range' 96 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_104 : (List.range' 104 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_112 : (List.range' 112 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_120 : (List.range' 120 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_128 : (List.range' 128 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_136 : (List.range' 136 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_144 : (List.range' 144 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_152 : (List.range' 152 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_160 : (List.range' 160 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_168 : (List.range' 168 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_176 : (List.range' 176 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_184 : (List.range' 184 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_192 : (List.range' 192 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_200 : (List.range' 200 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2_part_208 : (List.range' 208 8).all (fun k => entCheck 2 k && s8Check 2 k) = true := by decide +kernel
private theorem tripleEnt_2 : (List.range' 0 216).all (fun k => entCheck 2 k && s8Check 2 k) = true := by
  exact (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 0 8 208 tripleEnt_2_part_0 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 8 8 200 tripleEnt_2_part_8 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 16 8 192 tripleEnt_2_part_16 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 24 8 184 tripleEnt_2_part_24 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 32 8 176 tripleEnt_2_part_32 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 40 8 168 tripleEnt_2_part_40 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 48 8 160 tripleEnt_2_part_48 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 56 8 152 tripleEnt_2_part_56 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 64 8 144 tripleEnt_2_part_64 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 72 8 136 tripleEnt_2_part_72 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 80 8 128 tripleEnt_2_part_80 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 88 8 120 tripleEnt_2_part_88 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 96 8 112 tripleEnt_2_part_96 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 104 8 104 tripleEnt_2_part_104 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 112 8 96 tripleEnt_2_part_112 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 120 8 88 tripleEnt_2_part_120 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 128 8 80 tripleEnt_2_part_128 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 136 8 72 tripleEnt_2_part_136 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 144 8 64 tripleEnt_2_part_144 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 152 8 56 tripleEnt_2_part_152 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 160 8 48 tripleEnt_2_part_160 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 168 8 40 tripleEnt_2_part_168 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 176 8 32 tripleEnt_2_part_176 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 184 8 24 tripleEnt_2_part_184 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 192 8 16 tripleEnt_2_part_192 (@check_range_add (fun k => entCheck 2 k && s8Check 2 k) 200 8 8 tripleEnt_2_part_200 tripleEnt_2_part_208))))))))))))))))))))))))))
private theorem tripleBlock_2_part_0 : (List.range' 0 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_4 : (List.range' 4 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_8 : (List.range' 8 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_12 : (List.range' 12 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_16 : (List.range' 16 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_20 : (List.range' 20 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_24 : (List.range' 24 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_28 : (List.range' 28 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2_part_32 : (List.range' 32 4).all (liveBlock 2) = true := by decide +kernel
private theorem tripleBlock_2 : (List.range' 0 36).all (liveBlock 2) = true := by
  exact (@check_range_add (liveBlock 2) 0 4 32 tripleBlock_2_part_0 (@check_range_add (liveBlock 2) 4 4 28 tripleBlock_2_part_4 (@check_range_add (liveBlock 2) 8 4 24 tripleBlock_2_part_8 (@check_range_add (liveBlock 2) 12 4 20 tripleBlock_2_part_12 (@check_range_add (liveBlock 2) 16 4 16 tripleBlock_2_part_16 (@check_range_add (liveBlock 2) 20 4 12 tripleBlock_2_part_20 (@check_range_add (liveBlock 2) 24 4 8 tripleBlock_2_part_24 (@check_range_add (liveBlock 2) 28 4 4 tripleBlock_2_part_28 tripleBlock_2_part_32))))))))
theorem tripleCheck_2 : tripleCheck 2=true := by
  exact @tripleCheck_join 2 tripleEnt_2 tripleBlock_2
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_3_part_0 : (List.range' 0 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_8 : (List.range' 8 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_16 : (List.range' 16 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_24 : (List.range' 24 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_32 : (List.range' 32 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_40 : (List.range' 40 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_48 : (List.range' 48 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_56 : (List.range' 56 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_64 : (List.range' 64 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_72 : (List.range' 72 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_80 : (List.range' 80 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_88 : (List.range' 88 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_96 : (List.range' 96 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_104 : (List.range' 104 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_112 : (List.range' 112 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_120 : (List.range' 120 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_128 : (List.range' 128 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_136 : (List.range' 136 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_144 : (List.range' 144 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_152 : (List.range' 152 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_160 : (List.range' 160 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_168 : (List.range' 168 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_176 : (List.range' 176 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_184 : (List.range' 184 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_192 : (List.range' 192 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_200 : (List.range' 200 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3_part_208 : (List.range' 208 8).all (fun k => entCheck 3 k && s8Check 3 k) = true := by decide +kernel
private theorem tripleEnt_3 : (List.range' 0 216).all (fun k => entCheck 3 k && s8Check 3 k) = true := by
  exact (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 0 8 208 tripleEnt_3_part_0 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 8 8 200 tripleEnt_3_part_8 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 16 8 192 tripleEnt_3_part_16 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 24 8 184 tripleEnt_3_part_24 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 32 8 176 tripleEnt_3_part_32 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 40 8 168 tripleEnt_3_part_40 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 48 8 160 tripleEnt_3_part_48 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 56 8 152 tripleEnt_3_part_56 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 64 8 144 tripleEnt_3_part_64 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 72 8 136 tripleEnt_3_part_72 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 80 8 128 tripleEnt_3_part_80 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 88 8 120 tripleEnt_3_part_88 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 96 8 112 tripleEnt_3_part_96 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 104 8 104 tripleEnt_3_part_104 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 112 8 96 tripleEnt_3_part_112 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 120 8 88 tripleEnt_3_part_120 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 128 8 80 tripleEnt_3_part_128 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 136 8 72 tripleEnt_3_part_136 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 144 8 64 tripleEnt_3_part_144 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 152 8 56 tripleEnt_3_part_152 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 160 8 48 tripleEnt_3_part_160 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 168 8 40 tripleEnt_3_part_168 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 176 8 32 tripleEnt_3_part_176 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 184 8 24 tripleEnt_3_part_184 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 192 8 16 tripleEnt_3_part_192 (@check_range_add (fun k => entCheck 3 k && s8Check 3 k) 200 8 8 tripleEnt_3_part_200 tripleEnt_3_part_208))))))))))))))))))))))))))
private theorem tripleBlock_3_part_0 : (List.range' 0 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_4 : (List.range' 4 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_8 : (List.range' 8 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_12 : (List.range' 12 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_16 : (List.range' 16 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_20 : (List.range' 20 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_24 : (List.range' 24 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_28 : (List.range' 28 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3_part_32 : (List.range' 32 4).all (liveBlock 3) = true := by decide +kernel
private theorem tripleBlock_3 : (List.range' 0 36).all (liveBlock 3) = true := by
  exact (@check_range_add (liveBlock 3) 0 4 32 tripleBlock_3_part_0 (@check_range_add (liveBlock 3) 4 4 28 tripleBlock_3_part_4 (@check_range_add (liveBlock 3) 8 4 24 tripleBlock_3_part_8 (@check_range_add (liveBlock 3) 12 4 20 tripleBlock_3_part_12 (@check_range_add (liveBlock 3) 16 4 16 tripleBlock_3_part_16 (@check_range_add (liveBlock 3) 20 4 12 tripleBlock_3_part_20 (@check_range_add (liveBlock 3) 24 4 8 tripleBlock_3_part_24 (@check_range_add (liveBlock 3) 28 4 4 tripleBlock_3_part_28 tripleBlock_3_part_32))))))))
theorem tripleCheck_3 : tripleCheck 3=true := by
  exact @tripleCheck_join 3 tripleEnt_3 tripleBlock_3
end SigGolfCandidate.T3M.Nonbinary
end
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart2 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_4_part_0 : (List.range' 0 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_8 : (List.range' 8 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_16 : (List.range' 16 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_24 : (List.range' 24 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_32 : (List.range' 32 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_40 : (List.range' 40 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_48 : (List.range' 48 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_56 : (List.range' 56 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_64 : (List.range' 64 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_72 : (List.range' 72 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_80 : (List.range' 80 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_88 : (List.range' 88 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_96 : (List.range' 96 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_104 : (List.range' 104 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_112 : (List.range' 112 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_120 : (List.range' 120 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_128 : (List.range' 128 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_136 : (List.range' 136 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_144 : (List.range' 144 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_152 : (List.range' 152 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_160 : (List.range' 160 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_168 : (List.range' 168 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_176 : (List.range' 176 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_184 : (List.range' 184 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_192 : (List.range' 192 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_200 : (List.range' 200 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4_part_208 : (List.range' 208 8).all (fun k => entCheck 4 k && s8Check 4 k) = true := by decide +kernel
private theorem tripleEnt_4 : (List.range' 0 216).all (fun k => entCheck 4 k && s8Check 4 k) = true := by
  exact (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 0 8 208 tripleEnt_4_part_0 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 8 8 200 tripleEnt_4_part_8 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 16 8 192 tripleEnt_4_part_16 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 24 8 184 tripleEnt_4_part_24 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 32 8 176 tripleEnt_4_part_32 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 40 8 168 tripleEnt_4_part_40 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 48 8 160 tripleEnt_4_part_48 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 56 8 152 tripleEnt_4_part_56 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 64 8 144 tripleEnt_4_part_64 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 72 8 136 tripleEnt_4_part_72 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 80 8 128 tripleEnt_4_part_80 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 88 8 120 tripleEnt_4_part_88 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 96 8 112 tripleEnt_4_part_96 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 104 8 104 tripleEnt_4_part_104 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 112 8 96 tripleEnt_4_part_112 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 120 8 88 tripleEnt_4_part_120 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 128 8 80 tripleEnt_4_part_128 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 136 8 72 tripleEnt_4_part_136 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 144 8 64 tripleEnt_4_part_144 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 152 8 56 tripleEnt_4_part_152 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 160 8 48 tripleEnt_4_part_160 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 168 8 40 tripleEnt_4_part_168 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 176 8 32 tripleEnt_4_part_176 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 184 8 24 tripleEnt_4_part_184 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 192 8 16 tripleEnt_4_part_192 (@check_range_add (fun k => entCheck 4 k && s8Check 4 k) 200 8 8 tripleEnt_4_part_200 tripleEnt_4_part_208))))))))))))))))))))))))))
private theorem tripleBlock_4_part_0 : (List.range' 0 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_4 : (List.range' 4 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_8 : (List.range' 8 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_12 : (List.range' 12 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_16 : (List.range' 16 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_20 : (List.range' 20 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_24 : (List.range' 24 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_28 : (List.range' 28 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4_part_32 : (List.range' 32 4).all (liveBlock 4) = true := by decide +kernel
private theorem tripleBlock_4 : (List.range' 0 36).all (liveBlock 4) = true := by
  exact (@check_range_add (liveBlock 4) 0 4 32 tripleBlock_4_part_0 (@check_range_add (liveBlock 4) 4 4 28 tripleBlock_4_part_4 (@check_range_add (liveBlock 4) 8 4 24 tripleBlock_4_part_8 (@check_range_add (liveBlock 4) 12 4 20 tripleBlock_4_part_12 (@check_range_add (liveBlock 4) 16 4 16 tripleBlock_4_part_16 (@check_range_add (liveBlock 4) 20 4 12 tripleBlock_4_part_20 (@check_range_add (liveBlock 4) 24 4 8 tripleBlock_4_part_24 (@check_range_add (liveBlock 4) 28 4 4 tripleBlock_4_part_28 tripleBlock_4_part_32))))))))
theorem tripleCheck_4 : tripleCheck 4=true := by
  exact @tripleCheck_join 4 tripleEnt_4 tripleBlock_4
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_5_part_0 : (List.range' 0 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_8 : (List.range' 8 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_16 : (List.range' 16 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_24 : (List.range' 24 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_32 : (List.range' 32 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_40 : (List.range' 40 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_48 : (List.range' 48 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_56 : (List.range' 56 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_64 : (List.range' 64 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_72 : (List.range' 72 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_80 : (List.range' 80 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_88 : (List.range' 88 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_96 : (List.range' 96 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_104 : (List.range' 104 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_112 : (List.range' 112 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_120 : (List.range' 120 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_128 : (List.range' 128 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_136 : (List.range' 136 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_144 : (List.range' 144 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_152 : (List.range' 152 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_160 : (List.range' 160 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_168 : (List.range' 168 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_176 : (List.range' 176 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_184 : (List.range' 184 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_192 : (List.range' 192 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_200 : (List.range' 200 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5_part_208 : (List.range' 208 8).all (fun k => entCheck 5 k && s8Check 5 k) = true := by decide +kernel
private theorem tripleEnt_5 : (List.range' 0 216).all (fun k => entCheck 5 k && s8Check 5 k) = true := by
  exact (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 0 8 208 tripleEnt_5_part_0 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 8 8 200 tripleEnt_5_part_8 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 16 8 192 tripleEnt_5_part_16 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 24 8 184 tripleEnt_5_part_24 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 32 8 176 tripleEnt_5_part_32 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 40 8 168 tripleEnt_5_part_40 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 48 8 160 tripleEnt_5_part_48 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 56 8 152 tripleEnt_5_part_56 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 64 8 144 tripleEnt_5_part_64 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 72 8 136 tripleEnt_5_part_72 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 80 8 128 tripleEnt_5_part_80 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 88 8 120 tripleEnt_5_part_88 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 96 8 112 tripleEnt_5_part_96 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 104 8 104 tripleEnt_5_part_104 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 112 8 96 tripleEnt_5_part_112 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 120 8 88 tripleEnt_5_part_120 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 128 8 80 tripleEnt_5_part_128 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 136 8 72 tripleEnt_5_part_136 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 144 8 64 tripleEnt_5_part_144 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 152 8 56 tripleEnt_5_part_152 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 160 8 48 tripleEnt_5_part_160 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 168 8 40 tripleEnt_5_part_168 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 176 8 32 tripleEnt_5_part_176 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 184 8 24 tripleEnt_5_part_184 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 192 8 16 tripleEnt_5_part_192 (@check_range_add (fun k => entCheck 5 k && s8Check 5 k) 200 8 8 tripleEnt_5_part_200 tripleEnt_5_part_208))))))))))))))))))))))))))
private theorem tripleBlock_5_part_0 : (List.range' 0 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_4 : (List.range' 4 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_8 : (List.range' 8 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_12 : (List.range' 12 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_16 : (List.range' 16 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_20 : (List.range' 20 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_24 : (List.range' 24 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_28 : (List.range' 28 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5_part_32 : (List.range' 32 4).all (liveBlock 5) = true := by decide +kernel
private theorem tripleBlock_5 : (List.range' 0 36).all (liveBlock 5) = true := by
  exact (@check_range_add (liveBlock 5) 0 4 32 tripleBlock_5_part_0 (@check_range_add (liveBlock 5) 4 4 28 tripleBlock_5_part_4 (@check_range_add (liveBlock 5) 8 4 24 tripleBlock_5_part_8 (@check_range_add (liveBlock 5) 12 4 20 tripleBlock_5_part_12 (@check_range_add (liveBlock 5) 16 4 16 tripleBlock_5_part_16 (@check_range_add (liveBlock 5) 20 4 12 tripleBlock_5_part_20 (@check_range_add (liveBlock 5) 24 4 8 tripleBlock_5_part_24 (@check_range_add (liveBlock 5) 28 4 4 tripleBlock_5_part_28 tripleBlock_5_part_32))))))))
theorem tripleCheck_5 : tripleCheck 5=true := by
  exact @tripleCheck_join 5 tripleEnt_5 tripleBlock_5
end SigGolfCandidate.T3M.Nonbinary
end
end
end
-- ==== merged from T3M_Verify_Nonbinary_ChainsGoodChecksPart3 ====
section

section

section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_6_part_0 : (List.range' 0 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_8 : (List.range' 8 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_16 : (List.range' 16 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_24 : (List.range' 24 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_32 : (List.range' 32 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_40 : (List.range' 40 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_48 : (List.range' 48 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_56 : (List.range' 56 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_64 : (List.range' 64 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_72 : (List.range' 72 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_80 : (List.range' 80 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_88 : (List.range' 88 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_96 : (List.range' 96 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_104 : (List.range' 104 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_112 : (List.range' 112 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_120 : (List.range' 120 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_128 : (List.range' 128 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_136 : (List.range' 136 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_144 : (List.range' 144 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_152 : (List.range' 152 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_160 : (List.range' 160 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_168 : (List.range' 168 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_176 : (List.range' 176 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_184 : (List.range' 184 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_192 : (List.range' 192 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_200 : (List.range' 200 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6_part_208 : (List.range' 208 8).all (fun k => entCheck 6 k && s8Check 6 k) = true := by decide +kernel
private theorem tripleEnt_6 : (List.range' 0 216).all (fun k => entCheck 6 k && s8Check 6 k) = true := by
  exact (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 0 8 208 tripleEnt_6_part_0 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 8 8 200 tripleEnt_6_part_8 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 16 8 192 tripleEnt_6_part_16 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 24 8 184 tripleEnt_6_part_24 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 32 8 176 tripleEnt_6_part_32 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 40 8 168 tripleEnt_6_part_40 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 48 8 160 tripleEnt_6_part_48 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 56 8 152 tripleEnt_6_part_56 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 64 8 144 tripleEnt_6_part_64 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 72 8 136 tripleEnt_6_part_72 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 80 8 128 tripleEnt_6_part_80 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 88 8 120 tripleEnt_6_part_88 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 96 8 112 tripleEnt_6_part_96 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 104 8 104 tripleEnt_6_part_104 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 112 8 96 tripleEnt_6_part_112 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 120 8 88 tripleEnt_6_part_120 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 128 8 80 tripleEnt_6_part_128 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 136 8 72 tripleEnt_6_part_136 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 144 8 64 tripleEnt_6_part_144 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 152 8 56 tripleEnt_6_part_152 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 160 8 48 tripleEnt_6_part_160 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 168 8 40 tripleEnt_6_part_168 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 176 8 32 tripleEnt_6_part_176 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 184 8 24 tripleEnt_6_part_184 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 192 8 16 tripleEnt_6_part_192 (@check_range_add (fun k => entCheck 6 k && s8Check 6 k) 200 8 8 tripleEnt_6_part_200 tripleEnt_6_part_208))))))))))))))))))))))))))
private theorem tripleBlock_6_part_0 : (List.range' 0 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_4 : (List.range' 4 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_8 : (List.range' 8 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_12 : (List.range' 12 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_16 : (List.range' 16 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_20 : (List.range' 20 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_24 : (List.range' 24 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_28 : (List.range' 28 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6_part_32 : (List.range' 32 4).all (liveBlock 6) = true := by decide +kernel
private theorem tripleBlock_6 : (List.range' 0 36).all (liveBlock 6) = true := by
  exact (@check_range_add (liveBlock 6) 0 4 32 tripleBlock_6_part_0 (@check_range_add (liveBlock 6) 4 4 28 tripleBlock_6_part_4 (@check_range_add (liveBlock 6) 8 4 24 tripleBlock_6_part_8 (@check_range_add (liveBlock 6) 12 4 20 tripleBlock_6_part_12 (@check_range_add (liveBlock 6) 16 4 16 tripleBlock_6_part_16 (@check_range_add (liveBlock 6) 20 4 12 tripleBlock_6_part_20 (@check_range_add (liveBlock 6) 24 4 8 tripleBlock_6_part_24 (@check_range_add (liveBlock 6) 28 4 4 tripleBlock_6_part_28 tripleBlock_6_part_32))))))))
theorem tripleCheck_6 : tripleCheck 6=true := by
  exact @tripleCheck_join 6 tripleEnt_6 tripleBlock_6
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem tripleEnt_7_part_0 : (List.range' 0 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_8 : (List.range' 8 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_16 : (List.range' 16 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_24 : (List.range' 24 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_32 : (List.range' 32 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_40 : (List.range' 40 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_48 : (List.range' 48 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_56 : (List.range' 56 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_64 : (List.range' 64 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_72 : (List.range' 72 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_80 : (List.range' 80 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_88 : (List.range' 88 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_96 : (List.range' 96 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_104 : (List.range' 104 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_112 : (List.range' 112 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_120 : (List.range' 120 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_128 : (List.range' 128 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_136 : (List.range' 136 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_144 : (List.range' 144 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_152 : (List.range' 152 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_160 : (List.range' 160 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_168 : (List.range' 168 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_176 : (List.range' 176 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_184 : (List.range' 184 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_192 : (List.range' 192 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_200 : (List.range' 200 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7_part_208 : (List.range' 208 8).all (fun k => entCheck 7 k && s8Check 7 k) = true := by decide +kernel
private theorem tripleEnt_7 : (List.range' 0 216).all (fun k => entCheck 7 k && s8Check 7 k) = true := by
  exact (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 0 8 208 tripleEnt_7_part_0 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 8 8 200 tripleEnt_7_part_8 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 16 8 192 tripleEnt_7_part_16 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 24 8 184 tripleEnt_7_part_24 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 32 8 176 tripleEnt_7_part_32 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 40 8 168 tripleEnt_7_part_40 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 48 8 160 tripleEnt_7_part_48 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 56 8 152 tripleEnt_7_part_56 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 64 8 144 tripleEnt_7_part_64 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 72 8 136 tripleEnt_7_part_72 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 80 8 128 tripleEnt_7_part_80 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 88 8 120 tripleEnt_7_part_88 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 96 8 112 tripleEnt_7_part_96 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 104 8 104 tripleEnt_7_part_104 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 112 8 96 tripleEnt_7_part_112 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 120 8 88 tripleEnt_7_part_120 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 128 8 80 tripleEnt_7_part_128 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 136 8 72 tripleEnt_7_part_136 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 144 8 64 tripleEnt_7_part_144 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 152 8 56 tripleEnt_7_part_152 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 160 8 48 tripleEnt_7_part_160 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 168 8 40 tripleEnt_7_part_168 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 176 8 32 tripleEnt_7_part_176 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 184 8 24 tripleEnt_7_part_184 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 192 8 16 tripleEnt_7_part_192 (@check_range_add (fun k => entCheck 7 k && s8Check 7 k) 200 8 8 tripleEnt_7_part_200 tripleEnt_7_part_208))))))))))))))))))))))))))
private theorem tripleBlock_7_part_0 : (List.range' 0 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_4 : (List.range' 4 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_8 : (List.range' 8 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_12 : (List.range' 12 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_16 : (List.range' 16 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_20 : (List.range' 20 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_24 : (List.range' 24 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_28 : (List.range' 28 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7_part_32 : (List.range' 32 4).all (liveBlock 7) = true := by decide +kernel
private theorem tripleBlock_7 : (List.range' 0 36).all (liveBlock 7) = true := by
  exact (@check_range_add (liveBlock 7) 0 4 32 tripleBlock_7_part_0 (@check_range_add (liveBlock 7) 4 4 28 tripleBlock_7_part_4 (@check_range_add (liveBlock 7) 8 4 24 tripleBlock_7_part_8 (@check_range_add (liveBlock 7) 12 4 20 tripleBlock_7_part_12 (@check_range_add (liveBlock 7) 16 4 16 tripleBlock_7_part_16 (@check_range_add (liveBlock 7) 20 4 12 tripleBlock_7_part_20 (@check_range_add (liveBlock 7) 24 4 8 tripleBlock_7_part_24 (@check_range_add (liveBlock 7) 28 4 4 tripleBlock_7_part_28 tripleBlock_7_part_32))))))))
theorem tripleCheck_7 : tripleCheck 7=true := by
  exact @tripleCheck_join 7 tripleEnt_7 tripleBlock_7
end SigGolfCandidate.T3M.Nonbinary
end
end
end
