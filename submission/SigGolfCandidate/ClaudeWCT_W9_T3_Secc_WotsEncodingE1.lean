import SigGolfCandidate.T3_Secc_WotsEncodingE1
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEncodingMatch

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
