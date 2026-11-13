import SigGolfCandidate.OuterRecoverBudget
import SigGolfCandidate.OuterExpand
import SigGolfCandidate.Merge054
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterExpansionWorst
open scoped ENNReal
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.SearchCost (cost cost_bound)
theorem bound_expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    CBound (fun _ => True) expandWorstCost (OuterExpand.expandN message pk sig) := by
  unfold OuterExpand.expandN
  split
  · exact .pure _ _ trivial
  · refine (bound_sharedDigestSearch _ _ _ _).bind' (l := 25866 + recoverWorst 4 + searchFuel)
      (fun found _ => ?_) (by rw [recoverWorst_four]; unfold expandWorstCost searchFuel digestAttemptLimit; omega)
    rcases found with _ | ⟨counter, output⟩
    · exact .pure _ _ trivial
    · dsimp only
      refine (OuterRecoverBudget.forest_bound _ _ _ _).bind' (l := recoverWorst 4 + searchFuel) (fun forest _ => ?_) (by omega)
      refine (bound_recoverHintedLayers _ _ _ 4 _).bind' (l := searchFuel) (fun layers _ => ?_) (by omega)
      rcases layers with _ | layers
      · exact .pure _ _ trivial
      · dsimp only
        split
        · exact .pure _ _ trivial
        · split
          · exact .pure _ _ trivial
          · refine (ClaudeWCT.WCT9.Cost.bound_searchTop _ _ _ _ _ _).bind' (l := 0) (fun c _ => ?_) (by omega)
            cases c <;> exact .pure _ 0 trivial

theorem bound_expandCompact (message : Message) (pk : Digest) (sig : OuterSignatureCodec.NewSig) :
    CBound (fun _=>True) expandWorstCost (OuterExpand.expandCompact message pk sig) := by
  unfold OuterExpand.expandCompact
  exact (bound_expandN ..).map _ (fun _ _=>trivial)

theorem cost_expandCompact (answers : Answers) (message : Message) (pk : Digest) (sig : OuterSignatureCodec.NewSig) :
    cost answers (OuterExpand.expandCompact message pk sig)≤2^24 := cost_bound answers (bound_expandCompact ..)

theorem excess_weight (n : Nat) (hn : n≤2^24) :
    (2:ℝ≥0∞)^((8/7:ℝ)*(n:ℝ)/1048576)≤ENNReal.ofReal (2^19) := by
  calc
    _ ≤ (2:ℝ≥0∞)^((19:Nat):ℝ) := by
      apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
      have hnR : (n:ℝ)≤2^24 := by exact_mod_cast hn
      calc
        (8/7:ℝ)*(n:ℝ)/1048576 ≤ (8/7:ℝ)*(2^24:ℝ)/1048576 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnR (by norm_num)) (by norm_num)
        _ ≤ 19 := by norm_num
    _ = ENNReal.ofReal (2^19) := by
      rw [ENNReal.rpow_natCast,ENNReal.ofReal_pow (by norm_num)]
      norm_num

#print axioms excess_weight

#print axioms bound_expandN
#print axioms cost_expandCompact
end OuterExpansionWorst
