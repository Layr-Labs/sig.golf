import SigGolfCandidate.OuterHonestCarriers
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHonestInnerCarriers
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete (ftsTreeOK ftsTreeOK_at authAt_four_ok authAt_three_ok)
open OuterHybridForestComplete OuterHybridForestCorrectness OuterHybridGlobalCorrectness OuterHonestCarriers
attribute [local irreducible] sharedNodes OuterCoordinateCorrectness.nodes

theorem coordOKb_fts {first : Bool} {coord : Nat} {nodes : Array Digest} (h : coordOKb first coord nodes=true) :
    ftsTreeOK coord nodes=true := by
  simp only [coordOKb,Bool.and_eq_true] at h
  exact h.1

theorem signFromOutput_ftsPathOK (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hfts : ForestsOK answers) (rho : Digest) (counter : BitVec 32) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers
      (OuterSigning.signFromOutput cache rho counter output) = some w) :
    FtsPathOK w.signature := by
  have hf := signFromOutput_forest answers cache rho counter output w he
  have hT := eval_forestCheck_true answers (digestIndex output) (hfts (digestIndex output) (digestIndex_lt output))
  refine ⟨fun p => ?_, ?_, fun p => ?_⟩
  · rw [hf, forest_pairs]
    exact ⟨authAt_four_ok (firstChild _).isLt (fun heap h8 h16 => ftsTreeOK_at (coordOKb_fts ((hT.1 p.val p.isLt).1)) h8 h16),
      authAt_four_ok (secondChild _).isLt (fun heap h8 h16 => ftsTreeOK_at (coordOKb_fts ((hT.1 p.val p.isLt).2)) h8 h16)⟩
  · rw [hf, forest_singleton_path]
    exact authAt_four_ok (forestSelectionFromOutput output).singleton.isLt (fun heap h8 h16 => ftsTreeOK_at (coordOKb_fts hT.2) h8 h16)
  · rw [hf, forest_pairs]
    have hp4 : p.val < 4 := by have := p.isLt; omega
    exact ⟨authAt_three_ok (firstChild _).isLt (fun heap h8 h16 => ftsTreeOK_at (coordOKb_fts ((hT.1 p.val hp4).1)) h8 h16),
      authAt_three_ok (secondChild _).isLt (fun heap h8 h16 => ftsTreeOK_at (coordOKb_fts ((hT.1 p.val hp4).2)) h8 h16)⟩


#print axioms signFromOutput_ftsPathOK
end OuterHonestInnerCarriers
