import SigGolfCandidate.OuterCanonHonestInput
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterPairedStructural
open ClaudeWCT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)

def FtsTrial (T : Answers) (x : HashInput) : Prop :=
  ∃index coord heap k,index<2^31 ∧ coord<9 ∧
    (WCT9.ftsGround coord heap ∨ (2≤heap ∧ heap<4 ∧ Extract.Paired.first coord=false)) ∧
    k<OuterExtractModel.honestFtsNonce T index coord heap ∧
    x=pad64 (WCT9.wctTopInput coord index heap ((OuterExtractModel.nodes T index coord).getD (2*heap) 0)
      (BitVec.ofNat 128 (k%2^64)) ((OuterExtractModel.nodes T index coord).getD (2*heap+1) 0))
theorem ftsTrial_cell {T : Answers} {labels : OuterCanonBase.Labels} (h : OuterCanonBase.Paired.Agrees T labels)
    {x : HashInput} (ht : FtsTrial T x) :
    ∃ m : OuterCanonBase.Node, x = OuterCanonBase.Paired.cell (OuterCanonBase.secretsOf T) m labels := by
  obtain ⟨index, coord, heap, k, hi, hco, hg, hk, rfl⟩ := ht
  obtain ⟨level, c, hc, rfl, hnl⟩ : ∃ level c, c < 2 ^ (6 - level) ∧ heap = 2 ^ (6 - level) + c ∧
      OuterExtractGround.ftsNonceLevel coord level := by
    rcases hg with hg|⟨h2,h4,hf⟩
    · have h8:=WCT9.ftsGround_ge8 hg
      by_cases h16 : heap<16
      · exact ⟨3,heap-8,by norm_num;omega,by norm_num;omega,Or.inl (Or.inl rfl)⟩
      · have h32 : heap<32 ∧ coord<4:=by unfold WCT9.ftsGround at hg;omega
        exact ⟨2,heap-16,by norm_num;omega,by norm_num;omega,Or.inl (Or.inr ⟨rfl,h32.2⟩)⟩
    · exact ⟨5,heap-2,by norm_num;omega,by norm_num;omega,Or.inr ⟨rfl,hf⟩⟩
  have h23:=OuterExtractBounds.level _ _ hnl
  have hnot4 : level≠4:=by
    rcases hnl with h|h
    · unfold Extract.Paired.ftsNonceLevel at h;omega
    · omega
  obtain ⟨n, hn, hni, hnc, hnl', hnx⟩ :=
    OuterCanonBase.ftsNodeAt_some ⟨index, hi⟩ ⟨coord, hco⟩ level c (by omega)
      (by rwa [show 7 - level - 1 = 6 - level by omega])
  have htl : level ≤ OuterCanonBase.Paired.topLevel ⟨coord, hco⟩ := by
    unfold OuterCanonBase.Paired.topLevel
    split_ifs with hf
    · have hh:=OuterExtractBounds.used _ _ hnl hf;omega
    · omega
  have hpow : 2 ^ (7 - level) = 2 * 2 ^ (6 - level) := by
    rw [← pow_succ']; congr 1; omega
  have hL := OuterCanonBase.Paired.actual_nodes_label T labels h ⟨index, hi⟩ ⟨coord, hco⟩ level (2*c) htl (by omega)
  have hR := OuterCanonBase.Paired.actual_nodes_label T labels h ⟨index, hi⟩ ⟨coord, hco⟩ level (2*c+1) htl (by omega)
  have e1 : 2*(2^(6-level)+c) = 2^(7-level)+2*c := by omega
  have e2 : 2*(2^(6-level)+c)+1 = 2^(7-level)+(2*c+1) := by omega
  have hfs := OuterCanonBase.Paired.fts_step T labels h ⟨index, hi⟩ ⟨coord, hco⟩ level c hnl hc n hn
  have hsel : OuterExtractModel.honestFtsNonce T index coord (2^(6-level)+c) = OuterCanonBase.Paired.wSelNonce labels n := by
    unfold OuterExtractModel.honestFtsNonce
    rw [e2, e1]
    erw [hL, hR]
    exact congrArg Prod.fst hfs
  rw [hsel] at hk
  have ha := OuterCanonBase.Paired.wActive_trial_of_le (labels := labels) (n := n) hk.le
  have hs := OuterCanonBase.Paired.wSelNonce_lt labels n
  have hcl := OuterCanonBase.Paired.wTrialCap_le n.1.coord.val n.1.level.val
  refine ⟨.wctNode (OuterCanonBase.Paired.wWithNonce n k), ?_⟩
  rw [OuterCanonBase.Paired.cell_wctNode_active ha, OuterCanonBase.Paired.wWithNonce_nonce n (by omega)]
  simp only [OuterCanonBase.Paired.wWithNonce_index, OuterCanonBase.Paired.wWithNonce_coord, OuterCanonBase.Paired.wWithNonce_level,
    OuterCanonBase.Paired.wWithNonce_idx, hni, hnc, hnl', hnx, show 7 - level - 1 = 6 - level by omega,
    if_neg (show level ≠ 4 by omega), if_pos hnl]
  rw [e2, e1]
  erw [hL, hR]
  rfl

#print axioms ftsTrial_cell
end OuterPairedStructural
