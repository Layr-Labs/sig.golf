import SigGolfCandidate.OuterWitnessOverlay
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterWitnessFreePadded
open RiscvZkvm.Rv64 SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired
open OuterExpand OuterWitnessOverlay

theorem extract (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (off k : Nat) (h : ∀ c,c<5 → off+k≤outerNoncePos c ∨ outerNoncePos c+8≤off) :
    (witEncOuter output w nonces).extractLsb' (8*off) (8*k)=(witEncF16 output w).extractLsb' (8*off) (8*k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  by_cases hi : 8*off+j<8*21756
  · have hb:=OuterWitnessOverlay.extract_free output w nonces (off+j/8) 1 (by omega) (by
      intro c hc
      have H:=h c hc
      omega)
    have H:=congrArg (fun b : BitVec 8=>b.getLsbD (j%8)) hb
    simp only [BitVec.getLsbD_extractLsb',show j%8<8 from Nat.mod_lt _ (by decide),decide_true,Bool.true_and] at H
    have he : 8*(off+j/8)+j%8=8*off+j := by omega
    simpa only [he] using H
  · rw [BitVec.getLsbD_of_ge _ _ (by omega : 8*21756≤8*off+j),BitVec.getLsbD_of_ge _ _ (by omega : 8*21756≤8*off+j)]

#print axioms extract
end OuterWitnessFreePadded
