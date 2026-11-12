import SigGolfCandidate.OuterWitnessFreePadded
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifierLayers
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired W9Machine
open OuterExpand

theorem free (off k : Nat) (h : off+k≤112 ∨ 7664≤off) :
    ∀ c,c<5 → off+k≤outerNoncePos c ∨ outerNoncePos c+8≤off := by
  intro c hc
  unfold outerNoncePos outerCoord V3.regionOffset
  interval_cases c <;> norm_num <;> omega

theorem extract (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (off k : Nat) (h : off+k≤112 ∨ 7664≤off) :
    (witEncOuter output w ns).extractLsb' (8*off) (8*k)=(witEncF16 output w).extractLsb' (8*off) (8*k) :=
  OuterWitnessFreePadded.extract output w ns off k (free off k h)

theorem dig (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (off : Nat) (h : off+16≤112 ∨ 7664≤off) :
    ClaudeWCT.W9.T3M.wdig (witEncOuter output w ns) off=ClaudeWCT.W9.T3M.wdig (witEncF16 output w) off := extract output w ns off 16 h

@[simp] theorem rho (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) :
    wrho (witEncOuter output w ns)=w.signature.rho := by
  rw [←wrho_witEncF16 output w]
  unfold wrho
  exact dig output w ns rhoOff (Or.inr (by decide))

@[simp] theorem dc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) :
    wdc (witEncOuter output w ns)=w.digestCounter := by
  rw [←wdc_witEncF16 output w]
  unfold wdc wle32
  exact extract output w ns dcOff 4 (Or.inr (by decide))

@[simp] theorem topHigh (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) :
    wtopHigh (witEncOuter output w ns)=w.topHigh := by
  rw [←wtopHigh_witEncF16 output w]
  unfold wtopHigh wchoice
  rw [extract output w ns choiceOff 1 (Or.inr (by decide))]

theorem layers (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (n : Nat) (left right : Digest) (hn : n≤4) :
    layersCanonicalBC (witEncOuter output w ns) (digestIndex output) n (.pair left right)=
      SigGolfCandidate.Research.SharedForest.verifyLayers w (digestIndex output) n (.pair left right) := by
  have hrow (lay : Layer):=ClaudeWCT.W9.T3M.PairedNonce.rowBlock_out (digestIndex output) lay
  rw [layersCanonicalBC_eq_H,topHigh,
    layersCanonicalBCH_tail _ (witEncOuter output w ns) (witEncF16 output w) _
      (fun off h1 _=>dig output w ns off (Or.inr h1))
      (fun lay=>by
        unfold wleafHigh
        rw [dig output w ns _ (Or.inr (by have :=leafBufferBase_bounds lay;omega))])
      (fun lay=>by
        unfold wbcCtr wle32 bcCounterOff
        exact extract output w ns _ 4 (by rcases hrow lay with h|h <;>omega))
      (fun lay=>by
        unfold wbcPad bcCounterOff
        exact extract output w ns _ 12 (by rcases hrow lay with h|h <;>omega))
      (fun lay=>by
        unfold wbcHigh
        rw [dig output w ns _ (by rcases hrow lay with h|h <;>omega)])]
  rw [←wtopHigh_witEncF16 output w,←layersCanonicalBC_eq_H]
  exact layersCanonicalBC_witEncF16 output w n left right hn
#print axioms layers
end OuterVerifierLayers
