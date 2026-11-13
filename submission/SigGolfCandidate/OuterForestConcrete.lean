import SigGolfCandidate.OuterForestMoment
import SigGolfCandidate.OuterGroundFactors
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestConcrete
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh
noncomputable def fc (c : Nat) : ENNReal := mG (ftsZeroBits c 8)
noncomputable def gc (c : Nat) : ENNReal := if c<4 then mG 1 else Budgets.signingZ
noncomputable def oc (c : Nat) : ENNReal := mG (OuterGroundCore.width c)

theorem V_forest (secret : BitVec 256) (index : Nat) (hi : index<2^31)
    (selected : ForestSelection) (words : ForestWords) (cache : RCache)
    (hs : FreshF index (OuterForestBudget.AllAbove 0) cache) :
    V secret Budgets.signingZ (OuterForestMoment.forest index selected words) cache≤
      Budgets.signingZ^31121*(mG 1^80*mG 2^56)*(mG 5^8*mG 4^2) := by
  have h:=OuterForestMoment.V_forest secret Budgets.signingZ (SigGolfCandidate.Budget.one_le_zOf _)
    index hi selected words fc gc oc (fun c _ => facF_ok c) (fun c _ => facG_ok c)
    (fun c _ => OuterGroundFactors.outer_fac c) cache hs
  refine h.trans (le_of_eq ?_)
  rw [OuterForestMoment.forestCB_eq]
  norm_num [fc,gc,oc,OuterGroundCore.width,ftsZeroBits]
  ring
#print axioms V_forest
end OuterForestConcrete
