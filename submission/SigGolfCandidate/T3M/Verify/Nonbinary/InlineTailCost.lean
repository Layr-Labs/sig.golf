import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailState

/- Exact per-row arithmetic only. The twelve leaf-prefix instructions are
   excluded here and remain charged by the later leaf stage. Each actual
   chain ECALL costs eight cycles, hence seven in addition to its word.
   This is not a wholeVerify bound or accepting-run measurement. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.T3M.Nonbinary
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def inlineChainCost (rank : Nat) : Nat := (words rank).length-12+7*hashes rank
def legacyThreeCost (rank : Nat) : Nat :=
  NCtx.chainCost 51 (digit rank 0)+NCtx.chainCost 52 (digit rank 1)+
    NCtx.chainCost 53 (digit rank 2)

theorem chain_costs_check : ((List.range 64).all fun rank =>
    decide (inlineChainCost rank+1=legacyThreeCost rank))=true := by
  decide +kernel

theorem chain_cost_saved_one (rank : Nat) (hr : rank < 64) :
    inlineChainCost rank+1=legacyThreeCost rank :=
  of_decide_eq_true (List.all_eq_true.mp chain_costs_check rank (List.mem_range.mpr hr))

-- Alreadyfused common final-return removal contributes ZERO additional cut.
theorem projected_ready_arithmetic : 23+5601+1118+706+90=7538 := rfl

#print axioms chain_costs_check
#print axioms chain_cost_saved_one
end SigGolfCandidate.T3M.Nonbinary.InlineTail
