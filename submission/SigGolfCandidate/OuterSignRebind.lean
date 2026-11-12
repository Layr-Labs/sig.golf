import SigGolfCandidate.OuterSignTransfers
import SigGolfCandidate.Merge096
import Lean.Elab.Tactic
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Meta Elab Tactic

elab "transfer_sign_field" : tactic => do
  let g←getMainGoal
  let ty←instantiateMVars (←g.getType)
  unless ty.getAppFn.isConstOf ``SigGolfCandidate.Rv.CodeAt do
    throwError "expected a CodeAt goal"
  let args:=ty.getAppArgs
  let pc:=args[1]!
  unless pc.getAppFn.isConstOf ``SigGolfCandidate.T3M.pcOf do
    throwError "expected pcOf address"
  let b:=pc.getAppArgs[0]!
  let fn←mkAppOptM ``OuterSignTransfers.code #[some b,some args[2]!]
  replaceMainGoal (←g.apply fn)
  evalTactic (←`(tactic| all_goals first | assumption | decide +kernel))

namespace OuterSignRebind
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Sign

theorem topSetup : SharedTopSetup.Code OuterImages.signImage := by
  have old:=SharedTopSetup.installed_code
  cases old
  constructor <;> transfer_sign_field
#print axioms topSetup
end OuterSignRebind
