import SigGolfCandidate.OuterSignRebind
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Meta Elab Tactic

syntax "expose_sign_code" : tactic
syntax "close_sign_code" : tactic

elab_rules : tactic
| `(tactic| expose_sign_code) => withMainContext do
  let env←getEnv
  for d in ←getLCtx do
    if d.isImplementationDetail then continue
    let ty←instantiateMVars d.type
    if let .const n _:=ty.getAppFn then
      if Lean.isStructure env n && (←isProp ty) then
        let g←getMainGoal
        let alts←g.cases d.fvarId
        replaceMainGoal (alts.toList.map (·.mvarId))
        evalTactic (←`(tactic| all_goals expose_sign_code))
        return

elab_rules : tactic
| `(tactic| close_sign_code) => do
  let g←getMainGoal
  let ty←instantiateMVars (←g.getType)
  if ty.getAppFn.isConstOf ``SigGolfCandidate.Rv.CodeAt then
    evalTactic (←`(tactic| transfer_sign_field))
  else
    evalTactic (←`(tactic| constructor <;> close_sign_code))
