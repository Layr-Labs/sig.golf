import SigGolfCandidate.Merge051

namespace SigGolfCandidate.T3M.Verify

deriving instance Lean.ToExpr for Br
deriving instance Lean.ToExpr for PRes

open Lean Meta Elab Command

/-- Freeze a closed symbolic path result as a literal; the generated equality is kernel checked. -/
elab "path_block " id:ident " := " t:term : command => do
  liftTermElabM do
    let e ← Term.elabTermEnsuringType t (mkConst ``PRes)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let lit ← SigGolfCandidate.Rv.evalToLiteral e
    let base := (← getCurrNamespace) ++ id.getId
    let resName := base ++ `res
    addDecl <| Declaration.defnDecl {
      name := resName, levelParams := [], type := mkConst ``PRes, value := lit,
      hints := .abbrev, safety := .safe }
    enableRealizationsForConst resName
    compileDecls #[resName]
    let ty ← mkEq e (mkConst resName)
    addDecl <| Declaration.thmDecl {
      name := base, levelParams := [], type := ty, value := (← mkEqRefl (mkConst resName)) }
    enableRealizationsForConst base

end SigGolfCandidate.T3M.Verify
