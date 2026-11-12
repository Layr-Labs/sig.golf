import Lean
set_option debug.skipKernelTC false
set_option autoImplicit false
namespace OuterProofNormalize
open Lean Meta
/-- Keep reflexivity arguments in weak-head form to avoid comparing two unused world tables. -/
def reflexivity (value : Expr) : MetaM Expr :=
  Meta.transform value (pre:=fun e=>do
    let f:=e.getAppFn
    let args:=e.getAppArgs
    if f.isConstOf ``Eq.refl && args.size==2 then
      let reduced←withTransparency .all (whnf args[1]!)
      return .done (mkApp2 f args[0]! reduced)
    return .continue)

partial def namespaces (env : Environment) : Name→Environment
  | .str parent _=>namespaces (env.registerNamespace parent) parent
  | _=>env
end OuterProofNormalize
