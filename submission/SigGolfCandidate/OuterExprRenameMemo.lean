import Lean
set_option debug.skipKernelTC false
set_option autoImplicit false
namespace OuterExprRenameMemo
open Lean
partial def visit (renameName : Name→Name) (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some r:=(←get)[e]? then return r
  let r←match e with
    | .const n ls=>pure (.const (renameName n) ls)
    | .app f a=>return .app (←visit renameName f) (←visit renameName a)
    | .lam n t b bi=>return .lam n (←visit renameName t) (←visit renameName b) bi
    | .forallE n t b bi=>return .forallE n (←visit renameName t) (←visit renameName b) bi
    | .letE n t v b nd=>return .letE n (←visit renameName t) (←visit renameName v) (←visit renameName b) nd
    | .mdata d b=>return .mdata d (←visit renameName b)
    | .proj n i b=>return .proj (renameName n) i (←visit renameName b)
    | e=>pure e
  modify fun memo=>memo.insert e r
  return r

def rename (renameName : Name→Name) (e : Expr) : Expr := (visit renameName e).run' {}
end OuterExprRenameMemo
