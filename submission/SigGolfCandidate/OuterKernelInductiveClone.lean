import Lean
set_option debug.skipKernelTC false
set_option autoImplicit false
namespace OuterKernelInductiveClone
open Lean

def names (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let .inductInfo v:=ci | return #[]
  let mut ns:=#[]
  for n in v.all do
    ns:=ns.push n |>.push (n.appendCore `rec)
    if let some (.inductInfo w):=env.find? n then
      ns:=ns++w.ctors.toArray
  return ns

/-- Build an ordinary inductive declaration for later checked insertion into the kernel. -/
def declaration (env : Environment) (renameName : Name→Name) (renameExpr : Expr→Expr)
    (ci : ConstantInfo) : Option Declaration := do
  let .inductInfo v:=ci | none
  if v.numNested != 0 then none else do
    let types←v.all.mapM fun n=>do
      let some (.inductInfo w):=env.find? n | none
      let ctors←w.ctors.mapM fun c=>do
        let some (.ctorInfo cinfo):=env.find? c | none
        pure ({name:=renameName c,type:=renameExpr cinfo.type} : Constructor)
      pure ({name:=renameName n,type:=renameExpr w.type,ctors:=ctors} : InductiveType)
    pure (.inductDecl v.levelParams v.numParams types v.isUnsafe)
end OuterKernelInductiveClone
