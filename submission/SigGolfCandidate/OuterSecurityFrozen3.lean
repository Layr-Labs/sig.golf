import SigGolfCandidate.OuterSecurityLiftPhase3Core
set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.maxSteps 2000
open Lean Elab Term
namespace OuterSecurityLiftPhase3

def mappedName (env : Environment) (m : Std.HashMap Name Name) (n : Name) : Name:=
  (m[n]?).orElse (fun _=>candidate env n) |>.getD n

def renameExpr (env : Environment) (m : Std.HashMap Name Name) (e : Expr) : Expr:=
  OuterExprRenameMemo.rename (mappedName env m) e

def repairSlots (e : Expr) : Expr:=e.replace fun x=>Id.run do
  if !x.isAppOfArity `ClaudeWCT.W9.T3.Security.LargeResidual.Paired.slot_cellValues 7 then return none
  let args:=x.getAppArgs
  match args[6]! with
  | .lam _ _ (.lam _ _ b _) _=>
    if b.hasLooseBVar 0 || b.hasLooseBVar 1 then return none
    return some (mkAppN (mkConst `OuterResidualSlotReadout.slot_cellValues) (args.set! 6 (b.lowerLooseBVars 2 2)))
  | _=>return none

def repairDeps (ciName : Name) (e : Expr) : Expr:=e.replace fun x=>Id.run do
  if ciName==`ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_knownChildren then
    if x.isAppOfArity `List.mem_append_left 5 then
      let middle:=x.getAppArgs[4]!
      if middle.isAppOfArity `List.mem_append_left 5 then
        let inner:=middle.getAppArgs[4]!
        if inner.isAppOfArity `List.mem_append_right 5 then
          let trial:=inner.getAppArgs[4]!
          if trial.isAppOfArity `ClaudeWCT.W9.T3.Security.LargeResidual.mem_wTrialDeps 4 then
            return some (mkAppN (mkConst `OuterResidualReductionHelpers.wtrial_cellDepsP) trial.getAppArgs)
  if ciName==`ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_enc_known then
    if let .letE n t _ b nd:=x then
      if n.toString=="hkc" then
        let known:=t.bindingBody!.bindingBody!
        let mem:=t.bindingBody!.bindingDomain!
        if known.isAppOfArity `ClaudeWCT.W9.T3.Security.LargeResidual.Paired.RouterState.known 2 && mem.isAppOfArity `Membership.mem 5 then
          let deps:=mem.getAppArgs[3]!
          if deps.isAppOfArity `ClaudeWCT.W9.T3.Security.LargeResidual.msgDeps 1 then
            let st:=known.getAppArgs[0]!.lowerLooseBVars 2 2
            let leaf:=deps.getAppArgs[0]!.lowerLooseBVars 1 1
            return some (.letE n t (mkAppN (mkConst `OuterResidualReductionHelpers.msgDeps_known) #[st,leaf]) b nd)
  return none

def renameDecl (env : Environment) (m : Std.HashMap Name Name) (ci : ConstantInfo) : Option Declaration:=
  let n:=`OuterLifted3 ++ ci.name
  let wide:=(`ClaudeWCT.W9.T3.Security.LargeCoupling).isPrefixOf ci.name || (`ClaudeWCT.W9.T3.Security.LargeResidual).isPrefixOf ci.name || (`ClaudeWCT.W9.T3.Security.CanonGraph).isPrefixOf ci.name || (`ClaudeWCT.W9.CanonTable).isPrefixOf ci.name
  let names : Name→Name:=fun name=>
    if nativeSource ci.name && !nativeCanRename env name then name else mappedName env m name
  let omegaWidth:=ci.name==`ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_wphantom._proof_1_1
  let edit : Expr→Expr:=fun raw=>
    let e:=repairDeps ci.name (repairSlots raw)
    OuterExprRenameMemo.rename names (if wide then e.replace (fun x=>match x with
    | .lit (.natVal 511)=>if omegaWidth then some (.lit (.natVal 4095)) else none
    | .lit (.natVal 510)=>if omegaWidth then some (.lit (.natVal 4094)) else none
    | .lit (.natVal 512)=>some (.lit (.natVal 4096))
    | _=>none) else e)
  match ci with
  | .thmInfo v=>some (.thmDecl {v with name:=n,type:=edit v.type,value:=edit v.value})
  | .defnInfo v=>
    let value:=edit v.value
    let hints:=match v.hints with
      | .regular _=>.regular (getMaxHeight env value+1)
      | h=>h
    some (.defnDecl {v with name:=n,type:=edit v.type,value:=value,hints:=hints})
  | .opaqueInfo v=>some (.opaqueDecl {v with name:=n,type:=edit v.type,value:=edit v.value})
  | .inductInfo _=>OuterKernelInductiveClone.declaration env (mappedName env m) edit ci
  | _=>none

def replayNames : Array Name := #[
  `ClaudeWCT.W9.T3.Security.LargeResidual.Paired.not_prefix_parsed,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_unknownChild,
  `ClaudeWCT.W9.T3.Security.LargeResidual.Paired.cellDepsP_sub,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_knownChildren,
  `ClaudeWCT.W9.T3.Security.LargeResidual.Paired.not_prefix_enc,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_phantom,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_wphantom._proof_1_1,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_wphantom._proof_1_2,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_wphantom,
  `ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.referenceInput,
  `ClaudeWCT.W9.T3.Security.LargeResidual.Paired.Coherent.referenceInput_eq,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_enc_known,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_digest,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.case_other,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.routeQuery_observed,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.selVals_lookup_sign,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.signItems_wct_nonce,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.observed_signFinish,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.routeSign_observed,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.interaction_le,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.routeVerdict_observed,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.table_contact_le,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.contact_le_lazy,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.interaction_le',
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.table_cert_le,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.cert_le_lazy,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.contact_cert_bound_of_excess,
  `ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.large_bound,
  `ClaudeWCT.W9.T3.Secc.Paired.t3_securityP_split,
  `ClaudeWCT.W9.T3.Secc.Paired.t3_securityP_layout_split
]

-- Replay only previously checked declarations. Every insertion uses the ordinary kernel.
run_elab do
  let original←getEnv
  let root:=`ClaudeWCT.W9.T3.Secc.Paired.t3_securityP_layout_split
  let (_,s):=(visit original root).run {}
  let seeds:=s.order.filter fun n=>(candidate original n).isSome
  let mut mapped : Std.HashMap Name Name:={}
  for n in seeds do mapped:=mapped.insert n (candidate original n).get!
  for n in replayNames do
    if mapped.contains n then continue
    let some ci:=sourceInfo original n | throwError "Missing source declaration {n}"
    let group:=OuterKernelInductiveClone.names original ci
    let mut localMap:=mapped
    for q in group do localMap:=localMap.insert q (`OuterLifted3 ++ q)
    let some decl:=renameDecl (←getEnv) localMap ci | throwError "Unsupported declaration {n}"
    let decl←if n==`ClaudeWCT.W9.T3.Security.WPair.answers_free then
      match decl with
      | .thmDecl v=>
        let value←liftM <| OuterProofNormalize.reflexivity v.value
        pure (.thmDecl {v with value:=value})
      | _=>pure decl
    else pure decl
    let hb←liftM <| Core.liftIOCore <| IO.getNumHeartbeats.toIO
    match (←getEnv).addDeclCore (hb+200000).toUSize 100000 decl none (doCheck:=true) with
    | .ok env=>
      let mut registered:=env
      for name in decl.getNames do registered:=OuterProofNormalize.namespaces registered name
      setEnv registered
      for q in group do mapped:=mapped.insert q (`OuterLifted3 ++ q)
      mapped:=mapped.insert n (`OuterLifted3 ++ n)
    | .error ex=>
      let msg←liftM <| Core.liftIOCore <| (ex.toMessageData (←getOptions)).toString
      throwError "Kernel rejected {n}: {msg}"
  unless (←getEnv).contains (`OuterLifted3 ++ root) do throwError "Missing security root"
end OuterSecurityLiftPhase3
