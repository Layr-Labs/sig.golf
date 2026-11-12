import SigGolfCandidate.Merge124
import SigGolfCandidate.OuterSecurityBridgeMain
import SigGolfCandidate.OuterSecurityCleanWrapper
import SigGolfCandidate.OuterMacGame
import SigGolfCandidate.OuterNonMacExtensions
import SigGolfCandidate.OuterExtractBounds
import SigGolfCandidate.OuterPairedSatHeap
import SigGolfCandidate.OuterCanonRejected
import SigGolfCandidate.OuterCanonCapFail
import SigGolfCandidate.OuterCanonicalUntouched
import SigGolfCandidate.OuterInputShort
import SigGolfCandidate.OuterBankAllowed
import SigGolfCandidate.OuterBankNotDigest
import SigGolfCandidate.OuterProofNormalize
import SigGolfCandidate.OuterExprRenameMemo
import SigGolfCandidate.OuterKernelInductiveClone
import Lean
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Term
namespace OuterSecurityLift
structure Scan where
  seen : NameSet := {}
  reverse : Std.HashMap Name (Array Name) := {}
  order : Array Name := #[]

def worldReplacement (n : Name) : Option Name := Id.run do
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.queried_length_buildSharedCoordinate_world then return some `OuterCanonicalCount.coordinate_world
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.queried_length_buildPair_world then return some `OuterCanonicalForestCount.pair_world
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.queried_length_buildForest_world then return some `OuterCanonicalForestCount.forest_world
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.sharedNodes_world then return some `OuterCanonicalWorld.nodes_world
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.firstNodes_world then return some `OuterCanonicalWorld.firstNodes_world
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.secondNodes_world then return some `OuterCanonicalWorld.secondNodes_world
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.expectedPairRoot_world then return some `OuterCanonicalWorld.root_world
  if n==`ClaudeWCT.W9.T3.Security.WPair.Paired.forestCommitment_world then return some `OuterCanonicalWorld.commitment_world
  return none

def sourceInfo (env : Environment) (n : Name) : Option ConstantInfo := do
  let ci←env.find? ((worldReplacement n).getD n)
  match ci with
  | .thmInfo v=>return .thmInfo {v with name:=n}
  | .defnInfo v=>return .defnInfo {v with name:=n}
  | _=>return ci

def nativeSource (n : Name) : Bool :=
  (worldReplacement n).isSome || n.toString.startsWith "Outer"

def nativeCanRename (env : Environment) (n : Name) : Bool :=
  n.toString.startsWith "Outer" ||
  (`ClaudeWCT.W9.CanonTable).isPrefixOf n ||
  (`ClaudeWCT.W9.T3.Security.CanonGraph).isPrefixOf n ||
  ((env.find? n).map fun ci=>ci.type.getUsedConstants.contains `ClaudeWCT.W9.CanonTable.Omega).getD false

def deps (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let base:=ci.type.getUsedConstants ++ ((ci.value? (allowOpaque:=true)).getD (.sort .zero)).getUsedConstants
  let .inductInfo v:=ci | return if nativeSource ci.name then base.filter (nativeCanRename env) else base
  let mut allDeps:=base
  for c in v.ctors do
    allDeps:=allDeps.push c
    if let some ctor:=env.find? c then allDeps:=allDeps++ctor.type.getUsedConstants
  return if nativeSource ci.name then allDeps.filter (nativeCanRename env) else allDeps


partial def reach (rev : Std.HashMap Name (Array Name)) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | []=>seen
  | n::rest=>
    if seen.contains n then reach rev rest seen
    else reach rev (((rev[n]?).getD #[]).toList++rest) (seen.insert n)

def candidate (env : Environment) (n : Name) : Option Name := Id.run do
  if (worldReplacement n).isSome then return none
  for k in [`Hidden,`treeLabel_outer,`ftsLabel_outer,`ftsPrevLabel_outer,`cell_outer] do
    if n==(`ClaudeWCT.W9.CanonTable ++ k) then
      let target:=`OuterCanonWorld ++ k
      if env.contains target then return some target
  if (`ClaudeWCT.W9.T3.Security.CanonGraph.Paired).isPrefixOf n then
    let target:=n.replacePrefix `ClaudeWCT.W9.T3.Security.CanonGraph.Paired `OuterCanonBase.Paired
    if env.contains target then return some target
  if (`ClaudeWCT.W9.T3.Security.CanonGraph).isPrefixOf n then
    let paired:=n.replacePrefix `ClaudeWCT.W9.T3.Security.CanonGraph `OuterCanonBase.Paired
    if env.contains paired then return some paired
    let base:=n.replacePrefix `ClaudeWCT.W9.T3.Security.CanonGraph `OuterCanonBase
    if env.contains base then return some base
  for (old,new) in [(`ClaudeWCT.Bank.Paired,`OuterBankNotDigest),
      (`ClaudeWCT.Bank.Paired,`OuterBankAllowed),
      (`ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame,`OuterPaddedGame),
      (`ClaudeWCT.W9.T3.Security.PairedOuter.GameWith,`OuterGameWith),
      (`ClaudeWCT.W9.T3.Security.PairedOuter.MacGame,`OuterMacGame),
      (`ClaudeWCT.W9.PairedMac.Source,`OuterMacSource)] do
    if old.isPrefixOf n then
      let m:=n.replacePrefix old new
      if env.contains m then return some m
  for (old,new) in [(`ClaudeWCT.W9.T3.Security.Wots.PairedReference.honestInput_short,`OuterInputShort.honestInput_short),
      (`ClaudeWCT.W9.T3.Security.LargeCoupling.Paired.honestInput_short_all,`OuterInputShort.honestInput_short_all),
      (`SigGolfCandidate.Research.SharedForest.searchPreparedLayers_complete,`OuterSourceCompleteness.searchPreparedLayers_complete),
      (`ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sharedNode_untouched,`OuterCanonicalUntouched.node),
      (`ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sharedHeap_untouched,`OuterCanonicalUntouched.heap),
      (`ClaudeWCT.W9.T3.Security.Wots.PairedStructural.sat_sharedHeap,`OuterPairedStructural.sat_sharedHeap),
      (`ClaudeWCT.W9.T3.Security.Wots.PairedStructural.HonestQuery,`OuterPairedStructural.HonestQuery),
      (`ClaudeWCT.W9.T3.Security.Wots.PairedStructural.sat_sharedNode,`OuterPairedStructural.sat_sharedNode),
      (`ClaudeWCT.W9.T3.Security.Wots.PairedStructural.FtsTrial,`OuterPairedStructural.FtsTrial),
      (`ClaudeWCT.W9.T3.Security.Wots.PairedStructural.ftsTrial_cell,`OuterPairedStructural.ftsTrial_cell),
      (`ClaudeWCT.W9.T3M.Extract.Paired.ftsNonceLevel_le,`OuterExtractBounds.level),
      (`ClaudeWCT.W9.T3M.Extract.Paired.node_reference,`OuterNodeReference.reference),
      (`ClaudeWCT.W9.T3M.Extract.Paired.pairPrev,`OuterExtractModel.pairPrev),
      (`ClaudeWCT.W9.T3M.Extract.Paired.physical,`OuterExtractModel.physical),
      (`ClaudeWCT.W9.T3M.Extract.Paired.pads,`OuterExtractModel.pads),
      (`ClaudeWCT.W9.T3M.Extract.Paired.nodes,`OuterExtractModel.nodes),
      (`ClaudeWCT.W9.T3M.Extract.Paired.honestFtsNonce,`OuterExtractModel.honestFtsNonce),
      (`ClaudeWCT.W9.T3M.Extract.Paired.honestInput,`OuterExtractModel.honestInput),
      (`ClaudeWCT.W9.T3M.Extract.Paired.nodes_shared,`OuterExtractModel.nodes_shared),
      (`ClaudeWCT.W9.T3M.Extract.Paired.nodes_graph,`OuterExtractModel.nodes_graph),
      (`ClaudeWCT.W9.T3M.Extract.Paired.instDecidableFtsNonceLevel,`OuterExtractGround.instDecidableFtsNonceLevel),
      (`ClaudeWCT.W9.T3M.Extract.Paired.ftsNonceLevel,`OuterExtractGround.ftsNonceLevel),
      (`ClaudeWCT.W9.T3M.Extract.Paired.sharedNode_eq_nodeProgramP,`OuterExtractGround.sharedNode_eq_nodeProgramP),
      (`ClaudeWCT.W9.T3M.Extract.Paired.sharedNode_groundG,`OuterCanonicalNodeGround.groundG),
      (`ClaudeWCT.W9.T3M.Extract.Paired.sharedNode_ground,`OuterCanonicalNodeGround.ground),
      (`SigGolfCandidate.Research.SharedForest.sharedNode,`OuterCanonicalNode.node),
      (`SigGolfCandidate.Research.SharedForest.SharedHeapInv,`OuterCanonicalNode.HeapInv),
      (`SigGolfCandidate.Research.SharedForest.sharedNodes_graph,`OuterCanonicalNode.graph),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.sharedNode_free,`OuterCanonicalNodeQueries.free),
      (`ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sharedNode_short,`OuterCanonicalNodeQueries.short),
      (`ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sharedNode_nonEnc,`OuterCanonicalNodeQueries.nonEnc),
      (`ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.rootPool,`OuterSigning.rootPool),
      (`SigGolfCandidate.Research.SharedForest.requiredCredit,`OuterSigning.requiredCredit),
      (`ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sharedHeap_nonEnc,`OuterCanonicalNonEnc.hybrid_nonEnc),
      (`SigGolfCandidate.Research.SharedForest.recoverSharedInner_honest,`OuterCanonicalHonest.inner_honest),
      (`ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sharedHeap_short,`OuterCanonicalShort.hybrid_short),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.searchPreparedLayers_free,`OuterWorldFree.layers_free),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.queried_length_buildForest_world,`OuterCanonicalForestCount.forest_world),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.queried_length_buildPair_world,`OuterCanonicalForestCount.pair_world),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.queried_length_buildSharedCoordinate_world,`OuterCanonicalCount.coordinate_world),
      (`SigGolfCandidate.Research.SharedForest.buildForest_commitment,`OuterCanonicalModel.forest_result),
      (`SigGolfCandidate.Research.SharedForest.forestCommitment,`OuterCanonicalModel.commitment),
      (`SigGolfCandidate.Research.SharedForest.buildPair_result,`OuterCanonicalModel.pair_result),
      (`SigGolfCandidate.Research.SharedForest.buildPair,`OuterForestMoment.pair),
      (`SigGolfCandidate.Research.SharedForest.buildSingleton,`OuterForestMoment.singleton),
      (`SigGolfCandidate.Research.SharedForest.buildSharedCoordinate_result,`OuterCanonicalModel.coordinate_result),
      (`SigGolfCandidate.Research.SharedForest.buildSharedCoordinate,`OuterCanonicalModel.coordinate),
      (`SigGolfCandidate.Research.SharedForest.sharedHeap,`OuterCanonicalModel.heap),
      (`SigGolfCandidate.Research.SharedForest.sharedNodes,`OuterCanonicalModel.nodes),
      (`SigGolfCandidate.Research.SharedForest.firstNodes,`OuterCanonicalModel.firstNodes),
      (`SigGolfCandidate.Research.SharedForest.secondNodes,`OuterCanonicalModel.secondNodes),
      (`SigGolfCandidate.Research.SharedForest.expectedPairOpening,`OuterCanonicalModel.opening),
      (`SigGolfCandidate.Research.SharedForest.expectedPairRoot,`OuterCanonicalModel.root),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.sharedHeap_free,`OuterCanonicalWorld.heap_free),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.sharedNodes_world,`OuterCanonicalWorld.nodes_world),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.firstNodes_world,`OuterCanonicalWorld.firstNodes_world),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.secondNodes_world,`OuterCanonicalWorld.secondNodes_world),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.expectedPairRoot_world,`OuterCanonicalWorld.root_world),
      (`ClaudeWCT.W9.T3.Security.WPair.Paired.forestCommitment_world,`OuterCanonicalWorld.commitment_world),
      (`ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref.shared_signPayload_hashOnly,`OuterHashOnly.signPayload),
      (`SigGolfCandidate.Research.SharedForest.hashOnly_signPayload,`OuterHashOnly.signPayload),
      (`SigGolfCandidate.Research.SharedForest.hashOnly_sign,`OuterHashOnly.sign),
      (`SigGolfCandidate.Research.SharedForest.good_signFromOutput,`OuterGoodQueries.output),
      (`SigGolfCandidate.Research.SharedForest.good_searchPreparedLayers,`OuterGoodQueries.layers),
      (`SigGolfCandidate.Research.SharedForest.good_signPayload,`OuterGoodQueries.payload),
      (`SigGolfCandidate.Research.SharedForest.good_sign,`OuterGoodQueries.sign),
      (`ClaudeWCT.W9.T3M.Paired.expandB,`OuterRawExpand.expandB),
      (`ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign,`OuterAuthenticatedSign.authenticatedSign),
      (`ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign_interpretation,`OuterAuthenticatedSign.interpretation),
      (`ClaudeWCT.W9.T3.Security.PairedOuter.signFromOutput_nonMac,`OuterNonMac.output),
      (`ClaudeWCT.W9.T3.Security.PairedOuter.signPayload_nonMac,`OuterNonMac.payload),
      (`ClaudeWCT.W9.T3.Security.SharedQueries.searchPreparedLayers_allowed,`OuterSourceQueries.searchPreparedLayers_allowed),
      (`ClaudeWCT.W9.T3.Security.SharedQueries.signFromOutput_allowed,`OuterSourceQueries.signFromOutput_allowed),
      (`SigGolfCandidate.Research.SharedForest.sign,`OuterSigning.sign),
      (`SigGolfCandidate.Research.SharedForest.signPayload,`OuterSigning.signPayload),
      (`SigGolfCandidate.Research.SharedForest.signFromOutput,`OuterSigning.signFromOutput),
      (`SigGolfCandidate.Research.SharedForest.searchPreparedLayers,`OuterSigning.searchPreparedLayers),
      (`SigGolfCandidate.Research.SharedForest.buildForest,`OuterForestMoment.forest),
      (`ClaudeWCT.W9.T3M.Final.Paired.SecurityP,`OuterSecurityGame.Secure),
      (`ClaudeWCT.W9.T3M.Final.Paired.gameP,`OuterSecurityGame.game),
      (`ClaudeWCT.W9.T3M.Final.Paired.checkForgeryP,`OuterSecurityGame.checkForgery),
      (`ClaudeWCT.W9.T3M.Final.Paired.signingOracle,`OuterSecurityGame.signingOracle),
      (`ClaudeWCT.W9.T3M.Final.Paired.realExperimentP,`OuterSecurityGame.experiment)] do
    if n==old && env.contains new then return some new
  return none

partial def visit (env : Environment) (n : Name) : StateM Scan Unit := do
  if (←get).seen.contains n then return
  modify fun s=>{s with seen:=s.seen.insert n}
  if (candidate env n).isSome then
    modify fun s=>{s with order:=s.order.push n}
    return
  if let some ci:=sourceInfo env n then
    for d in deps env ci do
      modify fun s=>{s with reverse:=s.reverse.insert d ((s.reverse[d]?).getD #[] |>.push n)}
      visit env d
  modify fun s=>{s with order:=s.order.push n}

end OuterSecurityLift
