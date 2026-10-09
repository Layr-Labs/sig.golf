import SigGolfCandidate.T3.Secc.WotsTransport
import SigGolfCandidate.T3.Secc.WotsTransportSplit

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace SmallT
open _root_.SigGolfCandidate.T3.Security.Wots.Ref
structure TraceEvent where
  holds : Answers → List Entry → Prop
  mono : ∀ {T : Answers} {trace trace' : List Entry}, holds T trace → (∀ e ∈ trace, e ∈ trace') → holds T trace'
  transfer : ∀ {A T : Answers} {trace : List Entry}, ShortAgree A T →
    (∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1))) → holds A trace → holds T trace
end SmallT
open SmallT
end SigGolfCandidate.T3.Security.Wots
