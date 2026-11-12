import SigGolfCandidate.OuterPublicQueries
import SigGolfCandidate.OuterGoodQueries
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterRawExpand
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
abbrev Result:=HashOutput×SigGolfCandidate.Research.SharedForest.Witness×List Nat
def encode (p : Result) : ClaudeWCT.W9.T3M.WBytes:=OuterExpand.witEncOuter p.1 p.2.1 p.2.2
def expandB (m : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) : M (Option ClaudeWCT.W9.T3M.WBytes):=
  Option.map encode <$> OuterExpand.expandN m pk sig

theorem expand_wire (m : Message) (pk : Digest) (s : OuterSignatureCodec.NewSig) :
    expandB m pk (ClaudeWCT.W9.T3M.SharedCodec.sigDecC (OuterSignatureCodec.expand s))=
      OuterExpand.expandCompact m pk s := rfl

theorem hashOnly (m : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    SigGolfCandidate.T3.SourceReplay.HashOnly (expandB m pk sig) :=
  SigGolfCandidate.T3.SourceReplay.hashOnly_map _ (OuterHashOnly.expandN ..)

theorem publicOnly (m : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    AllQueriesSatisfy (expandB m pk sig) SigGolfCandidate.T3M.isPublic :=
  SigGolfCandidate.T3M.allQ_map _ (OuterPublicQueries.expandN ..)

theorem good (m : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    AllQueriesSatisfy (expandB m pk sig) SigGolfCandidate.T3.Cost.GoodQuery :=
  SigGolfCandidate.T3M.allQ_map _ (OuterGoodQueries.expandN ..)
#print axioms expand_wire
end OuterRawExpand
