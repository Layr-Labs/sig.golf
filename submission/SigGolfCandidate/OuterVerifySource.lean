import SigGolfCandidate.OuterFixedForestReplay
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifySource
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest

def verify (message : Message) (pk : Digest) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat) : M Bool := do
  if w.digestCounter.toNat≥digestVerifyWindow then return false
  let output←digest w.signature.rho message w.digestCounter
  if !verifyDigestAccepted output then return false
  let forest←OuterFixedForest.forest (digestIndex output) (forestSelectionFromOutput output)
    (forestWordsFromOutput output) w.signature.forest w.ftsNonces w.ftsNonces16 ns5
  let some root←verifyLayers w (digestIndex output) 4 (.pair forest.1 forest.2) | pure false
  pure (root==pk)

def fromRecovered (sig : SigGolfCandidate.Research.SharedForest.Signature) (counter : BitVec 32)
    (result : RecoveredLayers) (ns3 ns2 : List Nat) : SigGolfCandidate.Research.SharedForest.Witness:=
  ⟨sig,counter,fun lay=>result.counters.getD lay.val 0,!(result.lows.getD 0 true),result.nonces,
    fun lay=>result.lowerNonces.getD lay.val [],ns3,ns2⟩

theorem from_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (ho : evalWithAnswerFn answers (digest sig.rho message counter)=output)
    (ha : verifyDigestAccepted output=true)
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.1
        (evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1.2))=some result)
    (hpk : result.root=pk) :
    let forest:=evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)
    evalWithAnswerFn answers (verify message pk (fromRecovered sig counter result forest.2.1 forest.2.2.1) forest.2.2.2)=true := by
  have hc : ¬counter.toNat≥digestVerifyWindow:=Nat.not_le.mpr counter.isLt
  let forest:=evalWithAnswerFn answers (OuterForestCorrectness.recoverForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)
  have hv:=(recoverHintedLayers_verified answers sig (digestIndex output) 4 le_rfl _ _ hr).2.2.2.2
    (fromRecovered sig counter result forest.2.1 forest.2.2.1) rfl (by intros;rfl) rfl rfl (by intros;rfl)
  dsimp only [fromRecovered, forest] at hv
  have hn:=OuterFixedForestReplay.eval_forest answers (digestIndex output) (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest
  simp only [verify,fromRecovered,hc,if_false,evalWithAnswerFn_bind,ho,ha,Bool.not_true,Bool.false_eq_true,
    hn,hv,evalWithAnswerFn_pure,hpk,beq_self_eq_true]
#print axioms from_recovered
end OuterVerifySource
