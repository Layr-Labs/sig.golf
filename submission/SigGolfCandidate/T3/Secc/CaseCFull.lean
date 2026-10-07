import SigGolfCandidate.T3.Secc.CaseCLinkSplit

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCFull : DecidableEq T3.Cache := Classical.decEq _
def PinnedC (adversary : AdversaryP)
    (Q : Correctness.Answers → QueryLog Requests → Message → WBytes → List FirstHit.QueryEvent → Prop)
    (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  ∃ generated interaction checked, Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked ∧
    generated.value.1 = Extract.honestRoot z.2 0 0 ∧ interaction.value.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
    ∃ message witness, PaddedExtraction.WitnessOf z.2 generated.value.1 forgery message witness ∧
      ¬BPB.SignedDigest interaction.value.2 message witness ∧
      BPB.CaseCAt z.2 message witness (QueryRecorded.recordedTrace z.1).events ∧
      Q z.2 interaction.value.2 message witness checked.events
def FullQ (answers : Correctness.Answers) (log : QueryLog Requests) (message : Message) (witness : WBytes)
    (_events : List FirstHit.QueryEvent) : Prop :=
  ∀ f ∈ BPair.openedPositions (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))),
    BPair.Disclosed answers log f
theorem pinned_of_caseC {adversary : AdversaryP} {z : PaddedGame.TraceResult × Correctness.Answers}
    (h : Wots.CaseCFreshPinned adversary z) : PinnedC adversary (fun _ _ _ _ _ => True) z := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC⟩ := h
  exact ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC, trivial⟩
theorem queried_notDigest_keygen (A : Correctness.Answers) (input : T3.Spec.Domain)
    (h : input ∈ SourceReplay.queried A keygen) : BPB.NotDigestQ input :=
  BPB.allQ_queried A BPB.NotDigestQ keygen keygen_notDigest input h
end SigGolfCandidate.T3.Security.CaseC
