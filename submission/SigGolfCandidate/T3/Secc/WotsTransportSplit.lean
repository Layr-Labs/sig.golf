import SigGolfCandidate.T3.Secc.WotsTransportTable
import SigGolfCandidate.T3.Secc.SeccSufSigned

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload
def GameCaseCPinned (adversary : AdversaryP) (answers : Answers) (signed : Prop → Prop)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated interaction checked, GameSplit adversary result generated interaction checked ∧
    generated.value.1 = Extract.honestRoot answers 0 0 ∧
    interaction.value.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
    ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
      signed (BPB.SignedDigest interaction.value.2 message witness) ∧
      BPB.CaseCAt answers message witness result.events
abbrev CaseCFreshPinned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  GameCaseCPinned adversary z.2 Not (QueryRecorded.recordedTrace z.1)
abbrev CaseCSignedPinned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  GameCaseCPinned adversary z.2 id (QueryRecorded.recordedTrace z.1)
theorem GameSplit.extends {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × T3.Cache)}
    {interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)} {checked : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked) :
    SourceReplay.Extends interaction.state result.state := by
  obtain ⟨-, -, hc, rfl⟩ := h
  exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
    (FirstHit.recorded_support _ _ _ hc)
theorem GameCaseCPinned.linked {adversary : AdversaryP} {answers : Answers} {signed : Prop → Prop}
    {result : FirstHit.Recorded Bool} (h : GameCaseCPinned adversary answers signed result) :
    BPB.GameCaseC adversary answers signed result := by
  obtain ⟨generated, interaction, checked, hsplit, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hs, hC⟩ := h
  exact ⟨generated, hsplit.1, interaction, hsplit.2.1, hsplit.extends, hpk, hlen, forgery, hf, hfresh, message,
    witness, hof, hs, hC⟩
theorem caseCSignedPinned_impossible (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) : ¬CaseCSignedPinned adversary z :=
  fun h => BPB.caseC_signed_impossible adversary q hq z hz hclean h.linked
end SigGolfCandidate.T3.Security.Wots
