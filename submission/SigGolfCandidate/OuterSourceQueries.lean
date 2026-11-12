import SigGolfCandidate.OuterForestDomains
import SigGolfCandidate.OuterSigning
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterSourceQueries
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.SharedQueries
variable (Q : Spec.Domain→Prop) (hQ : TailAllowed Q)
include hQ
theorem searchPreparedLayers_allowed (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) :
    AllQueriesSatisfy (OuterSigning.searchPreparedLayers cache index prepared forest) Q := by
  unfold OuterSigning.searchPreparedLayers
  apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
  intro found
  rcases found with _ | ⟨counter0,digits0,low0⟩
  · exact SourceQueries.pure_allowed Q _
  · dsimp only
    split
    · exact SourceQueries.pure_allowed Q _
    · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
      intro found
      rcases found with _ | ⟨counter1,digits1,low1⟩
      · exact SourceQueries.pure_allowed Q _
      · dsimp only
        split
        · exact SourceQueries.pure_allowed Q _
        · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
          intro found
          rcases found with _ | ⟨counter2,digits2,low2⟩
          · exact SourceQueries.pure_allowed Q _
          · dsimp only
            split
            · exact SourceQueries.pure_allowed Q _
            · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
              intro found
              rcases found with _ | ⟨counter3,digits3,low3⟩
              · exact SourceQueries.pure_allowed Q _
              · exact SourceQueries.bind_allowed Q (hQ.top ..) fun _ => SourceQueries.pure_allowed Q _

theorem signFromOutput_allowed
    (hf : ∀ index selected words,AllQueriesSatisfy (OuterForestMoment.forest index selected words) Q)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    AllQueriesSatisfy (OuterSigning.signFromOutput cache rho counter output) Q := by
  unfold OuterSigning.signFromOutput
  exact SourceQueries.bind_allowed Q (hf ..) fun _=>
    SourceQueries.bind_allowed Q (prepareRoots_allowed Q hQ ..) fun _=>
      SourceQueries.bind_allowed Q (searchPreparedLayers_allowed Q hQ ..) fun found=>by
        cases found <;> exact SourceQueries.pure_allowed Q _
#print axioms signFromOutput_allowed
end OuterSourceQueries

namespace OuterNonMac
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest SigGolfCandidate.T3.Security
open _root_.SiggolfT3Mac4.Source (NonMac non_mac_tweak)
open ClaudeWCT.W9.T3.Security.PairedOuter (tail_nonMac digestSearch_nonMac)

theorem fts (index : Nat) (q : Spec.Domain)
    (hq : ClaudeWCT.W9.T3.Freshness.Paired.FtsQuery index q) : NonMac q := by
  rcases hq with hq|⟨coord,heap,left,pad,right,hc,hl,hh,rfl⟩
  · rcases q with (tag|input)|(tweak|message|region)
    · exact hq.elim
    · trivial
    · obtain ⟨coord,pair,hc,hp,rfl⟩:=hq
      exact ⟨non_mac_tweak 8 coord index 0 pair (by decide) 0,non_mac_tweak 8 coord index 0 pair (by decide) 1⟩
    · exact hq.elim
    · exact hq.elim
  · trivial

theorem forest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (OuterForestMoment.forest index selected words) NonMac :=
  SigGolfCandidate.T3M.allQ_mono (OuterForestDomains.forest_queries index selected words) (fts index)

theorem payload (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (OuterSigning.signPayload cache message) NonMac := by
  unfold OuterSigning.signPayload
  apply SourceQueries.bind_allowed NonMac
    (SourceQueries.privateNonce_allowed NonMac _root_.SiggolfT3Mac4.Source.nonce_coordinate_other _)
  intro rho
  apply SourceQueries.bind_allowed NonMac (digestSearch_nonMac ..)
  intro found
  rcases found with _|⟨counter,output⟩
  · exact SourceQueries.pure_allowed NonMac _
  · apply SourceQueries.bind_allowed NonMac (OuterSourceQueries.signFromOutput_allowed NonMac tail_nonMac forest ..)
    intro signed
    cases signed <;> exact SourceQueries.pure_allowed NonMac _
#print axioms payload
end OuterNonMac
