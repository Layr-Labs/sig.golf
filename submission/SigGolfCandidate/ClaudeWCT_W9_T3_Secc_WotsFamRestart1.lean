import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamCore
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafRestart
set_option Elab.async false

/-! # Family restart, step P5c-1: contacts and markers under family congruence (r3-lean-seedfam)

Family analogues of `Normalized.Restart.{frontierValue_leafCongr, contactAt_leafCongr, markerAt_leafCongr, fill_congr,
GDr_leaf}` (WotsLeafRestart): the honest events of every SOURCE chain are invariant under `FamGame.FamCongr`; a source
chain in the family is a real member (its leaf is in the tree). -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestartN
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart (source_bounds)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
variable {S : FamScheme} {F : FamAddr} {T T' : Answers}
  (hC : FamGame.FamCongr S (sourceMessages T) F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
  (hFtree : F.tree < 2 ^ 40)
include hC hF

include hFtree in
theorem frontierValue_famCongr {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    CanonicalRef.frontierValue T' (sourceMessages T') b = CanonicalRef.frontierValue T (sourceMessages T) b := by
  rw [FamGame.sourceMessages_congrF hC hF]
  obtain ⟨hbt, hbl⟩ := source_bounds hb
  by_cases hal : FamAlias S F b.key.lay b.key.tree b.key.leaf
  · obtain ⟨l, hla, hleq⟩ := famAlias_member S hal
    have hlt := famLeaf_lt S hF l
    have hk : b.key = famLeaf (S.grp F.lay) F l := by
      have := hla.eq_of_lt hbt (by omega) hFtree (by omega)
      cases hbk : b.key
      rw [hbk] at this
      exact this
    have hreal : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 := hb.1.2
      rw [hk] at h1
      exact h1
    have hbc : b.chain < chainCount F.lay := by have := hb.2; rwa [hal.1] at this
    cases b with
    | mk K c =>
      simp only at hk hbc
      subst hk
      exact hC.front l hreal c hbc
  · unfold CanonicalRef.frontierValue ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
    rw [FamGame.depth_congrF hC.toFamAgree b, wotsSeed_outF hC.toFamAgree (famBound_lt S hF) hbl hal]
    exact eval_chain_outF hC.toFamAgree hF hbl (by have := Mask.chainCount_le b.key.lay; have := hb.2; omega)
      (fun h => hal h.1) (by have := CanonicalRef.Mask.depth_le_seven T (sourceMessages T) b; omega) _

include hFtree in
theorem contactAt_famCongr (trace : List Entry) {b : ChainAddr} (hb : WotsExtract.SourceChain7 b) :
    CanonicalRef.ContactAt T' (sourceMessages T') trace b ↔ CanonicalRef.ContactAt T (sourceMessages T) trace b := by
  unfold CanonicalRef.ContactAt
  rw [FamGame.sourceMessages_congrF hC hF]
  rw [FamGame.depth_congrF hC.toFamAgree b]
  have hf := frontierValue_famCongr hC hF hFtree hb
  rw [FamGame.sourceMessages_congrF hC hF] at hf
  rw [hf]

theorem markerAt_famCongr (trace : List Entry) (b : ChainAddr) :
    CanonicalRef.MarkerAt T' (sourceMessages T') trace b ↔ CanonicalRef.MarkerAt T (sourceMessages T) trace b := by
  unfold CanonicalRef.MarkerAt CanonicalRef.referenceInput CanonicalRef.referenceDigits
  rw [FamGame.sourceMessages_congrF hC hF, FamGame.referenceSearch_congrF hC.toFamAgree]

end Congr

#print axioms frontierValue_famCongr
#print axioms contactAt_famCongr
#print axioms markerAt_famCongr
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamRestartN
