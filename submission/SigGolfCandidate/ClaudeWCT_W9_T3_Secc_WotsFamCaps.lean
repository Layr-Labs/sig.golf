import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamCongr
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafCore

/-! # Family restart: the reveal caps (r3-lean-seedfam)

`FamCaps S`: the policy fact behind `revSet_card_le`, per leaf (every leaf's reference digits have at most `zcap lay`
zeros: lower 5, top 7 in T51 (9 in #938's v6); `famCount - 3` today) and the coefficient budget of every family
(`zcap · members + 3 ≤ size`, members = `min grp (2^height − grp·f)`, so the short last family is covered).
`leafCaps` instantiates it for today's scheme from `Core.revSet_card_le`. -/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
attribute [local instance] Classical.propDecidable

/-- Real members of family `f` of layer `lay`. -/
def famMembers (S : FamScheme) (lay : Layer) (f : Nat) : Nat := min (S.grp lay) (2 ^ height lay - S.grp lay * f)

/-- Reveal caps of a family scheme. -/
structure FamCaps (S : FamScheme) where
  zcap : Layer → Nat
  zeros_le : ∀ {U : Finset HashInput} (R : Tables U) (L : LeafAddr),
    (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0).card ≤ zcap L.lay
  size_ge : ∀ lay f, zcap lay * famMembers S lay f + 3 ≤ S.size lay f

/-- Caps of the `Correctness` layout with today's producer: top 7 (T51; #938: 9), lower 5 revealed seeds per leaf;
the family budgets `7 · 4 + 3 = 31` (top) and `5 r + 3 = famSize` (lower, `r` real members). -/
def layoutCaps : FamCaps layoutScheme where
  zcap lay := if lay = 0 then 7 else 5
  zeros_le R L := by
    have h := Core.revSet_card_le_cap L R
    unfold Core.revSet at h
    exact h
  size_ge lay f := by
    show (if lay = 0 then 7 else 5) * min (WCT9.famGrp lay) (2 ^ height lay - WCT9.famGrp lay * f) + 3 ≤
      WCT9.famSize lay f
    unfold WCT9.famGrp WCT9.famSize
    split_ifs with h
    · -- T51: 4-leaf top families, 7 · 4 + 3 = 31 = topCoefCount (img-v6: 9 · 4 + 3 = 39)
      have := min_le_left 4 (2 ^ height lay - 4 * f)
      simp only [SigGolfCandidate.T3.topCoefCount]; omega
    · exact le_rfl

#print axioms layoutCaps
end ClaudeWCT.W9.T3.Security.Wots.FamRestart
