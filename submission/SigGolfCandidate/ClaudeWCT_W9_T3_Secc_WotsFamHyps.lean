import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamTot
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamV6

/-! # Family restart hypotheses for today's scheme and for v6 (r3-lean-seedfam)

`layoutHyps : FamHyps layoutScheme 301` (the scheme of the `Correctness` layout) and
`v6Hyps hs hz : FamHyps (v6Scheme hs) 301` (v6: lower 7-leaf, top 4-leaf families); with `seedErrorBoundF` the v6 seed
error is `≤ 602 y³/(1-y) ≤ (733/1000) y²` on the live small window. -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
open SigGolfCandidate.T3
open ClaudeWCT.W9.T3.Security.Wots.FamRestart

theorem chainCount_cases (lay : Layer) : chainCount lay = if lay = 0 then 51 else 43 := by
  fin_cases lay <;> rfl

/-- The scheme of the `Correctness` layout (v6 lower 7-leaf families, top per-leaf until the top port): charge
`max(1 · 51, 7 · 43) = 301`. -/
def layoutHyps : FamHyps layoutScheme 301 where
  caps := layoutCaps
  grp_le lay := by show WCT9.famGrp lay ≤ 2 ^ 20; unfold WCT9.famGrp; split_ifs <;> norm_num
  charge lay := by
    show WCT9.famGrp lay * chainCount lay ≤ 301
    unfold WCT9.famGrp; rw [chainCount_cases]; split_ifs <;> decide
  width lay := WCT9.famStride_ge lay
  points lay := by
    show (WCT9.famGrp lay - 1) * WCT9.famStride lay + chainCount lay < 1024
    unfold WCT9.famGrp WCT9.famStride; rw [chainCount_cases]; split_ifs <;> decide

/-- v6: lower 7-leaf (stride 43), top 4-leaf (stride 64) families, charge `max(4·51, 7·43) = 301`. -/
def v6Hyps (hs : V6.V6SeedSpec) (hz : V6.V6ZeroSpec) : FamHyps (V6.v6Scheme hs) 301 where
  caps := V6.v6Caps hs hz
  grp_le lay := by show V6.grp lay ≤ 2 ^ 20; unfold V6.grp; split_ifs <;> norm_num
  charge lay := by
    show V6.grp lay * chainCount lay ≤ 301
    unfold V6.grp; rw [chainCount_cases]; split_ifs <;> decide
  width lay := by
    show chainCount lay ≤ V6.stride lay
    unfold V6.stride; rw [chainCount_cases]; split_ifs <;> decide
  points lay := by
    show (V6.grp lay - 1) * V6.stride lay + chainCount lay < 1024
    unfold V6.grp V6.stride; rw [chainCount_cases]; split_ifs <;> decide

/-- v6 small-route seed error: `errTotF ≤ (733/1000) y²` on `y ≤ 3/2500` (via `602 y³/(1-y)`). -/
theorem v6_seedError (hs : V6.V6SeedSpec) (hz : V6.V6ZeroSpec) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q < 2 ^ 128) (hy : (q : ℝ) / 2 ^ 128 ≤ 3 / 2500) :
    (errTotF (V6.v6Scheme hs) adversary q).toReal ≤ (733 / 1000) * ((q : ℝ) / 2 ^ 128) ^ 2 :=
  seedErrorBoundF (v6Hyps hs hz) (by norm_num) adversary q hq hy

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot
