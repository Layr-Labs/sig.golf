import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopCapBad
import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpandNumericV6

/-! # img-v6 expand excess moment with the 5,239-byte codec (r3-lean-topbytes)

`expand` normalizes the top path (`SharedForest.normTop`), so the brute force is bounded by the true sibling field
only when every top node passed its zero test (`TopTreeOK`); otherwise by `searchFuel`
(`SharedForest.expand_cost_le_sign_field`, `excessField`). Hence

`E[2^((8/7)(N_e ∸ N_s)/2^20)] ≤ E[excessWeight (max field₂ field₃)] + Pr[¬TopLevelsOK] · excessWeight searchFuel
  ≤ 1.9 + 2^-135 · 4 ≤ 2`. -/

namespace SigGolfCandidate.Research.SharedExpansionV6
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Correctness (Answers builtTree treeValue)
open SigGolfCandidate.T3.SourceReplay (fixedAnswers)
open SigGolfCandidate.T3.SearchCost (cost counted_fst)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts)
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_buildTopTree)
open SigGolfCandidate.T3.CountedReplay (hashOnly_countBlocks support_replay)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand expandReplayExtra topField
  expand_cost_le_sign_field excessField TopTreeOK)
open ClaudeWCT.W9.T3.TopMoment
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The joint run, also returning the keygen's whole top tree. -/
def jointL (message : Message) : M ((Nat × Nat) × List (List Digest)) :=
  buildTopTree >>= fun levels => (fun c => (c, levels)) <$> (keygenRest levels >>= afterKeys message)

theorem jointCounts_eqL (message : Message) :
    jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig) =
      Prod.fst <$> jointL message := by
  rw [jointCounts_bind, keygen_split]
  unfold jointL afterKeys
  simp only [bind_assoc, map_bind, Functor.map_map, id_map']

/-- The excess weight as a function of the top tree. -/
noncomputable def excessG (levels : List (List Digest)) : ℝ≥0∞ :=
  open Classical in
  if TopLevelsOK levels then
    excessWeight (max (topFieldV ((levels.getD 11 []).getD 0 0)) (topFieldV ((levels.getD 11 []).getD 1 0)))
  else excessWeight ClaudeWCT.WCT9.searchFuel

theorem excessWeight_searchFuel_le : excessWeight ClaudeWCT.WCT9.searchFuel ≤ ENNReal.ofReal 4 := by
  unfold excessWeight expandReplayExtra ClaudeWCT.WCT9.searchFuel
  calc (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((1900 + 425765 + 524287 : ℕ) : ℝ) / 1048576)
      ≤ (2 : ℝ≥0∞) ^ ((2 : ℕ) : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; norm_num)
    _ = ENNReal.ofReal 4 := by rw [ENNReal.rpow_natCast]; norm_num

/-- **img-v6 expand excess moment** (5,239-byte codec): `E[2^((8/7)(N_e ∸ N_s)/2^20)] ≤ 2` on the honest joint run. -/
theorem expand_excess_moment (secret : BitVec 256) (message : Message)
    (hsign : ∀ cache, HashOnly (sign cache message)) (hexp : ∀ pk sig, HashOnly (expand message pk sig))
    (hrest : ∀ levels, HashOnly (keygenRest levels))
    (hpre : TopPrefixOK secret) (hnum : ExpandExcessNumeric19) :
    expectedValue (roRun secret (jointCounts keygen (fun keys => sign keys.2 message)
      (fun keys sig => expand message keys.1 sig)) ∅)
      (fun r => (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((r.1.2 - r.1.1 : ℕ) : ℝ) / 1048576)) ≤ 2 := by
  classical
  rw [jointCounts_eqL, roRun_map, expectedValue_map]
  have hho : HashOnly (jointL message) := by
    unfold jointL
    refine hashOnly_bind hashOnly_buildTopTree (fun levels => hashOnly_map _ (hashOnly_bind (hrest levels) ?_))
    intro keys
    unfold afterKeys jointCounts
    refine hashOnly_bind (hashOnly_pure _) (fun keys => ?_)
    refine hashOnly_bind (hashOnly_countBlocks _ (hsign keys.2)) (fun signed => ?_)
    cases signed.1 with
    | none => exact hashOnly_pure _
    | some sig => exact hashOnly_bind (hashOnly_countBlocks _ (hexp keys.1 sig)) (fun _ => hashOnly_pure _)
  -- pointwise: the excess is bounded by the top-tree function `excessG`
  have hpt : ∀ r ∈ support (roRun secret (jointL message) ∅),
      (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * (((r.1.1.2 - r.1.1.1 : ℕ)) : ℝ) / 1048576) ≤ excessG r.1.2 := by
    intro r hr
    obtain ⟨hash, _, heval⟩ := support_replay secret _ hho ∅ r hr
    set answers := fixedAnswers secret hash
    have hj : evalWithAnswerFn answers (jointL message) =
        (evalWithAnswerFn answers (jointCounts keygen (fun keys => sign keys.2 message)
          (fun keys sig => expand message keys.1 sig)), builtTree answers 0 0) := by
      rw [jointCounts_eqL]
      unfold jointL
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_map, SigGolfCandidate.T3.Correctness.eval_buildTopTree]
    have hle := eval_joint_cost_le_add answers keygen (fun keys => sign keys.2 message)
      (fun keys sig => expand message keys.1 sig) (expandReplayExtra + excessField answers)
      (fun sig hs => by
        have := expand_cost_le_sign_field answers message sig hs
        omega)
    rw [heval, hj]
    simp only
    have hsub : (evalWithAnswerFn answers (jointCounts keygen (fun keys => sign keys.2 message)
        (fun keys sig => expand message keys.1 sig))).2 - (evalWithAnswerFn answers (jointCounts keygen
        (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig))).1 ≤
        expandReplayExtra + excessField answers := by omega
    have hEq : excessG (builtTree answers 0 0) = excessWeight (excessField answers) := by
      unfold excessG excessField
      by_cases hT : TopTreeOK answers
      · have hL : TopLevelsOK (builtTree answers 0 0) := hT
        rw [if_pos hL, if_pos hT]
        rfl
      · have hL : ¬TopLevelsOK (builtTree answers 0 0) := hT
        rw [if_neg hL, if_neg hT]
    rw [hEq]
    unfold excessWeight
    apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    have hc := (Nat.cast_le (α := ℝ)).mpr hsub
    have h87 : (0 : ℝ) ≤ 8 / 7 := by norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc h87) (by norm_num)
  refine (expectedValue_mono_of_support hpt).trans ?_
  change Ev secret (jointL message) ∅ (fun r => excessG r.1.2) ≤ 2
  unfold jointL
  rw [Ev_bind]
  have hinner : ∀ (levels : List (List Digest)) (σ : RCache),
      Ev secret ((fun c => (c, levels)) <$> (keygenRest levels >>= afterKeys message)) σ
        (fun r => excessG r.1.2) ≤ excessG levels := by
    intro levels σ
    unfold Ev
    rw [roRun_map, expectedValue_map]
    exact Ev_const_le secret _ σ _
  refine le_trans (Ev_mono _ _ _ (fun r => hinner r.1 r.2)) ?_
  -- split off the cap-exhaustion event
  have hsplitG : ∀ r : List (List Digest) × RCache, excessG r.1 ≤
      excessWeight (max (topFieldV ((r.1.getD 11 []).getD 0 0)) (topFieldV ((r.1.getD 11 []).getD 1 0))) +
        (if TopLevelsOK r.1 then 0 else 1) * excessWeight ClaudeWCT.WCT9.searchFuel := by
    intro r
    unfold excessG
    split
    · simp
    · simp
  refine le_trans (Ev_mono _ _ _ hsplitG) ?_
  have hadd : Ev secret buildTopTree ∅ (fun r =>
      excessWeight (max (topFieldV ((r.1.getD 11 []).getD 0 0)) (topFieldV ((r.1.getD 11 []).getD 1 0))) +
        (if TopLevelsOK r.1 then 0 else 1) * excessWeight ClaudeWCT.WCT9.searchFuel) =
      Ev secret buildTopTree ∅ (fun r =>
        excessWeight (max (topFieldV ((r.1.getD 11 []).getD 0 0)) (topFieldV ((r.1.getD 11 []).getD 1 0)))) +
      Ev secret buildTopTree ∅ (fun r => if TopLevelsOK r.1 then 0 else 1) *
        excessWeight ClaudeWCT.WCT9.searchFuel := by
    unfold Ev
    rw [expectedValue_add, expectedValue_mul_const]
  rw [hadd]
  have h1 : Ev secret buildTopTree ∅ (fun r =>
      excessWeight (max (topFieldV ((r.1.getD 11 []).getD 0 0)) (topFieldV ((r.1.getD 11 []).getD 1 0)))) ≤
      ENNReal.ofReal (19 / 10) := by
    obtain ⟨γ, pre, sel, k, hsplit, hbound⟩ := hpre
    rw [hsplit]
    exact (Ev_buildTop_rootChildren secret pre sel k hbound excessWeight).trans hnum
  have h2 := Ev_buildTopTree_bad secret
  calc _ ≤ ENNReal.ofReal (19 / 10) + ENNReal.ofReal (1 / 2 ^ 135) * ENNReal.ofReal 4 :=
        add_le_add h1 (mul_le_mul' h2 excessWeight_searchFuel_le)
    _ = ENNReal.ofReal (19 / 10 + 1 / 2 ^ 135 * 4) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by norm_num)
    _ = 2 := by norm_num

#print axioms expand_excess_moment
end SigGolfCandidate.Research.SharedExpansionV6
