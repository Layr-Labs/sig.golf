import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamProg2

/-! # Family restart, step P2c: the prefix-game fill with a family overridden (r3-lean-seedfam)

Family analogues of the `Fill` section of `Normalized.RawLeaf` (WotsLeafProg): the chain `a = chainOfF F ca` of
family `F` is filled (`fillTable a (ovF … X) e`); the other step-0 rows of the family read `X.2`, private cells read the
override, every reference depth is unchanged, and the family seeds read `familyEval X.1`.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf (fillTable raw_ov_const)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable

/-- Seeds depend on the answers only through the private cells of their layer and tree (any `FamScheme`). -/
theorem wotsSeed_congr_cellsS (S : FamScheme) {T T' : Answers} {lay : Layer} (tree leaf i : Nat)
    (h : ∀ p, T (.inr (.inl (WCT9.lowerSeedHeader lay tree p))) = T' (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i := by
  rw [S.seed, S.seed]
  congr 2
  funext j
  rw [eval_lowerSeedPair, eval_lowerSeedPair, h]

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable (S : FamScheme) {F : FamAddr}

section Fill
variable (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
  (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hU hF haF hd1

theorem fill_pubF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (input : HashInput)
    (h : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), c ≠ ca → ∀ v,
      input ≠ chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inl (.inr input)) =
      match PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
      | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) e
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (raw R (.inl (.inr input))))
      | none => raw R (.inl (.inr input)) := by
  have hdX := restDepth_ovF S hF R X a
  unfold fillTable RawPrefix.fill
  rw [raw_ov_const hU a (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega), hdX]
  cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
  | some p =>
    simp only
    have hin := PrefixGame.rowOf_some hp
    obtain ⟨⟨step, hs⟩, v⟩ := p
    simp only at hin ⊢
    subst hin
    congr 1
    by_cases hz : step = 0
    · subst hz
      have hrow : chainRowW a 0 v = chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F ca) 0 v := by rw [haF]
      have h0 : WCT9.chainHigh a.key.lay a.chain 0 = zhF (S.grp F.lay) (chainCount F.lay) F ca := by subst haF; rfl
      rw [h0, hrow, raw_ovF_zero hU hF]
      exact halfOf_not_joinHalf _ _ _
    · congr 1
      rw [raw_ovF_pub]
      cases hzo : zeroOfF (S.grp F.lay) (chainCount F.lay) F (chainRowW a step v) with
      | none => rfl
      | some q =>
          have he := zeroOfF_some hzo
          have hw := hF.width
          have hc1 := q.1.2.isLt
          obtain ⟨-, -, hs', -⟩ := chainInputW_eq_chainRowW (a := chainOfF (S.grp F.lay) (chainCount F.lay) F q.1)
            (by subst haF; unfold chainOfF; simp only; have := ca.2.isLt; omega)
            (by unfold chainOfF; simp only; omega)
            (by have := RawPrefix.restDepth_le a R; omega) (by omega) he
          exact absurd hs' hz
  | none =>
    simp only
    have hc := (PrefixGame.rowOf_none_iff a input).mp hp
    apply raw_ovF_pub
    cases hzo : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
    | none => rfl
    | some q =>
        have he := zeroOfF_some hzo
        by_cases hqa : q.1 = ca
        · exfalso
          apply hc
          refine ⟨0, q.2, hd1, ?_⟩
          rw [he, hqa, haF]
        · exact absurd he (h q.1 hqa q.2)

theorem fill_privF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (coord : Coordinate) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e (.inr coord) =
      raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) (.inr coord) := by
  unfold fillTable RawPrefix.fill
  exact RawPrefix.raw_ov_private a _ _ _

theorem fill_zeroF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest)
    (c : GChainW (S.grp F.lay) (chainCount F.lay)) (hca : c ≠ ca) (v : Digest) :
    fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e
        (.inl (.inr (chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v))) =
      joinHalf (zhF (S.grp F.lay) (chainCount F.lay) F c) (X.2 c v)
        (WCT9.halfOf (!zhF (S.grp F.lay) (chainCount F.lay) F c)
          (raw R (.inl (.inr (chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v))))) := by
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.raw_ov_nonprefix, raw_ovF_zero hU hF]
  rw [PrefixGame.rowOf_none_iff]
  rintro ⟨step, value, hs, he⟩
  have hw := hF.width
  have hc1 := c.2.isLt
  obtain ⟨hal, hc, -, -⟩ := chainInputW_eq_chainRowW (a := a)
    (by unfold chainOfF; simp only; omega) (by subst haF; unfold chainOfF; simp only; have := ca.2.isLt; omega)
    (by omega) (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega) he
  apply hca
  subst haF
  have hL := hal.eq_of_lt hF.tree (lt_trans (famLeaf_lt hF c.1) (by norm_num)) hF.tree
    (lt_trans (famLeaf_lt hF ca.1) (by norm_num))
  have hleaf := congrArg LeafAddr.leaf hL
  unfold chainOfF famLeaf at hleaf hc
  simp only at hleaf hc
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext hc)

theorem famAgree_fill (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) :
    FamAgree S F (raw R) (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e) := by
  have hA := famAgree_ovF S hF R X
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (k | input) | coord
    · rfl
    · rw [fill_pubF hU S hF ca haF R hd1 X e input (fun c _ v he => hq c.1 c.2 0 v c.2.isLt (by omega) he)]
      cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
      | none => rfl
      | some p =>
          exfalso
          have hin := PrefixGame.rowOf_some hp
          apply hq ca.1 ca.2 p.1 p.2 ca.2.isLt (by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega)
          rw [hin]; exact congrArg (fun b => chainRowW b p.1.val p.2) haF
    · rw [fill_privF hU S hF ca haF R hd1]
      exact hA.out _ hq
  · rw [eval_lowerSeedPair, eval_lowerSeedPair] at *
    have := hA.half o ho hno
    rw [eval_lowerSeedPair, eval_lowerSeedPair] at this
    rw [fill_privF hU S hF ca haF R hd1]
    exact this

theorem depth_fillF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) (b : ChainAddr) :
    CanonicalRef.depth (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e) zeroMessages b =
      CanonicalRef.depth (raw R) zeroMessages b := by
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.depth_ov _ (by have := RawPrefix.restDepth_le a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X); omega),
    depth_ovF S hF]

theorem wotsSeed_fillF (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (e : Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f)) e) F.lay F.tree
        (S.grp F.lay * F.fam + l) c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (l.val * S.stride F.lay + c + 1) := by
  rw [← wotsSeed_ovF S hF R K f l c hc]
  apply wotsSeed_congr_cellsS S
  intro p
  exact fill_privF hU S hF ca haF R hd1 (K, f) e _

theorem fill_frontier_selfF (X : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (e : Digest) :
    CanonicalRef.frontierValue (fillTable a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e)
      zeroMessages a = e := by
  have hdX := restDepth_ovF S hF R X a
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.frontierValue_ov hU]
  obtain ⟨d', hd'⟩ : ∃ d', RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) = d' + 1 :=
    ⟨RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) - 1, by omega⟩
  generalize RawPrefix.ovSeed a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R X) e = s0
  revert s0
  rw [hd']
  intro s0
  exact PrefixGame.evaluate_const_succ d' e s0
end Fill

#print axioms fill_pubF
#print axioms famAgree_fill
#print axioms wotsSeed_fillF
#print axioms fill_frontier_selfF
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
