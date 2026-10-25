import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamCongr

/-! # Family restart, step P2b: the family override against a `FamScheme` (r3-lean-seedfam)

Family analogues of `Normalized.RawLeaf.{raw_ovL_zero, raw_ovL_pub, raw_ovL_tweak, famCoef_ovL, wotsSeed_ovL,
leafAgree_ovL, search_ovL, referenceSearch_ovL, depth_ovL, restDepth_ovL}`: for a family `F` of a scheme `S`
(`g = S.grp F.lay` leaves of `chainCount F.lay` chains, `n = S.cnt F.lay` coefficients), the override
`ovF g w b n F R (K, f)` makes the family read `K` (seeds `familyEval K` at `l·w + c + 1`), agrees with `R` outside the
family (`famAgree_ovF`), and leaves every reference depth unchanged.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW gptW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)
variable {g w b n : Nat} {F : FamAddr}

include hU in
theorem raw_ovF_zero (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) (c : GChainW g w) (v : Digest) :
    raw (ovF g w b n F R y) (.inl (.inr (chainRowW (chainOfF g w F c) 0 v))) =
      joinHalf (zhF g w F c) (y.2 c v) (WCT9.halfOf (!zhF g w F c) (raw R (.inl (.inr (chainRowW (chainOfF g w F c) 0 v))))) := by
  rw [RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _),
    RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _)]
  exact ovPubF_zero hU hF R.2 y.2 c v

theorem raw_ovF_pub (R : Tables U) (y : FamData g w n) (input : HashInput) (h : zeroOfF g w F input = none) :
    raw (ovF g w b n F R y) (.inl (.inr input)) = raw R (.inl (.inr input)) := by
  by_cases hm : input ∈ U
  · rw [RawPrefix.raw_mem _ _ hm, RawPrefix.raw_mem _ _ hm]
    show ovPubF g w F R.2 y.2 ⟨input, hm⟩ = R.2 ⟨input, hm⟩
    unfold ovPubF
    simp only [h]
  · rw [RawPrefix.raw_nonmem _ _ hm, RawPrefix.raw_nonmem _ _ hm]

theorem slotAtF_none {tw : BitVec 128} {bit : Nat} (h : ∀ j : Fin n, cellHdrF b F j = tw → ordF b F j % 2 ≠ bit) :
    slotAtF b n F tw bit = none := by
  unfold slotAtF
  rw [dif_neg]
  rintro ⟨j, h1, h2⟩
  exact h j h1 h2

theorem raw_ovF_tweak (R : Tables U) (y : FamData g w n) (tw : BitVec 128) (h : ∀ j : Fin n, cellHdrF b F j ≠ tw) :
    raw (ovF g w b n F R y) (.inr (.inl tw)) = raw R (.inr (.inl tw)) := by
  rw [RawPrefix.raw_private, RawPrefix.raw_private]
  show ovPrivF b n F R.1 y.1 (.inl tw) = R.1 (.inl tw)
  rw [ovPrivF_inl, slotAtF_none (fun j hj => absurd hj (h j)), slotAtF_none (fun j hj => absurd hj (h j))]
  exact ChainGraph.joinOutput_parts _

/-- The family coefficient `j` read through the scheme's packed half after the override is `K j`. -/
theorem famCoef_ovF (hF : FamOk g w b n F) (R : Tables U) (K : Fin n → Digest) (f : GChainW g w → Digest → Digest)
    (j : Fin n) :
    WCT9.seedHalf (evalWithAnswerFn (raw (ovF g w b n F R (K, f))) (WCT9.lowerSeedPair F.lay F.tree (ordF b F j / 2)))
      (ordF b F j) = K j := by
  rw [eval_lowerSeedPair]
  have hc := ovPrivF_cell hF R.1 K j
  rw [show ovPrivF b n F R.1 K (.inl (cellHdrF b F j)) = raw (ovF g w b n F R (K, f)) (.inr (.inl (cellHdrF b F j))) from rfl]
    at hc
  unfold halfOf at hc
  unfold WCT9.seedHalf
  unfold cellHdrF at hc
  split_ifs with h1 h2 h2
  · rw [if_pos h1] at hc; exact hc
  · rw [if_neg h1] at hc; exact hc

/-- A family cell with the header of pair index `o / 2` has ordinal pair `o / 2`. -/
theorem cellHdrF_eq_hdr (hF : FamOk g w b n F) (j' : Fin n) {o : Nat} (ho : o / 2 < 2 ^ 32)
    (h : cellHdrF b F j' = WCT9.lowerSeedHeader F.lay F.tree (o / 2)) : ordF b F j' / 2 = o / 2 := by
  unfold cellHdrF WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordF_pair_lt hF j'), Nat.mod_eq_of_lt ho] at this

variable (S : FamScheme)

/-- Admissible family of a scheme. -/
abbrev FamOkS (F : FamAddr) : Prop := FamOk (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F

/-- **Seed readout after the override**: leaf `l` of `F`, chain `c`, reads `familyEval K` at `l·w + c + 1`. -/
theorem wotsSeed_ovF (hF : FamOkS S F) (R : Tables U) (K : Fin (S.size F.lay F.fam) → Digest)
    (f : GChainW (S.grp F.lay) (chainCount F.lay) → Digest → Digest) (l : Fin (S.grp F.lay)) (c : Nat)
    (hc : c < chainCount F.lay) :
    WCT9.wotsSeed (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R (K, f))) F.lay F.tree
        (S.grp F.lay * F.fam + l) c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (l.val * S.stride F.lay + c + 1) := by
  rw [S.seed]
  have hg := S.grp_pos F.lay
  have hdiv : (S.grp F.lay * F.fam + l) / S.grp F.lay = F.fam := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt l.isLt, Nat.zero_add]
  have hmod : (S.grp F.lay * F.fam + l) % S.grp F.lay = l := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l.isLt]
  rw [S.point_eq _ _ _ hc, hdiv, hmod]
  congr 2
  funext j
  exact famCoef_ovF hF R K f j

/-- The family override changes nothing outside `F`'s own halves and step-0 rows. -/
theorem famAgree_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) :
    FamAgree S F (raw R) (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) := by
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (k | input) | (tw | x)
    · rfl
    · apply raw_ovF_pub
      cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
      | none => rfl
      | some p => exact absurd (zeroOfF_some hz) (hq p.1.1 p.1.2 0 p.2 p.1.2.isLt (by omega))
    · exact raw_ovF_tweak R y tw (fun j he => hq j (lt_of_lt_of_le j.isLt (S.size_le _ _)) he.symm)
    · rfl
  · obtain ⟨j, hj, hoj⟩ := ho
    rw [eval_lowerSeedPair, eval_lowerSeedPair]
    have ho2 : o / 2 < 2 ^ 32 := by
      rw [hoj]; have := hF.pair; unfold ordS; omega
    have hnone : slotAtF (S.cnt F.lay) (S.size F.lay F.fam) F (WCT9.lowerSeedHeader F.lay F.tree (o / 2)) (o % 2) = none := by
      apply slotAtF_none
      intro j' h1 h2
      have e1 := cellHdrF_eq_hdr hF j' ho2 h1
      apply hno j' (lt_of_lt_of_le j'.isLt (S.size_le _ _))
      unfold ordF at e1 h2
      unfold ordS at hoj ⊢
      omega
    rw [RawPrefix.raw_private, RawPrefix.raw_private]
    show WCT9.seedHalf ((ovPrivF (S.cnt F.lay) (S.size F.lay F.fam) F R.1 y.1 (.inl (WCT9.lowerSeedHeader F.lay F.tree (o / 2)))).extractLsb' 0 128,
      (ovPrivF (S.cnt F.lay) (S.size F.lay F.fam) F R.1 y.1 (.inl (WCT9.lowerSeedHeader F.lay F.tree (o / 2)))).extractLsb' 128 128) o = _
    rw [ovPrivF_inl]
    unfold WCT9.seedHalf
    split_ifs with h0
    · rw [h0] at hnone
      rw [hnone, ChainGraph.joinOutput_low]
      rfl
    · rw [show o % 2 = 1 by omega] at hnone
      rw [hnone, ChainGraph.joinOutput_high]
      rfl

theorem search_ovF (hF : FamOkS S F) (R : Tables U) (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))
    (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages K remaining =
      CanonicalRef.searchOf (raw R) zeroMessages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_outF (famAgree_ovF S hF R y)
    (respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F)

theorem referenceSearch_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (K : LeafAddr) :
    CanonicalRef.referenceSearch (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages K =
      CanonicalRef.referenceSearch (raw R) zeroMessages K :=
  CanonicalRef.referenceSearch_congr (fun K remaining _ => search_ovF S hF R y K remaining) K

theorem depth_ovF (hF : FamOkS S F) (R : Tables U) (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam))
    (a : ChainAddr) :
    CanonicalRef.depth (raw (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y)) zeroMessages a =
      CanonicalRef.depth (raw R) zeroMessages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_ovF S hF]

theorem restDepth_ovF (hF : FamOkS S F) (R : Tables U)
    (y : FamData (S.grp F.lay) (chainCount F.lay) (S.size F.lay F.fam)) (a : ChainAddr) :
    RawPrefix.restDepth a (ovF (S.grp F.lay) (chainCount F.lay) (S.cnt F.lay) (S.size F.lay F.fam) F R y) = RawPrefix.restDepth a R := by
  rw [RawPrefix.restDepth_eq, RawPrefix.restDepth_eq, depth_ovF S hF]

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
