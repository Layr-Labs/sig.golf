import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamTest
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafSum

/-! # Family restart, step P5a: family test counts and their allocation (r3-lean-seedfam)

Family analogues of `Normalized.Core.{StepZeroUnrev, NL, isTestQ_iff, NL_mkSample, sum_NL_le}` (WotsLeafSum):
a test query of family `F` is a step-0 row of one of its unrevealed chains (phantom chains of a short last family are
always unrevealed); every trace entry is a test query of at most one family, and is charged to the source chains of
that family only, at most `grp · chainCount` of them (`sum_NL_leF`: today `54`, v6 `max(4·54, 7·43) = 301`).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized (depth_eq)
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
open SphincsSecurity.QueryCap (recorded counted calls)
open SigGolfCandidate.T3.Security.Wots.Mask (chainCount_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable (S : FamScheme)

/-- The family of a leaf. -/
def famOf (L : LeafAddr) : FamAddr := ⟨L.lay, L.tree, L.leaf / S.grp L.lay⟩

/-- Member `l` of `F` is a real (in-tree) leaf. -/
def RealM (F : FamAddr) (l : Nat) : Prop := S.grp F.lay * F.fam + l < 2 ^ height F.lay

/-- `input` is the step-0 row of an unrevealed chain of family `F` in `T` (phantom chains count as unrevealed). -/
def StepZeroUnrevF (F : FamAddr) (T : Answers) (input : HashInput) : Prop :=
  ∃ c : GChainW (S.grp F.lay) (chainCount F.lay),
    (¬RealM S F c.1.val ∨ CanonicalRef.depth T (sourceMessages T) (chainOfF (S.grp F.lay) (chainCount F.lay) F c) ≠ 0) ∧
      ∃ v, input = chainRowW (chainOfF (S.grp F.lay) (chainCount F.lay) F c) 0 v

/-- Number of test queries of family `F` in a reference sample. -/
noncomputable def NLF (F : FamAddr) (s : RefSample) : ℕ :=
  (s.trace.filter fun e => decide (StepZeroUnrevF S F s.answers e.1)).length

/-- Test count charged to chain `a`: its family's. -/
noncomputable def NLaF (a : ChainAddr) (s : RefSample) : ℕ := NLF S (famOf S a.key) s

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

theorem zeroOfF_none_ne {g w b n : Nat} {F : FamAddr} (hF : FamOk g w b n F) {input : HashInput}
    (h : zeroOfF g w F input = none) (c : GChainW g w) (v : Digest) : input ≠ chainRowW (chainOfF g w F c) 0 v := by
  rintro rfl
  rw [zeroOfF_chainRow hF] at h
  cases h

theorem isTestQF_iff {F : FamAddr} (hF : FamOkS S F) {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (R : Tables U) (T : Answers)
    (hT : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), RealM S F c.1.val →
      CanonicalRef.depth T (sourceMessages T) (chainOfF (S.grp F.lay) (chainCount F.lay) F c) =
        CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c))
    (hreal : RealM S F ca.1.val) (query : RefWorld.Domain) :
    isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (revSetF S F R) query ↔
      ∃ x, query = .inl (.inr x) ∧ StepZeroUnrevF S F T x := by
  have hda : CanonicalRef.depth (raw R) zeroMessages a = RawPrefix.restDepth a R := (RawPrefix.restDepth_eq a R).symm
  have hw := hF.width
  rcases query with (k | input) | u
  · simp [isTestQF]
  · simp only [isTestQF, Sum.inl.injEq, Sum.inr.injEq, exists_eq_left']
    unfold StepZeroUnrevF
    cases hp : PrefixGame.rowOf a (RawPrefix.restDepth a R) input with
    | some p =>
        have hin := PrefixGame.rowOf_some hp
        simp only
        constructor
        · intro h0
          refine ⟨ca, Or.inr ?_, p.2, ?_⟩
          · rw [hT ca hreal, ← haF, hda]
            have := p.1.isLt
            omega
          · rw [hin, ← haF, show p.1.val = 0 from h0]
        · rintro ⟨c, -, v, he⟩
          rw [hin] at he
          have h1 : (p.1 : ℕ) < 256 := by have := p.1.isLt; have := RawPrefix.restDepth_le a R; omega
          have hc1 := c.2.isLt
          have hca1 := ca.2.isLt
          obtain ⟨-, -, hs, -⟩ := chainInputW_eq_chainRowW (a := chainOfF (S.grp F.lay) (chainCount F.lay) F c)
            (by subst haF; unfold chainOfF; simp only; omega) (by unfold chainOfF; simp only; omega) h1 (by omega) he
          exact hs
    | none =>
        simp only
        cases hz : zeroOfF (S.grp F.lay) (chainCount F.lay) F input with
        | none =>
            simp only [false_iff, not_exists, not_and]
            intro c _ v he
            exact zeroOfF_none_ne hF hz c v he
        | some cv =>
            simp only
            have he := zeroOfF_some hz
            constructor
            · intro hc
              refine ⟨cv.1, ?_, cv.2, he⟩
              by_cases hr : RealM S F cv.1.1.val
              · right
                rw [hT cv.1 hr]
                intro h0
                apply hc
                unfold revSetF
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hr, h0⟩
              · exact Or.inl hr
            · rintro ⟨c, hc, v, he'⟩
              rw [he] at he'
              obtain ⟨h1, -⟩ := chainRowF_zero_inj hF he'
              subst h1
              unfold revSetF
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
              intro hr h0
              rcases hc with hc | hc
              · exact hc hr
              · exact hc (by rw [hT cv.1 hr]; exact h0)
  · simp [isTestQF]

include hU in
theorem NL_mkSampleF {F : FamAddr} (hF : FamOkS S F) (htb : F.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits F.lay)
    {a : ChainAddr} (ca : GChainW (S.grp F.lay) (chainCount F.lay))
    (haF : a = chainOfF (S.grp F.lay) (chainCount F.lay) F ca) (hreal : RealM S F ca.1.val)
    (R : Tables U) (x : Hidden (RawPrefix.restDepth a R)) (run : SeedResult) :
    NLF S F (mkSample (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)) run) =
      calls (isTestQF (S.grp F.lay) (chainCount F.lay) F a (RawPrefix.restDepth a R) (revSetF S F R)) run.2 := by
  unfold NLF mkSample
  simp only
  rw [traceOf_filter_length]
  have hT : ∀ c : GChainW (S.grp F.lay) (chainCount F.lay), RealM S F c.1.val →
      CanonicalRef.depth (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x))
        (sourceMessages (answers hU (RawPrefix.ov a (RawPrefix.restDepth a R) R x)))
          (chainOfF (S.grp F.lay) (chainCount F.lay) F c) =
      CanonicalRef.depth (raw R) zeroMessages (chainOfF (S.grp F.lay) (chainCount F.lay) F c) := by
    intro c hc
    rw [depth_eq hU _ _ (sourceLeaf_memF S htb c.1 hc), RawPrefix.depth_ov a (by have := RawPrefix.restDepth_le a R; omega)]
  congr 1
  funext query
  exact propext (isTestQF_iff S hF ca haF R _ hT hreal query).symm

/-- Step-0 rows determine their family (families of source leaves; trees below `2^40`, leaves below `2^32`). -/
theorem stepZero_fam_unique (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) {L L' : LeafAddr}
    (hL : WotsExtract.SourceLeaf L) (hL' : WotsExtract.SourceLeaf L') {T T' : Answers} {input : HashInput}
    (h : StepZeroUnrevF S (famOf S L) T input) (h' : StepZeroUnrevF S (famOf S L') T' input) :
    famOf S L = famOf S L' := by
  obtain ⟨c, -, v, rfl⟩ := h
  obtain ⟨c', -, v', he⟩ := h'
  have hb : ∀ K : LeafAddr, WotsExtract.SourceLeaf K → K.tree < 2 ^ 40 ∧ K.leaf < 2 ^ 12 := fun K hK => by
    refine ⟨by have := hK.1; omega, ?_⟩
    have h1 := hK.2
    have h2 : 2 ^ height K.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3.Security.Wots.height_le K.lay)
    omega
  have hmem : ∀ (K : LeafAddr) (l : Fin (S.grp K.lay)), WotsExtract.SourceLeaf K →
      S.grp K.lay * (K.leaf / S.grp K.lay) + l.val < 2 ^ 32 := by
    intro K l hK
    have := (hb K hK).2; have := l.isLt; have := hgrp K.lay
    have : S.grp K.lay * (K.leaf / S.grp K.lay) ≤ K.leaf := Nat.mul_div_le _ _
    omega
  have hc1 := c.2.isLt; have hc2 := c'.2.isLt
  have hw1 := chainCount_le (famOf S L).lay; have hw2 := chainCount_le (famOf S L').lay
  obtain ⟨hal, -, -, -⟩ := chainInputW_eq_chainRowW (a := chainOfF _ _ (famOf S L') c')
    (by unfold chainOfF; simp only [Nat.reducePow]; omega) (by unfold chainOfF; simp only [Nat.reducePow]; omega)
    (by omega) (by omega) he
  have hE := hal.eq_of_lt (show L.tree < 2 ^ 40 from (hb L hL).1)
    (show S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val < 2 ^ 32 from hmem L c.1 hL)
    (show L'.tree < 2 ^ 40 from (hb L' hL').1)
    (show S.grp L'.lay * (L'.leaf / S.grp L'.lay) + c'.1.val < 2 ^ 32 from hmem L' c'.1 hL')
  have hlay : L.lay = L'.lay := by have h0 := congrArg LeafAddr.lay hE; exact h0
  have htree : L.tree = L'.tree := by have h0 := congrArg LeafAddr.tree hE; exact h0
  have hleaf : S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val =
      S.grp L'.lay * (L'.leaf / S.grp L'.lay) + c'.1.val := by have h0 := congrArg LeafAddr.leaf hE; exact h0
  rw [← hlay] at hleaf
  have hg := S.grp_pos L.lay
  have hc : c.1.val < S.grp L.lay := c.1.isLt
  have hc' : c'.1.val < S.grp L.lay := by
    have h := c'.1.isLt
    have hgg : S.grp (famOf S L').lay = S.grp L.lay := by show S.grp L'.lay = S.grp L.lay; rw [hlay]
    omega
  have e1 : (S.grp L.lay * (L.leaf / S.grp L.lay) + c.1.val) / S.grp L.lay = L.leaf / S.grp L.lay := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e2 : (S.grp L.lay * (L'.leaf / S.grp L.lay) + c'.1.val) / S.grp L.lay = L'.leaf / S.grp L.lay := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hc', Nat.zero_add]
  have hfam : L.leaf / S.grp L.lay = L'.leaf / S.grp L'.lay := by
    rw [← hlay, ← e1, ← e2, hleaf]
  unfold famOf
  rw [hfam, hlay, htree]

/-- Source chains of one family: at most `grp · chainCount`. -/
theorem card_famChains_le (F : FamAddr) :
    (SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => famOf S a.key = F).card ≤
      S.grp F.lay * chainCount F.lay := by
  classical
  have hinj : ∀ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains.filter (fun a => famOf S a.key = F),
      ∀ a' ∈ SigGolfCandidate.T3.Security.Wots.sourceChains.filter (fun a => famOf S a.key = F),
      ((a.key.leaf % S.grp F.lay, a.chain) : Nat × Nat) = (a'.key.leaf % S.grp F.lay, a'.chain) → a = a' := by
    intro a ha a' ha' he
    simp only [Finset.mem_filter] at ha ha'
    have h1 := congrArg FamAddr.lay ha.2; have h2 := congrArg FamAddr.tree ha.2; have h3 := congrArg FamAddr.fam ha.2
    have h1' := congrArg FamAddr.lay ha'.2; have h2' := congrArg FamAddr.tree ha'.2
    have h3' := congrArg FamAddr.fam ha'.2
    unfold famOf at h1 h2 h3 h1' h2' h3'
    simp only at h1 h2 h3 h1' h2' h3'
    simp only [Prod.mk.injEq] at he
    have e1 : a.key.leaf = S.grp F.lay * F.fam + a.key.leaf % S.grp F.lay := by
      rw [← h1, ← h3]; exact (Nat.div_add_mod _ _).symm
    have e2 : a'.key.leaf = S.grp F.lay * F.fam + a'.key.leaf % S.grp F.lay := by
      rw [← h1', ← h3']; exact (Nat.div_add_mod _ _).symm
    have hl : a.key.leaf = a'.key.leaf := by rw [e1, e2, he.1]
    have hk : a.key = a'.key := by
      cases ha0 : a.key; cases ha0' : a'.key
      rw [ha0] at h1 h2 hl; rw [ha0'] at h1' h2' hl
      simp only at h1 h2 hl h1' h2'
      rw [h1, ← h1', h2, ← h2', hl]
    cases a; cases a'
    simp only at hk he
    rw [hk, he.2]
  calc (SigGolfCandidate.T3.Security.Wots.sourceChains.filter fun a => famOf S a.key = F).card
      ≤ ((Finset.range (S.grp F.lay)) ×ˢ (Finset.range (chainCount F.lay))).card := by
        apply Finset.card_le_card_of_injOn (fun a => (a.key.leaf % S.grp F.lay, a.chain))
        · intro a ha
          simp only [Finset.mem_filter, Finset.coe_filter, Set.mem_setOf_eq] at ha
          have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp ha.1
          have h1 := congrArg FamAddr.lay ha.2
          unfold famOf at h1; simp only at h1
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          exact ⟨Nat.mod_lt _ (S.grp_pos _), h1 ▸ hs.2⟩
        · intro a ha a' ha' he
          exact hinj a (by simpa using ha) a' (by simpa using ha') he
    _ = S.grp F.lay * chainCount F.lay := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- **Per-sample allocation:** every trace entry is a test of at most one family, charged to at most `Cmax` source
chains (`Cmax ≥ grp · chainCount` on every layer). -/
theorem sum_NL_leF (hgrp : ∀ lay, S.grp lay ≤ 2 ^ 20) (Cmax : Nat) (hC : ∀ lay, S.grp lay * chainCount lay ≤ Cmax)
    (s : RefSample) :
    ∑ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLaF S a s ≤ Cmax * s.trace.length := by
  classical
  let test : FamAddr → Entry → Prop := fun F e =>
    StepZeroUnrevF S F s.answers e.1 ∧ ∃ L, WotsExtract.SourceLeaf L ∧ famOf S L = F
  have hcongr : ∀ a ∈ SigGolfCandidate.T3.Security.Wots.sourceChains, NLaF S a s =
      (s.trace.filter fun e => decide (test (famOf S a.key) e)).length := by
    intro a ha
    have hs := (SigGolfCandidate.T3.Security.Wots.mem_sourceChains a).mp ha
    unfold NLaF NLF
    congr 1
    apply List.filter_congr
    intro e _
    simp only [test, decide_eq_decide]
    exact ⟨fun h => ⟨h, a.key, hs.1, rfl⟩, fun h => h.1⟩
  rw [Finset.sum_congr rfl hcongr]
  exact ClaudeWCT.Arith.SideChannel.GroupedFamily.sum_charge_le SigGolfCandidate.T3.Security.Wots.sourceChains
    (fun a => famOf S a.key) test Cmax
    (fun e F F' h h' => by
      obtain ⟨h1, L, hL, rfl⟩ := h
      obtain ⟨h1', L', hL', rfl⟩ := h'
      exact stepZero_fam_unique S hgrp hL hL' h1 h1')
    (fun F => (card_famChains_le S F).trans (hC F.lay)) s.trace

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamSum
