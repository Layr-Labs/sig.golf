import SigGolfCandidate.ClaudeWCT.W9.New.BC.Respects
import SigGolfCandidate.ClaudeWCT.W9.New.Positions.FtsBridge

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem eval_chain_one_maskAt {s : Nat} (hs : s < depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain s 1 v) =
      if s + 1 = depth answers a then frontierValue answers a else 0 := by
  rw [eval_chain_one, ← chainRow_eq, maskAt_prefix answers a v hs]
  split
  · exact ChainGraph.joinOutput_low _ _
  · rfl
theorem eval_chain_prefix_maskAt (hd : 1 ≤ depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain 0 (depth answers a) v) =
      frontierValue answers a := by
  have h1 := Correctness.eval_chain_add (maskAt answers a) a.key.lay a.key.tree a.key.leaf a.chain 0
    (depth answers a - 1) 1 v
  rw [Nat.zero_add, eval_chain_one_maskAt answers a (by omega), if_pos (Nat.sub_add_cancel hd),
    Nat.sub_add_cancel hd] at h1
  exact h1
theorem eval_chain_maskAt (hd : 1 ≤ depth answers a) {count : Nat} (hc : depth answers a ≤ count)
    (hc' : count ≤ 256) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count v) =
      evalWithAnswerFn answers (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count
        (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = depth answers a + e := ⟨count - depth answers a, by omega⟩
  rw [Correctness.eval_chain_add, Correctness.eval_chain_add answers, Nat.zero_add,
    eval_chain_prefix_maskAt answers a hd]
  change _ = evalWithAnswerFn answers (chain a.key.lay a.key.tree a.key.leaf a.chain (depth answers a) e
    (frontierValue answers a))
  refine Respects.eval_eq (S := fun q => maskAt answers a q = answers q) ?_ (fun q hq => hq)
  unfold chain
  refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
  rw [pad64_chainInput, ← chainRow_eq]
  obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hstep
  exact maskAt_row_ge answers a value hlo (by omega)
def wotsTweak (lay : Layer) (tree leaf i : Nat) : BitVec 128 :=
  if lay = 0 then header 0 lay.val tree (i / 2) leaf else WCT9.lowerSeedHeader lay tree (WCT9.lowerOrdinal lay leaf i / 2)
def wotsPar (lay : Layer) (leaf i : Nat) : Nat := if lay = 0 then i % 2 else WCT9.lowerOrdinal lay leaf i % 2
theorem wotsPar_lt (lay : Layer) (leaf i : Nat) : wotsPar lay leaf i < 2 := by
  unfold wotsPar; split_ifs <;> omega
/-- A top seed is a half-cell (lower seeds are family evaluations, `lowerSeed_eq_cells`). -/
theorem wotsSeed_eq (T : Answers) {lay : Layer} (h : lay = 0) (tree leaf i : Nat) :
    WCT9.wotsSeed T lay tree leaf i =
      if wotsPar lay leaf i = 0 then (T (.inr (.inl (wotsTweak lay tree leaf i)))).extractLsb' 0 128
      else (T (.inr (.inl (wotsTweak lay tree leaf i)))).extractLsb' 128 128 := by
  subst h
  rfl
/-- A lower seed only reads the coefficient cells `lowerSeedHeader lay tree p` of its tree. -/
theorem lowerSeed_congr_cells {T T' : Answers} {lay : Layer} (tree leaf i : Nat)
    (h : ∀ p, T (.inr (.inl (WCT9.lowerSeedHeader lay tree p))) = T' (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))) :
    WCT9.lowerSeed T lay tree leaf i = WCT9.lowerSeed T' lay tree leaf i := by
  unfold WCT9.lowerSeed
  congr 2
  funext j
  unfold WCT9.lowerCoef WCT9.lowerCoefN WCT9.lowerSeedPair privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change WCT9.seedHalf ((T (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 0 128,
      (T (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 128 128) _ =
    WCT9.seedHalf ((T' (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 0 128,
      (T' (.inr (.inl (header 0 lay.val tree _ 0)))).extractLsb' 128 128) _
  rw [show header 0 lay.val tree (WCT9.lowerCoefOrdinal leaf j.val / 2) 0 =
    WCT9.lowerSeedHeader lay tree (WCT9.lowerCoefOrdinal leaf j.val / 2) from rfl, h]
theorem wotsTweak_self (a : ChainAddr) : wotsTweak a.key.lay a.key.tree a.key.leaf a.chain = seedTweakP a := by
  unfold wotsTweak seedTweakP seedTweak seedSlot
  split_ifs <;> rfl
theorem wotsPar_self (a : ChainAddr) : wotsPar a.key.lay a.key.leaf a.chain = seedSlot a % 2 := by
  unfold wotsPar seedSlot
  split_ifs <;> rfl
theorem wotsTweak_congr {lay : Layer} {tree tree' : Nat} (ht : tree % 2 ^ 40 = tree' % 2 ^ 40) (leaf i : Nat) :
    wotsTweak lay tree leaf i = wotsTweak lay tree' leaf i := by
  unfold wotsTweak WCT9.lowerSeedHeader
  split_ifs
  · exact header_congr rfl ht rfl
  · exact header_congr rfl ht rfl
theorem lowerPair_lt (lay : Layer) {leaf i : Nat} (hl : leaf < 2 ^ 24) (hi : i < chainCount lay) :
    WCT9.lowerOrdinal lay leaf i / 2 < 2 ^ 32 := by
  have := chainCount_le lay
  unfold WCT9.lowerOrdinal
  have : chainCount lay * leaf ≤ 58 * (2 ^ 24) := Nat.mul_le_mul (by omega) hl.le
  omega
def SlotOK (a : ChainAddr) (lay : Layer) (leaf : Nat) : Prop :=
  lay = 0 ∨ a.key.lay = 0 ∨ (leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24)
def MaskOK (a : ChainAddr) : Prop := a.key.lay = 0 ∨ a.key.leaf < 2 ^ 24
theorem slotOK_of {a : ChainAddr} {lay : Layer} {leaf : Nat} (h : lay = 0 ∨ MaskOK a) (hl : leaf < 2 ^ 24) :
    SlotOK a lay leaf := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hl, h⟩)
theorem maskOK_of_lt {a : ChainAddr} (h : a.key.leaf < 2 ^ 24) : MaskOK a := Or.inr h
theorem ord_inj {l l' i i' : Nat} (hi : i < 43) (hi' : i' < 43) (h1 : (43 * l + i) / 2 = (43 * l' + i') / 2)
    (h2 : (43 * l + i) % 2 = (43 * l' + i') % 2) : l = l' ∧ i = i' := by
  have : 43 * l + i = 43 * l' + i' := by omega
  omega
theorem wotsTweak_alias {lay : Layer} {tree leaf i : Nat} (hi : i < chainCount lay) (hb : SlotOK a lay leaf)
    (hac : a.chain < chainCount a.key.lay)
    (h : wotsTweak lay tree leaf i = seedTweakP a) (hp : wotsPar lay leaf i = seedSlot a % 2) :
    LeafAlias lay tree leaf a.key ∧ i = a.chain := by
  have hi58 := chainCount_le lay
  have ha58 := chainCount_le a.key.lay
  unfold wotsTweak seedTweakP at h
  unfold wotsPar seedSlot at hp
  by_cases h0 : lay = 0 <;> by_cases h0' : a.key.lay = 0
  · rw [if_pos h0] at h hp
    rw [if_pos h0'] at h hp
    obtain ⟨hal', hpair⟩ := seedTweak_alias (by simp only [Nat.reducePow]; omega)
      (by simp only [Nat.reducePow]; omega) h
    exact ⟨hal', by omega⟩
  · exfalso
    rw [if_pos h0, if_neg h0'] at h
    unfold WCT9.lowerSeedHeader at h
    have := (header_fields h).2.1
    have e1 : lay.val = 0 := by rw [h0]; rfl
    have e2 : a.key.lay.val ≠ 0 := fun e => h0' (Fin.ext e)
    have := a.key.lay.isLt
    omega
  · exfalso
    rw [if_neg h0, if_pos h0'] at h
    unfold WCT9.lowerSeedHeader seedTweak at h
    have := (header_fields h).2.1
    have e1 : a.key.lay.val = 0 := by rw [h0']; rfl
    have e2 : lay.val ≠ 0 := fun e => h0 (Fin.ext e)
    have := lay.isLt
    omega
  · rw [if_neg h0, if_neg h0'] at h hp
    obtain ⟨hl, hal⟩ : leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24 := by
      rcases hb with hb | hb | hb
      · exact absurd hb h0
      · exact absurd hb h0'
      · exact hb
    unfold WCT9.lowerSeedHeader at h
    obtain ⟨-, hl', ht, hP, -⟩ := header_fields h
    have hlay : lay = a.key.lay := by
      apply Fin.ext
      have := lay.isLt; have := a.key.lay.isLt
      omega
    have hs : seedSlot a = WCT9.lowerOrdinal a.key.lay a.key.leaf a.chain := by
      unfold seedSlot; rw [if_neg h0']
    rw [hs] at hP
    have p1 := lowerPair_lt lay hl hi
    have p2 := lowerPair_lt a.key.lay hal hac
    rw [← hlay] at p2 hP hac hp
    rw [Nat.mod_eq_of_lt p1, Nat.mod_eq_of_lt p2] at hP
    have cl : chainCount lay = 43 := by revert h0; fin_cases lay <;> decide
    have e : leaf = a.key.leaf ∧ i = a.chain := by
      unfold WCT9.lowerOrdinal at hP hp
      rw [cl] at hP hp hi hac
      exact ord_inj hi hac hP hp
    exact ⟨⟨hlay, ht, by rw [e.1]⟩, e.2⟩
theorem wotsSeed_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < chainCount lay) (hb : SlotOK a lay leaf)
    (hna : ¬(LeafAlias lay tree leaf a.key ∧ i = a.chain)) :
    WCT9.wotsSeed (maskAt answers a) lay tree leaf i = WCT9.wotsSeed answers lay tree leaf i := by
  by_cases hd : depth answers a = 0
  · rw [maskAt_of_depth_zero answers a hd]
  have hac := chain_lt_of_depth answers a (by omega)
  by_cases hl : lay = 0
  · rw [wotsSeed_eq _ hl, wotsSeed_eq _ hl]
    by_cases heq : wotsTweak lay tree leaf i = seedTweakP a
    · have hpar : wotsPar lay leaf i ≠ seedSlot a % 2 := fun hp => hna (wotsTweak_alias a hi hb hac heq hp)
      have hp2 := wotsPar_lt lay leaf i
      have ha0 : a.key.lay = 0 := by
        by_contra ha0
        unfold wotsTweak seedTweakP WCT9.lowerSeedHeader seedTweak at heq
        rw [if_pos hl, if_neg ha0] at heq
        have := (header_fields heq).2.1
        have e1 : lay.val = 0 := by rw [hl]; rfl
        have e2 : a.key.lay.val ≠ 0 := fun e => ha0 (Fin.ext e)
        have := a.key.lay.isLt
        omega
      rw [maskAt_tweak, heq, if_pos (⟨rfl, by omega, ha0⟩ : seedTweakP a = seedTweakP a ∧ 1 ≤ depth answers a ∧
        a.key.lay = 0)]
      by_cases h0 : seedSlot a % 2 = 0
      · have hi1 : ¬wotsPar lay leaf i = 0 := by omega
        rw [if_neg hi1, if_neg hi1, if_pos h0, ChainGraph.joinOutput_high]
      · have hi0 : wotsPar lay leaf i = 0 := by omega
        rw [if_pos hi0, if_pos hi0, if_neg h0, ChainGraph.joinOutput_low]
    · rw [maskAt_untouched answers a (q := .inr (.inl _)) heq]
  · rw [WCT9.wotsSeed_lower _ hl, WCT9.wotsSeed_lower _ hl]
    apply lowerSeed_congr_cells
    intro p
    rw [maskAt_tweak, if_neg]
    rintro ⟨he, -, ha0⟩
    unfold seedTweakP seedTweak WCT9.lowerSeedHeader at he
    rw [if_pos ha0] at he
    have := (header_fields he).2.1
    have e1 : lay.val ≠ 0 := fun e => hl (Fin.ext e)
    have e2 : a.key.lay.val = 0 := by rw [ha0]; rfl
    have := lay.isLt
    omega
theorem wotsSeed_alias (T : Answers) {lay : Layer} {tree leaf : Nat} {L : LeafAddr}
    (h : LeafAlias lay tree leaf L) (hb : lay = 0 ∨ (leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24)) (i : Nat) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T L.lay L.tree L.leaf i := by
  rcases hb with h0 | ⟨hl, hL⟩
  · have h0' : L.lay = 0 := h.1 ▸ h0
    rw [show WCT9.wotsSeed T lay tree leaf i = leafSeed T lay tree leaf i by
        unfold WCT9.wotsSeed; rw [if_pos h0],
      show WCT9.wotsSeed T L.lay L.tree L.leaf i = leafSeed T L.lay L.tree L.leaf i by
        unfold WCT9.wotsSeed; rw [if_pos h0']]
    exact leafSeed_alias T h i
  have he : leaf = L.leaf := by
    have := h.2.2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  obtain ⟨hlay, ht, -⟩ := h
  subst he
  rw [← hlay]
  by_cases h0 : lay = 0
  · rw [wotsSeed_eq _ h0, wotsSeed_eq _ h0, wotsTweak_congr ht]
  · rw [WCT9.wotsSeed_lower _ h0, WCT9.wotsSeed_lower _ h0]
    have hc : ∀ p, WCT9.lowerSeedHeader lay tree p = WCT9.lowerSeedHeader lay L.tree p := fun p => by
      unfold WCT9.lowerSeedHeader
      exact header_congr rfl ht rfl
    have hcoef : WCT9.lowerCoef T lay tree L.leaf = WCT9.lowerCoef T lay L.tree L.leaf := by
      funext j
      unfold WCT9.lowerCoef WCT9.lowerCoefN WCT9.lowerSeedPair privatePair
      rw [show header 0 lay.val tree (WCT9.lowerCoefOrdinal L.leaf j.val / 2) 0 =
        header 0 lay.val L.tree (WCT9.lowerCoefOrdinal L.leaf j.val / 2) 0 from hc _]
    unfold WCT9.lowerSeed
    rw [hcoef]
end Mask
theorem chain_maskAt (answers : Answers) (a : ChainAddr) (count : Nat) (hcount : depth answers a ≤ count)
    (hsmall : count ≤ 256) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count
      (WCT9.wotsSeed (maskAt answers a) a.key.lay a.key.tree a.key.leaf a.chain)) =
    evalWithAnswerFn answers (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count
      (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  by_cases hd : depth answers a = 0
  · rw [Mask.maskAt_of_depth_zero answers a hd]
  · exact Mask.eval_chain_maskAt answers a (by omega) hcount hsmall _
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem eval_honestChain_maskAt (lay : Layer) (tree leaf i count : Nat) (hi : i < chainCount lay)
    (hc : count ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ count) :
    evalWithAnswerFn (maskAt answers a) (chain lay tree leaf i 0 count (WCT9.wotsSeed (maskAt answers a) lay tree leaf i)) =
      evalWithAnswerFn answers (chain lay tree leaf i 0 count (WCT9.wotsSeed answers lay tree leaf i)) := by
  by_cases hd : depth answers a = 0
  · rw [maskAt_of_depth_zero answers a hd]
  have hi' : i < 2 ^ 24 := by
    have := chainCount_le lay
    simp only [Nat.reducePow]; omega
  have hc' : a.chain < 2 ^ 24 := by
    have := chain_lt_of_depth answers a (by omega)
    have := chainCount_le a.key.lay
    simp only [Nat.reducePow]; omega
  by_cases hal' : LeafAlias lay tree leaf a.key ∧ i = a.chain
  · obtain ⟨hal', rfl⟩ := hal'
    have hb' : lay = 0 ∨ (leaf < 2 ^ 24 ∧ a.key.leaf < 2 ^ 24) := by
      rcases hb with hb | hb | hb
      · exact Or.inl hb
      · exact Or.inl (hal'.1.trans hb)
      · exact Or.inr hb
    rw [chain_alias hal', wotsSeed_alias _ hal' hb', wotsSeed_alias _ hal' hb']
    exact eval_chain_maskAt answers a (by omega) (halias hal' rfl) hc _
  · rw [wotsSeed_maskAt answers a lay tree leaf i hi hb hal']
    apply eval_maskAt_of_respects
    unfold chain
    refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
    rw [pad64_chainInput]
    intro s' v' hs' heq
    have hstep' : step < 256 := by
      have := (List.mem_range'_1.mp hstep).2
      omega
    have h := chainInput_eq_chainRow hi' hc' hstep' hs' heq
    exact hal' ⟨h.1, h.2.1⟩
theorem wotsEnd_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < chainCount lay) (hb : SlotOK a lay leaf) :
    WCT9.wotsEnd (maskAt answers a) lay tree leaf i = WCT9.wotsEnd answers lay tree leaf i := by
  unfold WCT9.wotsEnd
  apply eval_honestChain_maskAt answers a lay tree leaf i _ hi (by have := width_le lay i; omega) hb
  intro hal' hia
  obtain ⟨hl', -, -⟩ := hal'
  subst hl' hia
  exact depth_le_width answers a hi
theorem wotsValue_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) (hi : i < chainCount lay)
    (hdig : digits.getD i 0 ≤ 256) (hb : SlotOK a lay leaf)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ digits.getD i 0) :
    WCT9.wotsValue (maskAt answers a) lay tree leaf digits i = WCT9.wotsValue answers lay tree leaf digits i :=
  eval_honestChain_maskAt answers a lay tree leaf i _ hi hdig hb halias
theorem wotsRoot_maskAt (lay : Layer) (tree leaf : Nat) (hb : SlotOK a lay leaf) :
    WCT9.wotsRoot (maskAt answers a) lay tree leaf = WCT9.wotsRoot answers lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_maskAt answers a lay tree leaf i (List.mem_range.mp hi) hb)]
  exact eval_maskAt_of_respects answers a (respectsP_leafHash a _ _ _ _)
theorem height_pow_le (lay : Layer) : 2 ^ height lay ≤ 2 ^ 12 :=
  Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)
theorem wotsTree_maskAt (lay : Layer) (tree : Nat) (hal : lay = 0 ∨ MaskOK a) :
    WCT9.wotsTree (maskAt answers a) lay tree = WCT9.wotsTree answers lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_maskAt answers a lay tree leaf
    (slotOK_of hal (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega)))]
  exact eval_maskAt_of_respects answers a (respectsP_buildLevels a 3 _ _ _ _ (by decide))
theorem builtTree_maskAt_top (tree : Nat) :
    builtTree (maskAt answers a) 0 tree = builtTree answers 0 tree := by
  rw [← WCT9.wotsTree_top, ← WCT9.wotsTree_top, wotsTree_maskAt answers a 0 tree (Or.inl rfl)]
theorem leafRoot_maskAt_top (tree leaf : Nat) :
    Correctness.leafRoot (maskAt answers a) 0 tree leaf = Correctness.leafRoot answers 0 tree leaf := by
  rw [← WCT9.wotsRoot_top, ← WCT9.wotsRoot_top, wotsRoot_maskAt answers a 0 tree leaf (Or.inl rfl)]
theorem honestRoot_maskAt (lay : Layer) (tree : Nat) (hal : lay = 0 ∨ MaskOK a) :
    Extract.honestRoot (maskAt answers a) lay tree = Extract.honestRoot answers lay tree := by
  unfold Extract.honestRoot
  rw [wotsTree_maskAt answers a lay tree hal]
theorem honestPair_maskAt (lay : Layer) (tree : Nat) (hal : lay = 0 ∨ MaskOK a) :
    Extract.honestPair (maskAt answers a) lay tree = Extract.honestPair answers lay tree := by
  unfold Extract.honestPair
  rw [wotsTree_maskAt answers a lay tree hal]
theorem ftsQuery_untouchedP {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    UntouchedP a q :=
  untouchedP_of_untouched a ⟨ClaudeWCT.WCT9.Wots.ftsQuery_untouched a h,
    ClaudeWCT.WCT9.Wots.ftsQuery_untouched (slotAddr a) h⟩
theorem honestForest_maskAt (index : Nat) :
    Extract.honestForest (maskAt answers a) index = Extract.honestForest answers index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestForest_congr
    (fun _ hq => maskAt_untouched answers a (ftsQuery_untouchedP a hq))
end Mask
theorem leafMsg_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    leafMsg (maskAt answers a) L = leafMsg answers L := by
  unfold leafMsg
  split
  · rw [Mask.honestPair_maskAt answers a _ _ (Or.inr hal)]
  · rw [Mask.honestForest_maskAt]
theorem referenceSearch_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceSearch (maskAt answers a) L = referenceSearch answers L := by
  unfold referenceSearch
  rw [leafMsg_maskAt answers a hal]
  exact Mask.eval_maskAt_of_respects answers a (Mask.respectsP_layerCounterSearch a _ _ _ _ _ _)
theorem referenceDigits_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceDigits (maskAt answers a) L = referenceDigits answers L := by
  unfold referenceDigits
  rw [referenceSearch_maskAt answers a hal]
theorem referenceInput_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) (L : LeafAddr) :
    referenceInput (maskAt answers a) L = referenceInput answers L := by
  unfold referenceInput
  rw [referenceSearch_maskAt answers a hal, leafMsg_maskAt answers a hal]
theorem depth_maskAt_all (answers : Answers) (a b : ChainAddr) (hal : Mask.MaskOK a) :
    depth (maskAt answers a) b = depth answers b := by
  unfold depth
  rw [referenceDigits_maskAt answers a hal]
theorem depth_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) :
    depth (maskAt answers a) a = depth answers a :=
  depth_maskAt_all answers a a hal
theorem frontierValue_maskAt (answers : Answers) (a : ChainAddr) (hal : Mask.MaskOK a) :
    frontierValue (maskAt answers a) a = frontierValue answers a := by
  unfold frontierValue honestChainValue
  rw [depth_maskAt answers a hal]
  exact chain_maskAt answers a _ le_rfl (by have := Mask.depth_le_seven answers a; omega)
theorem frontierValue_maskAt_other (answers : Answers) (a b : ChainAddr) (hb : b.chain < chainCount b.key.lay)
    (hbl : b.key.leaf < 2 ^ 24) (hal : Mask.MaskOK a)
    (halias : Mask.LeafAlias b.key.lay b.key.tree b.key.leaf a.key → b.chain = a.chain → depth answers a ≤ depth answers b) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  unfold frontierValue honestChainValue
  rw [depth_maskAt_all answers a b hal]
  exact Mask.eval_honestChain_maskAt answers a _ _ _ _ _ hb (by have := Mask.depth_le_seven answers b; omega)
    (Mask.slotOK_of (Or.inr hal) hbl) halias
theorem frontierValue_maskAt_bounded (answers : Answers) (a b : ChainAddr)
    (ha : a.key.tree < 2 ^ 40 ∧ a.key.leaf < 2 ^ 24) (hb : b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 24)
    (hc : b.chain < chainCount b.key.lay) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  apply frontierValue_maskAt_other answers a b hc hb.2 (Or.inr ha.2)
  intro hal hch
  have hk : b.key = a.key := by
    have := hal.eq_of_lt hb.1 (by omega) ha.1 (by omega)
    cases hbk : b.key
    rw [hbk] at this
    exact this
  have : b = a := by
    cases b; cases a
    simp only at hk hch
    rw [hk, hch]
  rw [this]
end ClaudeWCT.W9.T3.Security.Wots
