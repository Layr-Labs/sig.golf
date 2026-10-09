import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRest

/-! # Leaf congruence (campaign X1 stage B, step B3)

The honest part of the WOTS reference game is unchanged when a lower leaf `L`'s family coefficients and its chain
rows below the signed digits change, as long as every chain of `L` keeps its frontier value (its honest value at
the signed digit) and its rows from the digit on (`LeafCongr`). This is the honest-side input of the seed-test
reduction: the leaf's step-0 rows can be programmed at the family seeds without the honest signer noticing. -/

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask

/-- Queries outside lower leaf `L`'s chain rows and family coefficient cells. -/
def LeafOut (L : LeafAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ c step value, c < chainCount L.lay → step < 256 → input ≠ chainRow ⟨L, c⟩ step value
  | .inr (.inl tweak) => ∀ j, j < 17 → tweak ≠ WCT9.lowerSeedHeader L.lay L.tree (WCT9.lowerCoefOrdinal L.leaf j / 2)
  | _ => True

/-- Chain addresses whose `Untouched` classes cover `LeafOut L`: the leaf's chains and, per coefficient cell, the
leaf-0 address whose seed tweak is that cell. -/
def coverAddrs (L : LeafAddr) : List ChainAddr :=
  (List.range (chainCount L.lay)).map (fun c => ⟨L, c⟩) ++
    (List.range 17).map (fun j => ⟨⟨L.lay, L.tree, 0⟩, 2 * (WCT9.lowerCoefOrdinal L.leaf j / 2)⟩)

theorem respects_cover {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) :
    ∀ cs : List ChainAddr, Respects (fun q => ∀ c ∈ cs, Untouched c q) p
  | [] => Respects.mono' (h ⟨⟨0, 0, 0⟩, 0⟩) (fun _ _ c hc => absurd hc List.not_mem_nil)
  | c :: cs => Respects.mono' (Respects.inter (h c) (respects_cover h cs)) (fun q hq c' hc' => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hq.1
      · exact hq.2 c' hc')

theorem leafOut_of_cover {L : LeafAddr} {q : Spec.Domain} (h : ∀ c ∈ coverAddrs L, Untouched c q) :
    LeafOut L q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro c step value hc hs heq
    exact h ⟨L, c⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)) step value hs heq
  · intro j hj heq
    apply h ⟨⟨L.lay, L.tree, 0⟩, 2 * (WCT9.lowerCoefOrdinal L.leaf j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    show tweak = seedTweak _
    rw [heq]
    unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (WCT9.lowerCoefOrdinal L.leaf j / 2) / 2 = WCT9.lowerCoefOrdinal L.leaf j / 2 by omega]
  · trivial

/-- A program respecting every chain's `Untouched` class respects `LeafOut L`. -/
theorem respects_leafOut {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) (L : LeafAddr) :
    Respects (LeafOut L) p :=
  Respects.mono' (respects_cover h (coverAddrs L)) fun _ hq => leafOut_of_cover hq

section Programs
variable (L : LeafAddr)
theorem respectsL_signForest (index : Nat) (output : HashOutput) :
    Respects (LeafOut L) (ClaudeWCT.WCT9.signForest index output) :=
  respects_leafOut (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_signForest c index output) L
theorem respectsL_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (LeafOut L) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respects_leafOut (fun c => respects_digest c _ _ _) L) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
theorem respectsL_privateMac (region : Region) : Respects (LeafOut L) (privateMac region) :=
  respects_leafOut (fun c => respects_privateMac c region) L
theorem respectsL_privateNonce (message : Message) : Respects (LeafOut L) (privateNonce message) :=
  respects_leafOut (fun c => respects_privateNonce c message) L
theorem respectsL_mask (level index : Nat) : Respects (LeafOut L) (mask level index) :=
  respects_leafOut (fun c => respects_mask c level index) L
theorem respectsL_nodeHash (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 1) :
    Respects (LeafOut L) (nodeHash tag lay tree heap left right) :=
  respects_leafOut (fun c => respects_nodeHash c tag lay tree heap left right ht) L
theorem respectsL_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (LeafOut L) (buildLevels tag lay tree h leaves) :=
  respects_leafOut (fun c => respects_buildLevels c tag lay tree h leaves ht) L
theorem respectsL_buildLevelsBelow (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (LeafOut L) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  respects_leafOut (fun c => by
    unfold WCT9.buildLevelsBelow
    exact Respects.foldlM _ _ (fun level _ levels =>
      Respects.bind (respects_buildLevel c tag lay tree h level _ ht) fun _ => Respects.pure' _) _) L
theorem respectsL_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (LeafOut L) (leafHash lay tree leaf ends) :=
  respects_leafOut (fun c => respects_leafHash c lay tree leaf ends) L
theorem respectsL_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (fuel counter : Nat) :
    Respects (LeafOut L) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) :=
  respects_leafOut (fun c => respects_layerCounterSearch c lay tree leaf msg fuel counter) L
theorem leafOut_ftsQuery {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    LeafOut L q :=
  leafOut_of_cover fun c _ => ClaudeWCT.WCT9.Wots.ftsQuery_untouched c h
/-- Chain rows outside `L` (another leaf, or a chain index beyond the leaf's chains). -/
theorem leafOut_chainInput {lay : Layer} {tree leaf i s : Nat} (v : Digest) (hi : i < 2 ^ 24) (hs : s < 256)
    (hna : ¬(LeafAlias lay tree leaf L ∧ i < chainCount L.lay)) :
    LeafOut L (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  intro c step value hc hstep heq
  rw [pad64_chainInput] at heq
  have hc' : c < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  obtain ⟨hal, rfl, -, -⟩ := chainInput_eq_chainRow (a := ⟨L, c⟩) hi hc' hs hstep heq
  exact hna ⟨hal, hc⟩
/-- Private cells of other layers or of non-zero tags are outside `L`. -/
theorem leafOut_header {t l tr p ix : Nat} (h : t % 256 ≠ 0 ∨ l % 256 ≠ L.lay.val) :
    LeafOut L (.inr (.inl (header t l tr p ix))) := by
  intro j _ heq
  unfold WCT9.lowerSeedHeader at heq
  have hf := header_fields heq
  have hL : L.lay.val % 256 = L.lay.val := Nat.mod_eq_of_lt (lt_trans L.lay.isLt (by decide))
  rcases h with h | h
  · exact h (by simpa using hf.1)
  · exact h (hf.2.1.trans hL)
theorem respectsL_topPath (cache : Cache) (leaf : Nat) : Respects (LeafOut L) (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ => Respects.bind (respectsL_mask L _ _) fun _ => Respects.pure' _
end Programs

/-- `T'` agrees with `T` outside `L` and on the other halves of `L`'s coefficient cells. -/
structure LeafAgree (L : LeafAddr) (T T' : Answers) : Prop where
  out : ∀ q, LeafOut L q → T' q = T q
  half : ∀ o, (∃ j, j < 17 ∧ o / 2 = WCT9.lowerCoefOrdinal L.leaf j / 2) →
    (∀ j, j < 17 → o ≠ WCT9.lowerCoefOrdinal L.leaf j) →
    WCT9.seedHalf (evalWithAnswerFn T' (WCT9.lowerSeedPair L.lay L.tree (o / 2))) o =
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair L.lay L.tree (o / 2))) o

/-- Leaf congruence: `LeafAgree`, plus agreement on the rows of `L`'s chains from their signed digits on and on
every chain's frontier value. -/
structure LeafCongr (L : LeafAddr) (T T' : Answers) : Prop extends LeafAgree L T T' where
  rows : ∀ c, c < chainCount L.lay → ∀ s v, depth T ⟨L, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRow ⟨L, c⟩ s v))) = T (.inl (.inr (chainRow ⟨L, c⟩ s v)))
  front : ∀ c, c < chainCount L.lay → frontierValue T' ⟨L, c⟩ = frontierValue T ⟨L, c⟩

section Agree
variable {L : LeafAddr} {T T' : Answers} (hC : LeafAgree L T T') (hL0 : L.lay ≠ 0) (hLleaf : L.leaf < 2 ^ 24)
include hC

theorem eval_out {α : Type} {p : M α} (h : Respects (LeafOut L) p) :
    evalWithAnswerFn T' p = evalWithAnswerFn T p :=
  (h.eval_eq hC.out)
theorem queried_out {α : Type} {p : M α} (h : Respects (LeafOut L) p) :
    SourceReplay.queried T' p = SourceReplay.queried T p :=
  (h.queried_eq hC.out)
theorem eval_chain_out {lay : Layer} {tree leaf i : Nat} (hi : i < 2 ^ 24)
    (hna : ¬(LeafAlias lay tree leaf L ∧ i < chainCount L.lay)) {start count : Nat} (hc : start + count ≤ 256)
    (v : Digest) :
    evalWithAnswerFn T' (chain lay tree leaf i start count v) = evalWithAnswerFn T (chain lay tree leaf i start count v) := by
  apply eval_out hC
  unfold chain
  refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
  have := List.mem_range'_1.mp hstep
  exact leafOut_chainInput L value hi (by omega) hna

include hL0 hLleaf in
/-- Seeds of other leaves are unchanged (they read other cells, or the other halves of `L`'s cells). -/
theorem wotsSeed_out {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬LeafAlias lay tree leaf L)
    (i : Nat) : WCT9.wotsSeed T' lay tree leaf i = WCT9.wotsSeed T lay tree leaf i := by
  by_cases h0 : lay = 0
  · rw [wotsSeed_eq _ h0, wotsSeed_eq _ h0, hC.out _ ?_]
    unfold wotsTweak
    rw [if_pos h0]
    apply leafOut_header L (Or.inr _)
    rw [h0]
    intro he
    exact hL0 (Fin.ext (by simpa using he.symm))
  · rw [WCT9.wotsSeed_lower _ h0, WCT9.wotsSeed_lower _ h0]
    unfold WCT9.lowerSeed
    congr 2
    funext j
    unfold WCT9.lowerCoef WCT9.lowerCoefN
    set o := WCT9.lowerCoefOrdinal leaf j.val with ho
    have ho2 : o / 2 < 2 ^ 32 := by
      have : o ≤ 17 * leaf + 16 := by rw [ho]; unfold WCT9.lowerCoefOrdinal WCT9.lowerCoefCount; omega
      omega
    by_cases hcell : ∃ j', j' < 17 ∧ WCT9.lowerSeedHeader lay tree (o / 2) =
        WCT9.lowerSeedHeader L.lay L.tree (WCT9.lowerCoefOrdinal L.leaf j' / 2)
    · obtain ⟨j', hj', he⟩ := hcell
      unfold WCT9.lowerSeedHeader at he
      obtain ⟨-, hl, ht, hp, -⟩ := header_fields he
      have hlay : lay = L.lay := Fin.ext (by
        rwa [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
          Nat.mod_eq_of_lt (lt_trans L.lay.isLt (by decide))] at hl)
      have hoL : WCT9.lowerCoefOrdinal L.leaf j' / 2 < 2 ^ 32 := by
        unfold WCT9.lowerCoefOrdinal WCT9.lowerCoefCount; omega
      rw [Nat.mod_eq_of_lt ho2, Nat.mod_eq_of_lt hoL] at hp
      have hpair : WCT9.lowerSeedPair lay tree (o / 2) = WCT9.lowerSeedPair L.lay L.tree (o / 2) := by
        unfold WCT9.lowerSeedPair privatePair
        rw [header_congr (by rw [hlay]) ht rfl]
      rw [hpair]
      apply hC.half o ⟨j', hj', hp⟩
      intro j'' hj'' hoe
      apply hna
      refine ⟨hlay, ht, ?_⟩
      have : leaf = L.leaf := by
        rw [ho] at hoe
        unfold WCT9.lowerCoefOrdinal WCT9.lowerCoefCount at hoe
        have := j.isLt
        omega
      rw [this]
    · have hq : T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) =
          T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) :=
        hC.out _ (fun j' hj' he => hcell ⟨j', hj', he⟩)
      unfold WCT9.lowerSeedPair privatePair privateHash
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      change WCT9.seedHalf ((T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
          (T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o =
        WCT9.seedHalf ((T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
          (T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o
      rw [hq]
include hL0 hLleaf in
theorem wotsEnd_out {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬LeafAlias lay tree leaf L)
    (i : Nat) (hi : i < chainCount lay) : WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_out hC hL0 hLleaf hleaf hna]
  exact eval_chain_out hC (by have := chainCount_le lay; simp only [Nat.reducePow]; omega)
    (fun h => hna h.1) (by have := width_le lay i; omega) _
include hL0 hLleaf in
theorem wotsRoot_out {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬LeafAlias lay tree leaf L) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_out hC hL0 hLleaf hleaf hna i (List.mem_range.mp hi))]
  exact eval_out hC (respectsL_leafHash L _ _ _ _)
include hL0 hLleaf in
theorem wotsTree_lay {lay : Layer} (hl : lay ≠ L.lay) (tree : Nat) :
    WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_out hC hL0 hLleaf
    (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega) (fun h => hl h.1))]
  exact eval_out hC (respectsL_buildLevels L 3 _ _ _ _ (by decide))
theorem honestForest_out (index : Nat) : Extract.honestForest T' index = Extract.honestForest T index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestForest_congr (fun _ hq => hC.out _ (leafOut_ftsQuery L hq))
include hL0 hLleaf in
/-- Messages of leaves on `L`'s layer come from the layer above (or the forest), which `L` does not touch. -/
theorem leafMsg_lay {K : LeafAddr} (hK : K.lay = L.lay) : leafMsg T' K = leafMsg T K := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [wotsTree_lay hC hL0 hLleaf (fun he => by
      have := congrArg Fin.val he
      rw [← hK] at this
      simp only at this
      omega)]
  · rw [honestForest_out hC]
include hL0 hLleaf in
theorem referenceSearch_lay {K : LeafAddr} (hK : K.lay = L.lay) : referenceSearch T' K = referenceSearch T K := by
  unfold referenceSearch
  rw [leafMsg_lay hC hL0 hLleaf hK]
  exact eval_out hC (respectsL_layerCounterSearch L _ _ _ _ _ _)
include hL0 hLleaf in
theorem depth_lay {a : ChainAddr} (ha : a.key.lay = L.lay) : depth T' a = depth T a := by
  unfold depth referenceDigits
  rw [referenceSearch_lay hC hL0 hLleaf ha]
end Agree

section Congr
variable {L : LeafAddr} {T T' : Answers} (hC : LeafCongr L T T') (hL0 : L.lay ≠ 0) (hLleaf : L.leaf < 2 ^ 24)
include hC
include hL0 hLleaf in
/-- `L`'s own chains: from the frontier on, the rows agree. -/
theorem eval_chainL {c count : Nat} (hc : c < chainCount L.lay) (hd : depth T ⟨L, c⟩ ≤ count) (hcount : count ≤ 256) :
    evalWithAnswerFn T' (chain L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T' L.lay L.tree L.leaf c)) =
      evalWithAnswerFn T (chain L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T L.lay L.tree L.leaf c)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = depth T ⟨L, c⟩ + e := ⟨count - depth T ⟨L, c⟩, by omega⟩
  have hd' : depth T' ⟨L, c⟩ = depth T ⟨L, c⟩ := depth_lay hC.toLeafAgree hL0 hLleaf rfl
  rw [Correctness.eval_chain_add, Correctness.eval_chain_add T, Nat.zero_add]
  have hf := hC.front c hc
  unfold frontierValue honestChainValue at hf
  simp only at hf
  rw [hd'] at hf
  rw [hf]
  refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
  unfold chain
  refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
  rw [pad64_chainInput]
  obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hstep
  exact hC.rows c hc step value hlo (by omega)
include hL0 hLleaf in
theorem wotsEnd_congr {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (i : Nat) (hi : i < chainCount lay) :
    WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  by_cases hal : LeafAlias lay tree leaf L
  · have hb : lay = 0 ∨ (leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24) := Or.inr ⟨hleaf, hLleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsEnd
    rw [chain_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb, hal.1]
    exact eval_chainL hC hL0 hLleaf hi' (depth_le_width T ⟨L, i⟩ hi') (by have := width_le L.lay i; omega)
  · exact wotsEnd_out hC.toLeafAgree hL0 hLleaf hleaf hal i hi
include hL0 hLleaf in
theorem wotsValue_congr {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (digits : List Nat) (i : Nat)
    (hi : i < chainCount lay) (hdig : digits.getD i 0 ≤ 256)
    (halias : LeafAlias lay tree leaf L → depth T ⟨L, i⟩ ≤ digits.getD i 0) :
    WCT9.wotsValue T' lay tree leaf digits i = WCT9.wotsValue T lay tree leaf digits i := by
  by_cases hal : LeafAlias lay tree leaf L
  · have hb : lay = 0 ∨ (leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24) := Or.inr ⟨hleaf, hLleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsValue
    rw [chain_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb]
    exact eval_chainL hC hL0 hLleaf hi' (halias hal) hdig
  · unfold WCT9.wotsValue
    rw [wotsSeed_out hC.toLeafAgree hL0 hLleaf hleaf hal]
    exact eval_chain_out hC.toLeafAgree (by have := chainCount_le lay; simp only [Nat.reducePow]; omega)
      (fun h => hal h.1) (by omega) _
include hL0 hLleaf in
theorem wotsRoot_congr {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_congr hC hL0 hLleaf hleaf i (List.mem_range.mp hi))]
  exact eval_out hC.toLeafAgree (respectsL_leafHash L _ _ _ _)
include hL0 hLleaf in
theorem wotsTree_congr (lay : Layer) (tree : Nat) : WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_congr hC hL0 hLleaf
    (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega))]
  exact eval_out hC.toLeafAgree (respectsL_buildLevels L 3 _ _ _ _ (by decide))
include hL0 hLleaf in
theorem leafMsg_congr (K : LeafAddr) : leafMsg T' K = leafMsg T K := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [wotsTree_congr hC hL0 hLleaf]
  · rw [honestForest_out hC.toLeafAgree]
include hL0 hLleaf in
theorem referenceSearch_congr (K : LeafAddr) : referenceSearch T' K = referenceSearch T K := by
  unfold referenceSearch
  rw [leafMsg_congr hC hL0 hLleaf K]
  exact eval_out hC.toLeafAgree (respectsL_layerCounterSearch L _ _ _ _ _ _)
include hL0 hLleaf in
theorem referenceDigits_congr (K : LeafAddr) : referenceDigits T' K = referenceDigits T K := by
  unfold referenceDigits
  rw [referenceSearch_congr hC hL0 hLleaf K]
include hL0 hLleaf in
theorem depth_congr (a : ChainAddr) : depth T' a = depth T a := by
  unfold depth
  rw [referenceDigits_congr hC hL0 hLleaf]
include hL0 hLleaf in
theorem eval_signTop_leaf (cache : Cache) (leaf : Nat) (hleaf : leaf < 2 ^ 24) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) :
    evalWithAnswerFn T' (signTop cache leaf digits) = evalWithAnswerFn T (signTop cache leaf digits) := by
  have hv : (List.range (chainCount 0)).map (leafValue T' 0 0 leaf digits) =
      (List.range (chainCount 0)).map (leafValue T 0 0 leaf digits) := by
    rw [← WCT9.wotsValue_top, ← WCT9.wotsValue_top]
    apply List.map_congr_left
    intro i hi
    apply wotsValue_congr hC hL0 hLleaf hleaf digits i (List.mem_range.mp hi)
    · have := hvalid i (List.mem_range.mp hi)
      have := width_le 0 i
      omega
    · intro hal
      exact absurd hal.1.symm hL0
  simp only [signTop, evalWithAnswerFn_bind, eval_buildLeaf_sig _ 0 0 leaf digits hvalid, evalWithAnswerFn_pure,
    hv]
  rw [eval_out hC.toLeafAgree (respectsL_topPath L _ _)]
include hL0 hLleaf in
theorem eval_buildTreeP_leaf {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (hsel : selected < 2 ^ height lay)
    (halias : LeafAlias lay tree selected L → ∀ i, i < chainCount L.lay → depth T ⟨L, i⟩ ≤ digits.getD i 0) :
    evalWithAnswerFn T' (WCT9.buildTreeP lay tree selected digits) =
      evalWithAnswerFn T (WCT9.buildTreeP lay tree selected digits) := by
  rw [WCT9.eval_buildTreeP_result _ hlay tree selected digits hvalid hsel,
    WCT9.eval_buildTreeP_result _ hlay tree selected digits hvalid hsel, wotsTree_congr hC hL0 hLleaf]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  apply wotsValue_congr hC hL0 hLleaf (by have := height_pow_le lay; omega) digits i hi'
  · have := hvalid i hi'
    have := width_le lay i
    omega
  · intro hal
    exact halias hal i (hal.1 ▸ hi')
include hL0 hLleaf in
theorem count_buildTreeP_leaf {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    (SourceReplay.queried T' (WCT9.buildTreeP lay tree selected digits)).length =
      (SourceReplay.queried T (WCT9.buildTreeP lay tree selected digits)).length := by
  have hroots : ∀ X, (evalWithAnswerFn X (WCT9.treeRowsP lay tree selected digits)).1 =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot X lay tree) := fun X => by
    obtain ⟨hlen, hroot, -, -⟩ := WCT9.eval_treeRowsP X hlay tree selected digits hvalid
    exact Correctness.list_eq_range_map _ _ _ hlen hroot
  have hm' : (List.range (2 ^ height lay)).map (WCT9.wotsRoot T' lay tree) =
      (List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree) :=
    List.map_congr_left (fun leaf hleaf => wotsRoot_congr hC hL0 hLleaf
      (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega))
  rw [WCT9.buildTreeP_factor]
  simp only [queried_length_bind, queried_length_pure, queried_length_treeRowsP]
  rw [hroots, hroots, hm', queried_out hC.toLeafAgree (respectsL_buildLevelsBelow L 3 _ _ _ _ (by decide))]
include hL0 hLleaf in
theorem eval_signLayers_leaf (hLtree : L.tree < 2 ^ 40) (cache : Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg T (routeLeaf index (Fin.ofNat 4 m))) →
      evalWithAnswerFn T' (WCT9.signLayersBC cache index n msg) =
        evalWithAnswerFn T (WCT9.signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [WCT9.signLayersBC, evalWithAnswerFn_bind]
      rw [eval_out hC.toLeafAgree (respectsL_layerCounterSearch L _ _ _ _ _ _)]
      by_cases hn0 : n = 0
      · subst hn0
        have hD : ((evalWithAnswerFn T (WCT9.layerCounterSearch (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
            (route index (Fin.ofNat 4 0)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 0)))).map Prod.snd).getD dummyTop =
            referenceDigits T (routeLeaf index (Fin.ofNat 4 0)) := by
          rw [hmsg 0 rfl]
          exact ClaudeWCT.W9.T3.Security.Wots.Mask.topSigned_reference T (routeLeaf index (Fin.ofNat 4 0)) rfl
        simp only [ite_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        have hlt : (route index (Fin.ofNat 4 0)).1 < 2 ^ 24 := by
          have := route_leaf_bound index (Fin.ofNat 4 0)
          have := height_pow_le (Fin.ofNat 4 0)
          omega
        rw [hD, eval_signTop_leaf hC hL0 hLleaf cache _ hlt _ (ClaudeWCT.W9.T3.Security.Wots.Mask.referenceDigits_spec T (routeLeaf index (Fin.ofNat 4 0))).2]
      cases hs : evalWithAnswerFn T (WCT9.layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hn0, ite_false]; rfl
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (WCT9.layerCounterSearch_some T _ _ _ msg (WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
            (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hsearch : referenceSearch T (routeLeaf index (Fin.ofNat 4 n)) = some (counter, digits) := by
            unfold referenceSearch
            rw [← hmsg n rfl]
            exact hs
          simp only [hn0, ite_false]
          · simp only [evalWithAnswerFn_bind]
            have hl0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
              rw [h] at hv
              exact hn0 hv.symm
            rw [eval_buildTreeP_leaf hC hL0 hLleaf hl0 _ _ digits hvalid (route_leaf_bound index _)
                (fun hal i _ => ClaudeWCT.W9.T3.Security.Wots.Mask.routeLeaf_alias (a := ⟨L, i⟩) hindex hsearch hLtree (by omega) hal),
              WCT9.eval_buildTreeP_result T hl0 _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            rw [WCT9.topPair_take]
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rw [ih (by omega) _ (fun m' hm' => by
              obtain rfl : m = m' := by omega
              exact ClaudeWCT.W9.T3.Security.Wots.Mask.signedMsg_succ T index m (by omega))]
            cases evalWithAnswerFn T (WCT9.signLayersBC cache index (m + 1) _) <;> rfl
include hL0 hLleaf in
theorem count_signLayers_leaf (hLtree : L.tree < 2 ^ 40) (cache : Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg T (routeLeaf index (Fin.ofNat 4 m))) →
      (SourceReplay.queried T' (WCT9.signLayersBC cache index n msg)).length =
        (SourceReplay.queried T (WCT9.signLayersBC cache index n msg)).length := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [WCT9.signLayersBC]
      refine count_bind_of (eval_out hC.toLeafAgree (respectsL_layerCounterSearch L _ _ _ _ _ _))
        (by rw [queried_out hC.toLeafAgree (respectsL_layerCounterSearch L _ _ _ _ _ _)]) ?_
      by_cases hn0 : n = 0
      · simp only [hn0, ite_true]
        generalize ((evalWithAnswerFn T (WCT9.layerCounterSearch (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
          (route index (Fin.ofNat 4 0)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 0)))).map Prod.snd).getD dummyTop = dg
        rw [queried_length_bind, queried_length_bind, queried_length_signTop, queried_length_signTop]
        rfl
      cases hs : evalWithAnswerFn T (WCT9.layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hn0, ite_false]; rfl
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (WCT9.layerCounterSearch_some T _ _ _ msg (WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
            (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hsearch : referenceSearch T (routeLeaf index (Fin.ofNat 4 n)) = some (counter, digits) := by
            unfold referenceSearch
            rw [← hmsg n rfl]
            exact hs
          simp only [hn0, ite_false]
          · have hl0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
              rw [h] at hv
              exact hn0 hv.symm
            refine count_bind_of (eval_buildTreeP_leaf hC hL0 hLleaf hl0 _ _ digits hvalid (route_leaf_bound index _)
                (fun hal i _ => ClaudeWCT.W9.T3.Security.Wots.Mask.routeLeaf_alias (a := ⟨L, i⟩) hindex hsearch hLtree (by omega) hal))
              (count_buildTreeP_leaf hC hL0 hLleaf hl0 _ _ digits hvalid) ?_
            rw [WCT9.eval_buildTreeP_result T hl0 _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            rw [WCT9.topPair_take]
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hmsg' : ∀ m', m + 1 = m' + 1 → WCT9.LayerMsg.pair
                (WCT9.topPair (Fin.ofNat 4 (m + 1)) (WCT9.wotsTree T (Fin.ofNat 4 (m + 1))
                  (route index (Fin.ofNat 4 (m + 1))).2)).1
                (WCT9.topPair (Fin.ofNat 4 (m + 1)) (WCT9.wotsTree T (Fin.ofNat 4 (m + 1))
                  (route index (Fin.ofNat 4 (m + 1))).2)).2 =
                leafMsg T (routeLeaf index (Fin.ofNat 4 m')) := fun m' hm' => by
              rw [show m' = m by omega]
              exact ClaudeWCT.W9.T3.Security.Wots.Mask.signedMsg_succ T index m (by omega)
            refine count_bind_of (eval_signLayers_leaf hC hL0 hLleaf hLtree cache index hindex (m + 1) (by omega)
              _ hmsg') (ih (by omega) _ hmsg') ?_
            cases evalWithAnswerFn T (WCT9.signLayersBC cache index (m + 1) _) <;> rfl
include hL0 hLleaf in
theorem eval_signPayload_leaf (hLtree : L.tree < 2 ^ 40) (cache : Cache) (message : Message) :
    evalWithAnswerFn T' (signPayload cache message) = evalWithAnswerFn T (signPayload cache message) := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine eval_bind_of (eval_out hC.toLeafAgree (respectsL_privateNonce L message)) ?_
  generalize evalWithAnswerFn T (privateNonce message) = rho
  refine eval_bind_of (eval_out hC.toLeafAgree (respectsL_digestSearch L _ _ _ _)) ?_
  generalize evalWithAnswerFn T (ClaudeWCT.WCT9.digestSearch rho message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine eval_bind_of (eval_out hC.toLeafAgree (respectsL_signForest L _ _)) ?_
    rw [ClaudeWCT.WCT9.eval_signForest]
    dsimp only
    refine eval_bind_of (eval_signLayers_leaf hC hL0 hLleaf hLtree cache _ (WCT9.digestIndex_lt _) 4
      le_rfl _ (fun m hm => ?_)) ?_
    · obtain rfl : m = 3 := by omega
      rw [← Extract.honestForest_eq_wct9]
      exact ClaudeWCT.W9.T3.Security.Wots.Mask.signedMsg_top T _ (WCT9.digestIndex_lt _)
    · generalize evalWithAnswerFn T (WCT9.signLayersBC cache (WCT9.digestIndex output) 4 _) = pieces
      rcases pieces with _ | pieces <;> rfl
include hL0 hLleaf in
theorem count_signPayload_leaf (hLtree : L.tree < 2 ^ 40) (cache : Cache) (message : Message) :
    (SourceReplay.queried T' (signPayload cache message)).length =
      (SourceReplay.queried T (signPayload cache message)).length := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine count_bind_of (eval_out hC.toLeafAgree (respectsL_privateNonce L message))
    (by rw [queried_out hC.toLeafAgree (respectsL_privateNonce L message)]) ?_
  generalize evalWithAnswerFn T (privateNonce message) = rho
  refine count_bind_of (eval_out hC.toLeafAgree (respectsL_digestSearch L _ _ _ _))
    (by rw [queried_out hC.toLeafAgree (respectsL_digestSearch L _ _ _ _)]) ?_
  generalize evalWithAnswerFn T (ClaudeWCT.WCT9.digestSearch rho message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine count_bind_of (eval_out hC.toLeafAgree (respectsL_signForest L _ _))
      (by rw [queried_out hC.toLeafAgree (respectsL_signForest L _ _)]) ?_
    rw [ClaudeWCT.WCT9.eval_signForest]
    dsimp only
    have hmsg : ∀ m, 4 = m + 1 → WCT9.LayerMsg.forest (ClaudeWCT.WCT9.honestForest T (WCT9.digestIndex output)) =
        leafMsg T (routeLeaf (WCT9.digestIndex output) (Fin.ofNat 4 m)) := fun m hm => by
      obtain rfl : m = 3 := by omega
      rw [← Extract.honestForest_eq_wct9]
      exact ClaudeWCT.W9.T3.Security.Wots.Mask.signedMsg_top T _ (WCT9.digestIndex_lt _)
    refine count_bind_of (eval_signLayers_leaf hC hL0 hLleaf hLtree cache _ (WCT9.digestIndex_lt _)
      4 le_rfl _ hmsg) (count_signLayers_leaf hC hL0 hLleaf hLtree cache _ (WCT9.digestIndex_lt _) 4
      le_rfl _ hmsg) ?_
    generalize evalWithAnswerFn T (WCT9.signLayersBC cache (WCT9.digestIndex output) 4 _) = pieces
    rcases pieces with _ | pieces <;> rfl
include hL0 hLleaf in
theorem eval_sign_leaf (hLtree : L.tree < 2 ^ 40) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn T' (FullGame.authenticatedSign published request) =
      evalWithAnswerFn T (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine eval_bind_of (eval_out hC.toLeafAgree (respectsL_privateMac L _)) ?_
  split
  · exact eval_signPayload_leaf hC hL0 hLleaf hLtree _ _
  · rfl
include hL0 hLleaf in
theorem count_sign_leaf (hLtree : L.tree < 2 ^ 40) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    (SourceReplay.queried T' (FullGame.authenticatedSign published request)).length =
      (SourceReplay.queried T (FullGame.authenticatedSign published request)).length := by
  unfold FullGame.authenticatedSign
  refine count_bind_of (eval_out hC.toLeafAgree (respectsL_privateMac L _)) (by rw [queried_out hC.toLeafAgree (respectsL_privateMac L _)]) ?_
  split
  · exact count_signPayload_leaf hC hL0 hLleaf hLtree _ _
  · rfl
include hL0 hLleaf in
theorem eval_keygenPayload_leaf : evalWithAnswerFn T' keygenPayload = evalWithAnswerFn T keygenPayload := by
  have hb : builtTree T' 0 0 = builtTree T 0 0 := by
    rw [← WCT9.wotsTree_top, ← WCT9.wotsTree_top, wotsTree_congr hC hL0 hLleaf]
  rw [Correctness.keygenPayload_eq, Correctness.eval_cachePayloadProgram, Correctness.eval_cachePayloadProgram,
    Correctness.eval_buildTree_levels T' 0 0 0 [] (Cost.validDigits_nil 0),
    Correctness.eval_buildTree_levels T 0 0 0 [] (Cost.validDigits_nil 0), hb]
  simp only [eval_out hC.toLeafAgree (respectsL_mask L _ _)]
include hL0 hLleaf in
theorem eval_keygen_leaf : evalWithAnswerFn T' keygen = evalWithAnswerFn T keygen := by
  unfold keygen
  refine eval_bind_of (eval_keygenPayload_leaf hC hL0 hLleaf) ?_
  generalize evalWithAnswerFn T keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  exact eval_out hC.toLeafAgree (Respects.bind (respectsL_privateMac L region) fun _ => Respects.pure' _)
include hL0 hLleaf in
theorem count_keygen_leaf : (SourceReplay.queried T' keygen).length = (SourceReplay.queried T keygen).length := by
  have hr : (List.range (2 ^ height 0)).map (Correctness.leafRoot T' 0 0) =
      (List.range (2 ^ height 0)).map (Correctness.leafRoot T 0 0) := by
    rw [← WCT9.wotsRoot_top, ← WCT9.wotsRoot_top]
    exact List.map_congr_left fun leaf hleaf => wotsRoot_congr hC hL0 hLleaf
      (by have := List.mem_range.mp hleaf; have := height_pow_le 0; omega)
  have hp : (SourceReplay.queried T' keygenPayload).length = (SourceReplay.queried T keygenPayload).length := by
    rw [Correctness.keygenPayload_eq, queried_length_cachePayload, queried_length_cachePayload,
      Correctness.buildTree_eq, queried_length_bind T', queried_length_bind T,
      queried_length_treeRows, queried_length_treeRows,
      Correctness.eval_treeRows _ 0 0 0 [] (Cost.validDigits_nil 0),
      Correctness.eval_treeRows _ 0 0 0 [] (Cost.validDigits_nil 0)]
    dsimp only
    rw [hr, queried_length_bind, queried_length_bind, queried_length_pure, queried_length_pure,
      queried_out hC.toLeafAgree (respectsL_buildLevels L 3 _ _ _ _ (by decide))]
  unfold keygen
  refine count_bind_of (eval_keygenPayload_leaf hC hL0 hLleaf) hp ?_
  generalize evalWithAnswerFn T keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  rw [queried_out hC.toLeafAgree (Respects.bind (respectsL_privateMac L region) fun _ => Respects.pure' _)]
include hL0 hLleaf in
theorem offlineGame_leaf (hLtree : L.tree < 2 ^ 40) (adversary : Final.AdversaryP) :
    offlineGame T' adversary = offlineGame T adversary := by
  have hk : keygenCharge T' = keygenCharge T := count_keygen_leaf hC hL0 hLleaf
  have hs : offlineSign T' = offlineSign T := by
    funext published request
    unfold offlineSign
    rw [show signCharge T' published request = signCharge T published request from
      count_sign_leaf hC hL0 hLleaf hLtree published request, eval_sign_leaf hC hL0 hLleaf hLtree]
  have hi : offlineImpl T' = offlineImpl T := by
    funext published
    unfold offlineImpl
    rw [hs]
  unfold offlineGame offlineInteraction
  rw [hk, eval_keygen_leaf hC hL0 hLleaf, hi]
include hL0 hLleaf in
/-- **Leaf congruence of the reference game.** -/
theorem referenceGame_leaf (hLtree : L.tree < 2 ^ 40) (adversary : Final.AdversaryP) (q : Nat) :
    referenceGame T' adversary q = referenceGame T adversary q := by
  unfold referenceGame
  rw [offlineGame_leaf hC hL0 hLleaf hLtree]
end Congr
end Leaf
end ClaudeWCT.W9.T3.Security.Wots
