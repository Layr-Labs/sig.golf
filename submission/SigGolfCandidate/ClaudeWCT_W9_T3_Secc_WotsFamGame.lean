import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamCongr
set_option Elab.async false

/-! # Family restart, step P3b: family congruence leaves the honest reference game unchanged (r3-lean-seedfam)

Port of the leaf route (`WotsLeafCongr` legacy helpers + normalized `CanonicalRef.Leaf.Congr`, and the game part of
`WotsLeafProg`: `referenceGame_leaf`) from one WOTS leaf to a family `F` of `grp` leaves sharing one seed polynomial,
against the abstract `FamScheme` interface.

* `FamRestart`: family `respects` lemmas (`respectsF_*`), `famOut_chainInput`, and the legacy-namespace helpers
  `eval_chain_outF`, `wotsEnd_outF`, `wotsRoot_outF`, `wotsTree_layF`, `honestForest_outF`, `leafMsg_layF`,
  `referenceSearch_layF`, `depth_layF`.
* `CanonicalRef.FamGame`: `FamCongr S messages F T T'` (`FamAgree` plus rows/front of every chain of every leaf of `F`),
  `wotsEnd/Value/Root/Tree_congrF`, `sourceMessages_congrF`, the signer/keygen invariance and
  **`referenceGame_fam`**.

Aliasing split: a leaf either `FamAlias`es `F` — then it is the family member `famLeaf F (leaf % grp)` up to the
`2^40` tree aliasing, and the one-leaf lemmas `Mask.chainW_alias` / `wotsSeed_alias` / `sourceLeaf_alias` apply to that
member — or not, and then `wotsSeed_outF` / `eval_chain_outF` apply.
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

variable (S : FamScheme)

/-! ## Family members and aliasing -/

/-- Leaves of an admissible family are below `2^24`. -/
theorem famLeaf_lt {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) (l : Fin (S.grp F.lay)) :
    (famLeaf (S.grp F.lay) F l).leaf < 2 ^ 24 := by
  show S.grp F.lay * F.fam + l.val < 2 ^ 24
  have := l.isLt
  omega

theorem famBound_lt {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    F.fam * S.grp F.lay < 2 ^ 24 := by
  have := S.grp_pos F.lay
  rw [Nat.mul_comm]
  omega

/-- A family-aliasing leaf is (up to tree aliasing) the member `leaf % grp` of the family. -/
theorem famAlias_member {F : FamAddr} {lay : Layer} {tree leaf : Nat} (h : FamAlias S F lay tree leaf) :
    ∃ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) ∧
      (famLeaf (S.grp F.lay) F l).leaf = leaf := by
  have hleq : (famLeaf (S.grp F.lay) F ⟨leaf % S.grp F.lay, Nat.mod_lt _ (S.grp_pos _)⟩).leaf = leaf := by
    show S.grp F.lay * F.fam + leaf % S.grp F.lay = leaf
    rw [← h.2.2, Nat.div_add_mod]
  exact ⟨⟨leaf % S.grp F.lay, Nat.mod_lt _ (S.grp_pos _)⟩, ⟨h.1, h.2.1, by rw [hleq]⟩, hleq⟩

/-- A small leaf aliasing a member of the family family-aliases the family. -/
theorem famAlias_of_leafAlias {F : FamAddr} (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {lay : Layer}
    {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) {l : Fin (S.grp F.lay)}
    (h : LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l)) : FamAlias S F lay tree leaf := by
  refine ⟨h.1, h.2.1, ?_⟩
  have h2 : leaf % 2 ^ 32 = (S.grp F.lay * F.fam + l.val) % 2 ^ 32 := h.2.2
  have hl := famLeaf_lt S hF l
  change S.grp F.lay * F.fam + l.val < 2 ^ 24 at hl
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  rw [h2, Nat.mul_add_div (S.grp_pos _), Nat.div_eq_of_lt l.isLt, Nat.add_zero]

theorem leafAlias_famLay {F : FamAddr} {lay : Layer} {tree leaf : Nat} {l : Fin (S.grp F.lay)}
    (h : LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l)) : lay = F.lay := h.1

/-! ## Programs respecting `FamOut` -/

section Programs
variable (F : FamAddr)
theorem respectsF_signForest (index : Nat) (output : HashOutput) :
    Respects (FamOut S F) (ClaudeWCT.WCT9.signForest index output) :=
  respects_famOut S (fun c => ClaudeWCT.WCT9.Wots.Mask.respects_signForest c index output) F
theorem respectsF_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Respects (FamOut S F) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [ClaudeWCT.WCT9.digestSearch]
      refine Respects.bind (respects_famOut S (fun c => respects_digest c _ _ _) F) fun output => ?_
      split
      · exact Respects.pure' _
      · exact ih _
theorem respectsF_privateMac (region : Region) : Respects (FamOut S F) (privateMac region) :=
  respects_famOut S (fun c => respects_privateMac c region) F
theorem respectsF_privateNonce (message : Message) : Respects (FamOut S F) (privateNonce message) :=
  respects_famOut S (fun c => respects_privateNonce c message) F
theorem respectsF_mask (level index : Nat) : Respects (FamOut S F) (mask level index) :=
  respects_famOut S (fun c => respects_mask c level index) F
theorem respectsF_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (FamOut S F) (buildLevels tag lay tree h leaves) :=
  respects_famOut S (fun c => respects_buildLevels c tag lay tree h leaves ht) F
theorem respectsF_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Respects (FamOut S F) (leafHash lay tree leaf ends) :=
  respects_famOut S (fun c => respects_leafHash c lay tree leaf ends) F
theorem respectsF_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (fuel counter : Nat) :
    Respects (FamOut S F) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) :=
  respects_famOut S (fun c => respects_layerCounterSearch c lay tree leaf msg fuel counter) F
theorem famOut_ftsQuery {index : Nat} {q : SigGolfCandidate.T3.Spec.Domain} (h : WCT9.FtsQuery index q) :
    FamOut S F q :=
  famOut_of_cover S fun c _ => ClaudeWCT.WCT9.Wots.ftsQuery_untouched c h
/-- Chain rows outside `F` (a leaf not aliasing the family, or a chain index beyond the leaves' chains). -/
theorem famOut_chainInput (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) {lay : Layer} {tree leaf i s : Nat}
    (v : Digest) (hleaf : leaf < 2 ^ 24) (hi : i < 2 ^ 24) (hs : s < 256)
    (hna : ¬(FamAlias S F lay tree leaf ∧ i < chainCount F.lay)) :
    FamOut S F (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i s v)))) := by
  intro l c step value hc hstep heq
  rw [pad64_chainInputW] at heq
  have hc' : c < 2 ^ 24 := by have := chainCount_le F.lay; simp only [Nat.reducePow]; omega
  obtain ⟨hal, rfl, -, -⟩ :=
    chainInputW_eq_chainRowW (a := ⟨famLeaf (S.grp F.lay) F l, c⟩) hi hc' hs (by omega) heq
  exact hna ⟨famAlias_of_leafAlias S hF hleaf hal, hc⟩
theorem respectsF_topPath (cache : Cache) (leaf : Nat) : Respects (FamOut S F) (topPath cache leaf) := by
  unfold topPath
  exact Respects.mapM _ _ fun level _ => Respects.bind (respectsF_mask S F _ _) fun _ => Respects.pure' _
theorem famOut_of_hdr (input : HashInput) (h : BitVec 128)
    (hblock : SigGolfCandidate.T3M.Extract.hdrBlock input = SphincsSecurity.bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, step < 7 → h ≠ chainHeader l tr leaf i step) :
    FamOut S F (.inl (.inr input)) := by
  intro l c step value _ hs heq
  have hb : SigGolfCandidate.T3M.Extract.hdrBlock (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ step value) =
      SphincsSecurity.bytesLE 16 (chainHeader (famLeaf (S.grp F.lay) F l).lay (famLeaf (S.grp F.lay) F l).tree
        (famLeaf (S.grp F.lay) F l).leaf c step) :=
    WCT9.chainInputW_header _ _ _ _ _ _
  rw [heq, hb] at hblock
  exact htag _ _ _ _ _ hs (SphincsSecurity.bytesLE_injective hblock).symm
theorem famOut_of_length (input : HashInput) (hl : input.length ≠ 64) : FamOut S F (.inl (.inr input)) := by
  intro l c step value _ _ heq
  apply hl
  rw [heq, chainRowW_length]
theorem foldOK_famOut (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) : Mask.FoldOK (FamOut S F) lay tree h := by
  intro level i left right hlev hi
  refine famOut_of_hdr S F _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader ?_ l tr leaf c step hs
  by_cases h0 : lay = 0
  · exact Or.inl h0
  · exact Or.inr (Mask.lowerHeap_lt' hlev (h7 h0) hi)
theorem respectsF_lowerLevels (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (FamOut S F) (WCT9.lowerLevels lay tree h leaves) :=
  Mask.respects_lowerLevels' (foldOK_famOut S F lay tree h h7) leaves hlen
/-! Top-nonce layer (r3-lean-nonsec): the img-v6 top tree leaves the family classes untouched. -/
theorem respectsF_topNodeHashN (heap n : Nat) (left right : Digest) :
    Respects (FamOut S F) (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  apply Respects.projHash
  rw [Mask.pad64_topNodeInput_block4]
  exact famOut_of_hdr S F _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ _ right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs
theorem respectsF_topNonceSearch (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Respects (FamOut S F) (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respectsF_topNodeHashN S F _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respectsF_topNodeHashN S F _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respectsF_topNonceSearch h heap left right fuel (n + 1)
theorem respectsF_buildTopLevels (leaves : List Digest) : Respects (FamOut S F) (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · rw [← WCT9.lowerNodeHash_top]
    exact Mask.respects_lowerNodeHash' _ _ _ _ _ (famOut_of_hdr S F _ _
      (SigGolfCandidate.T3M.Extract.hdrBlock_block4 _ _ 0 _)
      fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader (Or.inl rfl) l tr leaf c step hs)
  · unfold topNodeAt
    exact Respects.map _ (respectsF_topNonceSearch S F _ _ _ _ _ _)
theorem respectsF_buildLevelsBelowW (tag lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (FamOut S F) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  Mask.respects_buildLevelsBelow' (foldOK_famOut S F lay tree h h7) tag leaves hlen
theorem respectsF_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects (FamOut S F) (WCT9.lowerLeafHash lay tree leaf ends) :=
  Mask.respects_lowerLeafHash' _ _ _ _ (famOut_of_length S F _ (Mask.pad64_long_length
    (SigGolfCandidate.T3.Security.Wots.Enc.leafInput_long lay tree leaf ends hlen)))
end Programs

/-! ## Legacy-namespace helpers under `FamAgree` -/

section Agree
variable {S} {F : FamAddr} {T T' : Answers} (hC : FamAgree S F T T')
  (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC

theorem queried_outF {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    SourceReplay.queried T' p = SourceReplay.queried T p :=
  h.queried_eq hC.out

include hF in
theorem eval_chain_outF {lay : Layer} {tree leaf i : Nat} (hleaf : leaf < 2 ^ 24) (hi : i < 2 ^ 24)
    (hna : ¬(FamAlias S F lay tree leaf ∧ i < chainCount F.lay)) {start count : Nat} (hc : start + count ≤ 256)
    (v : Digest) :
    evalWithAnswerFn T' (WCT9.chainW lay tree leaf i start count v) =
      evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count v) := by
  apply eval_outF hC
  exact Mask.respects_chainW' _ _ _ _ _ _ _ fun step value _ hhi =>
    famOut_chainInput S F hF value hleaf hi (by omega) hna

include hF in
theorem wotsEnd_outF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬FamAlias S F lay tree leaf)
    (i : Nat) (hi : i < chainCount lay) : WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_outF hC (famBound_lt S hF) hleaf hna]
  exact eval_chain_outF hC hF hleaf (by have := chainCount_le lay; simp only [Nat.reducePow]; omega)
    (fun h => hna h.1) (by have := width_le lay i; omega) _

include hF in
theorem wotsRoot_outF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24) (hna : ¬FamAlias S F lay tree leaf) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_outF hC hF hleaf hna i (List.mem_range.mp hi))]
  exact eval_outF hC (respectsF_lowerLeafHash S F _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))

include hF in
theorem wotsTree_layF {lay : Layer} (hl : lay ≠ F.lay) (tree : Nat) :
    WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_outF hC hF
    (by have := List.mem_range.mp hleaf; have := height_pow_le lay; omega) (fun h => hl h.1))]
  split_ifs
  · exact eval_outF hC (respectsF_buildTopLevels S F _)
  · exact eval_outF hC (respectsF_lowerLevels S F _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))

theorem honestForest_outF (index : Nat) : Extract.honestTop T' index = Extract.honestTop T index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hC.out _ (famOut_ftsQuery S F hq))

include hF in
/-- Messages of leaves on `F`'s layer come from the layer above (or the forest), which `F` does not touch. -/
theorem leafMsg_layF {K : LeafAddr} (hK : K.lay = F.lay) : leafMsg T' K = leafMsg T K := by
  unfold leafMsg
  split
  · unfold Extract.honestPair
    rw [wotsTree_layF hC hF (fun he => by
      have := congrArg Fin.val he
      rw [← hK] at this
      simp only at this
      omega)]
  · rw [honestForest_outF hC]

include hF in
theorem referenceSearch_layF {K : LeafAddr} (hK : K.lay = F.lay) :
    referenceSearch T' K = referenceSearch T K := by
  unfold referenceSearch
  rw [leafMsg_layF hC hF hK]
  exact eval_outF hC (respectsF_layerCounterSearch S F _ _ _ _ _ _)

include hF in
theorem depth_layF {a : ChainAddr} (ha : a.key.lay = F.lay) : depth T' a = depth T a := by
  unfold depth referenceDigits
  rw [referenceSearch_layF hC hF ha]
end Agree

#print axioms famAlias_of_leafAlias
#print axioms wotsTree_layF
#print axioms depth_layF
end ClaudeWCT.W9.T3.Security.Wots.FamRestart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.W9.T3.Security.Wots.FamRestart
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
variable (S : FamScheme)

/-- Family congruence: `FamAgree`, plus agreement on the rows of every chain of every REAL leaf of `F` (index below
`2 ^ height F.lay`; the last family of a tree may have phantom members) from its signed digit on, and on every such
chain's frontier value. -/
structure FamCongr (messages : LeafAddr → WCT9.LayerMsg) (F : FamAddr) (T T' : Answers) : Prop
    extends FamAgree S F T T' where
  rows : ∀ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay → ∀ c, c < chainCount F.lay → ∀ s v,
    CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ s v))) =
      T (.inl (.inr (chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ s v)))
  front : ∀ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay → ∀ c, c < chainCount F.lay →
    CanonicalRef.frontierValue T' messages ⟨famLeaf (S.grp F.lay) F l, c⟩ =
      CanonicalRef.frontierValue T messages ⟨famLeaf (S.grp F.lay) F l, c⟩

variable {S} {messages : LeafAddr → WCT9.LayerMsg} {F : FamAddr} {T T' : Answers}

theorem searchOf_congrF (hC : FamAgree S F T T') (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf T' messages K remaining = CanonicalRef.searchOf T messages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_outF hC (respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F)

theorem referenceSearch_congrF (hC : FamAgree S F T T') (K : LeafAddr) :
    CanonicalRef.referenceSearch T' messages K = CanonicalRef.referenceSearch T messages K :=
  CanonicalRef.referenceSearch_congr (fun K r _ => searchOf_congrF hC K r) K

theorem depth_congrF (hC : FamAgree S F T T') (a : ChainAddr) :
    CanonicalRef.depth T' messages a = CanonicalRef.depth T messages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_congrF hC]

section Chains
variable (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC

/-- A member's own chains: from the frontier on, the rows agree. -/
theorem eval_chainF {L : LeafAddr} (hL : ∃ l : Fin (S.grp F.lay), S.grp F.lay * F.fam + l.val < 2 ^ height F.lay ∧ famLeaf (S.grp F.lay) F l = L) {c count : Nat}
    (hc : c < chainCount L.lay) (hd : CanonicalRef.depth T messages ⟨L, c⟩ ≤ count) (hcount : count ≤ 256) :
    evalWithAnswerFn T' (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T' L.lay L.tree L.leaf c)) =
      evalWithAnswerFn T (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T L.lay L.tree L.leaf c)) := by
  obtain ⟨l, hr, rfl⟩ := hL
  obtain ⟨e, rfl⟩ : ∃ e, count = CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ + e :=
    ⟨count - CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩, by omega⟩
  have hd' : CanonicalRef.depth T' messages ⟨famLeaf (S.grp F.lay) F l, c⟩ =
      CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, c⟩ :=
    depth_congrF hC.toFamAgree ⟨famLeaf (S.grp F.lay) F l, c⟩
  rw [eval_chainW_add', eval_chainW_add' T, Nat.zero_add]
  have hf := hC.front l hr c hc
  unfold CanonicalRef.frontierValue honestChainValueW at hf
  simp only at hf
  rw [hd'] at hf
  rw [hf]
  refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
  refine Mask.respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW]
  exact hC.rows l hr c hc step value hlo (by omega)

include hF in
theorem wotsEnd_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) (i : Nat) (hi : i < chainCount lay) :
    WCT9.wotsEnd T' lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  have hleaf : leaf < 2 ^ 24 := by have := height_pow_le lay; omega
  by_cases hfa : FamAlias S F lay tree leaf
  · obtain ⟨l, hal, hll⟩ := famAlias_member S hfa
    have hr : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 : S.grp F.lay * F.fam + l.val = leaf := hll
      rw [h1, ← leafAlias_famLay S hal]
      exact hreal
    generalize hL : famLeaf (S.grp F.lay) F l = L at hal hll
    have hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24 := ⟨hleaf, hll ▸ hleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsEnd
    rw [Mask.chainW_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb,
      show maxDigit lay i = maxDigit L.lay i by rw [hal.1]]
    exact eval_chainF hC ⟨l, hr, hL⟩ hi' (CanonicalRef.depth_le T messages ⟨L, i⟩ hi')
      (by have := width_le L.lay i; omega)
  · exact wotsEnd_outF hC.toFamAgree hF hleaf hfa i hi

include hF in
theorem wotsValue_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) (digits : List Nat) (i : Nat)
    (hi : i < chainCount lay) (hdig : digits.getD i 0 ≤ 256)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) →
      CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    WCT9.wotsValue T' lay tree leaf digits i = WCT9.wotsValue T lay tree leaf digits i := by
  have hleaf : leaf < 2 ^ 24 := by have := height_pow_le lay; omega
  by_cases hfa : FamAlias S F lay tree leaf
  · obtain ⟨l, hal, hll⟩ := famAlias_member S hfa
    have hr : S.grp F.lay * F.fam + l.val < 2 ^ height F.lay := by
      have h1 : S.grp F.lay * F.fam + l.val = leaf := hll
      rw [h1, ← leafAlias_famLay S hal]
      exact hreal
    have hdl := halias l hal
    generalize hL : famLeaf (S.grp F.lay) F l = L at hal hll hdl
    have hb : leaf < 2 ^ 24 ∧ L.leaf < 2 ^ 24 := ⟨hleaf, hll ▸ hleaf⟩
    have hi' : i < chainCount L.lay := hal.1 ▸ hi
    unfold WCT9.wotsValue
    rw [Mask.chainW_alias hal, wotsSeed_alias T' hal hb, wotsSeed_alias T hal hb]
    exact eval_chainF hC ⟨l, hr, hL⟩ hi' hdl hdig
  · unfold WCT9.wotsValue
    rw [wotsSeed_outF hC.toFamAgree (famBound_lt S hF) hleaf hfa]
    exact eval_chain_outF hC.toFamAgree hF hleaf
      (by have := chainCount_le lay; simp only [Nat.reducePow]; omega) (fun h => hfa h.1) (by omega) _

include hF in
theorem wotsRoot_congrF {lay : Layer} {tree leaf : Nat} (hreal : leaf < 2 ^ height lay) :
    WCT9.wotsRoot T' lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i hi => wotsEnd_congrF hC hF hreal i (List.mem_range.mp hi))]
  exact eval_outF hC.toFamAgree (respectsF_lowerLeafHash S F _ _ _ _
    (by simp only [List.length_map, List.length_range]; exact SigGolfCandidate.T3.Security.Wots.Enc.chainCount_ge4 _))

include hF in
theorem wotsTree_congrF (lay : Layer) (tree : Nat) : WCT9.wotsTree T' lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf hleaf => wotsRoot_congrF hC hF (List.mem_range.mp hleaf))]
  split_ifs
  · exact eval_outF hC.toFamAgree (respectsF_buildTopLevels S F _)
  · exact eval_outF hC.toFamAgree (respectsF_lowerLevels S F _ _ _ (by fin_cases lay <;> decide) _
      (by simp only [List.length_map, List.length_range]; exact le_rfl))
end Chains

theorem famOut_of_coverP {q : Spec.Domain} (h : ∀ c ∈ coverAddrsF S F, UntouchedP c q) : FamOut S F q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro l c step value hc hs heq
    exact h ⟨famLeaf (S.grp F.lay) F l, c⟩ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_finRange l,
      List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩⟩)) step value hs heq
  · intro j hj heq
    apply h ⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    rw [heq]
    unfold seedTweakP seedSlot seedTweak WCT9.lowerOrdinal WCT9.lowerSeedHeader
    simp only
    split <;> simp [Nat.mul_div_cancel_left]
  · trivial

variable (S) in
theorem respects_famOutP {α : Type} {p : M α} (h : ∀ c, Respects (UntouchedP c) p) (F : FamAddr) :
    Respects (FamOut S F) p :=
  Respects.mono' (ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf.respects_coverP h (coverAddrsF S F))
    fun _ hq => famOut_of_coverP hq

theorem buildForest_outF (hC : FamAgree S F T T') (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    ExecEq T T' (buildForest index selected words) (buildForest index selected words) := by
  have h := respects_famOutP S (fun a => CanonicalRef.respectsP_buildForest a index selected words) F
  exact ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem forestCommitment_outF (hC : FamAgree S F T T') (index : Nat) :
    CanonicalRef.forestCommitment T' index = CanonicalRef.forestCommitment T index := by
  have h := congrArg Prod.snd (buildForest_outF hC index (forestSelectionFromOutput 0) (forestWordsFromOutput 0)).1
  simpa only [buildForest_commitment] using h

theorem sourceMessages_congrF (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    CanonicalRef.sourceMessages T' = CanonicalRef.sourceMessages T := by
  funext K
  unfold CanonicalRef.sourceMessages
  split
  · unfold Extract.honestPair
    rw [wotsTree_congrF hC hF]
  · rw [forestCommitment_outF hC.toFamAgree]
end Congr

section Game
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
variable {S : FamScheme} {messages : LeafAddr → LayerMsg} {F : FamAddr} {T T' : Answers}

section Pieces
variable (hC : FamCongr S messages F T T') (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
include hC hF

theorem eval_signTop_fam (cache : Cache) (leaf : Nat) (hleaf : leaf < 2 ^ height 0) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias 0 0 leaf (famLeaf (S.grp F.lay) F l) →
      ∀ i, i < chainCount F.lay → CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    evalWithAnswerFn T' (signTop cache leaf digits) = evalWithAnswerFn T (signTop cache leaf digits) := by
  have hv : (List.range (chainCount 0)).map (WCT9.wotsValue T' 0 0 leaf digits) =
      (List.range (chainCount 0)).map (WCT9.wotsValue T 0 0 leaf digits) := by
    apply List.map_congr_left
    intro i hi
    apply wotsValue_congrF hC hF hleaf digits i (List.mem_range.mp hi)
    · have := hvalid i (List.mem_range.mp hi)
      have := width_le 0 i
      omega
    · intro l hal
      exact halias l hal i (leafAlias_famLay S hal ▸ List.mem_range.mp hi)
  rw [Mask.eval_signTop_wots T' cache leaf digits hvalid, Mask.eval_signTop_wots T cache leaf digits hvalid, hv,
    eval_outF hC.toFamAgree (respectsF_topPath S F _ _)]

theorem wotsPieces_congrF {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ height lay)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (halias : ∀ l : Fin (S.grp F.lay), LeafAlias lay tree leaf (famLeaf (S.grp F.lay) F l) →
      ∀ i, i < chainCount F.lay → CanonicalRef.depth T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ ≤ digits.getD i 0) :
    wotsPieces T' lay tree leaf digits = wotsPieces T lay tree leaf digits := by
  unfold wotsPieces
  rw [wotsTree_congrF hC hF]
  congr 1
  apply List.map_congr_left
  intro i hi
  apply wotsValue_congrF hC hF hleaf digits i (List.mem_range.mp hi)
  · have := hvalid i (List.mem_range.mp hi); have := width_le lay i; omega
  · intro l hal
    exact halias l hal i (leafAlias_famLay S hal ▸ List.mem_range.mp hi)

theorem fixedPrepared_pieces_congrF (index : Nat) (hi : index < 2 ^ 31) (lay : Layer) (hlay : lay ≠ 0)
    {counter : BitVec 32} {digits : List Nat} {low : Bool}
    (hsearch : CanonicalRef.referenceSearch T messages (sourceLeaf index lay) = some (counter, digits, low))
    (htree : F.tree < 2 ^ 40) :
    preparedPieces lay (route index lay).1 (fixedPrepared T' index lay) digits =
      preparedPieces lay (route index lay).1 (fixedPrepared T index lay) digits := by
  have hv := CanonicalRef.Mask.source_digits_valid T messages lay hsearch rfl
  have hp (X : Answers) : preparedPieces lay (route index lay).1 (fixedPrepared X index lay) digits =
      wotsPieces X lay (route index lay).2 (route index lay).1 digits := by
    unfold fixedPrepared
    rw [← eval_buildTreePrefixes_result X hlay _ _ (route_leaf_bound index lay)]
    exact preparedPieces_result X hlay _ _ digits hv (route_leaf_bound index lay)
  rw [hp, hp]
  apply wotsPieces_congrF hC hF (route_leaf_bound index lay) digits hv
  intro l hal i _
  exact CanonicalRef.Mask.sourceLeaf_alias T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ hi hsearch htree
    (famLeaf_lt S hF l) hal
end Pieces

theorem searchPreparedLayers_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index < 2 ^ 31)
    (forest : PairRoot) (hforest : LayerMsg.pair forest.1 forest.2 = sourceMessages T (sourceLeaf index 3)) :
    let prepared := (⟨fixedPrepared T index 1, fixedPrepared T index 2, fixedPrepared T index 3⟩ : PreparedRoots)
    let prepared' := (⟨fixedPrepared T' index 1, fixedPrepared T' index 2, fixedPrepared T' index 3⟩ : PreparedRoots)
    ExecEq T T' (searchPreparedLayers cache index prepared forest)
      (searchPreparedLayers cache index prepared' forest) := by
  let messages := sourceMessages T
  have hlevels (lay : Layer) : (fixedPrepared T' index lay).levels = (fixedPrepared T index lay).levels := by
    dsimp only [fixedPrepared]
    rw [wotsTree_congrF hC hF]
  have hs (lay : Layer) (remaining : Nat)
      (_hc : referenceContext T messages (sourceLeaf index lay) = some remaining) :
      ExecEq T T' (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay))
        (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay)) :=
    let h := respects_famOut S (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) F
    ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩
  have h0 : LayerMsg.pair (topPair 1 (fixedPrepared T index 1).levels).1
      (topPair 1 (fixedPrepared T index 1).levels).2 = messages (sourceLeaf index 0) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 0 (by decide)]; rfl
  have h1 : LayerMsg.pair (topPair 2 (fixedPrepared T index 2).levels).1
      (topPair 2 (fixedPrepared T index 2).levels).2 = messages (sourceLeaf index 1) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 1 (by decide)]; rfl
  have h2 : LayerMsg.pair (topPair 3 (fixedPrepared T index 3).levels).1
      (topPair 3 (fixedPrepared T index 3).levels).2 = messages (sourceLeaf index 2) := by
    dsimp only [messages]
    rw [fixedPrepared_pair, sourceMessages_route_lower T index 2 (by decide)]; rfl
  have h3 : LayerMsg.pair forest.1 forest.2 = messages (sourceLeaf index 3) := hforest
  have hc0 : referenceContext T messages (sourceLeaf index 0) = some WCT9.CanonicalPolicy.totalCredit := rfl
  dsimp only
  unfold searchPreparedLayers
  dsimp only
  rw [hlevels 1, hlevels 2, hlevels 3, h0, h1, h2, h3]
  refine ExecEq.bind (hs 0 WCT9.CanonicalPolicy.totalCredit hc0) ?_
  intro found0 hr0
  cases found0 with
  | none => exact ExecEq.pure' _ _ _
  | some found0 =>
    rcases found0 with ⟨counter0, digits0, low0⟩
    have href0 := referenceSearch_of_run hc0 hr0
    have hc1 : referenceContext T messages (sourceLeaf index 1) =
        some (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0 digits0) := by
      apply context_parent_success (leaf := sourceLeaf index 1) (by change 1 ≠ 0; decide)
      · rw [sourceLeaf_parent index 1 (by decide)]; exact hc0
      · rw [sourceLeaf_parent index 1 (by decide)]; exact href0
    dsimp only
    split
    · exact ExecEq.pure' _ _ _
    · refine ExecEq.bind (hs 1 _ hc1) ?_
      intro found1 hr1
      cases found1 with
      | none => exact ExecEq.pure' _ _ _
      | some found1 =>
        rcases found1 with ⟨counter1, digits1, low1⟩
        have href1 := referenceSearch_of_run hc1 hr1
        have hc2 : referenceContext T messages (sourceLeaf index 2) =
            some (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0
              digits0) 1 low1 digits1) := by
          apply context_parent_success (leaf := sourceLeaf index 2) (by change 2 ≠ 0; decide)
          · rw [sourceLeaf_parent index 2 (by decide)]; exact hc1
          · rw [sourceLeaf_parent index 2 (by decide)]; exact href1
        dsimp only
        split
        · exact ExecEq.pure' _ _ _
        · refine ExecEq.bind (hs 2 _ hc2) ?_
          intro found2 hr2
          cases found2 with
          | none => exact ExecEq.pure' _ _ _
          | some found2 =>
            rcases found2 with ⟨counter2, digits2, low2⟩
            have href2 := referenceSearch_of_run hc2 hr2
            have hc3 : referenceContext T messages (sourceLeaf index 3) =
                some (CanonicalPolicy.nextResidual
                  (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual WCT9.CanonicalPolicy.totalCredit 0 low0
                    digits0) 1 low1 digits1) 2 low2 digits2) := by
              apply context_parent_success (leaf := sourceLeaf index 3) (by change 3 ≠ 0; decide)
              · rw [sourceLeaf_parent index 3 (by decide)]; exact hc2
              · rw [sourceLeaf_parent index 3 (by decide)]; exact href2
            dsimp only
            split
            · exact ExecEq.pure' _ _ _
            · refine ExecEq.bind (hs 3 _ hc3) ?_
              intro found3 hr3
              cases found3 with
              | none => exact ExecEq.pure' _ _ _
              | some found3 =>
                rcases found3 with ⟨counter3, digits3, low3⟩
                have href3 := referenceSearch_of_run hc3 hr3
                have hv0 := CanonicalRef.Mask.source_digits_valid T messages 0 href0 rfl
                have ht : ExecEq T T' (signTop cache (route index 0).1 digits0)
                    (signTop cache (route index 0).1 digits0) := by
                  have hlt : (route index (0 : Layer)).1 < 2 ^ height (0 : Layer) := route_leaf_bound index (0 : Layer)
                  refine ⟨eval_signTop_fam hC hF cache _ hlt _ hv0 ?_, ?_⟩
                  · intro l hal i _
                    apply CanonicalRef.Mask.sourceLeaf_alias T messages ⟨famLeaf (S.grp F.lay) F l, i⟩ hi href0
                      htree (famLeaf_lt S hF l)
                    rw [route_top_tree index hi]
                    exact hal
                  · rw [SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop,
                      SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop]
                refine ExecEq.bind ht ?_
                intro top _
                apply ExecEq.pure_eq
                rw [fixedPrepared_pieces_congrF hC hF index hi 1 (by decide) href1 htree,
                  fixedPrepared_pieces_congrF hC hF index hi 2 (by decide) href2 htree,
                  fixedPrepared_pieces_congrF hC hF index hi 3 (by decide) href3 htree]

theorem execEq_outF (hC : FamAgree S F T T') {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    ExecEq T T' p p :=
  ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem signFromOutput_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    ExecEq T T' (signFromOutput cache rho counter output) (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine ExecEq.bind (buildForest_outF hC.toFamAgree _ _ _) ?_
  intro forest hforest
  refine ExecEq.bind_effect (Mask.queried_length_prepareRoots_congr _ _ _) ?_
  simp only [prepareRoots_result]
  refine ExecEq.bind (searchPreparedLayers_famEq hC htree hF cache _ (digestIndex_lt output) forest.2 ?_) ?_
  · rw [← hforest, buildForest_commitment, sourceMessages_route_bottom T _ (digestIndex_lt output)]
  · intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem signPayload_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    ExecEq T T'
      (SigGolfCandidate.Research.SharedForest.signPayload cache message)
      (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateNonce S F _)) ?_
  intro rho _
  refine ExecEq.bind (execEq_outF hC.toFamAgree
    (respects_famOutP S (fun a => CanonicalRef.respectsP_sharedDigestSearch a _ _ _ _) F)) ?_
  intro selected _
  cases selected with
  | none => exact ExecEq.pure' _ _ _
  | some selected =>
    rcases selected with ⟨counter, output⟩
    refine ExecEq.bind (signFromOutput_famEq hC htree hF _ _ _ _) ?_
    intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem authenticatedSign_famEq (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    ExecEq T T'
      (PairedOuter.FullGame.authenticatedSign published request)
      (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateMac S F _)) ?_
  intro tag _
  split
  · exact signPayload_famEq hC htree hF _ _
  · exact ExecEq.pure' _ _ _

theorem keygen_famEq (hC : FamCongr S (sourceMessages T) F T T')
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24) :
    ExecEq T T' SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygen := by
  have hp : ExecEq T T' keygenPayload keygenPayload := by
    refine ⟨?_, ?_⟩
    · rw [Wots.Mask.eval_keygenPayload_wots, Wots.Mask.eval_keygenPayload_wots, wotsTree_congrF hC hF]
      exact eval_outF hC.toFamAgree (respects_famOut S (fun c => Wots.Mask.respects_keygenRest c _) F)
    · refine Wots.Mask.queried_length_keygenPayload_congr (S := FamOut S F)
        (fun L => respects_famOut S (fun c => Wots.Mask.respects_buildTopLevels c L) F) T' T hC.out ?_
      rw [(SigGolfCandidate.T3.Correctness.eval_buildTopTree T').trans (WCT9.wotsTree_top T').symm,
        (SigGolfCandidate.T3.Correctness.eval_buildTopTree T).trans (WCT9.wotsTree_top T).symm,
        wotsTree_congrF hC hF]
  unfold SigGolfCandidate.T3.keygen
  refine ExecEq.bind hp ?_
  rintro ⟨pk, region⟩ _
  exact ExecEq.bind (execEq_outF hC.toFamAgree (respectsF_privateMac S F _)) fun _ _ => ExecEq.pure' _ _ _

/-- **Family congruence of the reference game.** If `T'` agrees with `T` outside family `F` (and on the other halves
of its cells), and on the rows of all of `F`'s chains from their signed digits on and on their frontier values, the
honest reference game is unchanged. -/
theorem referenceGame_fam (hC : FamCongr S (sourceMessages T) F T T') (htree : F.tree < 2 ^ 40)
    (hF : S.grp F.lay * F.fam + S.grp F.lay ≤ 2 ^ 24)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame T' adversary q = PairedReference.referenceGame T adversary q :=
  PairedReference.referenceGame_congr _ _ (keygen_famEq hC hF).1 (keygen_famEq hC hF).2
    (fun cache request => (authenticatedSign_famEq hC htree hF cache request).1)
    (fun cache request => (authenticatedSign_famEq hC htree hF cache request).2) adversary q
end Game

#print axioms wotsTree_congrF
#print axioms sourceMessages_congrF
#print axioms searchPreparedLayers_famEq
#print axioms referenceGame_fam
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.FamGame
