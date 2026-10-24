import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsMaskRef
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsMaskRest

/-! # Leaf congruence (campaign X1 stage B, step B3)

The honest part of the WOTS reference game is unchanged when a leaf `L`'s family coefficients and its chain
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

/-- Queries outside leaf `L`'s chain rows and family coefficient cells (every layer; top leaves since T8D). -/
def LeafOut (L : LeafAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ c step value, c < chainCount L.lay → step < 7 → input ≠ chainRowW ⟨L, c⟩ step value
  | .inr (.inl tweak) => ∀ j, j < WCT9.famCount L.lay →
      tweak ≠ WCT9.lowerSeedHeader L.lay L.tree (WCT9.famOrdinal L.lay L.leaf j / 2)
  | _ => True

/-- Chain addresses whose `Untouched` classes cover `LeafOut L`: the leaf's chains and, per coefficient cell, the
leaf-0 address whose seed tweak is that cell. -/
def coverAddrs (L : LeafAddr) : List ChainAddr :=
  (List.range (chainCount L.lay)).map (fun c => ⟨L, c⟩) ++
    (List.range (WCT9.famCount L.lay)).map (fun j => ⟨⟨L.lay, L.tree, 0⟩, 2 * (WCT9.famOrdinal L.lay L.leaf j / 2)⟩)

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
    have hu := h ⟨L, c⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)) step value
      (by omega)
    unfold chainRowW WCT9.chainInputW at heq
    split at heq
    · exact hu.2 heq
    · exact hu.1 heq
  · intro j hj heq
    apply h ⟨⟨L.lay, L.tree, 0⟩, 2 * (WCT9.famOrdinal L.lay L.leaf j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    show tweak = seedTweak _
    rw [heq]
    unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (WCT9.famOrdinal L.lay L.leaf j / 2) / 2 = WCT9.famOrdinal L.lay L.leaf j / 2 by omega]
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
theorem respectsL_buildLevels (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 1) :
    Respects (LeafOut L) (buildLevels tag lay tree h leaves) :=
  respects_leafOut (fun c => respects_buildLevels c tag lay tree h leaves ht) L
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
    LeafOut L (.inl (.inr (pad64 (WCT9.chainInputW lay tree leaf i s v)))) := by
  intro c step value hc hstep heq
  rw [pad64_chainInputW] at heq
  have hc' : c < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  obtain ⟨hal, rfl, -, -⟩ := chainInputW_eq_chainRowW (a := ⟨L, c⟩) hi hc' hs (by omega) heq
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
/-! C2/C3 (FULL): the lower trees and the chain-0 high half. -/
theorem leafOut_of_hdr (input : HashInput) (h : BitVec 128)
    (hblock : SigGolfCandidate.T3M.Extract.hdrBlock input = SphincsSecurity.bytesLE 16 h)
    (htag : ∀ (l : Layer) tr leaf i step, step < 7 → h ≠ chainHeader l tr leaf i step) :
    LeafOut L (.inl (.inr input)) := by
  intro c step value _ hs heq
  have hb : SigGolfCandidate.T3M.Extract.hdrBlock (chainRowW ⟨L, c⟩ step value) =
      SphincsSecurity.bytesLE 16 (chainHeader L.lay L.tree L.leaf c step) :=
    WCT9.chainInputW_header _ _ _ _ _ _
  rw [heq, hb] at hblock
  exact htag _ _ _ _ _ hs (SphincsSecurity.bytesLE_injective hblock).symm
theorem leafOut_of_length (input : HashInput) (hl : input.length ≠ 64) : LeafOut L (.inl (.inr input)) := by
  intro c step value _ _ heq
  apply hl
  rw [heq, chainRowW_length]
theorem foldOK_leafOut (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) : Mask.FoldOK (LeafOut L) lay tree h := by
  intro level i left right hlev hi
  refine leafOut_of_hdr L _ _ (SigGolfCandidate.T3M.Extract.hdrBlock_block4 left _ 0 right)
    fun l tr leaf c step hs => Mask.merkleTweak_ne_chainHeader ?_ l tr leaf c step hs
  by_cases h0 : lay = 0
  · exact Or.inl h0
  · exact Or.inr (Mask.lowerHeap_lt' hlev (h7 h0) hi)
theorem respectsL_lowerLevels (lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (LeafOut L) (WCT9.lowerLevels lay tree h leaves) :=
  Mask.respects_lowerLevels' (foldOK_leafOut L lay tree h h7) leaves hlen
theorem respectsL_buildLevelsBelowW (tag lay tree h : Nat) (h7 : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) : Respects (LeafOut L) (WCT9.buildLevelsBelow tag lay tree h leaves) :=
  Mask.respects_buildLevelsBelow' (foldOK_leafOut L lay tree h h7) tag leaves hlen
theorem respectsL_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    Respects (LeafOut L) (WCT9.lowerLeafHash lay tree leaf ends) :=
  Mask.respects_lowerLeafHash' _ _ _ _ (leafOut_of_length L _ (Mask.pad64_long_length
    (SigGolfCandidate.T3.Security.Wots.Enc.leafInput_long lay tree leaf ends hlen)))
end Programs

/-- `T'` agrees with `T` outside `L` and on the other halves of `L`'s coefficient cells. -/
structure LeafAgree (L : LeafAddr) (T T' : Answers) : Prop where
  out : ∀ q, LeafOut L q → T' q = T q
  half : ∀ o, (∃ j, j < WCT9.famCount L.lay ∧ o / 2 = WCT9.famOrdinal L.lay L.leaf j / 2) →
    (∀ j, j < WCT9.famCount L.lay → o ≠ WCT9.famOrdinal L.lay L.leaf j) →
    WCT9.seedHalf (evalWithAnswerFn T' (WCT9.lowerSeedPair L.lay L.tree (o / 2))) o =
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair L.lay L.tree (o / 2))) o

/-- Leaf congruence: `LeafAgree`, plus agreement on the rows of `L`'s chains from their signed digits on and on
every chain's frontier value. -/
structure LeafCongr (L : LeafAddr) (T T' : Answers) : Prop extends LeafAgree L T T' where
  rows : ∀ c, c < chainCount L.lay → ∀ s v, depth T ⟨L, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRowW ⟨L, c⟩ s v))) = T (.inl (.inr (chainRowW ⟨L, c⟩ s v)))
  front : ∀ c, c < chainCount L.lay → frontierValue T' ⟨L, c⟩ = frontierValue T ⟨L, c⟩

section Agree
variable {L : LeafAddr} {T T' : Answers} (hC : LeafAgree L T T') (hLleaf : L.leaf < 2 ^ 24)
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
    evalWithAnswerFn T' (WCT9.chainW lay tree leaf i start count v) =
      evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count v) := by
  apply eval_out hC
  exact Mask.respects_chainW' _ _ _ _ _ _ _ fun step value _ hhi =>
    leafOut_chainInput L value hi (by omega) hna

theorem honestForest_out (index : Nat) : Extract.honestTop T' index = Extract.honestTop T index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hC.out _ (leafOut_ftsQuery L hq))
end Agree

section Congr
variable {L : LeafAddr} {T T' : Answers} (hC : LeafCongr L T T') (hLleaf : L.leaf < 2 ^ 24)
include hC
end Congr
end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

structure Congr (messages : LeafAddr → WCT9.LayerMsg) (L : LeafAddr) (T T' : Answers) : Prop
    extends LeafAgree L T T' where
  rows : ∀ c, c < chainCount L.lay → ∀ s v, CanonicalRef.depth T messages ⟨L, c⟩ ≤ s → s < 256 →
    T' (.inl (.inr (chainRowW ⟨L,c⟩ s v)))=T (.inl (.inr (chainRowW ⟨L,c⟩ s v)))
  front : ∀ c, c < chainCount L.lay →
    CanonicalRef.frontierValue T' messages ⟨L,c⟩=CanonicalRef.frontierValue T messages ⟨L,c⟩

variable {messages : LeafAddr → WCT9.LayerMsg} {L : LeafAddr} {T T' : Answers}

theorem searchOf_congr (hC : LeafAgree L T T') (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf T' messages K remaining=CanonicalRef.searchOf T messages K remaining := by
  unfold CanonicalRef.searchOf
  exact eval_out hC (respects_leafOut (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) L)

theorem referenceSearch_congr (hC : LeafAgree L T T') (K : LeafAddr) :
    CanonicalRef.referenceSearch T' messages K=CanonicalRef.referenceSearch T messages K :=
  CanonicalRef.referenceSearch_congr (fun K r _ => searchOf_congr hC K r) K

theorem depth_congr (hC : LeafAgree L T T') (a : ChainAddr) :
    CanonicalRef.depth T' messages a=CanonicalRef.depth T messages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_congr hC]

section Congr
variable (hC : Congr messages L T T') (hLleaf : L.leaf < 2^24)
include hC
include hLleaf in
/-- `L`'s own chains: from the frontier on, the rows agree. -/
theorem eval_chainL {c count : Nat} (hc : c < chainCount L.lay) (hd : CanonicalRef.depth T messages ⟨L, c⟩ ≤ count) (hcount : count ≤ 256) :
    evalWithAnswerFn T' (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T' L.lay L.tree L.leaf c)) =
      evalWithAnswerFn T (WCT9.chainW L.lay L.tree L.leaf c 0 count (WCT9.wotsSeed T L.lay L.tree L.leaf c)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = CanonicalRef.depth T messages ⟨L, c⟩ + e := ⟨count - CanonicalRef.depth T messages ⟨L, c⟩, by omega⟩
  have hd' : CanonicalRef.depth T' messages ⟨L, c⟩ = CanonicalRef.depth T messages ⟨L, c⟩ := depth_congr hC.toLeafAgree ⟨L, c⟩
  rw [eval_chainW_add', eval_chainW_add' T, Nat.zero_add]
  have hf := hC.front c hc
  unfold CanonicalRef.frontierValue honestChainValueW at hf
  simp only at hf
  rw [hd'] at hf
  rw [hf]
  refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
  refine Mask.respects_chainW' _ _ _ _ _ _ _ fun step value hlo hhi => ?_
  rw [pad64_chainInputW]
  exact hC.rows c hc step value hlo (by omega)
end Congr
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
