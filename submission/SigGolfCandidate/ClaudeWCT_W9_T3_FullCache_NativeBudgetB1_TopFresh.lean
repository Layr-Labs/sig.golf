import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopMoment
import SigGolfCandidate.T3_FullCache_NativeBudget

/-! # Freshness of the top-node trial inputs (r3-lean-topbytes, img-v6)

`TopQ heap x`: the oracle input `x` carries the top-node tweak of `heap` (`queryHeader x = nodeTweak 3 0 0 heap`);
every trial `topTrial heap n l r` does. Markers separate the root children (heaps 2, 3: marker byte 2, 3) from the
private pairs / MAC / nonce (`header`, marker 1), the chains (marker ≥ 128) and the leaf hashes (`leafTweak`, marker 1);
other top nodes differ in the low tweak word (`topNodeWord`, injective on heaps 1..4095).

`Bound.allQueries` / `Bound.and_of_allQueries` combine query predicates with the shape-carrying `Bound` (needed because
the node heaps of a level are only below 4096 thanks to the level lengths). -/

namespace SigGolfCandidate.T3.Cost.Bound
open OracleComp OracleSpec

theorem allQueries {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) : AllQueriesSatisfy oa P := by
  induction h with
  | pure a k hp => exact allQueriesSatisfy_pure _ _
  | query q f k hq _ ih => exact (allQueriesSatisfy_query_bind_iff q f P).mpr ⟨hq, ih⟩

theorem and_of_allQueries {P P' : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (hA : AllQueriesSatisfy oa P) (h : Bound P' Post k oa) : Bound (fun q => P' q ∧ P q) Post k oa := by
  induction h with
  | pure a k hp => exact .pure a k hp
  | query q f k hq _ ih =>
      have hq' := (allQueriesSatisfy_query_bind_iff q f P).mp hA
      exact .query q f k ⟨hq, hq'.1⟩ (fun u => ih u (hq'.2 u))

end SigGolfCandidate.T3.Cost.Bound

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery avoids_pure avoids_bind avoids_map avoids_foldlM
  avoids_shortHash_of_ne avoids_privateHash_of_ne HasTag hasTag_privatePair)
open SigGolfCandidate.T3.QuerySpace (queryHeader queryHeader_padded queryHeader_leafInput)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The input carries the top-node tweak of `heap`. -/
def TopQ (heap : Nat) (x : HashInput) : Prop := queryHeader x = bytesLE 16 (nodeTweak 3 0 0 heap)

theorem topQ_topTrial (heap n : Nat) (left right : Digest) : TopQ heap (topTrial heap n left right) := by
  unfold TopQ topTrial topNodeInput
  simpa only [List.append_assoc] using
    queryHeader_padded (bytesLE 16 left) (nonceBytes n ++ bytesLE 16 right) (bytesLE_length ..) (nodeTweak 3 0 0 heap)

theorem topQ_ne {input target : HashInput} {hdr : BitVec 128} {heap : Nat}
    (h : queryHeader input = bytesLE 16 hdr) (hn : hdr ≠ nodeTweak 3 0 0 heap) (ht : TopQ heap target) :
    input ≠ target := by
  rintro rfl
  exact hn (bytesLE_injective (h.symm.trans ht))

theorem topNodeWord_eq {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096) : topNodeWord heap = heap := by
  unfold topNodeWord; omega

theorem tweakMarker_top {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096) :
    tweakMarker (nodeTweak 3 0 0 heap) = heap % 256 := by
  have hl := nodeTweak_top_low 0 heap
  unfold tweakLow at hl
  unfold tweakMarker
  rw [← Nat.mod_mod_of_dvd _ (by norm_num : 256 ∣ 2 ^ 64), hl, topNodeWord_eq h1 h2]

theorem ne_top_of_marker {hdr : BitVec 128} {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096)
    (hm : tweakMarker hdr ≠ heap % 256) : hdr ≠ nodeTweak 3 0 0 heap := by
  rintro rfl
  exact hm (tweakMarker_top h1 h2)

theorem top_tweak_ne {a b : Nat} (ha1 : 1 ≤ a) (ha2 : a < 4096) (hb1 : 1 ≤ b) (hb2 : b < 4096) (hne : a ≠ b) :
    nodeTweak 3 0 0 a ≠ nodeTweak 3 0 0 b := by
  intro he
  have := congrArg tweakLow he
  rw [nodeTweak_top_low, nodeTweak_top_low, topNodeWord_eq ha1 ha2, topNodeWord_eq hb1 hb2] at this
  exact hne this

section RootChildren
variable (secret : BitVec 256) (target : HashInput) (heap : Nat) (ht : TopQ heap target) (h23 : heap = 2 ∨ heap = 3)
include ht h23

theorem tav_privatePair (tag lay tree position index : Nat) :
    Avoids secret target (privatePair tag lay tree position index) := by
  unfold privatePair
  apply avoids_bind
  · apply avoids_privateHash_of_ne
    obtain ⟨l, t, p, i, hq⟩ := hasTag_privatePair secret tag lay tree position index
    refine topQ_ne hq (ne_top_of_marker (by omega) (by omega) ?_) ht
    rw [header_marker]; omega
  · intro _; exact avoids_pure _ _ _

theorem tav_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids secret target (chain lay tree leaf i start count value) := by
  unfold chain
  apply avoids_foldlM
  intro value step
  apply avoids_shortHash_of_ne
  have hh : queryHeader (pad64 (chainInput lay tree leaf i step value)) =
      bytesLE 16 (chainHeader lay tree leaf i step) := by
    simpa only [chainInput, List.append_assoc] using
      queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16])
        (chainHeader lay tree leaf i step)
  refine topQ_ne hh (ne_top_of_marker (by omega) (by omega) ?_) ht
  have := chainHeader_tweakMarker lay tree leaf i step
  omega

/-- Witness stack: top chains (G `value | header | 0 | 0`, F `chainInput`) carry the chain header in bytes `16..32`. -/
theorem tav_topChain (leaf i start count : Nat) (value : Digest) :
    Avoids secret target (topChain leaf i start count value) := by
  unfold topChain
  apply avoids_foldlM
  intro value step
  apply avoids_shortHash_of_ne
  have hh : queryHeader (pad64 (topChainInput leaf i step value)) = bytesLE 16 (chainHeader 0 0 leaf i step) := by
    unfold topChainInput
    split
    · simpa only [List.append_assoc] using
        queryHeader_padded (bytesLE 16 value) (zero16 ++ zero16) (bytesLE_length ..) (chainHeader 0 0 leaf i step)
    · simpa only [chainInput, List.append_assoc] using
        queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16]) (chainHeader 0 0 leaf i step)
  refine topQ_ne hh (ne_top_of_marker (by omega) (by omega) ?_) ht
  have := chainHeader_tweakMarker 0 0 leaf i step
  omega

theorem tav_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Avoids secret target (leafHash lay tree leaf ends) := by
  unfold leafHash
  apply avoids_shortHash_of_ne
  refine topQ_ne (queryHeader_leafInput ..) (ne_top_of_marker (by omega) (by omega) ?_) ht
  rw [leafTweak_marker]; omega

theorem tav_topNodeHashN (heap' n : Nat) (left right : Digest) (h1 : 1 ≤ heap') (h2 : heap' < 4096)
    (hne : heap' ≠ heap) : Avoids secret target (topNodeHashN heap' n left right) := by
  unfold topNodeHashN
  apply avoids_shortHash_of_ne
  have hq := topQ_topTrial heap' n left right
  unfold TopQ topTrial at hq
  exact topQ_ne hq (top_tweak_ne h1 h2 (by omega) (by omega) hne) ht

theorem tav_topNonceSearch (h heap' : Nat) (left right : Digest) (h1 : 1 ≤ heap') (h2 : heap' < 4096)
    (hne : heap' ≠ heap) : ∀ fuel n, Avoids secret target (topNonceSearch h heap' left right fuel n) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n; unfold topNonceSearch
      exact avoids_bind (tav_topNodeHashN secret target heap ht h23 heap' n left right h1 h2 hne)
        fun _ => avoids_pure _ _ _
  | succ fuel ih =>
      intro n; unfold topNonceSearch
      refine avoids_bind (tav_topNodeHashN secret target heap ht h23 heap' n left right h1 h2 hne) fun v => ?_
      split
      · exact avoids_pure _ _ _
      · exact ih (n + 1)

theorem tav_topNodeAt (h heap' : Nat) (left right : Digest) (h1 : 1 ≤ heap') (h2 : heap' < 4096)
    (hne : heap' ≠ heap) : Avoids secret target (topNodeAt h heap' left right) := by
  unfold topNodeAt
  exact tav_topNonceSearch secret target heap ht h23 h heap' left right h1 h2 hne _ 0

theorem tav_nodeHash_root (left right : Digest) : Avoids secret target (nodeHash 3 0 0 1 left right) := by
  unfold nodeHash
  apply avoids_shortHash_of_ne
  have hq : queryHeader (pad64 (bytesLE 16 left ++ bytesLE 16 (nodeTweak 3 0 0 1) ++ zero16 ++ bytesLE 16 right)) =
      bytesLE 16 (nodeTweak 3 0 0 1) := by
    simpa only [List.append_assoc] using
      queryHeader_padded (bytesLE 16 left) (zero16 ++ bytesLE 16 right) (bytesLE_length ..) (nodeTweak 3 0 0 1)
  exact topQ_ne hq (top_tweak_ne (by omega) (by omega) (by omega) (by omega) (by omega)) ht

end RootChildren

end ClaudeWCT.W9.T3.TopMoment
