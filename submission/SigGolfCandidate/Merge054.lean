import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import SigGolfCandidate.Merge001
import SigGolfCandidate.Merge016
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge043
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge048
import SigGolfCandidate.Merge049
import SigGolfCandidate.Merge050
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge053

-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_KeygenMomentV6 ====
section

/-! # img-v6 keygen moment (r3-lean-topbytes)

`E[2^(countBlocks keygen / 2^20)] ≤ 2`: every top node (heights 1..11) is a nonce search whose trials are fresh oracle
queries, so `V` of the node is at most `m_h · (rest)` with `z·(2^-h + (1 - 2^-h)·m_h) ≤ m_h`, `z ≤ m_h`
(certificate `ClaudeWCT.Numerics.V6Budgets.keygen_step`, r3k); the deterministic remainder costs 1,003,010
compressions and `z^1003010 · Π_h m_h^(2^(12-h)) ≤ 2` (`keygen_moment`).

Part A: freshness of the trials of ANY top node `2 ≤ heap < 4096` against the leaf loop (private pairs of tag 0,
chains, leaf hashes) and against the other nodes. -/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness (Avoids avoids_pure avoids_bind avoids_foldlM avoids_shortHash_of_ne
  avoids_privateHash_of_ne hasTag_privatePair preserves)
open SigGolfCandidate.T3.QuerySpace (queryHeader queryHeader_padded queryHeader_leafInput)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem tweakLow_top {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096) : tweakLow (nodeTweak 3 0 0 heap) = heap := by
  rw [nodeTweak_top_low, topNodeWord_eq h1 h2]

theorem ne_top_of_low {hdr : BitVec 128} {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096)
    (hl : 4096 ≤ tweakLow hdr) : hdr ≠ nodeTweak 3 0 0 heap := by
  rintro rfl
  rw [tweakLow_top h1 h2] at hl
  omega

theorem tweakTag_top {heap : Nat} (h1 : 1 ≤ heap) (h2 : heap < 4096) :
    tweakTag (nodeTweak 3 0 0 heap) = heap / 256 % 256 := by
  have hl := tweakLow_top h1 h2
  unfold tweakLow at hl
  unfold tweakTag
  have : (nodeTweak 3 0 0 heap).toNat / 256 % 256 = (nodeTweak 3 0 0 heap).toNat % 2 ^ 64 / 256 % 256 := by
    rw [show (2 : Nat) ^ 64 = 256 * 2 ^ 56 by norm_num, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (by norm_num : 256 ∣ 2 ^ 56)]
  rw [this, hl]

theorem header0_ne_top (lay tree position index : Nat) {heap : Nat} (h1 : 2 ≤ heap) (h2 : heap < 4096) :
    header 0 lay tree position index ≠ nodeTweak 3 0 0 heap := by
  intro he
  have hm := congrArg tweakMarker he
  have ht := congrArg tweakTag he
  rw [header_marker, tweakMarker_top (by omega) h2] at hm
  rw [tweakTag_top (by omega) h2] at ht
  have : tweakTag (header 0 lay tree position index) = 0 := by
    simp [header_tag]
  rw [this] at ht
  omega

theorem chainHeader_low_ge (lay : Layer) (tree leaf i step : Nat) :
    4096 ≤ tweakLow (chainHeader lay tree leaf i step) := by
  have hb := (chainHeaderLow_band lay tree leaf i step).1
  have hf := chainHeaderFlaggedLow_toNat lay tree leaf i step
  have hl : tweakLow (chainHeader lay tree leaf i step) = (chainHeaderFlaggedLow lay tree leaf i step).toNat := by
    unfold tweakLow
    rw [← chainHeader_low, BitVec.extractLsb'_toNat]
    simp
  rw [hl, hf]
  have : (4096 : Nat) ≤ 193 * 2 ^ 56 := by norm_num
  omega

theorem leafTweak_low_ge (lay : Layer) (tree leaf : Nat) : 4096 ≤ tweakLow (leafTweak lay tree leaf) := by
  unfold leafTweak tweakLow
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [Nat.mod_eq_of_lt (BitVec.isLt _), hyperWord_toNat]
  have : (4096 : Nat) ≤ 193 * 2 ^ 56 := by norm_num
  omega

theorem topTrial_ne_heap {a b : Nat} (n m : Nat) (l r l' r' : Digest) (ha1 : 1 ≤ a) (ha2 : a < 4096)
    (hb1 : 1 ≤ b) (hb2 : b < 4096) (hne : a ≠ b) : topTrial a n l r ≠ topTrial b m l' r' := by
  intro he
  have h2 := topQ_topTrial a n l r
  have h3 := topQ_topTrial b m l' r'
  unfold TopQ at h2 h3
  rw [he] at h2
  exact top_tweak_ne ha1 ha2 hb1 hb2 hne (bytesLE_injective (h2.symm.trans h3))

section AnyHeap
variable (secret : BitVec 256) (target : HashInput) (heap : Nat) (ht : TopQ heap target)
  (h2 : 2 ≤ heap) (h4 : heap < 4096)
include ht h2 h4

theorem gav_privatePair0 (lay tree position index : Nat) :
    Avoids secret target (privatePair 0 lay tree position index) := by
  unfold privatePair
  apply avoids_bind
  · apply avoids_privateHash_of_ne
    obtain ⟨l, t, p, i, hq⟩ := hasTag_privatePair secret 0 lay tree position index
    exact topQ_ne hq (header0_ne_top l t p i h2 h4) ht
  · intro _; exact avoids_pure _ _ _

theorem gav_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
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
  exact topQ_ne hh (ne_top_of_low (by omega) h4 (chainHeader_low_ge ..)) ht

/-- Witness stack: top chains (G `value | header | 0 | 0`, F `chainInput`) carry the chain header in bytes `16..32`. -/
theorem gav_topChain (leaf i start count : Nat) (value : Digest) :
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
  exact topQ_ne hh (ne_top_of_low (by omega) h4 (chainHeader_low_ge ..)) ht

theorem gav_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Avoids secret target (leafHash lay tree leaf ends) := by
  unfold leafHash
  apply avoids_shortHash_of_ne
  exact topQ_ne (queryHeader_leafInput ..) (ne_top_of_low (by omega) h4 (leafTweak_low_ge ..)) ht

theorem gav_topPairsFrom (first start : Nat) (init : List Digest) :
    Avoids secret target (topPairsFrom first start init) := by
  unfold topPairsFrom topSeedPair
  exact avoids_foldlM _ _ _ _ (fun acc j => avoids_bind (gav_privatePair0 secret target heap ht h2 h4 0 0 _ 0)
    (fun _ => avoids_pure _ _ _)) _

theorem gav_buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    Avoids secret target (buildLeafTopC leaf coefs digits signatureOnly) := by
  unfold buildLeafTopC
  apply avoids_bind
  · apply avoids_foldlM
    intro state i
    refine avoids_bind (gav_topChain secret target heap ht h2 h4 _ _ _ _ _) (fun value => ?_)
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (gav_topChain secret target heap ht h2 h4 _ _ _ _ _) (fun _ => avoids_pure _ _ _)
  · intro state
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (gav_leafHash secret target heap ht h2 h4 _ _ _ _) (fun _ => avoids_pure _ _ _)

theorem gav_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) :
    Avoids secret target (topTreeStep st leaf) := by
  unfold topTreeStep topFamilyCoefs
  refine avoids_bind ?_ (fun cc => avoids_bind (gav_buildLeafTopC secret target heap ht h2 h4 _ _ _ _)
    (fun _ => avoids_pure _ _ _))
  split
  · unfold topCoefsK
    exact avoids_bind (gav_topPairsFrom secret target heap ht h2 h4 _ _ _) (fun _ => avoids_pure _ _ _)
  · exact avoids_pure _ _ _

end AnyHeap

theorem expectedValue_uniform_ite' (P : HashOutput → Prop) [DecidablePred P] (B b : ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => if P a then B else b) =
      Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] * B +
        (1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]) * b := by
  have hc := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) P
  rw [probFailure_uniformSample, tsub_zero] at hc
  have hn : Pr[fun a => ¬P a | ($ᵗ HashOutput : ProbComp HashOutput)] =
      1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hc ▸ le_add_right le_rfl)) (by
      rw [add_comm]; exact hc)
  have he : (fun a => if P a then B else b) =
      fun a => (if P a then 1 else 0) * B + (if ¬P a then 1 else 0) * b := by
    funext a; by_cases hp : P a <;> simp [hp]
  rw [he, expectedValue_add, expectedValue_mul_const, expectedValue_mul_const, expectedValue_ite_one,
    expectedValue_ite_one, hn]

/-- The trials of every node with heap in `S` are fresh. -/
def FreshS (S : Nat → Prop) (cache : RCache) : Prop :=
  ∀ heap, S heap → ∀ n l r, cache (topTrial heap n l r) = none

theorem FreshS.mono {S S' : Nat → Prop} {cache : RCache} (h : FreshS S cache) (hS : ∀ x, S' x → S x) :
    FreshS S' cache := fun heap hs => h heap (hS heap hs)

/-- The cache after the leaf loop: every node trial is fresh. -/
theorem leafLoop_fresh (secret : BitVec 256) (r : (List Digest × List Digest × Digest) × RCache)
    (hr : r ∈ support (roRun secret ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0)) ∅)) :
    FreshS (fun h => 2 ≤ h ∧ h < 4096) r.2 := by
  intro heap hh n l rr
  rw [preserves secret _ _ (avoids_foldlM _ _ _ _
    (fun st leaf => gav_topTreeStep secret _ heap (topQ_topTrial heap n l rr) hh.1 hh.2 st leaf) _) ∅ r hr]
  rfl

/-- **One node** (height `h ∈ 1..11`): `V ≤ m · B` from a cache where its trials are fresh. -/
theorem V_node {β : Type} (secret : BitVec 256) (z m B : ℝ≥0∞) (h heap : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11)
    (hh1 : 1 ≤ heap) (hh2 : heap < 4096) (left right : Digest) (next : Digest → M β) (S : Nat → Prop)
    (hstep : z * (((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ + (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) * m) ≤ m) (hzm : z ≤ m)
    (hS1 : ∀ x, S x → 1 ≤ x ∧ x < 4096)
    (hnext : ∀ v cache, FreshS (fun x => S x ∧ x ≠ heap) cache → V secret z (next v) cache ≤ B)
    (cache : RCache) (hfresh : FreshS S cache) (hheap : S heap) :
    V secret z ((Prod.snd <$> topNodeAt h heap left right) >>= next) cache ≤ m * B := by
  rw [bind_map_left]
  unfold topNodeAt
  have hcap : topNonceCap h - 1 < 2 ^ 64 := by
    unfold topNonceCap
    have : (2 : Nat) ^ topZeroBits h ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (topZeroBits_le h h11)
    have : (104 : Nat) * 2 ^ 8 < 2 ^ 64 := by norm_num
    omega
  refine V_topNonceSearch_bind secret z h heap left right _ (FreshS (fun x => S x ∧ x ≠ heap)) B (m * B)
    ?_ ?_ ?_ ?_ (topNonceCap h - 1) 0 (by omega) cache (hfresh.mono (fun x hx => hx.1))
    (fun k _ _ => hfresh heap hheap k left right)
  · intro σ hσ k ans x hx n l r
    have hx' := hS1 x hx.1
    exact (QueryCache.cacheQuery_of_ne (cache := σ) ans
      (topTrial_ne_heap n k l r left right hx'.1 hx'.2 hh1 hh2 hx.2)).trans (hσ x hx n l r)
  · intro σ hσ k ans
    apply hnext
    intro x hx n l r
    have hx' := hS1 x hx.1
    exact (QueryCache.cacheQuery_of_ne (cache := σ) ans
      (topTrial_ne_heap n k l r left right hx'.1 hx'.2 hh1 hh2 hx.2)).trans (hσ x hx n l r)
  · rw [expectedValue_uniform_ite' (fun a => topZeroOk h (topVal heap a) = true), prob_topAccept h1 h11]
    calc z * (((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ * B + (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) * (m * B))
        = z * (((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ + (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) * m) * B := by ring
      _ ≤ m * B := mul_le_mul' hstep le_rfl
  · exact mul_le_mul' hzm le_rfl

/-- **The nodes of one level** (indices `l`, heaps `base + i`): `V ≤ m^|l| · B`. -/
theorem V_nodes {β : Type} (secret : BitVec 256) (z m : ℝ≥0∞) (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11)
    (base : Nat) (nodes : List Digest)
    (hstep : z * (((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ + (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) * m) ≤ m) (hzm : z ≤ m) :
    ∀ (l : List Nat) (S : Nat → Prop) (next : List Digest → M β) (B : ℝ≥0∞),
      (∀ x, S x → 1 ≤ x ∧ x < 4096) → l.Nodup → (∀ i ∈ l, S (base + i)) →
      (∀ as cache, as.length = l.length → FreshS (fun x => S x ∧ ∀ i ∈ l, x ≠ base + i) cache →
        V secret z (next as) cache ≤ B) →
      ∀ cache, FreshS S cache →
        V secret z ((l.mapM fun i => Prod.snd <$> topNodeAt h (base + i) (nodes.getD (2 * i) 0)
          (nodes.getD (2 * i + 1) 0)) >>= next) cache ≤ m ^ l.length * B := by
  intro l
  induction l with
  | nil =>
      intro S next B _ _ _ hnext cache hfresh
      simp only [List.mapM_nil, pure_bind, List.length_nil, pow_zero, one_mul]
      exact hnext [] cache rfl (hfresh.mono (fun x hx => hx.1))
  | cons i l ih =>
      intro S next B hS1 hnd hin hnext cache hfresh
      rw [List.mapM_cons]
      simp only [bind_assoc, pure_bind]
      have hi := hin i (List.mem_cons_self ..)
      have hb := hS1 _ hi
      have hrest := ih (fun x => S x ∧ x ≠ base + i)
      refine le_trans (V_node secret z m (m ^ l.length * B) h (base + i) h1 h11 hb.1 hb.2 _ _ _ S hstep hzm hS1
        (fun v cache' hc => ?_) cache hfresh hi) (le_of_eq ?_)
      · refine hrest (fun as => next (v :: as)) B (fun x hx => hS1 x hx.1) (List.nodup_cons.mp hnd).2
          (fun j hj => ⟨hin j (List.mem_cons_of_mem _ hj), fun he => (List.nodup_cons.mp hnd).1 (by
            have : j = i := by omega
            exact this ▸ hj)⟩) (fun as c' hlen hc' => ?_) cache' hc
        apply hnext (v :: as) c' (by simp [hlen])
        exact hc'.mono (fun x hx => ⟨⟨hx.1, hx.2 i (List.mem_cons_self ..)⟩,
          fun j hj => hx.2 j (List.mem_cons_of_mem _ hj)⟩)
      · rw [List.length_cons, pow_succ]; ring

theorem buildTopLevel_lt12 (level : Nat) (hl : level ≠ 12) (nodes : List Digest) :
    buildTopLevel level nodes = (List.range (nodes.length / 2)).mapM fun i =>
      Prod.snd <$> topNodeAt level (2 ^ (12 - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0) := by
  unfold buildTopLevel
  simp only [hl, if_false]

theorem levelShape_append (a : Nat) (ha : 1 ≤ a) (ha12 : a ≤ 12) (levels : List (List Digest)) (as : List Digest)
    (h : LevelShape 12 (a - 1) levels) (has : as.length = 2 ^ (12 - a)) : LevelShape 12 a (levels ++ [as]) := by
  refine ⟨by simp [h.1]; omega, fun j hj => ?_⟩
  by_cases hold : j ≤ a - 1
  · rw [List.getD_append levels [as] [] j (by have := h.1; omega)]
    exact h.2 j hold
  · have he : j = a := by omega
    subst j
    rw [List.getD_append_right levels [as] [] a (by have := h.1; omega)]
    simp only [h.1, show a - (a - 1 + 1) = 0 by omega, List.getD_cons_zero]
    exact has

/-- The per-level factor `m_level ^ (nodes at the level)`. -/
noncomputable def mlev (m : Nat → ℝ≥0∞) (level : Nat) : ℝ≥0∞ := m level ^ (2 ^ (12 - level))

theorem pow_level_facts (a : Nat) (ha : 1 ≤ a) (ha11 : a ≤ 11) :
    2 ^ (12 - (a - 1)) / 2 = 2 ^ (12 - a) ∧ 2 ≤ 2 ^ (12 - a) ∧ 2 ^ (12 - a) + 2 ^ (12 - a) = 2 ^ (13 - a) ∧
      2 ^ (13 - a) ≤ 4096 ∧ 2 ^ (12 - (a - 1)) = 2 ^ (13 - a) := by
  interval_cases a <;> norm_num

/-- **Levels `a .. a+n-1`** (all ≤ 11). -/
theorem V_levels {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (m : Nat → ℝ≥0∞)
    (hstep : ∀ h, 1 ≤ h → h ≤ 11 →
      z * (((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ + (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) * m h) ≤ m h)
    (hzm : ∀ h, 1 ≤ h → h ≤ 11 → z ≤ m h) :
    ∀ n a, 1 ≤ a → a + n ≤ 12 → ∀ (levels : List (List Digest)) (next : List (List Digest) → M β) (B : ℝ≥0∞),
      LevelShape 12 (a - 1) levels →
      (∀ ls cache, LevelShape 12 (a - 1 + n) ls → FreshS (fun x => 2 ≤ x ∧ x < 2 ^ (13 - (a + n))) cache →
        V secret z (next ls) cache ≤ B) →
      ∀ cache, FreshS (fun x => 2 ≤ x ∧ x < 2 ^ (13 - a)) cache →
        V secret z ((List.range' a n).foldlM topStepL levels >>= next) cache ≤
          ((List.range' a n).map (mlev m)).prod * B := by
  intro n
  induction n with
  | zero =>
      intro a _ _ levels next B hsh hnext cache hf
      simp only [List.range'_zero, List.foldlM_nil, pure_bind, List.map_nil, List.prod_nil, one_mul]
      exact hnext levels cache (by simpa using hsh) (by simpa using hf)
  | succ n ih =>
      intro a ha han levels next B hsh hnext cache hf
      obtain ⟨p1, p2, p3, p4, p5⟩ := pow_level_facts a ha (by omega)
      have hlen : (levels.getD (a - 1) []).length = 2 ^ (13 - a) := by rw [← p5]; exact hsh.2 (a - 1) le_rfl
      rw [List.range'_succ, List.foldlM_cons, List.map_cons, List.prod_cons]
      unfold topStepL
      rw [buildTopLevel_lt12 a (by omega), hlen, show 2 ^ (13 - a) / 2 = 2 ^ (12 - a) by omega]
      simp only [bind_assoc, pure_bind]
      have hrest := ih (a + 1) (by omega) (by omega)
      refine le_trans (V_nodes secret z (m a) a ha (by omega) (2 ^ (12 - a)) (levels.getD (a - 1) [])
        (hstep a ha (by omega)) (hzm a ha (by omega)) (List.range (2 ^ (12 - a)))
        (fun x => 2 ≤ x ∧ x < 2 ^ (13 - a)) _ (((List.range' (a + 1) n).map (mlev m)).prod * B)
        (fun x hx => ⟨by omega, by omega⟩) (List.nodup_range) (fun i hi => by
          rw [List.mem_range] at hi; exact ⟨by omega, by omega⟩) (fun as c hl hc => ?_) cache hf) (le_of_eq ?_)
      · refine hrest (levels ++ [as]) next B (levelShape_append a ha (by omega) levels as hsh (by simpa using hl))
          (fun ls c' hs hc' => hnext ls c' (by rw [show a - 1 + (n + 1) = a + 1 - 1 + n by omega]; exact hs)
            (by simpa [show a + 1 + n = a + (n + 1) by omega] using hc')) c
          (hc.mono (fun x hx => ⟨⟨hx.1, by
            have : 2 ^ (13 - (a + 1)) = 2 ^ (12 - a) := by congr 1; omega
            omega⟩, fun i hi => by
            rw [List.mem_range] at hi
            have : 2 ^ (13 - (a + 1)) = 2 ^ (12 - a) := by congr 1; omega
            omega⟩))
      · simp only [List.length_range, mlev]; ring

theorem bound_keygenRest (levels : List (List Digest)) :
    CBound (fun _ => True) 4097 (SigGolfCandidate.Research.SharedExpansionV6.keygenRest levels) := by
  unfold SigGolfCandidate.Research.SharedExpansionV6.keygenRest SigGolfCandidate.Research.SharedExpansionV6.payloadTail
  simp only [bind_assoc]
  refine (Bound.mapM_list (P := GoodQuery) (List.range' 0 12) _ (fun level => 2^(11-level))
    (fun level _ => bound_maskedLevel (levels.getD level []) level)).bind' (l := 2)
    (fun _ _ => ?_) (by decide +kernel)
  simp only [pure_bind]
  exact (bound_privateMac _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by omega)

/-- The root level: one node hash. -/
theorem V_root {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) (ls : List (List Digest))
    (hsh : LevelShape 12 11 ls) (next : List (List Digest) → M β) (B : ℝ≥0∞)
    (hnext : ∀ ls' cache, V secret z (next ls') cache ≤ B) (cache : RCache) :
    V secret z (topStepL ls 12 >>= next) cache ≤ z * B := by
  have hlen : (ls.getD 11 []).length = 2 := by simpa using hsh.2 11 le_rfl
  have hb : CBound (fun _ => True) 1 (topStepL ls 12) := by
    unfold topStepL
    refine (bound_buildTopLevel 12 (ls.getD (12 - 1) [])).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) ?_
    rw [show (12 : Nat) - 1 = 11 from rfl, hlen]
    simp [topLevelCost]
  refine le_trans (V_bind_le secret z _ next cache B (fun r _ => hnext _ _)) ?_
  have := V_of_bound hb secret z hz cache
  rw [pow_one] at this
  exact mul_le_mul' this le_rfl

theorem buildTopLevels_split12 (leaves : List Digest) :
    buildTopLevels leaves = ((List.range' 1 11).foldlM topStepL [leaves] >>= fun ls => topStepL ls 12) := by
  unfold buildTopLevels
  rw [show List.range' 1 12 = List.range' 1 11 ++ [12] by decide, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

/-- **The keygen `V`-bound** (all node searches, fresh): `V keygen ≤ z^998912 · (Π_ℓ mlev ℓ · (z · z^4097))`. -/
theorem V_keygen (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) (m : Nat → ℝ≥0∞)
    (hstep : ∀ h, 1 ≤ h → h ≤ 11 →
      z * (((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ + (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) * m h) ≤ m h)
    (hzm : ∀ h, 1 ≤ h → h ≤ 11 → z ≤ m h) :
    V secret z keygen ∅ ≤ z ^ topLeavesCost * (((List.range' 1 11).map (mlev m)).prod * (z * z ^ 4097)) := by
  rw [SigGolfCandidate.Research.SharedExpansionV6.keygen_split]
  unfold buildTopTree
  simp only [bind_assoc]
  have hleaf : Bound GoodQuery (fun st : List Digest × List Digest × Digest => st.1.length = 2 ^ 12) topLeavesCost
      ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0)) :=
    ((Bound.foldlM_range 4096 _ (fun i (st : List Digest × List Digest × Digest) => st.1.length = i)
      topLeafCost ([], [], 0) rfl (fun leaf _ st hst => bound_topTreeStep st leaf hst)).mono
        (fun _ h => h) (fun st h => by simpa using h)).mono_k (by rw [topLeaves_sum])
  refine le_trans (V_bind_le secret z _ _ ∅ _ (fun r hr => ?_)) (mul_le_mul' (V_of_bound hleaf secret z hz ∅) le_rfl)
  have hlen := hleaf.post_of_roRun secret ∅ r hr
  have hf := leafLoop_fresh secret r hr
  rw [buildTopLevels_split12, bind_assoc]
  refine V_levels secret z m hstep hzm 11 1 (by omega) (by omega) [r.1.1] _ (z * z ^ 4097)
    ⟨rfl, fun j hj => by
      have : j = 0 := by omega
      subst j; simpa using hlen⟩ (fun ls c hs _ => ?_) r.2 (by simpa using hf)
  exact V_root secret z hz ls (by simpa using hs) _ _ (fun ls' c' => by
    have := V_of_bound (bound_keygenRest ls') secret z hz c'
    exact this) c

section Numeric
open ClaudeWCT.Numerics.V6Budgets
open ClaudeWCT.Numerics.CanonicalCompression (scale)

/-- `z = 2^(1/2^20)` as a real. -/
noncomputable def zR : ℝ := (2 : ℝ) ^ (1 / ((2 ^ 20 : ℕ) : ℝ))
/-- `m_b` (r3k certificate, #938's `keygenM (b-1)` for `p = 2^-b`), `b = 1..11`. -/
noncomputable def mR (i : Fin 11) : ℝ := (keygenM i : ℝ) / 2 ^ 128
/-- Campaign T51: the per-height certificate value: `z` for a height without zero bits (`b_h = 0`), else
`m_{b_h}`. -/
noncomputable def mT (h : Nat) : ℝ :=
  if topZeroBits h = 0 then zR else mR ⟨(topZeroBits h - 1) % 11, Nat.mod_lt _ (by decide)⟩
noncomputable def mE (h : Nat) : ℝ≥0∞ := if 1 ≤ h ∧ h ≤ 11 then ENNReal.ofReal (mT h) else 1

theorem zR_nonneg : 0 ≤ zR := by unfold zR; positivity
theorem zR_le : zR ≤ (keygenZNum : ℝ) / keygenZDen := keygen_z_le

theorem zE_eq : ((2 : ℝ≥0∞) ^ ((1 : ℝ) / 1048576)) = ENNReal.ofReal zR := by
  unfold zR
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  norm_num

theorem inv_two_pow_eq (h : Nat) : ((2 : ℝ≥0∞) ^ h)⁻¹ = ENNReal.ofReal (1 / 2 ^ h) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, one_div]

theorem mT_nonneg (h : Nat) : 0 ≤ mT h := by
  unfold mT mR; split_ifs
  · exact zR_nonneg
  · positivity

theorem mE_step (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    ENNReal.ofReal zR * (((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ + (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) * mE h) ≤ mE h ∧
      ENNReal.ofReal zR ≤ mE h := by
  have hm : mE h = ENNReal.ofReal (mT h) := by unfold mE; rw [if_pos ⟨h1, h11⟩]
  rw [hm]
  have hb8 := topZeroBits_le h h11
  by_cases hb : topZeroBits h = 0
  · have ht : mT h = zR := by unfold mT; rw [if_pos hb]
    rw [ht, hb]
    simp
  · have hb1 : 1 ≤ topZeroBits h := by omega
    have hk := keygen_step ⟨topZeroBits h - 1, by omega⟩ zR zR_nonneg zR_le
    simp only [show topZeroBits h - 1 + 1 = topZeroBits h by omega] at hk
    have ht : mT h = mR ⟨topZeroBits h - 1, by omega⟩ := by
      unfold mT; rw [if_neg hb]; congr 2; exact Nat.mod_eq_of_lt (by omega)
    have hq0 : (0 : ℝ) ≤ 1 / 2 ^ topZeroBits h := by positivity
    have hq1 : (1 : ℝ) / 2 ^ topZeroBits h ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have hm0 : 0 ≤ mR ⟨topZeroBits h - 1, by omega⟩ := by unfold mR; positivity
    rw [ht, inv_two_pow_eq]
    refine ⟨?_, ENNReal.ofReal_le_ofReal hk.2⟩
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add hq0 (by nlinarith), ← ENNReal.ofReal_mul zR_nonneg]
    exact ENNReal.ofReal_le_ofReal hk.1

theorem levels_prod (m : Nat → ℝ≥0∞) :
    ((List.range' 1 11).map (mlev m)).prod = ∏ i : Fin 11, m (i.val + 1) ^ (2 ^ (11 - i.val)) := by
  simp [List.range'_succ, mlev, Fin.prod_univ_succ, mul_assoc]

/-! Campaign T51 keygen certificate (KEYGEN-T51 section 4): heights 1, 2 (`b = 0`) cost `z` per node, heights
3..11 use #938's `keygenM (b_h - 1)`; fixed work `topLeavesCost + 4098 = 1,039,874`. -/
/-- The integer certificate entry of height `i + 1`. -/
def entryT51 (i : Fin 11) : Nat :=
  if topZeroBits (i.val + 1) = 0 then keygenZFix else keygenM ⟨(topZeroBits (i.val + 1) - 1) % 11, Nat.mod_lt _ (by decide)⟩
def keygenListT51 : List (Nat × Nat) :=
  (keygenZFix, 1039874) :: List.ofFn fun i : Fin 11 => (entryT51 i, 2 ^ (11 - i.val))

theorem keygenT51_list_checked : prodUp keygenListT51 * 100000 < 199934 * scale := by decide +kernel

theorem keygenListT51_prod :
    (keygenListT51.map fun e => ((e.1:ℝ)/scale)^e.2).prod =
      ((keygenZFix:ℝ)/scale)^1039874 * ∏ i : Fin 11, ((entryT51 i:ℝ)/scale)^(2^(11-i.val)) := by
  rw [keygenListT51, List.map_cons, List.prod_cons, List.map_ofFn, List.prod_ofFn]
  rfl

theorem mT_le_entry (i : Fin 11) (hzf : zR ≤ (keygenZFix:ℝ)/scale) :
    mT (i.val + 1) ≤ (entryT51 i:ℝ)/scale := by
  unfold mT entryT51 mR
  have hs : (scale:ℝ) = 2^128 := by norm_num [scale]
  split_ifs
  · exact hzf
  · rw [hs]

theorem keygen_moment_T51 (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ (keygenZNum:ℝ)/keygenZDen)
    (m : Fin 11 → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hm : ∀ i, m i ≤ (entryT51 i:ℝ)/scale) :
    z^1039874 * ∏ i : Fin 11, (m i)^(2^(11-i.val)) ≤ 2 := by
  have hzf := hz.trans keygenZ_fix
  have hprod := prodUp_ratio_ge keygenListT51
  rw [keygenListT51_prod] at hprod
  have hnum : (prodUp keygenListT51:ℝ)/scale < 199934/100000 := by
    have h := keygenT51_list_checked
    have h' : (prodUp keygenListT51:ℝ)*100000 < 199934*(scale:ℝ) := by exact_mod_cast h
    have hs0 : (0:ℝ) < scale := by norm_num [scale]
    generalize (prodUp keygenListT51:ℝ) = P at h' ⊢
    generalize (scale:ℝ) = S at h' hs0 ⊢
    rw [div_lt_iff₀ hs0]; linarith
  have hstep : z^1039874 * ∏ i : Fin 11, (m i)^(2^(11-i.val)) ≤
      ((keygenZFix:ℝ)/scale)^1039874 * ∏ i : Fin 11, ((entryT51 i:ℝ)/scale)^(2^(11-i.val)) := by
    apply mul_le_mul (pow_le_pow_left₀ hz0 hzf _) _ (Finset.prod_nonneg fun i _ => pow_nonneg (hm0 i) _)
      (by positivity)
    exact Finset.prod_le_prod (fun i _ => pow_nonneg (hm0 i) _) (fun i _ => pow_le_pow_left₀ (hm0 i) (hm i) _)
  linarith

/-- **Campaign T51 keygen moment**: `E[2^(countBlocks keygen / 2^20)] ≤ 2` (zero bits `b_h = 0,0,1,1,2..8`). -/
theorem keygen_moment_v6 (secret : BitVec 256) :
    expectedValue (roRun secret (countBlocks keygen) ∅)
      (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2 := by
  have hz1 : 1 ≤ ENNReal.ofReal zR := by
    rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
    unfold zR; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hV := V_keygen secret (ENNReal.ofReal zR) hz1 mE (fun h h1 h11 => (mE_step h h1 h11).1)
    (fun h h1 h11 => (mE_step h h1 h11).2)
  have hlhs : expectedValue (roRun secret (countBlocks keygen) ∅)
      (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) = V secret (ENNReal.ofReal zR) keygen ∅ := by
    unfold V
    congr 1
    funext r
    rw [← zE_eq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  rw [hlhs]
  refine hV.trans ?_
  rw [levels_prod, show topLeavesCost = 1035776 from rfl]
  have hfin : ∀ i : Fin 11, mE (i.val + 1) = ENNReal.ofReal (mT (i.val + 1)) := by
    intro i; unfold mE; rw [if_pos ⟨by omega, by omega⟩]
  simp only [hfin]
  have hzf := zR_le.trans keygenZ_fix
  have hnum := keygen_moment_T51 zR zR_nonneg zR_le (fun i => mT (i.val + 1)) (fun i => mT_nonneg _)
    (fun i => mT_le_entry i hzf)
  have hm0 : ∀ i : Fin 11, 0 ≤ mT (i.val + 1) ^ (2 ^ (11 - i.val)) := fun i => pow_nonneg (mT_nonneg _) _
  have heq : ENNReal.ofReal zR ^ 1035776 * ((∏ i : Fin 11, ENNReal.ofReal (mT (i.val + 1)) ^ (2 ^ (11 - i.val))) *
      (ENNReal.ofReal zR * ENNReal.ofReal zR ^ 4097)) =
      ENNReal.ofReal (zR ^ 1039874 * ∏ i : Fin 11, (mT (i.val + 1)) ^ (2 ^ (11 - i.val))) := by
    rw [ENNReal.ofReal_mul (pow_nonneg zR_nonneg _), ENNReal.ofReal_prod_of_nonneg (fun i _ => hm0 i),
      ENNReal.ofReal_pow zR_nonneg]
    simp only [ENNReal.ofReal_pow (mT_nonneg _)]
    ring
  rw [heq]
  calc ENNReal.ofReal (zR ^ 1039874 * ∏ i : Fin 11, (mT (i.val + 1)) ^ (2 ^ (11 - i.val))) ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal hnum
    _ = 2 := ENNReal.ofReal_ofNat 2

end Numeric

end ClaudeWCT.W9.T3.TopMoment
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopCapBad ====
section

/-! # img-v6 top-node cap exhaustion (r3-lean-topbytes)

The 5,239-byte codec drops the zero-test bits of the top path nodes, so an honest signature only survives the codec
when every top node on its path passed its zero test. A node search fails only if all `104·2^h` trials miss, so

`Pr[some keygen top node (heights 1..11) fails its zero test] ≤ Σ_h 2^(12-h)·(1 - 2^-h)^(104·2^h) ≤ 2^-135`

(exact value 2^-143.27; the bound uses `(1 - 2^-h)^(2^h) ≤ 3/8`).

* `Ev_topNonceSearch_fuel`: the value-weighted nonce-search bound with a fuel-indexed bound `b k`.
* `E_node`, `E_nodes`, `E_levels`: additive versions of `V_node`/`V_nodes`/`V_levels` (`KeygenMomentV6`).
* `Ev_buildTopTree_bad`: `E[1_{¬TopLevelsOK}]` over `buildTopTree` from the empty cache is at most `2^-135`. -/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Every built top node (heights 1..11) passes its zero test (= `SharedForest.TopTreeOK` on `builtTree`). -/
def TopLevelsOK (levels : List (List Digest)) : Prop :=
  ∀ j : Nat, 1 ≤ j → j ≤ 11 → ∀ i, i < 2 ^ (12 - j) →
    topZeroOk j (SigGolfCandidate.T3.Correctness.treeValue levels j i) = true

/-- The nodes of levels `1..k` pass their zero tests. -/
def OKUpTo (k : Nat) (levels : List (List Digest)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → ∀ v ∈ levels.getD j [], topZeroOk j v = true

/-- Probability that one node search at height `h` exhausts its cap (T51: acceptance `2^-b_h`, `b_h = topZeroBits h`;
`b_h = 0` never fails). -/
noncomputable def capFail (h : Nat) : ℝ≥0∞ := (1 - ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹) ^ topNonceCap h

/-- Per-level contribution. -/
noncomputable def elev (level : Nat) : ℝ≥0∞ := ((2 ^ (12 - level) : ℕ) : ℝ≥0∞) * capFail level

theorem topZeroOk_zero (j : Nat) : topZeroOk j 0 = true := by
  unfold topZeroOk; split <;> simp

/-- Value-weighted nonce-search bound, fuel-indexed. -/
theorem Ev_topNonceSearch_fuel {β : Type} (secret : BitVec 256) (h heap : Nat) (left right : Digest)
    (next : Nat × Digest → M β) (F : β × RCache → ℝ≥0∞) (G : RCache → Prop) (w : Digest → ℝ≥0∞) (b : Nat → ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (topTrial heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      Ev secret (next (k, topVal heap answer)) (cache.cacheQuery (topTrial heap k left right) answer) F ≤
        w (topVal heap answer))
    (hstep : ∀ k, expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if topZeroOk h (topVal heap answer) then w (topVal heap answer) else b k) ≤ b (k + 1))
    (htail : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer => w (topVal heap answer)) ≤ b 0) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (topTrial heap k left right) = none) →
      Ev secret (topNonceSearch h heap left right fuel n >>= next) cache F ≤ b fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_zero_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      exact (expectedValue_mono _ fun answer => hnext cache hg n answer).trans htail
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_succ_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      refine le_trans (expectedValue_mono _ fun answer => ?_) (hstep fuel)
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : topTrial heap k left right ≠ topTrial heap n left right := by
          intro he
          have := topTrial_injective heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))

theorem Ev_le_one {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache) (F : α × RCache → ℝ≥0∞)
    (hF : ∀ r, F r ≤ 1) : Ev secret program cache F ≤ 1 :=
  Ev_le_of_support secret program cache (fun r _ => hF r)

theorem capFail_step (p B : ℝ≥0∞) (hp : p ≤ 1) (k : Nat) :
    p * B + (1 - p) * (B + (1 - p) ^ (k + 1)) ≤ B + (1 - p) ^ (k + 1 + 1) := by
  rw [mul_add, ← add_assoc, ← add_mul, add_tsub_cancel_of_le hp, one_mul, ← pow_succ']

theorem capFail_tail (p B : ℝ≥0∞) (hp : p ≤ 1) : p * B + (1 - p) * 1 ≤ B + (1 - p) ^ (0 + 1) := by
  rw [mul_one, zero_add, pow_one]
  exact add_le_add (mul_le_of_le_one_left (by positivity) hp) le_rfl

/-- **One node**: if every continuation after a node passing its zero test is bounded by `B` (and `F ≤ 1`), the
node search plus continuation is bounded by `B + capFail h`. -/
theorem E_node {β : Type} (secret : BitVec 256) (h heap : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11)
    (hh1 : 1 ≤ heap) (hh2 : heap < 4096) (left right : Digest) (next : Digest → M β) (F : β × RCache → ℝ≥0∞)
    (hF : ∀ r, F r ≤ 1) (S : Nat → Prop) (B : ℝ≥0∞)
    (hS1 : ∀ x, S x → 1 ≤ x ∧ x < 4096)
    (hnext : ∀ v cache, topZeroOk h v = true → FreshS (fun x => S x ∧ x ≠ heap) cache →
      Ev secret (next v) cache F ≤ B)
    (cache : RCache) (hfresh : FreshS S cache) (hheap : S heap) :
    Ev secret ((Prod.snd <$> topNodeAt h heap left right) >>= next) cache F ≤ B + capFail h := by
  rw [bind_map_left]
  unfold topNodeAt
  have hcap : topNonceCap h - 1 < 2 ^ 64 := by
    unfold topNonceCap
    have : (2 : Nat) ^ topZeroBits h ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (topZeroBits_le h h11)
    have : (104 : Nat) * 2 ^ 8 < 2 ^ 64 := by norm_num
    omega
  have hcap1 : topNonceCap h - 1 + 1 = topNonceCap h := by
    unfold topNonceCap; have : 0 < 2 ^ topZeroBits h := by positivity
    omega
  set p : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ topZeroBits h)⁻¹ with hpdef
  have hp1 : p ≤ 1 := by
    rw [hpdef, ← prob_topAccept h1 h11 heap]; exact probEvent_le_one
  have hres := Ev_topNonceSearch_fuel secret h heap left right (fun x => next x.2) F
    (FreshS (fun x => S x ∧ x ≠ heap)) (fun v => if topZeroOk h v then B else 1)
    (fun k => B + (1 - p) ^ (k + 1)) ?_ ?_ ?_ ?_ (topNonceCap h - 1) 0 (by omega) cache
    (hfresh.mono (fun x hx => hx.1)) (fun k _ _ => hfresh heap hheap k left right)
  · refine hres.trans (le_of_eq ?_)
    unfold capFail
    rw [hcap1]
  · intro σ hσ k ans x hx n l r
    have hx' := hS1 x hx.1
    exact (QueryCache.cacheQuery_of_ne (cache := σ) ans
      (topTrial_ne_heap n k l r left right hx'.1 hx'.2 hh1 hh2 hx.2)).trans (hσ x hx n l r)
  · intro σ hσ k ans
    dsimp only
    split
    · rename_i hok
      apply hnext _ _ hok
      intro x hx n l r
      have hx' := hS1 x hx.1
      exact (QueryCache.cacheQuery_of_ne (cache := σ) ans
        (topTrial_ne_heap n k l r left right hx'.1 hx'.2 hh1 hh2 hx.2)).trans (hσ x hx n l r)
    · exact Ev_le_one secret _ _ F hF
  · intro k
    have he : (fun answer => if topZeroOk h (topVal heap answer) = true then
        (if topZeroOk h (topVal heap answer) = true then B else 1) else B + (1 - p) ^ (k + 1)) =
        fun a => if topZeroOk h (topVal heap a) = true then B else B + (1 - p) ^ (k + 1) := by
      funext a; split <;> simp_all
    rw [he, expectedValue_uniform_ite' (fun a => topZeroOk h (topVal heap a) = true), prob_topAccept h1 h11]
    exact capFail_step p B hp1 k
  · have he : (fun answer => if topZeroOk h (topVal heap answer) = true then B else (1 : ℝ≥0∞)) =
        fun a => if topZeroOk h (topVal heap a) = true then B else 1 := rfl
    rw [he, expectedValue_uniform_ite' (fun a => topZeroOk h (topVal heap a) = true), prob_topAccept h1 h11]
    exact capFail_tail p B hp1

/-- **The nodes of one level** (indices `l`, heaps `base + i`): `B + |l| · capFail h`. -/
theorem E_nodes {β : Type} (secret : BitVec 256) (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11)
    (base : Nat) (nodes : List Digest) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1) :
    ∀ (l : List Nat) (S : Nat → Prop) (next : List Digest → M β) (B : ℝ≥0∞),
      (∀ x, S x → 1 ≤ x ∧ x < 4096) → l.Nodup → (∀ i ∈ l, S (base + i)) →
      (∀ as cache, as.length = l.length → (∀ v ∈ as, topZeroOk h v = true) →
        FreshS (fun x => S x ∧ ∀ i ∈ l, x ≠ base + i) cache → Ev secret (next as) cache F ≤ B) →
      ∀ cache, FreshS S cache →
        Ev secret ((l.mapM fun i => Prod.snd <$> topNodeAt h (base + i) (nodes.getD (2 * i) 0)
          (nodes.getD (2 * i + 1) 0)) >>= next) cache F ≤ B + (l.length : ℝ≥0∞) * capFail h := by
  intro l
  induction l with
  | nil =>
      intro S next B _ _ _ hnext cache hfresh
      simp only [List.mapM_nil, pure_bind, List.length_nil, Nat.cast_zero, zero_mul, add_zero]
      exact hnext [] cache rfl (by simp) (hfresh.mono (fun x hx => hx.1))
  | cons i l ih =>
      intro S next B hS1 hnd hin hnext cache hfresh
      rw [List.mapM_cons]
      simp only [bind_assoc, pure_bind]
      have hi := hin i (List.mem_cons_self ..)
      have hb := hS1 _ hi
      have hrest := ih (fun x => S x ∧ x ≠ base + i)
      refine le_trans (E_node secret h (base + i) h1 h11 hb.1 hb.2 _ _ _ F hF S
        (B + (l.length : ℝ≥0∞) * capFail h) hS1 (fun v cache' hok hc => ?_) cache hfresh hi) (le_of_eq ?_)
      · refine hrest (fun as => next (v :: as)) B (fun x hx => hS1 x hx.1) (List.nodup_cons.mp hnd).2
          (fun j hj => ⟨hin j (List.mem_cons_of_mem _ hj), fun he => (List.nodup_cons.mp hnd).1 (by
            have : j = i := by omega
            exact this ▸ hj)⟩) (fun as c' hlen hoks hc' => ?_) cache' hc
        apply hnext (v :: as) c' (by simp [hlen])
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hok
          · exact hoks u hu
        · exact hc'.mono (fun x hx => ⟨⟨hx.1, hx.2 i (List.mem_cons_self ..)⟩,
            fun j hj => hx.2 j (List.mem_cons_of_mem _ hj)⟩)
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem okUpTo_append (a : Nat) (ha : 1 ≤ a) (levels : List (List Digest)) (as : List Digest)
    (hlen : levels.length = a) (h : OKUpTo (a - 1) levels) (has : ∀ v ∈ as, topZeroOk a v = true) :
    OKUpTo a (levels ++ [as]) := by
  intro j hj1 hja v hv
  by_cases hold : j ≤ a - 1
  · rw [List.getD_append levels [as] [] j (by omega)] at hv
    exact h j hj1 hold v hv
  · have he : j = a := by omega
    subst j
    rw [List.getD_append_right levels [as] [] a (by omega)] at hv
    simp only [hlen, Nat.sub_self, List.getD_cons_zero] at hv
    exact has v hv

/-- **Levels `a .. a+n-1`** (all ≤ 11): `B + Σ elev`. -/
theorem E_levels {β : Type} (secret : BitVec 256) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1) :
    ∀ n a, 1 ≤ a → a + n ≤ 12 → ∀ (levels : List (List Digest)) (next : List (List Digest) → M β) (B : ℝ≥0∞),
      LevelShape 12 (a - 1) levels → OKUpTo (a - 1) levels →
      (∀ ls cache, LevelShape 12 (a - 1 + n) ls → OKUpTo (a - 1 + n) ls →
        FreshS (fun x => 2 ≤ x ∧ x < 2 ^ (13 - (a + n))) cache → Ev secret (next ls) cache F ≤ B) →
      ∀ cache, FreshS (fun x => 2 ≤ x ∧ x < 2 ^ (13 - a)) cache →
        Ev secret ((List.range' a n).foldlM topStepL levels >>= next) cache F ≤
          B + ((List.range' a n).map elev).sum := by
  intro n
  induction n with
  | zero =>
      intro a _ _ levels next B hsh hok hnext cache hf
      simp only [List.range'_zero, List.foldlM_nil, pure_bind, List.map_nil, List.sum_nil, add_zero]
      exact hnext levels cache (by simpa using hsh) (by simpa using hok) (by simpa using hf)
  | succ n ih =>
      intro a ha han levels next B hsh hok hnext cache hf
      obtain ⟨p1, p2, p3, p4, p5⟩ := pow_level_facts a ha (by omega)
      have hlen : (levels.getD (a - 1) []).length = 2 ^ (13 - a) := by rw [← p5]; exact hsh.2 (a - 1) le_rfl
      have hlevels : levels.length = a := by have := hsh.1; omega
      rw [List.range'_succ, List.foldlM_cons, List.map_cons, List.sum_cons]
      unfold topStepL
      rw [buildTopLevel_lt12 a (by omega), hlen, show 2 ^ (13 - a) / 2 = 2 ^ (12 - a) by omega]
      simp only [bind_assoc, pure_bind]
      have hrest := ih (a + 1) (by omega) (by omega)
      refine le_trans (E_nodes secret a ha (by omega) (2 ^ (12 - a)) (levels.getD (a - 1) []) F hF
        (List.range (2 ^ (12 - a)))
        (fun x => 2 ≤ x ∧ x < 2 ^ (13 - a)) _ (B + ((List.range' (a + 1) n).map elev).sum)
        (fun x hx => ⟨by omega, by omega⟩) (List.nodup_range) (fun i hi => by
          rw [List.mem_range] at hi; exact ⟨by omega, by omega⟩) (fun as c hl hoks hc => ?_) cache hf)
        (le_of_eq ?_)
      · refine hrest (levels ++ [as]) next B (levelShape_append a ha (by omega) levels as hsh (by simpa using hl))
          (by simpa using okUpTo_append a ha levels as hlevels hok hoks)
          (fun ls c' hs hok' hc' => hnext ls c'
            (by rw [show a - 1 + (n + 1) = a + 1 - 1 + n by omega]; exact hs)
            (by rw [show a - 1 + (n + 1) = a + 1 - 1 + n by omega]; exact hok')
            (by simpa [show a + 1 + n = a + (n + 1) by omega] using hc')) c
          (hc.mono (fun x hx => ⟨⟨hx.1, by
            have : 2 ^ (13 - (a + 1)) = 2 ^ (12 - a) := by congr 1; omega
            omega⟩, fun i hi => by
            rw [List.mem_range] at hi
            have : 2 ^ (13 - (a + 1)) = 2 ^ (12 - a) := by congr 1; omega
            omega⟩))
      · simp only [List.length_range, elev]; ring

theorem getD_mem_or_zero (l : List Digest) (i : Nat) : l.getD i 0 ∈ l ∨ l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => right; rfl
  | some v => left; exact List.mem_of_getElem? h

theorem topLevelsOK_of_okUpTo (ls : List (List Digest)) (nodes : List Digest) (hlen : ls.length = 12)
    (hok : OKUpTo 11 ls) : TopLevelsOK (ls ++ [nodes]) := by
  intro j hj1 hj11 i _
  unfold SigGolfCandidate.T3.Correctness.treeValue
  rw [List.getD_append ls [nodes] [] j (by omega)]
  rcases getD_mem_or_zero (ls.getD j []) i with hm | hz
  · exact hok j hj1 hj11 _ hm
  · rw [hz]; exact topZeroOk_zero j

/-- **Cap exhaustion over the keygen top tree** (exact sum form). -/
theorem Ev_buildTopTree_bad_sum (secret : BitVec 256) :
    Ev secret buildTopTree ∅ (fun r => open Classical in if TopLevelsOK r.1 then 0 else 1) ≤
      ((List.range' 1 11).map elev).sum := by
  classical
  unfold buildTopTree
  have hleaf : Bound GoodQuery (fun st : List Digest × List Digest × Digest => st.1.length = 2 ^ 12) topLeavesCost
      ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0)) :=
    ((Bound.foldlM_range 4096 _ (fun i (st : List Digest × List Digest × Digest) => st.1.length = i)
      topLeafCost ([], [], 0) rfl (fun leaf _ st hst => bound_topTreeStep st leaf hst)).mono
        (fun _ h => h) (fun st h => by simpa using h)).mono_k (by rw [topLeaves_sum])
  rw [Ev_bind]
  refine Ev_le_of_support secret _ ∅ (fun r hr => ?_)
  have hlen := hleaf.post_of_roRun secret ∅ r hr
  have hf := leafLoop_fresh secret r hr
  rw [buildTopLevels_split12]
  have hF : ∀ r : List (List Digest) × RCache, (if TopLevelsOK r.1 then (0 : ℝ≥0∞) else 1) ≤ 1 := by
    intro r; split <;> simp
  have h := E_levels secret (fun r : List (List Digest) × RCache => if TopLevelsOK r.1 then (0 : ℝ≥0∞) else 1)
    hF 11 1 (by omega) (by omega) [r.1.1] (fun ls => topStepL ls 12) 0
    ⟨rfl, fun j hj => by
      have : j = 0 := by omega
      subst j; simpa using hlen⟩
    (fun j hj1 hj0 => absurd hj1 (by omega)) (fun ls c hs hok _ => ?_) r.2 (by simpa using hf)
  · simpa using h
  · unfold topStepL
    rw [Ev_bind]
    refine Ev_le_of_support secret _ c (fun q _ => ?_)
    rw [Ev_pure]
    have hl : ls.length = 12 := by have := hs.1; omega
    simp [topLevelsOK_of_okUpTo ls q.1 hl (by simpa using hok)]

/-! ### Numeric tail: `(1 - 2^-h)^(2^h) ≤ 3/8`, so the total is at most `4094 · (3/8)^104 ≤ 2^-135`. -/

theorem capBase_nat (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : 8 * (2 ^ h - 1) ^ (2 ^ h) ≤ 3 * (2 ^ h) ^ (2 ^ h) := by
  interval_cases h <;> decide +kernel

theorem capBase_real (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : (1 - 1 / 2 ^ h : ℝ) ^ (2 ^ h) ≤ 3 / 8 := by
  have hpos : (0 : ℝ) < 2 ^ h := by positivity
  have e : (1 - 1 / 2 ^ h : ℝ) = ((2 ^ h - 1 : ℕ) : ℝ) / (2 : ℝ) ^ h := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  rw [e, div_pow, div_le_iff₀ (by positivity)]
  have k : ((8 * (2 ^ h - 1) ^ (2 ^ h) : ℕ) : ℝ) ≤ ((3 * (2 ^ h) ^ (2 ^ h) : ℕ) : ℝ) := by
    exact_mod_cast capBase_nat h h1 h11
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at k
  linarith

theorem capFail_le (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : capFail h ≤ ENNReal.ofReal ((3 / 8 : ℝ) ^ 104) := by
  unfold capFail topNonceCap
  have hb8 := topZeroBits_le h h11
  generalize topZeroBits h = b at hb8 ⊢
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · simp
  · rw [inv_two_pow_eq]
    have hx : (0 : ℝ) ≤ 1 / 2 ^ b := by positivity
    have hx1 : 1 / 2 ^ b ≤ (1 : ℝ) := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hx, ← ENNReal.ofReal_pow (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 104, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (by linarith) _) (capBase_real b hb1 (by omega)) 104

theorem elev_sum_le : ((List.range' 1 11).map elev).sum ≤ ENNReal.ofReal (1 / 2 ^ 135) := by
  have h1 : ((List.range' 1 11).map elev).sum ≤
      ((List.range' 1 11).map fun l => ((2 ^ (12 - l) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((3 / 8 : ℝ) ^ 104)).sum := by
    apply List.sum_le_sum
    intro l hl
    rw [List.mem_range'_1] at hl
    exact mul_le_mul' le_rfl (capFail_le l (by omega) (by omega))
  refine h1.trans ?_
  rw [List.sum_map_mul_right]
  have h2 : ((List.range' 1 11).map fun l => ((2 ^ (12 - l) : ℕ) : ℝ≥0∞)).sum = ENNReal.ofReal 4094 := by
    simp [List.range', List.map, List.sum_cons]
    norm_num
  rw [h2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **Cap exhaustion over the keygen top tree**: `Pr[¬TopLevelsOK] ≤ 2^-135`. -/
theorem Ev_buildTopTree_bad (secret : BitVec 256) :
    Ev secret buildTopTree ∅ (fun r => open Classical in if TopLevelsOK r.1 then 0 else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 135) :=
  (Ev_buildTopTree_bad_sum secret).trans elev_sum_le

end ClaudeWCT.W9.T3.TopMoment
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpandMomentV6 ====
section

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
  calc (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((1900 + 425765 + 65535 : ℕ) : ℝ) / 1048576)
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

end SigGolfCandidate.Research.SharedExpansionV6
end
-- ==== merged from T3M_Images_Keygen ====
section

set_option maxRecDepth 16384
namespace SigGolfCandidate.T3M.Images
open SigGolfCandidate.Legacy
def keygenCode_0 : List (BitVec 32) := bv_list% 32 [0x293,0x8000e93,0x20f37,0xeb303,0x8eb383,0x6f3023,0x7f3423,0x9000e93,0x20f37,0x20f0f13,0xeb303,0x8eb383,0x6f3023,0x7f3423,0x20f37,0x20f3823,0x20f3c23,0x413,0x493,0x3300d13,0x3300d93,0xf93,0x20b37,0x460b0b13,0x50137,0x913,0x1337,0x2695263,0x21bb7,0xa00b8b93,0x6903b3,0x439393,0x238cb3,0x1bc000ef,0x190913,0xfddff06f,0xc00793,0xa93,0x300000ef,0x3b80006f,0x1013303,0x1813383,0x6f3023,0x7f3423,0x9c37,0x20c0c13,0x40000a13,0x200693,0x100313,0x86a0663,0x993,0x749dc63,0x1337,0xd0130313,0x2069f13,0x1e36333,0x2099393,0x20e37,0x6e3823,0x7e3c23,0x20537,0x4000593,0x20637,0x6060613,0x73,0x13a0e33,0x4e1e13,0x2e0e33,0xe3303,0x8e3383,0x20eb7,0x60e8e93,0xebe03,0x8ebe83,0x1c34333,0x1d3c3b3,0x6c3023,0x7c3423,0x10c0c13,0x198993,0xf8dff06f,0x1a5a13,0x168693,0xf75ff06f,0x8000e93,0x9f37,0xfe0f0f13,0xeb303,0x8eb383,0x6f3023,0x7f3423,0x9000e93,0x9f37,0xeb303,0x8eb383,0x6f3023,0x7f3423,0x9f37,0xfe0f0f13,0x20f3823,0x20f3c23,0x1337,0xe0130313,0x393,0x9e37,0xfe0e0e13,0x6e3823,0x7e3c23,0x9537,0xfe050513,0x85b7,0x4058593,0x9637,0x73,0x100293,0x513,0x73,0xa13,0x11a1e63,0x20eb7,0x1d0e8e93,0xeb303,0x8eb383,0x6bb023,0x7bb423,0x55a0463,0x7340006f,0x14383b3,0x2039313,0x1041f13,0x1e36333,0x10136313,0x20e37,0x1a0e0e13,0x6e3823,0xa90006f,0x1a050513,0x4000593,0x20637,0x1d060613,0x73,0x1a0a13,0xfa1ff06f,0x8067,0x8193,0x1091313,0x20136313,0x3041f13,0x1e36333,0xc100f13,0x38f1f13,0x1e36333,0x20e37,0x600e0e13,0x6e3823,0xe3c23,0x13,0x71c000ef,0xda9dc63,0x198693,0x788000ef,0x6c0006f,0x1041313,0x20e1f13,0x1e36333,0x136313,0x48393,0x2091f13,0x1e3e3b3,0x20e37,0x6e3823,0x7e3c23,0x20537,0x4000593,0x20637,0x4060613,0x73,0x19fe13,0x4e1e13,0x20eb7,0x40e8e93,0x1de0e33,0x20f37,0x1d0f0f13,0xe3303,0x8e3383,0x6f3023,0x7f3423,0x13b0e33,0xe4883,0x700a93,0x41463,0x7b00006f,0xf8463,0x88a93,0xec9ff0ef,0x20f9a63,0x1303f33,0x1e98e33,0x4e1e13,0x20eb7,0x600e8e93,0x1de0e33,0x20eb7,0x1d0e8e93,0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10b8b93,0x198993,0xf2dff06f,0x40f9263,0x1d0593,0x459593,0x3f58593,0xfc05f593,0x20537,0x60050513,0x20637,0x3c060613,0x197e93,0x73,0x4e9e93,0x41d60eb3,0x10eb303,0x18eb383,0x6cb023,0x7cb423,0x18067,0x7ac0006f,0xfff78313,0x6a1a33,0xa0a0663,0xa0c13,0x1a1313,0x86c5c63,0x5c1e13,0x2e0e33,0x20f37,0x200f0f13,0xe3303,0x8e3383,0x6f3023,0x7f3423,0x20f37,0x230f0f13,0x10e3303,0x18e3383,0x6f3023,0x7f3423,0x2049e13,0x1cae333,0x1830333,0xfe6f3023,0xfe0f3423]

def keygenCode_1 : List (BitVec 32) := bv_list% 32 [0x1c7e93,0x4e9e93,0x20537,0x20050513,0x4000593,0x20637,0x24060613,0x73,0x73c0006f,0x2e0e33,0x41d60eb3,0x10eb303,0x18eb383,0x6e3023,0x7e3423,0x13,0x1c0c13,0xf69ff06f,0x7080006f,0xf59ff06f,0x8067,0x50137,0x10113,0xa000f13,0x1013303,0x1813383,0x6f3023,0x7f3423,0x80c37,0x20c0c13,0x1a37,0xa0a13,0xb13,0xb93,0x1a5d13,0x4a1a93,0x50137,0x10113,0x2a8ab3,0x1337,0xd0130313,0x20b1393,0x736333,0x20b9393,0x20e37,0xe0e13,0x6e3823,0x7e3c23,0x20537,0x50513,0x4000593,0x20637,0x6060613,0x73,0xab303,0x63383,0x734333,0x6c3023,0x8ab303,0x863383,0x734333,0x6c3423,0x10ab303,0x1063383,0x734333,0x6c3823,0x18ab303,0x1863383,0x734333,0x6c3c23,0x20a8a93,0x20c0c13,0x1b8b93,0xf7abece3,0x1a5a13,0x1b0b13,0xc00313,0xf46b68e3,0x20e37,0xe0e13,0xeb7,0x80e8e93,0xeb303,0x6e3023,0x8eb303,0x6e3423,0x10eb303,0x26e3023,0x18eb303,0x26e3423,0x20e3823,0x20e3c23,0x1337,0xe0130313,0x6e3823,0xe3c23,0x20537,0x50513,0x4000593,0x70637,0x60613,0x73,0x100313,0x2031313,0x6e3c23,0x70637,0x2060613,0x73,0xfff00913,0x395913,0xa09b7,0x98993,0x70b37,0xb0b13,0x80cb7,0xc8c93,0xb3b83,0x12bfbb3,0x8b3c03,0x806b7,0x2068693,0x713,0x6e783,0xe787b3,0x377b833,0x37787b3,0x381813,0x3d7d893,0x1180833,0x127f7b3,0xf80833,0x3d85713,0x1287833,0x1070733,0x46e783,0xe787b3,0x377b833,0x37787b3,0x381813,0x3d7d893,0x1180833,0x127f7b3,0xf80833,0x3d85713,0x1287833,0x1070733,0x868693,0xf9369ee3,0x3d75793,0x1277733,0xf70733,0x12747b3,0x17b793,0xfff78793,0xf77733,0x1870733,0xecb023,0x10b0b13,0xb3b83,0x12bfbb3,0x8b3c03,0x806b7,0x2068693,0x713,0x6e783,0xe787b3,0x377b833,0x37787b3,0x381813,0x3d7d893,0x1180833,0x127f7b3,0xf80833,0x3d85713,0x1287833,0x1070733,0x46e783,0xe787b3,0x377b833,0x37787b3,0x381813,0x3d7d893,0x1180833,0x127f7b3,0xf80833,0x3d85713,0x1287833,0x1070733,0x868693,0xf9369ee3,0x3d75793,0x1277733,0xf70733,0x12747b3,0x17b793,0xfff78793,0xf77733,0x1870733,0xecb423,0x10b0b13,0xb3b83,0x12bfbb3,0x8b3c03,0x806b7,0x2068693,0x713,0x6e783,0xe787b3,0x377b833,0x37787b3,0x381813,0x3d7d893,0x1180833,0x127f7b3,0xf80833,0x3d85713,0x1287833,0x1070733,0x46e783,0xe787b3,0x377b833,0x37787b3,0x381813,0x3d7d893,0x1180833,0x127f7b3,0xf80833,0x3d85713,0x1287833,0x1070733,0x868693,0xf9369ee3,0x3d75793,0x1277733,0xf70733,0x12747b3,0x17b793,0xfff78793,0xf77733,0x1870733,0xecb823,0x10b0b13,0xb3b83,0x12bfbb3,0x8b3c03,0x806b7,0x2068693,0x713,0x6e783,0xe787b3,0x377b833,0x37787b3,0x381813,0x3d7d893,0x1180833,0x127f7b3]

def keygenCode_2 : List (BitVec 32) := bv_list% 32 [16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,16189235,19351475,1554323,0xfff78793,16217907,25626419,15514659,1049235,1299,115]++List.replicate 45 19++bv_list% 32 [12583827,264803,1049491,7603299,915,6521747,7639859,19071795,134711,437128723,33772435,8272931,33755923,16995091,50598803,7562035,202379027,59711251,31679283,268071827,8622995,7562035,134865811,7562035,0x885ff06f,0x650006f,0x600f13,65603379,34019091,1533715,3731,132407,15022115,343075,67110291,67438099,115,67449347,4993059,75837955,4994083,84226563,4995107,92615171,4996131,34343955,1052435,34545427,31917875,2002579,0x1000f13,0xfbee98e3,2451,32871,19,0x3d0006f,1939,136503,0xc050513,136631,0xff050513,2067,3091,531,1555,429715,2031379,985187,15222835,16534579,12730931,66576147,1447443,31876659,66543379,1546131,31975347,1513235,2023059,0xfc0e96e3,1187603,32000051,2236179,32000051,7479059,32000051,4737075,343811,31999795,8732419,32262067,0xf8b512e3,134967,485439523,486489123,32871,19,5245587,28315411,0x85e9c6e3,4197011,0x1480006f]++bv_list% 32 [0x6041263,0x19f313,0x393,0x4731c63,0x3400393,0x533c863,0x10e3303,0x46e3023,0x18e3303,0x46e3423,0x40e3823,0x40e3c23,0x60e3023,0x60e3423,0x30e0513,0x4000593,0x20e0613,0xfffa8313,0x3300393,0x99463,0xa8313,0x6a1463,0x30e0613,0x73,0xf10ff06f,0x20e3023,0x20e3423,0xe0513,0x4000593,0x30e0613,0x73,0xef4ff06f] ++ bv_list% 32 [0x100a13,0x100693,0x851ff06f,0x1a5a13,0x168693,0x84dff06f,0xc00e13,0x9c68063,0xffd68713,0x300e13,0x7c6ca63,0x71863,0x100713,0x80006f,0x800713,0x4000e13,0x40ee0e33,0xfff00813,0x1c81833,0xb00e13,0x1c69663,0xff00813,0x2881813,0x6800893,0xe898b3,0x41d60f33,0x18f3f03,0x10f7f33,0x20f0663,0x20e37,0x220e3f03,0x1f0f13,0x11f7e63,0x23ee3023,0x20537,0x20050513,0x4000593,0x73,0xfcdff06f,0x20e37,0x220e3023,0x4c1e13,0x2e0e33,0x41d60eb3,0x10eb303,0x18eb383,0x6e3023]
def keygenCode_3 : List (BitVec 32) := bv_list% 32 [0x7e3423,0x83dff06f] ++ bv_list% 32 [0x3000f13,0xefe9cc63,0x600a93,0x3200f13,0xefe9c663,0x500a93,0xee4ff06f] ++ List.replicate 247 19
def keygenCode_4 : List (BitVec 32) := List.replicate 93 19 ++ bv_list% 32 [3148435,2579093091,4197011,2555375727,787347,267645715,8590099,8639379,6546355,7735,4043181587,29618995,4395795,4445075,29619123,6546355,15927,859704851,29618995,2298643,2347923,29619123,6546355,24119,1432227347,29618995,1250067,1299347,29619123,6546355,50566035,2706370671] ++ bv_list% 32 [0x397f13,0x40f1263,0x21c37,0x295f13,0x1f7e93,0x1f00713,0x2ef0733,0x1d70733,0x175713,0x2071713,0x176713,0xe8c63,0x1f0c3203,0x4c3023,0x1f8c3203,0x4c3423,0x10c0c13,0xf70ff06f,0x993,0x8067,0x397f13,0x6f1f13,0x1e686b3,0x713,0x793,0x215b7,0x1f058513,0xfbcff06f]
def keygenCode : List (BitVec 32) :=
  [keygenCode_0, keygenCode_1, keygenCode_2, keygenCode_3, keygenCode_4].foldl (· ++ ·) []
def keygenData : List (BitVec 8) := [
]
def keygenImage : Riscv.Image := ⟨keygenCode, keygenData⟩
def keygenWords : Nat := 1177
end SigGolfCandidate.T3M.Images
end
-- ==== merged from ClaudeWCT_W9_T3M_Submission ====
section

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy
structure Images where
  sign : Riscv.Image
  expand : Riscv.Image
  verify : Riscv.Image
def submission (I : Images) : Submission where
  sizes := ⟨5310, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image
    | .keygen => SigGolfCandidate.T3M.Images.keygenImage
    | .sign => I.sign
    | .expand => I.expand
    | .verify => I.verify
variable (I : Images)
@[simp] theorem submission_sizes : (submission I).sizes = ⟨5310, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : (submission I).layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
theorem message_after_witness : (submission I).layout.message = (submission I).layout.witness + 22016 := by
  rw [submission_layout]
@[simp] theorem submission_keygen : (submission I).image .keygen = SigGolfCandidate.T3M.Images.keygenImage := rfl
@[simp] theorem submission_sign : (submission I).image .sign = I.sign := rfl
@[simp] theorem submission_expand : (submission I).image .expand = I.expand := rfl
@[simp] theorem submission_verify : (submission I).image .verify = I.verify := rfl
end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.Legacy

def submission (I : Images) : Submission where
  sizes := ⟨5195, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image := (ClaudeWCT.W9.T3M.submission I).image

variable (I : Images)
@[simp] theorem submission_sizes : (submission I).sizes = ⟨5195, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : (submission I).layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
@[simp] theorem submission_image : (submission I).image = (ClaudeWCT.W9.T3M.submission I).image := rfl
@[simp] theorem submission_keygen : (submission I).image .keygen = SigGolfCandidate.T3M.Images.keygenImage := rfl
@[simp] theorem submission_sign : (submission I).image .sign = I.sign := rfl
@[simp] theorem submission_expand : (submission I).image .expand = I.expand := rfl
@[simp] theorem submission_verify : (submission I).image .verify = I.verify := rfl

end ClaudeWCT.W9.T3M.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_Pending ====
section

section
namespace ClaudeWCT.W9.T3.SourceReplay
open OracleComp OracleSpec
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_mapM
  hashOnly_foldlM hashOnly_shortHash hashOnly_privatePair hashOnly_nodeHash fixedAnswers fixed_replay)
open ClaudeWCT.WCT9 (Signature Witness)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[aesop safe apply] theorem hashOnly_chain (index coord selected i start count : Nat) (value : Digest) :
    HashOnly (ClaudeWCT.WCT9.chain index coord selected i start count value) := by
  unfold ClaudeWCT.WCT9.chain; hashes
@[aesop safe apply] theorem hashOnly_leafHash (index coord selected : Nat) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash; hashes
@[aesop safe apply] theorem hashOnly_forestPk (index : Nat) (pairs : List (Digest × Digest)) :
    HashOnly (ClaudeWCT.WCT9.forestPk index pairs) := by
  unfold ClaudeWCT.WCT9.forestPk; hashes
@[aesop safe apply] theorem hashOnly_ite' {α : Type} {c : Prop} [Decidable c] {p q : M α}
    (hp : HashOnly p) (hq : HashOnly q) : HashOnly (if c then p else q) := by
  split
  · exact hp
  · exact hq
@[aesop safe apply] theorem hashOnly_ftsSeedPair (index coord pair : Nat) :
    HashOnly (ClaudeWCT.WCT9.ftsSeedPair index coord pair) := by
  unfold ClaudeWCT.WCT9.ftsSeedPair; exact hashOnly_privatePair _ _ _ _ _
@[aesop safe apply] theorem hashOnly_lowerSeedPair (lay : Layer) (tree pair : Nat) :
    HashOnly (ClaudeWCT.WCT9.lowerSeedPair lay tree pair) := by
  unfold ClaudeWCT.WCT9.lowerSeedPair; exact hashOnly_privatePair _ _ _ _ _
theorem hashOnly_packedSecret (pairQuery : Nat → M (Digest × Digest)) (h : ∀ p, HashOnly (pairQuery p))
    (q : Nat) (carry : Digest) : HashOnly (ClaudeWCT.WCT9.packedSecret pairQuery q carry) := by
  unfold ClaudeWCT.WCT9.packedSecret
  split
  · exact hashOnly_bind (h _) fun _ => hashOnly_pure _
  · exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_packedSecret_fts (index coord q : Nat) (carry : Digest) :
    HashOnly (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.ftsSeedPair index coord) q carry) :=
  hashOnly_packedSecret _ (hashOnly_ftsSeedPair index coord) q carry
@[aesop safe apply] theorem hashOnly_packedSecret_lower (lay : Layer) (tree q : Nat) (carry : Digest) :
    HashOnly (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.lowerSeedPair lay tree) q carry) :=
  hashOnly_packedSecret _ (hashOnly_lowerSeedPair lay tree) q carry
@[aesop safe apply] theorem hashOnly_ftsCoefs (index coord : Nat) :
    HashOnly (ClaudeWCT.WCT9.ftsCoefs index coord) := by
  unfold ClaudeWCT.WCT9.ftsCoefs
  exact hashOnly_foldlM _ _ (fun acc j =>
    hashOnly_bind (hashOnly_ftsSeedPair index coord j) fun _ => hashOnly_pure _) _
@[aesop safe apply] theorem hashOnly_leafHashP (index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHashP index coord selected pad ends) := by
  unfold ClaudeWCT.WCT9.leafHashP; exact SigGolfCandidate.T3.SourceReplay.hashOnly_shortHash _
@[aesop safe apply] theorem hashOnly_buildChildF (index coord selected : Nat) (word : ClaudeWCT.WCT9.Rank)
    (coefs : List Digest) (padL : Digest) :
    HashOnly (ClaudeWCT.WCT9.buildChildF index coord selected word coefs padL) := by
  unfold ClaudeWCT.WCT9.buildChildF
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · exact hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (hashOnly_leafHashP _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_wctNodeHash (coord index heap : Nat) (left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctNodeHash coord index heap left right) := by
  unfold ClaudeWCT.WCT9.wctNodeHash; exact hashOnly_nodeHash _ _ _ _ _ _
/-- C1: the paired leaf / node / child (either half) only make public hash queries. -/
@[aesop safe apply] theorem hashOnly_ftsHash (heap : Nat) (input : HashInput) :
    HashOnly (ClaudeWCT.WCT9.ftsHash heap input) := by
  rw [ClaudeWCT.WCT9.ftsHash_eq]
  split
  · unfold ClaudeWCT.WCT9.highHash
    exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_publicHash _) fun _ => hashOnly_pure _
  · exact SigGolfCandidate.T3.SourceReplay.hashOnly_shortHash _
@[aesop safe apply] theorem hashOnly_leafHashH (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHashH heap index coord selected pad ends) := by
  unfold ClaudeWCT.WCT9.leafHashH; exact hashOnly_ftsHash _ _
@[aesop safe apply] theorem hashOnly_wctNodeHashH (coord index heap : Nat) (left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctNodeHashH coord index heap left right) := by
  unfold ClaudeWCT.WCT9.wctNodeHashH; exact hashOnly_ftsHash _ _
@[aesop safe apply] theorem hashOnly_buildChildH (heap index coord selected : Nat) (word : ClaudeWCT.WCT9.Rank)
    (coefs : List Digest) (padL : Digest) :
    HashOnly (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs padL) := by
  unfold ClaudeWCT.WCT9.buildChildH
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · exact hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (hashOnly_leafHashH _ _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_wctTopHash (coord index heap : Nat) (left pad right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctTopHash coord index heap left pad right) := by
  unfold ClaudeWCT.WCT9.wctTopHash ClaudeWCT.WCT9.highHash
  exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_publicHash _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_wctHeapNode (coord index heap : Nat) (padR left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctHeapNode coord index heap padR left right) := by
  unfold ClaudeWCT.WCT9.wctHeapNode
  exact hashOnly_ite' (hashOnly_wctTopHash _ _ _ _ _ _) (hashOnly_wctNodeHash _ _ _ _ _)
@[aesop safe apply] theorem hashOnly_heapBuild (index coord : Nat) (padR : Digest) (leaves : List Digest) :
    HashOnly (ClaudeWCT.WCT9.heapBuild index coord padR leaves) := by
  unfold ClaudeWCT.WCT9.heapBuild
  exact hashOnly_foldlM _ _ (fun nodes heap =>
    hashOnly_bind (hashOnly_wctHeapNode coord index heap padR _ _) fun _ => hashOnly_pure _) _
@[aesop safe apply] theorem hashOnly_buildCoordinateF (index : Nat) (coord : ClaudeWCT.WCT9.Coord)
    (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) (prev : Digest × Digest) :
    HashOnly (ClaudeWCT.WCT9.buildCoordinateF index coord selected word prev) := by
  unfold ClaudeWCT.WCT9.buildCoordinateF
  refine hashOnly_bind (hashOnly_ftsCoefs index coord.val) fun coefs => ?_
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state j => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildChildF index coord.val j word _ prev.1) fun r => ?_
    rcases r with ⟨root, values⟩
    exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_heapBuild index coord.val prev.2 state.1) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (carry : Digest) : HashOnly (ClaudeWCT.WCT9.buildLeafP lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafP
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_packedSecret_lower _ _ _ _) fun r => ?_
    rcases r with ⟨seed, carry'⟩
    exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun _ => hashOnly_pure _
/-! C2/C3: the half-selecting hashes of the current scheme make the same single query as `shortHash`. -/
@[aesop safe apply] theorem hashOnly_halfHash (high : Bool) (input : HashInput) :
    HashOnly (ClaudeWCT.WCT9.halfHash high input) := by
  rw [ClaudeWCT.WCT9.halfHash_eq]
  exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_publicHash _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_chainW (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    HashOnly (ClaudeWCT.WCT9.chainW lay tree leaf i start count value) := by
  unfold ClaudeWCT.WCT9.chainW
  exact hashOnly_foldlM _ _ (fun _ _ => hashOnly_halfHash _ _) _
@[aesop safe apply] theorem hashOnly_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ends) := by
  unfold ClaudeWCT.WCT9.lowerLeafHash ClaudeWCT.WCT9.leafHashW ClaudeWCT.WCT9.lowerHash
  exact hashOnly_halfHash _ _
@[aesop safe apply] theorem hashOnly_lowerNodeHash (lay tree heap : Nat) (left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.lowerNodeHash lay tree heap left right) := by
  unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash
  exact hashOnly_halfHash _ _
@[aesop safe apply] theorem hashOnly_lowerLevel (lay tree h level : Nat) (nodes : List Digest) :
    HashOnly (ClaudeWCT.WCT9.lowerLevel lay tree h level nodes) := by
  unfold ClaudeWCT.WCT9.lowerLevel; hashes
@[aesop safe apply] theorem hashOnly_buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (carry : List Digest) : HashOnly (ClaudeWCT.WCT9.buildLeafPF lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafPF
  refine hashOnly_bind ?_ fun cc => ?_
  · unfold ClaudeWCT.WCT9.lowerCoefs ClaudeWCT.WCT9.lowerFamCoefs
    split
    · exact hashOnly_bind (hashOnly_bind (hashOnly_foldlM _ _ (fun acc j =>
        hashOnly_bind (hashOnly_lowerSeedPair _ _ _) fun _ => hashOnly_pure _) _) fun _ => hashOnly_pure _)
        fun _ => hashOnly_pure _
    · exact hashOnly_pure _
  rcases cc with ⟨coefs, carry'⟩
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · exact hashOnly_bind (hashOnly_chainW _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (hashOnly_chainW _ _ _ _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (hashOnly_lowerLeafHash _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_buildLevelsBelow (tag lay tree h : Nat) (leaves : List Digest) :
    HashOnly (ClaudeWCT.WCT9.buildLevelsBelow tag lay tree h leaves) := by
  unfold ClaudeWCT.WCT9.buildLevelsBelow; hashes
@[aesop safe apply] theorem hashOnly_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.buildTreeP lay tree selected digits) := by
  unfold ClaudeWCT.WCT9.buildTreeP
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state leaf => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildLeafPF lay tree leaf _ _) fun r => ?_
    rcases r with ⟨⟨root, values⟩, carry⟩
    exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_buildLevelsBelow _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.digestSearch; hashes
@[aesop safe apply] theorem hashOnly_openingStep (index : Nat) (output : HashOutput)
    (state : List ClaudeWCT.WCT9.Opening × List (Digest × Digest)) (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.openingStep index output state coord) := by
  unfold ClaudeWCT.WCT9.openingStep; hashes
@[aesop safe apply] theorem hashOnly_forestRows (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows; hashes
@[aesop safe apply] theorem hashOnly_signForest (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest; hashes
@[aesop safe apply] theorem hashOnly_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput)
    (coord : ClaudeWCT.WCT9.Coord) (prev : Digest × Digest) :
    HashOnly (ClaudeWCT.WCT9.recoverCoordinate sig index output coord prev) := by
  unfold ClaudeWCT.WCT9.recoverCoordinate; hashes
@[aesop safe apply] theorem hashOnly_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.recoverFts sig index output) := by
  unfold ClaudeWCT.WCT9.recoverFts ClaudeWCT.WCT9.recoverFtsFrom; hashes
@[aesop safe apply] theorem hashOnly_encodingHash (lay : Layer) (input : HashInput) :
    HashOnly (ClaudeWCT.WCT9.encodingHash lay input) := by
  exact (ClaudeWCT.WCT9.allQueries_encodingHash_iff lay input _).mpr (hashOnly_shortHash input)
@[aesop safe apply] theorem hashOnly_verificationHash (lay : Layer) (high : Bool) (input : HashInput) :
    HashOnly (ClaudeWCT.WCT9.verificationHash lay high input) := by
  exact (ClaudeWCT.WCT9.allQueries_verificationHash_iff lay high input _).mpr (hashOnly_shortHash input)
@[aesop safe apply] theorem hashOnly_layerCounterSearch (lay : Layer) (tree leaf : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
@[aesop safe apply] theorem hashOnly_signLayersBC (cache : Cache) (index n : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) :
    HashOnly (ClaudeWCT.WCT9.signLayersBC cache index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.signLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.signLayersBC; hashes
@[aesop safe apply] theorem hashOnly_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer)
    (digits : List Nat) : HashOnly (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair; hashes
@[aesop safe apply] theorem hashOnly_expandLayersBC (sig : Signature) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.expandLayersBC sig index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
@[aesop safe apply] theorem hashOnly_verifyTop (sig : Signature) (index : Nat) (answer : Digest) :
    HashOnly (ClaudeWCT.WCT9.verifyTop sig index answer) := by
  unfold ClaudeWCT.WCT9.verifyTop
  exact ClaudeWCT.W9.T3M.allQ_topDecodeRun _ _ _
    (fun _ _ => SigGolfCandidate.T3.SourceReplay.hashOnly_layChain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun _ =>
        hashOnly_foldlM _ _ (fun _ _ => hashOnly_nodeHash _ _ _ _ _ _) _
@[aesop safe apply] theorem hashOnly_recoverLayerPairGuard (sig : Signature) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.recoverLayerPairGuard sig index lay answer digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPairGuard ClaudeWCT.WCT9.lowerGuardedRun
  hashes
@[aesop safe apply] theorem hashOnly_verifyLayersBC (w : Witness) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.verifyLayersBC w index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
-- img-v6: `searchLimit lay = (lay.val + 3)/2 * 2^20` would let aesop's whnf unfold `Nat.mul` 2^20 times.
attribute [local irreducible] ClaudeWCT.WCT9.searchLimit in
@[aesop safe apply] theorem hashOnly_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signPayloadWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signPayloadWith; hashes
attribute [local irreducible] ClaudeWCT.WCT9.searchLimit in
@[aesop safe apply] theorem hashOnly_signWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signWith; hashes
attribute [local irreducible] ClaudeWCT.WCT9.searchLimit in
@[aesop safe apply] theorem hashOnly_expandWith (limit : Nat) (message : Message) (pk : Digest)
    (sig : Signature) : HashOnly (ClaudeWCT.WCT9.expandWith limit message pk sig) := by
  unfold ClaudeWCT.WCT9.expandWith; hashes
@[aesop safe apply] theorem hashOnly_verifyWith (limit : Nat) (message : Message) (pk : Digest)
    (w : Witness) : HashOnly (ClaudeWCT.WCT9.verifyWith limit message pk w) := by
  unfold ClaudeWCT.WCT9.verifyWith; hashes
@[aesop safe apply] theorem hashOnly_signPayload (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.signPayload cache message) :=
  hashOnly_signPayloadWith _ cache message
@[aesop safe apply] theorem hashOnly_sign (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.sign cache message) :=
  hashOnly_signWith _ cache message
theorem hashOnly_topFold (sig : Signature) (index : Nat) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.topFold sig index digits) := by
  unfold ClaudeWCT.WCT9.topFold ClaudeWCT.WCT9.topEnds
  refine hashOnly_bind (hashOnly_mapM _ _ fun i => SigGolfCandidate.T3.SourceReplay.hashOnly_layChain _ _ _ _ _ _ _)
    fun ends => ?_
  refine hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun value => ?_
  exact hashOnly_foldlM _ _ (fun v j => by unfold ClaudeWCT.WCT9.topStep; exact hashOnly_nodeHash _ _ _ _ _ _) _
theorem hashOnly_topNonceSearch (h heap : Nat) (l r : Digest) :
    ∀ fuel n, HashOnly (SigGolfCandidate.T3.topNonceSearch h heap l r fuel n)
  | 0, n => by
      unfold SigGolfCandidate.T3.topNonceSearch SigGolfCandidate.T3.topNodeHashN
      exact hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_projHash _ _) fun _ => hashOnly_pure _
  | fuel + 1, n => by
      unfold SigGolfCandidate.T3.topNonceSearch
      refine hashOnly_bind (by unfold SigGolfCandidate.T3.topNodeHashN
                               exact SigGolfCandidate.T3.SourceReplay.hashOnly_projHash _ _) fun _ => ?_
      split
      · exact hashOnly_pure _
      · exact hashOnly_topNonceSearch h heap l r fuel (n + 1)
theorem hashOnly_topFoldN (sig : Signature) (index : Nat) (digits : List Nat) :
    HashOnly (ClaudeWCT.WCT9.topFoldN sig index digits) := by
  unfold ClaudeWCT.WCT9.topFoldN ClaudeWCT.WCT9.topEnds
  refine hashOnly_bind (hashOnly_mapM _ _ fun i => SigGolfCandidate.T3.SourceReplay.hashOnly_layChain _ _ _ _ _ _ _)
    fun ends => ?_
  refine hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun value => ?_
  exact hashOnly_foldlM _ _ (fun v j => by
    unfold ClaudeWCT.WCT9.topStepN SigGolfCandidate.T3.topNodeAt
    exact hashOnly_bind (hashOnly_topNonceSearch _ _ _ _ _ _) fun _ => hashOnly_pure _) _
@[aesop safe apply] theorem hashOnly_verifyTopN (sig : Signature) (nonces : List Nat) (index : Nat) (answer : Digest) :
    HashOnly (ClaudeWCT.WCT9.verifyTopN sig nonces index answer) := by
  unfold ClaudeWCT.WCT9.verifyTopN
  exact ClaudeWCT.W9.T3M.allQ_topDecodeRun _ _ _
    (fun _ _ => SigGolfCandidate.T3.SourceReplay.hashOnly_layChain _ _ _ _ _ _ _) fun _ =>
      hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_leafHash _ _ _ _) fun _ =>
        hashOnly_foldlM _ _ (fun _ j => by
          dsimp only
          split
          · unfold SigGolfCandidate.T3.topNodeHashN
            exact SigGolfCandidate.T3.SourceReplay.hashOnly_projHash _ _
          · exact hashOnly_nodeHash _ _ _ _ _ _) _
theorem hashOnly_topNode (index : Nat) (v o : Digest) : HashOnly (ClaudeWCT.WCT9.topNode index v o) := by
  unfold ClaudeWCT.WCT9.topNode; exact hashOnly_nodeHash _ _ _ _ _ _
theorem hashOnly_expandLayersT (sig : Signature) (index : Nat) (o : Digest) (n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.expandLayersT sig index o n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.expandLayersT; exact hashOnly_pure _
  | succ n ih =>
    unfold ClaudeWCT.WCT9.expandLayersT
    refine hashOnly_bind (hashOnly_layerCounterSearch _ _ _ _ _ _) fun r => ?_
    rcases r with _ | ⟨counter, digits⟩
    · exact hashOnly_pure _
    · exact hashOnly_ite' (hashOnly_bind (hashOnly_topFold _ _ _) fun _ =>
          hashOnly_bind (hashOnly_topNode _ _ _) fun _ => hashOnly_pure _)
        (hashOnly_bind (hashOnly_recoverLayerPair _ _ _ _) fun _ => hashOnly_bind (ih _) fun r => by
          rcases r with _ | ⟨v, root, cs⟩ <;> exact hashOnly_pure _)
theorem hashOnly_searchTop (index : Nat) (v sib pk : Digest) (fuel c : Nat) :
    HashOnly (ClaudeWCT.WCT9.searchTop index v sib pk fuel c) := by
  induction fuel generalizing c with
  | zero => unfold ClaudeWCT.WCT9.searchTop; exact hashOnly_pure _
  | succ fuel ih =>
    unfold ClaudeWCT.WCT9.searchTop
    exact hashOnly_bind (hashOnly_topNode _ _ _) fun _ => hashOnly_ite' (hashOnly_pure _) (ih _)
theorem hashOnly_expandS (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (ClaudeWCT.WCT9.expandS limit message pk sig) := by
  unfold ClaudeWCT.WCT9.expandS
  refine hashOnly_bind (hashOnly_digestSearch _ _ _ _) fun r => ?_
  rcases r with _ | ⟨counter, output⟩
  · exact hashOnly_pure _
  refine hashOnly_bind (hashOnly_recoverFts _ _ _) fun root => ?_
  refine hashOnly_bind (hashOnly_expandLayersT _ _ _ _ _) fun r => ?_
  rcases r with _ | ⟨v, root', cs⟩
  · exact hashOnly_pure _
  refine hashOnly_ite' (hashOnly_pure _) (hashOnly_bind (hashOnly_searchTop _ _ _ _ _ _) fun r => ?_)
  rcases r with _ | c <;> exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (ClaudeWCT.WCT9.Rev3.expand message pk sig) := by
  unfold ClaudeWCT.WCT9.Rev3.expand
  exact hashOnly_map _ (hashOnly_expandS _ message pk sig)
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
    HashOnly (ClaudeWCT.WCT9.Rev3.verify message pk w) :=
  hashOnly_verifyWith _ message pk w
theorem sign_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (cache : Cache) (message : Message) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.sign cache message)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.sign cache message)) :=
  fixed_replay secret hash _ (hashOnly_sign cache message)
theorem expand_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (sig : Signature) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.expand message pk sig)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.expand message pk sig)) :=
  fixed_replay secret hash _ (hashOnly_expand message pk sig)
theorem verify_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (w : Witness) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.verify message pk w)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.verify message pk w)) :=
  fixed_replay secret hash _ (hashOnly_verify message pk w)
end ClaudeWCT.W9.T3.SourceReplay
end
section
namespace ClaudeWCT.W9.T3.NonceSampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev NonceOutputs := Message → HashOutput
abbrev SearchOutputs := SearchKey → HashOutput
abbrev QueryKey := Message ⊕ SearchKey
@[irreducible] noncomputable def nonceSampler : SampleableType NonceOutputs :=
  Derivation.outputSampler Message
@[irreducible] noncomputable def combinedSampler : SampleableType (QueryKey → HashOutput) :=
  Derivation.outputSampler QueryKey
noncomputable local instance : SampleableType NonceOutputs := nonceSampler
noncomputable local instance : SampleableType SearchOutputs := Presampling.tableSampler
noncomputable local instance : SampleableType (QueryKey → HashOutput) := combinedSampler
def nonceInputs (secret : BitVec 256) (message : Message) : HashInput :=
  privateInput secret (.inr (.inl message))
theorem nonceInputs_injective (secret : BitVec 256) : Function.Injective (nonceInputs secret) := by
  intro a b he
  exact Sum.inl.inj (Sum.inr.inj (privateInput_injective secret he))
theorem nonceInputs_length (secret : BitVec 256) (message : Message) :
    (nonceInputs secret message).length = 128 := by
  simp only [nonceInputs, privateInput_nonce, List.length_append, SphincsSecurity.bytesLE_length,
    zero16, List.length_replicate]
theorem nonceInputs_ne_searchQuery (secret : BitVec 256) (message : Message) (key : SearchKey) :
    nonceInputs secret message ≠ searchQuery key := by
  intro he
  have hl := congrArg List.length he
  rw [nonceInputs_length, searchQuery_length] at hl
  omega
def combinedInputs (secret : BitVec 256) : QueryKey → HashInput :=
  Sum.elim (nonceInputs secret) searchQuery
theorem combinedInputs_injective (secret : BitVec 256) : Function.Injective (combinedInputs secret) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (nonceInputs_injective secret he)
    | inr b => exact False.elim (nonceInputs_ne_searchQuery secret a b he)
  | inr a =>
    cases b with
    | inl b => exact False.elim (nonceInputs_ne_searchQuery secret b a he.symm)
    | inr b => exact congrArg Sum.inr (searchQuery_injective he)
noncomputable def preparedCache (secret : BitVec 256)
    (nonceOutputs : NonceOutputs) (searchOutputs : SearchOutputs) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ (combinedInputs secret) (Sum.elim nonceOutputs searchOutputs)
theorem preparedCache_nonce (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (message : Message) :
    preparedCache secret nonceOutputs searchOutputs (nonceInputs secret message) = some (nonceOutputs message) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inl message)
theorem preparedCache_search (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (key : SearchKey) :
    preparedCache secret nonceOutputs searchOutputs (searchQuery key) = some (searchOutputs key) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inr key)
theorem combined_uniform :
    𝒮[($ᵗ (QueryKey → HashOutput) : ProbComp _)] =
    𝒮[do
      let nonces ← ($ᵗ NonceOutputs : ProbComp _)
      let searches ← ($ᵗ SearchOutputs : ProbComp _)
      pure (Sum.elim nonces searches)] := by
  classical
  let : Fintype SearchOutputs := @Pi.instFintype SearchKey (fun _ => HashOutput)
    (Classical.decEq SearchKey) inferInstance (fun _ => inferInstance)
  let : Fintype NonceOutputs := @Pi.instFintype Message (fun _ => HashOutput)
    (Classical.decEq Message) inferInstance (fun _ => inferInstance)
  let split : (QueryKey → HashOutput) ≃ NonceOutputs × SearchOutputs :=
    Equiv.sumArrowEquivProdArrow Message SearchKey HashOutput
  have he := evalSPMF_map_bijective_uniform_cross
    (α := NonceOutputs × SearchOutputs) (β := QueryKey → HashOutput) split.symm split.symm.bijective
  have hp := evalDist_independent_uniform_pair (α := NonceOutputs) (β := SearchOutputs)
  rw [evalSPMF_map, ← hp] at he
  simpa only [evalSPMF_bind, evalSPMF_pure, map_bind, map_pure, split,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk] using he.symm
theorem presample_combined {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (QueryKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (cacheTable ∅ (combinedInputs secret) outputs)] := by
  let : SampleableType (QueryKey → SphincsSecurity.HashOutput) := combinedSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (QueryKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec))
        (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret)))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput)
      (combinedInputs secret) (combinedInputs_injective secret) ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let nonceOutputs ← ($ᵗ NonceOutputs : ProbComp _)
      let searchOutputs ← ($ᵗ SearchOutputs : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (preparedCache secret nonceOutputs searchOutputs)] := by
  rw [presample_combined, evalSPMF_bind, combined_uniform]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  rfl
end ClaudeWCT.W9.T3.NonceSampling
end
section
namespace ClaudeWCT.W9.T3.Completeness
open OracleComp OracleSpec ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_foldlM hashOnly_keygen
  fixedAnswers fixed_replay)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand hashOnly_verify)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true
theorem hashOnly_honestProgram (message : Message) : HashOnly (honestProgram message) := by
  unfold honestProgram
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (hashOnly_sign keys.2 message)
  intro sig
  cases sig with
  | none => exact hashOnly_pure false
  | some sig =>
    apply hashOnly_bind (hashOnly_expand message keys.1 sig)
    intro witness
    cases witness with
    | none => exact hashOnly_pure false
    | some witness => exact hashOnly_verify message keys.1 witness
theorem hashOnly_everyMessageProgram : HashOnly everyMessageProgram := by
  apply hashOnly_foldlM
  intro accepted message
  exact hashOnly_bind (hashOnly_honestProgram message) fun _ => hashOnly_pure _
theorem everyMessageProgram_true (answers : SigGolfCandidate.T3.Correctness.Answers)
    (hall : ∀ message, evalWithAnswerFn answers (honestProgram message) = true) :
    evalWithAnswerFn answers everyMessageProgram = true := by
  have hf : ∀ messages : List Message, ∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted) = accepted := by
    intro messages
    induction messages with
    | nil => intro accepted; rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hall, Bool.and_true]
      exact ih accepted
  exact hf _ true
noncomputable local instance : SampleableType (SearchKey → HashOutput) :=
  Presampling.tableSampler
theorem failure_le_bad_table (secret : BitVec 256) (program : M Bool)
    (good : (SearchKey → HashOutput) → Prop)
    (hzero : ∀ outputs, good outputs →
      Pr[fun value => value = false |
        (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
          (Presampling.preparedCache outputs)] = 0) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] ≤
    Pr[fun outputs => ¬good outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value = false))
    (Presampling.presample_source secret program)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_probEvent
  intro outputs _ hgood
  exact hzero outputs (not_not.mp hgood)
theorem prepared_failure_zero (secret : BitVec 256) (program : M Bool)
    (outputs : SearchKey → HashOutput)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      (Presampling.preparedCache outputs).AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program) = (pure true : ProbComp Bool)) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (Presampling.preparedCache outputs)] = 0 :=
  SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret program _ hgood
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler
end ClaudeWCT.W9.T3.Completeness
end
section
namespace ClaudeWCT.W9.T3.Freshness
open OracleComp OracleSpec
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery SearchQ SearchHdr RowHdr searchQ_ne header_not_search
  hasTag_not_search hasTag_privatePair)
open ClaudeWCT.WCT9 (FtsQuery FtsInput FtsSeed)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem ftsChain_not_search (index coord selected t step : Nat) :
    ¬ SearchHdr (ClaudeWCT.WCT9.ftsChainHeader index coord selected t step) := by
  have := ClaudeWCT.WCT9.ftsChainHeaderP_tweakMarker index coord selected t step 0
  unfold SearchHdr RowHdr ClaudeWCT.WCT9.ftsChainHeader; omega
theorem ftsLeaf_not_search (index coord selected : Nat) :
    ¬ SearchHdr (ClaudeWCT.WCT9.ftsLeafHeader index coord selected) := by
  unfold SearchHdr RowHdr
  rw [ClaudeWCT.WCT9.ftsLeafHeader_tweakMarker, ClaudeWCT.WCT9.ftsLeafHeader_tweakTag]; omega
theorem ftsNode_not_search {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    ¬ SearchHdr (ClaudeWCT.WCT9.wctNodeHeader coord index heap) := by
  unfold SearchHdr RowHdr
  rw [ClaudeWCT.WCT9.wctNodeHeader_tweakMarker, ClaudeWCT.WCT9.wctNodeHeader_tweakTag hk]
  by_cases hn : SigGolfCandidate.T3.FtsNew heap
  · rw [if_pos ⟨hk, hn⟩, if_pos hn]; obtain ⟨_, _⟩ := hn; omega
  · rw [if_neg (fun h => hn h.2), if_neg hn]; omega
theorem avoidsQuery_of_fts (secret : BitVec 256) (target : HashInput)
    (ht : SearchQ target) (index : Nat) (q : Spec.Domain)
    (hq : FtsQuery index q) : avoidsQuery secret target q := by
  rcases q with (coin | input) | (tweak | other)
  · exact hq.elim
  · rcases ClaudeWCT.WCT9.FtsInput.hdrBlock (show FtsInput index input from hq) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨coord, selected, -, -, hblock⟩ | ⟨coord, heap, hk, -, -, hblock⟩ | hblock
    · exact searchQ_ne hblock (ftsChain_not_search index coord selected t step) ht
    · exact searchQ_ne hblock (ftsLeaf_not_search index coord selected) ht
    · exact searchQ_ne hblock (ftsNode_not_search hk index heap) ht
    · exact searchQ_ne hblock (header_not_search 15 0 index 0 0 (by decide)) ht
  · obtain ⟨coord, pair, -, -, rfl⟩ := (show FtsSeed index tweak from hq)
    exact hasTag_not_search (hasTag_privatePair secret 8 coord index 0 pair) (by decide) ht
  · exact hq.elim
theorem avoids_signForest (secret : BitVec 256) (target : HashInput)
    (ht : SearchQ target) (index : Nat) (output : HashOutput) :
    Avoids secret target (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (ClaudeWCT.WCT9.signForest_queries index output)
    (fun q hq => avoidsQuery_of_fts secret target ht index q hq)
end ClaudeWCT.W9.T3.Freshness
end
section
namespace ClaudeWCT.W9.T3.BudgetClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V)
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (AllSearchesFreshBC)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (sign keys.2 message)
theorem honestSignCount_realize (secret : BitVec 256) (message : Message) :
    realize secret (honestSignCount message) = (do
      let keys ← realize secret keygen
      Cost.World.countBlocks (realize secret (sign keys.2 message))) := by
  rw [honestSignCount, Cost.realize_bind]
  congr 1
  funext keys
  exact Cost.realize_count secret _
end ClaudeWCT.W9.T3.BudgetClosure
end
section
namespace ClaudeWCT.W9.T3.ExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun)
open SigGolfCandidate.T3.Cost (countBlocks)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts eval_joint_cost_le)
open SigGolfCandidate.T3.SourceReplay (hashOnly_pure hashOnly_bind hashOnly_keygen)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
theorem hashOnly_honestJointCounts (message : Message) :
    SigGolfCandidate.T3.SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact hashOnly_pure _
  | some sig =>
    apply hashOnly_bind
      (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_expand message keys.1 sig))
    intro expanded
    exact hashOnly_pure _
end ClaudeWCT.W9.T3.ExpansionClosure
end
section
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (keygen Cache Digest realize)
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open ClaudeWCT.W9.T3M (Images submission)
def verifyCycleBound : Nat := 6997
def claimedC : Nat := 7083
def DigestCapOk (hash : Hash) (m : Message) (w : Bytes 22012) : Prop :=
  ∀ N, evalWithAnswerFn hash (mrealize 0 (digestP m w)) = some N → WCT9.capOk N = true
variable (I : Images)
def KeygenRunCounts : Prop := ∀ sk : SecretKey,
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .keygen sk =
    (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$> countBoth (mrealize sk keygen)
def KeygenRunWith : Prop := ∀ (hash : Hash) (sk : SecretKey),
  ((submission I).runWith hash .keygen sk).value =
      some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) ∧
    ((submission I).runWith hash .keygen sk).finished = true ∧
    ((submission I).runWith hash .keygen sk).cycles < CYCLE_LIMIT ∧
    ((submission I).runWith hash .keygen sk).hashCalls = (evalWithAnswerFn hash (countBoth (mrealize sk keygen))).2.1 ∧
    ((submission I).runWith hash .keygen sk).hashCompressions =
      (evalWithAnswerFn hash (countBoth (mrealize sk keygen))).2.2
def SignRefines : Prop := ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .sign (sk, cache, m) =
    (fun p => (p.1.map sigBC, p.2.1, p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))
def SignTerminates : Prop := ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  ((submission I).runWith hash .sign (sk, cache, m)).finished = true ∧
    ((submission I).runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT
def ExpandRefines : Prop := ∀ (m : Message) (pk : PublicKey) (s : Bytes 5310),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .expand (m, pk, s) =
    (fun p => (p.1.map (fun x => witEnc x.1 x.2), p.2.1, p.2.2)) <$>
      countBoth (mrealize 0 (expandN m pk (sigDecC s)))
def ExpandTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5310),
  ((submission I).runWith hash .expand (m, pk, s)).finished = true ∧
    ((submission I).runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT
def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 22012),
  (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22012),
  ((submission I).runWith hash .verify (m, pk, w)).finished = true ∧
    ((submission I).runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT
def VerifyAcceptCycles : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22012),
  SigGolfCandidate.T3M.Verify.HashOk hash → DigestCapOk hash m w →
  ((submission I).runWith hash .verify (m, pk, w)).value.isSome = true →
    ((submission I).runWith hash .verify (m, pk, w)).cycles ≤ verifyCycleBound
structure Pending : Prop where
  admissible : (submission I).Admissible
  keygen_run_counts : KeygenRunCounts I
  keygen_runWith : KeygenRunWith I
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I
def SourceCompleteness : Prop := ∀ secret : BitVec 256,
  1 - 1 / (2 : ℝ≥0∞) ^ 128 ≤
    Pr[= true | (simulateQ SphincsSecurity.romImpl
      (realize secret ClaudeWCT.W9.T3.Completeness.everyMessageProgram)).run' ∅]
def SignMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2
def ExpandMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2
/-- img-v6 keygen budget (nonce trials make keygen's compressions random): the spec moment
`E[2^(countBlocks keygen / 2^20)] ≤ 2` in the random-oracle model (COMPUTED 1.99933317; proved separately). -/
def KeygenMoment : Prop := ∀ (secret : BitVec 256),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret (SigGolfCandidate.T3.Cost.countBlocks keygen) ∅)
    (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2
structure SourceFacts : Prop where
  source_completeness : SourceCompleteness
  honest_sign_exponential_budget : SignMoment
  honest_expand_exponential_budget : ExpandMoment
  honest_keygen_exponential_budget : KeygenMoment
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ (cache : Cache) (message : SigGolfCandidate.T3.Message),
    AllQueriesSatisfy (sign cache message) isHash
  hashOnly_expand : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (sig : Signature),
    AllQueriesSatisfy (expand message pk sig) isHash
  hashOnly_verify : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (w : Witness),
    AllQueriesSatisfy (verify message pk w) isHash
  securityP : SecurityP
end ClaudeWCT.W9.T3M.Final
end


namespace ClaudeWCT.W9.T3.Freshness.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery SearchQ searchQ_ne)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The shared forest adds padded heaps4..7; all remaining query domains are unchanged. -/
def FtsQuery (index : Nat) (query : Query) : Prop :=
  ClaudeWCT.WCT9.FtsQuery index query ∨
    ∃ (coord heap : Nat) (left pad right : Digest), coord<9 ∧ 2≤heap ∧ heap<8 ∧
      query=.inl (.inr (pad64 (wctTopInput coord index heap left pad right)))

theorem lift_bound {index : Nat} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound (ClaudeWCT.WCT9.FtsQuery index) Post k oa) : Bound (FtsQuery index) Post k oa :=
  h.mono (fun _ hq => Or.inl hq) (fun _ hp => hp)

theorem avoidsQuery (secret : BitVec 256) (target : HashInput) (ht : SearchQ target)
    (index : Nat) (query : Query) (hq : FtsQuery index query) :
    SigGolfCandidate.T3.Freshness.avoidsQuery secret target query := by
  rcases hq with hlegacy|⟨coord,heap,left,pad,right,hcoord,_,_,rfl⟩
  · exact Freshness.avoidsQuery_of_fts secret target ht index query hlegacy
  · have hblock : SigGolfCandidate.T3M.Extract.hdrBlock
        (pad64 (wctTopInput coord index heap left pad right)) = bytesLE 16 (wctNodeHeader coord index heap) := by
      unfold wctTopInput
      rw [List.append_assoc (bytesLE 16 left ++ _),
        hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
    exact searchQ_ne hblock (Freshness.ftsNode_not_search hcoord index heap) ht

theorem bound_sharedOuterHash (coord index heap : Nat) (left right : Digest)
    (hc : coord<9) (hl : 2≤heap) (hh : heap<4) :
    Bound (FtsQuery index) (fun _ => True) 1 (sharedOuterHash coord index heap left right) := by
  have hq : FtsQuery index (.inl (.inr (pad64 (wctTopInput coord index heap left 0 right)))) :=
    Or.inr ⟨coord,heap,left,0,right,hc,hl,by omega,rfl⟩
  unfold sharedOuterHash
  split
  · exact bound_shortHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])
  · exact bound_highHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])

theorem bound_sharedNode (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot)
    (left right : Digest) (hc : coord<9) (hl : 2≤heap) (hh : heap<128) :
    Bound (FtsQuery index) (fun _ => True) 1 (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact bound_sharedOuterHash coord index heap left right hc hl (by assumption)
  · split
    · have hq : FtsQuery index (.inl (.inr
          (pad64 (wctTopInput coord index heap left (pads (heap/2-2)).2 right)))) :=
        Or.inr ⟨coord,heap,left,(pads (heap/2-2)).2,right,hc,hl,by assumption,rfl⟩
      split
      · exact bound_highHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])
      · exact bound_shortHashP _ 1 hq (by simp [pad64_length,wctTopInput_length])
    · exact lift_bound (ftsBound_nodeHashH index coord heap left right hc hl hh)

theorem bound_sharedHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) (hc : coord<9) :
    Bound (FtsQuery index) (fun _ => True) (if first then 124 else 126)
      (sharedHeap first index coord pads leaves) := by
  unfold sharedHeap
  refine (Bound.foldlM_list (P := FtsQuery index)
    (List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse
    (fun (nodes : Array Digest) heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2*heap) 0) (nodes.getD (2*heap+1) 0)
      pure (nodes.set! heap value)) (fun _ _ => True) (fun _ => 1) _
    trivial (fun i hi nodes _ => ?_)).mono_k (by simp)
  have hmem := List.getElem_mem hi
  rw [List.mem_reverse, List.mem_range'] at hmem
  have hb : 2≤((List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse[i]'hi) ∧
      ((List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse[i]'hi)<128 := by
    cases first <;> simp only [Bool.false_eq_true,↓reduceIte] at hmem ⊢ <;> omega
  exact (bound_sharedNode first coord index _ pads _ _ hc hb.1 hb.2).bind' (l:=0)
    (fun value _ => .pure (nodes.set! _ value) 0 trivial) (by omega)

theorem bound_buildSharedCoordinate (first : Bool) (index coord : Nat)
    (hcoord : coord<9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    Bound (FtsQuery index) (fun _ => True) (if first then 3479 else 3481)
      (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  refine (lift_bound (ftsBound_ftsCoefs index coord hcoord)).bind'
    (l:=3328+if first then 124 else 126) (fun coefs _ => ?_) ?_
  · refine (Bound.foldlM_range_le 128 _ (fun _ _ => True) (fun _ => 26) ([],[])
      trivial (fun j hj state _ => ?_) (fun _ _ => trivial) (by simp)).bind'
      (l:=if first then 124 else 126) (fun state _ => ?_) le_rfl
    · refine (lift_bound (ftsBound_buildChildH index (128 + j) coord (rawChild first j) word coefs
        (pads (j/64)).1 hcoord (rawChild_lt first j hj))).bind' (l:=0)
        (fun child _ => .pure _ 0 trivial) (by simp [ClaudeWCT.WCT9.childCost])
    · exact (bound_sharedHeap first index coord pads state.1 hcoord).bind' (l:=0)
        (fun nodes _ => .pure (nodes,state.2) 0 trivial) (by omega)
  · cases first <;> decide

theorem bound_buildPair (index pair : Nat) (hpair : pair<4) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    Bound (FtsQuery index) (fun _ => True) 6960 (buildPair index pair s aWord bWord prev) := by
  unfold buildPair
  refine (bound_buildSharedCoordinate true index (2*pair) (by omega)
    (firstChild s) aWord (fun _ => prev)).bind' (l:=3481) (fun a _ => ?_) (by decide)
  exact (bound_buildSharedCoordinate false index (2*pair+1) (by omega)
    (secondChild s) bWord (nodesPair a.1)).bind' (l:=0)
    (fun b _ => .pure _ 0 trivial) (by decide)

theorem bound_buildSingleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    Bound (FtsQuery index) (fun _ => True) 3481 (buildSingleton index selected word prev) := by
  unfold buildSingleton
  exact (bound_buildSharedCoordinate false index 8 (by decide) selected word (fun _ => prev)).bind'
    (l:=0) (fun built _ => .pure _ 0 trivial) (by decide)

theorem bound_buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Bound (FtsQuery index) (fun _ => True) 31321 (buildForest index selected words) := by
  unfold buildForest
  refine (Bound.foldlM_list (P:=FtsQuery index) (List.finRange 4) _ (fun _ _ => True)
    (fun _ => 6960) ([],ftsStart) trivial (fun i hi state _ => ?_)).bind'
    (l:=3481) (fun state _ => ?_) (by simp)
  · exact (bound_buildPair index _ ((List.finRange 4)[i]'hi).isLt _ _ _ state.2).bind'
      (l:=0) (fun built _ => .pure _ 0 trivial) (by decide)
  · exact (bound_buildSingleton index selected.singleton words.singleton state.2).bind'
      (l:=0) (fun last _ => .pure _ 0 trivial) (by decide)

theorem buildForest_queries (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (buildForest index selected words) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (bound_buildForest index selected words)

theorem avoids_buildForest (secret : BitVec 256) (target : HashInput)
    (ht : SearchQ target) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    Avoids secret target (buildForest index selected words) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (buildForest_queries index selected words)
    (fun query hq => avoidsQuery secret target ht index query hq)

end ClaudeWCT.W9.T3.Freshness.Paired

namespace SigGolfCandidate.Research.SharedSigningBudget
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Freshness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.PairRows
open ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Shared forest queries leave every WOTS encoding row fresh. -/
theorem buildForest_preserves_rows (secret : BitVec 256) (index stage : Nat)
    (selected : ForestSelection) (words : ForestWords) (cache : RCache)
    (hfresh : RowsFreshFrom stage cache)
    (result : (ForestOpening × PairRoot) × RCache)
    (hr : result ∈ support (roRun secret (buildForest index selected words) cache)) :
    RowsFreshFrom stage result.2 := by
  intro lay hl tree leaf left right counter hc
  rw [preserves secret _ _ (ClaudeWCT.W9.T3.Freshness.Paired.avoids_buildForest secret _
    (rowQ_pairTrial ..).searchQ index selected words) cache result hr]
  exact hfresh lay hl tree leaf left right counter hc

/-- Fixed forest/root preparation and the cost-tiered canonical searches compose. -/
theorem V_signFromOutput_certified_tier (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) (haccepted : digestAccepted output = true) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (signFromOutput cache rho counter output) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^112322 *
        ((ClaudeWCT.Numerics.TopZero.tierInitialBound (conditionalExtra output) : ENNReal)/scale) := by
  have he := (conditional_bounds_of_accepted output haccepted).1
  have h := V_signFromOutput_fixed secret SigGolfCandidate.T3.Budgets.signingZ
    (SigGolfCandidate.T3.Budgets.signingZ^180 *
      ((ClaudeWCT.Numerics.TopZero.tierInitialBound (conditionalExtra output) : ENNReal)/scale))
    (SigGolfCandidate.Budget.one_le_zOf _) cache rho counter output rcache ?_
  · simpa only [← mul_assoc, ← pow_add] using h
  · intro forest hforest prepared hprepared
    have hr := prepareRoots_preserves_rows secret (digestIndex output) 0 forest.2
      (buildForest_preserves_rows secret (digestIndex output) 0 _ _ rcache hfresh forest hforest)
      prepared hprepared
    simpa only [conditionalCredit, conditionalTopFloor,
      CanonicalPolicy.totalCredit, CanonicalPolicy.topFloor] using
      (V_searchPreparedLayers_certified_tier secret cache (digestIndex output)
        (conditionalExtra output) he prepared.1 forest.1.2 prepared.2 hr)

/-- The original floor-14 bound is recovered on the lowest digest-cost tier. -/
theorem V_signFromOutput_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) (haccepted : digestAccepted output = true)
    (hzero : conditionalExtra output = 0) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (signFromOutput cache rho counter output) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^112322 *
        ((ClaudeWCT.Numerics.TopZero.initialBound : ENNReal)/scale) := by
  simpa only [hzero, ClaudeWCT.Numerics.TopZero.tierInitialBound] using
    V_signFromOutput_certified_tier secret cache rho counter output rcache hfresh haccepted
end SigGolfCandidate.Research.SharedSigningBudget


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

theorem sharedDigestSearch_eq_run (rho : Digest) (message : Message) (counter fuel : Nat) :
    sharedDigestSearch rho message counter fuel=DigestGeneric.run digestAccepted rho message counter fuel := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih => simp only [sharedDigestSearch,DigestGeneric.run,ih]

theorem sharedDigestSearch_table_failure (outputsFallback : Answers) (rho : Digest) (message : Message) :
    Pr[fun outputs => evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs outputsFallback)
      (sharedDigestSearch rho message 0 digestAttemptLimit)=none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤1/(2:ENNReal)^400 := by
  simp_rw [sharedDigestSearch_eq_run]
  rw [DigestGeneric.run_table_failure _ _ (by rfl)]
  exact DigestGeneric.failure_power_400 _ ClaudeWCT.Bank.Paired.digestAccepted_acceptance_lower

end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Budgets (zeroAnswers)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := ClaudeWCT.W9.T3.Presampling.tableSampler

def TableGoodForNonces (nonces : Message → Digest) (outputs : SearchKey → HashOutput) : Prop :=
  (∀ message, evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)
    (sharedDigestSearch (nonces message) message 0 digestAttemptLimit)≠none) ∧
  ContextGood (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)

theorem not_tableGoodForNonces (nonces : Message → Digest) (outputs : SearchKey → HashOutput) :
    ¬TableGoodForNonces nonces outputs ↔
    (∃ message, evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)
      (sharedDigestSearch (nonces message) message 0 digestAttemptLimit)=none) ∨
    (∃ context, ContextFailed context (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)) := by
  classical
  simp only [TableGoodForNonces,ContextGood,not_and_or,not_forall,ne_eq,not_not]

theorem tableGoodForNonces_failure (nonces : Message → Digest) :
    Pr[fun outputs => ¬TableGoodForNonces nonces outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)]≤1/(2:ENNReal)^138 := by
  simp_rw [not_tableGoodForNonces]
  exact all_search_failure_small ($ᵗ (SearchKey → HashOutput) : ProbComp _)
    (fun message outputs => evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers)
      (sharedDigestSearch (nonces message) message 0 digestAttemptLimit)=none)
    (fun context outputs => ContextFailed context (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs zeroAnswers))
    (by simp [Message,Fintype.card_bitVec])
    (fun message => sharedDigestSearch_table_failure zeroAnswers (nonces message) message)
    context_table_failure

end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem sharedDigestSearch_none_agreement (outputs : SearchKey → HashOutput) (answers fallback : Answers)
    (hagree : ClaudeWCT.W9.T3.Budgets.SearchAgreement outputs answers) (rho : Digest) (message : Message) :
    evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit)=none ↔
      evalWithAnswerFn (ClaudeWCT.W9.T3.Presampling.tableAnswers outputs fallback)
        (sharedDigestSearch rho message 0 digestAttemptLimit)=none := by
  simp_rw [sharedDigestSearch_eq_run]
  exact (DigestGeneric.run_none_agreement _ _ (by rfl) outputs answers hagree rho message).trans
    (DigestGeneric.run_none_table _ _ (by rfl) outputs fallback rho message).symm

end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Budgets (zeroAnswers)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem tableGoodForNonces_signing (outputs : SearchKey → HashOutput) (answers : Answers)
    (nonces : Message → Digest) (hgood : TableGoodForNonces nonces outputs)
    (hagree : ClaudeWCT.W9.T3.Budgets.SearchAgreement outputs answers)
    (hnonce : ∀ message, evalWithAnswerFn answers (privateNonce message)=nonces message) :
    SigningComplete answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 := by
  have hcontext : ContextGood answers :=
    (contextGood_agreement outputs answers zeroAnswers hagree).mpr hgood.2
  have hc := (SigGolfCandidate.T3.Correctness.keygen_correct answers).2.2
  have hm : (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.tag=
      evalWithAnswerFn answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) := hc
  intro message
  apply sign_complete answers hcontext _ message hm.symm
  intro hd
  rw [hnonce message] at hd
  exact hgood.1 message ((sharedDigestSearch_none_agreement outputs answers zeroAnswers hagree _ _).mp hd)

end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.SourceReplay
open ClaudeWCT.W9.T3.SourceReplay
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[aesop safe apply] theorem hashOnly_sharedOuterHash (coord index heap : Nat) (left right : Digest) :
    HashOnly (sharedOuterHash coord index heap left right) := by
  unfold sharedOuterHash
  split
  · exact hashOnly_shortHash _
  · unfold highHash
    exact hashOnly_bind (hashOnly_publicHash _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_sharedNode (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) :
    HashOnly (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact hashOnly_sharedOuterHash _ _ _ _ _
  · split
    · split
      · unfold highHash
        exact hashOnly_bind (hashOnly_publicHash _) fun _ => hashOnly_pure _
      · exact hashOnly_shortHash _
    · exact hashOnly_wctNodeHashH _ _ _ _ _
@[aesop safe apply] theorem hashOnly_recoverSharedInner (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    HashOnly (recoverSharedInner first index coord selected word values path prev) := by
  unfold recoverSharedInner
  refine hashOnly_bind (hashOnly_mapM _ _ (fun _ => ClaudeWCT.W9.T3.SourceReplay.hashOnly_chain _ _ _ _ _ _ _)) fun _ => ?_
  refine hashOnly_bind (hashOnly_leafHashH _ _ _ _ _ _) fun _ => ?_
  exact hashOnly_foldlM _ _ (fun _ _ => hashOnly_sharedNode _ _ _ _ _ _ _) _
@[aesop safe apply] theorem hashOnly_recoverPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : HashOnly (recoverPair index pair s aWord bWord opened prev) := by
  unfold recoverPair
  refine hashOnly_bind (hashOnly_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  refine hashOnly_bind (hashOnly_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact hashOnly_bind (hashOnly_sharedOuterHash _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : HashOnly (recoverSingleton index selected word opened prev) := by
  unfold recoverSingleton
  refine hashOnly_bind (hashOnly_recoverSharedInner _ _ _ _ _ _ _ _) fun _ => ?_
  exact hashOnly_bind (hashOnly_sharedOuterHash _ _ _ _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : HashOnly (recoverForest index selected words opened) := by
  unfold recoverForest
  exact hashOnly_bind (hashOnly_foldlM _ _ (fun _ _ => hashOnly_recoverPair _ _ _ _ _ _ _) _) fun _ =>
    hashOnly_recoverSingleton _ _ _ _ _
@[aesop safe apply] theorem hashOnly_layerCounterSearchAt (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (counter fuel : Nat) :
    HashOnly (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold CanonicalPolicy.layerCounterSearchAt; exact hashOnly_pure _
  | succ fuel ih =>
    unfold CanonicalPolicy.layerCounterSearchAt
    refine hashOnly_bind (SigGolfCandidate.T3.SourceReplay.hashOnly_publicHash _) fun result => ?_
    split
    · exact ih _
    · exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_recoverHintedLayers (sig : Signature) (index : Nat) (other : Digest)
    (n : Nat) (msg : LayerMsg) (topFloor : Nat := CanonicalPolicy.topFloor) :
    HashOnly (recoverHintedLayers sig index other n msg topFloor) := by
  induction n generalizing msg with
  | zero => unfold recoverHintedLayers; exact hashOnly_pure _
  | succ n ih =>
    unfold recoverHintedLayers
    refine hashOnly_bind (hashOnly_layerCounterSearchAt _ _ _ _ _ _ _) fun result => ?_
    rcases result with _ | ⟨counter,digits,low⟩
    · exact hashOnly_pure _
    · dsimp only
      split
      · refine hashOnly_bind (hashOnly_topFoldN _ _ _) fun p => ?_
        rcases p with ⟨_, _⟩
        exact hashOnly_bind (hashOnly_topNode _ _ _) fun _ => hashOnly_pure _
      · refine hashOnly_bind (hashOnly_recoverLayerPair _ _ _ _) fun pair => ?_
        refine hashOnly_bind (ih _) fun previous => ?_
        cases previous <;> exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_sharedDigestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    HashOnly (sharedDigestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold sharedDigestSearch; exact hashOnly_pure _
  | succ fuel ih =>
    unfold sharedDigestSearch
    refine hashOnly_bind (hashOnly_digest _ _ _) fun output => ?_
    split
    · exact hashOnly_pure _
    · exact ih _
@[aesop safe apply] theorem hashOnly_signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (signPayload cache message) := by
  rw [ClaudeWCT.Bank.Paired.signPayload_factor]
  refine hashOnly_bind (hashOnly_privateNonce _) fun rho => ?_
  refine hashOnly_bind (hashOnly_sharedDigestSearch _ _ _ _) fun found => ?_
  rcases found with _ | ⟨counter,output⟩
  · exact hashOnly_pure _
  · exact ClaudeWCT.Bank.Paired.payHashOnly cache rho output
@[aesop safe apply] theorem hashOnly_sign (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    HashOnly (sign cache message) := by
  unfold sign
  refine hashOnly_bind (hashOnly_privateMac _) fun _ => ?_
  split
  · exact hashOnly_pure _
  · exact hashOnly_signPayload _ _
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (expand message pk sig) := by
  unfold expand expandFill
  split
  · exact hashOnly_pure _
  · refine hashOnly_bind (hashOnly_sharedDigestSearch _ _ _ _) fun found => ?_
    rcases found with _ | ⟨counter,output⟩
    · exact hashOnly_pure _
    · refine hashOnly_bind (hashOnly_recoverForest _ _ _ _) fun forest => ?_
      refine hashOnly_bind (hashOnly_recoverHintedLayers _ _ _ _ _ (conditionalTopFloor output)) fun layers => ?_
      cases layers
      · exact hashOnly_pure _
      · dsimp only
        split
        · exact hashOnly_pure _
        · split
          · exact hashOnly_pure _
          · refine hashOnly_bind (hashOnly_searchTop _ _ _ _ _ _) fun found => ?_
            cases found <;> exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_verifyLayers (w : Witness) (index n : Nat) (msg : LayerMsg) :
    HashOnly (verifyLayers w index n msg) := by
  induction n generalizing msg with
  | zero => unfold verifyLayers; exact hashOnly_pure _
  | succ n ih =>
    unfold verifyLayers
    dsimp only
    split
    · exact hashOnly_pure _
    · refine hashOnly_bind (hashOnly_verificationHash _ _ _) fun answer => ?_
      split
      · exact hashOnly_verifyTopN _ _ _ _
      · split
        · refine hashOnly_bind (hashOnly_recoverLayerPairGuard _ _ _ _ _) fun found => ?_
          cases found
          · exact hashOnly_pure _
          · exact ih _
        · exact hashOnly_pure _
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
    HashOnly (verify message pk w) := by
  unfold verify
  split
  · exact hashOnly_pure _
  · refine hashOnly_bind (hashOnly_digest _ _ _) fun output => ?_
    split
    · exact hashOnly_pure _
    · refine hashOnly_bind (hashOnly_recoverForest _ _ _ _) fun forest => ?_
      refine hashOnly_bind (hashOnly_verifyLayers _ _ _ _) fun root => ?_
      cases root <;> exact hashOnly_pure _
end SigGolfCandidate.Research.SharedForest

namespace ClaudeWCT.W9.T3.Completeness.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler

noncomputable def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness

noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true

theorem honestProgram_true (answers : Answers) (message : Message)
    (hcomplete : SigningComplete answers (evalWithAnswerFn answers keygen).2) (htree : TopTreeOK answers) :
    evalWithAnswerFn answers (honestProgram message)=true := by
  obtain ⟨sig,hs⟩ := hcomplete message
  have hc := keygen_correct answers
  obtain ⟨w,he,hv⟩ := sign_expands answers _ hc.2.1 htree message sig hs
  rw [←hc.1] at he hv
  simp only [honestProgram,evalWithAnswerFn_bind,hs,he,hv]

theorem hashOnly_honestProgram (message : Message) : HashOnly (honestProgram message) := by
  unfold honestProgram
  refine hashOnly_bind hashOnly_keygen fun keys => ?_
  refine hashOnly_bind (SigGolfCandidate.Research.SharedForest.hashOnly_sign keys.2 message) fun sig => ?_
  cases sig
  · exact hashOnly_pure _
  · refine hashOnly_bind (SigGolfCandidate.Research.SharedForest.hashOnly_expand _ _ _) fun witness => ?_
    cases witness
    · exact hashOnly_pure _
    · exact SigGolfCandidate.Research.SharedForest.hashOnly_verify _ _ _

theorem hashOnly_everyMessageProgram : HashOnly everyMessageProgram :=
  hashOnly_foldlM _ _ (fun _ message => hashOnly_bind (hashOnly_honestProgram message) fun _ => hashOnly_pure _) _

theorem everyMessageProgram_true_of_complete (answers : Answers)
    (hcomplete : SigningComplete answers (evalWithAnswerFn answers keygen).2) (htree : TopTreeOK answers) :
    evalWithAnswerFn answers everyMessageProgram=true := by
  have hall := fun message => honestProgram_true answers message hcomplete htree
  have hf : ∀ messages : List Message, ∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted)=accepted := by
    intro messages
    induction messages with
    | nil => intro accepted; rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons,evalWithAnswerFn_bind,evalWithAnswerFn_pure,hall,Bool.and_true]
      exact ih accepted
  exact hf _ true

/- img-v6: the failure bound and `source_completeness` moved to `Final/CompletenessV6.lean` (cap exhaustion). -/
end ClaudeWCT.W9.T3.Completeness.Paired


namespace SigGolfCandidate.Research.SharedSigningBudget
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.W9.T3.CanonicalSearch ClaudeWCT.W9.T3.PairRows
open ClaudeWCT.Numerics.CanonicalCompression
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def digestMoment : ENNReal := (ftsBound:ENNReal)/scale
noncomputable def postMoment : ENNReal := signingZ^112322*((ClaudeWCT.Numerics.TopZero.initialBound:ENNReal)/scale)
noncomputable def payloadMoment : ENNReal := signingZ^112324*tierDigestMoment
noncomputable def signingMoment : ENNReal := signingZ^2*payloadMoment

theorem digestMoment_ge_one : 1 ≤ digestMoment := by
  apply (ENNReal.toReal_le_toReal (by simp) (by unfold digestMoment scale; finiteness)).mp
  norm_num [digestMoment,ENNReal.toReal_div,ftsBound,scale]

theorem postMoment_ge_one : 1 ≤ postMoment := by
  apply one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
  apply (ENNReal.toReal_le_toReal (by simp) (by unfold scale; finiteness)).mp
  norm_num [ENNReal.toReal_div,ClaudeWCT.Numerics.TopZero.initialBound,scale]

theorem payloadMoment_ge_one : 1 ≤ payloadMoment :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    tierDigestMoment_ge_one

theorem digest_moment_step : signingZ*
    (SphincsSecurity.Completeness.failMass (DigestGeneric.decoder digestAccepted)*digestMoment+
      (1-SphincsSecurity.Completeness.failMass (DigestGeneric.decoder digestAccepted))) ≤ digestMoment := by
  have hfail : SphincsSecurity.Completeness.failMass (DigestGeneric.decoder digestAccepted)=
      1-(ftsNum:ENNReal)/ftsDen := by
    rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept,
      DigestGeneric.decoder_acceptance,ClaudeWCT.Bank.Paired.digestAccepted_acceptance_exact]
  rw [hfail]
  exact (mul_le_mul' signing_z_ratio le_rfl).trans fts_ratio_step

theorem V_sharedDigestSearch (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel≤2^32) (cache : RCache)
    (hfresh : ∀ c, counter≤c → c<2^32 → cache (digestTrial rho message c)=none) :
    V secret signingZ (sharedDigestSearch rho message counter fuel) cache ≤ digestMoment := by
  rw [sharedDigestSearch_eq_run]
  exact DigestGeneric.V_run digestAccepted secret signingZ digestMoment digestMoment_ge_one rho message
    digest_moment_step fuel counter hlimit cache hfresh

theorem signPayload_eq_weighted (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SharedForest.signPayload cache message =
      privateNonce message >>= fun rho =>
      sharedDigestSearch rho message 0 digestAttemptLimit >>= fun found =>
      match found with
      | none => pure none
      | some (counter, output) =>
          (fun w : Option Witness => w.map Witness.signature) <$>
            signFromOutput cache rho counter output := by
  unfold SharedForest.signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  cases found with
  | none => rfl
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      simp only [map_eq_bind_pure_comp, Function.comp_def]
      apply bind_congr
      intro witness
      cases witness <;> rfl

theorem V_signPayload_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache) :
    V secret signingZ (SharedForest.signPayload cache message) rcache ≤ payloadMoment := by
  calc
    _ ≤ signingZ^2 * (signingZ^112322 * tierDigestMoment) := by
      rw [signPayload_eq_weighted]
      apply SigGolfCandidate.T3.Budgets.V_bind_bounded secret signingZ
        (privateNonce message) _ rcache (signingZ^2)
        (signingZ^112322 * tierDigestMoment)
      · exact V_of_bound (bound_privateNonce message) secret signingZ
          (SigGolfCandidate.Budget.one_le_zOf _) rcache
      · intro nonce hn
        have hnonce := privateNonce_preserves_fresh secret message rcache hfresh nonce hn
        have hrows : RowsFreshFrom 0 nonce.2 := fun lay _ => hnonce.2 lay lay.isLt
        rw [sharedDigestSearch_eq_run]
        apply DigestGeneric.V_run_bind digestAccepted secret signingZ
          (signingZ^112322 * tierDigestMoment) nonce.1 message _
          (fun answer => signingZ^112322 *
            ((ClaudeWCT.Numerics.TopZero.tierInitialBound (conditionalExtra answer) : ENNReal)/scale))
        · intro rc _
          simpa only [V_pure] using
            (one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
              tierDigestMoment_ge_one)
        · intro rc hr c hc answer ha
          rw [V_map]
          exact V_signFromOutput_certified_tier secret cache nonce.1 (BitVec.ofNat 32 c)
            answer (rc.cacheQuery (digestTrial nonce.1 message c) answer)
            (hr.cacheDigest nonce.1 message c answer) ha
        · exact scaled_step signingZ tierDigestMoment (signingZ^112322)
            (DigestGeneric.decoder digestAccepted)
            (fun answer => (ClaudeWCT.Numerics.TopZero.tierInitialBound
              (conditionalExtra answer) : ENNReal)/scale)
            tier_digest_moment_step
        · exact (by have := ClaudeWCT.WCT9.digestAttemptLimit_le; omega)
        · exact hrows
        · exact fun c _ hc => hnonce.1 _ _ _ hc
    _ = payloadMoment := by
      rw [payloadMoment, ← mul_assoc, ← pow_add]
      rfl

theorem V_sign_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache) :
    V secret signingZ (SharedForest.sign cache message) rcache ≤ signingMoment := by
  apply V_sign_fixed secret signingZ payloadMoment (SigGolfCandidate.Budget.one_le_zOf _)
    payloadMoment_ge_one cache message rcache
  intro checked hc _
  exact V_signPayload_certified secret cache message checked.2
    (privateMac_preserves_fresh secret cache.region rcache hfresh checked hc)

theorem signingMoment_eq : signingMoment =
    signingZ^112326*tierDigestMoment := by
  unfold signingMoment payloadMoment
  rw [show 112326=2+112324 by decide,pow_add]
  ac_rfl

/-- The fixed sign cost proved for the current Lean scheme (`signingMoment_eq`: 2 + 2 + 112142 + 180; v6 lower
seed families: `prepared_roots_cost` 80821 = 81146 − 325; T51 top 4-leaf families: `bound_signTop` 180 = 16 + 152 + 12). -/
def schemeFixedSignCost : Nat := 112326

/-- img-v6 open obligation (opus-crumbs PORT v6 C): the scheme's proved fixed sign cost is at most the certified img-v6
value 112326 (`TopZero.fixedSignCost`). Discharged by `decide` once the lower 7-leaf / top 4-leaf seed-family scheme
ports land (they lower `bound_buildForest` / `prepared_roots_cost`); the v6 envelope has slack ≈ +100 compressions. -/
def SchemeFixedCostV6 : Prop := schemeFixedSignCost ≤ ClaudeWCT.Numerics.TopZero.fixedSignCost

/-- Discharged by the v6 seed-family scheme (r3-lean-seedfam). -/
theorem schemeFixedCostV6_holds : SchemeFixedCostV6 := by
  unfold SchemeFixedCostV6 schemeFixedSignCost ClaudeWCT.Numerics.TopZero.fixedSignCost
  decide

theorem signingMoment_le_two (hfix : SchemeFixedCostV6) : signingMoment ≤ 2 := by
  rw [signingMoment_eq]
  have hz := ENNReal.toReal_mono (by unfold zDen; finiteness) signing_z_ratio
  rw [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast] at hz
  apply (ENNReal.toReal_le_toReal (by unfold signingZ SigGolfCandidate.Budget.zOf scale; finiteness)
    (by simp)).mp
  simp only [tierDigestMoment, ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  have hz1 : 1 ≤ signingZ.toReal := by
    have h1 : (1:ENNReal) ≤ signingZ := SigGolfCandidate.Budget.one_le_zOf _
    have h := ENNReal.toReal_mono (by unfold signingZ SigGolfCandidate.Budget.zOf; finiteness) h1
    simpa only [ENNReal.toReal_one] using h
  have hfixed : signingZ.toReal^112326≤(ClaudeWCT.Numerics.TopZero.fixedBound:ℝ)/scale :=
    ((pow_le_pow_right₀ hz1 hfix).trans (pow_le_pow_left₀ ENNReal.toReal_nonneg hz _)).trans
      ClaudeWCT.Numerics.TopZero.fixed_ratio_bound
  calc
    _ ≤ ((ClaudeWCT.Numerics.TopZero.fixedBound:ℝ)/scale)*(((ftsBound:ℝ)/scale)*
        ((ClaudeWCT.Numerics.TopZero.mixedInitialBound:ℝ)/scale)) := by gcongr
    _ ≤ 2 := by
      norm_num [ClaudeWCT.Numerics.TopZero.fixedBound, ftsBound,
        ClaudeWCT.Numerics.TopZero.mixedInitialBound, scale]

theorem V_sign_le_two (hfix : SchemeFixedCostV6) (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (rcache : RCache) (hfresh : AllSearchesFreshBC rcache) :
    V secret signingZ (SharedForest.sign cache message) rcache ≤ 2 :=
  (V_sign_certified secret cache message rcache hfresh).trans (signingMoment_le_two hfix)

def honestSignCount (message : Message) : M (Option SharedForest.Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (SharedForest.sign keys.2 message)

theorem honest_sign_exponential_budget (hfix : SchemeFixedCostV6) (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result => (2:ENNReal)^((result.1.2:ℝ)/131072)) ≤ 2 := by
  rw [honestSignCount,SigGolfCandidate.T3.Sampling.roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h := V_sign_le_two hfix secret keys.1.2 message keys.2
    (keygen_fresh_from_empty_bc secret keys hkeys)
  simpa only [V,signingZ_pow] using h
end SigGolfCandidate.Research.SharedSigningBudget

section
namespace SigGolfCandidate.Research.SharedExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun)
open SigGolfCandidate.T3.Cost (countBlocks)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts eval_joint_cost_le)
open SigGolfCandidate.T3.SourceReplay (hashOnly_pure hashOnly_bind hashOnly_keygen)
open SigGolfCandidate.Research.SharedForest (hashOnly_sign hashOnly_expand)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
theorem joint_sign_exponential_budget (hfix : SigGolfCandidate.Research.SharedSigningBudget.SchemeFixedCostV6)
    (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.1 : ℝ) / 131072)) ≤ 2 := by
  refine le_trans ?_ (SigGolfCandidate.Research.SharedSigningBudget.honest_sign_exponential_budget hfix secret message)
  simp only [honestJointCounts, jointCounts, SigGolfCandidate.Research.SharedSigningBudget.honestSignCount,
    SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig, signCost⟩, rcache⟩
  cases sig with
  | none => simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
  | some sig =>
    simp only [SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
theorem hashOnly_honestJointCounts (message : Message) :
    SigGolfCandidate.T3.SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact hashOnly_pure _
  | some sig =>
    apply hashOnly_bind
      (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_expand message keys.1 sig))
    intro expanded
    exact hashOnly_pure _
/-- img-v6 obligations of the expand moment: the top-tree leaf prefix avoids the root children's trials (scheme,
`topPrefixOK`) and the numeric certificate N2b (r3k, `expandExcessNumeric_holds`). -/
structure ExpandV6Facts : Prop where
  top_prefix : ∀ secret, SigGolfCandidate.Research.SharedExpansionV6.TopPrefixOK secret
  numeric : SigGolfCandidate.Research.SharedExpansionV6.ExpandExcessNumeric19

theorem expandV6_facts (hnum : SigGolfCandidate.Research.SharedExpansionV6.ExpandExcessNumeric19) : ExpandV6Facts :=
  ⟨ClaudeWCT.W9.T3.TopMoment.topPrefixOK, hnum⟩

/-- **img-v6 expand moment (Hölder)**: `E[2^(N_e/2^20)] ≤ ‖2^(N_s/2^20)‖₈ · ‖2^((N_e ∸ N_s)/2^20)‖_{8/7} ≤ 2`;
the pointwise `expand ≤ 8·sign` is false for v6 (PORT v6 §E). -/
theorem honest_expand_exponential_budget (F : ExpandV6Facts) (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2 := by
  have hrest : ∀ levels, SigGolfCandidate.T3.SourceReplay.HashOnly
      (SigGolfCandidate.Research.SharedExpansionV6.keygenRest levels) := fun levels => by
    unfold SigGolfCandidate.Research.SharedExpansionV6.keygenRest
      SigGolfCandidate.Research.SharedExpansionV6.payloadTail maskedLevel pairedMask
    hashes
  have hS := joint_sign_exponential_budget SigGolfCandidate.Research.SharedSigningBudget.schemeFixedCostV6_holds
    secret message
  have hD := SigGolfCandidate.Research.SharedExpansionV6.expand_excess_moment secret message
    (fun cache => hashOnly_sign cache message) (fun pk sig => hashOnly_expand message pk sig) hrest
    (F.top_prefix secret) F.numeric
  exact ClaudeWCT.Arith.ExpectHolder.expand_moment_of_holder (roRun secret (honestJointCounts message) ∅)
    (fun r => r.1.1) (fun r => r.1.2) hS hD
theorem uniform_message_expand_exponential_budget (F : ExpandV6Facts) (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestJointCounts message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 1048576)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_expand_exponential_budget F secret message
end SigGolfCandidate.Research.SharedExpansionClosure
end

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (M Spec Cache Digest keygen)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand)
open ClaudeWCT.W9.T3M.Paired (submission expandN expandB verifyP witEnc witEncN)
open ClaudeWCT.W9.T3M.SharedCodec (sigBC sigDecC)

abbrev submission := ClaudeWCT.W9.T3M.Paired.submission
abbrev sigBC := ClaudeWCT.W9.T3M.SharedCodec.sigBC
abbrev sigDecC := ClaudeWCT.W9.T3M.SharedCodec.sigDecC
abbrev expandN := ClaudeWCT.W9.T3M.Paired.expandN
abbrev expandB := ClaudeWCT.W9.T3M.Paired.expandB
abbrev verifyP := ClaudeWCT.W9.T3M.Paired.verifyP
abbrev witEnc := ClaudeWCT.W9.T3M.Paired.witEnc
/-- img-v6: the honest expand output carries the top node nonces (`Paired.witEncN`). -/
abbrev witEncN := ClaudeWCT.W9.T3M.Paired.witEncN

 def verifyCycleBound : Nat := 6921
 def claimedC : Nat := 7007
 def DigestCapOk (hash : Hash) (m : Message) (w : Bytes 22012) : Prop :=
  SigGolfCandidate.Research.SharedForest.jointAccountingCost
    (hash (SigGolfCandidate.T3M.toQ (SigGolfCandidate.T3.pad64
      (SigGolfCandidate.T3.digestInput (wrho w) m (wdc w)))))≤777
 variable (I : Images)
 def KeygenRunCounts : Prop := ∀ sk : SecretKey,
  (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> (submission I).run .keygen sk=
    (fun p => (some ((p.1.1 : PublicKey),cacheB p.1.2),p.2.1,p.2.2)) <$> countBoth (mrealize sk keygen)
def KeygenRunWith : Prop := ∀ (hash : Hash) (sk : SecretKey),
  ((submission I).runWith hash .keygen sk).value =
      some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) ∧
    ((submission I).runWith hash .keygen sk).finished = true ∧
    ((submission I).runWith hash .keygen sk).cycles < CYCLE_LIMIT ∧
    ((submission I).runWith hash .keygen sk).hashCalls = (evalWithAnswerFn hash (countBoth (mrealize sk keygen))).2.1 ∧
    ((submission I).runWith hash .keygen sk).hashCompressions =
      (evalWithAnswerFn hash (countBoth (mrealize sk keygen))).2.2
 def SignRefines : Prop := ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> (submission I).run .sign (sk,cache,m)=
    (fun p => (p.1.map sigBC,p.2.1,p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))
 def SignTerminates : Prop := ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  ((submission I).runWith hash .sign (sk,cache,m)).finished=true ∧
    ((submission I).runWith hash .sign (sk,cache,m)).cycles<CYCLE_LIMIT
 def ExpandRefines : Prop := ∀ (m : Message) (pk : PublicKey) (s : Bytes 5195),
  (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> (submission I).run .expand (m,pk,s)=
    (fun p => (p.1.map (fun x => witEncN x.1 x.2),p.2.1,p.2.2)) <$>
      countBoth (mrealize 0 (expandN m pk (sigDecC s)))
 def ExpandTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5195),
  ((submission I).runWith hash .expand (m,pk,s)).finished=true ∧
    ((submission I).runWith hash .expand (m,pk,s)).cycles<CYCLE_LIMIT
 def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 22012),
  (fun r => (r.value,r.hashCalls)) <$> (submission I).run .verify (m,pk,w)=
    (fun p => (if p.1 then some () else none,p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
 def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22012),
  ((submission I).runWith hash .verify (m,pk,w)).finished=true ∧
    ((submission I).runWith hash .verify (m,pk,w)).cycles<CYCLE_LIMIT
 def VerifyAcceptCycles : Prop := ∀ (floors : SigGolfCandidate.T3.Layer→Nat),
  SigGolfCandidate.T3M.Verify.CreditFloors floors →
  ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22012),
  SigGolfCandidate.T3M.Verify.HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w) hash → DigestCapOk hash m w →
  ((submission I).runWith hash .verify (m,pk,w)).value.isSome=true →
    ((submission I).runWith hash .verify (m,pk,w)).cycles≤verifyCycleBound
 structure Pending : Prop where
  admissible : (submission I).Admissible
  keygen_run_counts : KeygenRunCounts I
  keygen_runWith : KeygenRunWith I
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I

end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (M Spec Cache Digest keygen)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand verify)
 def SourceCompleteness : Prop := ∀ secret : BitVec 256,
  1-1/(2:ENNReal)^128≤Pr[=true | (simulateQ SphincsSecurity.romImpl
    (SigGolfCandidate.T3.realize secret ClaudeWCT.W9.T3.Completeness.Paired.everyMessageProgram)).run' ∅]
 def SignMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
    (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount message) ∅)
    (fun result => (2:ENNReal)^((result.1.2:ℝ)/131072))≤2
 def ExpandMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
    (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts message) ∅)
    (fun result => (2:ENNReal)^((result.1.2:ℝ)/1048576))≤2
/-- img-v6 keygen budget (nonce trials make keygen's compressions random): the spec moment
`E[2^(countBlocks keygen / 2^20)] ≤ 2` in the random-oracle model (COMPUTED 1.99933317; proved separately). -/
def KeygenMoment : Prop := ∀ (secret : BitVec 256),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret (SigGolfCandidate.T3.Cost.countBlocks keygen) ∅)
    (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2
 structure SourceFacts : Prop where
  source_completeness : SourceCompleteness
  honest_sign_exponential_budget : SignMoment
  honest_expand_exponential_budget : ExpandMoment
  honest_keygen_exponential_budget : KeygenMoment
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ cache message, AllQueriesSatisfy (sign cache message) isHash
  hashOnly_expand : ∀ message pk sig, AllQueriesSatisfy (expand message pk sig) isHash
  hashOnly_verify : ∀ message pk witness, AllQueriesSatisfy (verify message pk witness) isHash
  securityP : SecurityP
end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 (Cache Digest)
open SigGolfCandidate.T3M (isHash isPublic)
open SigGolfCandidate.Research.SharedForest (Signature Witness)

structure SourceQueriesData (p0 : Prop) (p1 : Prop) (p2 : Prop) (p3 : Prop) (p4 : Prop) (p5 : Prop) (p6 : Prop) (p7 : Prop) (p8 : Prop) (p9 : Prop) : Prop where
  good_sign : p0
  good_expand : p1
  good_verify : p2
  good_expandN : p3
  good_verifyP : p4
  public_expandN : p5
  public_expandB : p6
  public_verifyP : p7
  hashOnly_expandB : p8
  hashOnly_verifyP : p9

abbrev SourceQueries : Prop := SourceQueriesData
  (∀(cache : Cache)(message : SigGolfCandidate.T3.Message),
AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.sign cache message) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.expand message pk sig) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : Witness),
AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.verify message pk w) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandN message pk sig) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : WBytes),
AllQueriesSatisfy (verifyP message pk w) SigGolfCandidate.T3.Cost.GoodQuery)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandN message pk sig) isPublic)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandB message pk sig) isPublic)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : WBytes),
AllQueriesSatisfy (verifyP message pk w) isPublic)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(sig : Signature),
AllQueriesSatisfy (expandB message pk sig) isHash)
  (∀(message : SigGolfCandidate.T3.Message)(pk : Digest)(w : WBytes),
AllQueriesSatisfy (verifyP message pk w) isHash)
end ClaudeWCT.W9.T3M.Final.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_Layer ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M.Extract (canonicalHeader_high_irrelevant)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def layerChains (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainPW lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)
theorem layerLeafP_eq (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerLeafP w index lay digits =
      (layerChains w index lay digits >>= WCT9.leafHashW lay (route index lay).2 (route index lay).1 (wtopLeafPad w)
        (wleafHigh w lay)) := rfl
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
theorem merkleNodeInput_top (tree heap : Nat) (left right : Digest) :
    WCT9.merkleNodeInput 0 tree heap left right = nodeInputP 3 0 tree heap left 0 right := by
  unfold WCT9.merkleNodeInput nodeInputP block4
  rw [WCT9.merkleTweak_top, show bytesLE 16 (0 : Digest) = zero16 by decide]
/-- The honest input of a tree node (C2 lower trees, C4 top tree: the packed fold input `merkleInputW`; top-nonce
layer: the honest pads are the keygen nonce digests, 0 on lower trees). -/
theorem merkle_honestInputW' (answers : Answers) (lay : Layer) (tree leaf step : Nat) :
    honestInput answers (.node lay tree step (leaf / 2 ^ (step + 1))) =
      pad64 (merkleInputW lay.val tree (height lay) leaf
        (fun j => treeValue (wotsTree answers lay tree) j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0)
        (honestPads answers lay tree leaf) step
        (treeValue (wotsTree answers lay tree) step (leaf / 2 ^ step))) := by
  unfold merkleInputW honestInput honestPads
  dsimp only
  rw [Correctness.sibling_pair (fun n => treeValue (wotsTree answers lay tree) step n) (leaf / 2 ^ step),
    Correctness.div_pow_succ, WCT9.merkleNodeInputN_eq_lowerNodeInputP]
theorem merkle_honestInputW (answers : Answers) (lay : Layer) (hlay : lay.val ≠ 0) (tree leaf step : Nat) :
    honestInput answers (.node lay tree step (leaf / 2 ^ (step + 1))) =
      pad64 (merkleInputW lay.val tree (height lay) leaf
        (fun j => treeValue (wotsTree answers lay tree) j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0) (fun _ => 0) step
        (treeValue (wotsTree answers lay tree) step (leaf / 2 ^ step))) := by
  rw [merkle_honestInputW', honestPads_lower answers (fun h => hlay (by rw [h]; rfl))]
theorem hdrBlock_merkleInputW (lay tree h leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64)
    (pads : Nat → Digest) (step : Nat) (value : Digest) :
    hdrBlock (pad64 (merkleInputW lay tree h leaf path hpads pads step value)) =
      bytesLE 16 (hpads step ++ WCT9.merkleWord lay tree (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1))) := by
  unfold merkleInputW
  dsimp only
  split <;> rw [pad64_lowerNodeInputP, WCT9.lowerNodeInputP, List.append_assoc] <;> exact hdrBlock_prefix _ _ _
theorem merkleInputW_length (lay tree h leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64)
    (pads : Nat → Digest) (step : Nat) (value : Digest) :
    (pad64 (merkleInputW lay tree h leaf path hpads pads step value)).length = 64 := by
  unfold merkleInputW
  dsimp only
  split <;> rw [pad64_lowerNodeInputP, lowerNodeInputP_length]
/-- C4: a top fold input carries the top label (`TopLow`: its low header word is `topNodeWord heap`). -/
theorem topLow_merkleInputW (tree h leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64)
    (pads : Nat → Digest) (step : Nat) (value : Digest) :
    TopLow (hdrBlock (pad64 (merkleInputW 0 tree h leaf path hpads pads step value))) := by
  rw [hdrBlock_merkleInputW, topLow_bytesLE_iff, tweakLow_eq_low, BitVec.extractLsb'_append_eq_right,
    WCT9.merkleWord_top, topNodeWord_toNat64]
  exact ⟨topNodeWord_pos _, lt_trans (topNodeWord_lt _) (by norm_num)⟩
/-- C4: two top fold inputs of the same step have the same decoding key (the key of a top label keeps only the low
word, which is the label `topNodeWord heap`). -/
theorem merkleInputW_sameHeader_top {tree h leaf step : Nat}
    (path path' : Nat → Digest) (hpads hpads' : Nat → BitVec 64) (pads pads' : Nat → Digest) (value value' : Digest) :
    SameHeader (pad64 (merkleInputW 0 tree h leaf path hpads pads step value))
      (pad64 (merkleInputW 0 tree h leaf path' hpads' pads' step value')) := by
  refine ⟨by rw [merkleInputW_length, merkleInputW_length], ?_⟩
  rw [hdrKey_of_top (merkleInputW_length ..) (topLow_merkleInputW ..),
    hdrKey_of_top (merkleInputW_length ..) (topLow_merkleInputW ..), hdrBlock_merkleInputW, hdrBlock_merkleInputW,
    SigGolfCandidate.T3M.Extract.bytesLE_header_words, SigGolfCandidate.T3M.Extract.bytesLE_header_words,
    List.take_left' (bytesLE_length 8 _), List.take_left' (bytesLE_length 8 _)]
/-- Two fold inputs of the same step have the same decoding key: on the lower trees the high tweak word is ignored
because the packed node word is marked (heap `< 128`), on the top tree (C4) because the label is `TopLow`. -/
theorem merkleInputW_sameHeader {lay tree h leaf step : Nat} (hh : 2 ^ (h - step - 1) + leaf / 2 ^ (step + 1) < 128)
    (path path' : Nat → Digest) (hpads hpads' : Nat → BitVec 64) (pads pads' : Nat → Digest) (value value' : Digest) :
    SameHeader (pad64 (merkleInputW lay tree h leaf path hpads pads step value))
      (pad64 (merkleInputW lay tree h leaf path' hpads' pads' step value')) := by
  by_cases h0 : lay = 0
  · subst h0; exact merkleInputW_sameHeader_top _ _ _ _ _ _ _ _
  refine ⟨by rw [merkleInputW_length, merkleInputW_length], ?_⟩
  have hm : ∀ heap, heap < 128 → 128 ≤ (WCT9.merkleWord lay tree heap).toNat % 256 := by
    intro heap hh'; rw [WCT9.merkleWord_lower h0, WCT9.lowerNodeWord_toNat hh']; omega
  have hn : ∀ (hp : BitVec 64), ¬ TopLow (bytesLE 16 (hp ++ WCT9.merkleWord lay tree
      (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1)))) := by
    intro hp ht
    generalize 2 ^ (h - step - 1) + leaf / 2 ^ (step + 1) = heap at hh ht
    rw [topLow_bytesLE_iff, tweakLow_eq_low, BitVec.extractLsb'_append_eq_right, WCT9.merkleWord_lower h0,
      WCT9.lowerNodeWord_toNat hh] at ht
    omega
  rw [hdrKey_of_len64 (merkleInputW_length ..) (by rw [hdrBlock_merkleInputW]; exact hn _),
    hdrKey_of_len64 (merkleInputW_length ..) (by rw [hdrBlock_merkleInputW]; exact hn _),
    hdrBlock_merkleInputW, hdrBlock_merkleInputW]
  apply canonicalHeader_high_irrelevant
  exact hm _ hh
theorem hdrBlock_merkleInput (tag lay tree h leaf : Nat) (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    hdrBlock (pad64 (merkleInput tag lay tree h leaf path pads step value)) =
      bytesLE 16 (nodeTweak tag lay tree (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1))) := by
  unfold merkleInput
  dsimp only
  split <;> rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4]
theorem merkleInput_length (tag lay tree h leaf : Nat) (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    (pad64 (merkleInput tag lay tree h leaf path pads step value)).length = 64 := by
  unfold merkleInput
  dsimp only
  split <;> simp only [nodeInputP, pad64_block4, block4_length]
theorem hdrBlock_chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) :
    hdrBlock (pad64 (chainInputP lay tree leaf i step pad0 pad1 headerPad value)) =
      bytesLE 16 (chainHeaderP lay tree leaf i step headerPad) := by
  rw [pad64_chainInputP, chainInputP_eq_block4, hdrBlock_block4]
private theorem canonicalHeader_replace_high (x : Digest) (pad : BitVec 64)
    (hb : 128 ≤ x.toNat % 256) :
    canonicalHeader (bytesLE 16 (pad ++ x.extractLsb' 0 64)) =
      canonicalHeader (bytesLE 16 x) := by
  have hl : 128 ≤ (x.extractLsb' 0 64).toNat % 256 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    omega
  have hx : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x :=
    BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := x)
  exact (canonicalHeader_high_irrelevant _ _ _ hl).trans
    (congrArg (fun y => canonicalHeader (bytesLE 16 y)) hx)
theorem canonicalHeader_chainHeaderP (lay : Layer) (tree leaf i step : Nat)
    (headerPad : BitVec 64) :
    canonicalHeader (bytesLE 16 (chainHeaderP lay tree leaf i step headerPad)) =
      canonicalHeader (bytesLE 16 (chainHeader lay tree leaf i step)) := by
  exact canonicalHeader_replace_high _ headerPad (SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i step)
theorem layerChains_queried (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (leaf tree : Nat) (hleaf : (route index lay).1 = leaf) (htree : (route index lay).2 = tree)
    (i : Nat) (hi : i < chainCount lay) :
    ∀ q ∈ queried answers (chainPW lay tree leaf i (digits.getD i 0)
        (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i)),
      q ∈ queried answers (layerChains w index lay digits) := by
  subst hleaf htree
  unfold layerChains
  exact queried_mapM_mem answers (fun i : Fin (chainCount lay) =>
    chainPW lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val))
        (List.finRange (chainCount lay)) ⟨i, hi⟩ (List.mem_finRange _)
theorem map_finRange_val {β : Type} (n : Nat) (g : Nat → β) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [show (fun i : Fin n => g i.val) = g ∘ Fin.val from rfl, ← List.map_map, map_val_finRange]
theorem route_tree_bound (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hidx (by norm_num))
theorem route_routed_bound (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  unfold route
  dsimp only
  generalize hb : ((![19, 12, 6, 0] : Layer → Nat) lay) = b
  have hd : index / 2 ^ (b + height lay) * 2 ^ height lay + index / 2 ^ b % 2 ^ height lay = index / 2 ^ b := by
    rw [pow_add, ← Nat.div_div_eq_div_mul]
    exact Nat.div_add_mod' _ _
  rw [hd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hidx (by norm_num))
theorem height_le (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
theorem width_le (lay : Layer) (i : Nat) : width lay i ≤ 3 := by unfold width; omega
/-- The chains and the leaf hash of a layer reach the honest WOTS root: either a hit, or the leaf pads are zero and
every chain starts from its honest value (with zero pads when it takes a step). -/
theorem layerLeaf_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (hv0 : evalWithAnswerFn answers (layerLeafP w index lay digits) =
      wotsRoot answers lay (route index lay).2 (route index lay).1) :
    HitIn answers (queried answers (layerLeafP w index lay digits)) ∨
      ((∀ i, i < chainCount lay →
        wvalueFor w lay digits i = wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        wleafHigh w lay = 0) := by
  classical
  by_cases hH : HitIn answers (queried answers (layerLeafP w index lay digits))
  · exact Or.inl hH
  right
  have hleafB := route_leaf_bound index lay
  have htreeB := route_tree_bound index lay hidx
  have hrouted := route_routed_bound index lay hidx
  have hqC : ∀ q ∈ queried answers (layerChains w index lay digits),
      q ∈ queried answers (layerLeafP w index lay digits) := by
    intro q hq
    rw [layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  generalize hleaf : (route index lay).1 = leaf at hleafB hrouted hv0 hH hqC ⊢
  generalize htree : (route index lay).2 = tree at htreeB hrouted hv0 hH hqC ⊢
  have htree31 : tree < 2 ^ 31 := by
    rw [← htree]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hleaf12 : leaf < 4096 :=
    lt_of_lt_of_le hleafB (Nat.pow_le_pow_right (by decide) (height_le lay))
  rw [layerLeafP_eq, evalWithAnswerFn_bind, hleaf, htree] at hv0
  have hends : evalWithAnswerFn answers (layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainPW lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i))) := by
    rw [layerChains, Correctness.eval_mapM, hleaf, htree]
    exact map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainPW lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalueFor w lay digits i)))
  rcases leafHashW_extract answers lay tree leaf (wtopLeafPad w) (wleafHigh w lay)
      (evalWithAnswerFn answers (layerChains w index lay digits))
      ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf))
      (by rw [hends]; simp) (by simp) hv0 with ⟨hE, hhi⟩ | ⟨hhit, hsame, hq⟩
  swap
  · exfalso
    apply hH
    refine ⟨.leaf lay tree leaf, _, ⟨hleafB, hrouted⟩, ?_, hhit, hsame⟩
    rw [layerLeafP_eq, queried_bind, hleaf, htree]
    exact List.mem_append_right _ hq
  refine ⟨?_, hhi⟩
  rw [hends] at hE
  have hE' := (List.map_inj_left).mp hE
  intro i hi
  have hd := hvalid i hi
  have hci := hE' i (List.mem_range.mpr hi)
  have hw : maxDigit lay i ≤ 7 := by unfold maxDigit; split_ifs <;> omega
  have hc := chainCount_le lay
  have hreach : pathValueW answers (fun s => WCT9.chainHigh lay i (digits.getD i 0 + s))
      (chainPathInputW lay tree leaf i (digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
        (wchainHeaderPad w lay i)) (wvalueFor w lay digits i) (maxDigit lay i - digits.getD i 0) =
      honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    unfold pathValueW
    rw [← chainPW_eq_hashPathW, hci, Nat.add_sub_cancel' hd]; rfl
  rcases chainPathW_extract answers lay tree leaf i _ _ _ _ _ _ _
      htree31 hleaf12 (by omega) (Or.inr (by omega)) hreach with
      ⟨hval, hpads⟩ | ⟨step, hstep, hq, hhit⟩
  · refine ⟨hval, fun hlt => ?_⟩
    obtain ⟨h0, h1, hh⟩ := hpads (by omega)
    exact ⟨Prod.ext h0 h1, hh⟩
  · exfalso
    apply hH
    have hs6 : digits.getD i 0 + step ≤ 6 := by omega
    refine ⟨.chain lay tree leaf i (digits.getD i 0 + step),
      pad64 (pathInputW answers (fun s => WCT9.chainHigh lay i (digits.getD i 0 + s))
        (chainPathInputW lay tree leaf i (digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i)) (wvalueFor w lay digits i) step),
      ⟨htree31, hleaf12, by omega, by omega⟩, ?_, ?_, ?_⟩
    · apply hqC
      apply layerChains_queried answers w index lay digits leaf tree hleaf htree i hi
      rw [chainPW_eq_hashPathW]; exact hq
    · rw [hashHitAt_iff]
      simp only [honestInput, Pos.high]
      exact hhit
    · refine SameHeader.of_canonical ?_ ?_ ?_
      · rw [honestInput_length, pathInputW, chainPathInputW, pad64_chainInputPW, chainInputPW_length]; simp [Pos.len]
      · rw [honestInput_length]; simp [Pos.len]
      simp only [honestInput]
      rw [pathInputW, chainPathInputW, pad64_chainInputPW, WCT9.chainInputW_padded]
      change canonicalHeader (((chainInputPW _ _ _ _ _ _ _ _ _).drop 16).take 16) =
        canonicalHeader (((WCT9.chainInputW _ _ _ _ _ _).drop 16).take 16)
      rw [chainInputPW_header, WCT9.chainInputW_header]
      exact canonicalHeader_chainHeaderP _ _ _ _ _ _
theorem foldlM_finRange_eq_hashPathW (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (count : Nat) (initial : Digest) :
    (List.finRange count).foldlM (fun value j => WCT9.halfHash (high j.val) (input j.val value)) initial =
      hashPathW high input count initial := by
  unfold hashPathW
  rw [← map_val_finRange count, List.foldlM_map]
/-- C4: `layerP` (every fold one-word, half by heap parity) as the leaf hash followed by a half-aware hash path of
`height lay` folds. -/
theorem layerP_eq_hashPathW (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = (layerLeafP w index lay digits >>= fun value =>
      hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
        (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (height lay) value) := by
  unfold layerP layerLeafP
  rcases route index lay with ⟨leaf, tree⟩
  dsimp only
  rw [bind_assoc]
  congr 1
  funext ends
  congr 1
  funext value
  rw [← foldlM_finRange_eq_hashPathW (merkleHighW lay.val (height lay) leaf)
    (merkleInputW lay.val tree (height lay) leaf (wpath w lay leaf) (wmerkleHigh w lay leaf) (wmerklePad w lay leaf))
    (height lay) value]
  rfl
/-- C4: the top layer's leaf hash and 12 folds as a half-aware hash path (`layerP` is stated for every layer). -/
theorem layerP_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hlay : lay = 0) (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) = honestRoot answers lay (route index lay).2) :
    HitIn answers (queried answers (layerP w index lay digits)) ∨ LayerShaped answers w index lay digits := by
  classical
  by_cases hH : HitIn answers (queried answers (layerP w index lay digits))
  · exact Or.inl hH
  right
  have hl0 : lay.val = 0 := by rw [hlay]; rfl
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits), q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)) (height lay)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [layerP_eq_hashPathW, queried_bind]
    exact List.mem_append_right _ hq
  have hleafB := route_leaf_bound index lay
  have htreeB := route_tree_bound index lay hidx
  have hM := merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay) (wpath w lay (route index lay).1)
    (fun j => treeValue (wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1 hleafB
      step hstep)
    (by
      have h := reaches
      rw [layerP_eq_hashPathW, evalWithAnswerFn_bind] at h
      unfold pathValueW
      rw [Nat.div_eq_of_lt hleafB]
      exact h)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hH
    refine ⟨.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)), pad64 (pathInputW answers
      (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (evalWithAnswerFn answers (layerLeafP w index lay digits)) step), ⟨htreeB, hstep, Or.inl hlay,
        fun _ => by subst hlay; exact route_top_tree index hidx, ?_⟩, hqM _ hq, ?_, ?_⟩
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [hashHitAt_iff, merkle_honestInputW' answers lay]; exact hhit
    · rw [merkle_honestInputW' answers lay, pathInputW, hl0]
      exact merkleInputW_sameHeader_top _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one, WCT9.wotsTree_leaf answers lay _ _ hleafB] at hv0
  rcases layerLeaf_extract answers w index lay digits hidx hvalid hv0 with hhit | ⟨hchains, hhi⟩
  · exact absurd (hhit.mono hqL) hH
  exact ⟨fun j hj => ⟨(hpath j hj).1, fun _ => (hpath j hj).2.2, fun _ => (hpath j hj).2.1⟩, hchains, hhi⟩

/-- The lower path of `layerPairP` as a half-aware hash path (C2). -/
theorem layerPairP_eq_hashPathW (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerPairP w index lay digits = (layerLeafP w index lay digits >>= fun value =>
      hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
        (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1
          (wpath w lay (route index lay).1) (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
        (height lay - 1) value >>= fun top =>
      pure (if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0
        then (top, wpath w lay (route index lay).1 (height lay - 1))
        else (wpath w lay (route index lay).1 (height lay - 1), top))) := by
  unfold layerPairP layerLeafP
  rcases route index lay with ⟨leaf, tree⟩
  dsimp only
  rw [bind_assoc]
  congr 1
  funext ends
  congr 1
  funext value
  rw [← foldlM_finRange_eq_hashPathW (merkleHighW lay.val (height lay) leaf)
    (merkleInputW lay.val tree (height lay) leaf (wpath w lay leaf) (wmerkleHigh w lay leaf) (wmerklePad w lay leaf))
    (height lay - 1) value]
  rfl
theorem height_pos (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem height_le7 {lay : Layer} (h0 : lay.val ≠ 0) : height lay ≤ 7 := by
  fin_cases lay <;> simp_all [height]
theorem lower_heap_lt128 {lay : Layer} (h0 : lay.val ≠ 0) {leaf step : Nat} (hleaf : leaf < 2 ^ height lay) :
    2 ^ (height lay - step - 1) + leaf / 2 ^ (step + 1) < 128 := by
  have h7 := height_le7 h0
  have hp : 2 ^ (height lay - step - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  have hl : leaf < 2 ^ 7 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by decide) h7)
  have hd : leaf / 2 ^ (step + 1) ≤ leaf / 2 := Nat.div_le_div_left (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (step + 1) := Nat.pow_le_pow_right (by decide) (by omega)) (by decide)
  have h64 : (2 : Nat) ^ 6 = 64 := by norm_num
  have h128 : (2 : Nat) ^ 7 = 128 := by norm_num
  omega
theorem layerPairP_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (hlay : lay.val ≠ 0)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) = honestPair answers lay (route index lay).2) :
    HitIn answers (queried answers (layerPairP w index lay digits)) ∨ LayerShaped answers w index lay digits := by
  classical
  by_cases hH : HitIn answers (queried answers (layerPairP w index lay digits))
  · exact Or.inl hH
  right
  have hh := height_pos lay
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [layerPairP_eq_hashPathW, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)) (height lay - 1)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [layerPairP_eq_hashPathW, queried_bind, queried_bind]
    exact List.mem_append_right _ (List.mem_append_left _ hq)
  have hleafB := route_leaf_bound index lay
  have htreeB := route_tree_bound index lay hidx
  have hq2 : (route index lay).1 / 2 ^ (height lay - 1) = 0 ∨ (route index lay).1 / 2 ^ (height lay - 1) = 1 := by
    have hq : (route index lay).1 / 2 ^ (height lay - 1) < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      have he : 2 ^ (height lay - 1) * 2 = 2 ^ height lay := by rw [← pow_succ, Nat.sub_add_cancel hh]
      rw [Nat.mul_comm, he]
      exact hleafB
    generalize (route index lay).1 / 2 ^ (height lay - 1) = q at hq ⊢
    omega
  rw [layerPairP_eq_hashPathW, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at reaches
  generalize htop : evalWithAnswerFn answers (hashPathW (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)) (height lay - 1)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))) = top at reaches
  have hpair : top = treeValue (wotsTree answers lay (route index lay).2) (height lay - 1)
        ((route index lay).1 / 2 ^ (height lay - 1)) ∧
      wpath w lay (route index lay).1 (height lay - 1) =
        treeValue (wotsTree answers lay (route index lay).2) (height lay - 1)
          ((route index lay).1 / 2 ^ (height lay - 1) ^^^ 1) := by
    unfold honestPair at reaches
    rcases hq2 with h | h <;> simp only [h] at reaches ⊢ <;>
      simp only [Nat.one_mod, if_true, if_false, Prod.mk.injEq, one_ne_zero] at reaches <;>
      exact ⟨by first | exact reaches.1 | exact reaches.2, by first | exact reaches.2 | exact reaches.1⟩
  have hM := merklePathW_extract answers lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay - 1) (wpath w lay (route index lay).1)
    (fun j => treeValue (wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (wotsTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1)
    (honestPads answers lay (route index lay).2 (route index lay).1)
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => merkleInputW_wotsTree_reference answers lay (route index lay).2 (route index lay).1 hleafB
      step (by omega))
    (by unfold pathValueW; rw [htop]; exact hpair.1)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hH
    refine ⟨.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)), pad64 (pathInputW answers
      (merkleHighW lay.val (height lay) (route index lay).1)
      (merkleInputW lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
        (wmerkleHigh w lay (route index lay).1) (wmerklePad w lay (route index lay).1))
      (evalWithAnswerFn answers (layerLeafP w index lay digits)) step), ⟨htreeB, by omega, Or.inr (by omega),
        fun hl => by subst hl; exact route_top_tree index hidx, ?_⟩, hqM _ hq, ?_, ?_⟩
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [hashHitAt_iff, merkle_honestInputW' answers lay]; exact hhit
    · rw [merkle_honestInputW' answers lay, pathInputW]
      exact merkleInputW_sameHeader (lower_heap_lt128 hlay hleafB) _ _ _ _ _ _ _ _
  rw [pow_zero, Nat.div_one, WCT9.wotsTree_leaf answers lay _ _ hleafB] at hv0
  rcases layerLeaf_extract answers w index lay digits hidx hvalid hv0 with hhit | ⟨hchains, hhi⟩
  · exact absurd (hhit.mono hqL) hH
  refine ⟨fun j hj => ?_, hchains, hhi⟩
  by_cases hjt : j < height lay - 1
  · exact ⟨(hpath j hjt).1, fun _ => (hpath j hjt).2.2, fun _ => (hpath j hjt).2.1⟩
  · have hj1 : j = height lay - 1 := by omega
    subst hj1
    exact ⟨hpair.2, fun h => by omega, fun h => by omega⟩

end ClaudeWCT.W9.T3M.Extract
namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-- Zero chain pads: the verifier chain is the honest chain of the current scheme. -/
theorem chainPW_zero_route (index : Nat) (lay : Layer) (i : Fin (chainCount lay))
    (digit : Nat) (value : Digest) (hindex : index < 2 ^ 31) :
    chainPW lay (route index lay).2 (route index lay).1 i.val digit (maxDigit lay i.val - digit) 0 0 0 value =
      WCT9.chainW lay (route index lay).2 (route index lay).1 i.val digit (maxDigit lay i.val - digit) value := by
  have hi := i.isLt
  have ht : (route index lay).2 < 2 ^ 31 := by fin_cases lay <;> simp [route, height] <;> omega
  have hl : (route index lay).1 < 4096 := by fin_cases lay <;> simp [route, height] <;> omega
  have hi64 : i.val < 64 := by have := chainCount_le lay; omega
  have hm : maxDigit lay i.val ≤ 7 := by unfold maxDigit; split_ifs <;> decide
  unfold chainPW WCT9.chainW
  apply WCT9.foldlM_congr_of_mem
  intro s hs v
  rw [List.mem_range'_1] at hs
  rw [chainInputW_eq_zero _ _ _ _ _ _ ht hl hi64 (by omega)]
/-- Zero leaf pads: the verifier leaf hash is the honest one. -/
theorem leafHashW_shaped {lay : Layer} {tree leaf : Nat} {pad : Digest} {hi : BitVec 64} (hh : hi = 0)
    (ends : List Digest) :
    WCT9.leafHashW lay tree leaf pad hi ends = WCT9.lowerLeafHash lay tree leaf ends := by
  -- T51 ("endpad"): `leafInputW` never reads `pad`
  subst hh
  rfl

theorem layerP_shaped_core (answers : Answers) (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (hlay : lay.val = 0) (hs : LayerShaped answers w (WCT9.digestIndex N) lay digits)
    -- Top-nonce layer (r3-lean-nonsec): the legacy `recoverLayer` hashes zero node pads; the img-v6 witness interface
    -- (HonestN) supplies this, or replaces this lemma by its nonce-reading top verifier.
    (hpad : ∀ j, j < height lay → wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j = 0) :
    layerP w (WCT9.digestIndex N) lay digits =
      recoverLayer (WCT9.toT3Signature (effectiveSignature (witDecP N w).signature (padDecP N w) digits)) (WCT9.digestIndex N) lay digits := by
  have hl0 : lay = 0 := Fin.ext hlay
  subst hl0
  have hpath : ∀ j : Fin (height 0), ((WCT9.toT3Signature (effectiveSignature (witDecP N w).signature (padDecP N w) digits)).layers 0).path j =
      wpath w 0 (route (WCT9.digestIndex N) 0).1 j.val := fun _ => rfl
  have hvals : ∀ i : Fin (chainCount 0),
      ((WCT9.toT3Signature (effectiveSignature (witDecP N w).signature (padDecP N w) digits)).layers 0).values i = wvalueFor w 0 digits i.val :=
    fun i => valueP_dec N w 0 digits i
  have hindex : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
  -- Witness stack: zero pads give the top chain of the current scheme (`chainW 0 0 = topChain = layChain 0`).
  have hzero : ∀ (i : Fin (chainCount 0)) (digit : Nat) (value : Digest),
      chainPW 0 (route (WCT9.digestIndex N) 0).2 (route (WCT9.digestIndex N) 0).1 i.val digit
        (maxDigit 0 i.val - digit) 0 0 0 value =
      layChain 0 (route (WCT9.digestIndex N) 0).2 (route (WCT9.digestIndex N) 0).1 i.val digit
        (maxDigit 0 i.val - digit) value := by
    intro i digit value
    rw [chainPW_zero_route _ 0 i digit value hindex, route_top_tree _ hindex, WCT9.chainW_top_eq, layChain_top]
  have hleaf := leafHashW_shaped (lay := 0) (tree := (route (WCT9.digestIndex N) 0).2)
    (leaf := (route (WCT9.digestIndex N) 0).1) (pad := wtopLeafPad w) hs.2.2
  unfold layerP recoverLayer
  simp only [hpath, hvals, hleaf, WCT9.lowerLeafHash_top]
  have hmz : ∀ j : Fin (height 0), wmerklePad w 0 (route (WCT9.digestIndex N) 0).1 j.val = 0 :=
    fun j => hpad j.val j.isLt
  have hmh : ∀ j : Fin (height 0), wmerkleHigh w 0 (route (WCT9.digestIndex N) 0).1 j.val = 0 :=
    fun j => (hs.1 j.val j.isLt).2.2 (Or.inr hlay)
  generalize hr : route (WCT9.digestIndex N) 0 = r at hs hzero hmz hmh ⊢
  obtain ⟨leaf, tree⟩ := r
  dsimp only at hs hzero hmz hmh ⊢
  have hchains : ((List.finRange (chainCount 0)).mapM fun i =>
      chainPW 0 tree leaf i.val (digits.getD i.val 0) (maxDigit 0 i.val - digits.getD i.val 0)
        (wchainPads w 0 i.val).1 (wchainPads w 0 i.val).2
        (wchainHeaderPad w 0 i.val) (wvalueFor w 0 digits i.val)) =
      ((List.finRange (chainCount 0)).mapM fun i =>
      layChain 0 tree leaf i.val (digits.getD i.val 0) (maxDigit 0 i.val - digits.getD i.val 0)
        (wvalueFor w 0 digits i.val)) := by
    congr 1
    funext i
    by_cases hd : digits.getD i.val 0 < maxDigit 0 i.val
    · rw [((hs.2.1 i.val i.isLt).2 hd).1, ((hs.2.1 i.val i.isLt).2 hd).2]
      exact hzero i _ _
    · have h0 : maxDigit 0 i.val - digits.getD i.val 0 = 0 := by omega
      rw [h0]
      rfl
  rw [hchains]
  congr 1
  funext ends
  congr 1
  funext value
  congr 1
  funext v j
  rw [hmz j, hmh j, ← WCT9.lowerNodeHash_eqP', Fin.val_zero, WCT9.lowerNodeHash_top]

theorem layerPairP_shaped_core (answers : Answers) (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (hs : LayerShaped answers w (WCT9.digestIndex N) lay digits) (hlay : lay.val ≠ 0) :
    layerPairP w (WCT9.digestIndex N) lay digits =
      WCT9.recoverLayerPair (effectiveSignature (witDecP N w).signature (padDecP N w) digits) (WCT9.digestIndex N) lay digits := by
  have hindex : WCT9.digestIndex N < 2 ^ 31 := WCT9.digestIndex_lt N
  have hzero := chainPW_zero_route (WCT9.digestIndex N) lay
  have hpath : ∀ j : Fin (height lay), ((effectiveSignature (witDecP N w).signature (padDecP N w) digits).layers lay).path j =
      wpath w lay (route (WCT9.digestIndex N) lay).1 j.val := fun _ => rfl
  have hvals : ∀ i : Fin (chainCount lay), ((effectiveSignature (witDecP N w).signature (padDecP N w) digits).layers lay).values i = wvalueFor w lay digits i.val :=
    fun i => valueP_dec N w lay digits i
  have hleaf := leafHashW_shaped (lay := lay) (tree := (route (WCT9.digestIndex N) lay).2)
    (leaf := (route (WCT9.digestIndex N) lay).1) (pad := wtopLeafPad w) hs.2.2
  unfold layerPairP WCT9.recoverLayerPair
  simp only [hpath, hvals, Fin.val_castLE, WCT9.topLevel, hleaf]
  have hmz : ∀ j : Fin (height lay - 1), wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val = 0 := by
    intro j
    have h := (hs.1 j.val (by omega)).2.1 (Or.inl (by omega))
    rwa [WCT9.honestNonce_lower answers (fun h0 => hlay (by rw [h0]; rfl)), WCT9.nonceDigest_zero] at h
  have hmh : ∀ j : Fin (height lay - 1), wmerkleHigh w lay (route (WCT9.digestIndex N) lay).1 j.val = 0 :=
    fun j => (hs.1 j.val (by omega)).2.2 (Or.inl (by omega))
  generalize hr : route (WCT9.digestIndex N) lay = r at hs hzero hmz hmh ⊢
  obtain ⟨leaf, tree⟩ := r
  dsimp only at hs hzero hmz hmh ⊢
  have hchains : ((List.finRange (chainCount lay)).mapM fun i =>
      chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
        (wchainHeaderPad w lay i.val) (wvalueFor w lay digits i.val)) =
      ((List.finRange (chainCount lay)).mapM fun i =>
      WCT9.chainW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wvalueFor w lay digits i.val)) := by
    refine congrArg (fun f => (List.finRange (chainCount lay)).mapM f) (funext fun i => ?_)
    by_cases hd : digits.getD i.val 0 < maxDigit lay i.val
    · rw [((hs.2.1 i.val i.isLt).2 hd).1, ((hs.2.1 i.val i.isLt).2 hd).2]
      exact hzero i _ _ hindex
    · have h0 : maxDigit lay i.val - digits.getD i.val 0 = 0 := by omega
      rw [h0]
      simp only [chainPW, WCT9.chainW, List.range'_zero, List.foldlM_nil]
  rw [hchains]
  congr 1
  funext ends
  congr 1
  funext value
  simp only [hmz, hmh, ← WCT9.lowerNodeHash_eqP hlay]

end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from ClaudeWCT_W9_T3M_Extract_Layers ====
section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem Diverge.mono {answers : Answers} {w : WBytes} {index : Nat} {lay : Layer} {qs qs' : List Spec.Domain}
    (h : Diverge answers w index lay qs) (hsub : ∀ q ∈ qs, q ∈ qs') : Diverge answers w index lay qs' := by
  obtain ⟨msg, digits, hfit, hne, hf, hs, hq⟩ := h
  exact ⟨msg, digits, hfit, hne, hf, hs, hsub _ hq⟩
theorem msgFits_honestMsg (answers : Answers) (index : Nat) (lay : Layer) :
    msgFits lay (honestMsg answers index lay) := by
  unfold honestMsg
  split <;> trivial
theorem ofNat_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt hn
theorem honestMsg_lower (answers : Answers) (index n : Nat) (h1 : 1 ≤ n) (h3 : n ≤ 3) :
    honestMsg answers index (Fin.ofNat 4 (n - 1)) =
      .pair (honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).1
        (honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).2 := by
  have hv : (Fin.ofNat 4 (n - 1) : Layer).val = n - 1 := ofNat_val _ (by omega)
  have hl : (⟨(Fin.ofNat 4 (n - 1) : Layer).val + 1, by omega⟩ : Layer) = Fin.ofNat 4 n := by
    apply Fin.ext
    show (Fin.ofNat 4 (n - 1) : Layer).val + 1 = (Fin.ofNat 4 n : Layer).val
    rw [hv, ofNat_val n (by omega)]
    omega
  unfold honestMsg
  rw [dif_pos (by rw [hv]; omega)]
  simp only [hl]
theorem honestMsg_three (answers : Answers) (index : Nat) :
    honestMsg answers index (Fin.ofNat 4 3) = .pair (honestTop answers index).1 (honestTop answers index).2 := by
  unfold honestMsg
  rw [dif_neg (by decide)]
private theorem queried_map_l {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem layersBC_succ_eq (w : WBytes) (index n : Nat) (msg : WCT9.LayerMsg) :
    layersBC w index (n + 1) msg =
      if (wbcCtr w index (Fin.ofNat 4 n)).toNat ≥ WCT9.verifyWindow then pure none else
      (ClaudeWCT.WCT9.encodingHash (Fin.ofNat 4 n) (layerEncodingInputP (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 msg (wbcCtr w index (Fin.ofNat 4 n)) (wbcPad w index (Fin.ofNat 4 n)) (wbcRight w)
          (wbcHigh w index (Fin.ofNat 4 n))) >>= fun answer =>
        if n = 0 then topLayerP w index answer
        else match decode (Fin.ofNat 4 n) answer with
          | some digits => layerGuardedPairP w index (Fin.ofNat 4 n) answer digits >>= fun pair =>
              match pair with
              | some pair => layersBC w index n (.pair pair.1 pair.2)
              | _ => pure none
          | _ => pure none) := by
  conv_lhs => unfold layersBC
  rfl
theorem layersBC_succ_split (answers : Answers) (w : WBytes) (index n : Nat) (msg : WCT9.LayerMsg) (out : Digest)
    (h : evalWithAnswerFn answers (layersBC w index (n + 1) msg) = some out) :
    ∃ digits, Frame answers w index (Fin.ofNat 4 n) msg digits ∧
      encodingQuery w index (Fin.ofNat 4 n) msg ∈ queried answers (layersBC w index (n + 1) msg) ∧
      (n = 0 → evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 n) digits) = out ∧
        ∀ q ∈ queried answers (layerP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layersBC w index (n + 1) msg)) ∧
      (n ≠ 0 →
        evalWithAnswerFn answers (layersBC w index n
          (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
            (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2)) = some out ∧
        (∀ q ∈ queried answers (layerPairP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layersBC w index (n + 1) msg)) ∧
        (∀ q ∈ queried answers (layersBC w index n
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2)),
          q ∈ queried answers (layersBC w index (n + 1) msg))) := by
  rw [layersBC_succ_eq] at h ⊢
  by_cases hc : (wbcCtr w index (Fin.ofNat 4 n)).toNat ≥ WCT9.verifyWindow
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h ⊢
  rw [evalWithAnswerFn_bind] at h
  rw [queried_bind]
  generalize hans : evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash (Fin.ofNat 4 n) (layerEncodingInputP (Fin.ofNat 4 n)
    (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg (wbcCtr w index (Fin.ofNat 4 n))
    (wbcPad w index (Fin.ofNat 4 n)) (wbcRight w) (wbcHigh w index (Fin.ofNat 4 n)))) = answer at h ⊢
  have hdig : ∃ digits, decode (Fin.ofNat 4 n) answer = some digits := by
    by_cases hn0 : n = 0
    · subst hn0
      simp only [if_true] at h
      exact decode_of_eval_topLayerP answers w index h
    · simp only [hn0, if_false] at h
      cases hd : decode (Fin.ofNat 4 n) answer with
      | none => rw [hd] at h; simp at h
      | some digits => exact ⟨digits, rfl⟩
  obtain ⟨digits, hd⟩ := hdig
  refine ⟨digits, ⟨by omega, by rw [hans]; exact hd⟩, ?_, ?_, ?_⟩
  · apply List.mem_append_left
    change encodingQuery w index (Fin.ofNat 4 n) msg ∈ [encodingQuery w index (Fin.ofNat 4 n) msg]
    exact List.mem_singleton_self _
  · intro hn0
    subst hn0
    simp only [if_true] at h ⊢
    rw [topLayerP_of_decode w index hd] at h ⊢
    rw [evalWithAnswerFn_map] at h
    refine ⟨Option.some.inj h, fun q hq => List.mem_append_right _ ?_⟩
    rw [queried_map_l]; exact hq
  · intro hn0
    simp only [hn0, if_false, hd] at h ⊢
    have hgood : WCT9.lowerRankGood answer := by
      rw [evalWithAnswerFn_bind] at h
      cases hp : evalWithAnswerFn answers (layerGuardedPairP w index (Fin.ofNat 4 n) answer digits) with
      | none => rw [hp] at h; simp at h
      | some pair => exact layerGuardedPairP_good_of_some answers w index (Fin.ofNat 4 n) answer digits pair hp
    rw [layerGuardedPairP_of_good w index (Fin.ofNat 4 n) answer digits hgood, bind_map_left] at h ⊢
    change evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits >>= fun pair =>
      layersBC w index n (.pair pair.1 pair.2)) = some out at h
    rw [evalWithAnswerFn_bind] at h
    refine ⟨h, fun q hq => ?_, fun q hq => ?_⟩
    · apply List.mem_append_right
      rw [queried_bind]; exact List.mem_append_left _ hq
    · apply List.mem_append_right
      rw [queried_bind]; exact List.mem_append_right _ hq
theorem layersBC_walk_n (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersBC w index n msg) = some (honestRoot answers 0 0) →
    HitIn answers (queried answers (layersBC w index n msg)) ∨
    (∃ lay : Layer, lay.val < n ∧ Diverge answers w index lay (queried answers (layersBC w index n msg)) ∧
      ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
    ((∀ l : Layer, l.val < n → Good answers w index l) ∧ msg = honestMsg answers index (Fin.ofNat 4 (n - 1)))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := layersBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := ofNat_val n (by omega)
      have hvalid := Cost.validDigits_decode hframe.2
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : HitIn answers (queried answers (layersBC w index (n + 1) msg)) ∨
          LayerShaped answers w index (Fin.ofNat 4 n) digits →
          (∀ l : Layer, l.val < n → Good answers w index l) →
          HitIn answers (queried answers (layersBC w index (n + 1) msg)) ∨
          (∃ lay : Layer, lay.val < n + 1 ∧
            Diverge answers w index lay (queried answers (layersBC w index (n + 1) msg)) ∧
            ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
          ((∀ l : Layer, l.val < n + 1 → Good answers w index l) ∧
            msg = honestMsg answers index (Fin.ofNat 4 n)) := by
        intro hx hgood
        rcases hx with hhit | hshape
        · exact Or.inl hhit
        by_cases heq : msg = honestMsg answers index (Fin.ofNat 4 n)
        · right; right
          refine ⟨fun l hl => ?_, heq⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact ⟨digits, heq ▸ hframe, hshape⟩
        · right; left
          exact ⟨Fin.ofNat 4 n, by omega, ⟨msg, digits, hfit, heq, hframe, hshape, henc⟩,
            fun l hl => hgood l (by omega)⟩
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, route_top_tree index hidx]
        refine finish ?_ (fun l hl => absurd hl (by omega))
        rcases layerP_extract answers w index (Fin.ofNat 4 0) digits rfl hidx hvalid hroot with hhit | hshape
        · exact Or.inl (hhit.mono hq)
        · exact Or.inr hshape
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := by
          trivial
        rcases layersBC_walk_n answers w index hidx n (by omega) (by omega) _ hfit' hrest with
          hhit | ⟨lay, hlay, hdiv, hgood⟩ | ⟨hgood, hmsg⟩
        · exact Or.inl (hhit.mono hqR)
        · exact Or.inr (Or.inl ⟨lay, by omega, hdiv.mono hqR, hgood⟩)
        · rw [honestMsg_lower answers index n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          refine finish ?_ hgood
          rcases layerPairP_extract answers w index (Fin.ofNat 4 n) digits hidx hvalid (by rw [hval]; exact hn0)
              hpair with hhit | hshape
          · exact Or.inl (hhit.mono hqP)
          · exact Or.inr hshape
theorem layersBC_walk (answers : Answers) (w : WBytes) (index : Nat) (root : Digest × Digest) (hidx : index < 2 ^ 31)
    (h : evalWithAnswerFn answers (layersBC w index 4 (.pair root.1 root.2)) = some (honestRoot answers 0 0)) :
    HitIn answers (queried answers (layersBC w index 4 (.pair root.1 root.2))) ∨
      (∃ lay : Layer, Diverge answers w index lay (queried answers (layersBC w index 4 (.pair root.1 root.2))) ∧
        ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
      ((∀ l : Layer, Good answers w index l) ∧ root = honestTop answers index) := by
  rcases layersBC_walk_n answers w index hidx 4 (by decide) le_rfl (.pair root.1 root.2) trivial h with
    hhit | ⟨lay, _, hdiv, hgood⟩ | ⟨hgood, hmsg⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl ⟨lay, hdiv, hgood⟩)
  · refine Or.inr (Or.inr ⟨fun l => hgood l l.isLt, ?_⟩)
    rw [show (4 - 1 : Nat) = 3 from rfl, honestMsg_three] at hmsg
    simp only [WCT9.LayerMsg.pair.injEq] at hmsg
    exact Prod.ext hmsg.1 hmsg.2
end ClaudeWCT.W9.T3M.Extract

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def CanonicalFrame (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg) (digits : List Nat) :
    Prop :=
  (wbcCtr w index lay).toNat < WCT9.verifyWindow ∧
    ClaudeWCT.WCT9.CanonicalPolicy.decode lay (evalWithAnswerFn answers (ClaudeWCT.WCT9.verificationHash lay (wtopHigh w) (layerEncodingInputP lay (route index lay).2 (route index lay).1
      msg (wbcCtr w index lay) (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay)))) = some digits

theorem queried_map_canonical {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p)=queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp

theorem layersCanonicalBC_succ_eq (w : WBytes) (index n : Nat) (msg : WCT9.LayerMsg) :
    layersCanonicalBC w index (n + 1) msg =
      if (wbcCtr w index (Fin.ofNat 4 n)).toNat ≥ WCT9.verifyWindow then pure none else
      (ClaudeWCT.WCT9.verificationHash (Fin.ofNat 4 n) (wtopHigh w) (layerEncodingInputP (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 msg (wbcCtr w index (Fin.ofNat 4 n)) (wbcPad w index (Fin.ofNat 4 n)) (wbcRight w)
          (wbcHigh w index (Fin.ofNat 4 n))) >>= fun answer =>
        if n = 0 then topLayerP w index answer
        else match ClaudeWCT.WCT9.CanonicalPolicy.decode (Fin.ofNat 4 n) answer with
          | some digits => layerGuardedPairP w index (Fin.ofNat 4 n) answer digits >>= fun pair =>
              match pair with
              | some pair => layersCanonicalBC w index n (.pair pair.1 pair.2)
              | _ => pure none
          | _ => pure none) := by
  conv_lhs => unfold layersCanonicalBC
  all_goals
    cases hr : route index (Fin.ofNat 4 n)
    simp only [hr] <;> rfl
theorem layersCanonicalBC_succ_split (answers : Answers) (w : WBytes) (index n : Nat) (msg : WCT9.LayerMsg) (out : Digest)
    (h : evalWithAnswerFn answers (layersCanonicalBC w index (n + 1) msg) = some out) :
    ∃ digits, CanonicalFrame answers w index (Fin.ofNat 4 n) msg digits ∧
      encodingQuery w index (Fin.ofNat 4 n) msg ∈ queried answers (layersCanonicalBC w index (n + 1) msg) ∧
      (n = 0 → evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 n) digits) = out ∧
        ∀ q ∈ queried answers (layerP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layersCanonicalBC w index (n + 1) msg)) ∧
      (n ≠ 0 →
        evalWithAnswerFn answers (layersCanonicalBC w index n
          (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
            (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2)) = some out ∧
        (∀ q ∈ queried answers (layerPairP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layersCanonicalBC w index (n + 1) msg)) ∧
        (∀ q ∈ queried answers (layersCanonicalBC w index n
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2)),
          q ∈ queried answers (layersCanonicalBC w index (n + 1) msg))) := by
  rw [layersCanonicalBC_succ_eq] at h ⊢
  by_cases hc : (wbcCtr w index (Fin.ofNat 4 n)).toNat ≥ WCT9.verifyWindow
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h ⊢
  rw [evalWithAnswerFn_bind] at h
  rw [queried_bind]
  generalize hans : evalWithAnswerFn answers (ClaudeWCT.WCT9.verificationHash (Fin.ofNat 4 n) (wtopHigh w) (layerEncodingInputP (Fin.ofNat 4 n)
    (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg (wbcCtr w index (Fin.ofNat 4 n))
    (wbcPad w index (Fin.ofNat 4 n)) (wbcRight w) (wbcHigh w index (Fin.ofNat 4 n)))) = answer at h ⊢
  have hdig : ∃ digits, ClaudeWCT.WCT9.CanonicalPolicy.decode (Fin.ofNat 4 n) answer = some digits := by
    by_cases hn0 : n = 0
    · subst hn0
      simp only [if_true] at h
      exact decode_of_eval_topLayerP answers w index h
    · simp only [hn0, if_false] at h
      cases hd : ClaudeWCT.WCT9.CanonicalPolicy.decode (Fin.ofNat 4 n) answer with
      | none => rw [hd] at h; simp at h
      | some digits => exact ⟨digits, rfl⟩
  obtain ⟨digits, hd⟩ := hdig
  refine ⟨digits, ⟨by omega, by rw [hans]; exact hd⟩, ?_, ?_, ?_⟩
  · apply List.mem_append_left
    change encodingQuery w index (Fin.ofNat 4 n) msg ∈ [encodingQuery w index (Fin.ofNat 4 n) msg]
    exact List.mem_singleton_self _
  · intro hn0
    subst hn0
    simp only [if_true] at h ⊢
    rw [topLayerP_of_decode w index hd] at h ⊢
    rw [evalWithAnswerFn_map] at h
    refine ⟨Option.some.inj h, fun q hq => List.mem_append_right _ ?_⟩
    rw [queried_map_canonical]; exact hq
  · intro hn0
    simp only [hn0, if_false, hd] at h ⊢
    have hgood : WCT9.lowerRankGood answer := by
      rw [evalWithAnswerFn_bind] at h
      cases hp : evalWithAnswerFn answers (layerGuardedPairP w index (Fin.ofNat 4 n) answer digits) with
      | none => rw [hp] at h; simp at h
      | some pair => exact layerGuardedPairP_good_of_some answers w index (Fin.ofNat 4 n) answer digits pair hp
    rw [layerGuardedPairP_of_good w index (Fin.ofNat 4 n) answer digits hgood, bind_map_left] at h ⊢
    change evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits >>= fun pair =>
      layersCanonicalBC w index n (.pair pair.1 pair.2)) = some out at h
    rw [evalWithAnswerFn_bind] at h
    refine ⟨h, fun q hq => ?_, fun q hq => ?_⟩
    · apply List.mem_append_right
      rw [queried_bind]; exact List.mem_append_left _ hq
    · apply List.mem_append_right
      rw [queried_bind]; exact List.mem_append_right _ hq

end ClaudeWCT.W9.T3M.Extract
end
-- ==== merged from W9Machine_WctChildContract ====
section

set_option autoImplicit false
namespace W9Machine.Child
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
def heapReg : Nat → Reg
  | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | 7 => .x30
  | _ => .x0
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  length : ends.length = 6
  pc : u.pc = pcOf (L.childWord j + 1)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (Chain.base L k)
  hashMode : u.getReg .x5 = 0
  hashInput : u.getReg .x10 = BitVec.ofNat 64 (Chain.base L k + 640)
  hashLen : u.getReg .x11 = 128
  nodeWord : u.getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 h
  leafAt : ∀ i, i < 8 → DigAt u (Chain.base L k + 640 + 16 * i)
    (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends i)
  padAt : ∀ l, l < 6 → DigAt u (Chain.base L k + V3.padOff j.val l) (V3.nodePad w k.val j.val l)
  sibAt : ∀ l, l < 6 → DigAt u (Chain.base L k + V3.sibOff j.val l) (V3.sibling w k.val j.val l)
  twAt : ∀ l, l < 6 → DigAt u (Chain.base L k + V3.blkOff j.val l + 16) (V3.nodeTw w k.val j.val l)
/-- Nested FTS hand-off: the computed top node of tree `k` lands at this address (high half of the heap-2/3 fold
output), the next region's leaf pad (bit 6 = 0) or Z slot (bit 6 = 1). Witness trim: for `k = 8` the virtual
region's slots are `WIT + 0` (`- 80`) and the R9 slot `WIT + 64` (`- 16`). -/
def handAddr (L : Layout) (k : Fin 9) (j : Fin 128) : Nat :=
  if k.val = 8 then (if j.val / 64 % 2 = 0 then Chain.base L k - 80 else Chain.base L k - 16)
  else if j.val / 64 % 2 = 0 then Chain.base L k - 176 else Chain.base L k - 32
def writes (L : Layout) (k : Fin 9) (j : Fin 128) (A : Nat) : Prop :=
  (Chain.base L k ≤ A ∧ A < Chain.base L k + 864) ∨ (handAddr L k j - 16 ≤ A ∧ A < handAddr L k j + 16)
def clobbers : List Reg := [.x3, .x10, .x11, .x12, .x14]
structure Post (L : Layout) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (computed : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (L.returnWord k + 74)
  hashLen : t.getReg .x11 = 64
  top : DigAt t (handAddr L k j) computed
  a2 : t.getReg .x12 = BitVec.ofNat 64 (handAddr L k j - 16)
  keep : ∀ r, r ∉ clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes L k j)
def Good (L : Layout) (b : Budget) (j : Fin 128) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (ends : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs),
    Pre L w index k j ends u →
    (∀ computed t, Post L k j u computed t → GoodQFor (P := P) L.image t N C Q A (K computed)) →
    GoodQFor (P := P) L.image u (N + b.fuel) (C + b.allCycles) Q (A + b.acceptCycles)
      (ccM (V3.childProgram w index k j ends) K)
end W9Machine.Child

namespace W9Machine.SharedChild
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  length : ends.length = 6
  pc : u.pc = pcOf (L.childWord j + 1)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (Chain.base L k)
  hashMode : u.getReg .x5 = 0
  hashInput : u.getReg .x10 = BitVec.ofNat 64 (Chain.base L k + 640)
  hashLen : u.getReg .x11 = 128
  nodeWord : u.getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  leafAt : ∀ i, i < 8 → DigAt u (Chain.base L k + 640 + 16 * i)
    (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends i)
  padAt : ∀ l, l < 6 → DigAt u (Chain.base L k + SharedV3.blkOff (SharedV3.physical k.val j.val) l + 32) (SharedV3.nodePad w k.val (SharedV3.physical k.val j.val) l)
  sibAt : ∀ l, l < 6 → DigAt u (Chain.base L k + SharedV3.sibOff (SharedV3.physical k.val j.val) l) (SharedV3.sibling w k.val (SharedV3.physical k.val j.val) l)
  twAt : ∀ l, l < 6 → DigAt u (Chain.base L k + SharedV3.blkOff (SharedV3.physical k.val j.val) l + 16) (SharedV3.nodeTw w k.val (SharedV3.physical k.val j.val) l)

/-- Where the computed top value lands: the next region's leaf pad (`- 176`, direction 0) or its R pad (`- 688` =
next region `+ 160`, direction 1); the final singleton (merged "Cm", stage 2) puts its left root on `WIT + 0`
(direction 0) and its right root on `WIT + 48` (direction 1); witness trim: `WIT = 4128 = coordinateBase 8 - 80`. -/
def handAddr (L : Layout) (k : Fin 9) (raw : Fin 128) : Nat :=
  if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0 then
    (if k.val = 8 then Chain.base L k - 80 else Chain.base L k - 176)
  else if k.val = 8 then Chain.base L k - 32 else Chain.base L k - 688

/-- Start of the 32-byte hash output carrying the computed top value: 16 bytes below the value for a high-half
value (every A/B child, and the singleton's left root, heap 2, stage 2 Cm: the junk low half lands on
`WIT - 16 .. WIT - 1`), at the value itself for the singleton's right root (heap 3, low half at `WIT + 48`). -/
def outputAddr (L : Layout) (k : Fin 9) (raw : Fin 128) : Nat :=
  if k.val = 8 then
    (if SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0 then handAddr L k raw - 16 else handAddr L k raw)
  else handAddr L k raw - 16

/-- Pairing stage 1: coordinate 0 (an A routine, levels `0..4`, no level-5 block) writes only
`[coordinateBase 0, + 784) = [10992, 11776)`, below the L1 layer at `WIT + 7664 = 11792`; the other regions keep
the 16-byte level-5 spill (`+ 864`). -/
def writes (L : Layout) (k : Fin 9) (raw : Fin 128) (A : Nat) : Prop :=
  (Chain.base L k ≤ A ∧ A < Chain.base L k + (if k.val = 0 then 784 else 864)) ∨
    (outputAddr L k raw ≤ A ∧ A < outputAddr L k raw + 32)

structure Post (L : Layout) (k : Fin 9) (raw : Fin 128) (u : MachineState)
    (computed : Digest) (t : MachineState) : Prop where
  /-- A/B return with `jalr zero,296(ra)`; the singleton (Cm, stage 2) with `jalr zero,320(ra)`, i.e. to word 854 for
  `returnWord 8 = 774`, the L3 entry. -/
  pc : t.pc = pcOf (L.returnWord k + (if k.val = 8 then 80 else 74))
  hashLen : t.getReg .x11 = 64
  top : DigAt t (handAddr L k raw) computed
  a2 : t.getReg .x12 = BitVec.ofNat 64 (outputAddr L k raw)
  keep : ∀ r, r ∉ Child.clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes L k raw)

/-- C1: every A routine fits its 32-word table slot, so no child takes the old spill jump. Kept (as 0) for the
interface of `cost`. -/
def spill (_k : Fin 9) (_raw : Fin 128) : Nat := 0

/-- C1 output offset (region-relative) of the hash computing the child-level-`m` value: `curO - 16` for a
high-half value (`SharedV3.hiOut`), `curO` otherwise. -/
def outOff (child m : Nat) : Nat :=
  SharedV3.blkOff child m + 48 * (child / 2 ^ m % 2) - (if SharedV3.hiOut child m then 16 else 0)

/-- C1 `skips′`: the elided `addi a2` words of a child routine (levels `0..3` whose output address equals the
previous one). The value depends only on `child % 32`; it is 0, 1 or 2 and sums to 42 over the 32 classes. -/
def skips (child : Nat) : Nat :=
  ((List.range 4).map fun l => if outOff child (l + 1) = outOff child l then 1 else 0).sum

/-- Exact cycles of a child routine: A `79 - skips′` (29 - skips′ instructions, seven hashed blocks), B and C
`91 - skips′` (34 - skips′ instructions, eight blocks). -/
def cost (k : Fin 9) (raw : Fin 128) : Nat :=
  (if SharedV3.first k.val then 79 else 91) - skips (SharedV3.physical k.val raw.val) + spill k raw

def Good (L : Layout) (k : Fin 9) (raw : Fin 128) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (ends : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs),
    Pre L w index k raw ends u →
    (∀ computed t, Post L k raw u computed t → GoodQFor (P := P) L.image t N C Q A (K computed)) →
    GoodQFor (P := P) L.image u (N + 39) (C + 96) Q (A + cost k raw)
      (ccM (SharedV3.childProgram w index k raw ends) K)
end W9Machine.SharedChild
end
-- ==== merged from W9Machine_WctChainContract ====
section

set_option autoImplicit false
namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
abbrev table := headerTable
abbrev program := V3.chainProgram
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 666) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  pc : u.pc = pcOf (L.chainWord rank)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (base L k)
  leafWord : u.getReg .x31 = BitVec.ofNat 64 (V3.leafLow index k.val j.val)
  nodeWord : u.getReg .x15 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  hashMode : u.getReg .x5 = 0
  stepOne : u.getReg .x7 = 1
  stepTwo : u.getReg .x13 = 2
  hashLen : u.getReg .x11 = 64
  childPC : u.getReg .x23 = pcOf (L.childWord j)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  witness : ∀ off, off < 848 → off % 8 = 0 →
    u.getMem (BitVec.ofNat 64 (base L k + off)) =
      w.extractLsb' (8 * (V3.regionOffset k.val + off)) 64
def writes (L : Layout) (k : Fin 9) (A : Nat) : Prop := base L k + 336 ≤ A ∧ A < base L k + 784
def clobbers : List Reg := [.x3, .x10, .x11, .x12, .x14, .x25]
structure Post (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (u : MachineState) (ends : List Digest) (t : MachineState) : Prop where
  length : ends.length = 6
  child : Child.Pre L w index k j ends t
  keep : ∀ r, r ∉ clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes L k)
def Good (L : Layout) (rank : Fin 666) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : List Digest → OracleComp HashSpec Obs),
    Pre L w index k j rank u →
    (∀ ends t, Post L w index k j u ends t → GoodQFor (P := P) L.image t N C Q A (K ends)) →
    GoodQFor (P := P) L.image u (N + 89) (C + 89) Q (A + 89)
      (ccM (program w index k j rank) K)
def AllGood (L : Layout) (P : Hash → Prop := HashOk) : Prop := ∀ rank : Fin 666, Good L rank (P := P)
end W9Machine.Chain
end
-- ==== merged from W9Machine_WctN600Contract ====
section

section

namespace W9Machine.N600
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def originalRanks : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,106,107,108,111,112,113,114,115,116,117,118,119,120,121,122,125,126,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,174,175,177,178,179,180,181,182,183,184,185,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,281,282,283,286,287,288,289,290,291,292,293,294,295,296,297,300,301,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,331,332,339,340,341,345,349,353,355,356,359,365,366,367,368,371,372,373,374,375,376,377,378,379,383,387,388,389,390,399,400,405,406,408,409,410,411,412,413,415,416,417,418,419,420,422,425,426,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,466,467,469,470,471,472,473,474,475,476,477,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,500,504,506,507,510,516,517,522,523,524,525,526,527,528,529,530,533,534,536,537,542,543,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,601,602,603,605,606,608,610,611,612,613,614,615,616,617,618,619,620,621,622,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665]
def rankCosts : List Nat := [76,76,79,79,79,79,80,80,79,79,79,80,79,79,79,79,79,79,83,83,83,81,82,82,81,82,82,83,82,82,82,82,82,82,82,81,82,82,83,83,82,83,82,83,82,82,83,83,83,83,83,82,83,82,83,79,82,83,82,82,83,82,82,82,83,82,83,82,83,79,79,82,82,82,83,81,82,82,83,79,83,83,83,85,86,86,85,86,86,87,86,86,86,86,86,86,86,85,86,85,86,86,85,85,84,84,84,85,85,85,84,85,84,85,82,85,86,85,85,86,85,86,86,85,86,82,82,85,85,85,86,84,85,85,86,82,82,84,85,85,85,82,82,83,83,82,86,85,86,85,85,86,86,86,86,86,85,86,85,86,83,86,87,86,86,86,85,86,86,85,86,82,83,86,86,86,87,86,86,87,83,83,85,86,86,86,83,82,86,83,79,82,83,82,82,86,85,85,85,86,85,86,85,86,82,83,86,86,86,86,84,85,85,86,82,83,85,86,86,86,83,82,86,83,79,79,82,82,82,86,84,85,85,86,82,83,85,86,85,85,82,82,86,83,79,79,79,79,81,82,82,81,82,82,83,82,82,82,82,82,82,82,81,82,85,86,86,85,85,84,84,84,85,85,85,84,85,84,85,82,85,86,85,85,86,85,86,86,85,86,82,82,85,85,85,86,84,85,85,86,82,82,84,85,85,85,82,85,86,86,85,89,88,89,88,89,85,88,87,87,84,85,88,85,85,87,88,85,84,88,85,82,85,86,85,85,88,88,89,85,86,85,86,86,85,86,82,82,85,85,85,87,88,88,89,85,86,89,85,85,86,82,82,84,85,88,88,85,85,89,85,82,78,79,79,78,82,81,82,81,81,82,82,82,82,82,81,82,81,82,82,85,86,85,85,85,84,85,85,84,85,81,82,85,85,85,86,85,85,86,82,82,84,85,85,85,82,81,85,82,82,85,86,85,85,88,88,85,85,88,84,85,85,84,88,85,81,82,85,85,85,88,88,85,86,85,85,86,82,82,84,85,88,88,85,85,89,85,82,81,85,85,82,75,78,79,78,78,82,81,81,81,82,81,82,81,82,78,82,85,85,85,85,83,84,84,85,81,82,84,85,85,85,82,81,85,82,78,82,85,85,85,87,88,88,85,85,88,87,84,84,88,85,81,82,84,85,88,88,85,85,85,82,81,85,85,82,78,75,78,78,78,82,80,81,81,82,78,82,84,85,84,84,81,81,85,82,78,82,84,85,88,88,85,84,88,84,81,81,85,85,82,78]
def oldRank (rank : Fin 563) : Nat := originalRanks.getD rank.val 0
def rankCost (rank : Fin 563) : Nat := rankCosts.getD rank.val 0
theorem oldRank_lt : ∀ rank : Fin 563, oldRank rank < 666 := by decide +kernel
def embed (rank : Fin 563) : Fin 666 := ⟨oldRank rank, oldRank_lt rank⟩
end W9Machine.N600
end

section


set_option autoImplicit false
namespace W9Machine.N600
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
abbrev Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 563) (u : MachineState) : Prop :=
  Chain.Pre L w index k j (embed rank) u
abbrev Post := Chain.Post
abbrev writes := Chain.writes
abbrev clobbers := Chain.clobbers
def program (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 563) : M (List Digest) :=
  V3.chainProgram w index k j (embed rank)
def Good (L : Layout) (rank : Fin 563) (P : Hash → Prop := HashOk) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : List Digest → OracleComp HashSpec Obs),
    Pre L w index k j rank u →
    (∀ ends t, Post L w index k j u ends t → GoodQFor (P := P) L.image t N C Q A (K ends)) →
    GoodQFor (P := P) L.image u (N + 89) (C + 89) Q (A + rankCost rank)
      (ccM (program w index k j rank) K)
def AllGood (L : Layout) (P : Hash → Prop := HashOk) : Prop := ∀ rank : Fin 563, Good L rank (P := P)
def NineCost (ranks : Fin 9 → Fin 563) : Nat :=
  ((List.finRange 9).map fun k => rankCost (ranks k)).sum
def JointCost (ranks : Fin 9 → Fin 563) (children : Fin 9 → Fin 128) : Nat :=
  NineCost ranks + ((List.finRange 9).map fun k => ClaudeWCT.WCT9.childExtra (children k)).sum
def ProducerCostOK (ranks : Fin 9 → Fin 563) (children : Fin 9 → Fin 128) : Prop :=
  JointCost ranks children ≤ 789
end W9Machine.N600
end
end
-- ==== merged from T3M_Verify_ChainRuns ====
section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
def lChunks : List (List (BitVec 32)) := [Images.verifyCode_0, Images.verifyCode_1, Images.verifyCode_2, Images.verifyCode_3, Images.verifyCode_4, Images.verifyCode_5, Images.verifyCode_6, Images.verifyCode_7, Images.verifyCode_8, Images.verifyCode_9, Images.verifyCode_10, Images.verifyCode_11, Images.verifyCode_12, Images.verifyCode_13, Images.verifyCode_14, Images.verifyCode_15, Images.verifyCode_16, Images.verifyCode_17, Images.verifyCode_18, Images.verifyCode_19, Images.verifyCode_20, Images.verifyCode_21, Images.verifyCode_22, Images.verifyCode_23, Images.verifyCode_24, Images.verifyCode_25, Images.verifyCode_26, Images.verifyCode_27, Images.verifyCode_28, Images.verifyCode_29, Images.verifyCode_30, Images.verifyCode_31, Images.verifyCode_32, Images.verifyCode_33, Images.verifyCode_34, Images.verifyCode_35, Images.verifyCode_36, Images.verifyCode_37, Images.verifyCode_38, Images.verifyCode_39, Images.verifyCode_40, Images.verifyCode_41, Images.verifyCode_42, Images.verifyCode_43, Images.verifyCode_44, Images.verifyCode_45, Images.verifyCode_46, Images.verifyCode_47, Images.verifyCode_48, Images.verifyCode_49, Images.verifyCode_50, Images.verifyCode_51, Images.verifyCode_52, Images.verifyCode_53, Images.verifyCode_54, Images.verifyCode_55, Images.verifyCode_56, Images.verifyCode_57, Images.verifyCode_58, Images.verifyCode_59, Images.verifyCode_60, Images.verifyCode_61, Images.verifyCode_62, Images.verifyCode_63, Images.verifyCode_64, Images.verifyCode_65, Images.verifyCode_66, Images.verifyCode_67, Images.verifyCode_68, Images.verifyCode_69, Images.verifyCode_70, Images.verifyCode_71, Images.verifyCode_72, Images.verifyCode_73, Images.verifyCode_74, Images.verifyCode_75, Images.verifyCode_76, Images.verifyCode_77, Images.verifyCode_78, Images.verifyCode_79, Images.verifyCode_80, Images.verifyCode_81, Images.verifyCode_82, Images.verifyCode_83, Images.verifyCode_84, Images.verifyCode_85, Images.verifyCode_86, Images.verifyCode_87, Images.verifyCode_88, Images.verifyCode_89, Images.verifyCode_90, Images.verifyCode_91, Images.verifyCode_92, Images.verifyCode_93, Images.verifyCode_94, Images.verifyCode_95, Images.verifyCode_96, Images.verifyCode_97, Images.verifyCode_98, Images.verifyCode_99, Images.verifyCode_100, Images.verifyCode_101, Images.verifyCode_102, Images.verifyCode_103, Images.verifyCode_104, Images.verifyCode_105, Images.verifyCode_106, Images.verifyCode_107, Images.verifyCode_108, Images.verifyCode_109, Images.verifyCode_110, Images.verifyCode_111, Images.verifyCode_112, Images.verifyCode_113, Images.verifyCode_114, Images.verifyCode_115, Images.verifyCode_116, Images.verifyCode_117, Images.verifyCode_118, Images.verifyCode_119, Images.verifyCode_120, Images.verifyCode_121, Images.verifyCode_122, Images.verifyCode_123, Images.verifyCode_124, Images.verifyCode_125, Images.verifyCode_126, Images.verifyCode_127, Images.verifyCode_128, Images.verifyCode_129, Images.verifyCode_130, Images.verifyCode_131, Images.verifyCode_132, Images.verifyCode_133, Images.verifyCode_134, Images.verifyCode_135, Images.verifyCode_136, Images.verifyCode_137, Images.verifyCode_138, Images.verifyCode_139, Images.verifyCode_140, Images.verifyCode_141, Images.verifyCode_142, Images.verifyCode_143, Images.verifyCode_144, Images.verifyCode_145, Images.verifyCode_146, Images.verifyCode_147, Images.verifyCode_148, Images.verifyCode_149, Images.verifyCode_150, Images.verifyCode_151, Images.verifyCode_152, Images.verifyCode_153, Images.verifyCode_154, Images.verifyCode_155, Images.verifyCode_156, Images.verifyCode_157, Images.verifyCode_158, Images.verifyCode_159, Images.verifyCode_160, Images.verifyCode_161, Images.verifyCode_162, Images.verifyCode_163, Images.verifyCode_164, Images.verifyCode_165, Images.verifyCode_166, Images.verifyCode_167, Images.verifyCode_168, Images.verifyCode_169, Images.verifyCode_170, Images.verifyCode_171, Images.verifyCode_172, Images.verifyCode_173, Images.verifyCode_174, Images.verifyCode_175, Images.verifyCode_176, Images.verifyCode_177, Images.verifyCode_178, Images.verifyCode_179, Images.verifyCode_180, Images.verifyCode_181, Images.verifyCode_182, Images.verifyCode_183, Images.verifyCode_184, Images.verifyCode_185, Images.verifyCode_186, Images.verifyCode_187, Images.verifyCode_188, Images.verifyCode_189, Images.verifyCode_190, Images.verifyCode_191, Images.verifyCode_192, Images.verifyCode_193, Images.verifyCode_194, Images.verifyCode_195, Images.verifyCode_196, Images.verifyCode_197, Images.verifyCode_198, Images.verifyCode_199, Images.verifyCode_200, Images.verifyCode_201, Images.verifyCode_202, Images.verifyCode_203, Images.verifyCode_204, Images.verifyCode_205, Images.verifyCode_206, Images.verifyCode_207, Images.verifyCode_208, Images.verifyCode_209, Images.verifyCode_210, Images.verifyCode_211, Images.verifyCode_212, Images.verifyCode_213, Images.verifyCode_214, Images.verifyCode_215, Images.verifyCode_216, Images.verifyCode_217, Images.verifyCode_218, Images.verifyCode_219, Images.verifyCode_220, Images.verifyCode_221, Images.verifyCode_222, Images.verifyCode_223, Images.verifyCode_224, Images.verifyCode_225, Images.verifyCode_226, Images.verifyCode_227, Images.verifyCode_228, Images.verifyCode_229, Images.verifyCode_230, Images.verifyCode_231, Images.verifyCode_232, Images.verifyCode_233, Images.verifyCode_234, Images.verifyCode_235, Images.verifyCode_236, Images.verifyCode_237, Images.verifyCode_238, Images.verifyCode_239, Images.verifyCode_240, Images.verifyCode_241, Images.verifyCode_242, Images.verifyCode_243, Images.verifyCode_244, Images.verifyCode_245, Images.verifyCode_246, Images.verifyCode_247, Images.verifyCode_248, Images.verifyCode_249, Images.verifyCode_250, Images.verifyCode_251, Images.verifyCode_252, Images.verifyCode_253, Images.verifyCode_254, Images.verifyCode_255, Images.verifyCode_256, Images.verifyCode_257, Images.verifyCode_258, Images.verifyCode_259, Images.verifyCode_260, Images.verifyCode_261, Images.verifyCode_262, Images.verifyCode_263, Images.verifyCode_264, Images.verifyCode_265, Images.verifyCode_266, Images.verifyCode_267, Images.verifyCode_268, Images.verifyCode_269, Images.verifyCode_270, Images.verifyCode_271, Images.verifyCode_272, Images.verifyCode_273, Images.verifyCode_274, Images.verifyCode_275, Images.verifyCode_276, Images.verifyCode_277, Images.verifyCode_278, Images.verifyCode_279, Images.verifyCode_280, Images.verifyCode_281, Images.verifyCode_282, Images.verifyCode_283, Images.verifyCode_284, Images.verifyCode_285, Images.verifyCode_286, Images.verifyCode_287, Images.verifyCode_288, Images.verifyCode_289, Images.verifyCode_290, Images.verifyCode_291, Images.verifyCode_292, Images.verifyCode_293, Images.verifyCode_294, Images.verifyCode_295, Images.verifyCode_296, Images.verifyCode_297, Images.verifyCode_298, Images.verifyCode_299, Images.verifyCode_300, Images.verifyCode_301, Images.verifyCode_302, Images.verifyCode_303, Images.verifyCode_304, Images.verifyCode_305, Images.verifyCode_306, Images.verifyCode_307, Images.verifyCode_308, Images.verifyCode_309, Images.verifyCode_310, Images.verifyCode_311, Images.verifyCode_312, Images.verifyCode_313, Images.verifyCode_314, Images.verifyCode_315, Images.verifyCode_316, Images.verifyCode_317, Images.verifyCode_318, Images.verifyCode_319, Images.verifyCode_320, Images.verifyCode_321, Images.verifyCode_322, Images.verifyCode_323, Images.verifyCode_324, Images.verifyCode_325, Images.verifyCode_326, Images.verifyCode_327, Images.verifyCode_328, Images.verifyCode_329, Images.verifyCode_330, Images.verifyCode_331, Images.verifyCode_332, Images.verifyCode_333, Images.verifyCode_334, Images.verifyCode_335, Images.verifyCode_336, Images.verifyCode_337, Images.verifyCode_338, Images.verifyCode_339, Images.verifyCode_340, Images.verifyCode_341, Images.verifyCode_342, Images.verifyCode_343, Images.verifyCode_344, Images.verifyCode_345, Images.verifyCode_346, Images.verifyCode_347, Images.verifyCode_348, Images.verifyCode_349, Images.verifyCode_350, Images.verifyCode_351, Images.verifyCode_352, Images.verifyCode_353, Images.verifyCode_354, Images.verifyCode_355, Images.verifyCode_356, Images.verifyCode_357, Images.verifyCode_358, Images.verifyCode_359, Images.verifyCode_360, Images.verifyCode_361, Images.verifyCode_362, Images.verifyCode_363, Images.verifyCode_364, Images.verifyCode_365, Images.verifyCode_366, Images.verifyCode_367, Images.verifyCode_368, Images.verifyCode_369, Images.verifyCode_370, Images.verifyCode_371, Images.verifyCode_372, Images.verifyCode_373, Images.verifyCode_374, Images.verifyCode_375, Images.verifyCode_376, Images.verifyCode_377, Images.verifyCode_378, Images.verifyCode_379, Images.verifyCode_380, Images.verifyCode_381, Images.verifyCode_382, Images.verifyCode_383, Images.verifyCode_384, Images.verifyCode_385, Images.verifyCode_386, Images.verifyCode_387, Images.verifyCode_388, Images.verifyCode_389, Images.verifyCode_390, Images.verifyCode_391, Images.verifyCode_392, Images.verifyCode_393, Images.verifyCode_394, Images.verifyCode_395, Images.verifyCode_396, Images.verifyCode_397, Images.verifyCode_398, Images.verifyCode_399, Images.verifyCode_400, Images.verifyCode_401, Images.verifyCode_402, Images.verifyCode_403, Images.verifyCode_404, Images.verifyCode_405, Images.verifyCode_406, Images.verifyCode_407, Images.verifyCode_408, Images.verifyCode_409, Images.verifyCode_410, Images.verifyCode_411, Images.verifyCode_412, Images.verifyCode_413, Images.verifyCode_414, Images.verifyCode_415, Images.verifyCode_416, Images.verifyCode_417, Images.verifyCode_418, Images.verifyCode_419, Images.verifyCode_420, Images.verifyCode_421, Images.verifyCode_422, Images.verifyCode_423, Images.verifyCode_424, Images.verifyCode_425, Images.verifyCode_426, Images.verifyCode_427, Images.verifyCode_428, Images.verifyCode_429, Images.verifyCode_430, Images.verifyCode_431, Images.verifyCode_432, Images.verifyCode_433, Images.verifyCode_434, Images.verifyCode_435, Images.verifyCode_436, Images.verifyCode_437, Images.verifyCode_438, Images.verifyCode_439, Images.verifyCode_440, Images.verifyCode_441, Images.verifyCode_442, Images.verifyCode_443, Images.verifyCode_444, Images.verifyCode_445, Images.verifyCode_446, Images.verifyCode_447, Images.verifyCode_448, Images.verifyCode_449, Images.verifyCode_450, Images.verifyCode_451, Images.verifyCode_452, Images.verifyCode_453, Images.verifyCode_454, Images.verifyCode_455, Images.verifyCode_456, Images.verifyCode_457, Images.verifyCode_458, Images.verifyCode_459, Images.verifyCode_460, Images.verifyCode_461, Images.verifyCode_462, Images.verifyCode_463, Images.verifyCode_464, Images.verifyCode_465, Images.verifyCode_466, Images.verifyCode_467, Images.verifyCode_468, Images.verifyCode_469, Images.verifyCode_470, Images.verifyCode_471, Images.verifyCode_472, Images.verifyCode_473, Images.verifyCode_474, Images.verifyCode_475, Images.verifyCode_476, Images.verifyCode_477, Images.verifyCode_478, Images.verifyCode_479, Images.verifyCode_480, Images.verifyCode_481, Images.verifyCode_482, Images.verifyCode_483, Images.verifyCode_484, Images.verifyCode_485, Images.verifyCode_486, Images.verifyCode_487, Images.verifyCode_488, Images.verifyCode_489, Images.verifyCode_490, Images.verifyCode_491, Images.verifyCode_492, Images.verifyCode_493, Images.verifyCode_494, Images.verifyCode_495, Images.verifyCode_496, Images.verifyCode_497, Images.verifyCode_498, Images.verifyCode_499, Images.verifyCode_500, Images.verifyCode_501, Images.verifyCode_502, Images.verifyCode_503, Images.verifyCode_504, Images.verifyCode_505, Images.verifyCode_506, Images.verifyCode_507, Images.verifyCode_508, Images.verifyCode_509, Images.verifyCode_510, Images.verifyCode_511, Images.verifyCode_512, Images.verifyCode_513, Images.verifyCode_514, Images.verifyCode_515, Images.verifyCode_516, Images.verifyCode_517, Images.verifyCode_518, Images.verifyCode_519, Images.verifyCode_520, Images.verifyCode_521, Images.verifyCode_522, Images.verifyCode_523, Images.verifyCode_524, Images.verifyCode_525, Images.verifyCode_526, Images.verifyCode_527, Images.verifyCode_528, Images.verifyCode_529, Images.verifyCode_530, Images.verifyCode_531, Images.verifyCode_532, Images.verifyCode_533, Images.verifyCode_534, Images.verifyCode_535, Images.verifyCode_536, Images.verifyCode_537, Images.verifyCode_538, Images.verifyCode_539, Images.verifyCode_540, Images.verifyCode_541, Images.verifyCode_542, Images.verifyCode_543, Images.verifyCode_544, Images.verifyCode_545, Images.verifyCode_546, Images.verifyCode_547, Images.verifyCode_548, Images.verifyCode_549, Images.verifyCode_550, Images.verifyCode_551, Images.verifyCode_552, Images.verifyCode_553, Images.verifyCode_554, Images.verifyCode_555, Images.verifyCode_556, Images.verifyCode_557, Images.verifyCode_558, Images.verifyCode_559, Images.verifyCode_560, Images.verifyCode_561, Images.verifyCode_562, Images.verifyCode_563, Images.verifyCode_564, Images.verifyCode_565, Images.verifyCode_566, Images.verifyCode_567, Images.verifyCode_568, Images.verifyCode_569, Images.verifyCode_570, Images.verifyCode_571, Images.verifyCode_572, Images.verifyCode_573, Images.verifyCode_574, Images.verifyCode_575, Images.verifyCode_576, Images.verifyCode_577, Images.verifyCode_578, Images.verifyCode_579, Images.verifyCode_580, Images.verifyCode_581, Images.verifyCode_582, Images.verifyCode_583, Images.verifyCode_584, Images.verifyCode_585, Images.verifyCode_586, Images.verifyCode_587, Images.verifyCode_588, Images.verifyCode_589, Images.verifyCode_590, Images.verifyCode_591, Images.verifyCode_592, Images.verifyCode_593, Images.verifyCode_594, Images.verifyCode_595, Images.verifyCode_596, Images.verifyCode_597, Images.verifyCode_598, Images.verifyCode_599, Images.verifyCode_600, Images.verifyCode_601, Images.verifyCode_602, Images.verifyCode_603, Images.verifyCode_604, Images.verifyCode_605, Images.verifyCode_606, Images.verifyCode_607, Images.verifyCode_608, Images.verifyCode_609, Images.verifyCode_610, Images.verifyCode_611, Images.verifyCode_612, Images.verifyCode_613, Images.verifyCode_614, Images.verifyCode_615, Images.verifyCode_616, Images.verifyCode_617, Images.verifyCode_618, Images.verifyCode_619, Images.verifyCode_620, Images.verifyCode_621, Images.verifyCode_622, Images.verifyCode_623, Images.verifyCode_624, Images.verifyCode_625, Images.verifyCode_626, Images.verifyCode_627, Images.verifyCode_628, Images.verifyCode_629, Images.verifyCode_630, Images.verifyCode_631, Images.verifyCode_632, Images.verifyCode_633, Images.verifyCode_634, Images.verifyCode_635, Images.verifyCode_636, Images.verifyCode_637, Images.verifyCode_638, Images.verifyCode_639, Images.verifyCode_640, Images.verifyCode_641, Images.verifyCode_642, Images.verifyCode_643, Images.verifyCode_644, Images.verifyCode_645, Images.verifyCode_646, Images.verifyCode_647, Images.verifyCode_648, Images.verifyCode_649, Images.verifyCode_650, Images.verifyCode_651, Images.verifyCode_652, Images.verifyCode_653, Images.verifyCode_654, Images.verifyCode_655, Images.verifyCode_656, Images.verifyCode_657, Images.verifyCode_658, Images.verifyCode_659, Images.verifyCode_660, Images.verifyCode_661, Images.verifyCode_662, Images.verifyCode_663, Images.verifyCode_664, Images.verifyCode_665, Images.verifyCode_666, Images.verifyCode_667, Images.verifyCode_668, Images.verifyCode_669, Images.verifyCode_670, Images.verifyCode_671, Images.verifyCode_672, Images.verifyCode_673, Images.verifyCode_674, Images.verifyCode_675, Images.verifyCode_676, Images.verifyCode_677, Images.verifyCode_678, Images.verifyCode_679, Images.verifyCode_680, Images.verifyCode_681, Images.verifyCode_682, Images.verifyCode_683, Images.verifyCode_684, Images.verifyCode_685, Images.verifyCode_686, Images.verifyCode_687, Images.verifyCode_688, Images.verifyCode_689, Images.verifyCode_690, Images.verifyCode_691, Images.verifyCode_692, Images.verifyCode_693, Images.verifyCode_694, Images.verifyCode_695, Images.verifyCode_696, Images.verifyCode_697, Images.verifyCode_698, Images.verifyCode_699, Images.verifyCode_700, Images.verifyCode_701, Images.verifyCode_702, Images.verifyCode_703, Images.verifyCode_704, Images.verifyCode_705, Images.verifyCode_706, Images.verifyCode_707, Images.verifyCode_708, Images.verifyCode_709, Images.verifyCode_710, Images.verifyCode_711, Images.verifyCode_712, Images.verifyCode_713, Images.verifyCode_714, Images.verifyCode_715, Images.verifyCode_716, Images.verifyCode_717, Images.verifyCode_718, Images.verifyCode_719, Images.verifyCode_720, Images.verifyCode_721, Images.verifyCode_722, Images.verifyCode_723, Images.verifyCode_724, Images.verifyCode_725, Images.verifyCode_726, Images.verifyCode_727, Images.verifyCode_728, Images.verifyCode_729, Images.verifyCode_730, Images.verifyCode_731, Images.verifyCode_732, Images.verifyCode_733, Images.verifyCode_734, Images.verifyCode_735, Images.verifyCode_736, Images.verifyCode_737, Images.verifyCode_738, Images.verifyCode_739, Images.verifyCode_740, Images.verifyCode_741, Images.verifyCode_742, Images.verifyCode_743, Images.verifyCode_744, Images.verifyCode_745, Images.verifyCode_746, Images.verifyCode_747, Images.verifyCode_748, Images.verifyCode_749, Images.verifyCode_750, Images.verifyCode_751, Images.verifyCode_752, Images.verifyCode_753, Images.verifyCode_754, Images.verifyCode_755, Images.verifyCode_756, Images.verifyCode_757, Images.verifyCode_758, Images.verifyCode_759, Images.verifyCode_760, Images.verifyCode_761, Images.verifyCode_762, Images.verifyCode_763, Images.verifyCode_764, Images.verifyCode_765, Images.verifyCode_766, Images.verifyCode_767, Images.verifyCode_768, Images.verifyCode_769, Images.verifyCode_770, Images.verifyCode_771, Images.verifyCode_772, Images.verifyCode_773, Images.verifyCode_774, Images.verifyCode_775, Images.verifyCode_776, Images.verifyCode_777, Images.verifyCode_778, Images.verifyCode_779, Images.verifyCode_780, Images.verifyCode_781, Images.verifyCode_782, Images.verifyCode_783, Images.verifyCode_784, Images.verifyCode_785, Images.verifyCode_786, Images.verifyCode_787, Images.verifyCode_788, Images.verifyCode_789, Images.verifyCode_790, Images.verifyCode_791, Images.verifyCode_792, Images.verifyCode_793, Images.verifyCode_794, Images.verifyCode_795, Images.verifyCode_796, Images.verifyCode_797, Images.verifyCode_798, Images.verifyCode_799, Images.verifyCode_800, Images.verifyCode_801, Images.verifyCode_802, Images.verifyCode_803, Images.verifyCode_804, Images.verifyCode_805, Images.verifyCode_806, Images.verifyCode_807, Images.verifyCode_808, Images.verifyCode_809, Images.verifyCode_810, Images.verifyCode_811, Images.verifyCode_812, Images.verifyCode_813, Images.verifyCode_814, Images.verifyCode_815, Images.verifyCode_816, Images.verifyCode_817, Images.verifyCode_818, Images.verifyCode_819, Images.verifyCode_820, Images.verifyCode_821, Images.verifyCode_822, Images.verifyCode_823, Images.verifyCode_824, Images.verifyCode_825, Images.verifyCode_826, Images.verifyCode_827, Images.verifyCode_828, Images.verifyCode_829, Images.verifyCode_830, Images.verifyCode_831, Images.verifyCode_832, Images.verifyCode_833, Images.verifyCode_834, Images.verifyCode_835, Images.verifyCode_836, Images.verifyCode_837, Images.verifyCode_838, Images.verifyCode_839, Images.verifyCode_840, Images.verifyCode_841, Images.verifyCode_842, Images.verifyCode_843, Images.verifyCode_844, Images.verifyCode_845, Images.verifyCode_846, Images.verifyCode_847, Images.verifyCode_848, Images.verifyCode_849, Images.verifyCode_850, Images.verifyCode_851, Images.verifyCode_852, Images.verifyCode_853, Images.verifyCode_854, Images.verifyCode_855, Images.verifyCode_856, Images.verifyCode_857, Images.verifyCode_858, Images.verifyCode_859, Images.verifyCode_860, Images.verifyCode_861, Images.verifyCode_862, Images.verifyCode_863, Images.verifyCode_864, Images.verifyCode_865, Images.verifyCode_866, Images.verifyCode_867, Images.verifyCode_868, Images.verifyCode_869, Images.verifyCode_870, Images.verifyCode_871, Images.verifyCode_872, Images.verifyCode_873, Images.verifyCode_874, Images.verifyCode_875, Images.verifyCode_876, Images.verifyCode_877, Images.verifyCode_878, Images.verifyCode_879, Images.verifyCode_880, Images.verifyCode_881, Images.verifyCode_882, Images.verifyCode_883, Images.verifyCode_884, Images.verifyCode_885, Images.verifyCode_886, Images.verifyCode_887, Images.verifyCode_888, Images.verifyCode_889, Images.verifyCode_890, Images.verifyCode_891, Images.verifyCode_892, Images.verifyCode_893, Images.verifyCode_894, Images.verifyCode_895, Images.verifyCode_896, Images.verifyCode_897, Images.verifyCode_898, Images.verifyCode_899, Images.verifyCode_900, Images.verifyCode_901, Images.verifyCode_902, Images.verifyCode_903, Images.verifyCode_904, Images.verifyCode_905, Images.verifyCode_906, Images.verifyCode_907, Images.verifyCode_908, Images.verifyCode_909, Images.verifyCode_910, Images.verifyCode_911, Images.verifyCode_912, Images.verifyCode_913, Images.verifyCode_914, Images.verifyCode_915, Images.verifyCode_916, Images.verifyCode_917, Images.verifyCode_918, Images.verifyCode_919, Images.verifyCode_920, Images.verifyCode_921, Images.verifyCode_922, Images.verifyCode_923, Images.verifyCode_924, Images.verifyCode_925, Images.verifyCode_926, Images.verifyCode_927, Images.verifyCode_928, Images.verifyCode_929, Images.verifyCode_930, Images.verifyCode_931, Images.verifyCode_932, Images.verifyCode_933, Images.verifyCode_934, Images.verifyCode_935, Images.verifyCode_936, Images.verifyCode_937, Images.verifyCode_938, Images.verifyCode_939, Images.verifyCode_940, Images.verifyCode_941, Images.verifyCode_942, Images.verifyCode_943, Images.verifyCode_944, Images.verifyCode_945, Images.verifyCode_946, Images.verifyCode_947, Images.verifyCode_948, Images.verifyCode_949, Images.verifyCode_950, Images.verifyCode_951, Images.verifyCode_952, Images.verifyCode_953, Images.verifyCode_954, Images.verifyCode_955, Images.verifyCode_956, Images.verifyCode_957, Images.verifyCode_958, Images.verifyCode_959, Images.verifyCode_960, Images.verifyCode_961, Images.verifyCode_962, Images.verifyCode_963, Images.verifyCode_964, Images.verifyCode_965, Images.verifyCode_966, Images.verifyCode_967, Images.verifyCode_968, Images.verifyCode_969, Images.verifyCode_970, Images.verifyCode_971, Images.verifyCode_972, Images.verifyCode_973, Images.verifyCode_974, Images.verifyCode_975, Images.verifyCode_976, Images.verifyCode_977, Images.verifyCode_978, Images.verifyCode_979, Images.verifyCode_980, Images.verifyCode_981, Images.verifyCode_982, Images.verifyCode_983, Images.verifyCode_984, Images.verifyCode_985, Images.verifyCode_986, Images.verifyCode_987, Images.verifyCode_988, Images.verifyCode_989, Images.verifyCode_990, Images.verifyCode_991, Images.verifyCode_992, Images.verifyCode_993, Images.verifyCode_994, Images.verifyCode_995, Images.verifyCode_996, Images.verifyCode_997, Images.verifyCode_998, Images.verifyCode_999, Images.verifyCode_1000, Images.verifyCode_1001, Images.verifyCode_1002, Images.verifyCode_1003, Images.verifyCode_1004]
def lcode (i : Nat) : List (BitVec 32) := ((lChunks.drop (i / 256)).flatten).drop (i % 256)
private theorem lChunks_eq_vChunks : lChunks = Verify.vChunks := rfl
theorem foldl_append_flatten' : ∀ (l : List (List (BitVec 32))) (a : List (BitVec 32)),
    l.foldl (· ++ ·) a = a ++ l.flatten
  | [], a => by simp
  | c :: l, a => by simp [foldl_append_flatten' l (a ++ c)]
set_option maxRecDepth 200000 in
theorem lChunks_foldl : Images.verifyCode = lChunks.foldl (· ++ ·) [] := by
  delta Images.verifyCode lChunks
  rfl
theorem lChunks_flatten : Images.verifyCode = lChunks.flatten := by
  rw [lChunks_foldl, foldl_append_flatten', List.nil_append]
set_option maxRecDepth 200000 in
theorem lChunks_ok : (lChunks.dropLast.all fun c => c.length == 256) = true := by
  exact (congrArg
    (fun cs : List (List (BitVec 32)) => cs.dropLast.all fun c => c.length == 256)
    lChunks_eq_vChunks).trans Verify.vChunks_ok
set_option maxRecDepth 200000 in
theorem lChunks_le : (lChunks.all fun c => decide (c.length ≤ 256)) = true := by
  exact (congrArg
    (fun cs : List (List (BitVec 32)) => cs.all fun c => decide (c.length ≤ 256))
    lChunks_eq_vChunks).trans Verify.vChunks_le
set_option maxRecDepth 200000 in
theorem lChunks_length : lChunks.length = 1005 := by decide +kernel
theorem drop_chunks' : ∀ (cs : List (List (BitVec 32))) (k : Nat),
    (cs.dropLast.all fun c => c.length == 256) = true → k < cs.length →
    cs.flatten.drop (256 * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show 256 * (k + 1) = c.length + 256 * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this
theorem flatten_len_le' : ∀ (cs : List (List (BitVec 32))),
    (cs.all fun c => decide (c.length ≤ 256)) = true → cs.flatten.length ≤ 256 * cs.length
  | [], _ => by simp
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have := flatten_len_le' cs h.2
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega
theorem verifyCode_length_le : Images.verifyCode.length ≤ 256 * 1005 := by
  rw [lChunks_flatten, ← lChunks_length]; exact flatten_len_le' _ lChunks_le
theorem lcode_eq (i : Nat) (hi : i / 256 < 1005) : lcode i = Images.verifyCode.drop i := by
  unfold lcode
  rw [lChunks_flatten, ← drop_chunks' lChunks (i / 256) lChunks_ok (by rw [lChunks_length]; exact hi),
    List.drop_drop]
  congr 1; omega
theorem lcodeAt (i : Nat) (hi : i < 257214) : CodeAt Images.verifyImage (pcOf i) (lcode i) := by
  have hl := verifyCode_length_le
  have hp : (pcOf i).toNat = 0x1000 + 4 * i := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  rw [lcode_eq i (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; omega
  · rw [hp]; omega
  · rw [hp, List.length_drop]; omega
  · rw [hp, show (0x1000 + 4 * i - 0x1000) / 4 = i by omega]
    exact List.prefix_refl _
def lstBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && lstBeq f as bs
  | _, _ => false
theorem lstBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, lstBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [lstBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [lstBeq] at h
    | cons b bs =>
      simp only [lstBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]
def rfBeq (a b : RegFile) : Bool := lstBeq E.beq a.fields b.fields
theorem rfBeq_eq {a b : RegFile} (h : rfBeq a b = true) : a = b := by
  have := lstBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl
def wBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2
theorem wBeq_eq {a b : Addr × E} (h : wBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [wBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]
def stBeq (a b : SymState) : Bool :=
  rfBeq a.regs b.regs && lstBeq wBeq a.mem b.mem && lstBeq Oblig.beq a.obl b.obl
theorem stBeq_eq {a b : SymState} (h : stBeq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [stBeq, Bool.and_eq_true] at h
  rw [rfBeq_eq h.1.1, lstBeq_eq (fun _ _ => wBeq_eq) h.1.2, lstBeq_eq (fun _ _ => Oblig.beq_eq) h.2]
def resBeq (a b : Result) : Bool :=
  stBeq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles
theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [stBeq_eq h1, E.beq_eq h2, h3, h4, h5]
def rOK (o : Option Result) (r : Result) : Bool :=
  match o with
  | some r' => resBeq r' r
  | none => false
theorem rOK_eq {o : Option Result} {r : Result} (h : rOK o r = true) : o = some r := by
  cases o with
  | none => simp [rOK] at h
  | some r' => simp only [rOK] at h; rw [resBeq_eq h]
def vrun (p f : Nat) : Option Result := symRun {} (lcode p) (pcOf p) f
def ttabIdx : Nat := 64072
def ckSlot (c : Nat) : Nat := 123085 + 1024 * c
def triBaseTab : List Nat :=
  [1189,2228,8374,4280,5306,6332,41151,16576,68798,28854,12472,17594,14524,15550,1277,21698,32950,53432,35002,22716,19646,20672,47299,26820,66754,39098,36028,37054,24768,25794,52421,126668,58553,44220,49342,57536,77388,118348,293,1445,55484,56510,103626,77516,118476,126796,129875,257181,45247,1533,51395,119244,455,185929,77354,777,118984,77644,118604,126924,1479,186056,102314,78936,131010,79034,3253,183,9401,10427,60605,61631,80059,7349,33975,13497,18619,11453,122054,42177,27829,65728,29881,30907,23741,64701,77772,78284,69823,38073,43195,31933,72902,46273,118732,122444,54457,113861,40125,76998,50369,97868,127308,549,129572,48317,78024,62657,97996,122572,129484,186025,63676,129956,78156,119116,127436,129617,187177,150144,150176,150220,150262,150302,150340,150376,150410,150442,150471,150530,150587,150642,150695,150746,150795,150842,150886,150943,150998,151051,151102,151151,151198,151243,151285,151340,151393,151444,151493,151540,151585,151628,151668,151721,151772,151821,151868,151913,151956,151997,152035,152086,152135,152182,152227,152270,152311,152350,152386,152435,152482,152527,152570,152611,152650,152687,152721,152768,152813,152856,152897,152936,152973,153008,153040,153084,153126,153166,153204,153240,153274,153306,153335,153394,153451,153506,153559,153610,153659,153706,153750,153807,153862,153915,153966,154015,154062,154107,154149,154204,154257,154308,154357,154404,154449,154492,154532,154585,154636,154685,154732,154777,154820,154861,154899,154950,154999,155046,155091,155134,155175,155214,155250,155299,155346,155391,155434,155475,155514,155551,155585,155632,155677,155720,155761,155800,155837,155872,155904,155948,155990,156030,156068,156104,156138,156170,156199,156258,156315,156370,156423,156474,156523,156570,156614,156671,156726,156779,156830,156879,156926,156971,157013,157068,157121,157172,157221,157268,157313,157356,157396,157449,157500,157549,157596,157641,157684,157725,157763,157814,157863,157910,157955,157998,158039,158078,158114,158163,158210,158255,158298,158339,158378,158415,158449,158496,158541,158584,158625,158664,158701,158736,158768,158812,158854,158894,158932,158968,159002,159034,159063,159122,159179,159234,159287,159338,159387,159434,159478,159535,159590,159643,159694,159743,159790,159835,159877,159932,159985,160036,160085,160132,160177,160220,160260,160313,160364,160413,160460,160505,160548,160589,160627,160678,160727,160774,160819,160862,160903,160942,160978,161027,161074,161119,161162,161203,161242,161279,161313,161360,161405,161448,161489,161528,161565,161600,161632,161676,161718,161758,161796,161832,161866,161898,161927,161986,162043,162098,162151,162202,162251,162298,162342,162399,162454,162507,162558,162607,162654,162699,162741,162796,162849,162900,162949,162996,163041,163084,163124,163177,163228,163277,163324,163369,163412,163453,163491,163542,163591,163638,163683,163726,163767,163806,163842,163891,163938,163983,164026,164067,164106,164143,164177,164224,164269,164312,164353,164392,164429,164464,164496,164540,164582,164622,164660,164696,164730,164762,164791,164850,164907,164962,165015,165066,165115,165162,165206,165263,165318,165371,165422,165471,165518,165563,165605,165660,165713,165764,165813,165860,165905,165948,165988,166041,166092,166141,166188,166233,166276,166317,166355,166406,166455,166502,166547,166590,166631,166670,166706,166755,166802,166847,166890,166931,166970,167007,167041,167088,167133,167176,167217,167256,167293,167328,167360,167404,167446,167486,167524,167560,167594,167626,167655,167714,167771,167826,167879,167930,167979,168026,168070,168127,168182,168235,168286,168335,168382,168427,168469,168524,168577,168628,168677,168724,168769,168812,168852,168905,168956,169005,169052,169097,169140,169181,169219,169270,169319,169366,169411,169454,169495,169534,169570,169619,169666,169711,169754,169795,169834,169871,169905,169952,169997,170040,170081,170120,170157,170192,170224,170268,170310,170350,170388,170424,170458,170490,170519,170578,170635,170690,170743,170794,170843,170890,170934,170991,171046,171099,171150,171199,171246,171291,171333,171388,171441,171492,171541,171588,171633,171676,171716,171769,171820,171869,171916,171961,172004,172045,172083,172134,172183,172230,172275,172318,172359,172398,172434,172483,172530,172575,172618,172659,172698,172735,172769,172816,172861,172904,172945,172984,173021,173056,173088,173132,173174,173214,173252,173288,173322,173354,173383,173442,173499,173554,173607,173658,173707,173754,173798,173855,173910,173963,174014,174063,174110,174155,174197,174252,174305,174356,174405,174452,174497,174540,174580,174633,174684,174733,174780,174825,174868,174909,174947,174998,175047,175094,175139,175182,175223,175262,175298,175347,175394,175439,175482,175523,175562,175599,175633,175680,175725,175768,175809,175848,175885,175920,175952,175996,176038,176078,176116,176152,176186,176218,176247,176306,176363,176418,176471,176522,176571,176618,176662,176719,176774,176827,176878,176927,176974,177019,177061,177116,177169,177220,177269,177316,177361,177404,177444,177497,177548,177597,177644,177689,177732,177773,177811,177862,177911,177958,178003,178046,178087,178126,178162,178211,178258,178303,178346,178387,178426,178463,178497,178544,178589,178632,178673,178712,178749,178784,178816,178860,178902,178942,178980,179016,179050,179082,179111,179170,179227,179282,179335,179386,179435,179482,179526,179583,179638,179691,179742,179791,179838,179883,179925,179980,180033,180084,180133,180180,180225,180268,180308,180361,180412,180461,180508,180553,180596,180637,180675,180726,180775,180822,180867,180910,180951,180990,181026,181075,181122,181167,181210,181251,181290,181327,181361,181408,181453,181496,181537,181576,181613,181648,181680,181724,181766,181806,181844,181880,181914,181946,181975,182033,182089,182143,182195,182245,182293,182339,182382,182438,182492,182544,182594,182642,182688,182732,182773,182827,182879,182929,182977,183023,183067,183109,183148,183200,183250,183298,183344,183388,183430,183470,183507,183557,183605,183651,183695,183737,183777,183815,183850,183898,183944,183988,184030,184070,184108,184144,184177,184223,184267,184309,184349,184387,184423,184457,184488,184531,184572,184611,184648,184683,184716,184747]
def posReg (d : Nat) : Reg :=
  match d with
  | 0 => .x0 | 1 => .x7 | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | _ => .x26
def posE (d : Nat) : E := RegFile.init.get (posReg d)
def bumpE : E := .bin .add (.reg .x25) (.reg .x28)
def s9E (first : Bool) : E := if first then .reg .x27 else bumpE
def kAt (rb : Reg) (off : Word) (k : Nat) : Addr := ⟨some (.reg rb), off + BitVec.ofNat 64 k⟩
def lAt (rb : Reg) (off : Word) (k : Nat) : E := .ld (addC (.reg rb) (off + BitVec.ofNat 64 k))
def headJ (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (addC (.reg rb) off) 48)).set .x25 (s9E first),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, s9E first)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩, .c (pcOf tgt), .jump, 6, 6⟩
def headR (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 7 else 6
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 bumpE,
    [(kAt rb off 16, .bin (.st .b 4) bumpE (posE d)), (kAt rb off 24, .reg .x4)],
    [.align8 (.reg rb), .valid (kAt rb off 20) 1, .valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩
def rungR (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 2 else 1
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (.c (BitVec.ofNat 64 a))
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 1) (.ld (addC (.reg .x10) 16)) (posE d))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 17⟩ 1]⟩, .c (pcOf (p + n)), .ecall, n, n⟩
/-- Pairing stage 1: value offset inside a chain block (`48` F, `0` G) and the hash destination offset of an
interior step (`48` F, `-16` G: the high half lands on the value). -/
def gVal (g : Bool) : Nat := if g then 0 else 48
def gOut (g : Bool) : Word := if g then BitVec.ofNat 64 (2 ^ 64 - 16) else 48
def copyRegs (rb : Reg) (off : Word) (g : Bool := false) : RegFile :=
  (RegFile.init.set .x3 (lAt rb off (gVal g))).set .x14 (lAt rb off (gVal g + 8))
def copyMem (rb : Reg) (off : Word) (slot : Nat) (g : Bool := false) : SymMem :=
  [(⟨none, BitVec.ofNat 64 (slot + 8)⟩, lAt rb off (gVal g + 8)), (⟨none, BitVec.ofNat 64 slot⟩, lAt rb off (gVal g))]
def copyObl (rb : Reg) (off : Word) (g : Bool := false) : List Oblig :=
  [.valid (kAt rb off (gVal g + 8)) 8, .valid (kAt rb off (gVal g)) 8]
def copyJ (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 (s9E first), copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 6, 6⟩
def copyF (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨(copyRegs rb off).set .x25 bumpE, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 5)), .fuel, 5, 5⟩
def copyN (rb : Reg) (off : Word) (slot : Nat) (tgt : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf tgt), .jump, 5, 5⟩
def hOff (i d : Nat) : Word := BitVec.ofNat 64 (64 * i + 8 * d) - 2048
def hKey (i d : Nat) : Addr := ⟨some (.reg .x28), hOff i d⟩
def hLoad (i d : Nat) : E := addC (.reg .x28) (BitVec.ofNat 64 (i + 256 * d) - BitVec.ofNat 64 385)
def headJH (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf tgt), .jump, 5, 5⟩
def ecallR (p : Nat) : Result := ⟨SymState.init, .c (pcOf p), .ecall, 0, 0⟩
def landOff (d : Nat) : Nat := if d = 6 then 2 else 1
def headRH (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) : Result :=
  let n := if slot.isSome then 5 else 4
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩
def headRV (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => .c (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) 48)).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + 4)), .ecall, 4, 4⟩
def copyFH (rb : Reg) (off : Word) (slot : Nat) (p : Nat) : Result :=
  ⟨⟨copyRegs rb off, copyMem rb off slot, copyObl rb off⟩, .c (pcOf (p + 4)), .fuel, 4, 4⟩
def shE (w : Reg) (b : Nat) : E :=
  if b = 9 then .reg w
  else if b < 10 then .bin .sll (.reg w) (.c (BitVec.ofNat 64 (10 - b)))
  else .bin .srl (.reg w) (.c (BitVec.ofNat 64 (b - 10)))
def xJ (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Result :=
  let a := .bin .and (shE w b) (.reg mreg)
  ⟨⟨RegFile.init.set .x14 a, [], []⟩,
    .bin .and (.bin .add a (.c imm)) (.c (~~~1#64)),
    .jump, (if b = 9 then 2 else 3), (if b = 9 then 2 else 3)⟩
def xbfJ (w : Reg) (imm : Word) : Result :=
  let a := .bin .and (.bin .srl (.reg w) (.c 44)) (.reg .x9)
  ⟨⟨RegFile.init.set .x14 a, [], []⟩,
    .bin .and (.bin .add a (.c imm)) (.c (~~~1#64)), .jump, 3, 3⟩
def ctabX : Result :=
  ⟨⟨RegFile.init.set .x14 (.bin .sub (.reg .x9) (.bin .sll (.reg .x29) (.c 12))), [], []⟩,
    .bin .and (.bin .add (.bin .sub (.reg .x9) (.bin .sll (.reg .x29) (.c 12))) (.c 1844)) (.c (~~~1#64)),
    .jump, 3, 3⟩
def retR : Result := ⟨⟨RegFile.init, [], []⟩, .bin .and (.reg .x1) (.c (~~~1#64)), .jump, 1, 1⟩
def rungRB (d : Nat) (slot : Option Nat) (p : Nat) : Result :=
  let n := if slot.isSome then 2 else 1
  ⟨⟨(match slot with
      | some a => RegFile.init.set .x12 (addC (.reg .x4) (BitVec.ofNat 64 a))
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 1) (.ld (addC (.reg .x10) 16)) (posE d))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 17⟩ 1]⟩, .c (pcOf (p + n)), .ecall, n, n⟩

def copyMemB (rb : Reg) (off : Word) (slot : Nat) (g : Bool := false) : SymMem :=
  [(⟨some (.reg .x4), BitVec.ofNat 64 (slot + 8)⟩, lAt rb off (gVal g + 8)),
   (⟨some (.reg .x4), BitVec.ofNat 64 slot⟩, lAt rb off (gVal g))]

def copyOblB (rb : Reg) (off : Word) (slot : Nat) (g : Bool := false) : List Oblig :=
  [.valid ⟨some (.reg .x4), BitVec.ofNat 64 (slot + 8)⟩ 8,
   .valid ⟨some (.reg .x4), BitVec.ofNat 64 slot⟩ 8] ++ copyObl rb off g

def copyNB (rb : Reg) (off : Word) (slot : Nat) (tgt : Nat) (g : Bool := false) : Result :=
  ⟨⟨copyRegs rb off g, copyMemB rb off slot g, copyOblB rb off slot g⟩, .c (pcOf tgt), .jump, 5, 5⟩

def headJHB (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) (g : Bool := false) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => addC (.reg .x4) (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) (gOut g))).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf tgt), .jump, 5, 5⟩

def headRHB (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) (g : Bool := false) : Result :=
  let n := if slot.isSome then 5 else 4
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => addC (.reg .x4) (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) (gOut g))).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩

def headRVB (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) (g : Bool := false) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12
      (match slot with
       | some a => addC (.reg .x4) (BitVec.ofNat 64 a)
       | none => addC (addC (.reg rb) off) (gOut g))).set .x25 (hLoad i d),
    [(kAt rb off 16, hLoad i d)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + 4)), .ecall, 4, 4⟩

def copyFHB (rb : Reg) (off : Word) (slot : Nat) (p : Nat) (g : Bool := false) : Result :=
  ⟨⟨copyRegs rb off g, copyMemB rb off slot g, copyOblB rb off slot g⟩, .c (pcOf (p + 4)), .fuel, 4, 4⟩

def skipJB (tgt : Nat) : Result :=
  ⟨SymState.init, .c (pcOf tgt), .jump, 1, 1⟩

/-- Pairing stage 1: chain `i`'s block inside a lower chain area (`W9.T3M.chainSlot` on layers 1..3) and its format. -/
def lowerSlot (i : Nat) : Nat :=
  if i = 0 then 2184 else if i % 2 = 1 then 104 * (20 - i / 2) + 16 else 104 * (21 - i / 2) + 40
def lowerG (i : Nat) : Bool := decide (i % 2 = 1)
/-- Pairing stage 1: chain block offsets relative to `x22` (= chain area + 520). -/
def offL (i : Nat) : Word := BitVec.ofNat 64 (lowerSlot i) - BitVec.ofNat 64 520
def slotL (i : Nat) : Nat := if i = 0 then 768 else 784 + 16 * i
/-- C3: hash destination of a chain's last step. Lower chain 0 writes its last hash 16 bytes below its slot, so the
slot receives the HIGH half and the leaf tweak's high word above it stays witness memory. -/
def outL (i : Nat) : Nat := if i = 0 then 752 else slotL i
def hSlot (i d : Nat) : Option Nat := if d = 6 then some (outL i) else none
def triBase (t dB dC : Nat) : Nat := triBaseTab.getD (64 * t + 8 * dB + dC) 0
def partLen (d : Nat) : Nat := if d = 7 then 4 else if d = 6 then 5 else 18 - 2 * d
def pcB (t dB dC : Nat) : Nat := triBase t dB dC + 15
def pcC (t dB dC : Nat) : Nat := pcB t dB dC + partLen dB - (if t=0 ∧ dB=7 then 4 else 0)
def pcX (t dB dC : Nat) : Nat := pcC t dB dC + partLen dC - (if dB=7 ∧ dC=7 then 4 else 0)
def rankFloor (t : Nat) : Nat := if t = 1 ∨ t = 8 then 5 else 3
def lowerImm (t : Nat) : Nat :=
  if t=0 then 1992 else if t=1 then 1952 else if t=2 then 2012 else if t=3 then 1480
  else if t=4 then 1500 else if t=5 then 1520 else if t=6 then 1540 else if t=7 then 1560
  else if t=8 then 1972 else if t=9 then 1580 else if t=10 then 1600 else if t=11 then 1620
  else if t=12 then 1640 else 1660
def entW (t k : Nat) : Nat :=
  (2^62 + (if t=1 ∨ t=8 then 128 else 256)*k + lowerImm t / 4 - 1024) % 2^62
def rungsOK (d0 slot p : Nat) : Bool :=
  (List.range' d0 (7 - d0)).all fun m =>
    rOK (vrun (p + 2 * (m - d0)) 3) (rungRB m (if m = 6 then some slot else none) (p + 2 * (m - d0)))
def partOK (i d p : Nat) (skip : Bool := false) : Bool :=
  if skip then true else if d = 7 then rOK (vrun p 4) (copyFHB .x22 (offL i) (slotL i) p (lowerG i))
  else rOK (vrun p 8) (headRVB .x22 (offL i) d (if d = 6 then some (slotL i) else none) p i (lowerG i)) &&
    rungsOK (d + 1) (slotL i) (p + 5)
def entCheck (t k : Nat) : Bool :=
  if k < rankFloor t then true else if k % 8 = 7 then
    if t = 0 then rOK (vrun (entW t k) 1) (skipJB (pcB t (k / 8 % 8) (k / 64)))
    else rOK (vrun (entW t k) 7) (copyNB .x22 (offL (3 * t)) (slotL (3 * t))
      (pcB t (k / 8 % 8) (k / 64) + (if k / 8 % 8 = 7 then 4 else 0)) (lowerG (3 * t)))
  else rOK (vrun (entW t k) 7) (headJHB .x22 (offL (3 * t))
      (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)) (3 * t) (k % 8) (hSlot (3 * t) (k % 8))
      (lowerG (3 * t))) &&
    rOK (vrun (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)) 1)
      (ecallR (triBase t (k / 8 % 8) (k / 64) + 2 * (k % 8) + landOff (k % 8)))
def xOK (t dB dC : Nat) : Bool :=
  if t = 13 then rOK (vrun (pcX t dB dC) 4) ctabX
  else if t = 5 ∨ t = 12 then rOK (vrun (pcX t dB dC) 4)
    (xbfJ (if t + 1 < 7 then .x16 else .x17) (BitVec.ofNat 64 (lowerImm (t+1))))
  else rOK (vrun (pcX t dB dC) 5)
    (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) (if t = 0 ∨ t = 7 then .x27 else .x9)
      (BitVec.ofNat 64 (lowerImm (t+1))))
def blkCheck (t dB dC : Nat) : Bool :=
  rungsOK 0 (outL (3 * t)) (triBase t dB dC) &&
    partOK (3 * t + 1) dB (pcB t dB dC) (decide (t=0 ∧ dB=7)) &&
    partOK (3 * t + 2) dC (pcC t dB dC) (decide (dB=7 ∧ dC=7)) && xOK t dB dC
def triCheck (t lo n : Nat) : Bool :=
  ((List.range' lo n).all fun k => entCheck t k) &&
    ((List.range' (lo / 8) (n / 8)).all fun q => blkCheck t (q / 8) (q % 8))
def ckCheck : Bool :=
  (List.range 8).all fun c => partOK 42 c (ckSlot c)

end SigGolfCandidate.T3M
end
-- ==== merged from W9Machine_WctPackedRuns ====
section

set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def packedHeader (chain digit : Nat) : E :=
  addC (.reg .x31) (BitVec.ofNat 64 (128 + 4 * chain + 256 * digit) - BitVec.ofNat 64 1537)
def packedPos (digit : Nat) : E :=
  if digit = 1 then .reg .x7 else if digit = 2 then .reg .x13 else if digit = 3 then .reg .x19 else .c 0
def headRHRel (rb : Reg) (off dst : Word) (p chain digit : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (.reg rb) dst)).set
      .x25 (packedHeader chain digit),
    [(kAt rb off 16, packedHeader chain digit)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + 4)), .ecall, 4, 4⟩
def rungRRel (rb : Reg) (digit : Nat) (dst : Option Word) (p : Nat) : Result :=
  let n := if dst.isSome then 2 else 1
  ⟨⟨(match dst with
      | some off => RegFile.init.set .x12 (addC (.reg rb) off)
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 1) (.ld (addC (.reg .x10) 16)) (packedPos digit))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 17⟩ 1]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩
def copyFHRel (rb : Reg) (off dst : Word) (p : Nat) : Result :=
  ⟨⟨copyRegs rb off,
    [(kAt rb dst 8, lAt rb off 56), (kAt rb dst 0, lAt rb off 48)],
    [.valid (kAt rb dst 8) 8, .valid (kAt rb dst 0) 8,
      .valid (kAt rb off 56) 8, .valid (kAt rb off 48) 8]⟩,
    .c (pcOf (p + 4)), .fuel, 4, 4⟩
end W9Machine
end
-- ==== merged from T3M_Verify_PackedHeader ====
section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
def packedHi (lay : Layer) (tree leaf : Nat) : Nat :=
  (tree * 2 ^ height lay + leaf) % 2 ^ 32 + lay.val * 2 ^ 32 + 193 * 2 ^ 40
def packedPrefix (lay : Layer) (tree leaf : Nat) : Nat := 128 + 2 ^ 16 * packedHi lay tree leaf
theorem packedHi_lt (lay : Layer) (tree leaf : Nat) : packedHi lay tree leaf < 2 ^ 48 := by
  have hr := Nat.mod_lt (tree * 2 ^ height lay + leaf) (by norm_num : 0 < 2 ^ 32)
  have hl := lay.isLt
  unfold packedHi
  omega
theorem packedWord_lt (lay : Layer) (tree leaf i m : Nat) (hi : i < 128) (hm : m < 256) :
    i + 256 * m + packedPrefix lay tree leaf < 2 ^ 64 := by
  have hh := packedHi_lt lay tree leaf
  unfold packedPrefix
  omega
theorem extract64_of_eq (x : BitVec 128) (n : Nat) (h : x = BitVec.ofNat 128 n) :
    x.extractLsb' 0 64 = BitVec.ofNat 64 n := by
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_zero, Nat.div_one]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem chainHeader_low_bounded (lay : Layer) (tree leaf i m : Nat) (hi : i < 64) (hm : m < 8)
    (ht : tree < 2 ^ (31 - height lay)) (hl : leaf < 2 ^ height lay) :
    (chainHeader lay tree leaf i m).extractLsb' 0 64 =
      BitVec.ofNat 64 (i + 256 * m + packedPrefix lay tree leaf) := by
  have hr : tree * 2 ^ height lay + leaf < 2 ^ 31 := by
    fin_cases lay <;> norm_num [height] at ht hl ⊢ <;> omega
  apply extract64_of_eq
  exact (chainHeader_actual lay tree leaf i m hr hl hi hm).trans
    (congrArg (BitVec.ofNat 128) (by
      unfold packedPrefix packedHi
      rw [Nat.mod_eq_of_lt (show tree * 2 ^ height lay + leaf < 2 ^ 32 by omega)]
      ring))
theorem wordsOf_chainInputP (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest)
    (headerPad : Word) (v : Digest) :
    wordsOf (chainInputP lay tree leaf i step p0 p1 headerPad v) =
      [p0.extractLsb' 0 64, p0.extractLsb' 64 64,
        (chainHeader lay tree leaf i step).extractLsb' 0 64, headerPad,
        p1.extractLsb' 0 64, p1.extractLsb' 64 64, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  unfold chainInputP
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  have hlo : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 0 64 =
      (chainHeader lay tree leaf i step).extractLsb' 0 64 := BitVec.extractLsb'_append_eq_right
  have hhi : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 64 64 = headerPad :=
    BitVec.extractLsb'_append_eq_left
  rw [hlo, hhi]
  rfl
theorem chainInputP_length (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest)
    (headerPad : Word) (v : Digest) :
    (chainInputP lay tree leaf i step p0 p1 headerPad v).length = 64 * (0 + 1) := by
  simp only [chainInputP, List.length_append, SphincsSecurity.bytesLE_length]
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_Words ====
section

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (header pad64 zero16 Digest HashOutput HashInput Layer)
open SphincsSecurity (bytesLE bytesLE_length)
abbrev dlo (d : BitVec 128) : Word := d.extractLsb' 0 64
abbrev dhi (d : BitVec 128) : Word := d.extractLsb' 64 64
def wword (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat) : Word := w.extractLsb' (64 * j) 64
theorem wword_toNat (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat) : (wword w j).toNat = w.toNat / 2 ^ (64 * j) % 2 ^ 64 := by
  simp only [wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem wword_zero (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat) (h : 2905 ≤ j) : wword w j = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [wword_toNat]
  have hw : w.toNat < 2 ^ (64 * j) :=
    lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide +kernel) (by omega))
  rw [Nat.div_eq_of_lt hw]; rfl
theorem wdig_lo (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat) : dlo (ClaudeWCT.W9.T3M.wdig w (8 * j)) = wword w j := by
  apply BitVec.eq_of_toNat_eq
  simp only [ClaudeWCT.W9.T3M.wdig, wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [show 8 * (8 * j) = 64 * j by ring, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem wdig_hi (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat) : dhi (ClaudeWCT.W9.T3M.wdig w (8 * j)) = wword w (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ClaudeWCT.W9.T3M.wdig, wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, show 8 * (8 * j) + 64 = 64 * (j + 1) by ring, Nat.mod_mod]
theorem wdig_words (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat) :
    wordsOf (bytesLE 16 (ClaudeWCT.W9.T3M.wdig w (8 * j))) = [wword w j, wword w (j + 1)] := by
  rw [wordsOf_bytesLE16, ← wdig_lo, ← wdig_hi]
def blk4 (a b c d : BitVec 128) : List UInt8 := bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c ++ bytesLE 16 d
theorem blk4_length (a b c d : BitVec 128) : (blk4 a b c d).length = 64 := by
  simp only [blk4, List.length_append, bytesLE_length]
theorem pad64_blk4 (a b c d : BitVec 128) : pad64 (blk4 a b c d) = blk4 a b c d :=
  pad64_of_aligned _ (by rw [blk4_length])
theorem wordsOf_blk4 (a b c d : BitVec 128) :
    wordsOf (blk4 a b c d) = [dlo a, dhi a, dlo b, dhi b, dlo c, dhi c, dlo d, dhi d] := by
  unfold blk4
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  rfl
theorem aligned_blk4 (a b c d : BitVec 128) : Aligned (blk4 a b c d) := by
  rw [Aligned, blk4_length]; omega
theorem blocks_blk4 (a b c d : BitVec 128) : (toQ (pad64 (blk4 a b c d))).blocks = 1 := by
  rw [pad64_blk4, blocks_toQ (aligned_blk4 a b c d), blk4_length]
theorem bytesLE16_zero : bytesLE 16 (0 : BitVec 128) = zero16 := by decide +kernel
theorem dlo_append (hi lo : BitVec 64) : dlo (hi ++ lo) = lo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_zero,
    ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
  have := lo.isLt
  omega
theorem dhi_append (hi lo : BitVec 64) : dhi (hi ++ lo) = hi := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := lo.isLt; have := hi.isLt
  rw [Nat.mul_comm, Nat.mul_add_div (by decide +kernel), Nat.div_eq_of_lt lo.isLt, Nat.add_zero, Nat.mod_eq_of_lt hi.isLt]
theorem wordsOf_append64 (hi lo : BitVec 64) : wordsOf (bytesLE 16 (hi ++ lo)) = [lo, hi] := by
  rw [wordsOf_bytesLE16]; exact congrArg₂ (fun x y => [x, y]) (dlo_append hi lo) (dhi_append hi lo)
theorem wordsOf_rowTweak (lay : Layer) (tree leaf : Nat) :
    wordsOf (bytesLE 16 (T3.rowTweak lay tree leaf)) =
      [T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf), 1] :=
  wordsOf_append64 _ _
theorem wordsOf_leafTweak (lay : Layer) (tree leaf : Nat) :
    wordsOf (bytesLE 16 (T3.leafTweak lay tree leaf)) =
      [T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf), 0] :=
  wordsOf_append64 _ _
theorem ftsLeafP_eq (index coord leaf : Nat) (pad0 secret pad1 : Digest) :
    T3M.ftsLeafP index coord leaf pad0 secret pad1 =
      T3.shortHash (blk4 pad0 (header 9 coord index 0 leaf) secret pad1) := rfl
theorem nodeHashP_eq (tag lay tree heap : Nat) (left pad right : Digest) :
    T3M.nodeHashP tag lay tree heap left pad right =
      T3.projHash (T3.nodeHalfHigh tag lay heap) (blk4 left (T3.nodeTweak tag lay tree heap) pad right) := rfl
theorem nodeHash_eq (tag lay tree heap : Nat) (left right : Digest) :
    T3.nodeHash tag lay tree heap left right =
      T3.projHash (T3.nodeHalfHigh tag lay heap) (blk4 left (T3.nodeTweak tag lay tree heap) 0 right) := by
  unfold T3.nodeHash blk4
  rw [bytesLE16_zero]
theorem ftsLeaf_eq (index coord leaf : Nat) (secret : Digest) :
    T3.ftsLeaf index coord leaf secret = T3.shortHash (blk4 0 (header 9 coord index 0 leaf) secret 0) := by
  unfold T3.ftsLeaf blk4
  rw [bytesLE16_zero]
theorem chainInputP_eq (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : Word) (value : Digest) :
    T3M.chainInputP lay tree leaf i step pad0 pad1 headerPad value =
      blk4 pad0 (T3M.chainHeaderP lay tree leaf i step headerPad) pad1 value := rfl
theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, bytesLE_length]
theorem digestHeader_lo (c : BitVec 32) : (T3.digestHeader c).extractLsb' 0 64 = 0 :=
  dlo_append (0#32 ++ c) 0#64
theorem digestHeader_hi (c : BitVec 32) : (T3.digestHeader c).extractLsb' 64 64 = BitVec.ofNat 64 c.toNat := by
  have h := dhi_append (0#32 ++ c) 0#64
  refine h.trans ?_
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_shiftLeft, Nat.zero_or]
  have := c.isLt; omega
theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.digestInput rho m c) =
      [dlo rho, dhi rho, 0, BitVec.ofNat 64 c.toNat,
        m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64, m.extractLsb' 192 64] := by
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16,
    digestHeader_lo, digestHeader_hi, wordsOf_bytesLE32]
  rfl
theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    pad64 (T3.digestInput rho m c) = T3.digestInput rho m c :=
  pad64_of_aligned _ (by rw [digestInput_length])
theorem blocks_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (toQ (pad64 (T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput, blocks_toQ (by rw [Aligned, digestInput_length]; omega), digestInput_length]
theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    pad64 (T3.encodingInput lay tree leaf msg c) =
      T3.encodingInput lay tree leaf msg c ++ List.replicate 28 0 := by
  unfold pad64
  simp only [T3.encodingInput, List.length_append, bytesLE_length]
theorem readLE_bytesLE4_pad (c : BitVec 32) : T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
  rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
  simp
theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    wordsOf (pad64 (T3.encodingInput lay tree leaf msg c)) =
      [dlo msg, dhi msg, T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf), 1,
        BitVec.ofNat 64 c.toNat, 0, 0, 0] := by
  rw [pad64_encodingInput]
  unfold T3.encodingInput
  have e : bytesLE 16 msg ++ bytesLE 16 (T3.rowTweak lay tree leaf) ++ bytesLE 4 c ++ List.replicate 28 0 =
      bytesLE 16 msg ++ bytesLE 16 (T3.rowTweak lay tree leaf) ++
        ((bytesLE 4 c ++ List.replicate 4 0) ++ List.replicate 24 0) := by
    simp only [List.append_assoc]
    rfl
  rw [e, wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_rowTweak, wordsOf_bytesLE16,
    wordsOf_append8 _ _ (by simp only [List.length_append, bytesLE_length, List.length_replicate]),
    readLE_bytesLE4_pad, show (24 : Nat) = 8 * 3 by rfl, wordsOf_replicate_zero]
  rfl
theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    (toQ (pad64 (T3.encodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl : (pad64 (T3.encodingInput lay tree leaf msg c)).length = 64 := by
    rw [pad64_encodingInput]
    simp only [T3.encodingInput, List.length_append, bytesLE_length, List.length_replicate]
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)
theorem forestPk_eq (index : Nat) (roots : List Digest) :
    T3.forestPk index roots = T3.shortHash (forestInput index roots) := rfl
theorem sum_map_16 : ∀ l : List Digest, (l.map fun _ => (16 : Nat)).sum = 16 * l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_16 l, List.length_cons]; ring
theorem forestInput_length (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (forestInput index roots).length = 128 := by
  unfold forestInput
  simp only [List.length_append, bytesLE_length, List.length_flatMap]
  rw [sum_map_16, List.length_drop, h]
theorem wordsOf_forestInput (index : Nat) (roots : List Digest) :
    wordsOf (forestInput index roots) =
      [dlo (roots.getD 0 0), dhi (roots.getD 0 0), BitVec.ofNat 64 (hdr0 11 0 index 0),
        BitVec.ofNat 64 (hdr1 index 0)] ++ (roots.drop 1).flatMap (fun d => [dlo d, dhi d]) := by
  unfold forestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_flatMap16]
  rfl
theorem pad64_forestInput (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    pad64 (forestInput index roots) = forestInput index roots :=
  pad64_of_aligned _ (by rw [forestInput_length index roots h])
theorem blocks_forestInput (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (toQ (pad64 (forestInput index roots))).blocks = 2 := by
  rw [pad64_forestInput index roots h,
    blocks_toQ (by rw [Aligned, forestInput_length index roots h]; omega), forestInput_length index roots h]
theorem wordsOf_pad64 (l : HashInput) (h : l.length % 8 = 0) :
    wordsOf (pad64 l) = wordsOf l ++ List.replicate ((64 - l.length % 64) % 64 / 8) 0 := by
  unfold pad64
  rw [wordsOf_append _ _ h]
  congr 1
  have : (64 - l.length % 64) % 64 = 8 * ((64 - l.length % 64) % 64 / 8) := by omega
  rw [this, wordsOf_replicate_zero]
  congr 1
  omega
theorem readWords_ofNat (t : MachineState) (a : Nat) : ∀ m, a + 8 * m < 2 ^ 64 →
    t.readWords (BitVec.ofNat 64 a) m =
      (List.range m).map fun j => t.getMem (BitVec.ofNat 64 (a + 8 * j)) := by
  intro m
  induction m generalizing a with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [MachineState.readWords_succ, ofNat_add8, ih (a + 8) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    congr 2; omega
theorem readWords_eight (t : MachineState) (A : Nat) (hA : A + 64 < 2 ^ 64) :
    t.readWords (BitVec.ofNat 64 A) 8 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] := by
  rw [readWords_ofNat t A 8 (by omega)]
  rfl
theorem hashInput_words8 (t : MachineState) (l : List UInt8) (A : Nat) (hl : l.length = 64)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hw : [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] = wordsOf l) :
    hashInput t = toQ l :=
  hashInput_toQ t l 0 A hl h10 hA (by omega) h11 (by norm_num) (by rw [readWords_eight t A hA']; exact hw)
end SigGolfCandidate.T3M.Verify
end
-- ==== merged from T3M_Verify_Mem ====
section

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
/-- Witness stack (charge 86): the witness starts at absolute 4128 (W 22012, still ending at 26140 next to the
message). -/
def WIT : Nat := 0x1020
def WSZ : Nat := 22012
/-- Byte bound of the 2752 loaded witness words; the last word is the 4-byte digest counter
zero-padded by the loader, since the witness itself is `WSZ = 22012` bytes. -/
def WX : Nat := 22016
def WLO : Nat := WIT + 48
theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]
theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun h' => h ((ofNat_eq_iff ha hb).mp h')
theorem ofNat_toNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem getMem_setMem (s : MachineState) (a v A : Word) :
    (s.setMem a v).getMem A = if A = a then v else s.getMem A := by
  simp [MachineState.setMem, MachineState.getMem]
theorem writeHash_getMem (s : MachineState) (ans : BitVec 256) (A : Word) :
    (writeHash s ans).getMem A =
      if A = s.getReg .x12 + 8 + 8 + 8 then ans.extractLsb' 192 64
      else if A = s.getReg .x12 + 8 + 8 then ans.extractLsb' 128 64
      else if A = s.getReg .x12 + 8 then ans.extractLsb' 64 64
      else if A = s.getReg .x12 then ans.extractLsb' 0 64
      else s.getMem A := by
  simp only [writeHash, MachineState.writeWords]
  show ((((s.setMem _ _).setMem _ _).setMem _ _).setMem _ _).getMem A = _
  simp only [getMem_setMem]
theorem writeHash_getMem_ofNat (s : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64) :
    (writeHash s ans).getMem (BitVec.ofNat 64 A) =
      if A = d + 24 then ans.extractLsb' 192 64
      else if A = d + 16 then ans.extractLsb' 128 64
      else if A = d + 8 then ans.extractLsb' 64 64
      else if A = d then ans.extractLsb' 0 64
      else s.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem, hd]
  simp only [show (8 : Word) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat,
    ofNat_eq_iff hA (by omega : d + 8 + 8 + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d + 8 + 8 < 2 ^ 64),
    ofNat_eq_iff hA (by omega : d + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d < 2 ^ 64)]
theorem writeWords_regs : ∀ (ws : List Word) (s : MachineState) (base : Word),
    (s.writeWords base ws).regs = s.regs ∧ (s.writeWords base ws).pc = s.pc
  | [], _, _ => ⟨rfl, rfl⟩
  | w :: ws, s, base => by
    simp only [MachineState.writeWords]
    obtain ⟨h1, h2⟩ := writeWords_regs ws (s.setMem base w) (base + 8)
    exact ⟨h1.trans rfl, h2.trans rfl⟩
theorem writeHash_getReg (s : MachineState) (ans : BitVec 256) (r : Reg) :
    (writeHash s ans).getReg r = s.getReg r := getReg_writeHash s ans r
theorem writeHash_pc (s : MachineState) (ans : BitVec 256) :
    (writeHash s ans).pc = s.pc + 4 := pc_writeHash s ans
theorem writeHash_frame (t : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64)
    (h : A + 8 ≤ d ∨ d + 32 ≤ A) :
    (writeHash t ans).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem_ofNat t ans d A hd hA hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
theorem writeHash_at0 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = ans.extractLsb' 0 64 := by
  rw [writeHash_getMem_ofNat t ans d d hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]
theorem writeHash_at8 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = ans.extractLsb' 64 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_pos rfl]
theorem writeHash_at16 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 16)) = ans.extractLsb' 128 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_neg (by omega), if_pos rfl]
theorem writeHash_at24 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 24)) = ans.extractLsb' 192 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_pos rfl]
theorem writeHash_lo (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = dlo (ans.extractLsb' 0 128) ∧
      (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = dhi (ans.extractLsb' 0 128) :=
  DigAt.writeHash_lo t ans d hd hd'
theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide +kernel) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide +kernel) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
theorem replaceWord32_0_toNat (w : BitVec 64) (v : BitVec 32) :
    (replaceWord32 w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (0 * 32)) : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1)) := by decide +kernel
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.zero_mul,
    Nat.shiftLeft_zero]
  have hv := v.isLt
  have hw := w.isLt
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1) < 2 ^ 64 by norm_num),
    land_split _ _ 0 32 (by decide +kernel), Nat.and_two_pow_sub_one_eq_mod, Nat.pow_zero, Nat.mod_one, Nat.add_zero,
    ← Nat.two_pow_add_eq_or_of_lt hv]
  ring
theorem merge_w0_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl]
  rw [replaceWord32_0_toNat]
  simp [BitVec.toNat_setWidth]
theorem merge_w0_high (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat / 2 ^ 32 = w.toNat / 2 ^ 32 % 2 ^ 32 := by
  rw [merge_w0_toNat]; omega
def baseK : List (Reg × Word) := [(.x5, 0), (.x18, 0xFFF)]
def pSlots : List Nat := [512,520,536]
def CTRW : Nat := 0x120
def PkOK (pk : Digest) (s : MachineState) : Prop :=
  s.getMem 0xA0 = dlo pk ∧ s.getMem 0xA8 = dhi pk
def PZero (s : MachineState) : Prop := ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0
def PHalf (s : MachineState) : Prop := (s.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
def WitHdr (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) : Prop :=
  ∀ j, 4 ≤ j → j < 6 → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j
def dataWords : List Nat :=
  [2 ^ 40, 17311559823019733055, 8198552921648689607, 0x30401, 0x7fc00, 2256, 11736, 0xa01, 0x901, 7072, 15264, 0]
def TOPLOAD : Nat := 0xffbf68
def TOPBASE : Nat := 0xffc000
def TOPB9 : Nat := 0xffbf10
def topWords : List Nat :=
  [17311559823019733055, 8198552921648689607, 0x30401, 0x7fc00, 0x201 + 193 * 2 ^ 56 + 3 * 2 ^ 48]
def DATA : Nat := 16777120
def TAB : Nat := 16709632
def HDATA : Nat := 0xffbf90
def headerBank (lay koff : Nat) : Nat := TOPBASE + 4096 * lay + 64 * koff
def hyperBase (lay : Nat) : Nat := 0x201 + lay * 2 ^ 48 + 193 * 2 ^ 56
def hdrAddr (lay : Nat) : Nat := TOPBASE - 120 + 8 * ((lay + 1) % 4)
structure DataOK (s : MachineState) : Prop where
  mask : s.getMem (BitVec.ofNat 64 (TOPBASE - 8)) = 520192#64
  header : ∀ lay, lay < 4 →
    s.getMem (BitVec.ofNat 64 (hdrAddr lay)) = BitVec.ofNat 64 (hyperBase lay)
  buffer3 : s.getMem (BitVec.ofNat 64 (TOPB9 + 56)) = 22288#64
  /-- Campaign T51: the r6 field mask 0xFF00 (verify data word 16), read by the g0 bodies' `ld t4,-288(s1)`. -/
  mask6 : s.getMem (BitVec.ofNat 64 (TOPB9 - 288)) = 65280#64
theorem DataOK.prefix {s : MachineState} (h : DataOK s) (lay : Nat) (hl : lay < 4) :
    s.getMem (BitVec.ofNat 64 (hdrAddr lay)) = BitVec.ofNat 64 (hyperBase lay) :=
  h.header lay hl
theorem hdrAddr_bounds (lay : Nat) : TOPBASE - 120 ≤ hdrAddr lay ∧ hdrAddr lay + 8 ≤ TOPBASE - 88 := by
  unfold hdrAddr TOPBASE; constructor <;> omega
theorem DataOK.congr_top {s t : MachineState} (h : DataOK s)
    (hm : ∀ A, TOPB9 - 288 ≤ A → A < TOPBASE →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : DataOK t := by
  have e1 : TOPB9 = 0xffbf10 := rfl
  have e2 : TOPBASE = 0xffc000 := rfl
  constructor
  · rw [hm _ (by omega) (by omega)]
    exact h.mask
  · intro lay hl
    have hb := hdrAddr_bounds lay
    rw [hm _ (by omega) (by omega)]
    exact h.header lay hl
  · rw [hm _ (by omega) (by omega)]
    exact h.buffer3
  · rw [hm _ (by omega) (by omega)]
    exact h.mask6
theorem DataOK.congr {s t : MachineState} (h : DataOK s)
    (hm : ∀ A, TAB ≤ A → A + 8 ≤ 2 ^ 24 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : DataOK t := by
  constructor
  · rw [hm _ (by unfold TOPBASE TAB; omega) (by unfold TOPBASE; omega)]
    exact h.mask
  · intro lay hl
    have hb := hdrAddr_bounds lay
    rw [hm _ (by unfold TOPBASE TAB at *; omega) (by unfold TOPBASE at *; omega)]
    exact h.header lay hl
  · rw [hm _ (by unfold TOPB9 TAB; omega) (by unfold TOPB9; omega)]
    exact h.buffer3
  · rw [hm _ (by unfold TOPB9 TAB; omega) (by unfold TOPB9; omega)]
    exact h.mask6
def Glob (gk : List (Reg × Word)) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (s : MachineState) : Prop :=
  (∀ p ∈ gk, s.getReg p.1 = p.2) ∧ WitHdr w s ∧ PkOK pk s ∧ PZero s ∧ PHalf s ∧ DataOK s
def WitAll (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) : Prop :=
  ∀ j, 8 * j < WX → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j
def Orig (w : ClaudeWCT.W9.T3M.WBytes) (P : Nat → Prop) (s : MachineState) : Prop :=
  ∀ j, 8 * j < WX → P (8 * j) → s.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = wword w j
theorem WitAll.orig {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} (h : WitAll w s) (P : Nat → Prop) : Orig w P s :=
  fun j hj _ => h j hj
theorem WitAll.hdr {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} (h : WitAll w s) : WitHdr w s :=
  fun j _ hj => h j (by unfold WX; omega)
theorem Orig.mono {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P P' : Nat → Prop} (h : Orig w P s)
    (hP : ∀ o, P' o → P o) : Orig w P' s :=
  fun j h1 h2 => h j h1 (hP _ h2)
theorem Orig.frame {w : ClaudeWCT.W9.T3M.WBytes} {s t : MachineState} {P : Nat → Prop} (h : Orig w P s)
    (hf : ∀ j, 8 * j < WX → P (8 * j) →
      t.getMem (BitVec.ofNat 64 (WIT + 8 * j)) = s.getMem (BitVec.ofNat 64 (WIT + 8 * j))) :
    Orig w P t :=
  fun j h1 h2 => (hf j h1 h2).trans (h j h1 h2)
theorem Orig.word {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off < WX) (hp : P off) :
    s.getMem (BitVec.ofNat 64 (WIT + off)) = wword w (off / 8) := by
  have := hO (off / 8) (by omega) (by rwa [show 8 * (off / 8) = off by omega])
  rwa [show 8 * (off / 8) = off by omega] at this
/-- The high word of a 16-byte witness digest (C2/C3 high-word pads). -/
theorem Orig.hi {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off + 8 < WX) (hp : P (off + 8)) :
    s.getMem (BitVec.ofNat 64 (WIT + off + 8)) = dhi (ClaudeWCT.W9.T3M.wdig w off) := by
  obtain ⟨j, rfl⟩ : ∃ j, off = 8 * j := ⟨off / 8, by omega⟩
  rw [show WIT + 8 * j + 8 = WIT + (8 * j + 8) by ring, hO.word (8 * j + 8) (by omega) hoff hp, wdig_hi]
  congr 1; omega
theorem Orig.dig {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off + 8 < WX) (hp0 : P off) (hp1 : P (off + 8)) :
    s.getMem (BitVec.ofNat 64 (WIT + off)) = dlo (ClaudeWCT.W9.T3M.wdig w off) ∧
      s.getMem (BitVec.ofNat 64 (WIT + off + 8)) = dhi (ClaudeWCT.W9.T3M.wdig w off) := by
  obtain ⟨j, rfl⟩ : ∃ j, off = 8 * j := ⟨off / 8, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [hO.word (8 * j) h8 (by omega) hp0, wdig_lo]; congr 1; omega
  · rw [show WIT + 8 * j + 8 = WIT + (8 * j + 8) by ring, hO.word (8 * j + 8) (by omega) hoff hp1, wdig_hi]
    congr 1; omega
def safeAddr (n : Nat) : Bool :=
  decide (n + 8 ≤ WIT) && !(pSlots.contains n) && n != 0xA0 && n != 0xA8 && n != CTRW
def isLowW (a : Nat) : E → Bool
  | .bin (.st .w 0) (.ld (.c k)) _ => k.toNat == a
  | _ => false
def relOK (rel : List Reg) (a : Addr) : Bool :=
  match a.base with
  | some (.reg r) => rel.any (fun x => Reg.beqN x r) && decide (a.off.toNat < 4096)
  | _ => false
def memOKA (allow : List Nat) (rel : List Reg) (ws : SymMem) : Bool :=
  ws.all fun p => relOK rel p.1 || (p.1.base.isNone &&
    (safeAddr p.1.off.toNat || (p.1.off.toNat == CTRW && isLowW CTRW p.2) ||
      (allow.contains p.1.off.toNat && decide ((WLO ≤ p.1.off.toNat ∨
        (WIT ≤ p.1.off.toNat ∧ p.1.off.toNat + 8 ≤ WIT + 32)) ∧ p.1.off.toNat < 2 ^ 23))))
def memOK (ws : SymMem) : Bool := memOKA [] [] ws
def regsOK (gk : List (Reg × Word)) (rf : RegFile) : Bool := gk.all fun p => E.beq (rf.get p.1) (.c p.2)
def RelOK (rel : List Reg) (s : MachineState) : Prop :=
  ∀ r ∈ rel, WLO ≤ (s.getReg r).toNat ∧ (s.getReg r).toNat < 2 ^ 23
theorem RelOK.nil (s : MachineState) : RelOK [] s := fun _ h => by simp at h
def Prot (A : Nat) : Prop := A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8 ∨ (WIT + 32 ≤ A ∧ A < WLO)
theorem safeAddr_spec {n : Nat} (h : safeAddr n = true) :
    n + 8 ≤ WIT ∧ n ∉ pSlots ∧ n ≠ 0xA0 ∧ n ≠ 0xA8 ∧ n ≠ CTRW := by
  unfold safeAddr at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun hm => ?_, h3, h4, h5⟩
  rw [List.contains_iff_mem.mpr hm] at h2; cases h2
theorem relOK_spec {rel : List Reg} : ∀ {a : Addr}, relOK rel a = true →
    ∃ r ∈ rel, a.base = some (.reg r) ∧ a.off.toNat < 4096
  | ⟨some (.reg r), off⟩, h => by
    simp only [relOK, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨x, hx, hxr⟩, hoff⟩ := h
    obtain rfl := Reg.beqN_eq hxr
    exact ⟨x, hx, rfl, hoff⟩
  | ⟨none, _⟩, h => by simp [relOK] at h
  | ⟨some (.c _), _⟩, h => by simp [relOK] at h
  | ⟨some (.ld _), _⟩, h => by simp [relOK] at h
  | ⟨some (.un _ _), _⟩, h => by simp [relOK] at h
  | ⟨some (.bin _ _ _), _⟩, h => by simp [relOK] at h
  | ⟨some (.ite _ _ _ _ _), _⟩, h => by simp [relOK] at h
theorem memOKA_cases {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    {p : Addr × E} (hp : p ∈ ws) :
    (∃ r ∈ rel, p.1.base = some (.reg r) ∧ p.1.off.toNat < 4096) ∨
    (p.1.base = none ∧
      (safeAddr p.1.off.toNat = true ∨ (p.1.off.toNat = CTRW ∧ isLowW CTRW p.2 = true) ∨
        (p.1.off.toNat ∈ allow ∧ (WLO ≤ p.1.off.toNat ∨ (WIT ≤ p.1.off.toNat ∧ p.1.off.toNat + 8 ≤ WIT + 32)) ∧
          p.1.off.toNat < 2 ^ 23))) := by
  have := List.all_eq_true.mp h p hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Option.isNone_iff_eq_none] at this
  rcases this with hr | ⟨hb, hc⟩
  · exact Or.inl (relOK_spec hr)
  · right
    refine ⟨hb, ?_⟩
    rcases hc with (h1 | h2) | ⟨h3, h4⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨List.contains_iff_mem.mp h3, h4⟩)
theorem relWrite_ge {rel : List Reg} {s : MachineState} (hrel : RelOK rel s) {a : Addr} {r : Reg}
    (hr : r ∈ rel) (hb : a.base = some (.reg r)) (hoff : a.off.toNat < 4096) :
    (a.eval s).toNat = (s.getReg r).toNat + a.off.toNat ∧ WLO ≤ (a.eval s).toNat := by
  obtain ⟨h1, h2⟩ := hrel r hr
  obtain ⟨b, off⟩ := a
  simp only at hb hoff ⊢
  subst hb
  simp only [Addr.eval, E.eval, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, by omega⟩
theorem memOKA_prot {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) (A : Nat) (hA : A < 2 ^ 64) (hp : Prot A) :
    ∀ p ∈ ws, BitVec.ofNat 64 A ≠ p.1.eval s := by
  intro p hp'
  have hps : ∀ a ∈ pSlots, a < WIT := by decide +kernel
  rcases memOKA_cases h hp' with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
  · obtain ⟨_, hge⟩ := relWrite_ge hrel hr hb hoff
    intro heq
    have : (p.1.eval s).toNat = A := by rw [← heq, ofNat_toNat_lt _ hA]
    rcases hp with h1 | h1 | h1 | ⟨_, h1⟩
    · have := hps A h1; unfold WLO at hge; omega
    · unfold WLO WIT at hge; omega
    · unfold WLO WIT at hge; omega
    · omega
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval]
    intro heq
    have hoff : off.toNat = A := by rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨-, h4⟩
    · obtain ⟨s1, s2, s3, s4, -⟩ := safeAddr_spec h1
      rcases hp with h | h | h | ⟨h, -⟩
      · exact s2 h
      · exact s3 h
      · exact s4 h
      · omega
    · rcases hp with h | h | h | ⟨h, -⟩
      · rw [h2] at h; unfold CTRW at h; simp [pSlots] at h
      · unfold CTRW at h2; omega
      · unfold CTRW at h2; omega
      · unfold CTRW WIT at *; omega
    · rcases hp with h | h | h | ⟨h'', h'⟩
      · have := hps A h; unfold WLO WIT at *; omega
      · unfold WLO WIT at h4; omega
      · unfold WLO WIT at h4; omega
      · unfold WLO WIT at *; omega
theorem memOKA_ctr {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) :
    (memEval s ws (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = (s.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    have hp := memOKA_cases h (List.mem_cons_self ..)
    have hws : memOKA allow rel ws = true := by
      simp only [memOKA, List.all_cons, Bool.and_eq_true] at h; simpa [memOKA] using h.2
    have ih' := ih hws
    rw [memEval_cons]
    by_cases he : BitVec.ofNat 64 CTRW = p.1.eval s
    · rw [if_pos he]
      rcases hp with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
      · obtain ⟨_, hge⟩ := relWrite_ge hrel hr hb hoff
        rw [← he, ofNat_toNat_lt _ (by unfold CTRW; omega)] at hge
        unfold CTRW WLO WIT at hge; omega
      · obtain ⟨⟨b, off⟩, v⟩ := p
        simp only at hb; subst hb
        have hoff : off.toNat = CTRW := by
          simp only [Addr.eval] at he; rw [← he, BitVec.toNat_ofNat]; rfl
        simp only [hoff] at hc
        rcases hc with h1 | ⟨-, h2⟩ | ⟨-, h3⟩
        · exact absurd rfl (safeAddr_spec h1).2.2.2.2
        · unfold isLowW at h2
          split at h2
          · rename_i k x
            simp only [beq_iff_eq] at h2
            have hk : k = BitVec.ofNat 64 CTRW := by
              apply BitVec.eq_of_toNat_eq; rw [h2, BitVec.toNat_ofNat]; rfl
            subst hk
            show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 CTRW)) 0 (x.eval s)).toNat / 2 ^ 32 = _
            rw [merge_w0_high]
            have := (s.getMem (BitVec.ofNat 64 CTRW)).isLt
            omega
          · cases h2
        · unfold WLO WIT CTRW at h3; omega
    · rw [if_neg he]; exact ih'
theorem memOKA_data {allow : List Nat} {rel : List Reg} {ws : SymMem} (h : memOKA allow rel ws = true)
    (s : MachineState) (hrel : RelOK rel s) (A : Nat) (hA : 2 ^ 23 + 4096 ≤ A) (hA' : A < 2 ^ 64) :
    ∀ p ∈ ws, BitVec.ofNat 64 A ≠ p.1.eval s := by
  intro p hp'
  rcases memOKA_cases h hp' with ⟨r, hr, hb, hoff⟩ | ⟨hb, hc⟩
  · obtain ⟨hev, -⟩ := relWrite_ge hrel hr hb hoff
    have h2 := (hrel r hr).2
    intro heq
    have : (p.1.eval s).toNat = A := by rw [← heq, ofNat_toNat_lt _ hA']
    omega
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval]
    intro heq
    have hoff : off.toNat = A := by rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA']
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨-, h4⟩
    · have := (safeAddr_spec h1).1; unfold WIT at this; omega
    · unfold CTRW at h2; omega
    · omega
theorem DATA_ge (k : Nat) (hk : k < 12) : 2 ^ 23 + 4096 ≤ DATA + 8 * k ∧ DATA + 8 * k + 8 ≤ 2 ^ 24 := by
  unfold DATA; omega
theorem Glob_toState_allow {gk0 gk : List (Reg × Word)} {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {s : MachineState}
    {allow : List Nat} {rel : List Reg}
    (hG : Glob gk0 w pk s) (σ : SymState) (pc : Word) (hm : memOKA allow rel σ.mem = true)
    (hrel : RelOK rel s) (hr : regsOK gk σ.regs = true) : Glob gk w pk (σ.toState s pc) := by
  obtain ⟨-, h0, h2, h3, h4, h5⟩ := hG
  have fr : ∀ A, A < 2 ^ 64 → Prot A →
      (σ.toState s pc).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [SymState.toState_getMem]
    exact memEval_frame s _ _ (memOKA_prot hm s hrel A hA hp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have := List.all_eq_true.mp hr p hp
    rw [SymState.toState_getReg, E.beq_eq this]; rfl
  · intro j hj4 hj
    rw [fr _ (by unfold WIT; omega) (Or.inr (Or.inr (Or.inr ⟨by unfold WIT; omega, by unfold WLO WIT; omega⟩)))]
    exact h0 j hj4 hj
  · exact ⟨(fr 0xA0 (by omega) (by simp [Prot])).trans h2.1, (fr 0xA8 (by omega) (by simp [Prot])).trans h2.2⟩
  · intro a ha
    have : a < 2 ^ 64 := by simp [pSlots] at ha; omega
    rw [fr a this (Or.inl ha)]; exact h3 a ha
  · show (memEval s σ.mem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
    rw [memOKA_ctr hm s hrel]; exact h4
  · apply h5.congr
    intro A hA hAend
    rw [SymState.toState_getMem, memEval_frame s _ _
      (memOKA_data hm s hrel _ (by unfold TAB at hA; omega) (by omega))]
theorem Glob_toState {gk0 gk : List (Reg × Word)} {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {s : MachineState}
    (hG : Glob gk0 w pk s) (σ : SymState) (pc : Word) (hm : memOK σ.mem = true)
    (hr : regsOK gk σ.regs = true) : Glob gk w pk (σ.toState s pc) :=
  Glob_toState_allow hG σ pc hm (RelOK.nil s) hr
theorem Orig_toState {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P P' : Nat → Prop} (hO : Orig w P s)
    (σ : SymState) (pc : Word)
    (hfr : ∀ o, o < WX → P' o → P o ∧ ∀ p ∈ σ.mem, BitVec.ofNat 64 (WIT + o) ≠ p.1.eval s) :
    Orig w P' (σ.toState s pc) := by
  intro j h1 h2
  obtain ⟨hp, hne⟩ := hfr (8 * j) h1 h2
  rw [SymState.toState_getMem, memEval_frame s _ _ hne]
  exact hO j h1 hp
theorem Orig_toState_const {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} {allow : List Nat}
    (hO : Orig w P s) (σ : SymState) (pc : Word) (hm : memOKA allow [] σ.mem = true) :
    Orig w (fun o => P o ∧ WIT + o ∉ allow) (σ.toState s pc) := by
  refine Orig_toState hO σ pc (fun o ho ⟨hp, hna⟩ => ⟨hp, fun p hp' heq => ?_⟩)
  rcases memOKA_cases hm hp' with ⟨r, hr, -⟩ | ⟨hb, hc⟩
  · simp at hr
  · obtain ⟨⟨b, off⟩, v⟩ := p
    simp only at hb; subst hb
    simp only [Addr.eval] at heq
    have hoff : off.toNat = WIT + o := by
      rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold WIT WX at *; omega)]
    simp only [hoff] at hc
    rcases hc with h1 | ⟨h2, -⟩ | ⟨h3, -⟩
    · have := (safeAddr_spec h1).1; omega
    · unfold CTRW WIT at h2; omega
    · exact hna h3
theorem WitAll_toState {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} (hW : WitAll w s) (σ : SymState)
    (pc : Word) (hm : memOK σ.mem = true) : WitAll w (σ.toState s pc) := by
  have := Orig_toState_const (hW.orig (fun _ => True)) σ pc hm
  intro j hj
  exact this j hj ⟨trivial, by simp⟩
theorem Orig_writeHash {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} (hO : Orig w P s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    Orig w (fun o => P o ∧ (WIT + o + 8 ≤ d ∨ d + 32 ≤ WIT + o)) (writeHash s ans) := by
  intro j h1 ⟨h2, h3⟩
  rw [writeHash_frame s ans d _ hd (by unfold WIT WX at *; omega) (by omega) h3]
  exact hO j h1 h2
theorem WitAll_writeHash {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} (hW : WitAll w s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hlow : d + 32 ≤ WIT) : WitAll w (writeHash s ans) := by
  intro j hj
  rw [writeHash_frame s ans d _ hd (by unfold WIT WX at *; omega) (by unfold WIT at hlow; omega)
    (Or.inr (by unfold WIT at *; omega))]
  exact hW j hj
def safeDest (d : Nat) : Bool :=
  decide (d % 8 = 0) && decide (d + 32 ≤ 2 ^ 23) &&
    (pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 2).map (fun j => WIT + 32 + 8 * j)).all
      (fun q => decide (q + 8 ≤ d ∨ d + 32 ≤ q))
theorem safeDest_hi (d : Nat) (h : WLO ≤ d) (h8 : d % 8 = 0) (hm : d + 32 ≤ 2 ^ 23) :
    safeDest d = true := by
  simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, MEMORY_BYTES]
  refine ⟨⟨by simpa using h8, by simpa using hm⟩, fun q hq => Or.inl ?_⟩
  simp only [List.mem_append, List.mem_map, List.mem_range, pSlots, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  unfold WLO WIT CTRW at *
  rcases hq with ((h1 | h1 | h1 | h1) | h1 | h1 | h1) | ⟨j, hj, rfl⟩ <;> omega
theorem Glob_writeHash {gk : List (Reg × Word)} {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {s : MachineState}
    (hG : Glob gk w pk s) (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hsafe : safeDest d = true) : Glob gk w pk (writeHash s ans) := by
  obtain ⟨h1, h0, h2, h3, h4, h5⟩ := hG
  simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsafe
  obtain ⟨⟨-, hd1⟩, hd2⟩ := hsafe
  have hd1' : d + 32 ≤ 2 ^ 24 := by omega
  have fr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ d ∨ d + 32 ≤ A) →
      (writeHash s ans).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [writeHash_getMem_ofNat s ans d A hd hA (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hps : ∀ a ∈ pSlots, a < WIT := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [writeHash_getReg]; exact h1 p hp
  · intro j hj4 hj
    have hm : WIT + 8 * j ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 2).map (fun j => WIT + 32 + 8 * j) :=
      List.mem_append_right _ (List.mem_map.mpr ⟨j - 4, List.mem_range.mpr (by omega), by omega⟩)
    rw [fr (WIT + 8 * j) (by unfold WIT; omega) (hd2 _ hm)]
    exact h0 j hj4 hj
  · have m0 : (0xA0 : Nat) ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 2).map (fun j => WIT + 32 + 8 * j) := by
      simp
    have m8 : (0xA8 : Nat) ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 2).map (fun j => WIT + 32 + 8 * j) := by
      simp
    exact ⟨(fr 0xA0 (by omega) (hd2 _ m0)).trans h2.1, (fr 0xA8 (by omega) (hd2 _ m8)).trans h2.2⟩
  · intro a ha
    have hm : a ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 2).map (fun j => WIT + 32 + 8 * j) :=
      List.mem_append_left _ (List.mem_append_left _ ha)
    have := hps a ha
    rw [fr a (by unfold WIT at this; omega) (hd2 _ hm)]; exact h3 a ha
  · have mc : CTRW ∈ pSlots ++ [0xA0, 0xA8, CTRW] ++ (List.range 2).map (fun j => WIT + 32 + 8 * j) := by simp
    show ((writeHash s ans).getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
    rw [fr CTRW (by unfold CTRW; omega) (hd2 _ mc)]; exact h4
  · apply h5.congr
    intro A hA hAend
    exact fr A (by omega) (Or.inr (by unfold TAB at hA; omega))
theorem Known_writeHash {known : List (Reg × Word)} {s : MachineState}
    (h : ∀ p ∈ known, s.getReg p.1 = p.2) (a : BitVec 256) : ∀ p ∈ known, (writeHash s a).getReg p.1 = p.2 := by
  intro p hp; rw [writeHash_getReg]; exact h p hp
end SigGolfCandidate.T3M.Verify
end
-- ==== merged from T3M_Verify_ChainSem ====
section

section
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
 theorem land_mask_pow (n p k : Nat) :
    n &&& (2^p * (2^k - 1)) = 2^p * (n / 2^p % 2^k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hp : p ≤ j
  · simp only [hp, decide_true, Bool.true_and, show j-p+p=j by omega]
    exact Bool.and_comm _ _
  · simp [hp]
 theorem field_shl_pow (W s p k : Nat) (hs : s ≤ p) (hpk : p+k ≤ 64) :
    W * 2^s % 2^64 / 2^p % 2^k = W / 2^(p-s) % 2^k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < k
  · simp only [hj, decide_true, Bool.true_and, show j+p<64 by omega, show s≤j+p by omega]
    rw [show j+p-s=j+(p-s) by omega]
  · simp [hj]
 theorem shE_mask_new (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w = W)
    (b k : Nat) (hb : b < 64) (hk : k ≤ 9) :
    ((shE w b).eval s &&& BitVec.ofNat 64 ((if b=9 then 512 else 1024)*(2^k-1))).toNat =
      (if b=9 then 512 else 1024)*(W.toNat / 2^b % 2^k) := by
  have hpow : 2^k ≤ 2^9 := Nat.pow_le_pow_right (by norm_num) hk
  by_cases h9 : b=9
  · subst b
    simp only [shE, if_true, E.eval, hw]
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact land_mask_pow _ 9 k
  · simp only [if_neg h9]
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (1024:Nat)=2^10 from rfl,
      land_mask_pow]
    congr 1
    unfold shE
    rw [if_neg h9]
    split_ifs with h10
    · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show 10-b<2^64 by omega), Nat.mod_eq_of_lt (show 10-b<64 by omega),
        Nat.shiftLeft_eq, field_shl_pow _ _ _ _ (by omega) (by omega), show 10-(10-b)=b by omega]
    · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show b-10<2^64 by omega), Nat.mod_eq_of_lt (show b-10<64 by omega),
        Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        show 2^(b-10)*2^10=2^b by rw [←Nat.pow_add]; congr 1; omega]
 theorem lowerImm_even (t : Nat) : lowerImm t % 2 = 0 := by
  unfold lowerImm
  split_ifs <;> decide +kernel
 theorem entW_address (t k : Nat) (ht : t<14) (hk : k<512) :
    pcOf (entW t k) = BitVec.ofNat 64
      ((if t=1 ∨ t=8 then 512 else 1024)*k+lowerImm t) := by
  apply BitVec.eq_of_toNat_eq
  interval_cases t <;> simp only [entW, lowerImm, pcOf, BitVec.toNat_ofNat] <;> norm_num <;> omega
 theorem entW_valid (t k : Nat) (ht : t<14) (hk : k<512) (hl : rankFloor t ≤ k) :
    entW t k < 133760 := by
  interval_cases t <;> norm_num [entW, lowerImm, rankFloor] at * <;> omega
 theorem entW_fault_address (t k : Nat) (ht : t<14) (hk : k<rankFloor t) :
    (pcOf (entW t k)).toNat < 0x1000 := by
  have hk' : k<512 := by unfold rankFloor at hk; split_ifs at hk <;> omega
  rw [entW_address t k ht hk',BitVec.toNat_ofNat]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  interval_cases t <;> norm_num [lowerImm, rankFloor] at * <;> omega
end SigGolfCandidate.T3M
end

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
abbrev vimage : Image := Images.verifyImage
theorem piece_steps {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 257214) (s : MachineState)
    (hpc : s.pc = pcOf p) (ho : ∀ o ∈ r.st.obl, o.holds s) :
    Steps vimage s r.steps r.cycles (r.toState s) :=
  symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)
theorem piece_ecall {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 257214) (s : MachineState)
    (ho : ∀ o ∈ r.st.obl, o.holds s) (hst : r.stop = .ecall) :
    fetch vimage (r.toState s) = some (.base .ECALL) :=
  symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst
theorem ofNat_add_off (x a b k : Nat) (h : b ≤ x + a) (h2 : x + a + k < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k) =
      BitVec.ofNat 64 (x + a - b + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem ofNat_add_off0 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) = BitVec.ofNat 64 (x + a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem ofNat_add_off48 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a + 48 < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) + 48 = BitVec.ofNat 64 (x + a - b + 48) := by
  rw [ofNat_add_off0 x a b h (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (48 : Word).toNat = 48 from rfl]
  omega
theorem valid_ofNat (A w : Nat) (hA : A + w ≤ 2 ^ 24) (ha : A % w = 0) :
    accessValid (BitVec.ofNat 64 A) w = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by simp only [MEMORY_BYTES]; omega, ha⟩
def OrigW (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A - Verify.WIT)) 64
theorem wdig_lo (w : ClaudeWCT.W9.T3M.WBytes) (off : Nat) :
    (ClaudeWCT.W9.T3M.wdig w off).extractLsb' 0 64 = w.extractLsb' (8 * off) 64 := by
  unfold ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem wdig_hi (w : ClaudeWCT.W9.T3M.WBytes) (off : Nat) :
    (ClaudeWCT.W9.T3M.wdig w off).extractLsb' 64 64 = w.extractLsb' (8 * (off + 8)) 64 := by
  unfold ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (off + 8) = 8 * off + 64 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize w.toNat / 2 ^ (8 * off) = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem DigAt_origW {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {A : Nat} (h0 : OrigW w s A) (h1 : OrigW w s (A + 8))
    (hA : Verify.WIT ≤ A) : DigAt s A (ClaudeWCT.W9.T3M.wdig w (A - Verify.WIT)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 - Verify.WIT = A - Verify.WIT + 8 by omega]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
def chainRegs : List Reg := [.x10, .x12, .x25, .x3, .x14]
def Keeps (r : Result) (ws : List Reg) : Prop := ∀ x, x ∉ ws → r.st.regs.get x = RegFile.init.get x
theorem Keeps.reg {r : Result} {ws : List Reg} (h : Keeps r ws) (s : MachineState) {x : Reg} (hx : x ∉ ws) :
    (r.toState s).getReg x = s.getReg x := by
  rw [Result.toState_getReg, h x hx, RegFile.init_get_eval]
theorem ne_of_not_mem {x r : Reg} {ws : List Reg} (hx : x ∉ ws) (hr : r ∈ ws) : x ≠ r := by
  rintro rfl; exact hx hr
theorem headJ_keeps (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) :
    Keeps (headJ rb off first tgt) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headR_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) :
    Keeps (headR rb off d slot p) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headR]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem rungR_keeps (d : Nat) (slot : Option Nat) (p : Nat) : Keeps (rungR d slot p) [.x12] := by
  intro x hx
  simp only [rungR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl
theorem copyJ_keeps (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) :
    Keeps (copyJ rb off slot first tgt) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyJ, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyF_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyF rb off slot p) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyF, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyN_keeps (rb : Reg) (off : Word) (slot tgt : Nat) : Keeps (copyN rb off slot tgt) [.x3, .x14] := by
  intro x hx
  simp only [copyN, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headJH_keeps (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) :
    Keeps (headJH rb off tgt i d slot) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headRH_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) :
    Keeps (headRH rb off d slot p i) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headRV_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) :
    Keeps (headRV rb off d slot p i) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRV]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyFH_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyFH rb off slot p) [.x3, .x14] := by
  intro x hx
  simp only [copyFH, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem xJ_keeps (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Keeps (xJ w b mreg imm) [.x14] := by
  intro x hx
  simp only [xJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem ctabX_keeps : Keeps ctabX [.x14] := by
  intro x hx
  simp only [ctabX]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem retR_keeps : Keeps retR [] := fun _ _ => rfl
theorem rungRB_keeps (d : Nat) (slot : Option Nat) (p : Nat) : Keeps (rungRB d slot p) [.x12] := by
  intro x hx
  simp only [rungRB]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl

theorem copyNB_keeps (rb : Reg) (off : Word) (slot tgt : Nat) (g : Bool := false) :
    Keeps (copyNB rb off slot tgt g) [.x3, .x14] := by
  intro x hx
  simp only [copyNB, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headJHB_keeps (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) (g : Bool := false) :
    Keeps (headJHB rb off tgt i d slot g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJHB]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headRHB_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) (g : Bool := false) :
    Keeps (headRHB rb off d slot p i g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRHB]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headRVB_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) (g : Bool := false) :
    Keeps (headRVB rb off d slot p i g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRVB]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem copyFHB_keeps (rb : Reg) (off : Word) (slot p : Nat) (g : Bool := false) :
    Keeps (copyFHB rb off slot p g) [.x3, .x14] := by
  intro x hx
  simp only [copyFHB, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
@[simp] theorem gVal_false : gVal false = 48 := rfl
@[simp] theorem gOut_false : gOut false = 48 := rfl
/-- Pairing stage 1: the padded chain step input in the format `g` (F: `chainInputP`; G: value first). -/
def chainInputL (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : HashInput :=
  if g then SphincsSecurity.bytesLE 16 v ++
      SphincsSecurity.bytesLE 16 (chainHeaderP lay tree leaf i step headerPad) ++
      SphincsSecurity.bytesLE 16 p0 ++ SphincsSecurity.bytesLE 16 p1
  else chainInputP lay tree leaf i step p0 p1 headerPad v
theorem chainInputL_length (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : (chainInputL lay tree leaf i step p0 p1 headerPad v g).length = 64 * (0 + 1) := by
  unfold chainInputL; split
  · simp only [List.length_append, SphincsSecurity.bytesLE_length]
  · exact chainInputP_length _ _ _ _ _ _ _ _ _
theorem wordsOf_chainInputL (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : wordsOf (chainInputL lay tree leaf i step p0 p1 headerPad v g) =
      if g then [v.extractLsb' 0 64, v.extractLsb' 64 64,
        (chainHeader lay tree leaf i step).extractLsb' 0 64, headerPad,
        p0.extractLsb' 0 64, p0.extractLsb' 64 64, p1.extractLsb' 0 64, p1.extractLsb' 64 64]
      else [p0.extractLsb' 0 64, p0.extractLsb' 64 64,
        (chainHeader lay tree leaf i step).extractLsb' 0 64, headerPad,
        p1.extractLsb' 0 64, p1.extractLsb' 64 64, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  unfold chainInputL; split
  · rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
      wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
      wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
      wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
    have hlo : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 0 64 =
        (chainHeader lay tree leaf i step).extractLsb' 0 64 := BitVec.extractLsb'_append_eq_right
    have hhi : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 64 64 = headerPad :=
      BitVec.extractLsb'_append_eq_left
    rw [hlo, hhi]; rfl
  · exact wordsOf_chainInputP _ _ _ _ _ _ _ _ _
/-- On a lower layer the format of chain `i` is `isG`. -/
theorem chainInputL_eq (lay : Layer) (hl : lay ≠ 0) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word)
    (v : Digest) : chainInputL lay tree leaf i step p0 p1 headerPad v (lowerG i) =
      ClaudeWCT.W9.T3M.chainInputPW lay tree leaf i step p0 p1 headerPad v := by
  have : ClaudeWCT.WCT9.isG lay i = lowerG i := by simp [ClaudeWCT.WCT9.isG, lowerG, hl]
  unfold chainInputL ClaudeWCT.W9.T3M.chainInputPW; rw [this]
structure LCtx where
  w : ClaudeWCT.W9.T3M.WBytes
  lay : Layer
  i0 : Nat
  koff : Nat
  tree : Nat
  leaf : Nat
  S6 : Nat
  d0 : Word
  d1 : Word
  ck : Nat
  ret : Nat
  bufferBound : S6 - 520 + 2248 ≤ Verify.WIT + ClaudeWCT.W9.T3M.leafBufferBase lay
namespace LCtx
/-- Pairing stage 1: chain `i`'s block (`x22 = S6` is the chain area + 520). -/
def blk (c : LCtx) (i : Nat) : Nat := c.S6 - 520 + lowerSlot i
/-- Address of chain `i`'s supplied value (F: block + 48, G: block start). -/
def vAt (c : LCtx) (i : Nat) : Nat := c.blk i + gVal (lowerG i)
/-- Hash destination of an interior step (F: block + 48; G: block - 16, so the high half lands on the value). -/
def oAt (c : LCtx) (i : Nat) : Nat := if lowerG i then c.blk i - 16 else c.blk i + 48
def dig (c : LCtx) (i : Nat) : Nat :=
  if i < 21 then c.d0.toNat / 8 ^ i % 8 else if i < 42 then c.d1.toNat / 8 ^ (i - 21) % 8 else c.ck
def w0 (c : LCtx) (i : Nat) : Nat := i + c.koff + packedPrefix c.lay c.tree c.leaf
def w1 (c : LCtx) : Nat := hdr1 c.tree c.leaf
def pad0At (c : LCtx) (i : Nat) : Nat := c.blk i + (if lowerG i then 32 else 0)
def pad1At (c : LCtx) (i : Nat) : Nat := c.blk i + (if lowerG i then 48 else 32)
def pad0 (c : LCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad0At i - Verify.WIT)
def pad1 (c : LCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad1At i - Verify.WIT)
def padHeader (c : LCtx) (i : Nat) : Word := c.w.extractLsb' (8 * (c.blk i - Verify.WIT + 24)) 64
def val (c : LCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.vAt i - Verify.WIT)
def bufferOffset (c : LCtx) : Nat := Verify.WIT + ClaudeWCT.W9.T3M.leafBufferBase c.lay - 768
def bufferSlot (c : LCtx) (i : Nat) : Nat := c.bufferOffset + slotL i
def bufferSafe (c : LCtx) (i : Nat) : Prop :=
  c.dig i = 7 ∧ (i = 0 ∨ i = 1 ∨ (0 < i ∧ i % 3 ≠ 0 ∧ c.dig (i-1) = 7))
instance (c : LCtx) (i : Nat) : Decidable (c.bufferSafe i) := by unfold bufferSafe; infer_instance
def bufferEnd (c : LCtx) (i : Nat) : Nat :=
  c.bufferSlot i + (if 1 < i ∧ c.dig (i-1) ≠ 7 then 16 else 0)
/-- Pairing stage 1: the bytes chain `j` writes: its header word and the 32-byte hash destination. -/
def chainWr (c : LCtx) (j A : Nat) : Prop :=
  (c.blk j + 16 ≤ A ∧ A < c.blk j + 24) ∨ (c.oAt j ≤ A ∧ A < c.oAt j + 32)
/-- C3 (frame shape adapted from b3cc11b): chain 0's final step writes `[slot 0 - 16, slot 0 + 16)` (its slot gets
the HIGH half, third disjunct) and never the leaf tweak `[slot 0 + 16, slot 0 + 32)`, whose high word stays witness
memory (`wleafHigh`); the other chains write from `slot 1` on (first disjunct); pairing stage 1: chain blocks are
written as `chainWr` (second disjunct). -/
def bufferWr (c : LCtx) (i A : Nat) : Prop :=
  (c.bufferSlot c.i0 ≤ A ∧ A < c.bufferEnd i ∧ (c.i0 = 0 → c.bufferSlot 1 ≤ A)) ∨
    (∃ j, c.i0 ≤ j ∧ j < i ∧ c.chainWr j A) ∨
    (c.i0 = 0 ∧ 0 < i ∧ c.bufferSlot 0 - 16 ≤ A ∧ A < c.bufferSlot 0 + 16)
/-- C3: write address of the final step of chain `i` (`slotL`, or 16 below it for chain 0). -/
def outSlot (c : LCtx) (i : Nat) : Nat := c.bufferOffset + outL i
/-- C3 + pairing stage 1: the half of chain `i`'s step-`m` answer the image keeps (chain 0's last step, and every
interior step of a G chain). -/
def stepHigh (i m : Nat) : Bool := decide (m = 6 ∧ i = 0) || (lowerG i && decide (m < 6))
def bufferOrig (c : LCtx) (s0 : MachineState) : Prop :=
  ∀ i, c.i0 ≤ i → i ≤ 42 → ∀ k < 2, OrigW c.w s0 (c.bufferSlot i + 8*k)
def bufferVal (c : LCtx) (i : Nat) : Digest :=
  if c.bufferSafe i then ClaudeWCT.W9.T3M.wdig c.w (c.bufferSlot i - Verify.WIT) else c.val i


def ok (c : LCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.koff ≤ 16 ∧ c.S6 % 8 = 0 ∧ Verify.WIT + 7664 + 520 ≤ c.S6 ∧
    c.S6 + 1744 ≤ 0x7000 ∧ c.ck ≤ 8 ∧ c.ret = ckSlot c.ck + partLen c.ck ∧ c.i0 ≤ 42 ∧
    c.tree < 2 ^ (31 - height c.lay) ∧ c.leaf < 2 ^ height c.lay ∧
    2 ^ 63 ≤ c.d0.toNat ∧ 2 ^ 63 ≤ c.d1.toNat
def x28v (c : LCtx) : Nat := packedPrefix c.lay c.tree c.leaf + c.koff + 385
theorem x28v_eq (c : LCtx) (h0 : c.koff = 0) : c.x28v = packedPrefix c.lay c.tree c.leaf + 385 := by
  generalize hp : packedPrefix c.lay c.tree c.leaf = q
  unfold x28v; rw [hp]; omega
def known (c : LCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 c.x28v), (.x9, 0x7fc00), (.x27, 0x3fe00), (.x5, 0),
   (.x22, BitVec.ofNat 64 c.S6),
   (.x16, c.d0), (.x17, c.d1), (.x29, 7#64 - BitVec.ofNat 64 c.ck),
   (.x4, BitVec.ofNat 64 c.bufferOffset)]
def kOf (c : LCtx) (t : Nat) : Nat := c.dig (3 * t) + 8 * c.dig (3 * t + 1) + 64 * c.dig (3 * t + 2)
def tb (c : LCtx) (i : Nat) : Nat := triBase (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tB (c : LCtx) (i : Nat) : Nat := pcB (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tC (c : LCtx) (i : Nat) : Nat := pcC (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tX (c : LCtx) (i : Nat) : Nat := pcX (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def startPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ckSlot c.ck
  else if i % 3 = 0 then entW (i / 3) (c.kOf (i / 3))
  else if i % 3 = 1 then c.tB i + (if 1 < i ∧ c.dig (i-1) = 7 ∧ c.dig i = 7 then 4 else 0) else c.tC i
def rungPc (c : LCtx) (i m : Nat) : Nat :=
  if i % 3 = 0 ∧ i ≠ 42 then c.tb i + 2 * m
  else c.startPc i + 3 + 2 * (m - c.dig i) - (if c.dig i = 6 then 1 else 0)
def endPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ckSlot c.ck + partLen c.ck
  else if i % 3 = 0 then c.tB i + (if 0 < i ∧ c.dig i = 7 ∧ c.dig (i+1) = 7 then 4 else 0)
  else if i % 3 = 1 then c.tC i else c.tX i
def Wr (c : LCtx) (i : Nat) (A : Nat) : Prop := c.bufferWr i A

def WrIn (c : LCtx) (i : Nat) (A : Nat) : Prop := c.Wr i A ∨ c.chainWr i A
def Orig0 (c : LCtx) (s0 : MachineState) : Prop :=
  (∀ i, c.i0 ≤ i → i ≤ 42 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ c.bufferOrig s0
def Base (c : LCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (c.bufferSlot (c.i0 + j)) (acc.getD j 0))
def ChainIn (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    s.pc = pcOf (c.startPc i)
def HdrOk (c : LCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 256 = 128 + i + c.koff ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 16 = packedHi c.lay c.tree c.leaf ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i
def StepInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    c.HdrOk i s ∧ DigAt s (c.vAt i) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    s.getReg .x12 = BitVec.ofNat 64 (c.oAt i) ∧ s.pc = pcOf (c.rungPc i m)
def PreHash (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 256 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i ∧ DigAt t (c.vAt i) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = 6 then c.outSlot i else c.oAt i) ∧
    t.pc = pcOf (c.rungPc i m + (if m = 6 then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)
def EndInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 - c.i0 ∧
    Verify.DataOK s0 ∧ s.pc = pcOf (c.endPc i)
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem memEval_one (s : MachineState) (k : Addr) (v : E) (a A : Nat) (h : k.eval s = BitVec.ofNat 64 a)
    (ha : a < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k, v)] (BitVec.ofNat 64 A) = if A = a then v.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h, memEval_nil]
  by_cases e : A = a
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha).mp h')), if_neg e]
theorem memEval_two (s : MachineState) (k1 k2 : Addr) (v1 v2 : E) (a1 a2 A : Nat)
    (h1 : k1.eval s = BitVec.ofNat 64 a1) (h2 : k2.eval s = BitVec.ofNat 64 a2) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k1, v1), (k2, v2)] (BitVec.ofNat 64 A) =
      if A = a1 then v1.eval s else if A = a2 then v2.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h1, memEval_one s k2 v2 a2 A h2 ha2 hA]
  by_cases e : A = a1
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha1).mp h')), if_neg e]
theorem replaceByte_toNat (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide +kernel
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
theorem stepByte (w : Word) (L J m : Nat) (hL : L < 256) (hm : m < 256) (hJ : J < 2 ^ 48)
    (h1 : w.toNat % 256 = L) (h2 : w.toNat / 2 ^ 16 = J) :
    StoreKind.merge .b w 1 (BitVec.ofNat 64 m) = BitVec.ofNat 64 (L + 256 * m + 2 ^ 16 * J) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show L + 256 * m + 2 ^ 16 * J < 2 ^ 64 by omega)]
  generalize w.toNat = x at *
  norm_num at h1 h2 ⊢
  omega
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem lowerSlot_props (i : Nat) (hi : i ≤ 42) :
    lowerSlot i % 8 = 0 ∧ 16 ≤ lowerSlot i ∧ lowerSlot i ≤ 2184 ∧ (0 < i → lowerSlot i ≤ 2120) := by
  unfold lowerSlot; split_ifs <;> omega
theorem blk_props (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    c.blk i % 8 = 0 ∧ Verify.WIT + 7664 + 16 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, -, h64, hlo, hhi, -⟩ := hc
  have := lowerSlot_props i hi
  unfold blk Verify.WIT at *; refine ⟨?_, ?_, ?_⟩ <;> omega
theorem vAt_eq (c : LCtx) (i : Nat) : c.vAt i = c.blk i + (if lowerG i then 0 else 48) := by
  unfold vAt gVal; cases lowerG i <;> simp
theorem vAt_bound (c : LCtx) (i : Nat) : (c.vAt i + 16 ≤ c.blk i + 16 ∧ c.blk i ≤ c.vAt i) ∨
    (c.blk i + 48 = c.vAt i) := by
  rw [vAt_eq]; cases lowerG i <;> simp
theorem oAt_props (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    c.oAt i % 8 = 0 ∧ Verify.WIT + 7664 ≤ c.oAt i ∧ c.oAt i + 32 ≤ 0x7000 ∧ c.oAt i + 16 ≤ c.vAt i + 16 ∧
      c.vAt i + 16 ≤ c.oAt i + 32 ∧ (lowerG i = true → c.oAt i + 16 = c.vAt i) ∧
      (lowerG i = false → c.oAt i = c.vAt i) := by
  have hb := c.blk_props hc i hi
  rw [vAt_eq]; unfold oAt
  cases h : lowerG i <;> simp <;> omega
/-- Every byte a chain writes lies in its layer's chain area (chain 0's destination spills 16 bytes past it). -/
theorem chainWr_range (c : LCtx) (hc : c.ok) {j A : Nat} (hj : j ≤ 42) (h : c.chainWr j A) :
    c.S6 - 520 ≤ A ∧ A < c.S6 - 520 + 2248 + (if j = 0 then 16 else 0) := by
  have hlo := hc.2.2.2.2.1
  have := lowerSlot_props j hj
  unfold chainWr oAt blk at h
  simp only [lowerG, lowerSlot, decide_eq_true_eq] at h this ⊢
  split_ifs at h this ⊢ <;> omega
theorem chainWr_range' (c : LCtx) {j A : Nat} (hj : j ≤ 42) (h : c.chainWr j A) :
    c.S6 - 520 ≤ A ∧ A < c.S6 - 520 + 2264 := by
  have := lowerSlot_props j hj
  unfold chainWr oAt blk at h
  simp only [lowerG, lowerSlot, decide_eq_true_eq] at h this ⊢
  split_ifs at h this ⊢ <;> omega
/-- Coarse shape of the chain frame (the chain blocks lumped into the chain area). -/
theorem Wr_range (c : LCtx) {i A : Nat} (hi : i ≤ 43) (h : c.Wr i A) :
    (c.bufferSlot c.i0 ≤ A ∧ A < c.bufferEnd i ∧ (c.i0 = 0 → c.bufferSlot 1 ≤ A)) ∨
      (c.S6 - 520 ≤ A ∧ A < c.S6 - 520 + 2264) ∨
      (c.i0 = 0 ∧ 0 < i ∧ c.bufferSlot 0 - 16 ≤ A ∧ A < c.bufferSlot 0 + 16) := by
  rcases h with h | ⟨j, -, hji, hj⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (c.chainWr_range' (by omega) hj))
  · exact Or.inr (Or.inr h)
/-- Pairing stage 1: a chain processed earlier never wrote a byte of a later chain's 64-byte block. -/
theorem chainWr_disj (c : LCtx) {j k A : Nat} (hjk : j < k) (hk : k ≤ 42) (h : c.chainWr j A) :
    A < c.blk k ∨ c.blk k + 64 ≤ A := by
  unfold chainWr oAt blk at h
  unfold blk
  simp only [lowerG, lowerSlot, decide_eq_true_eq] at h ⊢
  split_ifs at h ⊢ <;> omega
/-- A chain's own writes miss its pads and its header pad word. -/
theorem chainWr_self (c : LCtx) (hc : c.ok) {i A : Nat} (hi : i ≤ 42) (h : c.chainWr i A) :
    ¬ (c.blk i + (if lowerG i then 32 else 0) ≤ A ∧ A < c.blk i + (if lowerG i then 32 else 0) + 16) ∧
    ¬ (c.blk i + (if lowerG i then 48 else 32) ≤ A ∧ A < c.blk i + (if lowerG i then 48 else 32) + 16) ∧
    ¬ (c.blk i + 24 ≤ A ∧ A < c.blk i + 32) := by
  have hb := c.blk_props hc i hi
  unfold chainWr oAt at h
  cases hg : lowerG i <;> simp [hg] at h ⊢ <;> omega
theorem slotL_mono (i j : Nat) (h : i ≤ j) : slotL i ≤ slotL j := by unfold slotL; split_ifs <;> omega
theorem slotL_props (i : Nat) (hi : i ≤ 42) : slotL i % 16 = 0 ∧ 768 ≤ slotL i ∧ slotL i + 32 ≤ 0x5D0 := by
  unfold slotL; split <;> omega
theorem bufferSlot_props (c : LCtx) (i : Nat) (hi : i ≤ 42) :
    c.bufferSlot i % 8 = 0 ∧ 23056 ≤ c.bufferSlot i ∧ c.bufferSlot i + 32 ≤ 25936 := by
  have hb : 18928 ≤ ClaudeWCT.W9.T3M.leafBufferBase c.lay ∧
      ClaudeWCT.W9.T3M.leafBufferBase c.lay ≤ 21088 ∧
      ClaudeWCT.W9.T3M.leafBufferBase c.lay % 8 = 0 := by
    generalize c.lay = lay
    fin_cases lay <;> decide +kernel
  have hs := slotL_props i hi
  unfold bufferSlot bufferOffset Verify.WIT
  omega

theorem bufferEnd_bounds (c : LCtx) (i : Nat) :
    c.bufferSlot i ≤ c.bufferEnd i ∧ c.bufferEnd i ≤ c.bufferSlot i + 16 := by
  unfold bufferEnd; split <;> omega

theorem bufferEnd_mono (c : LCtx) (i : Nat) : c.bufferEnd i ≤ c.bufferEnd (i+1) := by
  have h := c.bufferEnd_bounds i
  have h' := c.bufferEnd_bounds (i+1)
  unfold bufferSlot slotL at *
  split_ifs at * <;> omega

theorem bufferWr_mono (c : LCtx) (i A : Nat) : c.bufferWr i A → c.bufferWr (i+1) A := by
  intro h
  have hm := c.bufferEnd_mono i
  unfold bufferWr at *
  rcases h with h | ⟨j, hj0, hji, hj⟩ | h
  · left; exact ⟨h.1, by omega, h.2.2⟩
  · right; left; exact ⟨j, hj0, by omega, hj⟩
  · right; right; omega

theorem bufferWr_copy (c : LCtx) (i A : Nat) (hi0 : c.i0 ≤ i) (hiz : 0 < i)
    (hlo : c.bufferSlot i ≤ A) (hhi : A < c.bufferSlot i + 16) : c.bufferWr (i+1) A := by
  have h := c.bufferEnd_bounds (i+1)
  have hmon := slotL_mono c.i0 i hi0
  unfold bufferWr bufferSlot at *
  left
  unfold slotL at *
  split_ifs at * <;> omega

theorem bufferWr_hash (c : LCtx) (i A : Nat) (hi0 : c.i0 ≤ i) (hiz : 0 < i) (hn : c.dig i ≠ 7)
    (hlo : c.bufferSlot i ≤ A) (hhi : A < c.bufferSlot i + 32) : c.bufferWr (i+1) A := by
  have he : c.bufferEnd (i+1) = c.bufferSlot (i+1) + (if 0 < i then 16 else 0) := by
    simp only [bufferEnd, Nat.add_sub_cancel]
    split_ifs <;> omega
  have hmon := slotL_mono c.i0 i hi0
  unfold bufferWr
  left
  rw [he]
  unfold bufferSlot slotL at *
  split_ifs at * <;> omega

theorem outSlot_ne (c : LCtx) (i : Nat) (hi : i ≠ 0) : c.outSlot i = c.bufferSlot i := by
  unfold outSlot bufferSlot outL; rw [if_neg hi]
theorem outSlot_zero (c : LCtx) : c.outSlot 0 + 16 = c.bufferSlot 0 := by
  unfold outSlot bufferSlot outL slotL; simp
theorem bufferWr_hash0 (c : LCtx) (A : Nat) (hi0 : c.i0 = 0)
    (hlo : c.outSlot 0 ≤ A) (hhi : A < c.outSlot 0 + 32) : c.bufferWr 1 A := by
  have e := c.outSlot_zero
  unfold bufferWr
  right; right; omega
theorem stepHigh_lt (i m : Nat) (hm : m < 6) : stepHigh i m = lowerG i := by
  unfold stepHigh; cases lowerG i <;> simp <;> omega
theorem stepHigh_six (i : Nat) : stepHigh i 6 = decide (i = 0) := by
  unfold stepHigh; simp
theorem bufferSafe_end (c : LCtx) (i : Nat) (hs : c.bufferSafe i) :
    c.bufferEnd i = c.bufferSlot i := by
  rcases hs.2 with h | h | h
  · simp [bufferEnd,h]
  · simp [bufferEnd,h]
  · simp [bufferEnd,h.2.2]

theorem bufferSafe_protected (c : LCtx) (hc : c.ok) (i A : Nat) (hi : i ≤ 42) (hs : c.bufferSafe i)
    (hb : c.blk 0 + 64 ≤ c.bufferSlot 0) (ha : c.bufferSlot i ≤ A) : ¬c.bufferWr i A := by
  rw [bufferWr,c.bufferSafe_end i hs]
  rintro (h | ⟨j, -, hji, hj⟩ | h)
  · unfold bufferSlot slotL at *; split_ifs at * <;> omega
  · have hr := c.chainWr_range hc (by omega) hj
    have h0 : c.blk 0 = c.S6 - 520 + 2184 := rfl
    have hz : i ≠ 0 := by omega
    unfold bufferSlot slotL at *
    split_ifs at * <;> omega
  · unfold bufferSlot slotL at *; split_ifs at * <;> omega

theorem bufferVal_at {c : LCtx} (hc : c.ok) {s0 t : MachineState} (h0 : c.bufferOrig s0)
    {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hs : c.bufferSafe i)
    (hb : c.blk 0 + 64 ≤ c.bufferSlot 0) (hF : Frame s0 t (c.bufferWr i)) :
    DigAt t (c.bufferSlot i) (c.bufferVal i) := by
  have hp := c.bufferSlot_props i hi.2
  have o0 := h0 i hi.1 hi.2 0 (by omega)
  have o1 := h0 i hi.1 hi.2 1 (by omega)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at o0 o1
  have f0 := hF (c.bufferSlot i) (by omega) (c.bufferSafe_protected hc i _ hi.2 hs hb (by omega))
  have f1 := hF (c.bufferSlot i+8) (by omega) (c.bufferSafe_protected hc i _ hi.2 hs hb (by omega))
  have hW : Verify.WIT ≤ c.bufferSlot i := by unfold Verify.WIT; omega
  have t0 : OrigW c.w t (c.bufferSlot i) := by unfold OrigW at *; rw [f0]; exact o0
  have t1 : OrigW c.w t (c.bufferSlot i+8) := by unfold OrigW at *; rw [f1]; exact o1
  rw [bufferVal,if_pos hs]
  exact DigAt_origW t0 t1 hW
theorem bufferSlot_mono (c : LCtx) (i j : Nat) (h : i ≤ j) :
    c.bufferSlot i ≤ c.bufferSlot j := by
  have := slotL_mono i j h
  unfold bufferSlot
  omega

theorem bufferSlot_gap (c : LCtx) (i j : Nat) (h : i < j) :
    c.bufferSlot i + 16 ≤ c.bufferSlot j := by
  unfold bufferSlot slotL
  split_ifs <;> omega

theorem bufferArea_slot (c : LCtx) : c.S6 - 520 + 2248 ≤ c.bufferSlot 0 := by
  have hs : c.bufferSlot 0 = Verify.WIT + ClaudeWCT.W9.T3M.leafBufferBase c.lay := by
    unfold bufferSlot bufferOffset Verify.WIT
    rw [show slotL 0 = 768 from rfl]
    have : 18928 ≤ ClaudeWCT.W9.T3M.leafBufferBase c.lay := by
      generalize c.lay = lay; fin_cases lay <;> decide +kernel
    omega
  rw [hs]
  exact c.bufferBound
theorem bufferBound_slot (c : LCtx) : c.blk 0 + 64 ≤ c.bufferSlot 0 := by
  have := c.bufferArea_slot
  unfold blk; rw [show lowerSlot 0 = 2184 from rfl]; omega

theorem block_before_buffer (c : LCtx) (i j : Nat) (hi : i ≤ 42) : c.blk i + 64 ≤ c.bufferSlot j := by
  have h := c.bufferArea_slot
  have hm := c.bufferSlot_mono 0 j (by omega)
  have := lowerSlot_props i hi
  unfold blk at *
  omega

theorem block_gap_buffer (c : LCtx) (i j : Nat) (hi : 0 < i) (hi42 : i ≤ 42) :
    c.blk i + 80 ≤ c.bufferSlot j := by
  have h := c.bufferArea_slot
  have hm := c.bufferSlot_mono 0 j (by omega)
  have := (lowerSlot_props i hi42).2.2.2 hi
  unfold blk at *
  omega

theorem bufferE_eval' (c : LCtx) {s : MachineState}
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (k : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 k)).eval s = BitVec.ofNat 64 (c.bufferOffset + k) := by
  rw [addC_eval]
  simp only [E.eval, h4, ofNat_add_ofNat]
theorem bufferE_eval (c : LCtx) {s : MachineState}
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 (slotL i))).eval s = BitVec.ofNat 64 (c.bufferSlot i) := by
  rw [addC_eval]
  simp only [E.eval, h4, ofNat_add_ofNat, bufferSlot]

theorem bufferAddr_eval (c : LCtx) {s : MachineState}
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i k : Nat) :
    (⟨some (.reg .x4), BitVec.ofNat 64 (slotL i+k)⟩ : Addr).eval s =
      BitVec.ofNat 64 (c.bufferSlot i+k) := by
  simp only [Addr.eval, E.eval, h4, ofNat_add_ofNat, bufferSlot, Nat.add_assoc]

theorem WrIn_next (c : LCtx) (i A : Nat) (hi0 : c.i0 ≤ i) (hi42 : i ≤ 42)
    (h : c.WrIn i A) : c.Wr (i+1) A := by
  rcases h with h | h
  · exact c.bufferWr_mono i A h
  · exact Or.inr (Or.inl ⟨i, hi0, by omega, h⟩)

theorem base_off (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S6 + (offL i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  have := lowerSlot_props i hi
  unfold offL blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S6 + lowerSlot i - 520 = c.S6 - 520 + lowerSlot i by
    omega]
theorem base_off0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    BitVec.ofNat 64 c.S6 + offL i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  have := lowerSlot_props i hi
  unfold offL blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S6 + lowerSlot i - 520 = c.S6 - 520 + lowerSlot i by
    omega]
/-- The hash destination register of an interior step (`gOut`). -/
theorem oAt_eval (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) (x : Word) (hx : x = BitVec.ofNat 64 (c.blk i)) :
    x + gOut (lowerG i) = BitVec.ofNat 64 (c.oAt i) := by
  have hb := c.blk_props hc i hi
  subst hx
  unfold oAt
  cases hg : lowerG i
  · simp only [Bool.false_eq_true, if_false]
    rw [show gOut false = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · simp only [if_true]
    rw [show gOut true = BitVec.ofNat 64 18446744073709551600 by unfold gOut; rfl, BitVec.ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show c.blk i + 18446744073709551600 = (c.blk i - 16) + 2^64 by omega,
      Nat.add_mod_right]
theorem known_get (c : LCtx) {s : MachineState} (h : ∀ p ∈ c.known, s.getReg p.1 = p.2) {r : Reg} {v : Word}
    (hm : (r, v) ∈ c.known) : s.getReg r = v := h _ hm
theorem w0_hdr0 (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 8) :
    BitVec.ofNat 64 (c.w0 i + 256 * m) = (chainHeader c.lay c.tree c.leaf (i + c.koff) m).extractLsb' 0 64 := by
  rw [chainHeader_low_bounded _ _ _ _ _ (by have := hc.2.2.1; omega) hm
    hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1]
  congr 1; unfold w0; omega
theorem w0_lt (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) : c.w0 i + 256 * m < 2 ^ 64 := by
  obtain ⟨-, -, hk, -⟩ := hc
  have hh := packedHi_lt c.lay c.tree c.leaf
  unfold w0 packedPrefix; omega
theorem w1_lt (c : LCtx) : c.w1 < 2 ^ 64 := hdr1_lt _ _
set_option maxRecDepth 20000 in
theorem chain_hashInput (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 8) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.pad0At i) (c.pad0 i)) (hp1 : DigAt t (c.pad1At i) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 256 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i)
    (hv : DigAt t (c.vAt i) v) :
    hashInput t = toQ (chainInputL c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) (c.padHeader i) v
      (lowerG i)) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputL_length _ _ _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputL, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two]
  rw [vAt_eq] at hv
  simp only [pad0At, pad1At] at hp0 hp1
  split
  · rename_i hg
    simp only [hg, if_true, Nat.add_zero] at hv hp0 hp1
    rw [hv.1, hv.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp0.1, hp0.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hp1.1, hp1.2, w0_hdr0 c hc i m hi hm]
    rfl
  · rename_i hg
    simp only [hg, Bool.false_eq_true, if_false, Nat.add_zero] at hv hp0 hp1
    rw [hp0.1, hp0.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_hdr0 c hc i m hi hm]
    rfl
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem orig_frame {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := (c.blk_props hc i hi.2)
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1 i hi.1 hi.2 k hk
/-- Pairing stage 1: no chain processed before chain `i` (nor a buffer write) touched chain `i`'s block. -/
theorem notWr_block (c : LCtx) (hc : c.ok) {i A : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (h1 : c.blk i ≤ A)
    (h2 : A < c.blk i + 64) : ¬ c.Wr i A := by
  have hbb := c.block_before_buffer i c.i0 hi.2
  have harea := c.bufferArea_slot
  have hls := lowerSlot_props i hi.2
  rintro (h | ⟨j, -, hji, hj⟩ | h)
  · omega
  · rcases c.chainWr_disj hji hi.2 hj with h' | h' <;> omega
  · have : 0 < i := h.2.1
    have := hls.2.2.2 this
    unfold blk at h1 h2
    omega
theorem orig_at {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i A : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hA1 : c.blk i ≤ A) (hA2 : A + 8 ≤ c.blk i + 64)
    (hA8 : (A - c.blk i) % 8 = 0) (hW : ¬ W A) : OrigW c.w t A := by
  have e : A = c.blk i + 8 * ((A - c.blk i) / 8) := by omega
  rw [e] at hW ⊢
  exact orig_frame hF h0 hc hi (by omega) hW
theorem dig_at {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i A : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hA1 : c.blk i ≤ A) (hA2 : A + 16 ≤ c.blk i + 64)
    (hA8 : (A - c.blk i) % 8 = 0) (hW0 : ¬ W A) (hW1 : ¬ W (A + 8)) :
    DigAt t A (ClaudeWCT.W9.T3M.wdig c.w (A - Verify.WIT)) := by
  have hb := c.blk_props hc i hi.2
  exact DigAt_origW (orig_at hF h0 hc hi hA1 (by omega) hA8 hW0) (orig_at hF h0 hc hi (by omega) (by omega)
    (by omega) hW1) (by omega)
theorem pads_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : c.i0 ≤ i ∧ i ≤ 42) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.pad0At i) (c.pad0 i) ∧ DigAt t (c.pad1At i) (c.pad1 i) := by
  have hb := c.blk_props hc i hi.2
  unfold pad0 pad1
  by_cases hg : lowerG i = true
  · have e0 : c.pad0At i = c.blk i + 32 := by simp [pad0At, hg]
    have e1 : c.pad1At i = c.blk i + 48 := by simp [pad1At, hg]
    have nc : ∀ A, c.chainWr i A → A < c.blk i + 24 := by
      intro A h; unfold chainWr oAt at h; simp only [hg, if_true] at h; omega
    have nW : ∀ A, c.blk i + 32 ≤ A → A < c.blk i + 64 → ¬ c.WrIn i A := by
      intro A h1 h2 hw
      rcases hw with hw | hw
      · exact c.notWr_block hc hi (by omega) h2 hw
      · have := nc A hw; omega
    rw [e0, e1]
    exact ⟨dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega)),
      dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega))⟩
  · have e0 : c.pad0At i = c.blk i := by simp [pad0At, hg]
    have e1 : c.pad1At i = c.blk i + 32 := by simp [pad1At, hg]
    have nc : ∀ A, c.chainWr i A → (c.blk i + 16 ≤ A ∧ A < c.blk i + 24) ∨ c.blk i + 48 ≤ A := by
      intro A h; unfold chainWr oAt at h; simp only [hg, Bool.false_eq_true, if_false] at h; omega
    have nW : ∀ A, c.blk i ≤ A → A < c.blk i + 48 → (A < c.blk i + 16 ∨ c.blk i + 32 ≤ A) → ¬ c.WrIn i A := by
      intro A h1 h2 h3 hw
      rcases hw with hw | hw
      · exact c.notWr_block hc hi h1 (by omega) hw
      · have := nc A hw; omega
    rw [e0, e1]
    exact ⟨dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega))
        (nW _ (by omega) (by omega) (by omega)),
      dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega))
        (nW _ (by omega) (by omega) (by omega))⟩
theorem rungPc_succ (c : LCtx) (i m : Nat) (hd : c.dig i ≤ m) : c.rungPc i (m + 1) = c.rungPc i m + 2 := by
  unfold rungPc; split_ifs <;> omega
theorem dig_lt (c : LCtx) (hc : c.ok) (i : Nat) (hi : i < 42) : c.dig i < 8 := by
  unfold dig; split_ifs <;> omega
theorem dig42 (c : LCtx) : c.dig 42 = c.ck := by unfold dig; simp
set_option maxHeartbeats 1000000 in
theorem rungPc_end (c : LCtx) (i : Nat) (hi : i ≤ 42) (hd : c.dig i < 7) : c.rungPc i 6 + 3 = c.endPc i := by
  by_cases h42 : i = 42
  · subst h42
    have e := c.dig42
    unfold rungPc endPc startPc partLen
    simp only [show ¬ (42 % 3 = 0 ∧ (42 : Nat) ≠ 42) by decide +kernel, if_false, if_true, e] at hd ⊢
    split_ifs <;> omega
  · have e1 : i % 3 = 1 → c.dig (3 * (i / 3) + 1) = c.dig i := fun h => by rw [show 3 * (i / 3) + 1 = i by omega]
    have e2 : i % 3 = 2 → c.dig (3 * (i / 3) + 2) = c.dig i := fun h => by rw [show 3 * (i / 3) + 2 = i by omega]
    unfold rungPc endPc startPc tb tB tC tX pcX pcC pcB partLen
    simp only [if_neg h42]
    split_ifs <;> omega
theorem prehash_step (c : LCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputL c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) (c.padHeader i) v
        (lowerG i)) ∧
      ∀ a : BitVec 256,
        (m < 6 → c.StepInv s0 i acc (m + 1) (Verify.vHalf (stepHigh i m) a) (writeHash t a)) ∧
        (m = 6 → c.EndInv s0 i (acc ++ [Verify.vHalf (stepHigh i m) a]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  have ho := c.oAt_props hc i hi.2
  have hs := c.bufferSlot_props i hi.2
  have hs0 := c.bufferSlot_props 0 (by omega)
  have hw0 := c.outSlot_zero
  have hwi : i ≠ 0 → c.outSlot i = c.bufferSlot i := c.outSlot_ne i
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide +kernel)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide +kernel)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  have hwb : c.outSlot i % 8 = 0 ∧ c.outSlot i + 32 ≤ 25936 := by
    by_cases hi0 : i = 0
    · subst hi0; omega
    · rw [hwi hi0]; omega
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = 6 then c.outSlot i else c.oAt i) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi.2 (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm6 => ?_, fun hm6 => ?_⟩
    ·
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.oAt i) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; exact h)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.oAt i ≤ A ∧ A < c.oAt i + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      have hhdr : c.oAt i + 32 ≤ c.blk i + 16 ∨ c.blk i + 32 ≤ c.oAt i := by
        unfold oAt; cases lowerG i <;> simp <;> omega
      have hnew : DigAt (writeHash t a) (c.vAt i) (Verify.vHalf (stepHigh i m) a) := by
        rw [stepHigh_lt i m (by omega)]
        cases hg : lowerG i
        · rw [(ho.2.2.2.2.2.2 hg).symm, Verify.vHalf_false]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
        · rw [(ho.2.2.2.2.2.1 hg).symm, Verify.vHalf_true]
          exact DigAt.writeHash_hi t a _ d12 (by omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        h25, ⟨?_, ?_, ?_⟩, hnew,
        by rw [getReg_writeHash]; exact h10, by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
        have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
        have : c.oAt i + 32 ≤ c.blk i + 80 := by unfold oAt; cases lowerG i <;> simp <;> omega
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0 packedPrefix; have := hc.2.2.1; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0 packedPrefix; have := hc.2.2.1; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    ·
      subst hm6
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.outSlot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have hpcE : (writeHash t a).pc = pcOf (c.endPc i) := by
        have hd7 : c.dig i < 7 := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi.2 hd7, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
      by_cases hi0 : i = 0
      · subst hi0
        have hz : c.i0 = 0 := by omega
        have hacc : acc.length = 0 := by omega
        have fW : Frame s0 (writeHash t a) (c.Wr (0 + 1)) := (hF.trans fr).mono (by
          intro A _ h
          rcases h with h | h
          · exact c.WrIn_next 0 A hi.1 hi.2 h
          · exact c.bufferWr_hash0 A hz h.1 h.2)
        refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen]; omega,
          h25, hpcE⟩
        rw [List.length_append, List.length_singleton] at hj
        have hj2 : j = acc.length := by omega
        subst hj2
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
          show c.i0 + acc.length = 0 by omega]
        have hh : stepHigh 0 6 = true := by decide
        rw [hh, Verify.vHalf_true, ← hw0]
        exact DigAt.writeHash_hi t a _ d12 (by omega)
      · have d12' : t.getReg .x12 = BitVec.ofNat 64 (c.bufferSlot i) := by rw [d12, hwi hi0]
        have fr' := hdst _ d12' (by omega)
        have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr').mono (by
          intro A _ h
          rcases h with h | h
          · exact c.WrIn_next i A hi.1 hi.2 h
          · exact c.bufferWr_hash i A hi.1 (by omega) (by omega) h.1 h.2)
        have hh : stepHigh i 6 = false := by unfold stepHigh; simp [hi0]
        rw [hh, Verify.vHalf_false]
        refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen]; omega,
          h25, hpcE⟩
        · rw [List.length_append, List.length_singleton] at hj
          by_cases hjl : j < acc.length
          · have hj' := hS j hjl
            have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
            have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
            have hmono : c.bufferSlot (c.i0 + j) + 16 ≤ c.bufferSlot i := by unfold bufferSlot slotL; split_ifs <;> omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
            exact hj'.frame fr' (by omega) (by omega) (by omega)
          · have hj2 : j = acc.length := by omega
            subst hj2
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
              show c.i0 + acc.length = i by omega]
            exact DigAt.writeHash_lo t a _ d12' (by omega)
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem posE_eval (c : LCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (m : Nat) (hm : m ≤ 6) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  interval_cases m
  · rfl
  · exact kr .x7 1 (by simp [known]) (by decide +kernel)
  · exact kr .x13 2 (by simp [known]) (by decide +kernel)
  · exact kr .x19 3 (by simp [known]) (by decide +kernel)
  · exact kr .x20 4 (by simp [known]) (by decide +kernel)
  · exact kr .x21 5 (by simp [known]) (by decide +kernel)
  · exact kr .x26 6 (by simp [known]) (by decide +kernel)
theorem w0_low (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) :
    (BitVec.ofNat 64 (c.w0 i + 256 * m)).toNat % 256 = 128 + i + c.koff ∧
      (BitVec.ofNat 64 (c.w0 i + 256 * m)).toNat / 2 ^ 16 = packedHi c.lay c.tree c.leaf := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi hm)]
  have := hc.2.2.1
  unfold w0 packedPrefix; constructor <;> omega
theorem rung_piece (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i ≤ 42) (hm : m ≤ 6) (hp : p < 257214)
    (hrun : vrun p 3 = some (rungRB m (if m = 6 then some (outL i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = 6 → t.getReg .x12 = BitVec.ofNat 64 (c.outSlot i)) ∧ (m < 6 → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 256 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = 6 then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  set r := rungRB m (if m = 6 then some (outL i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungRB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 17⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (17 : Word) = BitVec.ofNat 64 17 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun hp s hpc hobl
  have hec := piece_ecall hrun hp s hobl (by simp [hr, rungRB])
  have hn : r.steps = (if m = 6 then 2 else 1) ∧ r.cycles = (if m = 6 then 2 else 1) := by
    simp only [hr, rungRB]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungRB_keeps m (if m = 6 then some (outL i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 1 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungRB]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h6 => ?_, fun h6 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungRB, if_pos h6]
    rw [RegFile.get_set_self _ _ (by decide +kernel)]
    exact c.bufferE_eval' ((hR .x4 (by decide +kernel)).trans (hk (.x4, BitVec.ofNat 64 c.bufferOffset) (by simp [known]))) (outL i)
  · rw [Result.toState_getReg]
    simp only [hr, rungRB, if_neg (show m ≠ 6 by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have := c.lay.isLt
    have hkoff := hc.2.2.1
    rw [stepByte _ _ _ _ (by omega) (by omega) (packedHi_lt _ _ _) hl hj]
    congr 1; unfold w0 packedPrefix; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungRB]
    by_cases h6 : m = 6 <;> simp [h6, E.eval]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem not_mem_sub {x : Reg} {ws : List Reg} (hx : x ∉ chainRegs) (h : ws ⊆ chainRegs) : x ∉ ws :=
  fun hm => hx (h hm)
theorem w0_low0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    (BitVec.ofNat 64 (c.w0 i)).toNat % 256 = 128 + i + c.koff ∧
      (BitVec.ofNat 64 (c.w0 i)).toNat / 2 ^ 16 = packedHi c.lay c.tree c.leaf := by
  have := c.w0_low hc i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this
theorem rung_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hp : c.rungPc i m < 257214)
    (hrun : vrun (c.rungPc i m) 3 = some (rungRB m (if m = 6 then some (outL i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi.2 hm hp hrun s hpc hR h10 hH
  have hvb := c.vAt_bound i
  have hs := c.bufferSlot_props i hi.2
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
    have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide +kernel)]; exact h10
  · by_cases h6 : m = 6
    · rw [h12a h6, if_pos h6]
    · rw [h12b (by omega), h12, if_neg h6]
  · rw [hpc']
theorem val_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.vAt i) (c.val i) := by
  unfold val
  rw [vAt_eq]
  cases hg : lowerG i <;> simp only [Bool.false_eq_true, if_true, if_false] <;>
    exact dig_at hF h0 hc hi (by omega) (by omega) (by omega) (c.notWr_block hc hi (by omega) (by omega))
      (c.notWr_block hc hi (by omega) (by omega))
theorem Wr_mono (c : LCtx) (i : Nat) (A : Nat) (h : c.Wr i A) : c.WrIn i A := Or.inl h
theorem bv385 (a b : Nat) :
    BitVec.ofNat 64 (a + 385) + (BitVec.ofNat 64 b - BitVec.ofNat 64 385) = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem header_load (c : LCtx) {s : MachineState} (i d : Nat)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 c.x28v) :
    (hLoad i d).eval s = BitVec.ofNat 64 (c.w0 i + 256 * d) := by
  rw [hLoad, addC_eval]
  show s.getReg .x28 + (BitVec.ofNat 64 (i + 256 * d) - BitVec.ofNat 64 385) = _
  rw [h28, LCtx.x28v, bv385]
  congr 1
  unfold w0
  omega
theorem padHeader_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0)
    {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hF : Frame s0 t (c.Wr i)) :
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i := by
  have hb := c.blk_props hc i hi.2
  have h := orig_at hF h0 hc hi (A := c.blk i + 24) (by omega) (by omega) (by omega)
    (c.notWr_block hc hi (by omega) (by omega))
  simpa only [OrigW, padHeader, show c.blk i + 24 - Verify.WIT = c.blk i - Verify.WIT + 24 by omega] using h
theorem fetch_pc_congr {u v : MachineState} (h : u.pc = v.pc) : fetch vimage u = fetch vimage v := by
  unfold fetch; rw [h]
theorem headJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 257214) (hp1 : c.rungPc i (c.dig i) + landOff (c.dig i) < 257214)
    (hrun1 : vrun (c.startPc i) 7 = some (headJHB .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i
      (c.dig i) (hSlot i (c.dig i)) (lowerG i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 =
      some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  have hs := c.bufferSlot_props i hi.2
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE : ∀ k, k ≤ 80 → (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
    intro k hk'
    simp only [kAt, Addr.eval, E.eval, h22]
    exact c.base_off hc i hi.2 k hk'
  set r := headJHB .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i))
    (lowerG i) with hr
  have htable := c.header_load i (c.dig i)
    (kr _ _ (by simp [known]) (by decide +kernel))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJHB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun1 hp0 s hpc hobl
  have hn : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headJHB_keeps .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i))
    (lowerG i)
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i hi.2
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 256 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headJHB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA, htable]
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hp24 := padHeader_at hc h0 hi hF
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hvb := c.vAt_bound i
  have hpcT : (r.toState s).pc = pcOf (c.rungPc i (c.dig i) + landOff (c.dig i)) := by
    rw [Result.toState_pc]; simp only [hr, headJHB, E.eval]
  have hec : fetch vimage (r.toState s) = some (.base .ECALL) := by
    have hE := piece_ecall hrun2 hp1 (r.toState s) (by simp [ecallR, SymState.init]) rfl
    rw [← hE]
    apply fetch_pc_congr
    rw [hpcT, Result.toState_pc]; simp only [ecallR, E.eval]
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
    have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega)]; exact hp24
  · rw [Result.toState_getReg]; simp only [hr, headJHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headJHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    by_cases h6 : c.dig i = 6
    · simp only [hSlot, h6, if_true, E.eval]
      exact c.bufferE_eval' h4 (outL i)
    · simp only [hSlot, h6, if_false]
      rw [addC_eval]; exact c.oAt_eval hc i hi.2 _ a0e
  · rw [hpcT]; simp only [landOff]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem kAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h22]
  exact c.base_off hc i hi k hk
theorem lAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (lAt .x22 (offL i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h22]
  rw [c.base_off hc i hi k hk]
theorem copy_mem (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i : Nat)
    (hi : i ≤ 42) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMemB .x22 (offL i) (slotL i) (lowerG i)) (BitVec.ofNat 64 A) =
      if A = c.bufferSlot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = c.bufferSlot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := c.bufferSlot_props i hi
  have hg : gVal (lowerG i) ≤ 48 := by unfold gVal; split <;> omega
  unfold copyMemB
  rw [memEval_two s _ _ _ _ (c.bufferSlot i + 8) (c.bufferSlot i) A (c.bufferAddr_eval h4 i 8) (by simpa using c.bufferAddr_eval h4 i 0) (by omega) (by omega) hA,
    c.lAt_eval hc h22 i hi _ (by omega), c.lAt_eval hc h22 i hi _ (by omega)]
  simp only [vAt, Nat.add_assoc]
theorem copy_obl (c : LCtx) (hc : c.ok) {s : MachineState}
    (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i : Nat)
    (hi : i ≤ 42) : ∀ o ∈ copyOblB .x22 (offL i) (slotL i) (lowerG i), o.holds s := by
  have hb := c.blk_props hc i hi
  have hg : gVal (lowerG i) = 0 ∨ gVal (lowerG i) = 48 := by unfold gVal; split <;> simp
  have hs := c.bufferSlot_props i hi
  simp only [copyOblB, copyObl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro o ((rfl | rfl) | (rfl | rfl))
  · show accessValid ((⟨some (.reg .x4), BitVec.ofNat 64 (slotL i+8)⟩ : Addr).eval s) 8 = true
    rw [c.bufferAddr_eval h4 i 8]
    exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((⟨some (.reg .x4), BitVec.ofNat 64 (slotL i)⟩ : Addr).eval s) 8 = true
    rw [show (⟨some (.reg .x4), BitVec.ofNat 64 (slotL i)⟩ : Addr).eval s = BitVec.ofNat 64 (c.bufferSlot i) by simpa using c.bufferAddr_eval h4 i 0]
    exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x22 (offL i) (gVal (lowerG i) + 8)).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi _ (by omega)]
    exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x22 (offL i) (gVal (lowerG i))).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi _ (by omega)]
    exact valid_ofNat _ _ (by omega) (by omega)
theorem copy_post (c : LCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (hiz : 0 < i) (acc : List Digest) (hlen : acc.length = i - c.i0) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (c.bufferSlot (c.i0 + j)) (acc.getD j 0))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      memEval s (copyMemB .x22 (offL i) (slotL i) (lowerG i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (c.bufferSlot (c.i0 + j)) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  have hs := c.bufferSlot_props i hi.2
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = c.bufferSlot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = c.bufferSlot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h22 h4 i hi.2 A hA)
  have hfr : Frame s t (fun A => A = c.bufferSlot i + 8 ∨ A = c.bufferSlot i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have hlo := hc.2.2.2.2.1
    have hsm := c.bufferSlot_mono c.i0 i hi.1
    rcases h with h | h
    · exact c.bufferWr_mono i A h
    · exact c.bufferWr_copy i A hi.1 hiz (by omega) (by omega)
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
      have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
      have hmono : c.bufferSlot (c.i0 + j) + 16 ≤ c.bufferSlot i := by unfold bufferSlot slotL; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        show c.i0 + acc.length = i by omega]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2
theorem copyJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hiz : 0 < i) (first : Bool)
    (hfirst : first = true → i = 0 ∧ c.koff = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 257214)
    (hrun : vrun (c.startPc i) 7 = some (copyNB .x22 (offL i) (slotL i) (c.endPc i) (lowerG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyNB .x22 (offL i) (slotL i) (c.endPc i) (lowerG i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyNB] using c.copy_obl hc h22 h4 i (by omega))
  have hkeep := copyNB_keeps .x22 (offL i) (slotL i) (c.endPc i) (lowerG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ hiz acc hlen hF hS h22 h4
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl
theorem copyF_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hi0 : i ≠ 0) (hp0 : c.startPc i < 257214)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFHB .x22 (offL i) (slotL i) (c.startPc i) (lowerG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyFHB .x22 (offL i) (slotL i) (c.startPc i) (lowerG i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyFHB] using c.copy_obl hc h22 h4 i (by omega))
  have hkeep := copyFHB_keeps .x22 (offL i) (slotL i) (c.startPc i) (lowerG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ (Nat.pos_of_ne_zero hi0) acc hlen hF hS
    h22 h4 (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFHB, E.eval]; rw [hend]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem headR_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hi0 : i ≠ 0) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 257214)
    (hrp : c.rungPc i (c.dig i) + (if c.dig i = 6 then 2 else 1) = c.startPc i + 4)
    (hrun : vrun (c.startPc i) 8 =
      some (headRVB .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i (lowerG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i (by omega)
  have hs := c.bufferSlot_props i (by omega)
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h22 i (by omega)
  set r := headRVB .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i (lowerG i)
    with hr
  have htable := c.header_load i (c.dig i)
    (kr _ _ (by simp [known]) (by decide +kernel))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRVB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun hp0 s hpc hobl
  have hec := piece_ecall hrun hp0 s hobl (by simp [hr, headRVB])
  have hn : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRVB_keeps .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i
    (lowerG i)
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i (by omega)
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 256 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRVB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA, htable]
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hp24 := padHeader_at hc h0 ⟨hi.1, by omega⟩ hF
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 ⟨hi.1, by omega⟩ hF
  have hvb := c.vAt_bound i
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
    have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega)]; exact hp24
  · rw [Result.toState_getReg]; simp only [hr, headRVB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRVB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    by_cases h6 : c.dig i = 6
    · simp only [h6, if_true, E.eval]
      rw [c.outSlot_ne i hi0]
      exact c.bufferE_eval h4 i
    · simp only [h6, if_false]
      rw [addC_eval]; exact c.oAt_eval hc i (by omega) _ a0e
  · rw [Result.toState_pc, hrp]; simp only [hr, headRVB, E.eval]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem land_mask (n k : Nat) (hk : k ≤ 9) :
    n &&& (512 * (2 ^ k - 1)) = 512 * (n / 512 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (512 : Nat) = 2 ^ 9 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h9 : 9 ≤ j
  · simp only [h9, decide_true, Bool.true_and, show j - 9 + 9 = j by omega]
    by_cases hj : j - 9 < k
    · simp [hj]
    · simp [hj]
  · simp [h9]
theorem even_andNot1' (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]
theorem tab_target (a base b off : Nat) (h : off ≤ base) (ha : a + base + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 base + (BitVec.ofNat 64 b - BitVec.ofNat 64 off) =
      BitVec.ofNat 64 (a + (base - off) + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem field_shl (W s k : Nat) (hs : s ≤ 9) (hk : k ≤ 9) :
    W * 2 ^ s % 2 ^ 64 / 512 % 2 ^ k = W / 2 ^ (9 - s) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, show (512 : Nat) = 2 ^ 9 by norm_num,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < k
  · simp only [hj, decide_true, Bool.true_and, show j + 9 < 64 by omega, show s ≤ j + 9 by omega]
    rw [show j + 9 - s = j + (9 - s) by omega]
  · simp [hj]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem dig8_shift (X t' m : Nat) : X / 8 ^ (3 * t' + m) % 8 = X / 2 ^ (9 * t') / 8 ^ m % 8 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add, show (8 : Nat) ^ (3 * t') = 2 ^ (9 * t') by
    rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul]; ring_nf]
theorem kOf_eq (c : LCtx) (t : Nat) (ht : t < 14) :
    c.kOf t = (if t < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * (t % 7)) % 512 := by
  unfold kOf dig
  by_cases h7 : t < 7
  · simp only [h7, if_true, show 3 * t < 21 by omega, show 3 * t + 1 < 21 by omega, show 3 * t + 2 < 21 by omega]
    rw [show t % 7 = t by omega]
    have e0 : c.d0.toNat / 8 ^ (3 * t) % 8 = c.d0.toNat / 2 ^ (9 * t) % 8 := by
      have := dig8_shift c.d0.toNat t 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d0.toNat / 2 ^ (9 * t) = Y
    norm_num
    omega
  · simp only [h7, if_false, show ¬ 3 * t < 21 by omega, show ¬ 3 * t + 1 < 21 by omega,
      show ¬ 3 * t + 2 < 21 by omega, show 3 * t < 42 by omega, show 3 * t + 1 < 42 by omega,
      show 3 * t + 2 < 42 by omega, if_true]
    rw [show t % 7 = t - 7 by omega, show 3 * t + 1 - 21 = 3 * (t - 7) + 1 by omega,
      show 3 * t + 2 - 21 = 3 * (t - 7) + 2 by omega, show 3 * t - 21 = 3 * (t - 7) by omega]
    have e0 : c.d1.toNat / 8 ^ (3 * (t - 7)) % 8 = c.d1.toNat / 2 ^ (9 * (t - 7)) % 8 := by
      have := dig8_shift c.d1.toNat (t - 7) 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d1.toNat / 2 ^ (9 * (t - 7)) = Y
    norm_num
    omega
theorem kOf_lt (c : LCtx) (t : Nat) (ht : t < 14) : c.kOf t < 512 := by
  rw [c.kOf_eq t ht]; exact Nat.mod_lt _ (by norm_num)
theorem x_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (t : Nat) (ht : t < 13) (hi : c.i0 ≤ 3 * t + 2) (hp : c.tX (3 * t + 2) < 257214)
    (hrun : vrun (c.tX (3 * t + 2)) 5 = some (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7))
      (if t=0 ∨ t=7 then .x27 else .x9)
      (BitVec.ofNat 64 (lowerImm (t+1)))))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3 * t + 2) acc s) :
    ∃ u, Steps vimage s (if 9 * ((t + 1) % 7) = 9 then 2 else 3)
      (if 9 * ((t + 1) % 7) = 9 then 2 else 3) u ∧ c.ChainIn s0 (3 * t + 3) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  set r := xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7))
    (if t=0 ∨ t=7 then .x27 else .x9)
    (BitVec.ofNat 64 (lowerImm (t+1))) with hr
  have hst := piece_steps hrun hp s hpc' (by simp [hr, xJ])
  have hkeep := xJ_keeps (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7))
    (if t=0 ∨ t=7 then .x27 else .x9)
    (BitVec.ofNat 64 (lowerImm (t+1)))
  have hW : s.getReg (if t + 1 < 7 then .x16 else .x17) = (if t + 1 < 7 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide +kernel)
    · exact kr .x17 c.d1 (by simp [known]) (by decide +kernel)
  have h2 : s.getReg (if t=0 ∨ t=7 then .x27 else .x9) =
      BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*(2^9-1)) := by
    have h6 := kr .x27 0x3fe00 (by simp [known]) (by decide +kernel)
    have h2 := kr .x9 0x7fc00 (by simp [known]) (by decide +kernel)
    split_ifs <;> simp_all <;> omega
  have hm := shE_mask_new s _ _ hW (9 * ((t + 1) % 7)) 9 (by omega) (le_refl _)
  have himm := lowerImm_even (t+1)
  have hk1 := c.kOf_lt (t + 1) (by omega)
  have hrow : ((if t + 1 < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * ((t + 1) % 7)) % 2 ^ 9) = c.kOf (t + 1) := by
    rw [c.kOf_eq (t + 1) (by omega)]; rfl
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr bufferWr at h ⊢; rcases h with h | h | h
      · exact Or.inl h
      · right; left; obtain ⟨j, h1, h2, h3⟩ := h; exact ⟨j, h1, by omega, h3⟩
      · right; right; exact ⟨h.1, by omega, h.2.2⟩), hS⟩, by omega, h25, ?_⟩⟩
  rw [Result.toState_pc]
  simp only [hr, xJ, E.eval, BinOp.eval]
  rw [h2]
  have e : ((shE (if t + 1 < 7 then Reg.x16 else Reg.x17) (9 * ((t + 1) % 7))).eval s &&&
      BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*(2^9-1))) =
      BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*c.kOf (t+1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [hm,hrow,BitVec.toNat_ofNat]
    symm; apply Nat.mod_eq_of_lt; split_ifs <;> omega
  rw [e, ofNat_add_ofNat, even_andNot1' _ (by split_ifs <;> omega)]
  have e2 : BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*c.kOf (t+1) +
      (lowerImm (t+1))) = pcOf (entW (t+1) (c.kOf (t+1))) := by
    rw [entW_address _ _ (by omega) hk1]
    congr 1
    split_ifs <;> omega
  rw [e2]
  unfold startPc
  rw [if_neg (by omega), if_pos (by omega), show (3*t+3)/3=t+1 by omega]
theorem xbfJ_keeps (w : Reg) (imm : Word) : Keeps (xbfJ w imm) [.x14] := by
  intro x hx
  simp only [xbfJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem srl54_spare (W : Word) (hW : 2 ^ 63 ≤ W.toNat) : W.toNat / 2 ^ 54 = 512 + W.toNat / 2 ^ 54 % 512 := by
  have := W.isLt
  omega
theorem xbf_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (t : Nat) (ht : t = 5 ∨ t = 12) (hi : c.i0 ≤ 3 * t + 2) (hp : c.tX (3 * t + 2) < 257214)
    (hrun : vrun (c.tX (3 * t + 2)) 4 = some (xbfJ (if t + 1 < 7 then .x16 else .x17)
      (BitVec.ofNat 64 (lowerImm (t+1)))))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3 * t + 2) acc s) :
    ∃ u, Steps vimage s 3 3 u ∧ c.ChainIn s0 (3 * t + 3) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  set r := xbfJ (if t + 1 < 7 then .x16 else .x17) (BitVec.ofNat 64 (lowerImm (t+1))) with hr
  have hst := piece_steps hrun hp s hpc' (by simp [hr, xbfJ])
  have hkeep := xbfJ_keeps (if t + 1 < 7 then .x16 else .x17) (BitVec.ofNat 64 (lowerImm (t+1)))
  have hW : s.getReg (if t + 1 < 7 then .x16 else .x17) = (if t + 1 < 7 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide +kernel)
    · exact kr .x17 c.d1 (by simp [known]) (by decide +kernel)
  have h2 := kr .x9 0x7fc00 (by simp [known]) (by decide +kernel)
  have himm := lowerImm_even (t+1)
  have hk1 := c.kOf_lt (t + 1) (by omega)
  have hrow : (if t + 1 < 7 then c.d0 else c.d1).toNat / 2^54 %512 = c.kOf (t+1) := by
    rw [c.kOf_eq (t+1) (by omega)]; rcases ht with rfl|rfl <;> rfl
  have hm := shE_mask_new s _ _ hW 54 9 (by omega) (le_refl _)
  have e : ((if t+1<7 then c.d0 else c.d1) >>> (44 : Nat)) &&& (0x7fc00 : Word) = BitVec.ofNat 64 (1024*c.kOf (t+1)) := by
    apply BitVec.eq_of_toNat_eq
    have hm' : (((if t+1<7 then c.d0 else c.d1) >>> (44 : Nat)) &&& (0x7fc00 : Word)).toNat =
        1024*((if t+1<7 then c.d0 else c.d1).toNat/2^54%512) := by
      simpa [shE, E.eval, BinOp.eval, hW] using hm
    rw [hm',hrow,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024*c.kOf (t+1)<2^64 by omega)]
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr bufferWr at h ⊢; rcases h with h | h | h
      · exact Or.inl h
      · right; left; obtain ⟨j, h1, h2, h3⟩ := h; exact ⟨j, h1, by omega, h3⟩
      · right; right; exact ⟨h.1, by omega, h.2.2⟩), hS⟩, by omega, h25, ?_⟩⟩
  rw [Result.toState_pc]
  simp only [hr,xbfJ,E.eval,BinOp.eval,hW,h2]
  rw [show ((44:Word).toNat%64)=44 from rfl,e,ofNat_add_ofNat,even_andNot1' _ (by omega)]
  have e2 : BitVec.ofNat 64 (1024*c.kOf (t+1)+(lowerImm (t+1))) = pcOf (entW (t+1) (c.kOf (t+1))) := by
    rw [entW_address _ _ (by omega) hk1]
    rcases ht with rfl|rfl <;> simp <;> congr 1 <;> omega
  rw [e2]
  unfold startPc
  rw [if_neg (by omega),if_pos (by omega),show (3*t+3)/3=t+1 by omega]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
def ChainOut (c : LCtx) (s0 : MachineState) (n : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr n) acc s ∧ acc.length = n - c.i0 ∧ s.pc = pcOf c.ret
theorem next_inline (c : LCtx) (s0 : MachineState) (i : Nat) (hi : i < 42) (h2 : i % 3 ≠ 2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) : c.ChainIn s0 (i + 1) acc s := by
  obtain ⟨hB, hlen, h25, hpc⟩ := hs
  refine ⟨hB, hlen.trans (by omega), h25, ?_⟩
  rw [hpc]
  simp only [endPc, startPc, show i ≠ 42 by omega, show i + 1 ≠ 42 by omega, if_false]
  by_cases h0 : i % 3 = 0
  · rw [if_pos h0, if_neg (show (i + 1) % 3 ≠ 0 by omega), if_pos (show (i + 1) % 3 = 1 by omega)]
    unfold tB; rw [show (i + 1) / 3 = i / 3 by omega]
    simp only [Nat.add_sub_cancel]
    simp only [show (1 < i+1) ↔ (0 < i) by omega]
  · rw [if_neg h0, if_pos (show i % 3 = 1 by omega), if_neg (show (i + 1) % 3 ≠ 0 by omega),
      if_neg (show (i + 1) % 3 ≠ 1 by omega)]
    unfold tC; rw [show (i + 1) / 3 = i / 3 by omega]
theorem x13_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (_hi : c.i0 ≤ 41) (hp : c.tX 41 < 257214) (hrun : vrun (c.tX 41) 4 = some ctabX)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 41 acc s) :
    ∃ u, Steps vimage s 3 3 u ∧ c.ChainIn s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX 41) := by rw [hpc]; unfold endPc; simp
  have hst := piece_steps hrun hp s hpc' (by simp [ctabX])
  have h15 : s.getReg .x9 = BitVec.ofNat 64 0x7fc00 := kr .x9 0x7fc00 (by simp [known]) (by decide +kernel)
  have h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 c.ck := kr .x29 _ (by simp [known]) (by decide +kernel)
  have hck := hc.2.2.2.2.2.2.1
  refine ⟨ctabX.toState s, hst, ⟨⟨fun x hx => (ctabX_keeps.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr bufferWr at h ⊢; rcases h with h | h | h
      · exact Or.inl h
      · right; left; obtain ⟨j, h1, h2, h3⟩ := h; exact ⟨j, h1, by omega, h3⟩
      · right; right; exact ⟨h.1, by omega, h.2.2⟩), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [ctabX, E.eval, BinOp.eval, h15, h29]
    have e2 : BitVec.ofNat 64 0x7fc00 - (7#64 - BitVec.ofNat 64 c.ck) <<< ((12 : Word).toNat % 64) + (1844 : Word) =
        BitVec.ofNat 64 (0x1000 + 4 * ckSlot c.ck) := by
      have hk : c.ck ≤ 8 := hck
      generalize c.ck = k at hk ⊢
      unfold ckSlot
      interval_cases k <;> decide +kernel
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc; simp
theorem endPc_42_lt (c : LCtx) (hc : c.ok) : c.endPc 42 < 257214 := by
  have := hc.2.2.2.2.2.2.1
  unfold endPc ckSlot partLen; simp only [if_true]; split_ifs <;> omega
theorem ckend_out (c : LCtx) (hc : c.ok) {s0 : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 42 acc s) : c.ChainOut s0 43 acc s := by
  obtain ⟨hB, hlen, -, hpc⟩ := hs
  refine ⟨hB, hlen, ?_⟩
  rw [hpc, hc.2.2.2.2.2.2.2.1]
  unfold endPc; simp
end LCtx
end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M.LCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

theorem buffer_skip_base (c : LCtx) (hc : c.ok) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hs : c.bufferSafe i)
    (acc : List Digest) (hlen : acc.length = i-c.i0) (hB : c.Base s0 (c.Wr i) acc s) :
    c.Base s0 (c.Wr (i+1)) (acc ++ [c.bufferVal i]) s := by
  obtain ⟨hR,hF,hA⟩ := hB
  refine ⟨hR, hF.mono (fun A _ h => c.bufferWr_mono i A h), ?_⟩
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  by_cases hl : j < acc.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD]
    exact hA j hl
  · have hj' : j = acc.length := by omega
    subst hj'
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
      show c.i0+acc.length=i by omega]
    exact bufferVal_at hc h0.2 hi hs c.bufferBound_slot hF

theorem buffer_skip_inline (c : LCtx) (hc : c.ok) {s0 s : MachineState} (h0 : c.Orig0 s0)
    (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hSafe : c.bufferSafe i)
    (hpc : c.startPc i = c.endPc i) (acc : List Digest) (hs : c.ChainIn s0 i acc s) :
    c.EndInv s0 i (acc ++ [c.bufferVal i]) s := by
  obtain ⟨hB,hlen,h25,hp⟩ := hs
  refine ⟨c.buffer_skip_base hc s0 s h0 i hi hSafe acc hlen hB, ?_, h25, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · rwa [← hpc]

theorem buffer_skip_jump (c : LCtx) (hc : c.ok) {s0 s : MachineState} (h0 : c.Orig0 s0)
    (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hSafe : c.bufferSafe i)
    (hp : c.startPc i < 257214) (hrun : vrun (c.startPc i) 1 = some (skipJB (c.endPc i)))
    (acc : List Digest) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 1 1 t ∧ c.EndInv s0 i (acc ++ [c.bufferVal i]) t := by
  obtain ⟨hB,hlen,h25,hpc⟩ := hs
  set r := skipJB (c.endPc i)
  have hst := piece_steps hrun hp s hpc (by intro o ho; exact (List.not_mem_nil ho).elim)
  have hmem : ∀ A, (r.toState s).getMem A = s.getMem A := by
    intro A
    rw [Result.toState_getMem]
    rfl
  have hreg : ∀ x, (r.toState s).getReg x = s.getReg x := by
    intro x
    rw [Result.toState_getReg]
    exact RegFile.init_get_eval s x
  have hb := c.buffer_skip_base hc s0 s h0 i hi hSafe acc hlen hB
  refine ⟨r.toState s, hst, ⟨fun x hx => (hreg x).trans (hb.1 x hx), ?_, ?_⟩, ?_, h25, ?_⟩
  · intro A hA hn; rw [hmem]; exact hb.2.1 A hA hn
  · intro j hj; rcases hb.2.2 j hj with ⟨h1,h2⟩; exact ⟨(hmem _).trans h1,(hmem _).trans h2⟩
  · simp only [List.length_append,List.length_singleton]; omega
  · rw [Result.toState_pc]; rfl
end SigGolfCandidate.T3M.LCtx
end
-- ==== merged from W9Machine_WctPackedHeader ====
section

set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem chainPrefix_shift (index coord child : Nat) :
    V3.chainPrefix index coord child = ((index <<< 11) ||| (coord + 1) ||| (child <<< 4)) <<< 16 := by
  have hi : index <<< 27 = (index <<< 11) <<< 16 := by
    simp only [Nat.shiftLeft_eq]; omega
  have hc : child <<< 20 = (child <<< 4) <<< 16 := by
    simp only [Nat.shiftLeft_eq]; omega
  rw [Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib]
  simp only [V3.chainPrefix, hi, hc]
theorem chainPrefix_value (index coord child : Nat) (hk : coord < 9) (hj : child < 128) :
    V3.chainPrefix index coord child = 65536 * (2048 * index + 16 * child + (coord + 1)) := by
  rw [chainPrefix_shift, Nat.or_assoc, Nat.or_comm (coord + 1) (child <<< 4),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega : coord + 1 < 2 ^ 4)]
  have hl : (child <<< 4) + (coord + 1) < 2 ^ 11 := by
    simp only [Nat.shiftLeft_eq]; omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hl]
  simp only [Nat.shiftLeft_eq]
  omega
theorem chainLow_add (index coord child chain digit : Nat) (hc : chain < 6) (hd : digit < 4) :
    V3.chainLow index coord child chain digit =
      V3.chainPrefix index coord child + (128 + 4 * chain + 256 * digit) := by
  have hlo : 128 ||| (chain <<< 2) ||| (digit <<< 8) = 128 + 4 * chain + 256 * digit := by
    interval_cases chain <;> interval_cases digit <;> decide
  unfold V3.chainLow
  rw [hlo, Nat.or_comm, chainPrefix_shift,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega : 128 + 4 * chain + 256 * digit < 2 ^ 16)]
theorem leafLow_eq (index coord child : Nat) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128) :
    V3.leafLow index coord child = 1537 + V3.chainPrefix index coord child := by
  rw [chainPrefix_value _ _ _ hk hj]
  unfold V3.leafLow ClaudeWCT.WCT9.ftsLeafLow
  rw [Nat.mod_eq_of_lt (by omega : coord + 1 < 16), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi]
  omega
theorem packedHeader_eval (s : MachineState) (index coord child chain digit : Nat)
    (hp : s.getReg .x31 = BitVec.ofNat 64 (V3.leafLow index coord child))
    (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (hc : chain < 6) (hd : digit < 4) :
    (packedHeader chain digit).eval s = BitVec.ofNat 64 (V3.chainLow index coord child chain digit) := by
  simp only [packedHeader, addC_eval, E.eval, hp]
  rw [leafLow_eq _ _ _ hi hk hj, chainLow_add _ _ _ _ _ hc hd, chainPrefix_value _ _ _ hk hj]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hc' : 128 + 4 * chain + 256 * digit < 1537 := by omega
  rw [Nat.mod_eq_of_lt (by omega : 128 + 4 * chain + 256 * digit < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 1537 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 1537 + 65536 * (2048 * index + 16 * child + (coord + 1)) < 2 ^ 64)]
  omega
theorem packedPos_eval (s : MachineState) (digit : Nat) (hd : digit < 4)
    (h7 : s.getReg .x7 = 1) (h13 : s.getReg .x13 = 2) (h19 : s.getReg .x19 = 3) :
    (packedPos digit).eval s = BitVec.ofNat 64 digit := by
  interval_cases digit <;> simp [packedPos, E.eval, h7, h13, h19]
theorem wct_header_step (k index child t old digit : Nat) (hk : k < 9)
    (hi : index < 2 ^ 31) (hj : child < 128) (ht : t < 6) (ho : old < 4) (hd : digit < 4) :
    StoreKind.merge .b (BitVec.ofNat 64 (V3.chainLow index k child t old)) 1
      (BitVec.ofNat 64 digit) = BitVec.ofNat 64 (V3.chainLow index k child t digit) := by
  have heq : ∀ d, d < 4 → V3.chainLow index k child t d =
      (128 + 4 * t) + 256 * d + 2 ^ 16 * (2048 * index + 16 * child + (k + 1)) := by
    intro d h
    rw [chainLow_add _ _ _ _ _ ht h, chainPrefix_value _ _ _ hk hj]
    omega
  rw [heq old ho, heq digit hd]
  apply stepByte _ (128 + 4 * t) (2048 * index + 16 * child + (k + 1)) digit
    (by omega) (by omega) (by omega)
  all_goals
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (by omega : 128 + 4 * t + 256 * old + 2 ^ 16 * (2048 * index + 16 * child + (k + 1)) < 2 ^ 64)]
    omega
end W9Machine
end
-- ==== merged from W9Machine_WctImage ====
section

namespace W9Machine.Frozen
open SigGolfCandidate.T3M.Images in
def codeChunks : List (List (BitVec 32)) := SigGolfCandidate.T3M.Verify.vChunks
def dataChunks : List (List (BitVec 8)) := [SigGolfCandidate.T3M.Images.verifyData]
def image : SigGolfCandidate.Legacy.Riscv.Image := ⟨codeChunks.flatten, dataChunks.flatten⟩
def chainEntries : List Nat := [195584, 195648, 195712, 195776, 195840, 195904, 195968, 196032, 196096, 196160, 196224, 196288, 196352, 196416, 196480, 196544, 196608, 196672, 196736, 196800, 196864, 196928, 196992, 197056, 197120, 197184, 197248, 197312, 197376, 197440, 197504, 197568, 197632, 197696, 197760, 197824, 197888, 197952, 198016, 198080, 198144, 198208, 198272, 198336, 198400, 198464, 198528, 198592, 198656, 198720, 198784, 198848, 198912, 198976, 199040, 199104, 199168, 199232, 199296, 199360, 199424, 199488, 199552, 199616, 199680, 199744, 199808, 199872, 199936, 200000, 200064, 200128, 200192, 200256, 200320, 200384, 200448, 200512, 200576, 200640, 200704, 200768, 200832, 200896, 200960, 201024, 201088, 201152, 201216, 201280, 201344, 201408, 201472, 201536, 201600, 201664, 201728, 201792, 201856, 201920, 201984, 202048, 202112, 202176, 202240, 0, 202304, 202368, 202432, 0, 0, 202496, 202560, 202624, 202688, 202752, 202816, 202880, 202944, 203008, 203072, 203136, 203200, 0, 0, 203264, 203328, 0, 203392, 203456, 203520, 203584, 203648, 203712, 203776, 203840, 203904, 203968, 204032, 204096, 204160, 204224, 204288, 204352, 204416, 204480, 204544, 204608, 204672, 204736, 204800, 204864, 204928, 204992, 205056, 205120, 205184, 205248, 205312, 205376, 205440, 205504, 205568, 205632, 205696, 205760, 205824, 205888, 205952, 206016, 206080, 206144, 0, 0, 206208, 206272, 0, 206336, 206400, 206464, 206528, 206592, 206656, 206720, 206784, 206848, 0, 206912, 206976, 207040, 207104, 207168, 207232, 207296, 207360, 207424, 207488, 207552, 207616, 207680, 207744, 207808, 207872, 207936, 208000, 208064, 208128, 208192, 208256, 208320, 208384, 208448, 208512, 208576, 208640, 208704, 208768, 208832, 208896, 208960, 209024, 209088, 209152, 209216, 209280, 209344, 209408, 209472, 209536, 209600, 209664, 209728, 209792, 209856, 209920, 209984, 210048, 210112, 210176, 210240, 210304, 210368, 210432, 210496, 210560, 210624, 210688, 210752, 210816, 210880, 210944, 211008, 211072, 211136, 211200, 211264, 211328, 211392, 211456, 211520, 211584, 211648, 211712, 211776, 211840, 211904, 211968, 212032, 212096, 212160, 212224, 212288, 212352, 212416, 212480, 212544, 212608, 212672, 212736, 212800, 0, 212864, 212928, 212992, 0, 0, 213056, 213120, 213184, 213248, 213312, 213376, 213440, 213504, 213568, 213632, 213696, 213760, 0, 0, 213824, 213888, 0, 213952, 214016, 214080, 214144, 214208, 214272, 214336, 214400, 214464, 214528, 214592, 214656, 214720, 214784, 214848, 214912, 214976, 215040, 215104, 215168, 215232, 215296, 215360, 215424, 215488, 0, 0, 0, 215552, 215616, 0, 0, 0, 0, 0, 0, 215680, 215744, 215808, 0, 0, 0, 215872, 0, 0, 0, 215936, 0, 0, 0, 216000, 0, 216064, 216128, 0, 0, 216192, 0, 0, 0, 0, 0, 216256, 216320, 216384, 216448, 0, 0, 216512, 216576, 216640, 216704, 216768, 216832, 216896, 216960, 217024, 0, 0, 0, 217088, 0, 0, 0, 217152, 217216, 217280, 217344, 0, 0, 0, 0, 0, 0, 0, 0, 217408, 217472, 0, 0, 0, 0, 217536, 217600, 0, 217664, 217728, 217792, 217856, 217920, 217984, 0, 218048, 218112, 218176, 218240, 218304, 218368, 0, 218432, 0, 0, 218496, 218560, 0, 218624, 218688, 218752, 218816, 218880, 218944, 219008, 219072, 219136, 219200, 219264, 219328, 219392, 219456, 219520, 219584, 219648, 219712, 219776, 219840, 219904, 219968, 220032, 220096, 220160, 220224, 220288, 220352, 220416, 220480, 220544, 220608, 220672, 220736, 220800, 220864, 0, 0, 220928, 220992, 0, 221056, 221120, 221184, 221248, 221312, 221376, 221440, 221504, 221568, 0, 221632, 221696, 221760, 221824, 221888, 221952, 222016, 222080, 222144, 222208, 222272, 222336, 222400, 222464, 222528, 222592, 222656, 222720, 0, 0, 0, 222784, 0, 0, 0, 222848, 0, 222912, 222976, 0, 0, 223040, 0, 0, 0, 0, 0, 223104, 223168, 0, 0, 0, 0, 223232, 223296, 223360, 223424, 223488, 223552, 223616, 223680, 223744, 0, 0, 223808, 223872, 0, 223936, 224000, 0, 0, 0, 0, 224064, 224128, 0, 224192, 224256, 224320, 224384, 224448, 224512, 224576, 224640, 224704, 224768, 224832, 224896, 224960, 225024, 225088, 225152, 225216, 225280, 225344, 225408, 225472, 225536, 225600, 225664, 225728, 225792, 225856, 225920, 225984, 226048, 226112, 226176, 226240, 226304, 226368, 226432, 226496, 226560, 226624, 226688, 226752, 226816, 226880, 226944, 227008, 227072, 227136, 227200, 227264, 227328, 227392, 227456, 227520, 227584, 227648, 0, 227712, 227776, 227840, 0, 227904, 227968, 0, 228032, 0, 228096, 228160, 228224, 228288, 228352, 228416, 228480, 228544, 228608, 228672, 228736, 228800, 228864, 0, 228928, 228992, 229056, 229120, 229184, 229248, 229312, 229376, 229440, 229504, 229568, 229632, 229696, 229760, 229824, 229888, 229952, 230016, 230080, 230144, 230208, 230272, 230336, 230400, 230464, 230528, 230592, 230656, 230720, 230784, 230848, 230912, 230976, 231040, 231104, 231168, 231232, 231296, 231360, 231424, 231488, 231552]
def layout : W9Machine.Layout := ⟨image, fun r => chainEntries.getD r.val 0, fun j => 246464 + 64*j.val, fun k => [97, 183, 268, 352, 438, 522, 606, 691, 775].getD k.val 0, 0⟩
end W9Machine.Frozen

namespace W9Machine.SharedLayout
/-- The chain proof uses raw child labels. B tables permute their physical
authentication paths internally while retaining raw labels in leaf headers. -/
def childWord (coordinate child : Nat) : Nat :=
  if coordinate < 8 ∧ coordinate % 2 = 0 then 231616 + 32 * child
  else if coordinate = 8 then 235776 + 64 * child
  else 246464 + 64 * child
/-- `start k + length k` of the shared dispatcher (`W9Drv.SharedDispatch`); coordinate 8's dispatcher is 9 words
(765..773) after the dispatch hoist, so its children receive `ra = pcOf 774` and return with `320(ra)`. -/
def returnWord (k : Fin 9) : Nat := [97,183,267,351,437,521,605,691,774].getD k.val 0
def layout (coordinate : Fin 9) : W9Machine.Layout :=
  ⟨Frozen.image, Frozen.layout.chainWord, fun j => childWord coordinate.val j.val, returnWord, 0⟩
theorem image_eq (k : Fin 9) : (layout k).image = Frozen.image := rfl
theorem chain_eq (k : Fin 9) (r : Fin 666) :
    (layout k).chainWord r = Frozen.layout.chainWord r := rfl
end W9Machine.SharedLayout

namespace W9Machine
/-- Verify layouts run the FTS banks unshifted. -/
theorem Frozen.base_eq (k : Fin 9) : Chain.base Frozen.layout k = coordinateBase k := rfl
theorem SharedLayout.base_eq (k k' : Fin 9) : Chain.base (SharedLayout.layout k) k' = coordinateBase k' := rfl
end W9Machine
end
-- ==== merged from W9Machine_WctChainPieces ====
section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def leafSetupRel : Result :=
  ⟨⟨(RegFile.init.set .x10 (addC (.reg .x8) 640)).set .x11 (.c 128),
    [(kAt .x8 640 24, .c 0),
      (kAt .x8 640 16, .reg .x31)],
    [.valid (kAt .x8 640 24) 8, .valid (kAt .x8 640 16) 8]⟩,
    .bin .and (.bin .add (.reg .x23) (.c 4)) (.c (~~~1#64)), .jump, 5, 5⟩
inductive ChainPieceKind where
  | head (off dst chain digit : Nat)
  | rung (digit : Nat) (dst : Option Nat)
  | copy (off dst : Nat)
  | jump (target : Nat)
  | leaf
  deriving BEq, DecidableEq, Repr
structure ChainPiece where
  pc : Nat
  words : List (BitVec 32)
  kind : ChainPieceKind
  deriving Repr
def ChainPiece.result (p : ChainPiece) : Result :=
  match p.kind with
  | .head off dst chain digit =>
      headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p.pc chain digit
  | .rung digit dst => rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) p.pc
  | .copy off dst => copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p.pc
  | .jump target => ⟨SymState.init, .c (pcOf target), .jump, 1, 1⟩
  | .leaf => leafSetupRel
def ChainPiece.checked (p : ChainPiece) : Bool :=
  rOK (symRun {} p.words (pcOf p.pc) p.words.length) p.result
end W9Machine
end
-- ==== merged from W9Machine_WctRoutineModel ====
section

section


namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
def chainEntries : List Nat := Frozen.chainEntries
end W9Machine
end

section



namespace W9Machine
open SigGolfCandidate.T3M
/-- Witness stack: FTS chain `t`'s block offset from `s0` (F 592, G 504, F 528, G 400, F 424, F 320). -/
def ftsOff (t : Nat) : Nat := ClaudeWCT.W9.T3M.wctChainOff t
/-- Where an interior step (and an in-place terminal step) leaves its output: F `off + 48` (the value slot),
G `off - 16` (the high half lands on the value at `off`). -/
def ftsOut (t : Nat) : Nat := if ClaudeWCT.WCT9.ftsIsG t then ftsOff t - 16 else ftsOff t + 48
/-- `.copy off dst` copies `off + 48`, `off + 56` (the 16 bytes at `ftsOut t`) to the leaf slot. -/
def expectedChainKinds (digits : List Nat) (t : Nat) : List ChainPieceKind :=
  let d := digits.getD t 0
  if d = 0 then [] else
    let off := ftsOff t
    let out := ftsOut t
    let slot := if t = 0 then 640 else 672 + 16 * t
    let own := 0 < t ∧ t < 5 ∧ digits.getD (t + 1) 0 = 0
    let dst := if own then out else slot
    [.head off (if d = 1 then dst else out) t (4 - d)] ++
      ((List.range' (5 - d) (d - 1)).map fun step ↦
        .rung step (if step = 3 ∧ dst ≠ out then some dst else none)) ++
      (if own then [.copy (out - 48) slot] else [])
def expectedKinds (digits : List Nat) : List ChainPieceKind :=
  (List.range 6).flatMap (expectedChainKinds digits) ++ [.leaf]
def ChainPiece.isHash (p : ChainPiece) : Bool :=
  match p.kind with
  | .head .. | .rung .. => true
  | _ => false
def ChainPiece.totalCycles (p : ChainPiece) : Nat :=
  p.result.cycles + if p.isHash then 8 else 0
def ChainPiece.nextPc (p : ChainPiece) : Nat :=
  match p.kind with
  | .jump target => target
  | _ => p.pc + p.words.length
structure ChainRoutine where
  rank : Nat
  digits : List Nat
  pieces : List ChainPiece
def ChainRoutine.cycles (r : ChainRoutine) : Nat := (r.pieces.map ChainPiece.totalCycles).sum
def ChainRoutine.fuel (r : ChainRoutine) : Nat := (r.pieces.map fun p ↦ p.words.length).sum
def ChainRoutine.checked (r : ChainRoutine) : Bool :=
  decide (r.rank < 666) &&
  (r.digits == (ClaudeWCT.WCT9.compositions 5 6 7).getD r.rank []) &&
  (r.pieces.head?.map ChainPiece.pc == some (chainEntries.getD r.rank 0)) &&
  (r.pieces.filterMap (fun p ↦ match p.kind with | .jump _ => none | k => some k)
    == expectedKinds r.digits) &&
  ((r.pieces.zip r.pieces.tail).all fun pq ↦ pq.2.pc == pq.1.nextPc) &&
  ((r.pieces.filter ChainPiece.isHash).length == 7) &&
  decide (r.cycles ≤ 89) && decide (r.fuel ≤ 40)
end W9Machine
end
end
-- ==== merged from W9Machine_WctChainTrace ====
section

namespace W9Machine
inductive ChainWord where
  | original (offset : Nat)
  | header (chain step : Nat)
  | zero
  | answer (query word : Nat)
  | leafHeader
  deriving BEq, DecidableEq, Repr
structure ChainTrace where
  mem : List (Nat × ChainWord) := []
  input : Nat := 0
  output : Nat := 0
  chain : Nat := 0
  queries : List (List ChainWord) := []
  valid : Bool := true
  deriving Repr
def ChainTrace.read (s : ChainTrace) (off : Nat) : ChainWord :=
  ((s.mem.find? fun p => p.1 == off).map Prod.snd).getD (.original off)
def ChainTrace.put (s : ChainTrace) (off : Nat) (v : ChainWord) : ChainTrace :=
  { s with mem := (off, v) :: s.mem }
def ChainTrace.hash (s : ChainTrace) : ChainTrace :=
  let q := s.queries.length
  let input := (List.range 8).map fun i => s.read (s.input + 8 * i)
  let s := { s with queries := s.queries ++ [input] }
  (List.range 4).foldl (fun s i => s.put (s.output + 8 * i) (.answer q i)) s
def ChainTrace.step (s : ChainTrace) : ChainPieceKind → ChainTrace
  | .head off dst chain digit =>
      let s := s.put (off + 16) (.header chain digit)
      ({ s with input := off, output := dst, chain := chain }).hash
  | .rung digit dst =>
      let headerOk := match s.read (s.input + 16) with
        | .header chain _ => chain == s.chain
        | _ => false
      let s := s.put (s.input + 16) (.header s.chain digit)
      ({ s with output := dst.getD s.output, valid := s.valid && headerOk }).hash
  | .copy off dst =>
      let lo := s.read (off + 48)
      let hi := s.read (off + 56)
      (s.put dst lo).put (dst + 8) hi
  | .jump _ => s
  | .leaf => ((s.put 656 .leafHeader).put 664 .zero)
def chainTrace (r : ChainRoutine) : ChainTrace :=
  r.pieces.foldl (fun s p => s.step p.kind) {}
def traceLeafSlot (t : Nat) : Nat := if t = 0 then 640 else 672 + 16 * t
/-- Witness stack: G chains (1, 3) hash `value | header | pad0 | pad1` and their interior steps keep the high half
(answer words 2, 3); F chains hash `pad0 | header | pad1 | value` and keep the low half. -/
def chainQueryWords (digits : List Nat) (t j : Nat) : List ChainWord :=
  let off := ftsOff t
  let q := (digits.take t).sum + j
  let hdr := ChainWord.header t (4 - digits.getD t 0 + j)
  if ClaudeWCT.WCT9.ftsIsG t then
    [if j = 0 then .original off else .answer (q - 1) 2,
      if j = 0 then .original (off + 8) else .answer (q - 1) 3,
      hdr, .original (off + 24), .original (off + 32), .original (off + 40),
      .original (off + 48), .original (off + 56)]
  else
    [.original off, .original (off + 8), hdr, .original (off + 24),
      .original (off + 32), .original (off + 40),
      if j = 0 then .original (off + 48) else .answer (q - 1) 0,
      if j = 0 then .original (off + 56) else .answer (q - 1) 1]
def expectedQueries (digits : List Nat) : List (List ChainWord) :=
  (List.range 6).flatMap fun t => (List.range (digits.getD t 0)).map (chainQueryWords digits t)
def expectedEndpoint (digits : List Nat) (t word : Nat) : ChainWord :=
  if digits.getD t 0 = 0 then .original (traceLeafSlot t + 8 * word)
  else .answer ((digits.take (t + 1)).sum - 1) word
def ChainRoutine.traceChecked (r : ChainRoutine) : Bool :=
  let s := chainTrace r
  s.valid && (s.queries == expectedQueries r.digits) &&
    ((List.range 6).all fun t => (List.range 2).all fun word =>
      s.read (traceLeafSlot t + 8 * word) == expectedEndpoint r.digits t word) &&
    (s.read 656 == .leafHeader) && (s.read 664 == .zero) &&
    (s.mem.all fun p => decide (p.1 % 8 = 0 ∧ p.1 + 8 ≤ 784))
end W9Machine
end
-- ==== merged from W9Machine_WctRelativeMem ====
section

section
set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem headRHRel_keeps (rb : Reg) (off dst : Word) (p chain digit : Nat) :
    Keeps (headRHRel rb off dst p chain digit) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRHRel]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem rungRRel_keeps (rb : Reg) (digit : Nat) (dst : Option Word) (p : Nat) :
    Keeps (rungRRel rb digit dst p) [.x12] := by
  intro x hx; cases dst <;> first | rfl | exact RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))
theorem copyFHRel_keeps (rb : Reg) (off dst : Word) (p : Nat) :
    Keeps (copyFHRel rb off dst p) [.x3, .x14] := by
  intro x hx
  simp only [copyFHRel, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headRHRel_addresses (rb : Reg) (off dst : Word) (p chain digit : Nat)
    (s : MachineState) :
    ((headRHRel rb off dst p chain digit).toState s).getReg .x10 = s.getReg rb + off ∧
    ((headRHRel rb off dst p chain digit).toState s).getReg .x12 = s.getReg rb + dst := by
  simp [headRHRel, Result.toState_getReg, RegFile.get, RegFile.set, addC_eval, E.eval]
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest pad64)
theorem hashInput_blk4 (t : MachineState) (A : Nat) (a b c d : Digest)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (hA : A % 8 = 0)
    (hA' : A + 64 < 2 ^ 64) (ha : DigAt t A a) (hb : DigAt t (A + 16) b) (hc : DigAt t (A + 32) c)
    (hd : DigAt t (A + 48) d) : hashInput t = toQ (pad64 (blk4 a b c d)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA hA' h11
  rw [wordsOf_blk4, ha.1, ha.2, hb.1, hc.1, hd.1, show A + 24 = A + 16 + 8 by omega, hb.2,
    show A + 40 = A + 32 + 8 by omega, hc.2, show A + 56 = A + 48 + 8 by omega, hd.2]
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest pad64)
theorem relative_key (s : MachineState) (rb : Reg) (B off n : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) :
    (kAt rb (BitVec.ofNat 64 off) n).eval s = BitVec.ofNat 64 (B + off + n) := by
  simp only [kAt, Addr.eval, E.eval, hbase, ofNat_add_ofNat, Nat.add_assoc]
theorem headRHRel_mem (s : MachineState) (rb : Reg) (B off dst p chain digit A : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + off + 64 < 2 ^ 64)
    (hA : A < 2 ^ 64) :
    ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s).getMem
      (BitVec.ofNat 64 A) =
      if A = B + off + 16 then (packedHeader chain digit).eval s else s.getMem (BitVec.ofNat 64 A) := by
  exact memEval_one s _ _ (B + off + 16) A
    (relative_key s rb B off 16 hbase) (by omega) hA
theorem headRHRel_frame (s : MachineState) (rb : Reg) (B off dst p chain digit : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + off + 64 < 2 ^ 64) :
    Frame s ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s)
      (fun A => A = B + off + 16) := by
  intro A hA hn
  rw [headRHRel_mem s rb B off dst p chain digit A hbase hhi hA,
    if_neg hn]
theorem headRHRel_hashInput (s : MachineState) (rb : Reg) (B off dst p chain digit : Nat)
    (pad0 hdr pad1 value : Digest) (hbase : s.getReg rb = BitVec.ofNat 64 B)
    (halign : (B + off) % 8 = 0) (hhi : B + off + 64 < 2 ^ 64)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 64)
    (hlo : (packedHeader chain digit).eval s = hdr.extractLsb' 0 64)
    (hhigh : s.getMem (BitVec.ofNat 64 (B + off + 24)) = hdr.extractLsb' 64 64)
    (hp0 : DigAt s (B + off) pad0) (hp1 : DigAt s (B + off + 32) pad1)
    (hv : DigAt s (B + off + 48) value) :
    SigGolfCandidate.Legacy.Riscv.hashInput
      ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s) =
      toQ (pad64 (blk4 pad0 hdr pad1 value)) := by
  have hf := headRHRel_frame s rb B off dst p chain digit hbase hhi
  refine W9Machine.hashInput_blk4 _ (B + off) pad0 hdr pad1 value
    ?_ ?_ halign hhi (hp0.frame hf (by omega) (by omega) (by omega)) ?_
    (hp1.frame hf (by omega) (by omega) (by omega))
    (hv.frame hf (by omega) (by omega) (by omega))
  · simpa only [hbase, ofNat_add_ofNat] using
      (headRHRel_addresses rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit s).1
  · exact ((headRHRel_keeps rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
      p chain digit).reg s (by decide)).trans h11
  · constructor
    · rw [headRHRel_mem s rb B off dst p chain digit (B + off + 16) hbase hhi (by omega),
        if_pos rfl]
      exact hlo
    · rw [headRHRel_mem s rb B off dst p chain digit (B + off + 16 + 8) hbase hhi (by omega),
        if_neg (by omega)]
      simpa only [Nat.add_assoc] using hhigh
end W9Machine
end
end
-- ==== merged from W9Machine_WctTraceMem ====
section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def TraceMem (value : ChainWord → Word) (B : Nat) (tr : ChainTrace) (s : MachineState) : Prop :=
  ∀ off, off < 784 → s.getMem (BitVec.ofNat 64 (B + off)) = value (tr.read off)
theorem ChainTrace.read_put (tr : ChainTrace) (off x : Nat) (v : ChainWord) :
    (tr.put off v).read x = if x = off then v else tr.read x := by
  by_cases h : x = off
  · subst x; simp [ChainTrace.read, ChainTrace.put]
  · simp [ChainTrace.read, ChainTrace.put, h, show off ≠ x from Ne.symm h]
theorem head_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B off dst p chain digit : Nat) (ht : TraceMem value B tr s)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hB : B + 784 < 2 ^ 64)
    (hoff : off + 64 ≤ 784)
    (hh : (packedHeader chain digit).eval s = value (.header chain digit)) :
    TraceMem value B (tr.put (off + 16) (.header chain digit))
      ((headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s) := by
  intro x hx
  rw [headRHRel_mem s .x8 B off dst p chain digit (B + x) hbase (by omega) (by omega)]
  simp only [ChainTrace.read_put]
  split_ifs <;> first | exact hh | exact ht x hx | omega
end W9Machine
end
-- ==== merged from W9Machine_WctTraceInvariant ====
section

section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest pad64)
theorem rungRRel_mem (s : MachineState) (rb : Reg) (digit p A X : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hhi : A + 64 < 2 ^ 64)
    (hX : X < 2 ^ 64) (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit) :
    ((rungRRel rb digit dst p).toState s).getMem (BitVec.ofNat 64 X) =
      if X = A + 16 then StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (A + 16))) 1
        (BitVec.ofNat 64 digit) else s.getMem (BitVec.ofNat 64 X) := by
  have hk : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (A + 16) := by
    simp only [Addr.eval, E.eval, h10]
    exact ofNat_add_ofNat A 16
  have hm := memEval_one s ⟨some (.reg .x10), 16⟩
    (.bin (.st .b 1) (.ld (addC (.reg .x10) 16)) (packedPos digit)) (A + 16) X
    hk (by omega) hX
  have ha : BitVec.ofNat 64 A + (16 : Word) = BitVec.ofNat 64 (A + 16) :=
    ofNat_add_ofNat A 16
  simpa only [Result.toState_getMem, rungRRel, E.eval, BinOp.eval, addC_eval, h10,
    hstep, ha] using hm
theorem rungRRel_frame (s : MachineState) (rb : Reg) (digit p A : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hhi : A + 64 < 2 ^ 64)
    (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit) :
    Frame s ((rungRRel rb digit dst p).toState s) (fun X => X = A + 16) := by
  intro X hX hn
  rw [rungRRel_mem s rb digit p A X dst h10 hhi hX hstep, if_neg hn]
theorem rungRRel_hashInput (s : MachineState) (rb : Reg) (digit p A : Nat) (dst : Option Word)
    (pad0 hdr pad1 value : Digest) (h10 : s.getReg .x10 = BitVec.ofNat 64 A)
    (halign : A % 8 = 0) (hhi : A + 64 < 2 ^ 64)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 64)
    (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit)
    (hlo : StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (A + 16))) 1
      (BitVec.ofNat 64 digit) = hdr.extractLsb' 0 64)
    (hhigh : s.getMem (BitVec.ofNat 64 (A + 24)) = hdr.extractLsb' 64 64)
    (hp0 : DigAt s A pad0) (hp1 : DigAt s (A + 32) pad1) (hv : DigAt s (A + 48) value) :
    SigGolfCandidate.Legacy.Riscv.hashInput ((rungRRel rb digit dst p).toState s) =
      toQ (pad64 (blk4 pad0 hdr pad1 value)) := by
  have hf := rungRRel_frame s rb digit p A dst h10 hhi hstep
  refine W9Machine.hashInput_blk4 _ A pad0 hdr pad1 value
    (((rungRRel_keeps rb digit dst p).reg s (by decide)).trans h10)
    (((rungRRel_keeps rb digit dst p).reg s (by decide)).trans h11)
    halign hhi (hp0.frame hf (by omega) (by omega) (by omega)) ?_
    (hp1.frame hf (by omega) (by omega) (by omega))
    (hv.frame hf (by omega) (by omega) (by omega))
  constructor
  · rw [rungRRel_mem s rb digit p A (A + 16) dst h10 hhi (by omega) hstep, if_pos rfl]
    exact hlo
  · rw [rungRRel_mem s rb digit p A (A + 16 + 8) dst h10 hhi (by omega) hstep, if_neg (by omega)]
    simpa only [Nat.add_assoc] using hhigh
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest)
theorem copyFHRel_mem (s : MachineState) (rb : Reg) (B off dst p A : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) :
    ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s).getMem
      (BitVec.ofNat 64 A) =
      if A = B + dst + 8 then s.getMem (BitVec.ofNat 64 (B + off + 56)) else
      if A = B + dst then s.getMem (BitVec.ofNat 64 (B + off + 48)) else
      s.getMem (BitVec.ofNat 64 A) := by
  have hm := memEval_two s (kAt rb (BitVec.ofNat 64 dst) 8)
    (kAt rb (BitVec.ofNat 64 dst) 0) (lAt rb (BitVec.ofNat 64 off) 56)
    (lAt rb (BitVec.ofNat 64 off) 48) (B + dst + 8) (B + dst + 0) A
    (relative_key s rb B dst 8 hbase) (relative_key s rb B dst 0 hbase)
    (by omega) (by omega) hA
  simpa only [Result.toState_getMem, copyFHRel, lAt, E.eval, addC_eval, hbase,
    ofNat_add_ofNat, Nat.add_zero, Nat.add_assoc] using hm
theorem copyFHRel_frame (s : MachineState) (rb : Reg) (B off dst p : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64) :
    Frame s ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s)
      (fun A => A = B + dst ∨ A = B + dst + 8) := by
  intro A hA hn
  rw [copyFHRel_mem s rb B off dst p A hbase hhi hA,
    if_neg (fun h => hn (Or.inr h)), if_neg (fun h => hn (Or.inl h))]
theorem copyFHRel_digest (s : MachineState) (rb : Reg) (B off dst p : Nat) (value : Digest)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64)
    (hv : DigAt s (B + off + 48) value) :
    DigAt ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s)
      (B + dst) value := by
  constructor
  · rw [copyFHRel_mem s rb B off dst p (B + dst) hbase hhi (by omega),
      if_neg (by omega), if_pos rfl]
    exact hv.1
  · rw [copyFHRel_mem s rb B off dst p (B + dst + 8) hbase hhi (by omega), if_pos rfl]
    simpa only [Nat.add_assoc] using hv.2
end W9Machine
end
section
namespace W9Machine
theorem ChainTrace.read_hash (tr : ChainTrace) (x : Nat) :
    tr.hash.read x =
      if x = tr.output + 24 then .answer tr.queries.length 3 else
      if x = tr.output + 16 then .answer tr.queries.length 2 else
      if x = tr.output + 8 then .answer tr.queries.length 1 else
      if x = tr.output then .answer tr.queries.length 0 else tr.read x := by
  change ((((tr.put tr.output (.answer tr.queries.length 0)).put (tr.output + 8)
    (.answer tr.queries.length 1)).put (tr.output + 16) (.answer tr.queries.length 2)).put
    (tr.output + 24) (.answer tr.queries.length 3)).read x = _
  simp only [ChainTrace.read_put]
end W9Machine
end
section
namespace W9Machine
set_option maxRecDepth 10000
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.Legacy.Riscv
theorem copy_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B off dst p : Nat) (ht : TraceMem value B tr s)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hB : B + 784 < 2 ^ 64)
    (hoff : off + 64 ≤ 784) (hdst : dst + 16 ≤ 784) :
    TraceMem value B ((tr.put dst (tr.read (off + 48))).put (dst + 8) (tr.read (off + 56)))
      ((copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s) := by
  intro x hx
  rw [copyFHRel_mem s .x8 B off dst p (B + x) hbase (by omega) (by omega)]
  simp only [ChainTrace.read_put]
  split_ifs <;> first
  | simpa only [Nat.add_assoc] using ht (off + 56) (by omega)
  | simpa only [Nat.add_assoc] using ht (off + 48) (by omega)
  | exact ht x hx
  | omega
theorem rung_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B digit p : Nat) (dst : Option Word) (ht : TraceMem value B tr s)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + tr.input)) (hB : B + 784 < 2 ^ 64)
    (hi : tr.input + 64 ≤ 784) (hstep : (packedPos digit).eval s = BitVec.ofNat 64 digit)
    (hh : StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (B + tr.input + 16))) 1
      (BitVec.ofNat 64 digit) = value (.header tr.chain digit)) :
    TraceMem value B (tr.put (tr.input + 16) (.header tr.chain digit))
      ((rungRRel .x8 digit dst p).toState s) := by
  intro x hx
  rw [rungRRel_mem s .x8 digit p (B + tr.input) (B + x) dst h10 (by omega) (by omega) hstep]
  simp only [ChainTrace.read_put]
  split_ifs <;> first | exact hh | exact ht x hx | omega
theorem hash_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState)
    (B : Nat) (ans : BitVec 256) (ht : TraceMem value B tr s)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + tr.output)) (hB : B + 784 < 2 ^ 64)
    (ho : tr.output + 32 ≤ 784)
    (ha : ∀ i, i < 4 → value (.answer tr.queries.length i) = ans.extractLsb' (64 * i) 64) :
    TraceMem value B tr.hash (writeHash s ans) := by
  intro x hx
  rw [writeHash_getMem_ofNat s ans (B + tr.output) (B + x) h12 (by omega) (by omega)]
  rw [ChainTrace.read_hash]
  split_ifs <;> first
  | exact (ha 3 (by decide)).symm
  | exact (ha 2 (by decide)).symm
  | exact (ha 1 (by decide)).symm
  | exact (ha 0 (by decide)).symm
  | exact ht x hx
  | omega
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.Legacy.Riscv
def ChainWord.available (n : Nat) : ChainWord → Prop
  | .answer q _ => q < n
  | _ => True
def ChainTrace.Available (tr : ChainTrace) : Prop :=
  ∀ off, (tr.read off).available tr.queries.length
def chainValue (base : ChainWord → Word) (answers : List (BitVec 256)) : ChainWord → Word
  | .answer q i => (answers.getD q 0).extractLsb' (64 * i) 64
  | w => base w
theorem ChainWord.available_mono (w : ChainWord) (n m : Nat) (h : w.available n) (hn : n ≤ m) :
    w.available m := by
  cases w <;> simp_all [available]; omega
theorem ChainTrace.available_put (tr : ChainTrace) (off : Nat) (w : ChainWord)
    (h : tr.Available) (hw : w.available tr.queries.length) : (tr.put off w).Available := by
  intro x
  change ((tr.put off w).read x).available tr.queries.length
  rw [read_put]
  split_ifs
  · exact hw
  · exact h x
theorem ChainTrace.available_hash (tr : ChainTrace) (h : tr.Available) : tr.hash.Available := by
  intro x
  have hl : tr.hash.queries.length = tr.queries.length + 1 := by
    change (tr.queries ++ [_]).length = _
    simp only [List.length_append, List.length_singleton]
  rw [hl, read_hash]
  split_ifs
  all_goals first
    | exact Nat.lt_succ_self _
    | exact ChainWord.available_mono _ _ _ (h x) (by omega)
theorem chainValue_append (base : ChainWord → Word) (answers : List (BitVec 256))
    (ans : BitVec 256) (w : ChainWord) (h : w.available answers.length) :
    chainValue base (answers ++ [ans]) w = chainValue base answers w := by
  cases w with
  | answer q i =>
    simp only [ChainWord.available] at h
    simp only [chainValue, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  | original off => rfl
  | header t d => rfl
  | zero => rfl
  | leafHeader => rfl
theorem traceMem_append (base : ChainWord → Word) (answers : List (BitVec 256))
    (ans : BitVec 256) (tr : ChainTrace) (s : MachineState) (B : Nat)
    (ht : TraceMem (chainValue base answers) B tr s) (ha : tr.Available)
    (hn : tr.queries.length = answers.length) :
    TraceMem (chainValue base (answers ++ [ans])) B tr s := by
  intro off ho
  rw [chainValue_append base answers ans (tr.read off) (hn ▸ ha off)]
  exact ht off ho
theorem hash_trace_append (base : ChainWord → Word) (answers : List (BitVec 256))
    (ans : BitVec 256) (tr : ChainTrace) (s : MachineState) (B : Nat)
    (ht : TraceMem (chainValue base answers) B tr s) (ha : tr.Available)
    (hn : tr.queries.length = answers.length)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (B + tr.output))
    (hB : B + 784 < 2 ^ 64) (ho : tr.output + 32 ≤ 784) :
    TraceMem (chainValue base (answers ++ [ans])) B tr.hash (writeHash s ans) := by
  apply hash_trace_mem _ tr s B ans (traceMem_append base answers ans tr s B ht ha hn) h12 hB ho
  intro i hi
  simp [chainValue, hn, List.getD_eq_getElem?_getD]
end W9Machine
end
section
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.Legacy.Riscv
theorem ChainTrace.available_step (tr : ChainTrace) (kind : ChainPieceKind) (h : tr.Available) :
    (tr.step kind).Available := by
  cases kind with
  | head off dst chain digit =>
    apply ChainTrace.available_hash
    exact tr.available_put (off + 16) (.header chain digit) h trivial
  | rung digit dst =>
    apply ChainTrace.available_hash
    exact tr.available_put (tr.input + 16) (.header tr.chain digit) h trivial
  | copy off dst =>
    exact ChainTrace.available_put _ _ _
      (tr.available_put dst (tr.read (off + 48)) h (h _)) (h _)
  | jump target => exact h
  | leaf => exact ChainTrace.available_put _ _ _ (tr.available_put 656 .leafHeader h trivial) trivial
theorem chainTrace_available (r : ChainRoutine) : (chainTrace r).Available := by
  have hfold : ∀ (ps : List ChainPiece) (tr : ChainTrace), tr.Available →
      (ps.foldl (fun s p => s.step p.kind) tr).Available := by
    intro ps
    induction ps with
    | nil => intro tr h; exact h
    | cons p ps ih => intro tr h; exact ih _ (tr.available_step p.kind h)
  exact hfold r.pieces {} (fun _ => trivial)
theorem TraceMem.hashInput (value : ChainWord → Word) (B : Nat) (tr : ChainTrace)
    (s : MachineState) (input : List UInt8) (ht : TraceMem value B tr s)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + tr.input))
    (h11 : s.getReg .x11 = 64) (hB : B + 784 < 2 ^ 64)
    (hi : tr.input + 64 ≤ 784) (halign : (B + tr.input) % 8 = 0)
    (hlen : input.length = 64)
    (hwords : wordsOf input = ((List.range 8).map fun i => value (tr.read (tr.input + 8 * i)))) :
    SigGolfCandidate.Legacy.Riscv.hashInput s = toQ input := by
  apply hashInput_words8 s input (B + tr.input) hlen h10 halign (by omega) h11
  rw [hwords]
  simp only [List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, Nat.reduceMul,
    Nat.mul_zero, Nat.add_zero]
  have hread : ∀ x, x < 64 → s.getMem (BitVec.ofNat 64 (B + tr.input + x)) =
      value (tr.read (tr.input + x)) := by
    intro x hx
    simpa only [Nat.add_assoc] using ht (tr.input + x) (by omega)
  rw [ht tr.input (by omega), hread 8 (by decide), hread 16 (by decide), hread 24 (by decide),
    hread 32 (by decide), hread 40 (by decide), hread 48 (by decide), hread 56 (by decide)]
end W9Machine
end
end
-- ==== merged from W9Machine_WctChainInvDefs ====
section

set_option autoImplicit false
namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def originalValue (L : Layout) (u : MachineState) (index : Nat) (k : Fin 9) (j : Fin 128) : ChainWord → Word
  | .original off => u.getMem (BitVec.ofNat 64 (base L k + off))
  | .header t d => BitVec.ofNat 64 (V3.chainLow index k.val j.val t d)
  | .zero => 0
  | .leafHeader => BitVec.ofNat 64 (V3.leafLow index k.val j.val)
  | .answer _ _ => 0
structure Inv (L : Layout) (u : MachineState) (index : Nat) (k : Fin 9) (j : Fin 128)
    (tr : ChainTrace) (answers : List (BitVec 256)) (s : MachineState) : Prop where
  keep : ∀ r, r ∉ clobbers → s.getReg r = u.getReg r
  frame : Frame u s (writes L k)
  memory : TraceMem (chainValue (originalValue L u index k j) answers) (base L k) tr s
  count : tr.queries.length = answers.length
  available : tr.Available
  hashLen : s.getReg .x11 = 64
  pointers : 0 < answers.length →
    s.getReg .x10 = BitVec.ofNat 64 (base L k + tr.input) ∧
    s.getReg .x12 = BitVec.ofNat 64 (base L k + tr.output)
end W9Machine.Chain
end
-- ==== merged from W9Machine_WctWitnessBridge ====
section

set_option autoImplicit false
namespace W9Machine.Chain
open SigGolfCandidate.Legacy.Riscv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem Pre.origW {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 666} {u : MachineState} (h : Pre L w index k j rank u)
    (off : Nat) (ho : off < 848) (ha : off % 8 = 0) : OrigWD L.shift w u (base L k + off) := by
  have he : base L k + off + L.shift - 0x1020 = V3.regionOffset k.val + off := by
    simp only [base, coordinateBase, Layout.shift, V3.regionOffset]
    omega
  simpa only [OrigWD, he] using h.witness off ho ha
theorem inv_initial (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 666) (u : MachineState) (hu : Pre L w index k j rank u) :
    Inv L u index k j {} [] u := by
  refine ⟨fun _ _ => rfl, Frame.refl _ _, ?_, rfl, fun _ => trivial, hu.hashLen, ?_⟩
  · intro off ho; rfl
  · intro h; simp at h
end W9Machine.Chain
end
-- ==== merged from W9Machine_WctPlanGuard ====
section

namespace W9Machine
def pieceGuard (tr : ChainTrace) : ChainPieceKind → Bool
  | .head off dst chain digit => decide
      (320 ≤ off ∧ off + 64 ≤ 784 ∧ off % 8 = 0 ∧
       336 ≤ dst ∧ dst + 32 ≤ 784 ∧ dst % 8 = 0 ∧ chain < 6 ∧ digit < 4)
  | .rung digit dst =>
      decide (0 < tr.queries.length ∧ 320 ≤ tr.input ∧ tr.input + 64 ≤ 784 ∧
        tr.input % 8 = 0 ∧ 336 ≤ dst.getD tr.output ∧ dst.getD tr.output + 32 ≤ 784 ∧
        dst.getD tr.output % 8 = 0 ∧ digit < 4) &&
      match tr.read (tr.input + 16) with
      | .header chain old => decide (chain = tr.chain ∧ chain < 6 ∧ old < 4)
      | _ => false
  | .copy off dst => decide
      (off + 64 ≤ 784 ∧ off % 8 = 0 ∧ 336 ≤ dst ∧ dst + 16 ≤ 784 ∧ dst % 8 = 0)
  | .jump _ | .leaf => true
def planGuard : List ChainPiece → ChainTrace → Bool
  | [], _ => false
  | p :: ps, tr =>
      pieceGuard tr p.kind &&
      decide (p.words.length = p.result.steps + if p.isHash then 1 else 0) &&
      match p.kind with
      | .leaf => ps.isEmpty
      | _ => (ps.head?.map ChainPiece.pc == some p.nextPc) &&
          planGuard ps (tr.step p.kind)
end W9Machine
end
-- ==== merged from W9Machine_WctImageLink ====
section

namespace W9Machine.Frozen
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem codeChunks_length : codeChunks.length = 1005 :=
  SigGolfCandidate.T3M.Verify.vChunks_length
theorem codeChunks_ok : (codeChunks.dropLast.all fun c ↦ c.length == 256) = true :=
  SigGolfCandidate.T3M.Verify.vChunks_ok
theorem codeChunks_le : (codeChunks.all fun c ↦ decide (c.length ≤ 256)) = true :=
  SigGolfCandidate.T3M.Verify.vChunks_le
theorem image_code_eq : image.code = SigGolfCandidate.T3M.Images.verifyCode := by
  change SigGolfCandidate.T3M.Verify.vChunks.flatten = _
  exact SigGolfCandidate.T3M.Verify.verifyCode_eq.symm
def codeFrom (p : Nat) : List (BitVec 32) := SigGolfCandidate.T3M.Verify.codeFrom p
theorem codeFrom_eq (p : Nat) (hp : p < 257181) : codeFrom p = image.code.drop p := by
  rw [image_code_eq]
  exact SigGolfCandidate.T3M.Verify.codeFrom_eq p (by omega)
theorem codeFrom_at (p : Nat) (hp : p < 257181) : CodeAt image (pcOf p) (codeFrom p) := by
  have hl : image.code.length ≤ 256 * 1005 := by
    rw [image_code_eq]
    exact SigGolfCandidate.T3M.Verify.verifyCode_length
  have hp' : (pcOf p).toNat = 0x1000 + 4 * p := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  rw [codeFrom_eq p hp]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hp', List.length_drop]
    omega
  · rw [hp', show (0x1000 + 4 * p - 0x1000) / 4 = p by omega]
end W9Machine.Frozen
end
-- ==== merged from W9Machine_WctFetch ====
section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def sliceChecked (pc : Nat) (words : List (BitVec 32)) : Bool :=
  decide (pc < 257181) && (words == (Frozen.codeFrom pc).take words.length)
theorem slice_at (pc : Nat) (words : List (BitVec 32)) (h : sliceChecked pc words = true) :
    CodeAt Frozen.image (pcOf pc) words := by
  simp only [sliceChecked, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hb := Frozen.codeFrom_at pc h.1
  have hpref : words <+: Frozen.codeFrom pc := h.2 ▸ List.take_prefix _ _
  exact ⟨hb.1, hb.2.1, by
    have := hpref.length_le
    have := hb.2.2.1
    omega, hpref.trans hb.2.2.2⟩
theorem chainPiece_steps (p : ChainPiece) (hlink : sliceChecked p.pc p.words = true)
    (hcheck : p.checked = true) (s : MachineState) (hpc : s.pc = pcOf p.pc)
    (hob : ∀ o ∈ p.result.st.obl, o.holds s) :
    Steps Frozen.image s p.result.steps p.result.cycles (p.result.toState s) := by
  exact symRun_sound (rOK_eq hcheck) (slice_at p.pc p.words hlink) s hpc
    ((Oblig.all_iff s _).mpr hob)
theorem chainPiece_ecall (p : ChainPiece) (hlink : sliceChecked p.pc p.words = true)
    (hcheck : p.checked = true) (s : MachineState)
    (hob : ∀ o ∈ p.result.st.obl, o.holds s) (hstop : p.result.stop = .ecall) :
    SigGolfCandidate.Legacy.Riscv.fetch Frozen.image (p.result.toState s) =
      some (.base .ECALL) := by
  exact symRun_ecall (rOK_eq hcheck) (slice_at p.pc p.words hlink) s
    ((Oblig.all_iff s _).mpr hob) hstop
end W9Machine

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64

theorem chainPiece_steps_at {im : SigGolfCandidate.Legacy.Riscv.Image} (p : ChainPiece)
    (hc : CodeAt im (pcOf p.pc) p.words) (hcheck : p.checked = true)
    (s : MachineState) (hpc : s.pc = pcOf p.pc)
    (hob : ∀ o ∈ p.result.st.obl, o.holds s) :
    Steps im s p.result.steps p.result.cycles (p.result.toState s) := by
  exact symRun_sound (rOK_eq hcheck) hc s hpc ((Oblig.all_iff s _).mpr hob)

theorem chainPiece_ecall_at {im : SigGolfCandidate.Legacy.Riscv.Image} (p : ChainPiece)
    (hc : CodeAt im (pcOf p.pc) p.words) (hcheck : p.checked = true)
    (s : MachineState) (hob : ∀ o ∈ p.result.st.obl, o.holds s)
    (hstop : p.result.stop = .ecall) :
    SigGolfCandidate.Legacy.Riscv.fetch im (p.result.toState s) = some (.base .ECALL) := by
  exact symRun_ecall (rOK_eq hcheck) hc s ((Oblig.all_iff s _).mpr hob) hstop

end W9Machine
end
-- ==== merged from W9Machine_WctJudg ====
section

namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M publicHash shortHash pad64 HashOutput Digest)
variable {im : Image}
theorem GoodQFor.mono {s : MachineState} {N C A N' C' A' : Nat} {Q Q' : Prop} {X : OracleComp HashSpec Obs}
    (h : GoodQFor (P := P) im s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hQ : Q → Q' ∧ A ≤ A') :
    GoodQFor (P := P) im s N' C' Q' A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs hok => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs hok
  exact ⟨(hQ hq).1, by have := (hQ hq).2; omega⟩
theorem GoodQFor.congr {s : MachineState} {N C A : Nat} {Q : Prop} {X Y : OracleComp HashSpec Obs}
    (h : GoodQFor (P := P) im s N C Q A X) (hXY : X = Y) : GoodQFor (P := P) im s N C Q A Y := hXY ▸ h
theorem GoodQFor.steps {s t : MachineState} {k c N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs}
    (hst : Steps im s k c t) (h : GoodQFor (P := P) im t N C Q A X) : GoodQFor (P := P) im s (N + k) (C + c) Q (A + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs hok => ?_⟩
    obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs hok
    exact ⟨hq, by omega⟩
theorem GoodQFor.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {Q Q' : Prop}
    {X : OracleComp HashSpec Obs} (hst : Steps im s k c t) (h : GoodQFor (P := P) im t N C Q A X)
    (hN : N + k ≤ N') (hC : C + c ≤ C') (hQ : Q → Q' ∧ A + c ≤ A') : GoodQFor (P := P) im s N' C' Q' A' X :=
  (h.steps hst).mono hN hC hQ
theorem GoodQFor.query {s : MachineState} {N C A : Nat} {Q : Prop} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, GoodQFor (P := P) im (writeHash s a) N C Q A (K a)) :
    GoodQFor (P := P) im s (N + 1) (C + 8 * q.blocks) Q (A + 8 * q.blocks)
      (cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_query, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash q) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs hok => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs hok
    exact ⟨hq, by omega⟩
theorem GoodQFor.publicHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : HashOutput → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a, GoodQFor (P := P) im (writeHash s a) N C Q A (ccM (f a) K)) :
    GoodQFor (P := P) im s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (publicHash input >>= f) K) := by
  have := GoodQFor.query (P := P) (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]
theorem GoodQFor.shortHash_bind {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : Digest → M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQFor (P := P) im (writeHash s a) N C Q A (ccM (f (a.extractLsb' 0 128)) K)) :
    GoodQFor (P := P) im s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (shortHash input >>= f) K) := by
  have := GoodQFor.query (P := P) (K := fun a => ccM (f (a.extractLsb' 0 128)) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_shortHash_bind]
theorem GoodQFor.halt {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch im s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (hQ : s.getReg .x10 = 0 → Q ∧ 1 ≤ A) :
    GoodQFor (P := P) im s 1 1 Q A (pure (decide (s.getReg .x10 = 0), 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf h5, map_pure]
    by_cases hx : s.getReg .x10 = 0
    · simp only [obs, hx, if_true]
    · simp only [obs, hx, if_false]; rfl
  · rw [hF', evalWith_halt hash (F - 1) hf h5]
    by_cases hx : s.getReg .x10 = 0
    · simp only [hx, if_true]
      exact ⟨by decide +kernel, le_refl _, fun _ _ => hQ hx⟩
    · simp only [hx, if_false]
      exact ⟨by decide +kernel, le_refl _, fun h _ => absurd h (by decide +kernel)⟩
theorem GoodQFor.reject {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch im s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : GoodQFor (P := P) im s 1 1 Q A (pure (false, 0)) := by
  have := GoodQFor.halt (P := P) (Q := Q) (A := A) hf h5 (fun h => absurd (h10.symm.trans h) (by decide +kernel))
  rwa [h10] at this
theorem GoodQFor.accept {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch im s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 0) (hQ : Q) (hA : 1 ≤ A) :
    GoodQFor (P := P) im s 1 1 Q A (pure (true, 0)) := by
  have := GoodQFor.halt (P := P) (Q := Q) (A := A) hf h5 (fun _ => ⟨hQ, hA⟩)
  rwa [h10] at this
end W9Machine
end
-- ==== merged from W9Machine_WctPlanGood ====
section

section
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M shortHash pad64 Digest)
theorem chainPiece_shortHash {β : Type} (p : ChainPiece)
    (hlink : sliceChecked p.pc p.words = true) (hcheck : p.checked = true)
    (s : MachineState) (hpc : s.pc = pcOf p.pc)
    (hob : ∀ o ∈ p.result.st.obl, o.holds s) (hstop : p.result.stop = .ecall)
    (N C A : Nat) (Q : Prop) (input : List UInt8)
    (f : Digest → M β) (K : β → OracleComp HashSpec Obs)
    (h5 : (p.result.toState s).getReg .x5 = 0)
    (hv : hashArgumentsValid (p.result.toState s) = true)
    (hin : hashInput (p.result.toState s) = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQFor (P := P) Frozen.image (writeHash (p.result.toState s) a)
      N C Q A (ccM (f (a.extractLsb' 0 128)) K)) :
    GoodQFor (P := P) Frozen.image s (N + 1 + p.result.steps)
      (C + 8 * (toQ (pad64 input)).blocks + p.result.cycles) Q
      (A + 8 * (toQ (pad64 input)).blocks + p.result.cycles)
      (ccM (shortHash input >>= f) K) := by
  exact GoodQFor.steps (P := P) (chainPiece_steps p hlink hcheck s hpc hob)
    (GoodQFor.shortHash_bind (P := P) (chainPiece_ecall p hlink hcheck s hob hstop) h5 hv hin h)
end W9Machine
end
section
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify RiscvZkvm.Rv64
def chainPlan : List ChainPiece → MachineState → OracleComp HashSpec MachineState
  | [], s => pure s
  | p :: ps, s =>
      let t := p.result.toState s
      if p.isHash then do
        let ans ← (liftM (HashSpec.query (hashInput t)) : OracleComp HashSpec (BitVec 256))
        chainPlan ps (writeHash t ans)
      else chainPlan ps t
def planFuel : List ChainPiece → Nat
  | [] => 0
  | p :: ps => planFuel ps + p.result.steps + if p.isHash then 1 else 0
def planCycles : List ChainPiece → Nat
  | [] => 0
  | p :: ps => planCycles ps + p.totalCycles
def PlanReady : List ChainPiece → MachineState → (MachineState → Prop) → Prop
  | [], s, post => post s
  | p :: ps, s, post =>
      sliceChecked p.pc p.words = true ∧ p.checked = true ∧ s.pc = pcOf p.pc ∧
      (∀ o ∈ p.result.st.obl, o.holds s) ∧
      (if p.isHash then
        p.result.stop = .ecall ∧ (p.result.toState s).getReg .x5 = 0 ∧
        hashArgumentsValid (p.result.toState s) = true ∧
        (hashInput (p.result.toState s)).blocks = 1 ∧
        ∀ ans, PlanReady ps (writeHash (p.result.toState s) ans) post
      else PlanReady ps (p.result.toState s) post)
theorem chainPlan_good (ps : List ChainPiece) (s : MachineState) (post : MachineState → Prop)
    (hready : PlanReady ps s post) (N C A : Nat) (Q : Prop)
    (K : MachineState → OracleComp HashSpec Obs)
    (hK : ∀ t, post t → GoodQFor (P := P) Frozen.image t N C Q A (K t)) :
    GoodQFor (P := P) Frozen.image s (N + planFuel ps) (C + planCycles ps) Q (A + planCycles ps)
      (cc (chainPlan ps s) K) := by
  induction ps generalizing s with
  | nil => simpa only [chainPlan, planFuel, planCycles, Nat.add_zero, cc_pure] using hK s hready
  | cons p ps ih =>
    obtain ⟨hl, hc, hpc, hob, hr⟩ := hready
    by_cases hh : p.isHash = true
    · rw [if_pos hh] at hr
      obtain ⟨hstop, h5, hv, hb, htail⟩ := hr
      have hq := GoodQFor.query (P := P) (chainPiece_ecall p hl hc s hob hstop) h5 hv rfl
        (fun ans => ih _ (htail ans))
      have hs := GoodQFor.steps (P := P) (chainPiece_steps p hl hc s hpc hob) hq
      simpa only [chainPlan, if_pos hh, cc_bind, planFuel, planCycles,
        ChainPiece.totalCycles, hh, if_true, hb, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    · rw [if_neg hh] at hr
      have hs := GoodQFor.steps (P := P) (chainPiece_steps p hl hc s hpc hob) (ih _ hr)
      simpa only [chainPlan, if_neg hh, planFuel, planCycles, ChainPiece.totalCycles,
        Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
end W9Machine
end


namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000

def PlanReadyAt (im : Image) : List ChainPiece → MachineState → (MachineState → Prop) → Prop
  | [], s, post => post s
  | p :: ps, s, post =>
      CodeAt im (pcOf p.pc) p.words ∧ p.checked = true ∧ s.pc = pcOf p.pc ∧
      (∀ o ∈ p.result.st.obl, o.holds s) ∧
      (if p.isHash then
        p.result.stop = .ecall ∧ (p.result.toState s).getReg .x5 = 0 ∧
        hashArgumentsValid (p.result.toState s) = true ∧
        (hashInput (p.result.toState s)).blocks = 1 ∧
        ∀ ans, PlanReadyAt im ps (writeHash (p.result.toState s) ans) post
      else PlanReadyAt im ps (p.result.toState s) post)

theorem chainPlan_sim {im : Image} (ps : List ChainPiece) (s : MachineState) (post : MachineState → Prop)
    (hready : PlanReadyAt im ps s post) :
    Sim im s (planCycles ps) (chainPlan ps s) (fun result t => result = t ∧ post t) := by
  induction ps generalizing s with
  | nil => exact Sim.pure ⟨rfl, hready⟩
  | cons p ps ih =>
    obtain ⟨hl, hc, hpc, hob, hr⟩ := hready
    by_cases hh : p.isHash = true
    · rw [if_pos hh] at hr
      obtain ⟨hstop, h5, hv, hb, htail⟩ := hr
      have hq := Sim.query_bind (chainPiece_ecall_at p hl hc s hob hstop) h5 hv rfl
        (fun ans => ih _ (htail ans))
      have hs := Sim.steps (chainPiece_steps_at p hl hc s hpc hob) hq
      simpa only [chainPlan, if_pos hh, planCycles, ChainPiece.totalCycles, hh, if_true, hb,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    · rw [if_neg hh] at hr
      have hs := Sim.steps (chainPiece_steps_at p hl hc s hpc hob) (ih _ hr)
      simpa only [chainPlan, if_neg hh, planCycles, ChainPiece.totalCycles,
        Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

end W9Machine
end
-- ==== merged from W9Machine_WctChainControl ====
section

namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def terminalTrace : List ChainPiece → ChainTrace → ChainTrace
  | [], tr => tr
  | p :: ps, tr => if p.kind = .leaf then tr else terminalTrace ps (tr.step p.kind)
def PlanLinked (ps : List ChainPiece) : Prop :=
  ∀ p ∈ ps, sliceChecked p.pc p.words = true ∧ p.checked = true
theorem chain_next_pc (p : ChainPiece) (s : MachineState) (ans : BitVec 256)
    (hl : p.kind ≠ .leaf)
    (hw : p.words.length = p.result.steps + if p.isHash then 1 else 0) :
    (if p.isHash then writeHash (p.result.toState s) ans else p.result.toState s).pc =
      pcOf p.nextPc := by
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      simp only [ChainPiece.result, ChainPiece.isHash, headRHRel, if_true] at hw
      change (writeHash ((headRHRel .x8 _ _ pc chain digit).toState s) ans).pc = pcOf (pc + words.length)
      rw [writeHash_pc]
      change pcOf (pc + 4) + 4 = _
      rw [SigGolfCandidate.T3M.pcOf_add4]
      congr 1
      omega
    | rung digit dst =>
      cases dst <;>
        simp only [ChainPiece.result, ChainPiece.isHash, rungRRel, Option.map,
          Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true] at hw
      all_goals
        simp only [ChainPiece.isHash, if_true, writeHash_pc, ChainPiece.result,
          rungRRel, Option.map, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true,
          Result.toState_pc, E.eval, ChainPiece.nextPc]
        rw [SigGolfCandidate.T3M.pcOf_add4]
        congr 1
        omega
    | copy off dst =>
      simp only [ChainPiece.result, ChainPiece.isHash, copyFHRel, Bool.false_eq_true, if_false, Nat.add_zero] at hw
      change pcOf (pc + 4) = pcOf (pc + words.length)
      rw [hw]
    | jump target => rfl
    | leaf => exact False.elim (hl rfl)
end W9Machine
end
-- ==== merged from W9Machine_WctTraceProgram ====
section

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M publicHash)
open SphincsSecurity (bytesLE)
def wordBytes (ws : List Word) : List UInt8 := ws.flatMap (bytesLE 8)
def pieceQuery (tr : ChainTrace) (p : ChainPiece) : List ChainWord :=
  (tr.step p.kind).queries.getD tr.queries.length []
def planQueries : List ChainPiece → ChainTrace → List (List ChainWord)
  | [], _ => []
  | p :: ps, tr =>
      if p.isHash then pieceQuery tr p :: planQueries ps (tr.step p.kind)
      else planQueries ps (tr.step p.kind)
def traceProgram (base : ChainWord → Word) : List (List ChainWord) → List (BitVec 256) →
    M (List (BitVec 256))
  | [], answers => pure answers
  | q :: qs, answers => do
      let ans ← publicHash (wordBytes (q.map (chainValue base answers)))
      traceProgram base qs (answers ++ [ans])
theorem wordBytes_length (ws : List Word) : (wordBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordBytes, List.flatMap_cons, List.length_append, SphincsSecurity.bytesLE_length,
      List.length_cons] at *
    omega
theorem wordsOf_wordBytes (ws : List Word) : wordsOf (wordBytes ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change wordsOf (bytesLE 8 w ++ wordBytes ws) = w :: ws
    rw [wordsOf_append8 _ _ (SphincsSecurity.bytesLE_length _ _), readLE_bytesLE]
    simpa using congrArg (w :: ·) ih
theorem wordBytes_wordsOf (input : List UInt8) (n : Nat) (hn : input.length = 8 * n) :
    wordBytes (wordsOf input) = input := by
  have hl : (wordBytes (wordsOf input)).length = 8 * n := by
    rw [wordBytes_length, length_wordsOf n input hn]
  apply readLE_inj (hl.trans hn.symm)
  rw [← wordsToNat_wordsOf n _ hl, wordsOf_wordBytes, wordsToNat_wordsOf n input hn]
theorem ChainTrace.step_queries (tr : ChainTrace) (p : ChainPiece) :
    (tr.step p.kind).queries = tr.queries ++ if p.isHash then [pieceQuery tr p] else [] := by
  have qhash (t : ChainTrace) : t.hash.queries = t.queries ++
      [(List.range 8).map fun i => t.read (t.input + 8 * i)] := rfl
  cases p with
  | mk pc words kind =>
    cases kind <;> simp [pieceQuery, ChainTrace.step, ChainPiece.isHash, qhash,
      ChainTrace.put, List.getD_eq_getElem?_getD]
theorem planQueries_spec (ps : List ChainPiece) (tr : ChainTrace) :
    (ps.foldl (fun t p => t.step p.kind) tr).queries = tr.queries ++ planQueries ps tr := by
  induction ps generalizing tr with
  | nil => simp only [List.foldl_nil, planQueries, List.append_nil]
  | cons p ps ih =>
    rw [List.foldl_cons, ih, tr.step_queries p]
    simp only [planQueries]
    split_ifs <;> simp only [List.append_nil, List.append_assoc, List.singleton_append]
end W9Machine
end
-- ==== merged from W9Machine_WctChainSplit ====
section

set_option autoImplicit false
namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
def sourceEnds (w : WBytes) (k : Fin 9) (rank : Fin 666)
    (answers : List (BitVec 256)) : List Digest :=
  (List.finRange 6).map fun t =>
    let digits := ClaudeWCT.WCT9.codeword rank
    if digits.getD t.val 0 = 0 then wdig w (V3.regionOffset k.val + V3.leafSlot t.val)
    else (answers.getD ((digits.take (t.val + 1)).sum - 1) 0).extractLsb' 0 128
def SourceEquivalent : Prop :=
  ∀ (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 666)
    (u : MachineState), Pre L w index k j rank u →
    (do
      let answers ← traceProgram (originalValue L u index k j)
        (expectedQueries (ClaudeWCT.WCT9.codeword rank)) []
      pure (sourceEnds w k rank answers) : M (List Digest)) = program w index k j rank
def EndpointsCorrect : Prop :=
  ∀ (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 666)
    (u s : MachineState) (tr : ChainTrace) (answers : List (BitVec 256)),
    Pre L w index k j rank u → Inv L u index k j tr answers s →
    (∀ t, t < 6 → ∀ word, word < 2 →
      tr.read (traceLeafSlot t + 8 * word) =
        expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word) →
    ∀ t, t < 6 →
      DigAt s (base L k + traceLeafSlot t) ((sourceEnds w k rank answers).getD t 0)
end W9Machine.Chain
end
-- ==== merged from W9Machine_WctRoutineReady ====
section

section
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem chainPiece_steps_cycles (p : ChainPiece) : p.result.steps = p.result.cycles := by
  cases p with
  | mk pc words kind => cases kind <;> rfl
theorem planFuel_le_cycles (ps : List ChainPiece) : planFuel ps ≤ planCycles ps := by
  induction ps with
  | nil => exact Nat.le_refl 0
  | cons p ps ih =>
    simp only [planFuel, planCycles, ChainPiece.totalCycles, chainPiece_steps_cycles]
    split_ifs <;> omega
theorem planCycles_eq (r : ChainRoutine) : planCycles r.pieces = r.cycles := by
  unfold ChainRoutine.cycles
  induction r.pieces with
  | nil => rfl
  | cons p ps ih => simpa only [planCycles, List.map_cons, List.sum_cons, Nat.add_comm] using congrArg (· + p.totalCycles) ih
theorem ChainRoutine.checked_cycles (r : ChainRoutine) (h : r.checked = true) : r.cycles ≤ 89 := by
  simp only [checked, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2
theorem chainRoutine_good (r : ChainRoutine) (hr : r.checked = true)
    (s : MachineState) (post : MachineState → Prop) (hready : PlanReady r.pieces s post)
    (N C A : Nat) (Q : Prop) (K : MachineState → OracleComp HashSpec Obs)
    (hK : ∀ t, post t → GoodQFor (P := P) Frozen.image t N C Q A (K t)) :
    GoodQFor (P := P) Frozen.image s (N + 89) (C + 89) Q (A + 89)
      (cc (chainPlan r.pieces s) K) := by
  have hc := r.checked_cycles hr
  have hp := planCycles_eq r
  have hf := planFuel_le_cycles r.pieces
  exact (chainPlan_good r.pieces s post hready N C A Q K hK).mono
    (by omega) (by omega) (fun h => ⟨h, by omega⟩)
end W9Machine
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
structure RoutineReady (rank : Fin 666) (r : ChainRoutine) : Prop where
  guard : planGuard r.pieces {} = true
  linked : PlanLinked r.pieces
  entry : r.pieces.head?.map ChainPiece.pc = some (chainEntries.getD rank.val 0)
  queries : planQueries r.pieces {} = expectedQueries (ClaudeWCT.WCT9.codeword rank)
  endpoints : ∀ t, t < 6 → ∀ word, word < 2 →
    (terminalTrace r.pieces {}).read (traceLeafSlot t + 8 * word) =
      expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word
  pad : (terminalTrace r.pieces {}).read 672 = .original 672 ∧
    (terminalTrace r.pieces {}).read 680 = .original 680
  cycles : planCycles r.pieces ≤ 89
def terminalChecked (r : ChainRoutine) : Bool :=
  (planQueries r.pieces {} == expectedQueries r.digits) &&
    ((List.range 6).all fun t => (List.range 2).all fun word =>
      (terminalTrace r.pieces {}).read (traceLeafSlot t + 8 * word) ==
        expectedEndpoint r.digits t word) &&
    ((terminalTrace r.pieces {}).read 672 == .original 672) &&
    ((terminalTrace r.pieces {}).read 680 == .original 680)
end W9Machine.Chain
end
end
-- ==== merged from W9Machine_WctN600Assembly ====
section

section









section
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
set_option maxRecDepth 10000
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def hLoad (i d : Nat) : E := .ld (addC (.reg .x28) (hOff i d))
theorem leafSetup_keeps : Keeps leafSetupRel [.x25, .x10, .x11] := by
  intro r hr
  simp only [leafSetupRel]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hr (by simp))]
theorem leafSetup_mem (s : MachineState) (B A : Nat)
    (hbase : s.getReg .x8 = BitVec.ofNat 64 B) (hhi : B + 784 < 2 ^ 64) (hA : A < 2 ^ 64) :
    (leafSetupRel.toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + 664 then 0 else
      if A = B + 656 then s.getReg .x31 else s.getMem (BitVec.ofNat 64 A) := by
  exact memEval_two s _ _ _ _ (B + 664) (B + 656) A
    (by change s.getReg .x8 + 664 = _; rw [hbase]; exact ofNat_add_ofNat B 664)
    (by change s.getReg .x8 + 656 = _; rw [hbase]; exact ofNat_add_ofNat B 656)
    (by omega) (by omega) hA
theorem leaf_trace_mem (value : ChainWord → Word) (tr : ChainTrace) (s : MachineState) (B : Nat)
    (ht : TraceMem value B tr s) (hbase : s.getReg .x8 = BitVec.ofNat 64 B)
    (hB : B + 784 < 2 ^ 64) (hh : s.getReg .x31 = value .leafHeader)
    (hr : (0 : Word) = value .zero) :
    TraceMem value B (tr.step .leaf) (leafSetupRel.toState s) := by
  intro x hx
  rw [leafSetup_mem s B (B + x) hbase hB (by omega)]
  simp only [ChainTrace.step, ChainTrace.read_put]
  split_ifs <;> first | omega | exact ht x hx
theorem leafSetup_regs (s : MachineState) (B : Nat) (hbase : s.getReg .x8 = BitVec.ofNat 64 B) :
    (leafSetupRel.toState s).getReg .x10 = BitVec.ofNat 64 (B + 640) ∧
    (leafSetupRel.toState s).getReg .x11 = 128 ∧
    (leafSetupRel.toState s).pc = (s.getReg .x23 + 4) &&& ~~~1#64 := by
  simp only [leafSetupRel, Result.toState_getReg, Result.toState_pc,
    RegFile.get, RegFile.set, addC_eval, E.eval, BinOp.eval, hbase]
  exact ⟨ofNat_add_ofNat B 640, trivial, trivial⟩
end W9Machine
end
section
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
def wctChainClobbers : List Reg := [.x3, .x10, .x11, .x12, .x14, .x25]
theorem chainPiece_keeps (p : ChainPiece) : Keeps p.result wctChainClobbers := by
  intro r hr
  have hsmall : ∀ ws : List Reg, (∀ x ∈ ws, x ∈ wctChainClobbers) → r ∉ ws := by
    intro ws h hmem; exact hr (h r hmem)
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      exact headRHRel_keeps _ _ _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | rung digit dst =>
      exact rungRRel_keeps _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | copy off dst =>
      exact copyFHRel_keeps _ _ _ _ r
        (hsmall _ (by simp [wctChainClobbers]))
    | jump target => rfl
    | leaf => exact leafSetup_keeps r (hsmall _ (by simp [wctChainClobbers]))
end W9Machine
end
section
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem hKey_relative (s : MachineState) (H chain digit : Nat)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (H + 2048))
    (hH : H + 4096 < 2 ^ 64) (hc : chain < 8) (hd : digit < 3) :
    (hKey chain digit).eval s = BitVec.ofNat 64 (H + 64 * chain + 8 * digit) := by
  simp only [hKey, Addr.eval, E.eval, h28, hOff]
  convert ofNat_add_off0 (H + 2048) (64 * chain + 8 * digit) 2048 (by omega) (by omega) using 1 <;> congr 1; omega
theorem headRHRel_obligations (s : MachineState) (B off dst pc chain digit : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 B)
    (hB : B + 784 ≤ 2 ^ 24)
    (haB : B % 8 = 0) (hao : off % 8 = 0)
    (ho : off + 64 ≤ 784) :
    ∀ o ∈ (headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).st.obl,
      o.holds s := by
  intro o hm
  simp only [headRHRel, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  change accessValid ((kAt .x8 (BitVec.ofNat 64 off) 16).eval s) 8 = true
  rw [relative_key s .x8 B off 16 h8]
  exact valid_ofNat _ _ (by omega) (by omega)
theorem rungRRel_obligations (s : MachineState) (B off digit pc : Nat) (dst : Option Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + off))
    (hB : B + 784 ≤ 2 ^ 24) (haB : B % 8 = 0) (hao : off % 8 = 0)
    (ho : off + 64 ≤ 784) :
    ∀ o ∈ (rungRRel .x8 digit dst pc).st.obl, o.holds s := by
  intro o hm
  simp only [rungRRel, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · change (s.getReg .x10).toNat % 8 = 0
    rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : B + off < 2 ^ 64)]
    omega
  · change accessValid ((⟨some (.reg .x10), 17⟩ : Addr).eval s) 1 = true
    have he : (⟨some (.reg .x10), 17⟩ : Addr).eval s = BitVec.ofNat 64 (B + off + 17) := by
      simp only [Addr.eval, E.eval, h10]
      exact ofNat_add_ofNat (B + off) 17
    rw [he]
    exact valid_ofNat _ _ (by omega) (by omega)
theorem copyFHRel_obligations (s : MachineState) (B off dst pc : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 B) (hB : B + 784 ≤ 2 ^ 24)
    (haB : B % 8 = 0) (hao : off % 8 = 0) (had : dst % 8 = 0)
    (ho : off + 64 ≤ 784) (hd : dst + 16 ≤ 784) :
    ∀ o ∈ (copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc).st.obl, o.holds s := by
  intro o hm
  simp only [copyFHRel, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  all_goals
    simp only [Oblig.holds, relative_key s .x8 B _ _ h8]
    exact valid_ofNat _ _ (by omega) (by omega)
end W9Machine
end
section
set_option autoImplicit false
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.headerLoad {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 666} {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (t d : Nat) (ht : t < 6) (hd : d < 4) :
    (packedHeader t d).eval s = BitVec.ofNat 64 (V3.chainLow index k.val j.val t d) := by
  exact packedHeader_eval s index k.val j.val t d
    ((hs.keep .x31 (by decide)).trans hu.leafWord) hu.indexBound k.isLt j.isLt ht hd
theorem Inv.leafLoad {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 666} {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s) :
    s.getReg .x31 = BitVec.ofNat 64 (V3.leafLow index k.val j.val) :=
  (hs.keep .x31 (by decide)).trans hu.leafWord
end W9Machine.Chain
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.rung {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (digit pc old : Nat) (dst : Option Nat) (ans : BitVec 256)
    (hn : 0 < answers.length) (hi : 320 ≤ tr.input ∧ tr.input + 64 ≤ 784)
    (hdst : 336 ≤ dst.getD tr.output ∧ dst.getD tr.output + 32 ≤ 784)
    (hc : tr.chain < 6) (ho : old < 4) (hd : digit < 4)
    (hh : tr.read (tr.input + 16) = .header tr.chain old) :
    Inv L u index k j (tr.step (.rung digit dst)) (answers ++ [ans])
      (writeHash ((rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) pc).toState s) ans) := by
  have hk := k.isLt
  have hB : base L k + 784 < 2 ^ 64 := by unfold base coordinateBase Layout.shift; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hp := hs.pointers hn
  have hstep := packedPos_eval s digit hd
    ((hs.keep .x7 (by decide)).trans hu.stepOne)
    ((hs.keep .x13 (by decide)).trans hu.stepTwo)
    ((hs.keep .x19 (by decide)).trans (hu.heaps 3 (by decide) (by decide)))
  let prepared := (rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) pc).toState s
  have h12 : prepared.getReg .x12 = BitVec.ofNat 64 (base L k + dst.getD tr.output) := by
    cases dst with
    | none => exact hp.2
    | some d =>
      simp only [prepared, rungRRel, Option.map, Option.getD_some, Result.toState_getReg,
        RegFile.get, RegFile.set, addC_eval, E.eval, hb]
      exact ofNat_add_ofNat (base L k) d
  have hf : Frame s prepared (writes L k) :=
    (rungRRel_frame s .x8 digit pc (base L k + tr.input) (dst.map (BitVec.ofNat 64))
      hp.1 (by omega) hstep).mono (by intro A hA hw; unfold writes; omega)
  have hhash : Frame prepared (writeHash prepared ans) (writes L k) := by
    intro A hA hnot
    rw [writeHash_getMem_ofNat prepared ans (base L k + dst.getD tr.output) A h12 hA (by omega)]
    unfold writes at hnot
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨?_, ?_, ?_, ?_, tr.available_step _ hs.available, ?_, ?_⟩
  · intro r hr
    rw [writeHash_getReg]
    exact ((chainPiece_keeps ⟨pc, [], .rung digit dst⟩).reg s hr).trans (hs.keep r hr)
  · exact ((hs.frame.trans hf).trans hhash).mono (by intro A hA hw; rcases hw with (h | h) | h <;> exact h)
  · let th : ChainTrace :=
      { tr.put (tr.input + 16) (.header tr.chain digit) with
        output := dst.getD tr.output,
        valid := tr.valid && (match tr.read (tr.input + 16) with
          | .header chain _ => chain == tr.chain | _ => false) }
    apply hash_trace_append (originalValue L u index k j) answers ans th prepared (base L k)
      ?_ ?_ hs.count h12 hB hdst.2
    · apply rung_trace_mem _ tr s (base L k) digit pc (dst.map (BitVec.ofNat 64))
        hs.memory hp.1 hB hi.2 hstep
      rw [show base L k + tr.input + 16 = base L k + (tr.input + 16) by omega,
        hs.memory (tr.input + 16) (by omega), hh]
      exact wct_header_step k.val index j.val tr.chain old digit hk hu.indexBound j.isLt hc ho hd
    · exact tr.available_put (tr.input + 16) (.header tr.chain digit) hs.available trivial
  · change (tr.queries ++ [_]).length = (answers ++ [ans]).length
    simp only [List.length_append, List.length_singleton, hs.count]
  · rw [writeHash_getReg]
    exact ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hs.hashLen
  · intro _
    rw [writeHash_getReg, writeHash_getReg]
    exact ⟨((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hp.1, h12⟩
end W9Machine.Chain
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.head {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (off dst pc chain digit : Nat) (ans : BitVec 256)
    (hoff : 320 ≤ off ∧ off + 64 ≤ 784) (hdst : 336 ≤ dst ∧ dst + 32 ≤ 784)
    (hc : chain < 6) (hd : digit < 4) :
    Inv L u index k j (tr.step (.head off dst chain digit)) (answers ++ [ans])
      (writeHash ((headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
        pc chain digit).toState s) ans) := by
  have hk := k.isLt
  have hB : base L k + 784 < 2 ^ 64 := by unfold base coordinateBase Layout.shift; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hp := headRHRel_addresses .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
    pc chain digit s
  rw [hb, ofNat_add_ofNat, ofNat_add_ofNat] at hp
  let prepared := (headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).toState s
  have hf : Frame s prepared (writes L k) :=
    (headRHRel_frame s .x8 (base L k) off dst pc chain digit hb (by omega)).mono
      (by intro A hA hw; unfold writes; omega)
  have hhash : Frame prepared (writeHash prepared ans) (writes L k) := by
    intro A hA hn
    rw [writeHash_getMem_ofNat prepared ans (base L k + dst) A hp.2 hA (by omega)]
    unfold writes at hn
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨?_, ?_, ?_, ?_, tr.available_step _ hs.available, ?_, ?_⟩
  · intro r hr
    rw [writeHash_getReg]
    exact ((chainPiece_keeps ⟨pc, [], .head off dst chain digit⟩).reg s hr).trans (hs.keep r hr)
  · exact ((hs.frame.trans hf).trans hhash).mono (by intro A hA hw; rcases hw with (h | h) | h <;> exact h)
  · let th : ChainTrace :=
      { tr.put (off + 16) (.header chain digit) with
        input := off, output := dst, chain := chain }
    apply hash_trace_append (originalValue L u index k j) answers ans th prepared (base L k)
      ?_ ?_ hs.count hp.2 hB hdst.2
    · exact head_trace_mem _ tr s (base L k) off dst pc chain digit hs.memory hb hB hoff.2
        (hs.headerLoad hu chain digit hc hd)
    · exact tr.available_put _ (.header chain digit) hs.available trivial
  · change (tr.queries ++ [_]).length = (answers ++ [ans]).length
    simp only [List.length_append, List.length_singleton, hs.count]
  · rw [writeHash_getReg]
    exact ((headRHRel_keeps .x8 _ _ pc chain digit).reg s (by decide)).trans hs.hashLen
  · intro _
    rw [writeHash_getReg, writeHash_getReg]
    exact hp
end W9Machine.Chain
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.copy {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (off dst pc : Nat) (hoff : off + 64 ≤ 784)
    (hdst : 336 ≤ dst ∧ dst + 16 ≤ 784) :
    Inv L u index k j (tr.step (.copy off dst)) answers
      ((copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc).toState s) := by
  have hk := k.isLt
  have hB : base L k + 784 < 2 ^ 64 := by unfold base coordinateBase Layout.shift; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hf := (copyFHRel_frame s .x8 (base L k) off dst pc hb (by omega)).mono
    (show ∀ A, A < 2 ^ 64 → A = base L k + dst ∨ A = base L k + dst + 8 → writes L k A from
      by intro A hA hw; unfold writes; omega)
  refine ⟨?_, ?_, ?_, hs.count, tr.available_step _ hs.available, ?_, ?_⟩
  · intro r hr
    exact ((chainPiece_keeps ⟨pc, [], .copy off dst⟩).reg s hr).trans (hs.keep r hr)
  · exact (hs.frame.trans hf).mono (by intro A hA hw; exact hw.elim id id)
  · exact copy_trace_mem _ tr s (base L k) off dst pc hs.memory hb hB hoff hdst.2
  · exact ((copyFHRel_keeps .x8 _ _ pc).reg s (by decide)).trans hs.hashLen
  · intro hn
    exact ⟨((copyFHRel_keeps .x8 _ _ pc).reg s (by decide)).trans (hs.pointers hn).1,
      ((copyFHRel_keeps .x8 _ _ pc).reg s (by decide)).trans (hs.pointers hn).2⟩
theorem Inv.jump {L : Layout} {index : Nat} {k : Fin 9} {j : Fin 128}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hs : Inv L u index k j tr answers s) (pc target : Nat) :
    Inv L u index k j (tr.step (.jump target)) answers
      ((ChainPiece.result ⟨pc, [], .jump target⟩).toState s) := by
  refine ⟨?_, ?_, ?_, hs.count, hs.available, ?_, ?_⟩
  · intro r hr
    exact ((chainPiece_keeps ⟨pc, [], .jump target⟩).reg s hr).trans (hs.keep r hr)
  · intro A hA hn; exact hs.frame A hA hn
  · intro off ho; exact hs.memory off ho
  · exact hs.hashLen
  · exact hs.pointers
end W9Machine.Chain
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem Inv.hashEffect {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = true) (hg : pieceGuard tr p.kind = true)
    (ans : BitVec 256) :
    Inv L u index k j (tr.step p.kind) (answers ++ [ans]) (writeHash (p.result.toState s) ans) := by
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      obtain ⟨hlo, hhi, _, hdlo, hdhi, _, hc, hd⟩ := hg
      exact hs.head hu off dst pc chain digit ans ⟨hlo, hhi⟩ ⟨hdlo, hdhi⟩ hc hd
    | rung digit dst =>
      simp only [pieceGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨hn, hilo, hihi, _, hdlo, hdhi, _, hd⟩, hheader⟩ := hg
      cases he : tr.read (tr.input + 16) with
      | header chain old =>
        simp only [he, decide_eq_true_eq] at hheader
        obtain ⟨hechain, hc, ho⟩ := hheader
        subst chain
        exact hs.rung hu digit pc old dst ans (by rw [← hs.count]; exact hn)
          ⟨hilo, hihi⟩ ⟨hdlo, hdhi⟩ hc ho hd he
      | original off => simp [he] at hheader
      | zero => simp [he] at hheader
      | answer q i => simp [he] at hheader
      | leafHeader => simp [he] at hheader
    | copy off dst => contradiction
    | jump target => contradiction
    | leaf => contradiction
theorem Inv.plainEffect {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = false) (hl : p.kind ≠ .leaf)
    (hg : pieceGuard tr p.kind = true) :
    Inv L u index k j (tr.step p.kind) answers (p.result.toState s) := by
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit => contradiction
    | rung digit dst => contradiction
    | copy off dst =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      exact hs.copy hu off dst pc hg.1 ⟨hg.2.2.1, hg.2.2.2.1⟩
    | jump target => exact hs.jump pc target
    | leaf => exact False.elim (hl rfl)
theorem Inv.plainObligations {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = false) (hg : pieceGuard tr p.kind = true) :
    ∀ o ∈ p.result.st.obl, o.holds s := by
  have hk := k.isLt
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have hB : base L k + 784 ≤ 2 ^ 24 := by unfold base coordinateBase Layout.shift; omega
  have haB : base L k % 8 = 0 := by unfold base coordinateBase Layout.shift; omega
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit => contradiction
    | rung digit dst => contradiction
    | copy off dst =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      exact copyFHRel_obligations s (base L k) off dst pc hb hB haB hg.2.1 hg.2.2.2.2
        hg.1 hg.2.2.2.1
    | jump target => intro o ho; contradiction
    | leaf =>
      intro o ho
      simp only [ChainPiece.result, leafSetupRel, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · change accessValid (s.getReg .x8 + 664) 8 = true
        rw [hb]
        change accessValid (BitVec.ofNat 64 (base L k) + BitVec.ofNat 64 664) 8 = true
        rw [ofNat_add_ofNat]
        exact valid_ofNat _ _ (by omega) (by omega)
      · change accessValid (s.getReg .x8 + 656) 8 = true
        rw [hb]
        change accessValid (BitVec.ofNat 64 (base L k) + BitVec.ofNat 64 656) 8 = true
        rw [ofNat_add_ofNat]
        exact valid_ofNat _ _ (by omega) (by omega)
end W9Machine.Chain
end
section
namespace W9Machine
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (pad64)
def prepareTrace (tr : ChainTrace) : ChainPieceKind → ChainTrace
  | .head off dst chain digit =>
      { tr.put (off + 16) (.header chain digit) with
        input := off, output := dst, chain := chain }
  | .rung digit dst =>
      { tr.put (tr.input + 16) (.header tr.chain digit) with
        output := dst.getD tr.output,
        valid := tr.valid && (match tr.read (tr.input + 16) with
          | .header chain _ => chain == tr.chain | _ => false) }
  | kind => tr.step kind
theorem pieceQuery_prepared (tr : ChainTrace) (p : ChainPiece) (hh : p.isHash = true) :
    pieceQuery tr p = (List.range 8).map fun i =>
      (prepareTrace tr p.kind).read ((prepareTrace tr p.kind).input + 8 * i) := by
  have qhash (t : ChainTrace) : t.hash.queries = t.queries ++
      [(List.range 8).map fun i => t.read (t.input + 8 * i)] := rfl
  cases p with
  | mk pc words kind =>
    cases kind <;> simp only [ChainPiece.isHash, Bool.false_eq_true] at hh
    all_goals first
      | contradiction
      | simp [pieceQuery, ChainTrace.step, qhash, prepareTrace, ChainTrace.put,
          List.getD_eq_getElem?_getD]
    all_goals intro a ha; rfl
theorem preparedQuery (value : ChainWord → Word) (B : Nat) (tr : ChainTrace)
    (p : ChainPiece) (s : MachineState) (hh : p.isHash = true)
    (hm : TraceMem value B (prepareTrace tr p.kind) s)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (B + (prepareTrace tr p.kind).input))
    (h11 : s.getReg .x11 = 64) (hB : B + 784 < 2 ^ 64)
    (hi : (prepareTrace tr p.kind).input + 64 ≤ 784)
    (ha : (B + (prepareTrace tr p.kind).input) % 8 = 0) :
    hashInput s = toQ (pad64 (wordBytes ((pieceQuery tr p).map value))) ∧
    (toQ (pad64 (wordBytes ((pieceQuery tr p).map value)))).blocks = 1 := by
  have hl : (wordBytes ((pieceQuery tr p).map value)).length = 64 := by
    rw [wordBytes_length, List.length_map, pieceQuery_prepared tr p hh,
      List.length_map, List.length_range]
  rw [SigGolfCandidate.T3M.pad64_of_aligned _ (by omega)]
  refine ⟨TraceMem.hashInput value B (prepareTrace tr p.kind) s _ hm h10 h11 hB hi ha hl ?_, ?_⟩
  · rw [wordsOf_wordBytes, pieceQuery_prepared tr p hh, List.map_map]
    rfl
  · rw [blocks_toQ ⟨by omega, by omega⟩, hl]
end W9Machine
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (pad64)
structure PreparedHash (value : ChainWord → Word) (tr : ChainTrace) (p : ChainPiece)
    (s : MachineState) : Prop where
  obligations : ∀ o ∈ p.result.st.obl, o.holds s
  stop : p.result.stop = .ecall
  mode : (p.result.toState s).getReg .x5 = 0
  valid : hashArgumentsValid (p.result.toState s) = true
  query : hashInput (p.result.toState s) = toQ (pad64 (wordBytes ((pieceQuery tr p).map value)))
  blocks : (toQ (pad64 (wordBytes ((pieceQuery tr p).map value)))).blocks = 1
theorem Inv.hashReady {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (p : ChainPiece) (hh : p.isHash = true) (hg : pieceGuard tr p.kind = true) :
    PreparedHash (chainValue (originalValue L u index k j) answers) tr p s := by
  have hk := k.isLt
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  have h5 := (hs.keep .x5 (by decide)).trans hu.hashMode
  have hB : base L k + 784 ≤ 2 ^ 24 := by unfold base coordinateBase Layout.shift; omega
  have hBig : base L k + 784 < 2 ^ 64 := by omega
  have haB : base L k % 8 = 0 := by unfold base coordinateBase Layout.shift; omega
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      simp only [pieceGuard, decide_eq_true_eq] at hg
      obtain ⟨hlo, hhi, halign, hdlo, hdhi, hdalign, hchain, hdigit⟩ := hg
      have hp := headRHRel_addresses .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit s
      rw [hb, ofNat_add_ofNat, ofNat_add_ofNat] at hp
      have hlen := ((headRHRel_keeps .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).reg s (by decide)).trans hs.hashLen
      have hm := head_trace_mem _ tr s (base L k) off dst pc chain digit hs.memory hb hBig hhi
        (hs.headerLoad hu chain digit hchain hdigit)
      have hq := preparedQuery _ (base L k) tr ⟨pc, words, .head off dst chain digit⟩ _ hh hm
        hp.1 hlen hBig hhi (by change (base L k + off) % 8 = 0; omega)
      refine ⟨?_, rfl, ?_, ?_, hq.1, hq.2⟩
      · exact headRHRel_obligations s (base L k) off dst pc chain digit
          hb hB haB halign hhi
      · exact ((headRHRel_keeps .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) pc chain digit).reg s (by decide)).trans h5
      · exact hashArgs_const _ (base L k + off) 64 (base L k + dst) hp.1 hlen hp.2
          (by omega) (by decide) (by omega) (by omega) (by omega)
    | rung digit dst =>
      simp only [pieceGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨hn, hilo, hihi, hai, hdlo, hdhi, had, hd⟩, hheader⟩ := hg
      have hp := hs.pointers (by rw [← hs.count]; exact hn)
      have hstep := packedPos_eval s digit hd
        ((hs.keep .x7 (by decide)).trans hu.stepOne)
        ((hs.keep .x13 (by decide)).trans hu.stepTwo)
        ((hs.keep .x19 (by decide)).trans (hu.heaps 3 (by decide) (by decide)))
      let prepared := (rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) pc).toState s
      have h10 := ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hp.1
      have hlen := ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans hs.hashLen
      have h12 : prepared.getReg .x12 = BitVec.ofNat 64 (base L k + dst.getD tr.output) := by
        cases dst with
        | none => exact hp.2
        | some d =>
          simp only [prepared, rungRRel, Option.map, Option.getD_some, Result.toState_getReg,
            RegFile.get, RegFile.set, addC_eval, E.eval, hb]
          exact ofNat_add_ofNat (base L k) d
      have hm : TraceMem (chainValue (originalValue L u index k j) answers) (base L k)
          (prepareTrace tr (.rung digit dst)) prepared := by
        apply rung_trace_mem _ tr s (base L k) digit pc (dst.map (BitVec.ofNat 64))
          hs.memory hp.1 hBig hihi hstep
        cases he : tr.read (tr.input + 16) with
        | header chain old =>
          simp only [he, decide_eq_true_eq] at hheader
          obtain ⟨hechain, hc, ho⟩ := hheader
          subst chain
          rw [show base L k + tr.input + 16 = base L k + (tr.input + 16) by omega,
            hs.memory (tr.input + 16) (by omega), he]
          exact wct_header_step k.val index j.val tr.chain old digit hk hu.indexBound j.isLt hc ho hd
        | original off => simp [he] at hheader
        | zero => simp [he] at hheader
        | answer q i => simp [he] at hheader
        | leafHeader => simp [he] at hheader
      have hq := preparedQuery _ (base L k) tr ⟨pc, words, .rung digit dst⟩ prepared hh hm
        h10 hlen hBig hihi (by change (base L k + tr.input) % 8 = 0; omega)
      refine ⟨?_, rfl, ?_, ?_, hq.1, hq.2⟩
      · exact rungRRel_obligations s (base L k) tr.input digit pc (dst.map (BitVec.ofNat 64))
          hp.1 hB haB hai hihi
      · exact ((rungRRel_keeps .x8 digit (dst.map (BitVec.ofNat 64)) pc).reg s (by decide)).trans h5
      · exact hashArgs_const prepared (base L k + tr.input) 64 (base L k + dst.getD tr.output)
          h10 hlen h12 (by omega) (by decide) (by omega) (by omega) (by omega)
    | copy off dst => contradiction
    | jump target => contradiction
    | leaf => contradiction
end W9Machine.Chain
end
section
set_option autoImplicit false
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem merkleField_of_frame {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9}
    {j : Fin 128} {rank : Fin 666} {u s : MachineState} (hu : Pre L w index k j rank u)
    (hf : Frame u s (writes L k)) (off : Nat) (ha : off % 8 = 0)
    (ho : off + 16 ≤ 336 ∨ (784 ≤ off ∧ off + 16 ≤ 848)) :
    DigAt s (base L k + off) (wdig w (V3.regionOffset k.val + off)) := by
  have hk := k.isLt
  have h0 := hu.origW off (by omega) ha
  have h1 : OrigWD L.shift w u (base L k + off + 8) := by
    simpa only [Nat.add_assoc] using hu.origW (off + 8) (by omega) (by omega)
  have hdig := DigAt_origWD h0 h1 (by unfold base coordinateBase Layout.shift; omega)
  have he : base L k + off + L.shift - 0x1020 = V3.regionOffset k.val + off := by
    unfold base coordinateBase Layout.shift V3.regionOffset
    omega
  rw [he] at hdig
  exact hdig.frame hf (by unfold base coordinateBase Layout.shift; omega)
    (by unfold writes; omega) (by unfold writes; omega)
/-- Nested FTS child fields: levels 0..4 below the chain window, level 5 in the fixed block `784..848`. -/
theorem v3_field_bounds : ∀ j : Fin 128, ∀ l : Fin 6,
    V3.sibOff j.val l.val % 8 = 0 ∧
      (V3.sibOff j.val l.val + 16 ≤ 336 ∨ (784 ≤ V3.sibOff j.val l.val ∧ V3.sibOff j.val l.val + 16 ≤ 848)) ∧
    V3.padOff j.val l.val % 8 = 0 ∧
      (V3.padOff j.val l.val + 16 ≤ 336 ∨ (784 ≤ V3.padOff j.val l.val ∧ V3.padOff j.val l.val + 16 ≤ 848)) ∧
    (V3.blkOff j.val l.val + 16) % 8 = 0 ∧
      (V3.blkOff j.val l.val + 16 + 16 ≤ 336 ∨
        (784 ≤ V3.blkOff j.val l.val + 16 ∧ V3.blkOff j.val l.val + 16 + 16 ≤ 848)) := by
  decide +kernel
theorem merklePad_of_frame {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9}
    {j : Fin 128} {rank : Fin 666} {u s : MachineState} (hu : Pre L w index k j rank u)
    (hf : Frame u s (writes L k)) (l : Nat) (hl : l < 6) :
    DigAt s (base L k + V3.padOff j.val l) (V3.nodePad w k.val j.val l) := by
  have hb := v3_field_bounds j ⟨l, hl⟩
  have h := merkleField_of_frame hu hf (V3.padOff j.val l) hb.2.2.1 hb.2.2.2.1
  simpa only [V3.nodePad, wdig] using h
theorem merkleSibling_of_frame {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9}
    {j : Fin 128} {rank : Fin 666} {u s : MachineState} (hu : Pre L w index k j rank u)
    (hf : Frame u s (writes L k)) (l : Nat) (hl : l < 6) :
    DigAt s (base L k + V3.sibOff j.val l) (V3.sibling w k.val j.val l) := by
  have hb := v3_field_bounds j ⟨l, hl⟩
  have h := merkleField_of_frame hu hf (V3.sibOff j.val l) hb.1 hb.2.1
  simpa only [V3.sibling, wdig] using h
theorem merkleTw_of_frame {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9}
    {j : Fin 128} {rank : Fin 666} {u s : MachineState} (hu : Pre L w index k j rank u)
    (hf : Frame u s (writes L k)) (l : Nat) (hl : l < 6) :
    DigAt s (base L k + V3.blkOff j.val l + 16) (V3.nodeTw w k.val j.val l) := by
  have hb := v3_field_bounds j ⟨l, hl⟩
  have h := merkleField_of_frame hu hf (V3.blkOff j.val l + 16) hb.2.2.2.2.1 hb.2.2.2.2.2
  rw [← Nat.add_assoc] at h
  simpa only [V3.nodeTw, wdig, Nat.add_assoc] using h
theorem Inv.leafPost {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128}
    {rank : Fin 666} {u s : MachineState} {tr : ChainTrace} {answers : List (BitVec 256)}
    (hu : Pre L w index k j rank u) (hs : Inv L u index k j tr answers s)
    (ends : List Digest) (hlen : ends.length = 6)
    (hends : ∀ t, t < 6 → DigAt s (base L k + traceLeafSlot t) (ends.getD t 0))
    (hpad : tr.read 672 = .original 672 ∧ tr.read 680 = .original 680) :
    Post L w index k j u ends (leafSetupRel.toState s) := by
  have hk := k.isLt
  have hB : base L k + 784 < 2 ^ 64 := by unfold base coordinateBase Layout.shift; omega
  have hb := (hs.keep .x8 (by decide)).trans hu.baseReg
  let prepared := leafSetupRel.toState s
  have hp := leafSetup_regs s (base L k) hb
  have hkeep : ∀ r, r ∉ clobbers → prepared.getReg r = u.getReg r := by
    intro r hr
    exact ((chainPiece_keeps ⟨0, [], .leaf⟩).reg s hr).trans (hs.keep r hr)
  have hfLeaf : Frame s prepared (fun A => A = base L k + 656 ∨ A = base L k + 664) := by
    intro A hA hn
    rw [leafSetup_mem s (base L k) A hb hB hA,
      if_neg (fun h => hn (Or.inr h)), if_neg (fun h => hn (Or.inl h))]
  have hf : Frame u prepared (writes L k) := (hs.frame.trans hfLeaf).mono
    (by intro A hA hw; rcases hw with h | h; exact h; unfold writes; omega)
  have hend : ∀ t, t < 6 → DigAt prepared (base L k + traceLeafSlot t) (ends.getD t 0) := by
    intro t ht
    apply (hends t ht).frame hfLeaf
    · unfold traceLeafSlot base coordinateBase Layout.shift; split_ifs <;> omega
    · unfold traceLeafSlot; split_ifs <;> omega
    · unfold traceLeafSlot; split_ifs <;> omega
  have hLo : prepared.getMem (BitVec.ofNat 64 (base L k + 656)) =
      BitVec.ofNat 64 (V3.leafLow index k.val j.val) := by
    rw [leafSetup_mem s (base L k) (base L k + 656) hb hB (by omega), if_neg (by omega), if_pos rfl]
    exact hs.leafLoad hu
  have hHi : prepared.getMem (BitVec.ofNat 64 (base L k + 664)) = 0 := by
    rw [leafSetup_mem s (base L k) (base L k + 664) hb hB (by omega), if_pos rfl]
  have hSlot1 : DigAt prepared (base L k + 640 + 16 * 1)
      (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends 1) := by
    simp only [V3.leafFields, if_neg (show (1 : Nat) ≠ 0 by decide), if_true, ClaudeWCT.WCT9.ftsLeafHeader]
    refine ⟨?_, ?_⟩
    · rw [show base L k + 640 + 16 * 1 = base L k + 656 by omega, hLo, BitVec.extractLsb'_append_eq_right]
      rfl
    · rw [show base L k + 640 + 16 * 1 + 8 = base L k + 664 by omega, hHi, BitVec.extractLsb'_append_eq_left]
      rfl
  have hSlot2 : DigAt prepared (base L k + 640 + 16 * 2)
      (V3.leafFields k.val index j.val (V3.leafPad w k.val) ends 2) := by
    have hw0 : OrigWD L.shift w u (base L k + 672) := hu.origW 672 (by decide) (by decide)
    have hw1 : OrigWD L.shift w u (base L k + 672 + 8) := by
      simpa only [Nat.add_assoc] using hu.origW 680 (by decide) (by decide)
    have hdig := DigAt_origWD hw0 hw1 (by unfold base coordinateBase Layout.shift; omega)
    have he : base L k + 672 + L.shift - 0x1020 = V3.regionOffset k.val + 672 := by
      unfold base coordinateBase Layout.shift V3.regionOffset
      omega
    rw [he] at hdig
    have h720 : prepared.getMem (BitVec.ofNat 64 (base L k + 672)) = u.getMem (BitVec.ofNat 64 (base L k + 672)) := by
      rw [hfLeaf (base L k + 672) (by omega) (by omega), hs.memory 672 (by omega), hpad.1]
      rfl
    have h728 : prepared.getMem (BitVec.ofNat 64 (base L k + 672 + 8)) =
        u.getMem (BitVec.ofNat 64 (base L k + 672 + 8)) := by
      rw [show base L k + 672 + 8 = base L k + 680 by omega, hfLeaf (base L k + 680) (by omega) (by omega),
        hs.memory 680 (by omega), hpad.2]
      rfl
    have hv : V3.leafFields k.val index j.val (V3.leafPad w k.val) ends 2 =
        wdig w (V3.regionOffset k.val + 672) := by
      simp only [V3.leafFields, if_neg (show (2 : Nat) ≠ 0 by decide), if_neg (show (2 : Nat) ≠ 1 by decide),
        if_true, V3.leafPad, ClaudeWCT.W9.T3M.wleafPad, ClaudeWCT.W9.T3M.wctLeafBlock,
        ClaudeWCT.W9.T3M.regionBase, V3.regionOffset, wdig]
    rw [hv, show base L k + 640 + 16 * 2 = base L k + 672 by omega]
    exact ⟨h720.trans hdig.1, h728.trans hdig.2⟩
  refine { length := hlen, keep := hkeep, frame := hf, child := ?_ }
  refine {
    indexBound := hu.indexBound, length := hlen, pc := ?_,
    hashMode := (hkeep .x5 (by decide)).trans hu.hashMode,
    baseReg := (hkeep .x8 (by decide)).trans hu.baseReg,
    hashInput := hp.1, hashLen := hp.2.1,
    nodeWord := (hkeep .x15 (by decide)).trans hu.nodeWord,
    returnPC := (hkeep .x1 (by decide)).trans hu.returnPC,
    heaps := ?_, leafAt := ?_,
    padAt := fun l hl => merklePad_of_frame hu hf l hl,
    sibAt := fun l hl => merkleSibling_of_frame hu hf l hl,
    twAt := fun l hl => merkleTw_of_frame hu hf l hl }
  · rw [hp.2.2, hs.keep .x23 (by decide), hu.childPC, SigGolfCandidate.T3M.pcOf_add4, pcOf_and_not1]
  · intro h hlo hhi
    have hn : Child.heapReg h ∉ clobbers := by interval_cases h <;> decide
    exact (hkeep _ hn).trans (hu.heaps h hlo hhi)
  · intro i hi
    by_cases h0 : i = 0
    · subst i; simpa [V3.leafFields, traceLeafSlot] using hend 0 (by decide)
    · by_cases h1 : i = 1
      · subst i; exact hSlot1
      · by_cases h2 : i = 2
        · subst i; exact hSlot2
        · have he : base L k + 640 + 16 * i = base L k + traceLeafSlot (i - 2) := by
            unfold traceLeafSlot
            rw [if_neg (by omega)]
            omega
          simpa only [V3.leafFields, if_neg h0, if_neg h1, if_neg h2, he] using hend (i - 2) (by omega)
end W9Machine.Chain
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem runPlan_good {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u)
    (ps : List ChainPiece) (tr : ChainTrace) (answers : List (BitVec 256)) (s : MachineState)
    (hs : Inv L u index k j tr answers s) (hg : planGuard ps tr = true) (hl : PlanLinked ps)
    (hpc : ∀ p, ps.head? = some p → s.pc = pcOf p.pc)
    (N C A : Nat) (Q : Prop) (K : List (BitVec 256) → OracleComp HashSpec Obs)
    (hK : ∀ answers' s', Inv L u index k j (terminalTrace ps tr) answers' s' →
      GoodQFor (P := P) Frozen.image (leafSetupRel.toState s') N C Q A (K answers')) :
    GoodQFor (P := P) Frozen.image s (N + planFuel ps) (C + planCycles ps) Q (A + planCycles ps)
      (ccM (traceProgram (originalValue L u index k j) (planQueries ps tr) answers) K) := by
  induction ps generalizing tr answers s with
  | nil => simp [planGuard] at hg
  | cons p ps ih =>
    obtain ⟨hlink, hcheck⟩ := hl p (by simp)
    have hguard := hg
    simp only [planGuard, Bool.and_eq_true, decide_eq_true_eq] at hguard
    obtain ⟨⟨hguard, hw⟩, hrest⟩ := hguard
    by_cases hleaf : p.kind = .leaf
    · have hnil : ps = [] := by simpa [hleaf] using hrest
      subst ps
      have hh : p.isHash = false := by simp [ChainPiece.isHash, hleaf]
      have he : p.result = leafSetupRel := by simp [ChainPiece.result, hleaf]
      have ht := chainPiece_steps p hlink hcheck s (hpc p rfl) (hs.plainObligations hu p hh hguard)
      rw [he] at ht
      have hc := GoodQFor.steps (P := P) ht (hK answers s (by simpa [terminalTrace, hleaf] using hs))
      simpa only [planFuel, planCycles, planQueries, hh, Bool.false_eq_true, if_false,
        traceProgram, ccM_pure, ChainPiece.totalCycles, he, leafSetupRel,
        Nat.zero_add, Nat.add_zero] using hc
    · have htail : ((ps.head?.map ChainPiece.pc == some p.nextPc) &&
          planGuard ps (tr.step p.kind)) = true := by
        cases he : p.kind <;> simp_all
      simp only [Bool.and_eq_true, beq_iff_eq] at htail
      obtain ⟨hnext, hgtail⟩ := htail
      have hltail : PlanLinked ps := fun q hq => hl q (List.mem_cons_of_mem p hq)
      have hktail : ∀ answers' s', Inv L u index k j (terminalTrace ps (tr.step p.kind)) answers' s' →
          GoodQFor (P := P) Frozen.image (leafSetupRel.toState s') N C Q A (K answers') := by
        intro answers' s' h
        exact hK answers' s' (by simpa only [terminalTrace, if_neg hleaf] using h)
      have hnpc (ans : BitVec 256) : ∀ q, ps.head? = some q →
          (if p.isHash then writeHash (p.result.toState s) ans else p.result.toState s).pc = pcOf q.pc := by
        intro q hq
        have he : q.pc = p.nextPc := by simpa only [hq, Option.map_some, Option.some.injEq] using hnext
        exact (chain_next_pc p s ans hleaf hw).trans (congrArg pcOf he.symm)
      by_cases hh : p.isHash = true
      · have hr := hs.hashReady hu p hh hguard
        have hc := fun ans => ih (tr.step p.kind) (answers ++ [ans]) _
          (hs.hashEffect hu p hh hguard ans) hgtail hltail
          (by simpa only [if_pos hh] using hnpc ans) hktail
        have hq := GoodQFor.publicHash_bind (P := P)
          (chainPiece_ecall p hlink hcheck s hr.obligations hr.stop)
          hr.mode hr.valid hr.query hc
        have hrun := GoodQFor.steps (P := P) (chainPiece_steps p hlink hcheck s (hpc p rfl) hr.obligations) hq
        simpa only [planFuel, planCycles, planQueries, if_pos hh, traceProgram,
          ChainPiece.totalCycles, hr.blocks, Nat.mul_one, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hrun
      · have hfalse : p.isHash = false := Bool.eq_false_iff.mpr hh
        have hc := ih (tr.step p.kind) answers _ (hs.plainEffect hu p hfalse hleaf hguard)
          hgtail hltail (by simpa only [if_neg hh] using hnpc 0) hktail
        have hrun := GoodQFor.steps (P := P)
          (chainPiece_steps p hlink hcheck s (hpc p rfl) (hs.plainObligations hu p hfalse hguard)) hc
        simpa only [planFuel, planCycles, planQueries, if_neg hh, ChainPiece.totalCycles,
          Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrun
end W9Machine.Chain
end
section
namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem good_of_ready (source : SourceEquivalent) (endpoints : EndpointsCorrect)
    (rank : Fin 666) (r : ChainRoutine) (hr : RoutineReady rank r) : Good Frozen.layout rank (P := P) := by
  intro w index k j u N C A Q K hu hK
  have hpc : ∀ p, r.pieces.head? = some p → u.pc = pcOf p.pc := by
    intro p hp
    have he := hr.entry
    rw [hp] at he
    have he' : p.pc = chainEntries.getD rank.val 0 := Option.some.inj he
    exact hu.pc.trans (congrArg pcOf he'.symm)
  have hk : ∀ answers s, Inv Frozen.layout u index k j (terminalTrace r.pieces {}) answers s →
      GoodQFor (P := P) Frozen.image (leafSetupRel.toState s) N C Q A
        (K (sourceEnds w k rank answers)) := by
    intro answers s hs
    exact hK _ _ (hs.leafPost hu _ (by simp [sourceEnds])
      (endpoints Frozen.layout w index k j rank u s _ answers hu hs hr.endpoints) hr.pad)
  have hrun := runPlan_good hu r.pieces {} [] u (inv_initial Frozen.layout w index k j rank u hu)
    hr.guard hr.linked hpc N C A Q (fun answers => K (sourceEnds w k rank answers)) hk
  have hcost := hr.cycles
  have hfuel := planFuel_le_cycles r.pieces
  have hbig := hrun.mono (A' := A + 89) (by omega : N + planFuel r.pieces ≤ N + 89)
    (by omega : C + planCycles r.pieces ≤ C + 89) (fun h => ⟨h, by omega⟩)
  apply hbig.congr
  rw [hr.queries]
  have he := congrArg (fun p => ccM p K) (source Frozen.layout w index k j rank u hu)
  simpa only [ccM_bind, ccM_pure] using he
theorem allGood_of_ready (source : SourceEquivalent) (endpoints : EndpointsCorrect)
    (ready : ∀ rank : Fin 666, ∃ r, RoutineReady rank r) : AllGood Frozen.layout (P := P) := by
  intro rank
  obtain ⟨r, hr⟩ := ready rank
  exact good_of_ready source endpoints rank r hr
end W9Machine.Chain
end
end

section


namespace W9Machine.N600
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open Chain OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem good_of_ready (source : Chain.SourceEquivalent) (endpoints : Chain.EndpointsCorrect)
    (rank : Fin 563) (r : ChainRoutine) (hr : Chain.RoutineReady (embed rank) r)
    (hrankcost : planCycles r.pieces ≤ rankCost rank) : Good Frozen.layout rank (P := P) := by
  intro w index k j u N C A Q K hu hK
  have hpc : ∀ p, r.pieces.head? = some p → u.pc = pcOf p.pc := by
    intro p hp
    have he := hr.entry
    rw [hp] at he
    have he' : p.pc = chainEntries.getD (embed rank).val 0 := Option.some.inj he
    exact hu.pc.trans (congrArg pcOf he'.symm)
  have hk : ∀ answers s, Inv Frozen.layout u index k j (terminalTrace r.pieces {}) answers s →
      GoodQFor (P := P) Frozen.image (leafSetupRel.toState s) N C Q A
        (K (sourceEnds w k (embed rank) answers)) := by
    intro answers s hs
    exact hK _ _ (hs.leafPost hu _ (by simp [sourceEnds])
      (endpoints Frozen.layout w index k j (embed rank) u s _ answers hu hs hr.endpoints) hr.pad)
  have hrun := runPlan_good hu r.pieces {} [] u (inv_initial Frozen.layout w index k j (embed rank) u hu)
    hr.guard hr.linked hpc N C A Q (fun answers => K (sourceEnds w k (embed rank) answers)) hk
  have hcost := hr.cycles
  have hfuel := planFuel_le_cycles r.pieces
  have hbig := hrun.mono (A' := A + rankCost rank) (by omega : N + planFuel r.pieces ≤ N + 89)
    (by omega : C + planCycles r.pieces ≤ C + 89) (fun h => ⟨h, by omega⟩)
  apply hbig.congr
  rw [hr.queries]
  have he := congrArg (fun p => ccM p K) (source Frozen.layout w index k j (embed rank) u hu)
  simpa only [ccM_bind, ccM_pure, N600.program, Chain.program] using he
end W9Machine.N600
end

namespace W9Machine.N600
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open Chain OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem good_of_ready_layout (L : Layout)
    (himage : L.image = Frozen.image)
    (hchain : ∀ r, L.chainWord r = Frozen.layout.chainWord r) (source : Chain.SourceEquivalent) (endpoints : Chain.EndpointsCorrect)
    (rank : Fin 563) (r : ChainRoutine) (hr : Chain.RoutineReady (embed rank) r)
    (hrankcost : planCycles r.pieces ≤ rankCost rank) : Good L rank (P := P) := by
  intro w index k j u N C A Q K hu hK
  change (∀ ends t, Post L w index k j u ends t → GoodQFor (P := P) L.image t N C Q A (K ends)) at hK
  rw [himage] at hK ⊢
  have hpc : ∀ p, r.pieces.head? = some p → u.pc = pcOf p.pc := by
    intro p hp
    have he := hr.entry
    rw [hp] at he
    have he' : p.pc = chainEntries.getD (embed rank).val 0 := Option.some.inj he
    exact hu.pc.trans ((congrArg pcOf (hchain (embed rank))).trans (congrArg pcOf he'.symm))
  have hk : ∀ answers s, Inv L u index k j (terminalTrace r.pieces {}) answers s →
      GoodQFor (P := P) Frozen.image (leafSetupRel.toState s) N C Q A
        (K (sourceEnds w k (embed rank) answers)) := by
    intro answers s hs
    exact hK _ _ (hs.leafPost hu _ (by simp [sourceEnds])
      (endpoints L w index k j (embed rank) u s _ answers hu hs hr.endpoints) hr.pad)
  have hrun := runPlan_good hu r.pieces {} [] u (inv_initial L w index k j (embed rank) u hu)
    hr.guard hr.linked hpc N C A Q (fun answers => K (sourceEnds w k (embed rank) answers)) hk
  have hcost := hr.cycles
  have hfuel := planFuel_le_cycles r.pieces
  have hbig := hrun.mono (A' := A + rankCost rank) (by omega : N + planFuel r.pieces ≤ N + 89)
    (by omega : C + planCycles r.pieces ≤ C + 89) (fun h => ⟨h, by omega⟩)
  apply hbig.congr
  rw [hr.queries]
  have he := congrArg (fun p => ccM p K) (source L w index k j (embed rank) u hu)
  simpa only [ccM_bind, ccM_pure, N600.program, Chain.program] using he
end W9Machine.N600

namespace W9Machine.Chain
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem shared_field_bounds : ∀ j : Fin 128, ∀ l : Fin 6,
    SharedV3.sibOff j.val l.val % 8 = 0 ∧
      (SharedV3.sibOff j.val l.val + 16 ≤ 336 ∨
        (784 ≤ SharedV3.sibOff j.val l.val ∧ SharedV3.sibOff j.val l.val + 16 ≤ 848)) ∧
    (SharedV3.blkOff j.val l.val + 32) % 8 = 0 ∧
      (SharedV3.blkOff j.val l.val + 32 + 16 ≤ 336 ∨
        (784 ≤ SharedV3.blkOff j.val l.val + 32 ∧ SharedV3.blkOff j.val l.val + 32 + 16 ≤ 848)) ∧
    (SharedV3.blkOff j.val l.val + 16) % 8 = 0 ∧
      (SharedV3.blkOff j.val l.val + 16 + 16 ≤ 336 ∨
        (784 ≤ SharedV3.blkOff j.val l.val + 16 ∧ SharedV3.blkOff j.val l.val + 16 + 16 ≤ 848)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem Post.sharedChild {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {raw : Fin 128}
    {rank : Fin 666} {u t : MachineState} {ends : List Digest}
    (hu : Pre L w index k raw rank u) (ht : Post L w index k raw u ends t) :
    SharedChild.Pre L w index k raw ends t := by
  have hj := SharedV3.physical_lt k.val raw.val raw.isLt
  refine ⟨ht.child.indexBound, ht.length, ht.child.pc, ht.child.baseReg,
    ht.child.hashMode, ht.child.hashInput, ht.child.hashLen, ht.child.nodeWord,
    ht.child.returnPC, ht.child.heaps, ht.child.leafAt, ?_, ?_, ?_⟩
  · intro l hl
    have hb := shared_field_bounds ⟨SharedV3.physical k.val raw.val, hj⟩ ⟨l, hl⟩
    have h := merkleField_of_frame hu ht.frame
      (SharedV3.blkOff (SharedV3.physical k.val raw.val) l + 32) hb.2.2.1 hb.2.2.2.1
    simpa only [SharedV3.nodePad, base, Nat.add_assoc] using h
  · intro l hl
    have hb := shared_field_bounds ⟨SharedV3.physical k.val raw.val, hj⟩ ⟨l, hl⟩
    have h := merkleField_of_frame hu ht.frame
      (SharedV3.sibOff (SharedV3.physical k.val raw.val) l) hb.1 hb.2.1
    simpa only [SharedV3.sibling, base] using h
  · intro l hl
    have hb := shared_field_bounds ⟨SharedV3.physical k.val raw.val, hj⟩ ⟨l, hl⟩
    have h := merkleField_of_frame hu ht.frame
      (SharedV3.blkOff (SharedV3.physical k.val raw.val) l + 16) hb.2.2.2.2.1 hb.2.2.2.2.2
    simpa only [SharedV3.nodeTw, base, Nat.add_assoc] using h
end W9Machine.Chain

namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem publicHash_sim_bind {β : Type} {im : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : BitVec 256 → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (SigGolfCandidate.T3.pad64 input))
    (h : ∀ a, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (SigGolfCandidate.T3.pad64 input)).blocks + W)
      (SigGolfCandidate.T3.publicHash input >>= f) Q := by
  unfold TBSim
  rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h

theorem runPlan_tbsim_at {α : Type} {im : Image} {sk : BitVec 256}
    {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u)
    (ps : List ChainPiece) (tr : ChainTrace) (answers : List (BitVec 256)) (s : MachineState)
    (hs : Inv L u index k j tr answers s) (hg : planGuard ps tr = true) (hl : PlanLinked ps)
    (hc : ∀ p ∈ ps, CodeAt im (pcOf p.pc) p.words)
    (hpc : ∀ p, ps.head? = some p → s.pc = pcOf p.pc)
    (W : Nat) (Q : α → MachineState → Prop) (K : List (BitVec 256) → M α)
    (hK : ∀ answers' s', Inv L u index k j (terminalTrace ps tr) answers' s' →
      TBSim im sk (leafSetupRel.toState s') W (K answers') Q) :
    TBSim im sk s (W + planCycles ps)
      (traceProgram (originalValue L u index k j) (planQueries ps tr) answers >>= K) Q := by
  induction ps generalizing tr answers s with
  | nil => simp [planGuard] at hg
  | cons p ps ih =>
    obtain ⟨hlink, hcheck⟩ := hl p (by simp)
    have hcode := hc p (by simp)
    have hguard := hg
    simp only [planGuard, Bool.and_eq_true, decide_eq_true_eq] at hguard
    obtain ⟨⟨hguard, hw⟩, hrest⟩ := hguard
    by_cases hleaf : p.kind = .leaf
    · have hnil : ps = [] := by simpa [hleaf] using hrest
      subst ps
      have hh : p.isHash = false := by simp [ChainPiece.isHash, hleaf]
      have he : p.result = leafSetupRel := by simp [ChainPiece.result, hleaf]
      have ht := chainPiece_steps_at p hcode hcheck s (hpc p rfl) (hs.plainObligations hu p hh hguard)
      rw [he] at ht
      have hsim := TBSim.steps ht (hK answers s (by simpa [terminalTrace, hleaf] using hs))
      simpa only [planCycles, planQueries, hh, Bool.false_eq_true, if_false,
        traceProgram, pure_bind, ChainPiece.totalCycles, he, leafSetupRel,
        Nat.zero_add, Nat.add_zero, Nat.add_comm] using hsim
    · have htail : ((ps.head?.map ChainPiece.pc == some p.nextPc) &&
          planGuard ps (tr.step p.kind)) = true := by
        cases he : p.kind <;> simp_all
      simp only [Bool.and_eq_true, beq_iff_eq] at htail
      obtain ⟨hnext, hgtail⟩ := htail
      have hltail : PlanLinked ps := fun q hq => hl q (List.mem_cons_of_mem p hq)
      have hctail : ∀ q ∈ ps, CodeAt im (pcOf q.pc) q.words := fun q hq => hc q (by simp [hq])
      have hktail : ∀ answers' s', Inv L u index k j (terminalTrace ps (tr.step p.kind)) answers' s' →
          TBSim im sk (leafSetupRel.toState s') W (K answers') Q := by
        intro answers' s' h
        exact hK answers' s' (by simpa only [terminalTrace, if_neg hleaf] using h)
      have hnpc (ans : BitVec 256) : ∀ q, ps.head? = some q →
          (if p.isHash then writeHash (p.result.toState s) ans else p.result.toState s).pc = pcOf q.pc := by
        intro q hq
        have he : q.pc = p.nextPc := by simpa only [hq, Option.map_some, Option.some.injEq] using hnext
        exact (chain_next_pc p s ans hleaf hw).trans (congrArg pcOf he.symm)
      by_cases hh : p.isHash = true
      · have hr := hs.hashReady hu p hh hguard
        have hsim := fun ans => ih (tr.step p.kind) (answers ++ [ans]) _
          (hs.hashEffect hu p hh hguard ans) hgtail hltail hctail
          (by simpa only [if_pos hh] using hnpc ans) hktail
        have hq := publicHash_sim_bind
          (chainPiece_ecall_at p hcode hcheck s hr.obligations hr.stop)
          hr.mode hr.valid hr.query hsim
        have hrun := TBSim.steps (chainPiece_steps_at p hcode hcheck s (hpc p rfl) hr.obligations) hq
        simpa only [planCycles, planQueries, if_pos hh, traceProgram, bind_assoc,
          ChainPiece.totalCycles, hr.blocks, Nat.mul_one, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hrun
      · have hfalse : p.isHash = false := Bool.eq_false_iff.mpr hh
        have hsim := ih (tr.step p.kind) answers _ (hs.plainEffect hu p hfalse hleaf hguard)
          hgtail hltail hctail (by simpa only [if_neg hh] using hnpc 0) hktail
        have hrun := TBSim.steps
          (chainPiece_steps_at p hcode hcheck s (hpc p rfl) (hs.plainObligations hu p hfalse hguard)) hsim
        simpa only [planCycles, planQueries, if_neg hh, ChainPiece.totalCycles,
          Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrun

end W9Machine.Chain

namespace W9Machine.N600
open Chain OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000

theorem tbsim_of_ready_layout (L : Layout) (sk : BitVec 256)
    (hchain : ∀ rank, L.chainWord rank = Frozen.layout.chainWord rank)
    (source : Chain.SourceEquivalent) (endpoints : Chain.EndpointsCorrect)
    (rank : Fin 563) (r : ChainRoutine) (hr : Chain.RoutineReady (embed rank) r)
    (hcode : ∀ p ∈ r.pieces, CodeAt L.image (pcOf p.pc) p.words)
    (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (hu : Pre L w index k j rank u) :
    TBSim L.image sk u 89 (program w index k j rank) (Post L w index k j u) := by
  have hpc : ∀ p, r.pieces.head? = some p → u.pc = pcOf p.pc := by
    intro p hp
    have he := hr.entry
    rw [hp] at he
    have he' : p.pc = chainEntries.getD (embed rank).val 0 := Option.some.inj he
    exact hu.pc.trans ((congrArg pcOf (hchain (embed rank))).trans (congrArg pcOf he'.symm))
  have hk : ∀ answers s, Inv L u index k j (terminalTrace r.pieces {}) answers s →
      TBSim L.image sk (leafSetupRel.toState s) 0 (pure (sourceEnds w k (embed rank) answers))
        (Post L w index k j u) := by
    intro answers s hs
    exact TBSim.pure (hs.leafPost hu _ (by simp [sourceEnds])
      (endpoints L w index k j (embed rank) u s _ answers hu hs hr.endpoints) hr.pad)
  have hrun := runPlan_tbsim_at hu r.pieces {} [] u (inv_initial L w index k j (embed rank) u hu)
    hr.guard hr.linked hcode hpc 0 (Post L w index k j u)
    (fun answers => pure (sourceEnds w k (embed rank) answers)) hk
  have hbig := hrun.mono (by have := hr.cycles; omega : 0 + planCycles r.pieces ≤ 89)
    (fun _ _ h => h)
  apply hbig.of_eq
  rw [hr.queries]
  exact congrArg (mrealize sk) (source L w index k j (embed rank) u hu)

end W9Machine.N600
end
-- ==== merged from W9Machine_WctSourceWords ====
section

set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
theorem wordsOf_bytesLE8 (x : BitVec 64) : wordsOf (bytesLE 8 x) = [x] := by
  simpa using wordsOf_bytesLE 1 x
theorem chainInput_length (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) : (V3.chainInput index coord child chain step a b c value).length = 64 := by
  unfold V3.chainInput
  split <;> simp [SphincsSecurity.bytesLE_length]
/-- Witness stack: the eight words of an FTS step input, G chains (1, 3) `value | header | a | c`, F chains
`a | header | c | value`. -/
theorem wordsOf_chainInput (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) : wordsOf (V3.chainInput index coord child chain step a b c value) =
      if ClaudeWCT.WCT9.ftsIsG chain then
        [value.extractLsb' 0 64, value.extractLsb' 64 64,
         BitVec.ofNat 64 (V3.chainLow index coord child chain step), b,
         a.extractLsb' 0 64, a.extractLsb' 64 64,
         c.extractLsb' 0 64, c.extractLsb' 64 64]
      else
        [a.extractLsb' 0 64, a.extractLsb' 64 64,
         BitVec.ofNat 64 (V3.chainLow index coord child chain step), b,
         c.extractLsb' 0 64, c.extractLsb' 64 64,
         value.extractLsb' 0 64, value.extractLsb' 64 64] := by
  unfold V3.chainInput
  by_cases hG : ClaudeWCT.WCT9.ftsIsG chain = true
  all_goals first | rw [if_pos hG, if_pos hG] | rw [if_neg hG, if_neg hG]
  all_goals
    rw [wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length]),
      wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length]),
      wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length]),
      wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length])]
    rw [wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE8, wordsOf_bytesLE8]
    rfl
end W9Machine
end
-- ==== merged from W9Drv_GateDefs ====
section

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
abbrev idxOf (a : HashOutput) : Nat := ClaudeWCT.WCT9.digestIndex a
def DigestAt (a : HashOutput) (u : MachineState) : Prop :=
  ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (8 * k)) = a.extractLsb' (64 * k) 64
def dataBase7 : Nat := 0xffbde0
def stackBase7 : Nat := dataBase7
def rankPad : Word := 0x006000c000060000
structure HeaderBank (u : MachineState) : Prop where
  top : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
    BitVec.ofNat 64 (topWords.getD k 0)
  top8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21328
structure SetupMask (u : MachineState) : Prop where
  rankPadAt : u.getMem (BitVec.ofNat 64 (stackBase7 + 48)) = rankPad
  child : u.getMem (BitVec.ofNat 64 (dataBase7 + 368)) = BitVec.ofNat 64 0xf1b00
  jt : u.getMem (BitVec.ofNat 64 (dataBase7 + 376)) = BitVec.ofNat 64 0xfff00
  coord : u.getMem (BitVec.ofNat 64 (dataBase7 + 464)) = BitVec.ofNat 64 10992
  gate : u.getMem (BitVec.ofNat 64 (dataBase7 + 352)) = BitVec.ofNat 64 0x1524000000000000
  d0 : u.getMem (BitVec.ofNat 64 dataBase7) = BitVec.ofNat 64 0xfff
structure ForestData (u : MachineState) : Prop where
  /-- Campaign T51: verify data word 2 (bytes 16..23) is the r6 field mask 0xFF00 (only propagated here). -/
  zero0 : u.getMem (BitVec.ofNat 64 (dataBase7 + 16)) = BitVec.ofNat 64 0xFF00
  zero1 : u.getMem (BitVec.ofNat 64 (dataBase7 + 24)) = 0
  header : u.getMem (BitVec.ofNat 64 (dataBase7 + 32)) = BitVec.ofNat 64 0xf01
structure GatePre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 4
  glob : Glob [(.x5, 0)] w pk u
  len64 : u.getReg .x11 = 64
  forest : ForestData u
  digest : DigestAt a u
  bank : HeaderBank u
  wit : Orig w (fun o => o ≠ 22000) u
  setupMask : SetupMask u
  sp : u.getReg .x2 = BitVec.ofNat 64 stackBase7
end W9Drv

namespace W9Drv.SharedGate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
structure SetupMask (u : MachineState) : Prop where
  rankPadAt : u.getMem (BitVec.ofNat 64 (stackBase7 + 48)) = BitVec.ofNat 64 0x1801801800000
  child : u.getMem (BitVec.ofNat 64 (dataBase7 + 368)) = BitVec.ofNat 64 0xf1b00
  jt : u.getMem (BitVec.ofNat 64 (dataBase7 + 376)) = BitVec.ofNat 64 0xfff00
  coord : u.getMem (BitVec.ofNat 64 (dataBase7 + 464)) = BitVec.ofNat 64 10992
  gate : u.getMem (BitVec.ofNat 64 (dataBase7 + 352)) = BitVec.ofNat 64 (791 * 2^50)
  d0 : u.getMem (BitVec.ofNat 64 dataBase7) = BitVec.ofNat 64 0xfff
  aTable : u.getMem (BitVec.ofNat 64 (dataBase7 + 56)) = BitVec.ofNat 64 0xe3300
  singleton : u.getMem (BitVec.ofNat 64 (dataBase7 + 64)) = BitVec.ofNat 64 0xe7400
structure Pre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState) : Prop where
  pc : u.pc = pcOf 4
  glob : Glob [(.x5, 0)] w pk u
  len64 : u.getReg .x11 = 64
  forest : ForestData u
  digest : DigestAt a u
  bank : HeaderBank u
  wit : Orig w (fun o => o ≠ 22000) u
  setupMask : SetupMask u
  sp : u.getReg .x2 = BitVec.ofNat 64 stackBase7
end W9Drv.SharedGate
end
-- ==== merged from W9Machine_WctNestView ====
section

/-!
Nested FTS (r1-1): the witness view of one coordinate.

Tree `n - 1` hands its computed top node to region `n` (the leaf pad or the level-5 Z slot, with junk on the header
in front of it), and the verifier reads tree `n`'s pads from memory. The chain and child contracts are stated for a
witness `w`; for coordinate `n` they are used with `viewW w n u`, the witness whose eight hand-off words of region
`n` are replaced by the memory of `u`. Everything else is the witness itself.
-/

set_option autoImplicit false
namespace W9Machine.V3
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3 (Digest M shortHash)

def setW64 {n : Nat} (w : BitVec n) (off : Nat) (x : BitVec 64) : BitVec n :=
  w ^^^ (((w.extractLsb' off 64) ^^^ x).setWidth n <<< off)

theorem extract_setW64 {n : Nat} (w : BitVec n) (off o : Nat) (x : BitVec 64) (hoff : off + 64 ≤ n)
    (ho : o + 64 ≤ n) (hdis : o = off ∨ o + 64 ≤ off ∨ off + 64 ≤ o) :
    (setW64 w off x).extractLsb' o 64 = if o = off then x else w.extractLsb' o 64 := by
  unfold setW64
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  split
  · subst o
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    have h1 : off + i < n := by omega
    simp only [h1, show ¬ (off + i < off) by omega, show off + i - off = i by omega, hi, show i < n by omega,
      decide_true, Bool.true_and]
    cases w.getLsbD (off + i) <;> cases x.getLsbD i <;> simp
  · rename_i hne
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    have h1 : o + i < n := by omega
    by_cases hlt : o + i < off
    · simp [h1, hlt]
    · have h2 : ¬ (o + i - off < 64) := by omega
      simp [h1, hlt, h2]
      rw [BitVec.getLsbD_of_ge x (o + i - off) (by omega)]
      simp

theorem extract128_of_halves {n : Nat} (v : BitVec n) (d : BitVec 128) (b : Nat)
    (h0 : v.extractLsb' b 64 = d.extractLsb' 0 64) (h1 : v.extractLsb' (b + 64) 64 = d.extractLsb' 64 64) :
    v.extractLsb' b 128 = d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hl : i < 64
  · have := congrArg (fun x => x.getLsbD i) h0
    simp only [BitVec.getLsbD_extractLsb', hl, decide_true, Bool.true_and, Nat.zero_add] at this
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact this
  · have := congrArg (fun x => x.getLsbD (i - 64)) h1
    simp only [BitVec.getLsbD_extractLsb', show i - 64 < 64 by omega, decide_true, Bool.true_and] at this
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    rw [show b + i = b + 64 + (i - 64) by omega, this, show 64 + (i - 64) = i by omega]

theorem extract128_eq {n : Nat} (v w : BitVec n) (b : Nat)
    (h0 : v.extractLsb' b 64 = w.extractLsb' b 64) (h1 : v.extractLsb' (b + 64) 64 = w.extractLsb' (b + 64) 64) :
    v.extractLsb' b 128 = w.extractLsb' b 128 := by
  apply extract128_of_halves
  · rw [h0]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, show i < 128 by omega]
  · rw [h1]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, show 64 + i < 128 by omega, Nat.add_assoc]

def setWords {n : Nat} (w : BitVec n) (vals : Nat → BitVec 64) : List Nat → BitVec n
  | [] => w
  | o :: os => setW64 (setWords w vals os) o (vals o)

theorem extract_setWords {n : Nat} (w : BitVec n) (vals : Nat → BitVec 64) (os : List Nat) (p : Nat)
    (hos : ∀ o ∈ os, o % 64 = 0 ∧ o + 64 ≤ n) (hp : p % 64 = 0) (hpn : p + 64 ≤ n) :
    (setWords w vals os).extractLsb' p 64 = if p ∈ os then vals p else w.extractLsb' p 64 := by
  induction os with
  | nil => simp [setWords]
  | cons o os ih =>
    have ho := hos o (by simp)
    simp only [setWords]
    rw [extract_setW64 _ _ _ _ ho.2 hpn (by omega)]
    by_cases h : p = o
    · subst h; simp
    · rw [if_neg h, ih (fun o' h' => hos o' (List.mem_cons_of_mem _ h'))]
      simp [h]

/-- Hand-off words of a region: leaf header and pad (`656..688`), level-5 header and Z slot (`800..832`). -/
def handSlots : List Nat := [656, 664, 672, 680, 800, 808, 816, 824]
def isHand (o : Nat) : Prop := (656 ≤ o ∧ o < 688) ∨ (800 ≤ o ∧ o < 832)
instance (o : Nat) : Decidable (isHand o) := by unfold isHand; infer_instance
theorem mem_handSlots {o : Nat} (h8 : o % 8 = 0) : o ∈ handSlots ↔ isHand o := by
  unfold handSlots isHand
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega
def handBits (n : Nat) : List Nat := handSlots.map fun o => 8 * (regionOffset n + o)
/-- The witness seen by coordinate `n` at state `u`: region `n`'s hand-off words read from memory. -/
def viewW (w : WBytes) (n : Nat) (u : MachineState) : WBytes :=
  setWords w (fun b => u.getMem (BitVec.ofNat 64 (0x1020 + b / 8))) (handBits n)

theorem regionOffset_mod (n : Nat) : regionOffset n % 8 = 0 := by unfold regionOffset; omega
theorem regionOffset_le (n : Nat) : regionOffset n ≤ 6864 := by unfold regionOffset; omega

/-- A 64-bit witness word of the view: memory on region `n`'s hand-off words, the witness elsewhere. -/
theorem view_word (w : WBytes) (n : Nat) (u : MachineState) (p : Nat) (hp : p % 8 = 0) (hpn : p + 8 ≤ 22012) :
    (viewW w n u).extractLsb' (8 * p) 64 =
      if regionOffset n ≤ p ∧ isHand (p - regionOffset n) then u.getMem (BitVec.ofNat 64 (0x1020 + p))
      else w.extractLsb' (8 * p) 64 := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold viewW
  rw [extract_setWords _ _ _ _ ?_ (by omega) (by omega)]
  · have hmem : 8 * p ∈ handBits n ↔ regionOffset n ≤ p ∧ isHand (p - regionOffset n) := by
      unfold handBits
      simp only [List.mem_map]
      constructor
      · rintro ⟨o, ho, he⟩
        have h8 : o % 8 = 0 := by unfold handSlots at ho; simp at ho; omega
        have hh := (mem_handSlots h8).mp ho
        refine ⟨by omega, ?_⟩
        rw [show p - regionOffset n = o by omega]; exact hh
      · rintro ⟨hle, hh⟩
        refine ⟨p - regionOffset n, (mem_handSlots (by omega)).mpr hh, by omega⟩
    by_cases h : regionOffset n ≤ p ∧ isHand (p - regionOffset n)
    · rw [if_pos (hmem.mpr h), if_pos h, show 8 * p / 8 = p by omega]
    · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h]
  · intro o ho
    unfold handBits handSlots at ho
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    omega

/-- Outside region `n`'s hand-off words the view is the witness. -/
theorem view_dig (w : WBytes) (n : Nat) (u : MachineState) (off : Nat) (h8 : off % 8 = 0)
    (hb : off + 16 ≤ 22012)
    (h0 : ¬ (regionOffset n ≤ off ∧ isHand (off - regionOffset n)))
    (h1 : ¬ (regionOffset n ≤ off + 8 ∧ isHand (off + 8 - regionOffset n))) :
    wdig (viewW w n u) off = wdig w off := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_eq
  · rw [view_word w n u off h8 (by omega), if_neg h0]
  · rw [show 8 * off + 64 = 8 * (off + 8) by omega, view_word w n u (off + 8) (by omega) (by omega), if_neg h1]

/-- On a hand-off slot pair the view holds the memory digest. -/
theorem view_dig_hand (w : WBytes) (n : Nat) (u : MachineState) (o : Nat) (ho : o = 672 ∨ o = 816) (hn : n ≤ 8)
    (d : Digest) (hd : DigAt u (0x1020 + regionOffset n + o) d) :
    wdig (viewW w n u) (regionOffset n + o) = d := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_of_halves
  · rw [view_word w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.1, Nat.add_assoc]
  · rw [show 8 * (regionOffset n + o) + 64 = 8 * (regionOffset n + o + 8) by omega,
      view_word w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.2]
    congr 2
    omega

theorem child_low_bounds : ∀ j : Fin 128, ∀ l : Fin 5,
    sibOff j.val l.val + 16 ≤ 352 ∧ padOff j.val l.val + 16 ≤ 352 ∧ blkOff j.val l.val + 32 ≤ 352 ∧
    sibOff j.val l.val % 8 = 0 ∧ padOff j.val l.val % 8 = 0 ∧ blkOff j.val l.val % 8 = 0 := by
  decide +kernel

theorem view_dig_low (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (c : Nat) (hc8 : c % 8 = 0)
    (hc : c + 16 ≤ 656 ∨ (688 ≤ c ∧ c + 16 ≤ 800) ∨ (832 ≤ c ∧ c + 16 ≤ 848)) :
    wdig (viewW w n u) (regionOffset n + c) = wdig w (regionOffset n + c) := by
  have hr := regionOffset_mod n
  have hrl : regionOffset n ≤ 6864 := regionOffset_le n
  apply view_dig w n u _ (by omega) (by omega)
  · intro h; unfold isHand at h; omega
  · intro h; unfold isHand at h; omega

theorem sibling_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (l : Nat) :
    sibling (viewW w n u) n j.val l = sibling w n j.val l := by
  unfold sibling
  by_cases hl : l < 5
  · have hb := child_low_bounds j ⟨l, hl⟩
    simp only [Fin.val_mk] at hb
    exact view_dig_low w n u hn _ hb.2.2.2.1 (Or.inl (by omega))
  · have hs : sibOff j.val l = 784 ∨ sibOff j.val l = 832 := by
      unfold sibOff blkOff; rw [if_neg hl]; omega
    rcases hs with hs | hs <;> rw [hs]
    · exact view_dig_low w n u hn _ (by decide) (Or.inr (Or.inl ⟨by decide, by decide⟩))
    · exact view_dig_low w n u hn _ (by decide) (Or.inr (Or.inr ⟨by decide, by decide⟩))

theorem nodePad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (l : Nat) (hl : l < 5) :
    nodePad (viewW w n u) n j.val l = nodePad w n j.val l := by
  have hb := child_low_bounds j ⟨l, hl⟩
  simp only [Fin.val_mk] at hb
  exact view_dig_low w n u hn _ hb.2.2.2.2.1 (Or.inl (by omega))

theorem nodeHPad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (l : Nat) :
    nodeHPad (viewW w n u) n j.val l = nodeHPad w n j.val l := by
  unfold nodeHPad
  by_cases hl : l < 4 ∧ j.val / 2 ^ l % 2 = 1
  · rw [if_pos hl, if_pos hl]
    have hb := child_low_bounds j ⟨l, by omega⟩
    simp only [Fin.val_mk] at hb
    unfold nodeTw
    rw [show regionOffset n + blkOff j.val l + 16 = regionOffset n + (blkOff j.val l + 16) by omega,
      view_dig_low w n u hn _ (by omega) (Or.inl (by omega))]
  · rw [if_neg hl, if_neg hl]

theorem leafPad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (d : Digest)
    (hd : DigAt u (0x1020 + regionOffset n + 672) d) : leafPad (viewW w n u) n = d :=
  view_dig_hand w n u 672 (Or.inl rfl) hn d hd

theorem nodePad5_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (j : Fin 128) (d : Digest)
    (hd : DigAt u (0x1020 + regionOffset n + 816) d) : nodePad (viewW w n u) n j.val 5 = d := by
  unfold nodePad padOff blkOff
  rw [if_neg (by decide), show regionOffset n + (784 + 32) = regionOffset n + 816 by omega]
  exact view_dig_hand w n u 816 (Or.inr rfl) hn d hd

/-- The nested child of coordinate `n` read through the view is the tree with the hand-off pads. -/
theorem childProgram_view (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState) (j : Fin 128)
    (ends : List Digest) (padL padZ : Digest)
    (hL : DigAt u (0x1020 + regionOffset k.val + 672) padL) (hZ : DigAt u (0x1020 + regionOffset k.val + 816) padZ) :
    childProgram (viewW w k.val u) index k j ends = childN w index k j ends padL padZ := by
  have hn : k.val ≤ 8 := by omega
  unfold childProgram childN
  rw [leafPad_view w k.val u hn padL hL, nodePad5_view w k.val u hn j padZ hZ]
  simp only [sibling_view w k.val u hn j, nodeHPad_view w k.val u hn j,
    show List.range 5 = [0, 1, 2, 3, 4] from rfl, List.foldlM_cons, List.foldlM_nil,
    nodePad_view w k.val u hn j 0 (by decide), nodePad_view w k.val u hn j 1 (by decide),
    nodePad_view w k.val u hn j 2 (by decide), nodePad_view w k.val u hn j 3 (by decide),
    nodePad_view w k.val u hn j 4 (by decide)]

/-- Witness stack: every FTS chain block lies in `[320, 656)` of its region. -/
theorem chainOff_bound (t : Nat) (ht : t < 6) :
    320 ≤ ClaudeWCT.W9.T3M.wctChainOff t ∧ ClaudeWCT.W9.T3M.wctChainOff t + 64 ≤ 656 ∧
      ClaudeWCT.W9.T3M.wctChainOff t % 8 = 0 := by
  unfold ClaudeWCT.W9.T3M.wctChainOff
  split_ifs <;> omega
theorem chainField_bound (t : Nat) :
    ClaudeWCT.W9.T3M.wctPad0Off t + 16 ≤ 64 ∧ ClaudeWCT.W9.T3M.wctPad0Off t % 8 = 0 ∧
    ClaudeWCT.W9.T3M.wctPad1Off t + 16 ≤ 64 ∧ ClaudeWCT.W9.T3M.wctPad1Off t % 8 = 0 ∧
    ClaudeWCT.W9.T3M.wctValueOff t + 16 ≤ 64 ∧ ClaudeWCT.W9.T3M.wctValueOff t % 8 = 0 := by
  unfold ClaudeWCT.W9.T3M.wctPad0Off ClaudeWCT.W9.T3M.wctPad1Off ClaudeWCT.W9.T3M.wctValueOff
  cases ClaudeWCT.WCT9.ftsIsG t <;> simp

/-- The chains of coordinate `n` do not read the hand-off words. -/
theorem chainProgram_view (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState) (j : Fin 128)
    (rank : Fin 666) :
    chainProgram (viewW w k.val u) index k j rank = chainProgram w index k j rank := by
  have hn : k.val ≤ 8 := by omega
  unfold chainProgram
  refine congrArg (fun f => List.mapM f (List.finRange 6)) (funext fun t => ?_)
  have ht := t.isLt
  have hb := chainOff_bound t.val ht
  have hf := chainField_bound t.val
  have hA : chainPadA (viewW w k.val u) k.val t.val = chainPadA w k.val t.val := by
    unfold chainPadA chainOffset
    rw [Nat.add_assoc]
    exact view_dig_low w k.val u hn _ (by omega) (Or.inl (by omega))
  have hC : chainPadC (viewW w k.val u) k.val t.val = chainPadC w k.val t.val := by
    unfold chainPadC chainOffset
    rw [Nat.add_assoc]
    exact view_dig_low w k.val u hn _ (by omega) (Or.inl (by omega))
  have hB : chainPadB (viewW w k.val u) k.val t.val = chainPadB w k.val t.val := by
    unfold chainPadB chainOffset
    have hr := regionOffset_mod k.val
    have hrl := regionOffset_le k.val
    rw [view_word w k.val u _ (by omega) (by omega), if_neg (by unfold isHand; omega)]
  have hR : ∀ d, reveal (viewW w k.val u) k.val t.val d = reveal w k.val t.val d := by
    intro d
    unfold reveal
    split
    · unfold leafSlot
      split
      · exact view_dig_low w k.val u hn _ (by decide) (Or.inl (by decide))
      · exact view_dig_low w k.val u hn _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · unfold chainOffset
      rw [Nat.add_assoc]
      exact view_dig_low w k.val u hn _ (by omega) (Or.inl (by omega))
  simp only [hA, hB, hC, hR]

end W9Machine.V3

/-! Incoming pair slots for shared coordinates. Both128-bit outputs may leave
junk in their preceding headers, so the witness view includes those headers. -/
namespace W9Machine.SharedV3
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3 (Digest M shortHash)
open W9Machine.V3 (setWords extract_setWords extract128_eq extract128_of_halves regionOffset
  chainProgram chainPadA chainPadB chainPadC chainOffset reveal leafSlot chainOff_bound chainField_bound)
def handSlots : List Nat := [144, 152, 160, 168, 656, 664, 672, 680]
def isHand (o : Nat) : Prop := (144 ≤ o ∧ o < 176) ∨ (656 ≤ o ∧ o < 688)
instance (o : Nat) : Decidable (isHand o) := by unfold isHand; infer_instance
theorem mem_handSlots {o : Nat} (h8 : o % 8 = 0) : o ∈ handSlots ↔ isHand o := by
  unfold handSlots isHand
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega
def handBits (n : Nat) : List Nat := handSlots.map fun o => 8 * (regionOffset n + o)
/-- The witness seen by coordinate `n` at state `u`: region `n`'s hand-off words read from memory. -/
def viewW (w : WBytes) (n : Nat) (u : MachineState) : WBytes :=
  setWords w (fun b => u.getMem (BitVec.ofNat 64 (0x1020 + b / 8))) (handBits n)

theorem regionOffset_mod (n : Nat) : regionOffset n % 8 = 0 := by unfold regionOffset; omega
theorem regionOffset_le (n : Nat) : regionOffset n ≤ 6864 := by unfold regionOffset; omega

/-- A 64-bit witness word of the view: memory on region `n`'s hand-off words, the witness elsewhere. -/
theorem view_word (w : WBytes) (n : Nat) (u : MachineState) (p : Nat) (hp : p % 8 = 0) (hpn : p + 8 ≤ 22012) :
    (viewW w n u).extractLsb' (8 * p) 64 =
      if regionOffset n ≤ p ∧ isHand (p - regionOffset n) then u.getMem (BitVec.ofNat 64 (0x1020 + p))
      else w.extractLsb' (8 * p) 64 := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold viewW
  rw [extract_setWords _ _ _ _ ?_ (by omega) (by omega)]
  · have hmem : 8 * p ∈ handBits n ↔ regionOffset n ≤ p ∧ isHand (p - regionOffset n) := by
      unfold handBits
      simp only [List.mem_map]
      constructor
      · rintro ⟨o, ho, he⟩
        have h8 : o % 8 = 0 := by unfold handSlots at ho; simp at ho; omega
        have hh := (mem_handSlots h8).mp ho
        refine ⟨by omega, ?_⟩
        rw [show p - regionOffset n = o by omega]; exact hh
      · rintro ⟨hle, hh⟩
        refine ⟨p - regionOffset n, (mem_handSlots (by omega)).mpr hh, by omega⟩
    by_cases h : regionOffset n ≤ p ∧ isHand (p - regionOffset n)
    · rw [if_pos (hmem.mpr h), if_pos h, show 8 * p / 8 = p by omega]
    · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h]
  · intro o ho
    unfold handBits handSlots at ho
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    omega

/-- Outside region `n`'s hand-off words the view is the witness. -/
theorem view_dig (w : WBytes) (n : Nat) (u : MachineState) (off : Nat) (h8 : off % 8 = 0)
    (hb : off + 16 ≤ 22012)
    (h0 : ¬ (regionOffset n ≤ off ∧ isHand (off - regionOffset n)))
    (h1 : ¬ (regionOffset n ≤ off + 8 ∧ isHand (off + 8 - regionOffset n))) :
    wdig (viewW w n u) off = wdig w off := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_eq
  · rw [view_word w n u off h8 (by omega), if_neg h0]
  · rw [show 8 * off + 64 = 8 * (off + 8) by omega, view_word w n u (off + 8) (by omega) (by omega), if_neg h1]

/-- On a hand-off slot pair the view holds the memory digest. -/
theorem view_dig_hand (w : WBytes) (n : Nat) (u : MachineState) (o : Nat) (ho : o = 672 ∨ o = 160) (hn : n ≤ 8)
    (d : Digest) (hd : DigAt u (0x1020 + regionOffset n + o) d) :
    wdig (viewW w n u) (regionOffset n + o) = d := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_of_halves
  · rw [view_word w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.1, Nat.add_assoc]
  · rw [show 8 * (regionOffset n + o) + 64 = 8 * (regionOffset n + o + 8) by omega,
      view_word w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.2]
    congr 2
    omega


def SafeRead (c : Nat) : Prop := c % 8 = 0 ∧
  (c + 16 ≤ 144 ∨ (176 ≤ c ∧ c + 16 ≤ 656) ∨ (688 ≤ c ∧ c + 16 ≤ 848))
instance (c : Nat) : Decidable (SafeRead c) := by unfold SafeRead; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem child_reads : ∀ j : Fin 128, ∀ l : Fin 6,
    SafeRead (sibOff j.val l.val) ∧
    (l.val ≠ 4 → SafeRead (blkOff j.val l.val + 32)) ∧
    (l.val < 4 → SafeRead (blkOff j.val l.val + 16)) := by
  intro j
  fin_cases j <;> decide +kernel

theorem view_dig_safe (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (c : Nat) (hc : SafeRead c) :
    wdig (viewW w n u) (regionOffset n + c) = wdig w (regionOffset n + c) := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  rcases hc with ⟨hc8, hc⟩
  apply view_dig w n u _ (by omega) (by omega)
  · intro h; unfold isHand at h; omega
  · intro h; unfold isHand at h; omega

theorem sibling_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (l : Nat) (hl : l < 6) :
    sibling (viewW w n u) n j.val l = sibling w n j.val l := by
  exact view_dig_safe w n u hn _ (child_reads j ⟨l, hl⟩).1

theorem nodePad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (l : Nat) (hl : l < 6) (hne : l ≠ 4) :
    nodePad (viewW w n u) n j.val l = nodePad w n j.val l := by
  have h := view_dig_safe w n u hn _ ((child_reads j ⟨l, hl⟩).2.1 hne)
  simpa only [nodePad, Nat.add_assoc] using h

theorem nodeHPad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (l : Nat) :
    nodeHPad (viewW w n u) n j.val l = nodeHPad w n j.val l := by
  unfold nodeHPad
  by_cases h : l < 4
  · rw [if_pos h, if_pos h]
    have hd := view_dig_safe w n u hn _ ((child_reads j ⟨l, by omega⟩).2.2 h)
    have he : nodeTw (viewW w n u) n j.val l = nodeTw w n j.val l := by
      simpa only [nodeTw, Nat.add_assoc] using hd
    rw [he]
  · rw [if_neg h, if_neg h]

theorem leafPad_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (d : Digest)
    (hd : DigAt u (0x1020 + regionOffset n + 672) d) : leafPad (viewW w n u) n = d :=
  view_dig_hand w n u 672 (Or.inl rfl) hn d hd

theorem nodePad4_view (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (d : Digest) (hd : DigAt u (0x1020 + regionOffset n + 160) d) :
    nodePad (viewW w n u) n j.val 4 = d := by
  rw [pad4 _ _ _ j.isLt]
  exact view_dig_hand w n u 160 (Or.inr rfl) hn d hd

theorem childInput_view (w : WBytes) (index n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (padR value : Digest) (l : Nat) (hl : l < 6) :
    childInput (viewW w n u) index n j.val padR value l =
      childInput w index n j.val padR value l := by
  unfold childInput
  rw [sibling_view w n u hn j l hl, nodeHPad_view w n u hn j l]
  by_cases h : l = 4
  · simp only [h, ↓reduceIte]
  · rw [if_neg h, if_neg h, nodePad_view w n u hn j l hl h]

theorem childProgram_view (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState)
    (raw : Fin 128) (ends : List Digest) (padL padR : Digest)
    (hL : DigAt u (0x1020 + regionOffset k.val + 672) padL)
    (hR : DigAt u (0x1020 + regionOffset k.val + 160) padR) :
    childProgram (viewW w k.val u) index k raw ends = childN w index k raw ends padL padR := by
  have hn : k.val ≤ 8 := by omega
  let j : Fin 128 := ⟨physical k.val raw.val, physical_lt _ _ raw.isLt⟩
  unfold childProgram
  rw [leafPad_view w k.val u hn padL hL, nodePad4_view w k.val u hn j padR hR]
  have hi (l : Nat) (hl : l < 6) (value : Digest) :
      childInput (viewW w k.val u) index k.val (physical k.val raw.val) padR value l =
        childInput w index k.val (physical k.val raw.val) padR value l :=
    childInput_view w index k.val u hn j padR value l hl
  unfold childN
  rcases lastLevel_cases k.val with hh | hh
  all_goals simp only [hh, show List.range 4 = [0,1,2,3] from rfl,
    show List.range 5 = [0,1,2,3,4] from rfl, List.foldlM_cons, List.foldlM_nil,
    hi 0 (by decide), hi 1 (by decide), hi 2 (by decide), hi 3 (by decide),
    hi 4 (by decide), hi 5 (by decide)]

theorem chainProgram_view (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState) (j : Fin 128)
    (rank : Fin 666) :
    chainProgram (viewW w k.val u) index k j rank = chainProgram w index k j rank := by
  have hn : k.val ≤ 8 := by omega
  unfold chainProgram
  refine congrArg (fun f => List.mapM f (List.finRange 6)) (funext fun t => ?_)
  have ht := t.isLt
  have hb := chainOff_bound t.val ht
  have hf := chainField_bound t.val
  have hA : chainPadA (viewW w k.val u) k.val t.val = chainPadA w k.val t.val := by
    unfold chainPadA chainOffset
    rw [Nat.add_assoc]
    exact view_dig_safe w k.val u hn _ (by unfold SafeRead; omega)
  have hC : chainPadC (viewW w k.val u) k.val t.val = chainPadC w k.val t.val := by
    unfold chainPadC chainOffset
    rw [Nat.add_assoc]
    exact view_dig_safe w k.val u hn _ (by unfold SafeRead; omega)
  have hB : chainPadB (viewW w k.val u) k.val t.val = chainPadB w k.val t.val := by
    unfold chainPadB chainOffset
    have hr := regionOffset_mod k.val
    have hrl := regionOffset_le k.val
    rw [view_word w k.val u _ (by omega) (by omega), if_neg (by unfold isHand; omega)]
  have hR : ∀ d, reveal (viewW w k.val u) k.val t.val d = reveal w k.val t.val d := by
    intro d
    unfold reveal
    split
    · unfold leafSlot
      split
      · exact view_dig_safe w k.val u hn _ (by decide)
      · exact view_dig_safe w k.val u hn _ (by unfold SafeRead; omega)
    · unfold chainOffset
      rw [Nat.add_assoc]
      exact view_dig_safe w k.val u hn _ (by unfold SafeRead; omega)
  simp only [hA, hB, hC, hR]


end W9Machine.SharedV3

namespace W9Machine.SharedV3
/-! Pairing stage 1 (pair1-expand, shared-file change): view lemmas for an arbitrary witness base `B` (verify: `0x1020`;
expand's FTS initial phase: `0x520`). The unsuffixed declarations above are unchanged; `viewWB 0x1020 = viewW`. -/
variable (B : Nat)
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3 (Digest M shortHash)
open W9Machine.V3 (setWords extract_setWords extract128_eq extract128_of_halves regionOffset
  chainProgram chainPadA chainPadB chainPadC chainOffset reveal leafSlot chainOff_bound chainField_bound)
/-- The witness seen by coordinate `n` at state `u`: region `n`'s hand-off words read from memory. -/
def viewWB (w : WBytes) (n : Nat) (u : MachineState) : WBytes :=
  setWords w (fun b => u.getMem (BitVec.ofNat 64 (B + b / 8))) (handBits n)

/-- A 64-bit witness word of the view: memory on region `n`'s hand-off words, the witness elsewhere. -/
theorem view_wordB (w : WBytes) (n : Nat) (u : MachineState) (p : Nat) (hp : p % 8 = 0) (hpn : p + 8 ≤ 22012) :
    ((viewWB B) w n u).extractLsb' (8 * p) 64 =
      if regionOffset n ≤ p ∧ isHand (p - regionOffset n) then u.getMem (BitVec.ofNat 64 (B + p))
      else w.extractLsb' (8 * p) 64 := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold viewWB
  rw [extract_setWords _ _ _ _ ?_ (by omega) (by omega)]
  · have hmem : 8 * p ∈ handBits n ↔ regionOffset n ≤ p ∧ isHand (p - regionOffset n) := by
      unfold handBits
      simp only [List.mem_map]
      constructor
      · rintro ⟨o, ho, he⟩
        have h8 : o % 8 = 0 := by unfold handSlots at ho; simp at ho; omega
        have hh := (mem_handSlots h8).mp ho
        refine ⟨by omega, ?_⟩
        rw [show p - regionOffset n = o by omega]; exact hh
      · rintro ⟨hle, hh⟩
        refine ⟨p - regionOffset n, (mem_handSlots (by omega)).mpr hh, by omega⟩
    by_cases h : regionOffset n ≤ p ∧ isHand (p - regionOffset n)
    · rw [if_pos (hmem.mpr h), if_pos h, show 8 * p / 8 = p by omega]
    · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h]
  · intro o ho
    unfold handBits handSlots at ho
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    omega

/-- Outside region `n`'s hand-off words the view is the witness. -/
theorem view_digB (w : WBytes) (n : Nat) (u : MachineState) (off : Nat) (h8 : off % 8 = 0)
    (hb : off + 16 ≤ 22012)
    (h0 : ¬ (regionOffset n ≤ off ∧ isHand (off - regionOffset n)))
    (h1 : ¬ (regionOffset n ≤ off + 8 ∧ isHand (off + 8 - regionOffset n))) :
    wdig ((viewWB B) w n u) off = wdig w off := by
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_eq
  · rw [(view_wordB B) w n u off h8 (by omega), if_neg h0]
  · rw [show 8 * off + 64 = 8 * (off + 8) by omega, (view_wordB B) w n u (off + 8) (by omega) (by omega), if_neg h1]

/-- On a hand-off slot pair the view holds the memory digest. -/
theorem view_dig_handB (w : WBytes) (n : Nat) (u : MachineState) (o : Nat) (ho : o = 672 ∨ o = 160) (hn : n ≤ 8)
    (d : Digest) (hd : DigAt u (B + regionOffset n + o) d) :
    wdig ((viewWB B) w n u) (regionOffset n + o) = d := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  unfold wdig ClaudeWCT.W9.T3M.wdig
  apply extract128_of_halves
  · rw [(view_wordB B) w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.1, Nat.add_assoc]
  · rw [show 8 * (regionOffset n + o) + 64 = 8 * (regionOffset n + o + 8) by omega,
      (view_wordB B) w n u _ (by omega) (by omega), if_pos ⟨by omega, by unfold isHand; omega⟩]
    rw [← hd.2]
    congr 2
    omega


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem view_dig_safeB (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (c : Nat) (hc : SafeRead c) :
    wdig ((viewWB B) w n u) (regionOffset n + c) = wdig w (regionOffset n + c) := by
  have hr := regionOffset_mod n
  have hrl := regionOffset_le n
  rcases hc with ⟨hc8, hc⟩
  apply (view_digB B) w n u _ (by omega) (by omega)
  · intro h; unfold isHand at h; omega
  · intro h; unfold isHand at h; omega

theorem sibling_viewB (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (l : Nat) (hl : l < 6) :
    sibling ((viewWB B) w n u) n j.val l = sibling w n j.val l := by
  exact (view_dig_safeB B) w n u hn _ (child_reads j ⟨l, hl⟩).1

theorem nodePad_viewB (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (l : Nat) (hl : l < 6) (hne : l ≠ 4) :
    nodePad ((viewWB B) w n u) n j.val l = nodePad w n j.val l := by
  have h := (view_dig_safeB B) w n u hn _ ((child_reads j ⟨l, hl⟩).2.1 hne)
  simpa only [nodePad, Nat.add_assoc] using h

theorem nodeHPad_viewB (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (l : Nat) :
    nodeHPad ((viewWB B) w n u) n j.val l = nodeHPad w n j.val l := by
  unfold nodeHPad
  by_cases h : l < 4
  · rw [if_pos h, if_pos h]
    have hd := (view_dig_safeB B) w n u hn _ ((child_reads j ⟨l, by omega⟩).2.2 h)
    have he : nodeTw ((viewWB B) w n u) n j.val l = nodeTw w n j.val l := by
      simpa only [nodeTw, Nat.add_assoc] using hd
    rw [he]
  · rw [if_neg h, if_neg h]

theorem leafPad_viewB (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8) (d : Digest)
    (hd : DigAt u (B + regionOffset n + 672) d) : leafPad ((viewWB B) w n u) n = d :=
  (view_dig_handB B) w n u 672 (Or.inl rfl) hn d hd

theorem nodePad4_viewB (w : WBytes) (n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (d : Digest) (hd : DigAt u (B + regionOffset n + 160) d) :
    nodePad ((viewWB B) w n u) n j.val 4 = d := by
  rw [pad4 _ _ _ j.isLt]
  exact (view_dig_handB B) w n u 160 (Or.inr rfl) hn d hd

theorem childInput_viewB (w : WBytes) (index n : Nat) (u : MachineState) (hn : n ≤ 8)
    (j : Fin 128) (padR value : Digest) (l : Nat) (hl : l < 6) :
    childInput ((viewWB B) w n u) index n j.val padR value l =
      childInput w index n j.val padR value l := by
  unfold childInput
  rw [(sibling_viewB B) w n u hn j l hl, (nodeHPad_viewB B) w n u hn j l]
  by_cases h : l = 4
  · simp only [h, ↓reduceIte]
  · rw [if_neg h, if_neg h, (nodePad_viewB B) w n u hn j l hl h]

theorem childProgram_viewB (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState)
    (raw : Fin 128) (ends : List Digest) (padL padR : Digest)
    (hL : DigAt u (B + regionOffset k.val + 672) padL)
    (hR : DigAt u (B + regionOffset k.val + 160) padR) :
    childProgram ((viewWB B) w k.val u) index k raw ends = childN w index k raw ends padL padR := by
  have hn : k.val ≤ 8 := by omega
  let j : Fin 128 := ⟨physical k.val raw.val, physical_lt _ _ raw.isLt⟩
  unfold childProgram
  rw [(leafPad_viewB B) w k.val u hn padL hL, (nodePad4_viewB B) w k.val u hn j padR hR]
  have hi (l : Nat) (hl : l < 6) (value : Digest) :
      childInput ((viewWB B) w k.val u) index k.val (physical k.val raw.val) padR value l =
        childInput w index k.val (physical k.val raw.val) padR value l :=
    (childInput_viewB B) w index k.val u hn j padR value l hl
  unfold childN
  rcases lastLevel_cases k.val with hh | hh
  all_goals simp only [hh, show List.range 4 = [0,1,2,3] from rfl,
    show List.range 5 = [0,1,2,3,4] from rfl, List.foldlM_cons, List.foldlM_nil,
    hi 0 (by decide), hi 1 (by decide), hi 2 (by decide), hi 3 (by decide),
    hi 4 (by decide), hi 5 (by decide)]

theorem chainProgram_viewB (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState) (j : Fin 128)
    (rank : Fin 666) :
    chainProgram ((viewWB B) w k.val u) index k j rank = chainProgram w index k j rank := by
  have hn : k.val ≤ 8 := by omega
  unfold chainProgram
  refine congrArg (fun f => List.mapM f (List.finRange 6)) (funext fun t => ?_)
  have ht := t.isLt
  have hb := chainOff_bound t.val ht
  have hf := chainField_bound t.val
  have hA : chainPadA ((viewWB B) w k.val u) k.val t.val = chainPadA w k.val t.val := by
    unfold chainPadA chainOffset
    rw [Nat.add_assoc]
    exact (view_dig_safeB B) w k.val u hn _ (by unfold SafeRead; omega)
  have hC : chainPadC ((viewWB B) w k.val u) k.val t.val = chainPadC w k.val t.val := by
    unfold chainPadC chainOffset
    rw [Nat.add_assoc]
    exact (view_dig_safeB B) w k.val u hn _ (by unfold SafeRead; omega)
  have hB : chainPadB ((viewWB B) w k.val u) k.val t.val = chainPadB w k.val t.val := by
    unfold chainPadB chainOffset
    have hr := regionOffset_mod k.val
    have hrl := regionOffset_le k.val
    rw [(view_wordB B) w k.val u _ (by omega) (by omega), if_neg (by unfold isHand; omega)]
  have hR : ∀ d, reveal ((viewWB B) w k.val u) k.val t.val d = reveal w k.val t.val d := by
    intro d
    unfold reveal
    split
    · unfold leafSlot
      split
      · exact (view_dig_safeB B) w k.val u hn _ (by decide)
      · exact (view_dig_safeB B) w k.val u hn _ (by unfold SafeRead; omega)
    · unfold chainOffset
      rw [Nat.add_assoc]
      exact (view_dig_safeB B) w k.val u hn _ (by unfold SafeRead; omega)
  simp only [hA, hB, hC, hR]



theorem viewWB_eq (w : WBytes) (n : Nat) (u : MachineState) : viewWB 0x1020 w n u = viewW w n u := rfl
end W9Machine.SharedV3

end
