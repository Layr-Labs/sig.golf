import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopPrefixV6
import SigGolfCandidate.ClaudeWCT_Numerics_V6Budgets

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

#print axioms keygen_moment_v6
end Numeric

end ClaudeWCT.W9.T3.TopMoment
