import SigGolfCandidate.ClaudeWCT_Numerics_N600PriceCanonical
import SigGolfCandidate.Research_V7Composed198Gate
import SigGolfCandidate.ClaudeWCT_WCT9_Cost
import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_Budgets

section
namespace ClaudeWCT.W9.T3.LayerBudget
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Budgets (signingZ signing_z_le EncodingFreshBelow SourceFreshness V_bind_bounded
  post_of_roRun)
open ClaudeWCT.W9.T3.ProducerV5 (producerEncodingDecode)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow layerTrial V_layerCounterSearch bound_layerCounterSearch
  avoids_layerCounterSearch preserves_pairBelow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Envelopes
section AvoidsSupport
open SigGolfCandidate.T3.Freshness (Avoids avoids_pure avoids_bind)
theorem avoids_bind_support {α β : Type} {secret : BitVec 256} {target : HashInput} {program : M α}
    {next : α → M β} (hp : Avoids secret target program)
    (hn : ∀ a ∈ support program, Avoids secret target (next a)) : Avoids secret target (program >>= next) := by
  induction program using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact hn a (by simp)
  | query_bind t mx ih =>
    rw [bind_assoc]
    change AllQueriesSatisfy _ _ at hp ⊢
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    refine ⟨hp.1, fun u => ih u (hp.2 u) fun a ha => hn a ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩
theorem avoids_mapM_mem {α β : Type} {secret : BitVec 256} {target : HashInput} (f : α → M β) :
    ∀ items : List α, (∀ a ∈ items, Avoids secret target (f a)) → Avoids secret target (items.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact avoids_pure secret target _
  | a :: items, h => by
    rw [List.mapM_cons]
    exact avoids_bind (h a List.mem_cons_self) fun _ =>
      avoids_bind (avoids_mapM_mem f items fun b hb => h b (List.mem_cons_of_mem a hb)) fun _ =>
        avoids_pure secret target _
theorem length_of_mem_support_mapM {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [length_of_mem_support_mapM f xs zs hzs]
theorem mem_support_foldlM_inv {α β : Type} (f : α → β → M α) (Inv : Nat → α → Prop)
    (hstep : ∀ k a b, Inv k a → ∀ a' ∈ support (f a b), Inv (k + 1) a') :
    ∀ (xs : List β) (k : Nat) (init : α), Inv k init → ∀ s ∈ support (xs.foldlM f init), Inv (k + xs.length) s
  | [], k, init, hinit, s, hs => by
    rw [List.foldlM_nil] at hs
    simp only [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    simpa using hinit
  | x :: xs, k, init, hinit, s, hs => by
    rw [List.foldlM_cons, mem_support_bind_iff] at hs
    obtain ⟨a, ha, hs⟩ := hs
    have := mem_support_foldlM_inv f Inv hstep xs (k + 1) a (hstep k init x hinit a ha) s hs
    simpa [Nat.add_assoc, Nat.add_comm 1] using this
theorem avoids_foldlM_range'_inv {α : Type} {secret : BitVec 256} {target : HashInput} (f : α → Nat → M α)
    (Inv : Nat → α → Prop) :
    ∀ n s, (∀ k a, s ≤ k → k < s + n → Inv k a →
        Avoids secret target (f a k) ∧ ∀ b ∈ support (f a k), Inv (k + 1) b) →
      ∀ init, Inv s init → Avoids secret target ((List.range' s n).foldlM f init)
  | 0, s, _, init, _ => by rw [List.range'_zero, List.foldlM_nil]; exact avoids_pure secret target init
  | n + 1, s, hstep, init, hinit => by
    rw [List.range'_succ, List.foldlM_cons]
    have h0 := hstep s init le_rfl (by omega) hinit
    exact avoids_bind_support h0.1 fun b hb =>
      avoids_foldlM_range'_inv f Inv n (s + 1)
        (fun k a hk hk' ha => hstep k a (by omega) (by omega) ha) b (h0.2 b hb)
end AvoidsSupport
section Avoid
open SigGolfCandidate.T3.Freshness
variable (secret : BitVec 256) (target : HashInput) (ht : SearchQ target)
include ht
theorem avoids_packedLowerSecret (lay : Layer) (tree q : Nat) (carry : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.packedSecret (ClaudeWCT.WCT9.lowerSeedPair lay tree) q carry) := by
  unfold ClaudeWCT.WCT9.packedSecret ClaudeWCT.WCT9.lowerSeedPair
  split
  · exact avoids_bind (avoids_privatePair secret target ht 0 _ _ _ _ (by decide))
      fun _ => avoids_pure _ _ _
  · exact avoids_pure _ _ _
/-- C2/C3: a half-selecting hash makes the same single query as `shortHash`. -/
theorem avoids_halfHash_of_ne (high : Bool) (input : HashInput) (hne : pad64 input ≠ target) :
    Avoids secret target (ClaudeWCT.WCT9.halfHash high input) := by
  rw [ClaudeWCT.WCT9.halfHash_eq]
  apply avoids_bind
  · exact (allQueriesSatisfy_query_iff _ _).mpr hne
  · intro _; exact avoids_pure _ _ _
theorem avoids_chainW (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.chainW lay tree leaf i start count value) := by
  unfold ClaudeWCT.WCT9.chainW
  apply avoids_foldlM
  intro value step
  apply avoids_halfHash_of_ne secret target ht
  have hh : SigGolfCandidate.T3.QuerySpace.queryHeader (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) =
      SphincsSecurity.bytesLE 16 (chainHeader lay tree leaf i step) := by
    unfold ClaudeWCT.WCT9.chainInputW
    split
    · simpa only [List.append_assoc] using
        SigGolfCandidate.T3.QuerySpace.queryHeader_padded (SphincsSecurity.bytesLE 16 value) (zero16 ++ zero16)
          (by simp [SphincsSecurity.bytesLE_length]) (chainHeader lay tree leaf i step)
    · simpa only [SigGolfCandidate.T3.chainInput, List.append_assoc] using
        SigGolfCandidate.T3.QuerySpace.queryHeader_padded zero16 (zero16 ++ SphincsSecurity.bytesLE 16 value)
          (by simp [zero16]) (chainHeader lay tree leaf i step)
  exact searchQ_ne hh (chainHeader_not_search lay tree leaf i step) ht
theorem avoids_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Avoids secret target (ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ends) := by
  rw [ClaudeWCT.WCT9.lowerLeafHash_eq]
  unfold ClaudeWCT.WCT9.lowerHash
  apply avoids_halfHash_of_ne secret target ht
  exact searchQ_ne (SigGolfCandidate.T3.QuerySpace.queryHeader_leafInput ..) (leafTweak_not_search lay tree leaf) ht
omit ht in
/-- C2: the packed lower node word has marker `128 + heap` (heap < 128), so it is no search header. -/
theorem lowerTweak_not_search (lay tree heap : Nat) (hh : heap < 128) :
    ¬ SearchHdr (ClaudeWCT.WCT9.lowerTweak lay tree heap) := by
  have hm : tweakMarker (ClaudeWCT.WCT9.lowerTweak lay tree heap) = 128 + heap := by
    unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
    rw [append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat, hyperWord_toNat]
    omega
  unfold SearchHdr RowHdr; omega
theorem avoids_lowerNodeHash (lay tree heap : Nat) (left right : Digest) (hh : lay ≠ 0 → heap < 128) :
    Avoids secret target (ClaudeWCT.WCT9.lowerNodeHash lay tree heap left right) := by
  unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash
  apply avoids_halfHash_of_ne secret target ht
  have hq : SigGolfCandidate.T3.QuerySpace.queryHeader
      (pad64 (ClaudeWCT.WCT9.merkleNodeInput lay tree heap left right)) =
      SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay tree heap) := by
    simpa only [ClaudeWCT.WCT9.merkleNodeInput, List.append_assoc] using
      (SigGolfCandidate.T3.QuerySpace.queryHeader_padded (SphincsSecurity.bytesLE 16 left)
        (zero16 ++ SphincsSecurity.bytesLE 16 right) (SphincsSecurity.bytesLE_length ..)
        (ClaudeWCT.WCT9.merkleTweak lay tree heap))
  refine searchQ_ne hq ?_ ht
  by_cases h0 : lay = 0
  · subst h0
    rw [ClaudeWCT.WCT9.merkleTweak_top]
    exact nodeTweak_not_search 3 0 tree heap (by decide) (fun _ h _ => by omega)
  · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]
    exact lowerTweak_not_search lay tree heap (hh h0)
theorem avoids_lowerCoefs (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    Avoids secret target (ClaudeWCT.WCT9.lowerCoefs lay tree leaf carry) := by
  unfold ClaudeWCT.WCT9.lowerCoefs ClaudeWCT.WCT9.lowerFamCoefs ClaudeWCT.WCT9.lowerSeedPair
  split
  · exact avoids_bind (avoids_bind (avoids_foldlM _ _ _ _ (fun state j =>
      avoids_bind (avoids_privatePair secret target ht 0 _ _ _ _ (by decide)) fun _ => avoids_pure _ _ _) _)
      fun _ => avoids_pure _ _ _) fun _ => avoids_pure _ _ _
  · exact avoids_pure _ _ _
theorem avoids_buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : List Digest) :
    Avoids secret target (ClaudeWCT.WCT9.buildLeafPF lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafPF
  refine avoids_bind ?_ fun cc => ?_
  · exact avoids_lowerCoefs secret target ht _ _ _ _
  rcases cc with ⟨coefs, carry'⟩
  refine avoids_bind (avoids_foldlM _ _ _ _ (fun state i => ?_) _)
    (fun state => avoids_bind (avoids_lowerLeafHash secret target ht _ _ _ _) fun _ => avoids_pure _ _ _)
  exact avoids_bind (avoids_chainW secret target ht _ _ _ _ _ _ _) fun value =>
    avoids_bind (avoids_chainW secret target ht _ _ _ _ _ _ _) fun _ => avoids_pure _ _ _
/-- C2: the lower levels use `lowerLevel` (packed node word, heap < 128 below the root of a height-7 tree). -/
theorem avoids_buildLevel_below (lay tree h level : Nat) (nodes : List Digest) (hlev : level < h) (h1 : 1 ≤ level)
    (h7 : lay ≠ 0 → h ≤ 7) (hlen : nodes.length / 2 ≤ 2 ^ (h - level)) :
    Avoids secret target (ClaudeWCT.WCT9.lowerLevel lay tree h level nodes) := by
  unfold ClaudeWCT.WCT9.lowerLevel
  refine avoids_mapM_mem _ _ fun i hi => avoids_lowerNodeHash secret target ht _ _ _ _ _ fun hl => ?_
  have hi : i < nodes.length / 2 := List.mem_range.mp hi
  have hp : 2 ^ (h - level) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by have := h7 hl; omega)
  have : (2 : Nat) ^ 6 = 64 := by norm_num
  omega
theorem avoids_buildLevelsBelow (lay tree h : Nat) (hh : lay ≠ 0 → h ≤ 7) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) :
    Avoids secret target (ClaudeWCT.WCT9.buildLevelsBelow 3 lay tree h leaves) := by
  unfold ClaudeWCT.WCT9.buildLevelsBelow
  refine avoids_foldlM_range'_inv _ (fun k (levels : List (List Digest)) => levels.length = k ∧
      ∀ j < k, (levels.getD j []).length ≤ 2 ^ (h - j)) (h - 1) 1 ?_ [leaves]
    ⟨rfl, fun j hj => by rw [show j = 0 by omega]; simpa using hlen⟩
  intro k levels hk hk' ⟨hlk, hshape⟩
  have hnodes := hshape (k - 1) (by omega)
  rw [show h - (k - 1) = h - k + 1 by omega, Nat.pow_succ] at hnodes
  refine ⟨avoids_bind (avoids_buildLevel_below secret target ht lay tree h k _ (by omega) (by omega) hh (by omega))
    fun _ => avoids_pure _ _ _, fun b hb => ?_⟩
  rw [mem_support_bind_iff] at hb
  obtain ⟨nodes, hn, hb⟩ := hb
  simp only [support_pure, Set.mem_singleton_iff] at hb
  subst hb
  have hlenN : nodes.length = (levels.getD (k - 1) []).length / 2 := by
    unfold ClaudeWCT.WCT9.lowerLevel at hn
    rw [length_of_mem_support_mapM _ _ _ hn, List.length_range]
  refine ⟨by simp [hlk], fun j hj => ?_⟩
  by_cases hjk : j < k
  · rw [List.getD_append _ _ _ _ (by omega)]
    exact hshape j hjk
  · rw [show j = k by omega, List.getD_append_right _ _ _ _ (by omega), hlk, Nat.sub_self, List.getD_cons_zero,
      hlenN]
    omega
end Avoid
end Envelopes
end ClaudeWCT.W9.T3.LayerBudget
end
section
namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (failMass)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V V_pure V_of_bound)
open SigGolfCandidate.T3.Budgets (signingZ signing_z_le V_bind_bounded post_of_roRun signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow AllSearchesFreshBC digestSearch_preserves_pairBelow
  privateMac_preserves_fresh privateNonce_preserves_fresh)
open SigGolfCandidate.T3.BaseAudit (zU)
open SigGolfCandidate.T3.Cost (bound_privateNonce bound_privateMac)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.T3.Budgets
end

namespace SigGolfCandidate.Research.SharedSigningBudget
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Budgets (V_bind_bounded)
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The forest and retained lower roots consume a fixed budget before the
canonical search. The bound on that search is required only at reached states. -/
theorem V_signFromOutput_fixed (secret : BitVec 256) (z L : ENNReal) (hz : 1 ≤ z)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32)
    (output : HashOutput) (rcache : RCache)
    (hsearch : ∀ forest ∈ support (roRun secret
        (SigGolfCandidate.Research.SharedForest.buildForest (digestIndex output) (SigGolfCandidate.Research.SharedForest.forestSelectionFromOutput output)
          (SigGolfCandidate.Research.SharedForest.forestWordsFromOutput output)) rcache),
      ∀ prepared ∈ support (roRun secret (SigGolfCandidate.Research.SharedForest.prepareRoots (digestIndex output)) forest.2),
      V secret z (SigGolfCandidate.Research.SharedForest.searchPreparedLayers cache (digestIndex output) prepared.1 forest.1.2)
        prepared.2 ≤ L) :
    V secret z (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output) rcache ≤ z ^ 112142 * L := by
  unfold SigGolfCandidate.Research.SharedForest.signFromOutput
  refine (V_bind_bounded secret z _ _ rcache (z ^ 31321) (z ^ 80821 * L)
    (V_of_bound (SigGolfCandidate.Research.SharedForest.bound_buildForest ..) secret z hz rcache) ?_).trans_eq ?_
  · intro forest hforest
    have hp := SigGolfCandidate.Research.SharedForest.bound_prepareRoots (digestIndex output)
    rw [SigGolfCandidate.Research.SharedForest.prepared_roots_cost] at hp
    refine V_bind_bounded secret z _ _ forest.2 (z ^ 80821) L
      (V_of_bound hp secret z hz forest.2) ?_
    intro prepared hprepared
    refine (V_bind_bounded secret z _ _ prepared.2 L 1
      (hsearch forest hforest prepared hprepared) ?_).trans_eq (mul_one L)
    intro layers _
    cases layers.1 <;> simp only [V_pure, le_refl]
  · rw [← mul_assoc, ← pow_add]

/-- The payload adds the private nonce's two compressions. -/
theorem V_signPayload_fixed (secret : BitVec 256) (z D P : ENNReal) (hz : 1 ≤ z)
    (hP : 1 ≤ P) (cache : SigGolfCandidate.T3.Cache) (message : Message) (rcache : RCache)
    (hdigest : ∀ nonce ∈ support (roRun secret (privateNonce message) rcache),
      V secret z (SigGolfCandidate.Research.SharedForest.sharedDigestSearch nonce.1 message 0 digestAttemptLimit) nonce.2 ≤ D)
    (hnext : ∀ nonce ∈ support (roRun secret (privateNonce message) rcache),
      ∀ found ∈ support (roRun secret
        (SigGolfCandidate.Research.SharedForest.sharedDigestSearch nonce.1 message 0 digestAttemptLimit) nonce.2),
      ∀ counter output, found.1 = some (counter, output) →
        V secret z (SigGolfCandidate.Research.SharedForest.signFromOutput cache nonce.1 counter output) found.2 ≤ P) :
    V secret z (SigGolfCandidate.Research.SharedForest.signPayload cache message) rcache ≤ z ^ 2 * (D * P) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine V_bind_bounded secret z _ _ rcache (z ^ 2) (D * P)
    (V_of_bound (bound_privateNonce message) secret z hz rcache) ?_
  intro nonce hnonce
  refine V_bind_bounded secret z _ _ nonce.2 D P (hdigest nonce hnonce) ?_
  intro found hfound
  cases he : found.1 with
  | none => simpa only [V_pure] using hP
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      refine (V_bind_bounded secret z _ _ found.2 P 1
        (hnext nonce hnonce found hfound counter output he) ?_).trans_eq (mul_one P)
      intro result _
      cases result.1 <;> simp only [V_pure, le_refl]

/-- Cache authentication adds two compressions, including the rejecting branch. -/
theorem V_sign_fixed (secret : BitVec 256) (z P : ENNReal) (hz : 1 ≤ z) (hP : 1 ≤ P)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) (rcache : RCache)
    (hpayload : ∀ checked ∈ support (roRun secret (privateMac cache.region) rcache),
      checked.1 = cache.tag → V secret z (SigGolfCandidate.Research.SharedForest.signPayload cache message) checked.2 ≤ P) :
    V secret z (SigGolfCandidate.Research.SharedForest.sign cache message) rcache ≤ z ^ 2 * P := by
  unfold SigGolfCandidate.Research.SharedForest.sign
  refine V_bind_bounded secret z _ _ rcache (z ^ 2) P
    (V_of_bound (bound_privateMac cache.region) secret z hz rcache) ?_
  intro checked hchecked
  split
  · simpa only [V_pure] using hP
  · rename_i h
    exact hpayload checked hchecked (by simpa only [ne_eq, not_not] using h)

/-- The top-signing cost remains inside the search continuation; this identity
matches the numerical certificate's complete fixed-cost exponent. -/
theorem fixed_budget_factor (z D L : ENNReal) :
    z ^ 2 * (z ^ 2 * (D * (z ^ 112142 * (z ^ 180 * L)))) =
      z ^ 112326 * (D * L) := by
  rw [show 112326 = 2 + 2 + 112142 + 180 by decide, pow_add, pow_add, pow_add]
  ac_rfl

end SigGolfCandidate.Research.SharedSigningBudget

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Finite histogram laws allow arbitrary continuation weights. The floor is
an external canonical context and need not be statistically independent of ancestors. -/
theorem acceptedWeight_histogram {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor den : Nat) (weight : Nat → ENNReal)
    (hbound : ∀ answer value, dec answer = some value → credit value < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ value, dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0) :
    acceptedWeight dec (fun value => weight (credit value)) =
      ∑ i : Fin n, if floor ≤ i.val then
        (histogramWeight hist i.val : ENNReal) / den * weight i.val else 0 := by
  rw [acceptedWeight_nat_labels n dec credit weight hbound]
  apply Finset.sum_congr rfl
  intro i _
  rw [hlaw i]
  split_ifs <;> simp

/-- The weighted next row is exactly the integer dot product certified by the
arithmetic packet, divided by the common probability and fixed-point denominators. -/
theorem acceptedWeight_nextMass {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor residual den unit : Nat) (next : Array Nat)
    (hbound : ∀ answer value, dec answer = some value → credit value < n)
    (hhist : ∀ e ∈ hist, e.1 < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ value, dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0) :
    acceptedWeight dec (fun value => (next[residual-credit value]?.getD 0 : ENNReal) / unit) =
      (nextMass hist floor residual next : ENNReal) / (den * unit) := by
  rw [acceptedWeight_histogram n dec credit hist floor den
      (fun c => (next[residual-c]?.getD 0 : ENNReal) / unit) hbound hlaw,
    nextMass_finite hist n floor residual next hhist]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (show (unit : ENNReal) ≠ ∞ by simp))
    (Or.inl (show (den : ENNReal) ≠ ∞ by simp)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_assoc, mul_left_comm, mul_comm]

#print axioms acceptedWeight_histogram
#print axioms acceptedWeight_nextMass
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem acceptedWeight_acceptedMass {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor den : Nat)
    (hbound : ∀ answer value, dec answer = some value → credit value < n)
    (hhist : ∀ e ∈ hist, e.1 < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ value, dec answer = some value ∧ credit value = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0) :
    acceptedWeight dec (fun _ => 1) = (acceptedMass hist floor : ENNReal) / den := by
  rw [acceptedWeight_histogram n dec credit hist floor den (fun _ => 1) hbound hlaw,
    acceptedMass_finite hist n floor hhist]
  simp only [mul_one, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Integer rejection counts exactly complement the selected mass. -/
theorem failMass_of_acceptedMass {β : Type} (dec : HashOutput → Option β) (mass den : Nat)
    (hden : 0 < den) (hmass : mass ≤ den)
    (ha : acceptedWeight dec (fun _ => 1) = (mass : ENNReal) / den) :
    failMass dec = ((den-mass : Nat) : ENNReal) / den := by
  have hm : acceptedWeight dec (fun _ => (1 : ENNReal)) + failMass dec = 1 := by
    have h := uniform_decoder_weight dec (fun _ => (1 : ENNReal)) 1
    have he (answer : HashOutput) : (dec answer).elim (1 : ENNReal) (fun _ => 1) = 1 := by
      cases dec answer <;> rfl
    simp_rw [he] at h
    rw [expectedValue_const (by simp)] at h
    simpa only [mul_one] using h.symm
  rw [ha] at hm
  have hn : (mass : ENNReal)/den + ((den-mass : Nat) : ENNReal)/den = 1 := by
    rw [← ENNReal.add_div, ← Nat.cast_add, Nat.add_sub_of_le hmass]
    exact ENNReal.div_self (by exact_mod_cast hden.ne') (by simp)
  have hfinite : (mass : ENNReal)/den ≠ ∞ := by
    exact ENNReal.div_ne_top (by simp) (by exact_mod_cast hden.ne')
  have hf := ENNReal.eq_sub_of_add_eq hfinite ((add_comm _ _).trans hm)
  have hn' := ENNReal.eq_sub_of_add_eq hfinite ((add_comm _ _).trans hn)
  exact hf.trans hn'.symm

#print axioms acceptedWeight_acceptedMass
#print axioms failMass_of_acceptedMass
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem decoder_recurrence {β : Type} (n : Nat) [NeZero n]
    (dec : HashOutput → Option β) (credit : β → Nat)
    (hist : List (Nat × Nat)) (floor residual den : Nat) (next : Array Nat) (value : Nat)
    (hden : 0 < den)
    (hbound : ∀ answer digits, dec answer = some digits → credit digits < n)
    (hhist : ∀ e ∈ hist, e.1 < n)
    (hlaw : ∀ i : Fin n,
      Pr[fun answer => ∃ digits, dec answer = some digits ∧ credit digits = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ i.val then (histogramWeight hist i.val : ENNReal) / den else 0)
    (hcheck : recurrenceCheck den hist floor residual next value = true) :
    1 ≤ (value : ENNReal) / scale ∧
      ((zNum : ENNReal) / zDen) *
        (acceptedWeight dec (fun digits => (next[residual-credit digits]?.getD 0 : ENNReal) / scale) +
         failMass dec * ((value : ENNReal) / scale)) ≤ (value : ENNReal) / scale := by
  have hs := recurrenceCheck_sound den hist floor residual next value hden hcheck
  have hm : acceptedMass hist floor ≤ den := by
    simp only [recurrenceCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    exact hcheck.1.1.1.2
  rw [acceptedWeight_nextMass n dec credit hist floor residual den scale next hbound hhist hlaw,
    failMass_of_acceptedMass dec (acceptedMass hist floor) den hden hm
      (acceptedWeight_acceptedMass n dec credit hist floor den hbound hhist hlaw)]
  exact hs

#print axioms decoder_recurrence
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
open ClaudeWCT.Numerics ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The path-aware credit of a decoded answer (digits, selected half). -/
def dcredit (lay : Layer) (dl : List Nat × Bool) : Nat := CanonicalPolicy.credit lay dl.2 dl.1

theorem decoder_credit {lay : Layer} {floor : Nat} {answer : HashOutput} {dl : List Nat × Bool}
    (h : decoder lay floor answer = some dl) : floor ≤ dcredit lay dl := by
  obtain ⟨ds, l⟩ := dl
  exact CanonicalPolicy.producerDecodeOut_credit h

private theorem selected_probability_below (lay : Layer) (floor c : Nat) (hc : c < floor) :
    Pr[fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = c |
      ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
  have he : (fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = c) =
      (fun _ : HashOutput => False) := by
    funext answer
    apply propext
    constructor
    · rintro ⟨dl, hd, hr⟩
      have hf := decoder_credit hd
      omega
    · exact False.elim
  rw [he]
  simp

theorem top_decoder_credit_lt {floor : Nat} (hf : 3 ≤ floor) {answer : HashOutput} {dl : List Nat × Bool}
    (h : decoder 0 floor answer = some dl) : dcredit 0 dl < 220 := by
  obtain ⟨ds, l⟩ := dl
  exact producerDecodeAt_top_credit_lt hf (CanonicalPolicy.producerDecodeOut_spec h).2

theorem lower_decoder_credit_lt (lay : Layer) (hl : lay ≠ 0) {floor : Nat} {answer : HashOutput}
    {dl : List Nat × Bool} (h : decoder lay floor answer = some dl) : dcredit lay dl < 128 := by
  obtain ⟨ds, l⟩ := dl
  exact producerDecodeAt_lower_credit_lt lay hl (CanonicalPolicy.producerDecodeOut_spec h).2

/-- The exact selected-credit law of the canonical top search (T51: floor 14, restricted choice, d6b, top zero cap 7). -/
theorem selected_top_probability (c : Fin 220) :
    Pr[fun answer => ∃ dl, decoder 0 14 answer = some dl ∧ dcredit 0 dl = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if 14 ≤ c.val then (histogramWeight ClaudeWCT.Numerics.TopZero.topAcceptedHistogram c.val : ENNReal) / topDen else 0 := by
  by_cases hc : 14 ≤ c.val
  · rw [if_pos hc]
    exact selected_top_histogram_probability c.val hc
  · rw [if_neg hc]
    exact selected_probability_below 0 14 c.val (by omega)

/-- The exact selected-credit law of a canonical lower search (path-aware). -/
theorem selected_lower_probability (lay : Layer) (hl : lay ≠ 0) (floor : Nat) (c : Fin 128) :
    Pr[fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ c.val then (histogramWeight lowerHistogram c.val : ENNReal) / lowerDen else 0 := by
  by_cases hc : floor ≤ c.val
  · rw [if_pos hc]
    have hd (z : Fin 6) (i : Nat) (hi : i<128) :
        SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
          (65536*z.val+128*201+i) =
        (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
          SigGolfResearch.LowerEffectiveCounting.zeros w = z.val ∧
          SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
          SigGolfResearch.LowerEffectiveCounting.score w = i).card := by
      rw [← bits_digit_eq]
      exact CanonicalCounting.lower_digit z.val i hi
    exact selected_lower_histogram_probability hd lower_histogram_checked lay hl floor c.val hc c.isLt
  · rw [if_neg hc]
    exact selected_probability_below lay floor c.val (by omega)

#print axioms selected_top_probability
#print axioms selected_lower_probability
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem acceptedWeight_one_probability {β : Type} (dec : HashOutput → Option β) :
    acceptedWeight dec (fun _ => 1) =
      Pr[fun answer => (dec answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  unfold acceptedWeight
  have he (answer : HashOutput) : (dec answer).elim (0 : ENNReal) (fun _ => 1) =
      if (dec answer).isSome then 1 else 0 := by
    cases dec answer <;> simp
  simp_rw [he]
  exact expectedValue_ite_one _ _

#print axioms acceptedWeight_one_probability
end ClaudeWCT.W9.T3.CanonicalSearch


namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Freshness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 ClaudeWCT.W9.T3.LayerBudget.Envelopes ClaudeWCT.W9.T3.PairRows
open SigGolfCandidate.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

section Avoid
variable (secret : BitVec 256) (target : HashInput) (ht : SearchQ target)
include ht

theorem avoids_chainPrefixes (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids secret target (chainPrefixes lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => exact avoids_pure _ _ _
  | succ count ih =>
      unfold chainPrefixes
      apply avoids_bind
      · -- C3 (#866): a prefix step keeps the half `chainHigh lay i start` (same query input).
        apply avoids_halfHash_of_ne secret target ht
        have hh : queryHeader (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)) =
            bytesLE 16 (chainHeader lay tree leaf i start) := by
          unfold ClaudeWCT.WCT9.chainInputW
          split
          · simpa only [List.append_assoc] using
              queryHeader_padded (bytesLE 16 value) (zero16 ++ zero16) (by simp [bytesLE_length])
                (chainHeader lay tree leaf i start)
          · simpa only [SigGolfCandidate.T3.chainInput, List.append_assoc] using
              queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16])
                (chainHeader lay tree leaf i start)
        exact searchQ_ne hh (chainHeader_not_search lay tree leaf i start) ht
      · intro next
        exact avoids_bind (ih _ _) fun _ => avoids_pure _ _ _

theorem avoids_buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    Avoids secret target (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine avoids_bind ?_ fun cc => ?_
  · exact avoids_lowerCoefs secret target ht _ _ _ _
  · rcases cc with ⟨coefs, carry'⟩
    exact avoids_bind (avoids_mapM _ _ _ _
      (fun i => avoids_chainPrefixes secret target ht _ _ _ _ _ _ _)) fun prefixes =>
      avoids_bind (avoids_lowerLeafHash secret target ht _ _ _ _) fun _ => avoids_pure _ _ _

theorem avoids_buildTreePrefixes (lay : Layer) (tree selected : Nat) :
    Avoids secret target (buildTreePrefixes lay tree selected) := by
  unfold buildTreePrefixes
  refine avoids_bind_support (avoids_foldlM _ _ _ _ (fun state leaf => ?_) _) fun state hs => ?_
  · dsimp only
    split
    · refine avoids_bind (avoids_buildLeafPrefixes secret target ht _ _ _ _) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      exact avoids_pure _ _ _
    · refine avoids_bind (avoids_buildLeafPF secret target ht _ _ _ _ _) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      simp only [pure_bind]
      exact avoids_pure _ _ _
  · have hlen := mem_support_foldlM_inv _
        (fun k (s : List Digest × List (List Digest) × List Digest) => s.1.length = k)
        (fun k a leaf ha a' ha' => by
          dsimp only at ha'
          split_ifs at ha' with hleaf
          all_goals
            rw [mem_support_bind_iff] at ha'
            obtain ⟨⟨⟨root, prefixes⟩, carry⟩, -, ha'⟩ := ha'
            simp only [pure_bind, support_pure, Set.mem_singleton_iff] at ha'
            subst ha'
            simp [ha]) _ 0 _ rfl state hs
    have hh : lay.val ≠ 0 → height lay ≤ 7 := by fin_cases lay <;> decide
    refine avoids_bind (avoids_buildLevelsBelow secret target ht _ _ _ hh _ ?_) fun _ => avoids_pure _ _ _
    simp only [List.length_range, Nat.zero_add] at hlen
    omega

theorem avoids_prepareRoots (index : Nat) : Avoids secret target (prepareRoots index) := by
  unfold prepareRoots
  exact avoids_bind (avoids_buildTreePrefixes secret target ht _ _ _) fun _ =>
    avoids_bind (avoids_buildTreePrefixes secret target ht _ _ _) fun _ =>
      avoids_bind (avoids_buildTreePrefixes secret target ht _ _ _) fun _ => avoids_pure _ _ _
end Avoid

theorem prepareRoots_preserves_rows (secret : BitVec 256) (index stage : Nat)
    (cache : RCache) (hfresh : RowsFreshFrom stage cache) (result : PreparedRoots × RCache)
    (hr : result ∈ support (roRun secret (prepareRoots index) cache)) :
    RowsFreshFrom stage result.2 := by
  intro lay hl tree leaf left right counter hc
  rw [preserves secret _ _ (avoids_prepareRoots secret _ (rowQ_pairTrial ..).searchQ index)
    cache result hr]
  exact hfresh lay hl tree leaf left right counter hc

#print axioms avoids_prepareRoots
#print axioms prepareRoots_preserves_rows
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Budgets (V_bind_bounded)
open ClaudeWCT.WCT9
open CanonicalPolicy
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure SearchEnvelope (z : ENNReal) where
  initial : ENNReal
  one : Nat → ENNReal
  two : Nat → ENNReal
  three : Nat → ENNReal
  initial_ge : 1 ≤ initial
  one_ge : ∀ r, r < 56 → 1 ≤ one r
  two_ge : ∀ r, r < 41 → 1 ≤ two r
  three_ge : ∀ r, r < 22 → 1 ≤ three r
  initial_step : z * (acceptedWeight (decoder 0 14) (fun dl => one (nextResidual 69 0 dl.2 dl.1)) +
    SphincsSecurity.Completeness.failMass (decoder 0 14) * initial) ≤ initial
  one_step : ∀ r, r < 56 → z *
    (acceptedWeight (decoder 1 (threshold 1 r)) (fun dl => two (nextResidual r 1 dl.2 dl.1)) +
     SphincsSecurity.Completeness.failMass (decoder 1 (threshold 1 r)) * one r) ≤ one r
  two_step : ∀ r, r < 41 → z *
    (acceptedWeight (decoder 2 (threshold 2 r)) (fun dl => three (nextResidual r 2 dl.2 dl.1)) +
     SphincsSecurity.Completeness.failMass (decoder 2 (threshold 2 r)) * two r) ≤ two r
  three_step : ∀ r, r < 22 → z *
    (acceptedWeight (decoder 3 (threshold 3 r)) (fun _ => 1) +
     SphincsSecurity.Completeness.failMass (decoder 3 (threshold 3 r)) * three r) ≤ three r

theorem decoder_spec {lay : Layer} {floor : Nat} {answer : HashOutput} {ds : List Nat} {low : Bool}
    (h : decoder lay floor answer = some (ds, low)) :
    producerDecodeAt lay floor low (encodingAnswer lay answer) = some ds :=
  (producerDecodeOut_spec h).2

/-- The actual four searches follow canonical ancestors. Their continuation
weights depend on the remaining path-aware credit, and the retained lower reveals cost no HASH calls. -/
theorem V_searchPreparedLayers (secret : BitVec 256) (z : ENNReal) (hz : 1 ≤ z)
    (E : SearchEnvelope z) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret z (searchPreparedLayers cache index prepared forest) rcache ≤ z^180 * E.initial := by
  have hfactor : 1 ≤ z^180 := one_le_pow₀ hz
  unfold searchPreparedLayers
  simp only [CanonicalPolicy.totalCredit, threshold_top]
  apply V_layerSearch_bind (secret := secret) (z := z) (lay := 0)
    (weight := fun dl => z^180 * E.one (nextResidual 69 0 dl.2 dl.1))
  · intro rc _
    simpa only [V_pure] using one_le_mul hfactor E.initial_ge
  · intro rc hr counter hc answer dl0 hd0
    obtain ⟨ds0, l0⟩ := dl0
    have hd0' := decoder_spec hd0
    have hres1 := accepted_top_residual hd0'
    have hp1 : threshold 1 (nextResidual 69 0 l0 ds0) < 16 :=
      lower_one_floor_lt ⟨nextResidual 69 0 l0 ds0, hres1⟩
    simp only [show ¬ (threshold 1 (nextResidual 69 0 l0 ds0) ≥ 16) by omega, ↓reduceIte]
    apply V_layerSearch_bind (secret := secret) (z := z) (lay := 1)
      (weight := fun dl => z^180 * E.two (nextResidual (nextResidual 69 0 l0 ds0) 1 dl.2 dl.1))
    · intro rc _
      simpa only [V_pure] using one_le_mul hfactor (E.one_ge _ hres1)
    · intro rc hr counter1 hc1 answer1 dl1 hd1
      obtain ⟨ds1, l1⟩ := dl1
      have hd1' := decoder_spec hd1
      have hres2 : nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1 < 41 :=
        accepted_one_residual ⟨nextResidual 69 0 l0 ds0, hres1⟩ hd1'
      have hp2 : threshold 2 (nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1) ≤ 19 :=
        (lower_two_progress ⟨nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1, hres2⟩).1
      simp only [show ¬ (threshold 2 (nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1) ≥ 22) by omega,
        ↓reduceIte]
      apply V_layerSearch_bind (secret := secret) (z := z) (lay := 2)
        (weight := fun dl => z^180 * E.three
          (nextResidual (nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1) 2 dl.2 dl.1))
      · intro rc _
        simpa only [V_pure] using one_le_mul hfactor (E.two_ge _ hres2)
      · intro rc hr counter2 hc2 answer2 dl2 hd2
        obtain ⟨ds2, l2⟩ := dl2
        have hd2' := decoder_spec hd2
        have hres3 : nextResidual (nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1) 2 l2 ds2 < 22 :=
          accepted_two_residual ⟨nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1, hres2⟩ hd2'
        have hp3 := lower_three_progress _ hres3
        simp only [show ¬ (threshold 3
            (nextResidual (nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1) 2 l2 ds2) ≥ 22) by omega,
          ↓reduceIte]
        apply V_layerSearch_bind (secret := secret) (z := z) (lay := 3) (weight := fun _ => z^180)
        · intro rc _
          simpa only [V_pure] using one_le_mul hfactor (E.three_ge _ hres3)
        · intro rc hr counter3 hc3 answer3 dl3 hd3
          obtain ⟨ds3, l3⟩ := dl3
          have hd : SigGolfCandidate.T3.decode 0 (encodingAnswer 0 answer) = some ds0 :=
            (producerDecodeAt_spec hd0').1
          have hds := SigGolfCandidate.T3.decode_length_sum hd
          have hbound := bound_signTop cache (route index 0).1 ds0
            (by exact hds.1)
            (by exact hds.2.le)
          refine (V_bind_bounded secret z _ _ rc (z^180) 1
            (V_of_bound hbound secret z hz rc) ?_).trans_eq (mul_one _)
          intro top _
          simp only [V_pure]
          exact le_rfl
        · simpa only [mul_one] using scaled_step z
            (E.three (nextResidual (nextResidual (nextResidual 69 0 l0 ds0) 1 l1 ds1) 2 l2 ds2))
            (z^180) _ (fun _ => 1) (E.three_step _ hres3)
        · decide
        · exact hr
      · exact scaled_step z _ (z^180) _ _ (E.two_step _ hres2)
      · decide
      · exact hr
    · exact scaled_step z _ (z^180) _ _ (E.one_step _ hres1)
    · decide
    · exact hr
  · exact scaled_step z _ (z^180) _ _ E.initial_step
  · decide
  · exact hfresh

#print axioms V_searchPreparedLayers
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9 CanonicalPolicy
open ClaudeWCT.Numerics.CanonicalCompression ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem acceptedWeight_congr_on {α : Type} (dec : HashOutput → Option α)
    (w v : α → ENNReal) (h : ∀ answer value, dec answer = some value → w value = v value) :
    acceptedWeight dec w = acceptedWeight dec v := by
  unfold acceptedWeight
  congr 1
  funext answer
  cases hd : dec answer with
  | none => rfl
  | some value => exact h answer value hd

/-- Integer continuation rows give the envelope for the actual canonical
source decoder, through its exact selected-credit law (path-aware credits). -/
noncomputable def envelope_of_rows
    (topHist lowerHist : List (Nat × Nat)) (topDen lowerDen : Nat)
    (one two three : Array Nat) (initial : Nat)
    (htopDen : 0 < topDen) (hlowerDen : 0 < lowerDen)
    (htopHist : ∀ e ∈ topHist, e.1 < 220)
    (hlowerHist : ∀ e ∈ lowerHist, e.1 < 128)
    (htopBound : ∀ answer dl, decoder 0 14 answer = some dl → dcredit 0 dl < 220)
    (hlowerBound : ∀ (lay : Layer), lay ≠ 0 → ∀ floor answer dl,
      decoder lay floor answer = some dl → dcredit lay dl < 128)
    (htopLaw : ∀ i : Fin 220,
      Pr[fun answer => ∃ dl, decoder 0 14 answer = some dl ∧ dcredit 0 dl = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if 14 ≤ i.val then (histogramWeight topHist i.val : ENNReal)/topDen else 0)
    (hlowerLaw : ∀ (lay : Layer), lay ≠ 0 → ∀ floor (i : Fin 128),
      Pr[fun answer => ∃ dl, decoder lay floor answer = some dl ∧ dcredit lay dl = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if floor ≤ i.val then (histogramWeight lowerHist i.val : ENNReal)/lowerDen else 0)
    (hinitial : recurrenceCheck topDen topHist 14 69 one initial = true)
    (hone : ∀ r, r < 56 → recurrenceCheck lowerDen lowerHist (threshold 1 r) r two
      (one[r]?.getD 0) = true)
    (htwo : ∀ r, r < 41 → recurrenceCheck lowerDen lowerHist (threshold 2 r) r three
      (two[r]?.getD 0) = true)
    (hthree : ∀ r, r < 22 → recurrenceCheck lowerDen lowerHist (threshold 3 r) r #[scale]
      (three[r]?.getD 0) = true) : SearchEnvelope ((zNum : ENNReal)/zDen) := by
  have h0 := decoder_recurrence 220 (decoder 0 14) (dcredit 0) topHist 14 69 topDen one initial
    htopDen htopBound htopHist htopLaw hinitial
  have h1 (r : Nat) (hr : r < 56) := decoder_recurrence 128 (decoder 1 (threshold 1 r))
    (dcredit 1) lowerHist (threshold 1 r) r lowerDen two (one[r]?.getD 0) hlowerDen
    (hlowerBound 1 (by decide) _) hlowerHist (hlowerLaw 1 (by decide) _) (hone r hr)
  have h2 (r : Nat) (hr : r < 41) := decoder_recurrence 128 (decoder 2 (threshold 2 r))
    (dcredit 2) lowerHist (threshold 2 r) r lowerDen three (two[r]?.getD 0) hlowerDen
    (hlowerBound 2 (by decide) _) hlowerHist (hlowerLaw 2 (by decide) _) (htwo r hr)
  have h3 (r : Nat) (hr : r < 22) := decoder_recurrence 128 (decoder 3 (threshold 3 r))
    (dcredit 3) lowerHist (threshold 3 r) r lowerDen #[scale] (three[r]?.getD 0) hlowerDen
    (hlowerBound 3 (by decide) _) hlowerHist (hlowerLaw 3 (by decide) _) (hthree r hr)
  refine ⟨(initial : ENNReal)/scale,
    (fun r => (one[r]?.getD 0 : ENNReal)/scale),
    (fun r => (two[r]?.getD 0 : ENNReal)/scale),
    (fun r => (three[r]?.getD 0 : ENNReal)/scale),
    h0.1, (fun r hr => (h1 r hr).1), (fun r hr => (h2 r hr).1),
    (fun r hr => (h3 r hr).1), h0.2, (fun r hr => (h1 r hr).2),
    (fun r hr => (h2 r hr).2), ?_⟩
  intro r hr
  have hweight : acceptedWeight (decoder 3 (threshold 3 r))
      (fun dl => (#[scale][r-dcredit 3 dl]?.getD 0 : ENNReal)/scale) =
      acceptedWeight (decoder 3 (threshold 3 r)) (fun _ => 1) := by
    apply acceptedWeight_congr_on
    intro answer dl hd
    have hf := decoder_credit hd
    rw [lower_three_progress r hr] at hf
    rw [Nat.sub_eq_zero_of_le hf]
    change (scale : ENNReal)/scale = 1
    exact ENNReal.div_self (by norm_num [scale]) (by finiteness)
  have h := (h3 r hr).2
  rw [hweight] at h
  exact h

#print axioms envelope_of_rows
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable def SearchEnvelope.mono_z {z z' : ENNReal} (E : SearchEnvelope z) (hz : z' ≤ z) :
    SearchEnvelope z' where
  initial := E.initial
  one := E.one
  two := E.two
  three := E.three
  initial_ge := E.initial_ge
  one_ge := E.one_ge
  two_ge := E.two_ge
  three_ge := E.three_ge
  initial_step := (mul_le_mul' hz le_rfl).trans E.initial_step
  one_step r hr := (mul_le_mul' hz le_rfl).trans (E.one_step r hr)
  two_step r hr := (mul_le_mul' hz le_rfl).trans (E.two_step r hr)
  three_step r hr := (mul_le_mul' hz le_rfl).trans (E.three_step r hr)

theorem signing_z_ratio : SigGolfCandidate.T3.Budgets.signingZ ≤ (zNum : ENNReal)/zDen := by
  refine SigGolfCandidate.T3.Budgets.signing_z_le.trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold zDen; finiteness)).mp
  rw [ENNReal.toReal_ofReal (by norm_num [SigGolfCandidate.T3.BaseAudit.zU]),
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  norm_num [SigGolfCandidate.T3.BaseAudit.zU, zNum, zDen]

#print axioms SearchEnvelope.mono_z
#print axioms signing_z_ratio
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
open ClaudeWCT.Numerics ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem checkRows_at (stage : Nat) (row next : Array Nat) (h : checkRows stage row next = true)
    (r : Nat) (hr : r < row.size) :
    recurrenceCheck lowerDen lowerHistogram (CanonicalPolicy.threshold stage r) r next
      (row[r]?.getD 0) = true := by
  simp only [checkRows, List.all_eq_true] at h
  have he := h r (List.mem_range.mpr hr)
  simpa only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, show (default : Nat) = 0 from rfl] using he

noncomputable def certifiedEnvelope : SearchEnvelope ((zNum : ENNReal)/zDen) :=
  envelope_of_rows ClaudeWCT.Numerics.TopZero.topAcceptedHistogram lowerHistogram topDen lowerDen rowOne rowTwo rowThree ClaudeWCT.Numerics.TopZero.initialBound
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (fun a dl hd => top_decoder_credit_lt (by norm_num) hd)
    (fun lay hl floor a dl hd => lower_decoder_credit_lt lay hl hd)
    selected_top_probability selected_lower_probability
    ClaudeWCT.Numerics.TopZero.initial_checked
    (fun r hr => checkRows_at 1 rowOne rowTwo row_one_checked r (by exact hr))
    (fun r hr => checkRows_at 2 rowTwo rowThree row_two_checked r (by exact hr))
    (fun r hr => checkRows_at 3 rowThree #[scale] row_three_checked r (by exact hr))

theorem certifiedEnvelope_initial : certifiedEnvelope.initial = (ClaudeWCT.Numerics.TopZero.initialBound : ENNReal)/scale := rfl

theorem V_searchPreparedLayers_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (prepared : SigGolfCandidate.Research.SharedForest.PreparedRoots)
    (forest : SigGolfCandidate.Research.SharedForest.PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (SigGolfCandidate.Research.SharedForest.searchPreparedLayers cache index prepared forest) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^180 * ((ClaudeWCT.Numerics.TopZero.initialBound : ENNReal)/scale) := by
  have h := V_searchPreparedLayers secret SigGolfCandidate.T3.Budgets.signingZ
    (SigGolfCandidate.Budget.one_le_zOf _) (certifiedEnvelope.mono_z signing_z_ratio)
    cache index prepared forest rcache hfresh
  exact h

#print axioms certifiedEnvelope
#print axioms V_searchPreparedLayers_certified
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
open ClaudeWCT.Numerics ClaudeWCT.Numerics.CanonicalCompression
open ClaudeWCT.Numerics.CanonicalHistogram
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem top_acceptance :
    Pr[fun a => (decoder 0 14 a).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedMass ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 14 : ENNReal)/topDen := by
  rw [← acceptedWeight_one_probability]
  exact acceptedWeight_acceptedMass 220 (decoder 0 14) (dcredit 0)
    ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 14 topDen
    (fun a dl hd => top_decoder_credit_lt (by norm_num) hd) (by decide +kernel)
    selected_top_probability

theorem lower_acceptance (lay : Layer) (hl : lay≠0) (floor : Nat) :
    Pr[fun a => (decoder lay floor a).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedMass lowerHistogram floor : ENNReal)/lowerDen := by
  rw [← acceptedWeight_one_probability]
  exact acceptedWeight_acceptedMass 128 (decoder lay floor) (dcredit lay)
    lowerHistogram floor lowerDen
    (fun a dl hd => lower_decoder_credit_lt lay hl hd) (by decide +kernel)
    (selected_lower_probability lay hl floor)

theorem ofReal_nat_ratio (n d : Nat) (hd : 0<d) :
    ENNReal.ofReal (((n : ℚ)/d : ℚ) : ℝ) = (n : ENNReal)/d := by
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hd), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

def topFailureRate : ℚ := (acceptedMass ClaudeWCT.Numerics.TopZero.topAcceptedHistogram 14 : ℚ)/topDen
def lowerFailureRate : ℚ := (acceptedMass lowerHistogram 19 : ℚ)/lowerDen
/-- L3 (img-v6 floors up to 21, window `3·2^20`). -/
def lowerThreeFailureRate : ℚ := (acceptedMass lowerHistogram 21 : ℚ)/lowerDen

/-- The top counter window is the single parameter `topSearchLimit` (2^20, top-bytes layer / img-v4). -/
theorem top_failure_rate_440_checked : 0≤topFailureRate ∧ topFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤(topSearchLimit : ℚ)*topFailureRate := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simp only [topSearchLimit, Nat.cast_pow, Nat.cast_ofNat]
  decide +kernel

theorem lower_failure_rate_440_checked : 0≤lowerFailureRate ∧ lowerFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤2^21*lowerFailureRate := by decide +kernel

theorem lower_three_failure_rate_440_checked : 0≤lowerThreeFailureRate ∧ lowerThreeFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤(3*2^20)*lowerThreeFailureRate := by decide +kernel

/-- Top search window `topSearchLimit` (= 2^20). -/
theorem top_failure_power_440 : failMass (decoder 0 14)^topSearchLimit≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ topFailureRate
    topSearchLimit 440 top_failure_rate_440_checked.1 top_failure_rate_440_checked.2.1 _ top_failure_rate_440_checked.2.2
  rw [top_acceptance, topFailureRate, ofReal_nat_ratio _ _ (by decide)]

theorem lower_failure_power_440 (lay : Layer) (hl : lay≠0) (floor : Nat) (hf : floor≤19) :
    failMass (decoder lay floor)^(2^21)≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ lowerFailureRate
    (2^21) 440 lower_failure_rate_440_checked.1 lower_failure_rate_440_checked.2.1 _ lower_failure_rate_440_checked.2.2
  rw [lower_acceptance lay hl floor, lowerFailureRate, ofReal_nat_ratio _ _ (by decide)]
  gcongr
  exact_mod_cast acceptedMass_antitone lowerHistogram hf

/-- L3: floors up to 21 within the `3·2^20` window. -/
theorem lower_three_failure_power_440 (floor : Nat) (hf : floor≤21) :
    failMass (decoder 3 floor)^(3*2^20)≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ lowerThreeFailureRate
    (3*2^20) 440 lower_three_failure_rate_440_checked.1 lower_three_failure_rate_440_checked.2.1 _
    (by exact_mod_cast lower_three_failure_rate_440_checked.2.2)
  rw [lower_acceptance 3 (by decide) floor, lowerThreeFailureRate, ofReal_nat_ratio _ _ (by decide)]
  gcongr
  exact_mod_cast acceptedMass_antitone lowerHistogram hf

#print axioms top_failure_power_440
#print axioms lower_failure_power_440
#print axioms lower_three_failure_power_440
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Budgets (zeroAnswers finite_family_failure_le ofReal_inv_two_pow)
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

/-- A canonical encoding context: the routed family and the floor (img-v6: the top floor is fixed at 14; L1/L2
floors are below 20 (clipped at 19), L3 floors below 22). -/
abbrev EncodingContext := EncodingFamilyBC × Fin 22

def contextFloor (context : EncodingContext) : Nat :=
  if context.1.1=0 then 14 else if context.1.1=3 then context.2.val else min context.2.val 19

def ContextFailed (context : EncodingContext) (answers : Correctness.Answers) : Prop :=
  evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt context.1.1 (contextFloor context)
    (routedTree context.1.1 context.1.2.1) (routedLeaf context.1.1 context.1.2.1)
    (.pair context.1.2.2.1 context.1.2.2.2) 0 (searchLimit context.1.1))=none

theorem encodingContext_card_le : Fintype.card EncodingContext ≤ 2^301 := by
  change Fintype.card (EncodingFamilyBC × Fin 22) ≤ 2^301
  rw [Fintype.card_prod,encodingFamilyBC_card,Fintype.card_fin]
  exact (Nat.mul_le_mul_left _ (show 22≤2^11 by norm_num)).trans_eq (by rw [←pow_add])

theorem context_table_failure (context : EncodingContext) :
    Pr[fun outputs => ContextFailed context (Presampling.tableAnswers outputs zeroAnswers) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2:ENNReal)^440 := by
  unfold ContextFailed
  rw [Presampling.Canonical.search_table_failure _ (Presampling.searchLimit_le_rows _) ]
  by_cases hl : context.1.1=0
  · simpa only [contextFloor,hl,if_pos,searchLimit_top] using top_failure_power_440
  · by_cases h3 : context.1.1=3
    · have hf : context.2.val≤21 := by omega
      have hlow := lower_three_failure_power_440 context.2.val hf
      simp only [contextFloor,hl,h3,if_false,if_true]
      have hs : searchLimit (3 : Layer) = 3*2^20 := searchLimit_values.2.2.2
      rw [hs]
      exact hlow
    · have hf : min context.2.val 19≤19 := Nat.min_le_right _ _
      have hlow := lower_failure_power_440 context.1.1 hl (min context.2.val 19) hf
      simp only [contextFloor,hl,h3,if_false]
      refine le_trans ?_ hlow
      have hone : failMass (decoder context.1.1 (min context.2.val 19))≤1 := by
        rw [failMass_eq_probEvent]
        exact probEvent_le_one
      exact pow_le_pow_right_of_le_one' hone
        (by simpa only [lowerSearchLimit] using searchLimit_lower hl)
theorem context_family_failure :
    Pr[fun outputs => ∃ context, ContextFailed context (Presampling.tableAnswers outputs zeroAnswers) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ (2:ENNReal)^301*(1/(2:ENNReal)^440) := by
  have h := finite_family_failure_le ($ᵗ (SearchKey → HashOutput) : ProbComp _)
    (fun context outputs => ContextFailed context (Presampling.tableAnswers outputs zeroAnswers))
    (1/(2:ENNReal)^440) context_table_failure
  exact h.trans (mul_le_mul' (by exact_mod_cast encodingContext_card_le) le_rfl)

theorem completeness_union_arithmetic :
    (2:ENNReal)^256*(1/(2:ENNReal)^400)+(2:ENNReal)^301*(1/(2:ENNReal)^440)
      ≤ 1/(2:ENNReal)^138 := by
  have hr : (2:ℝ)^256*(1/(2:ℝ)^400)+(2:ℝ)^301*(1/(2:ℝ)^440)≤1/(2:ℝ)^138 := by
    set_option exponentiation.threshold 1024 in norm_num
  have h := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)] at h
  simpa only [ENNReal.ofReal_pow (show 0≤(2:ℝ) by norm_num),ENNReal.ofReal_ofNat,
    ofReal_inv_two_pow] using h

theorem all_search_failure_small {α ι : Type} [Fintype ι] (law : ProbComp α)
    (digestFailed : ι → α → Prop) (encodingFailed : EncodingContext → α → Prop)
    (hι : Fintype.card ι≤2^256)
    (hd : ∀ i, Pr[digestFailed i | law]≤1/(2:ENNReal)^400)
    (he : ∀ context, Pr[encodingFailed context | law]≤1/(2:ENNReal)^440) :
    Pr[fun value => (∃ i, digestFailed i value) ∨ (∃ context, encodingFailed context value) | law]
      ≤1/(2:ENNReal)^138 := by
  have hd' := finite_family_failure_le law digestFailed _ hd
  have he' := finite_family_failure_le law encodingFailed _ he
  have hι' : (Fintype.card ι:ENNReal)≤2^256 := by exact_mod_cast hι
  have hc' : (Fintype.card EncodingContext:ENNReal)≤2^301 := by exact_mod_cast encodingContext_card_le
  exact ((probEvent_or_le law _ _).trans (add_le_add hd' he')).trans
    ((add_le_add (mul_le_mul' hι' le_rfl) (mul_le_mul' hc' le_rfl)).trans completeness_union_arithmetic)

#print axioms context_table_failure
#print axioms all_search_failure_small
end ClaudeWCT.W9.T3.CanonicalSearch


namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def ContextGood (answers : Answers) : Prop := ∀ context, ¬ContextFailed context answers

theorem context_good_at_route (answers : Answers) (hgood : ContextGood answers)
    (index : Nat) (hi : index<2^31) (lay : Layer) (floor : Nat)
    (hf : if lay=0 then floor=14 else if lay=3 then floor<22 else floor<20) (left right : Digest) :
    ∃ found, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay floor
      (route index lay).2 (route index lay).1 (.pair left right) 0 (searchLimit lay))=some found := by
  let routed : Fin (2^32) := ⟨(route index lay).2*2^height lay+(route index lay).1,
    ClaudeWCT.W9.T3.Correctness.route_routed_lt index hi lay⟩
  let context : EncodingContext := ((lay,routed,left,right),⟨if lay=0 then 0 else floor,by
    by_cases hl : lay=0
    · simp [hl]
    · by_cases h3 : lay=3
      · rw [if_neg hl]; rw [if_neg hl, if_pos h3] at hf; exact hf
      · rw [if_neg hl]; rw [if_neg hl, if_neg h3] at hf; omega⟩)
  have hh := hgood context
  have hfloor : contextFloor context=floor := by
    by_cases hl : lay=0
    · have hf' : floor=14 := by simpa only [hl,if_true] using hf
      simpa only [contextFloor,context,hl,if_true] using hf'.symm
    · by_cases h3 : lay=3
      · dsimp only [contextFloor,context]; rw [if_neg hl, if_pos h3, if_neg hl]
      · have : floor<20 := by rw [if_neg hl, if_neg h3] at hf; exact hf
        dsimp only [contextFloor,context]; rw [if_neg hl, if_neg h3, if_neg hl]
        omega
  have ht := routedTree_of lay (tree:=(route index lay).2) (route_leaf_bound index lay)
  have hl := routedLeaf_of lay (tree:=(route index lay).2) (route_leaf_bound index lay)
  unfold ContextFailed at hh
  rw [hfloor] at hh
  simp only [context,routed,ht,hl] at hh
  exact Option.ne_none_iff_exists'.mp hh
end ClaudeWCT.W9.T3.CanonicalSearch

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem searchPreparedLayers_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index<2^31)
    (prepared : PreparedRoots) (forest : PairRoot) :
    ∃ result, evalWithAnswerFn answers (searchPreparedLayers cache index prepared forest)=some result := by
  obtain ⟨⟨c0,d0,l0⟩,hs0⟩ := context_good_at_route answers hgood index hi 0 14 (by rfl)
    (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2
  have hd0 := (canonical_search_some' answers 0 14 (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2)
    (searchLimit 0) 0 c0 d0 l0 (by decide) hs0).2.2.2
  let r1 := CanonicalPolicy.nextResidual 69 0 l0 d0
  have hr1 : r1<56 := CanonicalPolicy.accepted_top_residual hd0
  have hf1' : CanonicalPolicy.threshold 1 r1<16 := CanonicalPolicy.lower_one_floor_lt ⟨r1,hr1⟩
  have hf1 : CanonicalPolicy.threshold 1 r1<20 := by omega
  obtain ⟨⟨c1,d1,l1⟩,hs1⟩ := context_good_at_route answers hgood index hi 1
    (CanonicalPolicy.threshold 1 r1) (by simpa only [show (1:Layer)≠0 by decide, show (1:Layer)≠3 by decide, if_false] using hf1)
    (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2
  have hd1 := (canonical_search_some' answers 1 (CanonicalPolicy.threshold 1 r1)
    (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2)
    (searchLimit 1) 0 c1 d1 l1 (by decide) hs1).2.2.2
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  have hr2 : r2<41 := CanonicalPolicy.accepted_one_residual ⟨r1,hr1⟩ hd1
  have hf2 : CanonicalPolicy.threshold 2 r2<20 := by
    have h := (CanonicalPolicy.lower_two_progress ⟨r2,hr2⟩).1
    change CanonicalPolicy.threshold 2 r2≤19 at h
    omega
  obtain ⟨⟨c2,d2,l2⟩,hs2⟩ := context_good_at_route answers hgood index hi 2
    (CanonicalPolicy.threshold 2 r2) (by simpa only [show (2:Layer)≠0 by decide, show (2:Layer)≠3 by decide, if_false] using hf2)
    (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2
  have hd2 := (canonical_search_some' answers 2 (CanonicalPolicy.threshold 2 r2)
    (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2)
    (searchLimit 2) 0 c2 d2 l2 (by decide) hs2).2.2.2
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  have hr3 : r3<22 := CanonicalPolicy.accepted_two_residual ⟨r2,hr2⟩ hd2
  have hf3 : CanonicalPolicy.threshold 3 r3<22 := by
    rwa [CanonicalPolicy.lower_three_progress r3 hr3]
  obtain ⟨⟨c3,d3,l3⟩,hs3⟩ := context_good_at_route answers hgood index hi 3
    (CanonicalPolicy.threshold 3 r3) (by simpa only [show (3:Layer)≠0 by decide, if_false, if_true] using hf3) forest.1 forest.2
  have hn1 : ¬CanonicalPolicy.threshold 1 r1≥16 := by omega
  have hn2 : ¬CanonicalPolicy.threshold 2 r2≥22 := by omega
  have hn3 : ¬CanonicalPolicy.threshold 3 r3≥22 := by omega
  dsimp only [r1,r2,r3] at hs1 hs2 hs3 hn1 hn2 hn3
  simp only [searchPreparedLayers,CanonicalPolicy.threshold_top,CanonicalPolicy.totalCredit,
    evalWithAnswerFn_bind,hs0,hn1,if_false,hs1,hn2,hs2,hn3,hs3,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

#print axioms context_good_at_route
#print axioms searchPreparedLayers_complete
end SigGolfCandidate.Research.SharedForest


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

def run (accept : HashOutput → Bool) (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel+1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if accept output then return some (BitVec.ofNat 32 counter,output)
      run accept rho message (counter+1) fuel

def decoder (accept : HashOutput → Bool) (output : HashOutput) : Option HashOutput :=
  if accept output then some output else none

theorem run_none_iff (accept : HashOutput → Bool) (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, evalWithAnswerFn answers (run accept rho message counter fuel)=none ↔
      ∀ offset, offset<fuel → accept (evalWithAnswerFn answers
        (digest rho message (BitVec.ofNat 32 (counter+offset))))=false := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [run]
  | succ fuel ih =>
      intro counter
      simp only [run,evalWithAnswerFn_bind]
      by_cases ha : accept (evalWithAnswerFn answers (digest rho message (BitVec.ofNat 32 counter)))=true
      · simp only [ha,if_true,evalWithAnswerFn_pure,reduceCtorEq,false_iff]
        intro hall
        have h := hall 0 (by omega)
        simp only [Nat.add_zero,ha,Bool.true_eq_false] at h
      · have haf : accept (evalWithAnswerFn answers (digest rho message (BitVec.ofNat 32 counter)))=false :=
          Bool.eq_false_iff.mpr ha
        simp only [haf,Bool.false_eq_true,if_false,ih]
        constructor
        · intro hall offset hoff
          cases offset with
          | zero => simpa only [Nat.add_zero] using haf
          | succ offset =>
              rw [show counter+Nat.succ offset=counter+1+offset by omega]
              exact hall offset (by omega)
        · intro hall offset hoff
          have h := hall (offset+1) (by omega)
          rwa [show counter+(offset+1)=counter+1+offset by omega] at h

theorem run_none_table (accept : HashOutput → Bool) (L : Nat) (hL : L≤2^21)
    (outputs : SearchKey → HashOutput) (fallback : Answers) (rho : Digest) (message : Message) :
    evalWithAnswerFn (Presampling.tableAnswers outputs fallback) (run accept rho message 0 L)=none ↔
      ∀ c : Fin L, decoder accept (outputs (.inr ((rho,message),Fin.castLE hL c)))=none := by
  rw [run_none_iff]
  have hv (c : Nat) (hc : c<L) : evalWithAnswerFn (Presampling.tableAnswers outputs fallback)
      (digest rho message (BitVec.ofNat 32 (0+c)))=outputs (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
    rw [SigGolfCandidate.T3.Presampling.eval_digest]
    have hinput : pad64 (digestInput rho message (BitVec.ofNat 32 (0+c)))=
        searchQuery (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inr,ClaudeWCT.W9.T3.QuerySpace.digestQuery,
        SigGolfCandidate.T3.Sampling.digestTrial,Nat.zero_add]
      rfl
    rw [hinput,Presampling.tableAnswers_apply]
  have hd (x : HashOutput) : decoder accept x=none ↔ accept x=false := by simp [decoder]
  constructor
  · intro h c
    rw [hd,←hv c c.isLt]
    exact h c c.isLt
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)

theorem run_table_failure (accept : HashOutput → Bool) (L : Nat) (hL : L≤2^21)
    (fallback : Answers) (rho : Digest) (message : Message) :
    Pr[fun outputs => evalWithAnswerFn (Presampling.tableAnswers outputs fallback)
      (run accept rho message 0 L)=none | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
      SphincsSecurity.Completeness.failMass (decoder accept)^L := by
  simp_rw [run_none_table accept L hL]
  rw [SphincsSecurity.Completeness.failMass_eq_probEvent]
  have h := Presampling.uniform_table_restriction_failure
    (fun c : Fin L => .inr ((rho,message),Fin.castLE hL c))
    (fun _ _ h => Fin.castLE_injective hL (congrArg Prod.snd (Sum.inr.inj h)))
    (fun x => decoder accept x=none)
  simpa only [failMass_eq_probEvent,Fintype.card_fin,HashOutput,
    SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits] using h

#print axioms run_table_failure
end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    ∃ witness, evalWithAnswerFn answers (signFromOutput cache rho counter output)=some witness := by
  let forest := evalWithAnswerFn answers
    (buildForest (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots (digestIndex output))
  obtain ⟨layers,hl⟩ := searchPreparedLayers_complete answers hgood cache (digestIndex output)
    (digestIndex_lt output) prepared forest.2
  dsimp only [forest,prepared] at hl
  simp only [signFromOutput,evalWithAnswerFn_bind,hl,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem signPayload_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit)≠none) :
    ∃ signature, evalWithAnswerFn answers (signPayload cache message)=some signature := by
  obtain ⟨⟨counter,output⟩,hs⟩ := Option.ne_none_iff_exists'.mp hd
  obtain ⟨witness,hw⟩ := signFromOutput_complete answers hgood cache
    (evalWithAnswerFn answers (privateNonce message)) counter output
  simp only [signPayload,evalWithAnswerFn_bind,hs,hw,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem sign_complete (answers : Answers) (hgood : ContextGood answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hmac : evalWithAnswerFn answers (privateMac cache.region)=cache.tag)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit)≠none) :
    ∃ signature, evalWithAnswerFn answers (sign cache message)=some signature := by
  simpa only [sign,evalWithAnswerFn_bind,hmac,ne_eq,not_true_eq_false,if_false] using
    signPayload_complete answers hgood cache message hd

def SigningComplete (answers : Answers) (cache : SigGolfCandidate.T3.Cache) : Prop :=
  ∀ message, ∃ signature, evalWithAnswerFn answers (sign cache message)=some signature

def DigestFailed (answers : Answers) (message : Message) : Prop :=
  evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 digestAttemptLimit)=none

theorem signing_failed_implies_search (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hmac : evalWithAnswerFn answers (privateMac cache.region)=cache.tag)
    (hfail : ¬SigningComplete answers cache) :
    (∃ message, DigestFailed answers message) ∨ (∃ context, ContextFailed context answers) := by
  classical
  by_contra h
  rcases not_or.mp h with ⟨hd,hc⟩
  apply hfail
  intro message
  exact sign_complete answers (not_exists.mp hc) cache message hmac (not_exists.mp hd message)

#print axioms signFromOutput_complete
#print axioms signing_failed_implies_search
end SigGolfCandidate.Research.SharedForest


namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem context_none_agreement (outputs : SearchKey → HashOutput) (answers fallback : Answers)
    (hagree : Budgets.SearchAgreement outputs answers) (context : EncodingContext) :
    ContextFailed context answers ↔ ContextFailed context (Presampling.tableAnswers outputs fallback) := by
  exact (Presampling.Canonical.search_none_agreement (searchLimit context.1.1)
    (Presampling.searchLimit_le_rows _) outputs answers hagree context.1.1 (contextFloor context)
    context.1.2.1 (.pair context.1.2.2.1 context.1.2.2.2)).trans
    (Presampling.Canonical.search_none_table (searchLimit context.1.1)
      (Presampling.searchLimit_le_rows _) outputs fallback context.1.1 (contextFloor context)
      context.1.2.1 (.pair context.1.2.2.1 context.1.2.2.2)).symm

theorem contextGood_agreement (outputs : SearchKey → HashOutput) (answers fallback : Answers)
    (hagree : Budgets.SearchAgreement outputs answers) :
    ContextGood answers ↔ ContextGood (Presampling.tableAnswers outputs fallback) := by
  constructor
  · intro h context hh
    exact h context ((context_none_agreement outputs answers fallback hagree context).mpr hh)
  · intro h context hh
    exact h context ((context_none_agreement outputs answers fallback hagree context).mp hh)

#print axioms contextGood_agreement
end ClaudeWCT.W9.T3.CanonicalSearch


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signing_failed_keygen (answers : Answers)
    (hfail : ¬SigningComplete answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2) :
    (∃ message, DigestFailed answers message) ∨ (∃ context, ContextFailed context answers) := by
  have hc := (SigGolfCandidate.T3.Correctness.keygen_correct answers).2.2
  have hm : (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.tag=
      evalWithAnswerFn answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) := hc
  exact signing_failed_implies_search answers _ hm.symm hfail

theorem signing_failure_probability (law : ProbComp Answers)
    (hd : ∀ message, Pr[fun answers => DigestFailed answers message | law]≤1/(2:ENNReal)^400)
    (he : ∀ context, Pr[ContextFailed context | law]≤1/(2:ENNReal)^440) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 | law]
      ≤1/(2:ENNReal)^138 := by
  have hm := probEvent_mono (mx:=law) (fun answers _ => signing_failed_keygen answers)
  exact hm.trans (all_search_failure_small law (fun message answers => DigestFailed answers message)
    ContextFailed (by simp [Message,Fintype.card_bitVec]) hd he)

#print axioms signing_failure_probability
end SigGolfCandidate.Research.SharedForest


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 ENNReal
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem decoder_acceptance (accept : HashOutput → Bool) :
    Pr[fun output => (decoder accept output).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      Pr[fun output => accept output=true | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  apply congrArg (probEvent ($ᵗ HashOutput : ProbComp HashOutput))
  funext output
  apply propext
  simp [decoder]

theorem failure_power_400 (accept : HashOutput → Bool)
    (hacc : (1:ENNReal)/5000≤Pr[fun output => accept output=true | ($ᵗ HashOutput : ProbComp HashOutput)]) :
    failMass (decoder accept)^(2^21)≤1/(2:ENNReal)^400 := by
  apply Budgets.V5.failure_power_of_rate _ (1/5000) (2^21) 400 (by norm_num) (by norm_num) _ (by norm_num)
  rw [decoder_acceptance]
  have he : ENNReal.ofReal (((1/5000 : ℚ) : ℚ) : ℝ)=(1:ENNReal)/5000 := by
    push_cast
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
  rw [he]
  exact hacc

#print axioms failure_power_400
end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9 ENNReal
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler

theorem run_none_agreement (accept : HashOutput → Bool) (L : Nat) (hL : L≤2^21)
    (outputs : SearchKey → HashOutput) (answers : Answers)
    (hagree : ∀ key, answers (.inl (.inr (searchQuery key)))=outputs key) (rho : Digest) (message : Message) :
    evalWithAnswerFn answers (run accept rho message 0 L)=none ↔
      ∀ c : Fin L, decoder accept (outputs (.inr ((rho,message),Fin.castLE hL c)))=none := by
  rw [run_none_iff]
  have hv (c : Nat) (hc : c<L) : evalWithAnswerFn answers
      (digest rho message (BitVec.ofNat 32 (0+c)))=outputs (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
    rw [SigGolfCandidate.T3.Presampling.eval_digest]
    have hinput : pad64 (digestInput rho message (BitVec.ofNat 32 (0+c)))=
        searchQuery (.inr ((rho,message),Fin.castLE hL ⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inr,ClaudeWCT.W9.T3.QuerySpace.digestQuery,
        SigGolfCandidate.T3.Sampling.digestTrial,Nat.zero_add]
      rfl
    rw [hinput,hagree]
  have hd (x : HashOutput) : decoder accept x=none ↔ accept x=false := by simp [decoder]
  constructor
  · intro h c
    rw [hd,←hv c c.isLt]
    exact h c c.isLt
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)


#print axioms run_none_agreement
end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial digestTrial_injective
  digestTrial_length V_publicSearch public_randomOracle)
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem run_public (accept : HashOutput → Bool) (rho : Digest) (message : Message) :
    ∀ fuel counter, run accept rho message counter fuel =
      publicProgram (searchLoop (digestTrial rho message) (decoder accept)
        (fun c output => pure (BitVec.ofNat 32 c,output)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
    intro counter
    rw [run,searchLoop]
    simp only [publicProgram,simulateQ_bind,simulateQ_spec_query,
      SphincsSecurity.Concrete.oracleHash,HasQuery.query,SigGolfCandidate.T3.Sampling.publicHandler,
      digest,publicHash,bind_assoc,pure_bind,digestTrial,decoder]
    apply bind_congr
    intro answer
    split <;> simp only [simulateQ_map,simulateQ_pure,map_pure,ih,publicProgram]

theorem V_run (accept : HashOutput → Bool) (secret : BitVec 256) (z b : ENNReal)
    (hb : 1≤b) (rho : Digest) (message : Message)
    (hstep : z*(failMass (decoder accept)*b+(1-failMass (decoder accept)))≤b)
    (fuel counter : Nat) (hlimit : counter+fuel≤2^32) (cache : RCache)
    (hfresh : ∀ c, counter≤c → c<2^32 → cache (digestTrial rho message c)=none) :
    V secret z (run accept rho message counter fuel) cache≤b := by
  rw [run_public]
  exact V_publicSearch secret z b hb _ _ _ (2^32)
    (fun c _ => digestTrial_length rho message c)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    hstep fuel counter hlimit cache hfresh
#print axioms V_run
end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric


namespace ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.Freshness ClaudeWCT.W9.T3.PairRows
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem avoids_run_encoding (accept : HashOutput → Bool) (secret : BitVec 256)
    (target : HashInput) (ht : RowQ target) (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids secret target (run accept rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold run; exact avoids_pure _ _ _
  | succ fuel ih =>
    unfold run
    refine avoids_bind (SigGolfCandidate.T3.Freshness.avoids_digest_encoding secret target ht rho message _) ?_
    intro output
    split
    · exact avoids_pure _ _ _
    · exact ih _

theorem run_preserves_rows (accept : HashOutput → Bool) (secret : BitVec 256)
    (stage : Nat) (rho : Digest) (message : Message) (counter fuel : Nat) (cache : RCache)
    (hc : RowsFreshFrom stage cache) (result : Option (BitVec 32 × HashOutput) × RCache)
    (hr : result∈support (roRun secret (run accept rho message counter fuel) cache)) :
    RowsFreshFrom stage result.2 := by
  intro lay hl tree leaf left right c hlt
  rw [preserves secret _ _ (avoids_run_encoding accept secret _ (rowQ_pairTrial ..)
    rho message counter fuel) cache result hr]
  exact hc lay hl tree leaf left right c hlt
#print axioms run_preserves_rows
end ClaudeWCT.W9.T3.CanonicalSearch.DigestGeneric
