import SigGolfCandidate.ClaudeWCT.Numerics.N600Price
import SigGolfCandidate.Research.V7Composed198Gate
import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Budgets

section
namespace ClaudeWCT.W9.T3.LayerBudget
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Budgets (signingZ signing_z_le EncodingFreshBelow SourceFreshness V_bind_bounded
  post_of_roRun)
open ClaudeWCT.W9.T3.ProducerV5 (producerEncodingDecode producerRate producerRate_bounds producer_failMass)
open ClaudeWCT.W9.T3.PairRows (PairFreshBelow layerTrial V_layerCounterSearch bound_layerCounterSearch
  avoids_layerCounterSearch preserves_pairBelow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
structure Envelopes where
  b : Layer → ℚ
  ge_one : ∀ lay, 1 ≤ b lay
  step : ∀ lay, (SigGolfCandidate.T3.BaseAudit.zU : ℝ) * ((1 - producerRate lay) * (b lay : ℝ) + producerRate lay) ≤
    (b lay : ℝ)
namespace Envelopes
variable (E : Envelopes)
noncomputable def envelope (lay : Layer) : ENNReal := ENNReal.ofReal (E.b lay : ℝ)
theorem envelope_ge_one (lay : Layer) : 1 ≤ E.envelope lay := by
  rw [envelope, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast E.ge_one lay)
theorem moment_step (lay : Layer) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass (producerEncodingDecode lay) * E.envelope lay +
        (1 - failMass (producerEncodingDecode lay))) ≤ E.envelope lay := by
  have hp0 : 0 ≤ producerRate lay := by linarith [(producerRate_bounds lay).1]
  have hp1 : 0 ≤ 1 - producerRate lay := by linarith [(producerRate_bounds lay).2]
  have hb0 : 0 ≤ (E.b lay : ℝ) := by have := E.ge_one lay; exact_mod_cast (by linarith : (0 : ℚ) ≤ E.b lay)
  have hz0 : 0 ≤ (SigGolfCandidate.T3.BaseAudit.zU : ℝ) := by norm_num [SigGolfCandidate.T3.BaseAudit.zU]
  have hs : 1 - (1 - producerRate lay) = producerRate lay := by ring
  rw [producer_failMass, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp1, hs, envelope]
  calc
    _ ≤ ENNReal.ofReal (SigGolfCandidate.T3.BaseAudit.zU : ℝ) *
      (ENNReal.ofReal (1 - producerRate lay) * ENNReal.ofReal (E.b lay : ℝ) +
        ENNReal.ofReal (producerRate lay)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((SigGolfCandidate.T3.BaseAudit.zU : ℝ) *
        ((1 - producerRate lay) * (E.b lay : ℝ) + producerRate lay)) := by
      rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (E.step lay)
noncomputable def layerMomentBound : Nat → ENNReal
  | 0 => 1
  | n + 1 => E.envelope (Fin.ofNat 4 n) *
      (if n = 0 then signingZ ^ (layerFixedCost 1) else
        signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP (Fin.ofNat 4 n)) * layerMomentBound n)
theorem layerMomentBound_ge_one : ∀ n, 1 ≤ E.layerMomentBound n := by
  intro n; induction n with
  | zero => exact le_rfl
  | succ n ih =>
      simp only [layerMomentBound]
      apply one_le_mul (E.envelope_ge_one _)
      split
      · exact one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)
      · exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) ih
theorem V_layerCounterSearch_fresh (secret : BitVec 256) (lay : Layer)
    (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (layerTrial lay tree leaf msg c) = none) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg counter fuel) cache ≤ E.envelope lay :=
  V_layerCounterSearch secret _ _ (E.envelope_ge_one lay) lay tree leaf msg (E.moment_step lay) fuel counter
    hlimit cache hfresh
theorem bound_topPart (cache : Cache) (leaf : Nat) (out : Option (BitVec 32 × List Nat))
    (hout : ∀ counter digits, out = some (counter, digits) →
      digits.length = chainCount (Fin.ofNat 4 0) ∧ digits.sum = target (Fin.ofNat 4 0) ∧
        ValidDigits (Fin.ofNat 4 0) digits) :
    ∃ post, SigGolfCandidate.T3.Cost.CBound post (layerFixedCost 1)
      (signTop cache leaf ((out.map Prod.snd).getD dummyTop)) := by
  have hdig : ((out.map Prod.snd).getD dummyTop).length = 54 ∧
      ((out.map Prod.snd).getD dummyTop).sum ≤ 145 := by
    cases out with
    | none => exact ⟨by decide, by decide⟩
    | some pair =>
        obtain ⟨counter, digits⟩ := pair
        have hd := hout counter digits rfl
        exact ⟨hd.1, hd.2.1.trans_le (by decide)⟩
  exact ⟨_, (bound_signTop cache _ _ hdig.1 hdig.2).mono_k (by simp [layerFixedCost])⟩
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
  have hh : SigGolfCandidate.T3.QuerySpace.queryHeader
      (pad64 (SigGolfCandidate.T3.chainInput lay tree leaf i step value)) =
      SphincsSecurity.bytesLE 16 (chainHeader lay tree leaf i step) := by
    simpa only [SigGolfCandidate.T3.chainInput, List.append_assoc] using
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
theorem avoids_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.buildLeafP lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafP
  refine avoids_bind (avoids_foldlM _ _ _ _ (fun state i => ?_) _)
    (fun state => avoids_bind (avoids_leafHash secret target ht _ _ _ _) fun _ => avoids_pure _ _ _)
  refine avoids_bind (avoids_packedLowerSecret secret target ht _ _ _ _) fun sc => ?_
  rcases sc with ⟨seed, carry'⟩
  exact avoids_bind (avoids_chain secret target ht _ _ _ _ _ _ _) fun value =>
    avoids_bind (avoids_chain secret target ht _ _ _ _ _ _ _) fun _ => avoids_pure _ _ _
theorem avoids_buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.buildLeafPF lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafPF
  refine avoids_bind ?_ fun cc => ?_
  · unfold ClaudeWCT.WCT9.lowerCoefs
    refine avoids_foldlM _ _ _ _ (fun state j => ?_) _
    refine avoids_bind (avoids_packedLowerSecret secret target ht _ _ _ _) fun sc => ?_
    rcases sc with ⟨coef, carry'⟩
    exact avoids_pure _ _ _
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
theorem avoids_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    Avoids secret target (ClaudeWCT.WCT9.buildTreeP lay tree selected digits) := by
  unfold ClaudeWCT.WCT9.buildTreeP
  refine avoids_bind_support (avoids_foldlM _ _ _ _ (fun state leaf =>
      avoids_bind (avoids_buildLeafPF secret target ht _ _ _ _ _) fun r => ?_) _) fun state hs => ?_
  · rcases r with ⟨⟨root, values⟩, carry⟩
    exact avoids_pure _ _ _
  · have hlen := mem_support_foldlM_inv _ (fun k (s : List Digest × List Digest × Digest) => s.1.length = k)
      (fun k a b ha a' ha' => by
        rw [mem_support_bind_iff] at ha'
        obtain ⟨⟨⟨root, values⟩, carry⟩, -, ha'⟩ := ha'
        simp only [support_pure, Set.mem_singleton_iff] at ha'
        subst ha'
        simp [ha]) _ 0 _ rfl state hs
    have hh : lay.val ≠ 0 → height lay ≤ 7 := by fin_cases lay <;> decide
    refine avoids_bind (avoids_buildLevelsBelow secret target ht _ _ _ hh _ ?_) fun _ => avoids_pure _ _ _
    simp only [List.length_range, Nat.zero_add] at hlen
    omega
end Avoid
theorem V_signLayersBC (secret : BitVec 256) (cache : Cache) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg rcache, PairFreshBelow n rcache →
      V secret signingZ (ClaudeWCT.WCT9.signLayersBC cache index n msg) rcache ≤ E.layerMomentBound n := by
  intro n
  induction n with
  | zero =>
      intro _ msg rcache _
      simp only [ClaudeWCT.WCT9.signLayersBC, V_pure, layerMomentBound, le_refl]
  | succ n ih =>
      intro hn msg rcache hc
      have hnv : (Fin.ofNat 4 n).val = n := Nat.mod_eq_of_lt (by omega)
      have hs := E.V_layerCounterSearch_fresh secret (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
        (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n)) 0
        (by have := ClaudeWCT.WCT9.searchLimit_le (Fin.ofNat 4 n); unfold counterLimit at this; omega) rcache
        (fun c _ hlim => hc.layerTrial _ (by rw [hnv]; omega) _ _ _ _ hlim)
      simp only [ClaudeWCT.WCT9.signLayersBC, layerMomentBound]
      refine V_bind_bounded secret signingZ _ _ rcache _ _ hs ?_
      intro result hr
      have hpost := post_of_roRun (bound_layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
        (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n)) 0)
        secret rcache result hr
      have hnext : PairFreshBelow n result.2 := by
        intro other ho tree' leaf' left' right' c hlt
        have hne : Fin.ofNat 4 n ≠ other := by intro he; subst other; omega
        rw [SigGolfCandidate.T3.Freshness.preserves secret _ _ (avoids_layerCounterSearch secret hne
          (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0
          (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n)) tree' leaf' left' right' c) rcache result hr]
        exact hc other (by omega) tree' leaf' left' right' c hlt
      by_cases hn0 : n = 0
      · subst n
        simp only [ite_true]
        obtain ⟨post, htop⟩ := bound_topPart cache (route index (Fin.ofNat 4 0)).1 result.1
          (fun counter digits hx => hpost counter digits hx)
        refine V_bind_bounded secret signingZ _ _ result.2 _ 1
          (V_of_bound htop secret signingZ (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_ |>.trans_eq (mul_one _)
        intro out _; rw [V_pure]
      · simp only [hn0, ite_false]
        cases hx : result.1 with
        | none =>
            simp only [hx, V_pure]
            exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (E.layerMomentBound_ge_one n)
        | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hpost counter digits hx
          simp only [hx]
          refine V_bind_bounded secret signingZ _ _ result.2 _ _
            (V_of_bound (ClaudeWCT.WCT9.Cost.bound_buildTreeP (Fin.ofNat 4 n) _ _ digits hd.2.2) secret signingZ
              (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_
          intro treeResult htree
          have ht : PairFreshBelow n treeResult.2 :=
            preserves_pairBelow secret _ (fun target htag =>
              avoids_buildTreeP secret target htag.searchQ _ _ _ digits)
              n result.2 hnext treeResult htree
          refine V_bind_bounded secret signingZ _ _ treeResult.2 _ 1
            (ih (by omega) _ _ ht) ?_ |>.trans_eq (mul_one _)
          intro previous _
          cases previous.1 <;> rw [V_pure]
theorem layerMomentBound_four :
    E.layerMomentBound 4 = signingZ ^ (ClaudeWCT.WCT9.Cost.layerFixedCostP 4) *
      E.envelope 0 * E.envelope 1 * E.envelope 2 * E.envelope 3 := by
  have h4 : ClaudeWCT.WCT9.Cost.layerFixedCostP 4 = ClaudeWCT.WCT9.Cost.treeCostP 3 +
      (ClaudeWCT.WCT9.Cost.treeCostP 2 + (ClaudeWCT.WCT9.Cost.treeCostP 1 + layerFixedCost 1)) := rfl
  change E.envelope 3 * (signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP 3) * (E.envelope 2 *
    (signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP 2) * (E.envelope 1 * (signingZ ^ (ClaudeWCT.WCT9.Cost.treeCostP 1) *
      (E.envelope 0 * signingZ ^ (layerFixedCost 1))))))) = _
  rw [h4, pow_add, pow_add, pow_add]
  ring
theorem envelope_prod :
    E.envelope 0 * E.envelope 1 * E.envelope 2 * E.envelope 3 =
      ENNReal.ofReal ((E.b 0 : ℝ) * (E.b 1 : ℝ) * (E.b 2 : ℝ) * (E.b 3 : ℝ)) := by
  have h0 : 0 ≤ (E.b 0 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 0] : (0 : ℚ) ≤ E.b 0)
  have h1 : 0 ≤ (E.b 1 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 1] : (0 : ℚ) ≤ E.b 1)
  have h2 : 0 ≤ (E.b 2 : ℝ) := by exact_mod_cast (by linarith [E.ge_one 2] : (0 : ℚ) ≤ E.b 2)
  simp only [envelope]
  rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (mul_nonneg h0 h1),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h0 h1) h2)]
end Envelopes
open ClaudeWCT.W9.T3.BaseAudit in
noncomputable def Envelopes.v5 : Envelopes where
  b := ![V5.b1, V5.b2, V5.b3, V5.b4]
  ge_one := by intro lay; fin_cases lay <;> norm_num [V5.b1, V5.b2, V5.b3, V5.b4]
  step := by
    intro lay
    have hp := ClaudeWCT.W9.T3.ProducerV5.producerRate_ge lay
    let b : ℝ := (![V5.b1, V5.b2, V5.b3, V5.b4] lay : ℚ)
    have hb : 1 ≤ b := by fin_cases lay <;> norm_num [b, V5.b1, V5.b2, V5.b3, V5.b4]
    have hs : (SigGolfCandidate.T3.BaseAudit.zU : ℝ) *
        ((1 - (ClaudeWCT.W9.T3.ProducerV5.producerCountLower lay : ℝ) * (if lay = 0 then 2^127 else 7*2^126) / 2^256) * b +
          (ClaudeWCT.W9.T3.ProducerV5.producerCountLower lay : ℝ) * (if lay = 0 then 2^127 else 7*2^126) / 2^256) ≤ b := by
      fin_cases lay <;> norm_num [b, ClaudeWCT.W9.T3.ProducerV5.producerCountLower,
        SigGolfCandidate.T3.BaseAudit.zU, V5.b1, V5.b2, V5.b3, V5.b4]
    change (SigGolfCandidate.T3.BaseAudit.zU : ℝ) * ((1 - producerRate lay) * b + producerRate lay) ≤ b
    refine le_trans ?_ hs
    apply mul_le_mul_of_nonneg_left _ (by norm_num [SigGolfCandidate.T3.BaseAudit.zU])
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hb)]
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
noncomputable abbrev layerEnvelopes : ClaudeWCT.W9.T3.LayerBudget.Envelopes :=
  ClaudeWCT.W9.T3.LayerBudget.Envelopes.v5
noncomputable def digestEnvelope : ENNReal := ENNReal.ofReal (BaseAudit.V5.b0 : ℝ)
theorem digestEnvelope_ge_one : 1 ≤ digestEnvelope := by
  rw [digestEnvelope, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  norm_num [BaseAudit.V5.b0]
theorem digest_failMass_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V5.p0 : ℝ)) :
    failMass digestDecode = ENNReal.ofReal (1 - (BaseAudit.V5.p0 : ℝ)) := by
  rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept, haccept,
    ENNReal.ofReal_sub 1 (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J])]
  simp
theorem digest_moment_step_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V5.p0 : ℝ)) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope := by
  have hp0 : 0 ≤ (BaseAudit.V5.p0 : ℝ) := by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]
  have hp1 : 0 ≤ 1 - (BaseAudit.V5.p0 : ℝ) := by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]
  have hb0 : 0 ≤ (BaseAudit.V5.b0 : ℝ) := by norm_num [BaseAudit.V5.b0]
  have hz0 : 0 ≤ (zU : ℝ) := by norm_num [zU]
  have hs : 1 - (1 - (BaseAudit.V5.p0 : ℝ)) = (BaseAudit.V5.p0 : ℝ) := by ring
  rw [digest_failMass_of_acceptance haccept, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hp1, hs, digestEnvelope]
  calc
    _ ≤ ENNReal.ofReal (zU : ℝ) *
      (ENNReal.ofReal (1 - (BaseAudit.V5.p0 : ℝ)) * ENNReal.ofReal (BaseAudit.V5.b0 : ℝ) +
        ENNReal.ofReal (BaseAudit.V5.p0 : ℝ)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((zU : ℝ) *
        ((1 - (BaseAudit.V5.p0 : ℝ)) * (BaseAudit.V5.b0 : ℝ) + (BaseAudit.V5.p0 : ℝ))) := by
      rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h := BaseAudit.V5.step_0
      have h' : ((zU * ((1 - BaseAudit.V5.p0) * BaseAudit.V5.b0 + BaseAudit.V5.p0) : ℚ) : ℝ) ≤
          (BaseAudit.V5.b0 : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
theorem V_digestSearch_fresh_of_acceptance (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V5.p0 : ℝ)) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  ClaudeWCT.W9.T3.Sampling.V_digestSearch secret _ _ digestEnvelope_ge_one
    rho message (digest_moment_step_of_acceptance haccept) fuel counter hlimit cache hfresh
theorem digest_moment_step :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope :=
  digest_moment_step_of_acceptance digest_probability_eq_p0
theorem V_digestSearch_fresh (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  V_digestSearch_fresh_of_acceptance secret rho message fuel counter hlimit cache hfresh
    digest_probability_eq_p0
structure SourceFreshness (secret : BitVec 256) : Prop where
  forest : ∀ index output cache, PairFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (ClaudeWCT.WCT9.signForest index output) cache),
      PairFreshBelow 4 result.2
noncomputable def postDigestMomentFor (fts : ℕ) : ENNReal := signingZ ^ fts * layerEnvelopes.layerMomentBound 4
noncomputable def payloadMomentFor (fts : ℕ) : ENNReal := signingZ ^ 2 * (digestEnvelope * postDigestMomentFor fts)
noncomputable def signingMomentFor (fts : ℕ) : ENNReal := signingZ ^ 2 * payloadMomentFor fts
noncomputable def signingMoment : ENNReal := signingMomentFor BaseAudit.V5.ftsSign
theorem postDigestMomentFor_ge_one (fts : ℕ) : 1 ≤ postDigestMomentFor fts :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (layerEnvelopes.layerMomentBound_ge_one 4)
theorem payloadMomentFor_ge_one (fts : ℕ) : 1 ≤ payloadMomentFor fts :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    (one_le_mul digestEnvelope_ge_one (postDigestMomentFor_ge_one fts))
theorem V_signPayload_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) (fts : ℕ)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (signPayload cache message) rcache ≤ payloadMomentFor fts := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateNonce message) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro nonce hn
  have hnFresh := privateNonce_preserves_fresh secret message rcache hc nonce hn
  refine V_bind_bounded secret signingZ _ _ nonce.2 _ _
    (V_digestSearch_fresh secret nonce.1 message digestAttemptLimit 0
      (by have := ClaudeWCT.WCT9.digestAttemptLimit_le; omega) nonce.2
      (fun c _ hlim => hnFresh.1 _ _ _ hlim)) ?_
  intro found hd
  have hdFresh := digestSearch_preserves_pairBelow secret nonce.1 message 0 digestAttemptLimit nonce.2 hnFresh
    found hd
  cases hx : found.1 with
  | none => simp only [V_pure]; exact postDigestMomentFor_ge_one fts
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      obtain ⟨post, hbound⟩ := hforest (ClaudeWCT.WCT9.digestIndex output) output
      refine V_bind_bounded secret signingZ _ _ found.2 _ _
        (V_of_bound hbound secret signingZ (SigGolfCandidate.Budget.one_le_zOf _) found.2) ?_
      intro forest hforestRun
      have hforestFresh := hf.forest _ _ found.2 hdFresh forest hforestRun
      refine V_bind_bounded secret signingZ _ _ forest.2 _ 1
        (layerEnvelopes.V_signLayersBC secret cache (ClaudeWCT.WCT9.digestIndex output) 4 (by decide)
          (.pair forest.1.2.1 forest.1.2.2) forest.2 hforestFresh) ?_ |>.trans_eq (mul_one _)
      intro pieces _
      cases pieces.1 <;> rw [V_pure]
theorem V_sign_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) (fts : ℕ)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ signingMomentFor fts := by
  show V secret signingZ (ClaudeWCT.WCT9.signWith digestAttemptLimit cache message) rcache ≤
    signingMomentFor fts
  unfold ClaudeWCT.WCT9.signWith
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateMac cache.region) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro result hr
  have hmac := privateMac_preserves_fresh secret cache.region rcache hc result hr
  split
  · rw [V_pure]; exact payloadMomentFor_ge_one fts
  · exact V_signPayload_of_freshness_for secret hf fts hforest cache message result.2 hmac
theorem signingMomentFor_eq (fts : ℕ) : signingMomentFor fts =
    signingZ ^ (4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4) *
    (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 * layerEnvelopes.envelope 2 *
      layerEnvelopes.envelope 3) := by
  rw [signingMomentFor, payloadMomentFor, postDigestMomentFor, layerEnvelopes.layerMomentBound_four, pow_add,
    pow_add]
  ring
theorem signingMomentFor_mono {a b : ℕ} (h : a ≤ b) : signingMomentFor a ≤ signingMomentFor b := by
  have hz : signingZ ^ a ≤ signingZ ^ b := pow_le_pow_right₀ (SigGolfCandidate.Budget.one_le_zOf _) h
  unfold signingMomentFor payloadMomentFor postDigestMomentFor
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hz le_rfl)))
theorem envelope_product_eq : digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 *
    layerEnvelopes.envelope 2 * layerEnvelopes.envelope 3 =
    ENNReal.ofReal ((BaseAudit.V5.b0 : ℝ) * (BaseAudit.V5.b1 : ℝ) * (BaseAudit.V5.b2 : ℝ) *
      (BaseAudit.V5.b3 : ℝ) * (BaseAudit.V5.b4 : ℝ)) := by
  change ENNReal.ofReal (BaseAudit.V5.b0 : ℝ) * ENNReal.ofReal (BaseAudit.V5.b1 : ℝ) *
    ENNReal.ofReal (BaseAudit.V5.b2 : ℝ) * ENNReal.ofReal (BaseAudit.V5.b3 : ℝ) *
    ENNReal.ofReal (BaseAudit.V5.b4 : ℝ) = _
  rw [← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V5.b0 : ℝ) by norm_num [BaseAudit.V5.b0]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V5.b0 : ℝ) * (BaseAudit.V5.b1 : ℝ) by
      norm_num [BaseAudit.V5.b0, BaseAudit.V5.b1]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V5.b0 : ℝ) * (BaseAudit.V5.b1 : ℝ) * (BaseAudit.V5.b2 : ℝ) by
      norm_num [BaseAudit.V5.b0, BaseAudit.V5.b1, BaseAudit.V5.b2]),
    ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.V5.b0 : ℝ) * (BaseAudit.V5.b1 : ℝ) * (BaseAudit.V5.b2 : ℝ) *
      (BaseAudit.V5.b3 : ℝ) by
      norm_num [BaseAudit.V5.b0, BaseAudit.V5.b1, BaseAudit.V5.b2, BaseAudit.V5.b3])]
theorem fixed_le_112868 {fts : ℕ} (h : fts ≤ 31334) : 4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4 ≤ 112653 := by
  have h1 := ClaudeWCT.WCT9.Cost.layerFixedCostP_four
  have h2 := SigGolfCandidate.T3.Cost.layerFixedCost_four
  omega
theorem signingMomentFor_le_two_of_le {fts : ℕ} (h : fts ≤ 31334) : signingMomentFor fts ≤ 2 := by
  rw [signingMomentFor_eq]
  calc signingZ ^ (4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4) *
        (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 * layerEnvelopes.envelope 2 *
          layerEnvelopes.envelope 3)
      ≤ signingZ ^ 112653 * (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 *
          layerEnvelopes.envelope 2 * layerEnvelopes.envelope 3) :=
        mul_le_mul' (pow_le_pow_right₀ (SigGolfCandidate.Budget.one_le_zOf _) (fixed_le_112868 h)) le_rfl
    _ ≤ 2 := by
        rw [SigGolfCandidate.Budget.zOf_pow, envelope_product_eq]
        have hcast := ENNReal.ofReal_le_ofReal BaseAudit.V5.signing_envelope
        rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ ((112653 : ℝ) / 131072) by positivity)] at hcast
        norm_num only [ENNReal.ofReal_ofNat] at hcast
        convert hcast using 1
        norm_num
theorem signingMoment_le_two : signingMoment ≤ 2 :=
  signingMomentFor_le_two_of_le (by norm_num [BaseAudit.V5.ftsSign])
theorem V_sign_le_two_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) {fts : ℕ}
    (hfts : fts ≤ 31334)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_of_freshness_for secret hf fts hforest cache message rcache hc).trans
    (signingMomentFor_le_two_of_le hfts)
theorem realized_sign_exponential_budget_of_freshness_for (secret : BitVec 256)
    (hf : SourceFreshness secret) {fts : ℕ} (hfts : fts ≤ 31334)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (SigGolfCandidate.T3.Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  have h := V_sign_le_two_of_freshness_for secret hf hfts hforest cache message rcache hc
  rw [SigGolfCandidate.T3.Sampling.V_realized] at h
  simp only [signingZ_pow] at h
  rw [StateT.run'_eq, expectedValue_map]
  exact h
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
    V secret z (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output) rcache ≤ z ^ 112467 * L := by
  unfold SigGolfCandidate.Research.SharedForest.signFromOutput
  refine (V_bind_bounded secret z _ _ rcache (z ^ 31321) (z ^ 81146 * L)
    (V_of_bound (SigGolfCandidate.Research.SharedForest.bound_buildForest ..) secret z hz rcache) ?_).trans_eq ?_
  · intro forest hforest
    have hp := SigGolfCandidate.Research.SharedForest.bound_prepareRoots (digestIndex output)
    rw [SigGolfCandidate.Research.SharedForest.prepared_roots_cost] at hp
    refine V_bind_bounded secret z _ _ forest.2 (z ^ 81146) L
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
    z ^ 2 * (z ^ 2 * (D * (z ^ 112467 * (z ^ 169 * L)))) =
      z ^ 112640 * (D * L) := by
  rw [show 112640 = 2 + 2 + 112467 + 169 by decide, pow_add, pow_add, pow_add]
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
open SigGolfCandidate.T3 ClaudeWCT.WCT9 ClaudeWCT.W9.T3.ProducerV5.Canonical
theorem selected_event (lay : Layer) (floor c : Nat) (answer : HashOutput) :
    (∃ ds, decoder lay floor answer = some ds ∧ CanonicalPolicy.credit lay ds = c) ↔
      accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = c) (encodingAnswer lay answer) := by
  exact (accepted_iff lay floor _ _).symm


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

private theorem selected_probability_below (lay : Layer) (floor c : Nat) (hc : c < floor) :
    Pr[fun answer => ∃ ds, decoder lay floor answer = some ds ∧ CanonicalPolicy.credit lay ds = c |
      ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
  have he : (fun answer => ∃ ds, decoder lay floor answer = some ds ∧
      CanonicalPolicy.credit lay ds = c) = (fun _ : HashOutput => False) := by
    funext answer
    apply propext
    constructor
    · rintro ⟨ds, hd, hr⟩
      have hf := CanonicalPolicy.producerDecodeAt_credit hd
      omega
    · exact False.elim
  rw [he]
  simp

theorem selected_top_probability_of_law (hist : List (Nat × Nat)) (den floor : Nat)
    (hlaw : ∀ c : Fin 204, floor ≤ c.val+16 →
      Pr[fun answer => accepted 0 floor (fun ds => CanonicalPolicy.credit 0 ds = c.val+16)
        (encodingAnswer 0 answer) | ($ᵗ HashOutput : ProbComp HashOutput)] =
        (histogramWeight hist (c.val+16) : ENNReal)/den)
    (hfloor : 16 ≤ floor) (c : Fin 220) :
    Pr[fun answer => ∃ ds, decoder 0 floor answer = some ds ∧ CanonicalPolicy.credit 0 ds = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ c.val then (histogramWeight hist c.val : ENNReal) / den else 0 := by
  by_cases hc : floor ≤ c.val
  · rw [if_pos hc]
    have hc16 : 16 ≤ c.val := hfloor.trans hc
    let shifted : Fin 204 := ⟨c.val-16, by have := c.isLt; omega⟩
    have hs : shifted.val+16 = c.val := Nat.sub_add_cancel hc16
    have hp := hlaw shifted (by simpa only [hs] using hc)
    rw [hs] at hp
    calc
      _ = Pr[fun answer => accepted 0 floor (fun ds => CanonicalPolicy.credit 0 ds = c.val)
          (encodingAnswer 0 answer) | ($ᵗ HashOutput : ProbComp HashOutput)] := by
        apply probEvent_congr'
        · intro answer _
          exact selected_event 0 floor c.val answer
        · rfl
      _ = _ := hp
  · rw [if_neg hc]
    exact selected_probability_below 0 floor c.val (by omega)

theorem selected_lower_probability_of_law (hist : List (Nat × Nat)) (den : Nat)
    (lay : Layer) (floor : Nat)
    (hlaw : ∀ c : Fin 128, floor ≤ c.val →
      Pr[fun answer => accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = c.val)
        (encodingAnswer lay answer) | ($ᵗ HashOutput : ProbComp HashOutput)] =
        (histogramWeight hist c.val : ENNReal)/den)
    (c : Fin 128) :
    Pr[fun answer => ∃ ds, decoder lay floor answer = some ds ∧ CanonicalPolicy.credit lay ds = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ c.val then (histogramWeight hist c.val : ENNReal) / den else 0 := by
  by_cases hc : floor ≤ c.val
  · rw [if_pos hc]
    calc
      _ = Pr[fun answer => accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = c.val)
          (encodingAnswer lay answer) | ($ᵗ HashOutput : ProbComp HashOutput)] := by
        apply probEvent_congr'
        · intro answer _
          exact selected_event lay floor c.val answer
        · rfl
      _ = _ := hlaw c hc
  · rw [if_neg hc]
    exact selected_probability_below lay floor c.val (by omega)

#print axioms selected_top_probability_of_law
#print axioms selected_lower_probability_of_law
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
        have hh : queryHeader (pad64 (SigGolfCandidate.T3.chainInput lay tree leaf i start value)) =
            bytesLE 16 (chainHeader lay tree leaf i start) := by
          simpa only [SigGolfCandidate.T3.chainInput, List.append_assoc] using
            queryHeader_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16])
              (chainHeader lay tree leaf i start)
        exact searchQ_ne hh (chainHeader_not_search lay tree leaf i start) ht
      · intro next
        exact avoids_bind (ih _ _) fun _ => avoids_pure _ _ _

theorem avoids_buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    Avoids secret target (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine avoids_bind ?_ fun cc => ?_
  · unfold lowerCoefs
    refine avoids_foldlM _ _ _ _ (fun state j => ?_) _
    refine avoids_bind (avoids_packedLowerSecret secret target ht _ _ _ _) fun sc => ?_
    rcases sc with ⟨coef, carry'⟩
    exact avoids_pure _ _ _
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
        (fun k (s : List Digest × List (List Digest) × Digest) => s.1.length = k)
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
  one_ge : ∀ r, r < 52 → 1 ≤ one r
  two_ge : ∀ r, r < 35 → 1 ≤ two r
  three_ge : ∀ r, r < 18 → 1 ≤ three r
  initial_step : z * (acceptedWeight (decoder 0 16) (fun ds => one (nextResidual 63 0 ds)) +
    SphincsSecurity.Completeness.failMass (decoder 0 16) * initial) ≤ initial
  one_step : ∀ r, r < 52 → z *
    (acceptedWeight (decoder 1 (threshold 1 r)) (fun ds => two (nextResidual r 1 ds)) +
     SphincsSecurity.Completeness.failMass (decoder 1 (threshold 1 r)) * one r) ≤ one r
  two_step : ∀ r, r < 35 → z *
    (acceptedWeight (decoder 2 (threshold 2 r)) (fun ds => three (nextResidual r 2 ds)) +
     SphincsSecurity.Completeness.failMass (decoder 2 (threshold 2 r)) * two r) ≤ two r
  three_step : ∀ r, r < 18 → z *
    (acceptedWeight (decoder 3 (threshold 3 r)) (fun _ => 1) +
     SphincsSecurity.Completeness.failMass (decoder 3 (threshold 3 r)) * three r) ≤ three r

/-- The actual four searches follow canonical ancestors. Their continuation
weights depend on the remaining credit, and the retained lower reveals cost no HASH calls. -/
theorem V_searchPreparedLayers (secret : BitVec 256) (z : ENNReal) (hz : 1 ≤ z)
    (E : SearchEnvelope z) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret z (searchPreparedLayers cache index prepared forest) rcache ≤ z^169 * E.initial := by
  have hfactor : 1 ≤ z^169 := one_le_pow₀ hz
  unfold searchPreparedLayers
  simp only [CanonicalPolicy.totalCredit, threshold_top]
  apply V_layerSearch_bind (secret := secret) (z := z) (lay := 0) (weight := fun ds => z^169 * E.one (nextResidual 63 0 ds))
  · intro rc _
    simpa only [V_pure] using one_le_mul hfactor E.initial_ge
  · intro rc hr counter hc answer ds0 hd0
    have hres1 := accepted_top_residual hd0
    have hp1 : threshold 1 (nextResidual 63 0 ds0) ≤ 17 :=
      (lower_one_progress ⟨nextResidual 63 0 ds0, hres1⟩).1
    simp only [show ¬ (threshold 1 (nextResidual 63 0 ds0) ≥ 18) by omega, ↓reduceIte]
    apply V_layerSearch_bind (secret := secret) (z := z) (lay := 1)
      (weight := fun ds => z^169 * E.two (nextResidual (nextResidual 63 0 ds0) 1 ds))
    · intro rc _
      simpa only [V_pure] using one_le_mul hfactor (E.one_ge _ hres1)
    · intro rc hr counter1 hc1 answer1 ds1 hd1
      have hres2 : nextResidual (nextResidual 63 0 ds0) 1 ds1 < 35 :=
        accepted_one_residual ⟨nextResidual 63 0 ds0, hres1⟩ hd1
      have hp2 : threshold 2 (nextResidual (nextResidual 63 0 ds0) 1 ds1) ≤ 17 :=
        (lower_two_progress ⟨nextResidual (nextResidual 63 0 ds0) 1 ds1, hres2⟩).1
      simp only [show ¬ (threshold 2 (nextResidual (nextResidual 63 0 ds0) 1 ds1) ≥ 18) by omega,
        ↓reduceIte]
      apply V_layerSearch_bind (secret := secret) (z := z) (lay := 2)
        (weight := fun ds => z^169 * E.three (nextResidual (nextResidual (nextResidual 63 0 ds0) 1 ds1) 2 ds))
      · intro rc _
        simpa only [V_pure] using one_le_mul hfactor (E.two_ge _ hres2)
      · intro rc hr counter2 hc2 answer2 ds2 hd2
        have hres3 : nextResidual (nextResidual (nextResidual 63 0 ds0) 1 ds1) 2 ds2 < 18 :=
          accepted_two_residual ⟨nextResidual (nextResidual 63 0 ds0) 1 ds1, hres2⟩ hd2
        have hp3 := lower_three_progress _ hres3
        simp only [show ¬ (threshold 3
            (nextResidual (nextResidual (nextResidual 63 0 ds0) 1 ds1) 2 ds2) ≥ 18) by omega,
          ↓reduceIte]
        apply V_layerSearch_bind (secret := secret) (z := z) (lay := 3) (weight := fun _ => z^169)
        · intro rc _
          simpa only [V_pure] using one_le_mul hfactor (E.three_ge _ hres3)
        · intro rc hr counter3 hc3 answer3 ds3 hd3
          have hd : SigGolfCandidate.T3.decode 0 (encodingAnswer 0 answer) = some ds0 :=
            (producerDecodeAt_spec hd0).1
          have hds := SigGolfCandidate.T3.decode_length_sum hd
          have hbound := bound_signTop cache (route index 0).1 ds0
            (by exact hds.1)
            (by exact hds.2.le)
          refine (V_bind_bounded secret z _ _ rc (z^169) 1
            (V_of_bound hbound secret z hz rc) ?_).trans_eq (mul_one _)
          intro top _
          simp only [V_pure]
          exact le_rfl
        · simpa only [mul_one] using scaled_step z
            (E.three (nextResidual (nextResidual (nextResidual 63 0 ds0) 1 ds1) 2 ds2))
            (z^169) _ (fun _ => 1) (E.three_step _ hres3)
        · decide
        · exact hr
      · exact scaled_step z _ (z^169) _ _ (E.two_step _ hres2)
      · decide
      · exact hr
    · exact scaled_step z _ (z^169) _ _ (E.one_step _ hres1)
    · decide
    · exact hr
  · exact scaled_step z _ (z^169) _ _ E.initial_step
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
source decoder, through its exact selected-credit law. -/
noncomputable def envelope_of_rows
    (topHist lowerHist : List (Nat × Nat)) (topDen lowerDen : Nat)
    (one two three : Array Nat) (initial : Nat)
    (htopDen : 0 < topDen) (hlowerDen : 0 < lowerDen)
    (htopHist : ∀ e ∈ topHist, e.1 < 220)
    (hlowerHist : ∀ e ∈ lowerHist, e.1 < 128)
    (htopBound : ∀ answer ds, decoder 0 16 answer = some ds → credit 0 ds < 220)
    (hlowerBound : ∀ (lay : Layer), lay ≠ 0 → ∀ floor answer ds,
      decoder lay floor answer = some ds → credit lay ds < 128)
    (htopLaw : ∀ i : Fin 220,
      Pr[fun answer => ∃ ds, decoder 0 16 answer = some ds ∧ credit 0 ds = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if 16 ≤ i.val then (histogramWeight topHist i.val : ENNReal)/topDen else 0)
    (hlowerLaw : ∀ (lay : Layer), lay ≠ 0 → ∀ floor (i : Fin 128),
      Pr[fun answer => ∃ ds, decoder lay floor answer = some ds ∧ credit lay ds = i.val |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        if floor ≤ i.val then (histogramWeight lowerHist i.val : ENNReal)/lowerDen else 0)
    (hinitial : recurrenceCheck topDen topHist 16 63 one initial = true)
    (hone : ∀ r, r < 52 → recurrenceCheck lowerDen lowerHist (threshold 1 r) r two
      (one[r]?.getD 0) = true)
    (htwo : ∀ r, r < 35 → recurrenceCheck lowerDen lowerHist (threshold 2 r) r three
      (two[r]?.getD 0) = true)
    (hthree : ∀ r, r < 18 → recurrenceCheck lowerDen lowerHist (threshold 3 r) r #[scale]
      (three[r]?.getD 0) = true) : SearchEnvelope ((zNum : ENNReal)/zDen) := by
  have h0 := decoder_recurrence 220 (decoder 0 16) (credit 0) topHist 16 63 topDen one initial
    htopDen htopBound htopHist htopLaw hinitial
  have h1 (r : Nat) (hr : r < 52) := decoder_recurrence 128 (decoder 1 (threshold 1 r))
    (credit 1) lowerHist (threshold 1 r) r lowerDen two (one[r]?.getD 0) hlowerDen
    (hlowerBound 1 (by decide) _) hlowerHist (hlowerLaw 1 (by decide) _) (hone r hr)
  have h2 (r : Nat) (hr : r < 35) := decoder_recurrence 128 (decoder 2 (threshold 2 r))
    (credit 2) lowerHist (threshold 2 r) r lowerDen three (two[r]?.getD 0) hlowerDen
    (hlowerBound 2 (by decide) _) hlowerHist (hlowerLaw 2 (by decide) _) (htwo r hr)
  have h3 (r : Nat) (hr : r < 18) := decoder_recurrence 128 (decoder 3 (threshold 3 r))
    (credit 3) lowerHist (threshold 3 r) r lowerDen #[scale] (three[r]?.getD 0) hlowerDen
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
      (fun ds => (#[scale][r-credit 3 ds]?.getD 0 : ENNReal)/scale) =
      acceptedWeight (decoder 3 (threshold 3 r)) (fun _ => 1) := by
    apply acceptedWeight_congr_on
    intro answer ds hd
    have hf := producerDecodeAt_credit hd
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

theorem selected_top_probability (floor : Nat) (hfloor : 16 ≤ floor) (c : Fin 220) :
    Pr[fun answer => ∃ ds, decoder 0 floor answer = some ds ∧ CanonicalPolicy.credit 0 ds = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ c.val then (histogramWeight topAcceptedHistogram c.val : ENNReal) / topDen else 0 := by
  apply selected_top_probability_of_law _ _ floor _ hfloor c
  intro i hi
  have hden : (topDen : ENNReal) = 2^129 := by norm_num [topDen, Nat.cast_mul, Nat.cast_pow]
  rw [hden]
  exact selected_top_histogram_probability top_histogram_checked floor i hi

theorem selected_lower_probability (lay : Layer) (hl : lay ≠ 0) (floor : Nat) (c : Fin 128) :
    Pr[fun answer => ∃ ds, decoder lay floor answer = some ds ∧ CanonicalPolicy.credit lay ds = c.val |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      if floor ≤ c.val then (histogramWeight lowerHistogram c.val : ENNReal) / lowerDen else 0 := by
  apply selected_lower_probability_of_law _ _ lay floor _ c
  intro i hi
  have hd (z : Fin 6) (i : Nat) (hi : i<128) :
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        SigGolfResearch.LowerEffectiveCounting.zeros w = z.val ∧
        SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
        SigGolfResearch.LowerEffectiveCounting.score w = i).card := by
    rw [← bits_digit_eq]
    exact CanonicalCounting.lower_digit z.val i hi
  have hden : (lowerDen : ENNReal) = 2^130 := by norm_num [lowerDen, Nat.cast_mul, Nat.cast_pow]
  rw [hden]
  exact selected_lower_histogram_probability hd lower_histogram_checked lay hl floor i hi

theorem checkRows_at (stage : Nat) (row next : Array Nat) (h : checkRows stage row next = true)
    (r : Nat) (hr : r < row.size) :
    recurrenceCheck lowerDen lowerHistogram (CanonicalPolicy.threshold stage r) r next
      (row[r]?.getD 0) = true := by
  simp only [checkRows, List.all_eq_true] at h
  have he := h r (List.mem_range.mpr hr)
  simpa only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, show (default : Nat) = 0 from rfl] using he

noncomputable def certifiedEnvelope : SearchEnvelope ((zNum : ENNReal)/zDen) :=
  envelope_of_rows topAcceptedHistogram lowerHistogram topDen lowerDen rowOne rowTwo rowThree initialBound
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (fun a ds hd => producerDecodeAt_top_credit_lt hd)
    (fun lay hl floor a ds hd => producerDecodeAt_lower_credit_lt lay hl hd)
    (selected_top_probability 16 le_rfl) selected_lower_probability
    initial_checked
    (fun r hr => checkRows_at 1 rowOne rowTwo row_one_checked r (by exact hr))
    (fun r hr => checkRows_at 2 rowTwo rowThree row_two_checked r (by exact hr))
    (fun r hr => checkRows_at 3 rowThree #[scale] row_three_checked r (by exact hr))

theorem certifiedEnvelope_initial : certifiedEnvelope.initial = (initialBound : ENNReal)/scale := rfl

theorem V_searchPreparedLayers_certified (secret : BitVec 256) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (prepared : SigGolfCandidate.Research.SharedForest.PreparedRoots)
    (forest : SigGolfCandidate.Research.SharedForest.PairRoot) (rcache : RCache)
    (hfresh : RowsFreshFrom 0 rcache) :
    V secret SigGolfCandidate.T3.Budgets.signingZ
      (SigGolfCandidate.Research.SharedForest.searchPreparedLayers cache index prepared forest) rcache ≤
      SigGolfCandidate.T3.Budgets.signingZ^169 * ((initialBound : ENNReal)/scale) := by
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

theorem top_acceptance (floor : Nat) (hf : 16≤floor) :
    Pr[fun a => (decoder 0 floor a).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedMass topAcceptedHistogram floor : ENNReal)/topDen := by
  rw [← acceptedWeight_one_probability]
  exact acceptedWeight_acceptedMass 220 (decoder 0 floor) (CanonicalPolicy.credit 0)
    topAcceptedHistogram floor topDen
    (fun a ds hd => producerDecodeAt_top_credit_lt hd) (by decide +kernel)
    (selected_top_probability floor hf)

theorem lower_acceptance (lay : Layer) (hl : lay≠0) (floor : Nat) :
    Pr[fun a => (decoder lay floor a).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (acceptedMass lowerHistogram floor : ENNReal)/lowerDen := by
  rw [← acceptedWeight_one_probability]
  exact acceptedWeight_acceptedMass 128 (decoder lay floor) (CanonicalPolicy.credit lay)
    lowerHistogram floor lowerDen
    (fun a ds hd => producerDecodeAt_lower_credit_lt lay hl hd) (by decide +kernel)
    (selected_lower_probability lay hl floor)

theorem ofReal_nat_ratio (n d : Nat) (hd : 0<d) :
    ENNReal.ofReal (((n : ℚ)/d : ℚ) : ℝ) = (n : ENNReal)/d := by
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hd), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

def topFailureRate : ℚ := (acceptedMass topAcceptedHistogram 16 : ℚ)/topDen
def lowerFailureRate : ℚ := (acceptedMass lowerHistogram 17 : ℚ)/lowerDen

theorem top_failure_rate_checked : 0≤topFailureRate ∧ topFailureRate≤1 ∧
    (400 : ℚ)*0.6931471808≤2^22*topFailureRate := by decide +kernel

theorem lower_failure_rate_checked : 0≤lowerFailureRate ∧ lowerFailureRate≤1 ∧
    (400 : ℚ)*0.6931471808≤2^21*lowerFailureRate := by decide +kernel

theorem top_failure_power : failMass (decoder 0 16)^(2^22)≤1/(2:ENNReal)^400 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ topFailureRate
    (2^22) 400 top_failure_rate_checked.1 top_failure_rate_checked.2.1 _ top_failure_rate_checked.2.2
  rw [top_acceptance 16 le_rfl, topFailureRate, ofReal_nat_ratio _ _ (by decide)]

theorem lower_failure_power (lay : Layer) (hl : lay≠0) (floor : Nat) (hf : floor≤17) :
    failMass (decoder lay floor)^(2^21)≤1/(2:ENNReal)^400 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ lowerFailureRate
    (2^21) 400 lower_failure_rate_checked.1 lower_failure_rate_checked.2.1 _ lower_failure_rate_checked.2.2
  rw [lower_acceptance lay hl floor, lowerFailureRate, ofReal_nat_ratio _ _ (by decide)]
  gcongr
  exact_mod_cast acceptedMass_antitone lowerHistogram hf

theorem lower_threshold_bound (stage r : Nat)
    (hstage : (stage=1 ∧ r<52) ∨ (stage=2 ∧ r<35) ∨ (stage=3 ∧ r<18)) :
    CanonicalPolicy.threshold stage r≤17 := by
  rcases hstage with ⟨rfl,hr⟩ | ⟨rfl,hr⟩ | ⟨rfl,hr⟩
  · have h := List.all_eq_true.mp lower_thresholds_checked.1 r (List.mem_range.mpr (by exact hr))
    exact of_decide_eq_true h
  · have h := List.all_eq_true.mp lower_thresholds_checked.2.1 r (List.mem_range.mpr (by exact hr))
    exact of_decide_eq_true h
  · have h := List.all_eq_true.mp lower_thresholds_checked.2.2 r (List.mem_range.mpr (by exact hr))
    exact of_decide_eq_true h

#print axioms top_failure_power
#print axioms lower_failure_power
#print axioms lower_threshold_bound
end ClaudeWCT.W9.T3.CanonicalSearch

namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem top_layer_failure (secret : BitVec 256) (tree leaf : Nat) (msg : LayerMsg)
    (cache : RCache) (hfresh : RowsFreshFrom 0 cache) :
    Pr[fun result => result.1 = none | roRun secret
      (CanonicalPolicy.layerCounterSearchAt 0 16 tree leaf msg 0 (2^22)) cache] ≤
      1/(2:ENNReal)^400 := by
  exact (search_failure secret 0 16 tree leaf msg (2^22) 0 (by decide) cache
    (fun c _ hc => hfresh.layer 0 (by decide) tree leaf msg c hc)).trans top_failure_power

theorem lower_layer_failure (secret : BitVec 256) (lay : Layer) (hl : lay≠0)
    (floor tree leaf : Nat) (hf : floor≤17) (msg : LayerMsg)
    (cache : RCache) (hfresh : RowsFreshFrom lay.val cache) :
    Pr[fun result => result.1 = none | roRun secret
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg 0 (2^21)) cache] ≤
      1/(2:ENNReal)^400 := by
  exact (search_failure secret lay floor tree leaf msg (2^21) 0 (by decide) cache
    (fun c _ hc => hfresh.layer lay le_rfl tree leaf msg c hc)).trans (lower_failure_power lay hl floor hf)

#print axioms top_layer_failure
#print axioms lower_layer_failure
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

theorem top_failure_rate_440_checked : 0≤topFailureRate ∧ topFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤2^22*topFailureRate := by decide +kernel

theorem lower_failure_rate_440_checked : 0≤lowerFailureRate ∧ lowerFailureRate≤1 ∧
    (440 : ℚ)*0.6931471808≤2^21*lowerFailureRate := by decide +kernel

theorem top_failure_power_440 : failMass (decoder 0 16)^(2^22)≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ topFailureRate
    (2^22) 440 top_failure_rate_440_checked.1 top_failure_rate_440_checked.2.1 _ top_failure_rate_440_checked.2.2
  rw [top_acceptance 16 le_rfl, topFailureRate, ofReal_nat_ratio _ _ (by decide)]

theorem lower_failure_power_440 (lay : Layer) (hl : lay≠0) (floor : Nat) (hf : floor≤17) :
    failMass (decoder lay floor)^(2^21)≤1/(2:ENNReal)^440 := by
  apply ClaudeWCT.W9.T3.Budgets.V5.failure_power_of_rate _ lowerFailureRate
    (2^21) 440 lower_failure_rate_440_checked.1 lower_failure_rate_440_checked.2.1 _ lower_failure_rate_440_checked.2.2
  rw [lower_acceptance lay hl floor, lowerFailureRate, ofReal_nat_ratio _ _ (by decide)]
  gcongr
  exact_mod_cast acceptedMass_antitone lowerHistogram hf


#print axioms top_failure_power_440
#print axioms lower_failure_power_440
end ClaudeWCT.W9.T3.CanonicalSearch


namespace ClaudeWCT.W9.T3.CanonicalSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem top_layer_failure_440 (secret : BitVec 256) (tree leaf : Nat) (msg : LayerMsg)
    (cache : RCache) (hfresh : RowsFreshFrom 0 cache) :
    Pr[fun result => result.1 = none | roRun secret
      (CanonicalPolicy.layerCounterSearchAt 0 16 tree leaf msg 0 (2^22)) cache] ≤
      1/(2:ENNReal)^440 := by
  exact (search_failure secret 0 16 tree leaf msg (2^22) 0 (by decide) cache
    (fun c _ hc => hfresh.layer 0 (by decide) tree leaf msg c hc)).trans top_failure_power_440

theorem lower_layer_failure_440 (secret : BitVec 256) (lay : Layer) (hl : lay≠0)
    (floor tree leaf : Nat) (hf : floor≤17) (msg : LayerMsg)
    (cache : RCache) (hfresh : RowsFreshFrom lay.val cache) :
    Pr[fun result => result.1 = none | roRun secret
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg 0 (2^21)) cache] ≤
      1/(2:ENNReal)^440 := by
  exact (search_failure secret lay floor tree leaf msg (2^21) 0 (by decide) cache
    (fun c _ hc => hfresh.layer lay le_rfl tree leaf msg c hc)).trans (lower_failure_power_440 lay hl floor hf)

#print axioms top_layer_failure_440
#print axioms lower_layer_failure_440
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

abbrev EncodingContext := EncodingFamilyBC × Fin 18

def contextFloor (context : EncodingContext) : Nat :=
  if context.1.1=0 then 16 else context.2.val

def ContextFailed (context : EncodingContext) (answers : Correctness.Answers) : Prop :=
  evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt context.1.1 (contextFloor context)
    (routedTree context.1.1 context.1.2.1) (routedLeaf context.1.1 context.1.2.1)
    (.pair context.1.2.2.1 context.1.2.2.2) 0 (searchLimit context.1.1))=none

theorem encodingContext_card_le : Fintype.card EncodingContext ≤ 2^301 := by
  change Fintype.card (EncodingFamilyBC × Fin 18) ≤ 2^301
  rw [Fintype.card_prod,encodingFamilyBC_card,Fintype.card_fin]
  exact (Nat.mul_le_mul_left _ (show 18≤2^11 by norm_num)).trans_eq (by rw [←pow_add])

theorem context_table_failure (context : EncodingContext) :
    Pr[fun outputs => ContextFailed context (Presampling.tableAnswers outputs zeroAnswers) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2:ENNReal)^440 := by
  unfold ContextFailed
  rw [Presampling.Canonical.search_table_failure _ (Presampling.searchLimit_le_rows _) ]
  by_cases hl : context.1.1=0
  · simpa only [contextFloor,hl,if_pos,searchLimit_top,SigGolfCandidate.T3.counterLimit] using top_failure_power_440
  · have hf : context.2.val≤17 := by omega
    simpa only [contextFloor,hl,if_false,searchLimit_lower hl,lowerSearchLimit] using
      lower_failure_power_440 context.1.1 hl context.2.val hf

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
    (hf : if lay=0 then floor=16 else floor<18) (left right : Digest) :
    ∃ found, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay floor
      (route index lay).2 (route index lay).1 (.pair left right) 0 (searchLimit lay))=some found := by
  let routed : Fin (2^32) := ⟨(route index lay).2*2^height lay+(route index lay).1,
    ClaudeWCT.W9.T3.Correctness.route_routed_lt index hi lay⟩
  let context : EncodingContext := ((lay,routed,left,right),⟨if lay=0 then 0 else floor,by
    by_cases hl : lay=0
    · simp [hl]
    · simpa only [hl,if_false] using hf⟩)
  have hh := hgood context
  have hfloor : contextFloor context=floor := by
    by_cases hl : lay=0
    · have hf' : floor=16 := by simpa only [hl,if_true] using hf
      simpa only [contextFloor,context,hl,if_true] using hf'.symm
    · simp only [contextFloor,context,hl,if_false]
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
  obtain ⟨⟨c0,d0⟩,hs0⟩ := context_good_at_route answers hgood index hi 0 16 (by rfl)
    (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2
  have hd0 := (canonical_search_some answers 0 16 (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2)
    (searchLimit 0) 0 c0 d0 (by decide) hs0).2.2
  let r1 := CanonicalPolicy.nextResidual 63 0 d0
  have hr1 : r1<52 := CanonicalPolicy.accepted_top_residual hd0
  have hf1 : CanonicalPolicy.threshold 1 r1<18 := by
    have h := (CanonicalPolicy.lower_one_progress ⟨r1,hr1⟩).1
    change CanonicalPolicy.threshold 1 r1≤17 at h
    omega
  obtain ⟨⟨c1,d1⟩,hs1⟩ := context_good_at_route answers hgood index hi 1
    (CanonicalPolicy.threshold 1 r1) (by exact hf1)
    (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2
  have hd1 := (canonical_search_some answers 1 (CanonicalPolicy.threshold 1 r1)
    (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2)
    (searchLimit 1) 0 c1 d1 (by decide) hs1).2.2
  let r2 := CanonicalPolicy.nextResidual r1 1 d1
  have hr2 : r2<35 := CanonicalPolicy.accepted_one_residual ⟨r1,hr1⟩ hd1
  have hf2 : CanonicalPolicy.threshold 2 r2<18 := by
    have h := (CanonicalPolicy.lower_two_progress ⟨r2,hr2⟩).1
    change CanonicalPolicy.threshold 2 r2≤17 at h
    omega
  obtain ⟨⟨c2,d2⟩,hs2⟩ := context_good_at_route answers hgood index hi 2
    (CanonicalPolicy.threshold 2 r2) (by exact hf2)
    (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2
  have hd2 := (canonical_search_some answers 2 (CanonicalPolicy.threshold 2 r2)
    (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2)
    (searchLimit 2) 0 c2 d2 (by decide) hs2).2.2
  let r3 := CanonicalPolicy.nextResidual r2 2 d2
  have hr3 : r3<18 := CanonicalPolicy.accepted_two_residual ⟨r2,hr2⟩ hd2
  have hf3 : CanonicalPolicy.threshold 3 r3<18 := by
    rwa [CanonicalPolicy.lower_three_progress r3 hr3]
  obtain ⟨⟨c3,d3⟩,hs3⟩ := context_good_at_route answers hgood index hi 3
    (CanonicalPolicy.threshold 3 r3) (by exact hf3) forest.1 forest.2
  have hn1 : ¬CanonicalPolicy.threshold 1 r1≥18 := by omega
  have hn2 : ¬CanonicalPolicy.threshold 2 r2≥18 := by omega
  have hn3 : ¬CanonicalPolicy.threshold 3 r3≥18 := by omega
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
