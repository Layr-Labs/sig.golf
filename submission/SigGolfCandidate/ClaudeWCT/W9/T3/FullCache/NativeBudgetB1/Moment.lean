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
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem bound_topPart (cache : Cache) (leaf : Nat) (out : Option (BitVec 32 × List Nat))
    (hout : ∀ counter digits, out = some (counter, digits) →
      digits.length = chainCount (Fin.ofNat 4 0) ∧ digits.sum = target (Fin.ofNat 4 0) ∧
        ValidDigits (Fin.ofNat 4 0) digits) :
    ∃ post, SigGolfCandidate.T3.Cost.CBound post (layerFixedCost 1)
      (signTop cache leaf ((out.map Prod.snd).getD dummyTop)) := by
  first
  | (have hdig : ((out.map Prod.snd).getD dummyTop).length = 54 ∧
        ((out.map Prod.snd).getD dummyTop).sum = 126 := by
       cases out with
       | none => exact ⟨by decide, by decide⟩
       | some pair =>
           obtain ⟨counter, digits⟩ := pair
           have hd := hout counter digits rfl
           exact ⟨hd.1, hd.2.1⟩
     exact ⟨_, (bound_signTop cache _ _ hdig.1 hdig.2).mono_k (by simp [layerFixedCost])⟩)
  | (have hdig : ((out.map Prod.snd).getD dummyTop).length = 54 ∧
        ((out.map Prod.snd).getD dummyTop).sum ≤ 128 := by
       cases out with
       | none => exact ⟨by decide, by decide⟩
       | some pair =>
           obtain ⟨counter, digits⟩ := pair
           have hd := hout counter digits rfl
           exact ⟨hd.1, hd.2.1.trans_le (by decide)⟩
     exact ⟨_, (bound_signTop cache _ _ hdig.1 hdig.2).mono_k (by simp [layerFixedCost])⟩)
  | (have hdig : ((out.map Prod.snd).getD dummyTop).length = 54 ∧
        ((out.map Prod.snd).getD dummyTop).sum ≤ 129 := by
       cases out with
       | none => exact ⟨by decide, by decide⟩
       | some pair =>
           obtain ⟨counter, digits⟩ := pair
           have hd := hout counter digits rfl
           exact ⟨hd.1, hd.2.1.trans_le (by decide)⟩
     exact ⟨_, (bound_signTop cache _ _ hdig.1 hdig.2).mono_k (by simp [layerFixedCost])⟩)
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
theorem avoids_buildLeafP (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    Avoids secret target (ClaudeWCT.WCT9.buildLeafP lay tree leaf digits carry) := by
  unfold ClaudeWCT.WCT9.buildLeafP
  refine avoids_bind (avoids_foldlM _ _ _ _ (fun state i => ?_) _)
    (fun state => avoids_bind (avoids_leafHash secret target ht _ _ _ _) fun _ => avoids_pure _ _ _)
  refine avoids_bind (avoids_packedLowerSecret secret target ht _ _ _ _) fun sc => ?_
  rcases sc with ⟨seed, carry'⟩
  exact avoids_bind (avoids_chain secret target ht _ _ _ _ _ _ _) fun value =>
    avoids_bind (avoids_chain secret target ht _ _ _ _ _ _ _) fun _ => avoids_pure _ _ _
theorem avoids_buildLevel_below (lay tree h level : Nat) (nodes : List Digest) (hlev : level < h) (hh : h < 64)
    (hlen : nodes.length / 2 ≤ 2 ^ (h - level)) :
    Avoids secret target (buildLevel 3 lay tree h level nodes) := by
  unfold buildLevel
  refine avoids_mapM_mem _ _ fun i hi => avoids_nodeHash secret target ht _ _ _ _ _ _ (by decide)
    fun _ _ _ => ?_
  have hi : i < nodes.length / 2 := List.mem_range.mp hi
  have h2 : 2 ≤ 2 ^ (h - level) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (h - level) := Nat.pow_le_pow_right (by decide) (by omega)
  have h64 : 2 ^ (h - level) + 2 ^ (h - level) ≤ 2 ^ 64 := by
    rw [← Nat.two_mul, ← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
theorem avoids_buildLevelsBelow (lay tree h : Nat) (hh : h < 64) (leaves : List Digest)
    (hlen : leaves.length ≤ 2 ^ h) :
    Avoids secret target (ClaudeWCT.WCT9.buildLevelsBelow 3 lay tree h leaves) := by
  unfold ClaudeWCT.WCT9.buildLevelsBelow
  refine avoids_foldlM_range'_inv _ (fun k (levels : List (List Digest)) => levels.length = k ∧
      ∀ j < k, (levels.getD j []).length ≤ 2 ^ (h - j)) (h - 1) 1 ?_ [leaves]
    ⟨rfl, fun j hj => by rw [show j = 0 by omega]; simpa using hlen⟩
  intro k levels hk hk' ⟨hlk, hshape⟩
  have hnodes := hshape (k - 1) (by omega)
  rw [show h - (k - 1) = h - k + 1 by omega, Nat.pow_succ] at hnodes
  refine ⟨avoids_bind (avoids_buildLevel_below secret target ht lay tree h k _ (by omega) hh (by omega))
    fun _ => avoids_pure _ _ _, fun b hb => ?_⟩
  rw [mem_support_bind_iff] at hb
  obtain ⟨nodes, hn, hb⟩ := hb
  simp only [support_pure, Set.mem_singleton_iff] at hb
  subst hb
  have hlenN : nodes.length = (levels.getD (k - 1) []).length / 2 := by
    unfold buildLevel at hn
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
      avoids_bind (avoids_buildLeafP secret target ht _ _ _ _ _) fun r => ?_) _) fun state hs => ?_
  · rcases r with ⟨⟨root, values⟩, carry⟩
    exact avoids_pure _ _ _
  · have hlen := mem_support_foldlM_inv _ (fun k (s : List Digest × List Digest × Digest) => s.1.length = k)
      (fun k a b ha a' ha' => by
        rw [mem_support_bind_iff] at ha'
        obtain ⟨⟨⟨root, values⟩, carry⟩, -, ha'⟩ := ha'
        simp only [support_pure, Set.mem_singleton_iff] at ha'
        subst ha'
        simp [ha]) _ 0 _ rfl state hs
    have hh : height lay < 64 := by fin_cases lay <;> decide
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
    fin_cases lay <;> norm_num [producerRate, ClaudeWCT.W9.T3.ProducerV5.producerCount, V5.topCount129,
      V5.lowerCount197f5, V5.lowerCount196f5, V5.lowerCount197, SigGolfCandidate.T3.BaseAudit.zU, V5.b1, V5.b2, V5.b3, V5.b4]
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
          (.forest forest.1.2) forest.2 hforestFresh) ?_ |>.trans_eq (mul_one _)
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
theorem fixed_le_117348 {fts : ℕ} (h : fts ≤ 31550) : 4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4 ≤ 117348 := by
  have h1 := ClaudeWCT.WCT9.Cost.layerFixedCostP_four
  have h2 := SigGolfCandidate.T3.Cost.layerFixedCost_four
  omega
theorem signingMomentFor_le_two_of_le {fts : ℕ} (h : fts ≤ 31550) : signingMomentFor fts ≤ 2 := by
  rw [signingMomentFor_eq]
  calc signingZ ^ (4 + fts + ClaudeWCT.WCT9.Cost.layerFixedCostP 4) *
        (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 * layerEnvelopes.envelope 2 *
          layerEnvelopes.envelope 3)
      ≤ signingZ ^ 117348 * (digestEnvelope * layerEnvelopes.envelope 0 * layerEnvelopes.envelope 1 *
          layerEnvelopes.envelope 2 * layerEnvelopes.envelope 3) :=
        mul_le_mul' (pow_le_pow_right₀ (SigGolfCandidate.Budget.one_le_zOf _) (fixed_le_117348 h)) le_rfl
    _ ≤ 2 := by
        rw [SigGolfCandidate.Budget.zOf_pow, envelope_product_eq]
        have hcast := ENNReal.ofReal_le_ofReal BaseAudit.V5.signing_envelope
        rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ ((117348 : ℝ) / 131072) by positivity)] at hcast
        norm_num only [ENNReal.ofReal_ofNat] at hcast
        convert hcast using 1
        norm_num
theorem signingMoment_le_two : signingMoment ≤ 2 :=
  signingMomentFor_le_two_of_le (by norm_num [BaseAudit.V5.ftsSign])
theorem V_sign_le_two_of_freshness_for (secret : BitVec 256) (hf : SourceFreshness secret) {fts : ℕ}
    (hfts : fts ≤ 31550)
    (hforest : ∀ index output, ∃ post,
      SigGolfCandidate.T3.Cost.CBound post fts (ClaudeWCT.WCT9.signForest index output))
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_of_freshness_for secret hf fts hforest cache message rcache hc).trans
    (signingMomentFor_le_two_of_le hfts)
theorem realized_sign_exponential_budget_of_freshness_for (secret : BitVec 256)
    (hf : SourceFreshness secret) {fts : ℕ} (hfts : fts ≤ 31550)
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
