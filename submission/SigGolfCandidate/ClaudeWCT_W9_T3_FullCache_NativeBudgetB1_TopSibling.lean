import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopFresh

/-! # The brute-forced top-sibling field is uniform (r3-lean-topbytes, img-v6 expand excess moment)

Campaign T51: `topFieldV v = v.toNat / 2^112` (bits 112..127 of a level-11 node, the 16 bits expand brute-forces; the
signature omits bits 104..127 and bits 104..111 are the zero bits). For a fresh trial answer `a` of a height-11 node,
the zero test (bits 104..111) and the field (bits 112..127) are disjoint windows of `a`, so (`expected_ok_field`)
`E_a[ok ? φ(field) : b] = 2^-8·avgF φ + (1 − 2^-8)·b` and (`expected_field`) `E_a[φ(field)] = avgF φ`, with
`avgF φ = Σ_{c<2^16} 2^-16 φ c`. -/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The 16-bit brute-forced field of a level-11 node value (T51: bits 112..127). -/
def topFieldV (v : Digest) : Nat := v.toNat / 2 ^ 112

theorem topFieldV_lt (v : Digest) : topFieldV v < 2 ^ 16 := by
  have hv := v.isLt
  unfold topFieldV
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at hv ⊢
  omega

/-- Uniform average of `φ` over the 2^16 field values. -/
noncomputable def avgF (φ : Nat → ℝ≥0∞) : ℝ≥0∞ := ∑ c ∈ range (2 ^ 16), ((2 : ℝ≥0∞) ^ 16)⁻¹ * φ c

theorem topFieldV_topVal (heap : Nat) (a : HashOutput) :
    topFieldV (topVal heap a) = a.toNat / 2 ^ (topOff heap + 112) % 2 ^ 16 := by
  unfold topFieldV
  rw [topVal_toNat, show (2 : Nat) ^ 128 = 2 ^ 112 * 2 ^ 16 by norm_num, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← pow_add]

theorem window_split (y s c : Nat) :
    (y / 2 ^ s % 2 ^ 8 = 0 ∧ y / 2 ^ (s + 8) % 2 ^ 16 = c) ↔ y / 2 ^ s % 2 ^ 24 = c * 2 ^ 8 := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  generalize y / 2 ^ s = x
  have hm : x % 2 ^ 24 = x % 2 ^ 8 + 2 ^ 8 * (x / 2 ^ 8 % 2 ^ 16) := by
    rw [show (2 : Nat) ^ 24 = 2 ^ 8 * 2 ^ 16 by norm_num, Nat.mod_mul]
  have h1 := Nat.mod_lt x (show 0 < 2 ^ 8 by norm_num)
  have h2 := Nat.mod_lt (x / 2 ^ 8) (show 0 < 2 ^ 16 by norm_num)
  omega

theorem ok_field_iff (heap : Nat) (a : HashOutput) (c : Nat) :
    (topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c) ↔
      a.toNat / 2 ^ (topOff heap + 104) % 2 ^ 24 = c * 2 ^ 8 := by
  rw [topZeroOk_topVal_iff (by norm_num) (by norm_num), topFieldV_topVal, show zeroStart 11 = 104 from rfl,
    show topZeroBits 11 = 8 from rfl, show topOff heap + 112 = topOff heap + 104 + 8 by omega]
  exact window_split a.toNat (topOff heap + 104) c

theorem expected_finite_sum {α ι : Type} [DecidableEq ι] (law : ProbComp α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    expectedValue law (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expectedValue law (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectedValue_def]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [expectedValue_add, ih]

theorem prob_not (P : HashOutput → Prop) :
    Pr[fun a => ¬P a | ($ᵗ HashOutput : ProbComp HashOutput)] =
      1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  have hc := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) P
  rw [probFailure_uniformSample, tsub_zero] at hc
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hc ▸ le_add_right le_rfl))
    (by rw [add_comm]; exact hc)

/-- **Accepted trial, weighted by the omitted field.** -/
theorem expected_ok_field (heap : Nat) (φ : Nat → ℝ≥0∞) (b : ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => if topZeroOk 11 (topVal heap a) = true then φ (topFieldV (topVal heap a)) else b) =
      ((2 : ℝ≥0∞) ^ 8)⁻¹ * avgF φ + (1 - ((2 : ℝ≥0∞) ^ 8)⁻¹) * b := by
  have hpt : (fun a : HashOutput => if topZeroOk 11 (topVal heap a) = true then φ (topFieldV (topVal heap a)) else b) =
      fun a => (∑ c ∈ range (2 ^ 16), (if topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c
          then 1 else 0) * φ c) + (if ¬ topZeroOk 11 (topVal heap a) = true then 1 else 0) * b := by
    funext a
    by_cases hok : topZeroOk 11 (topVal heap a) = true
    · rw [if_pos hok, if_neg (not_not.mpr hok), zero_mul, add_zero,
        Finset.sum_eq_single (topFieldV (topVal heap a))]
      · rw [if_pos ⟨hok, rfl⟩, one_mul]
      · intro c _ hc
        rw [if_neg (fun h => hc h.2.symm), zero_mul]
      · intro hn; exact absurd (mem_range.mpr (topFieldV_lt _)) hn
    · rw [if_neg hok, if_pos hok, one_mul]
      rw [Finset.sum_eq_zero (fun c _ => by rw [if_neg (fun h => hok h.1), zero_mul]), zero_add]
  have hsum : ∑ c ∈ range (2 ^ 16), expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => (if topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c then 1 else 0) * φ c) =
      ((2 : ℝ≥0∞) ^ 8)⁻¹ * avgF φ := by
    unfold avgF
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [expectedValue_mul_const, expectedValue_ite_one]
    have hcl : c < 2 ^ 16 := mem_range.mp hc
    have hp : Pr[fun a : HashOutput => topZeroOk 11 (topVal heap a) = true ∧ topFieldV (topVal heap a) = c |
        ($ᵗ HashOutput : ProbComp HashOutput)] = ((2 : ℝ≥0∞) ^ 24)⁻¹ := by
      simp only [ok_field_iff heap _ c]
      exact prob_window _ _ _ (by have := topOff_add_le heap; omega) (by omega)
    rw [hp, ← mul_assoc, ← ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← pow_add]
  have hnot : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => (if ¬ topZeroOk 11 (topVal heap a) = true then 1 else 0) * b) =
      (1 - ((2 : ℝ≥0∞) ^ 8)⁻¹) * b := by
    rw [expectedValue_mul_const, expectedValue_ite_one, prob_not, prob_topAccept (by norm_num) (by norm_num)]
    rfl
  rw [hpt, expectedValue_add, expected_finite_sum, hsum, hnot]

/-- **Kept trial** (fuel exhausted): the field is uniform. -/
theorem expected_field (heap : Nat) (φ : Nat → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => φ (topFieldV (topVal heap a))) = avgF φ := by
  have hpt : (fun a : HashOutput => φ (topFieldV (topVal heap a))) =
      fun a => ∑ c ∈ range (2 ^ 16), (if topFieldV (topVal heap a) = c then 1 else 0) * φ c := by
    funext a
    rw [Finset.sum_eq_single (topFieldV (topVal heap a))]
    · rw [if_pos rfl, one_mul]
    · intro c _ hc; rw [if_neg (fun h => hc h.symm), zero_mul]
    · intro hn; exact absurd (mem_range.mpr (topFieldV_lt _)) hn
  rw [hpt, expected_finite_sum]
  unfold avgF
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [expectedValue_mul_const, expectedValue_ite_one]
  have hp : Pr[fun a : HashOutput => topFieldV (topVal heap a) = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 : ℝ≥0∞) ^ 16)⁻¹ := by
    simp only [topFieldV_topVal]
    exact prob_window _ _ _ (by have := topOff_add_le heap; omega) (mem_range.mp hc)
  rw [hp, mul_comm]

/-- `avgF φ` is a fixed point of the accepted-trial step. -/
theorem avgF_step (heap : Nat) (φ : Nat → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => if topZeroOk 11 (topVal heap a) = true then φ (topFieldV (topVal heap a)) else avgF φ) ≤ avgF φ := by
  rw [expected_ok_field, ← add_mul, add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr (by norm_num)), one_mul]

end ClaudeWCT.W9.T3.TopMoment

namespace SigGolfCandidate.T3.Cost.Bound
open OracleComp OracleSpec

theorem post_of_support {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) : ∀ x ∈ support oa, Post x := by
  intro x hx
  rw [← fst_countWith weight oa, support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  exact (h.count_support r hr).1

theorem post_of_roRun {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) (secret : BitVec 256) (cache : SigGolfCandidate.T3.Sampling.RCache)
    (r : α × SigGolfCandidate.T3.Sampling.RCache)
    (hr : r ∈ support (SigGolfCandidate.T3.Sampling.roRun secret oa cache)) : Post r.1 := by
  apply h.post_of_support
  apply SigGolfCandidate.T3.Cost.realize_support_subset secret
  apply support_simulateQ_run'_subset SphincsSecurity.romImpl _ cache
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

end SigGolfCandidate.T3.Cost.Bound

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery avoids_map preserves)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Query predicate of the freshness bounds: well-formed and avoiding `target`. -/
abbrev PAv (secret : BitVec 256) (target : HashInput) : Query → Prop :=
  fun q => GoodQuery q ∧ avoidsQuery secret target q

theorem avoids_of_bound {α : Type} {secret : BitVec 256} {target : HashInput} {Post : α → Prop} {k : Nat}
    {oa : M α} (h : Bound (PAv secret target) Post k oa) : Avoids secret target oa :=
  (h.mono (fun _ hq => hq.2) (fun _ hp => hp)).allQueries

theorem level_pow (level : Nat) (h1 : 1 ≤ level) (h10 : level ≤ 10) :
    2 ^ (13 - level) / 2 = 2 ^ (12 - level) ∧ 4 ≤ 2 ^ (12 - level) ∧ 2 ^ (12 - level) + 2 ^ (12 - level) ≤ 4096 := by
  interval_cases level <;> norm_num

section RootChildren2
variable (secret : BitVec 256) (target : HashInput) (heap : Nat) (ht : TopQ heap target) (h23 : heap = 2 ∨ heap = 3)
include ht h23

theorem tbound_topLevel (level : Nat) (h1 : 1 ≤ level) (h10 : level ≤ 10) (nodes : List Digest)
    (hlen : nodes.length = 2 ^ (13 - level)) :
    Bound (PAv secret target) (fun result => result.length = nodes.length / 2) (nodes.length / 2 * topLevelCost level)
      (buildTopLevel level nodes) := by
  obtain ⟨hp1, hp2, hp3⟩ := level_pow level h1 h10
  unfold buildTopLevel
  have hc := Bound.mapM_list (P := PAv secret target) (List.range (nodes.length / 2))
    (fun i => if level = 12 then nodeHash 3 0 0 (2 ^ (12 - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)
      else Prod.snd <$> topNodeAt level (2 ^ (12 - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))
    (fun _ => topLevelCost level) (fun i hi => by
      have hl : level ≠ 12 := by omega
      simp only [hl, if_false]
      rw [List.mem_range, hlen, hp1] at hi
      exact Bound.and_of_allQueries
        (avoids_map _ (tav_topNodeAt secret target heap ht h23 level _ _ _ (by omega) (by omega) (by omega)))
        (Bound.map _ ((bound_topNodeAt _ _ _ _).mono_k (by simp [topLevelCost, hl])) (fun _ _ => trivial)))
  simpa [List.map_const', List.sum_replicate, Nat.mul_comm] using hc

/-- Levels 1..10 of the top tree avoid the trials of the root's children. -/
theorem tbound_levels10 (leaves : List Digest) (hlen : leaves.length = 2 ^ 12) :
    Bound (PAv secret target) (LevelShape 12 10) (∑ i ∈ Finset.range 10, 2 ^ (12 - i) / 2 * topLevelCost (1 + i))
      ((List.range' 1 10).foldlM (fun levels level => do
        let nodes ← buildTopLevel level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) [leaves]) := by
  refine Bound.foldlM_range'_le 1 10 _ (LevelShape 12) (fun i => 2 ^ (12 - i) / 2 * topLevelCost (1 + i)) [leaves]
    ⟨rfl, fun j hj => by
      have he : j = 0 := by omega
      subst j
      simpa using hlen⟩
    (fun i hi levels hlevels => ?_) (fun _ h => h) le_rfl
  have hprevious : (levels.getD (1 + i - 1) []).length = 2 ^ (12 - i) := by
    simpa using hlevels.2 i (by omega)
  refine (tbound_topLevel secret target heap ht h23 (1 + i) (by omega) (by omega) (levels.getD (1 + i - 1) [])
    (by rw [hprevious]; congr 1; omega)).bind' (l := 0) (fun nodes hnodes => ?_) (by rw [hprevious, Nat.add_zero])
  have hnext : nodes.length = 2 ^ (12 - (i + 1)) := by
    rw [hprevious, show 12 - i = 12 - (i + 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)] at hnodes
    exact hnodes
  refine .pure (levels ++ [nodes]) 0 ⟨by simp [hlevels.1], ?_⟩
  intro j hj
  by_cases hold : j ≤ i
  · rw [List.getD_append levels [nodes] [] j (by have := hlevels.1; omega)]
    exact hlevels.2 j hold
  · have he : j = i + 1 := by omega
    subst j
    rw [List.getD_append_right levels [nodes] [] (i + 1) (by have := hlevels.1; omega)]
    simp only [hlevels.1, Nat.sub_self, List.getD_cons_zero]
    exact hnext

end RootChildren2

/-- One level step of `buildTopLevels`. -/
def topStepL (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← buildTopLevel level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])

theorem buildTopLevels_split (leaves : List Digest) :
    buildTopLevels leaves = ((List.range' 1 10).foldlM topStepL [leaves] >>= fun levels =>
      topStepL levels 11 >>= fun levels' => topStepL levels' 12) := by
  unfold buildTopLevels
  rw [show List.range' 1 12 = List.range' 1 10 ++ [11, 12] by decide, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

theorem Ev_const_le {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache) (c : ℝ≥0∞) :
    Ev secret program cache (fun _ => c) ≤ c :=
  Ev_le_of_support secret program cache (fun _ _ => le_rfl)

theorem topTrial_ne_23 (n m : Nat) (l r l' r' : Digest) : topTrial 2 n l r ≠ topTrial 3 m l' r' := by
  intro he
  have h2 := topQ_topTrial 2 n l r
  have h3 := topQ_topTrial 3 m l' r'
  unfold TopQ at h2 h3
  rw [he] at h2
  exact top_tweak_ne (a := 2) (b := 3) (by omega) (by omega) (by omega) (by omega) (by omega)
    (SphincsSecurity.bytesLE_injective (h2.symm.trans h3))

theorem topNonceCap_11 : topNonceCap 11 = 104 * 2 ^ 8 := rfl

/-- The level-11 step on a shape-10 level list: the two root children (heaps 2, 3), as explicit binds. -/
theorem topStepL_11 (levels : List (List Digest)) (hlen10 : (levels.getD 10 []).length = 4) :
    topStepL levels 11 = ((Prod.snd <$> topNodeAt 11 2 ((levels.getD 10 []).getD 0 0) ((levels.getD 10 []).getD 1 0))
      >>= fun a => (Prod.snd <$> topNodeAt 11 3 ((levels.getD 10 []).getD 2 0) ((levels.getD 10 []).getD 3 0))
      >>= fun b => pure (levels ++ [[a, b]])) := by
  unfold topStepL buildTopLevel
  rw [hlen10]
  simp only [show (4 : Nat) / 2 = 2 from rfl, show List.range 2 = [0, 1] from rfl, List.mapM_cons, List.mapM_nil,
    show (11 : Nat) - 1 = 10 from rfl, show ¬ ((11 : Nat) = 12) from by decide, if_false,
    show (2 : Nat) ^ (12 - 11) = 2 from rfl, bind_assoc, pure_bind]

/-- **The root children's omitted fields are independent and uniform** (from the cache after levels 1..10). -/
theorem Ev_rootChildren_tail (secret : BitVec 256) (g : Nat → ℝ≥0∞) (levels : List (List Digest))
    (hshape : LevelShape 12 10 levels) (cache : RCache)
    (hfresh : ∀ heap, heap = 2 ∨ heap = 3 → ∀ n l r, cache (topTrial heap n l r) = none) :
    Ev secret (topStepL levels 11 >>= fun levels' => topStepL levels' 12) cache
      (fun res => g (max (topFieldV ((res.1.getD 11 []).getD 0 0)) (topFieldV ((res.1.getD 11 []).getD 1 0)))) ≤
      avgF (fun c2 => avgF (fun c3 => g (max c2 c3))) := by
  have hlen10 : (levels.getD 10 []).length = 4 := by simpa using hshape.2 10 le_rfl
  have hlen : levels.length = 11 := hshape.1
  rw [topStepL_11 levels hlen10]
  simp only [bind_assoc, bind_map_left, pure_bind]
  unfold topNodeAt
  set L2 := (levels.getD 10 []).getD 0 0
  set R2 := (levels.getD 10 []).getD 1 0
  set L3 := (levels.getD 10 []).getD 2 0
  set R3 := (levels.getD 10 []).getD 3 0
  set F := (fun res : List (List Digest) × RCache =>
    g (max (topFieldV ((res.1.getD 11 []).getD 0 0)) (topFieldV ((res.1.getD 11 []).getD 1 0))))
  -- the root step keeps the children
  have hroot : ∀ (a b : Digest) (σ : RCache),
      Ev secret (topStepL (levels ++ [[a, b]]) 12) σ F ≤ g (max (topFieldV a) (topFieldV b)) := by
    intro a b σ
    unfold topStepL
    rw [Ev_bind]
    refine Ev_le_of_support _ _ _ (fun r _ => ?_)
    rw [Ev_pure]
    simp only [F]
    rw [List.getD_append _ _ _ 11 (by simp [hlen]), List.getD_append_right _ _ _ 11 (by simp [hlen])]
    simp [hlen]
  have hcap : topNonceCap 11 - 1 < 2 ^ 64 := by rw [topNonceCap_11]; norm_num
  refine Ev_topNonceSearch_bind secret 11 2 L2 R2 _ F (fun σ => ∀ n, σ (topTrial 3 n L3 R3) = none)
    (fun v => avgF (fun c3 => g (max (topFieldV v) c3))) _ ?_ ?_ ?_ ?_ (topNonceCap 11 - 1) 0 (by omega) cache
    (fun n => hfresh 3 (Or.inr rfl) n L3 R3) (fun k _ _ => hfresh 2 (Or.inl rfl) k L2 R2)
  · intro σ hσ k ans n
    exact (QueryCache.cacheQuery_of_ne (cache := σ) ans (fun he => topTrial_ne_23 k n L2 R2 L3 R3 he.symm)).trans (hσ n)
  · intro σ hσ k ans
    refine Ev_topNonceSearch_bind secret 11 3 L3 R3 _ F (fun _ => True)
      (fun v => g (max (topFieldV (topVal 2 ans)) (topFieldV v))) _ (fun _ _ _ _ => trivial) ?_ ?_ ?_
      (topNonceCap 11 - 1) 0 (by omega) _ trivial ?_
    · intro σ' _ k' ans'
      exact hroot _ _ _
    · exact avgF_step 3 (fun c => g (max (topFieldV (topVal 2 ans)) c))
    · exact le_of_eq (expected_field 3 (fun c => g (max (topFieldV (topVal 2 ans)) c)))
    · intro n _ _
      exact (QueryCache.cacheQuery_of_ne (cache := σ) ans (fun he => topTrial_ne_23 k n L2 R2 L3 R3 he.symm)).trans (hσ n)
  · exact avgF_step 2 (fun c2 => avgF (fun c3 => g (max c2 c3)))
  · exact le_of_eq (expected_field 2 (fun c2 => avgF (fun c3 => g (max c2 c3))))

/-- **Expand excess, RO part**: over the top-tree build (any prefix producing the 4096 leaves while avoiding the
root children's trials), `E[g(max(field v₂, field v₃))] ≤ avg_{c₂,c₃} g(max c₂ c₃)`. -/
theorem Ev_buildTop_rootChildren (secret : BitVec 256) {γ : Type} (pre : M γ) (sel : γ → List Digest) (k : Nat)
    (hpre : ∀ heap target, TopQ heap target → (heap = 2 ∨ heap = 3) →
      Bound (PAv secret target) (fun s => (sel s).length = 2 ^ 12) k pre) (g : Nat → ℝ≥0∞) :
    Ev secret (pre >>= fun s => buildTopLevels (sel s)) ∅
      (fun res => g (max (topFieldV ((res.1.getD 11 []).getD 0 0)) (topFieldV ((res.1.getD 11 []).getD 1 0)))) ≤
      avgF (fun c2 => avgF (fun c3 => g (max c2 c3))) := by
  rw [Ev_bind]
  refine Ev_le_of_support _ _ _ (fun r1 hr1 => ?_)
  have hlen : (sel r1.1).length = 2 ^ 12 :=
    (hpre 2 _ (topQ_topTrial 2 0 0 0) (Or.inl rfl)).post_of_roRun secret ∅ r1 hr1
  have hf1 : ∀ heap, heap = 2 ∨ heap = 3 → ∀ n l r, r1.2 (topTrial heap n l r) = none := by
    intro heap h23 n l r
    rw [preserves secret _ pre (avoids_of_bound (hpre heap _ (topQ_topTrial heap n l r) h23)) ∅ r1 hr1]
    rfl
  rw [buildTopLevels_split, Ev_bind]
  refine Ev_le_of_support _ _ _ (fun r2 hr2 => ?_)
  have hshape : LevelShape 12 10 r2.1 :=
    (tbound_levels10 secret _ 2 (topQ_topTrial 2 0 0 0) (Or.inl rfl) _ hlen).post_of_roRun secret _ r2 hr2
  have hf2 : ∀ heap, heap = 2 ∨ heap = 3 → ∀ n l r, r2.2 (topTrial heap n l r) = none := by
    intro heap h23 n l r
    rw [preserves secret _ _ (avoids_of_bound (tbound_levels10 secret _ heap (topQ_topTrial heap n l r) h23 _ hlen))
      r1.2 r2 hr2]
    exact hf1 heap h23 n l r
  exact Ev_rootChildren_tail secret g r2.1 hshape r2.2 hf2

end ClaudeWCT.W9.T3.TopMoment
