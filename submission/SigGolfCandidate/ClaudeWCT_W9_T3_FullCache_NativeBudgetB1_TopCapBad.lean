import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_KeygenMomentV6

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
