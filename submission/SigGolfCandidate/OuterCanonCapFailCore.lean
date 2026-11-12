import SigGolfCandidate.OuterCanonCapFailDefs
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option maxErrors 30
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance low] Classical.propDecidable
attribute [local instance] OuterCanonBase.Paired.instSampleableTypeLabels_capFail
namespace CapFailBound

/-! ### Uniform functions: events on a finite set of coordinates -/

theorem card_filter_forall_mem {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    (S : Finset α) (q : β → Prop) [DecidablePred q] [DecidablePred (fun f : α → β => ∀ a ∈ S, q (f a))] :
    (Finset.univ.filter (fun f : α → β => ∀ a ∈ S, q (f a))).card =
      (Finset.univ.filter q).card ^ S.card * Fintype.card β ^ (Fintype.card α - S.card) := by
  classical
  have hset : Finset.univ.filter (fun f : α → β => ∀ a ∈ S, q (f a)) =
      Fintype.piFinset (fun a => if a ∈ S then Finset.univ.filter q else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h a
      split_ifs with ha
      · simpa using h a ha
      · exact Finset.mem_univ _
    · intro h a ha
      simpa [ha] using h a
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_univ]
  have h1 : (Finset.univ.filter (fun a => a ∈ S)) = S := by ext; simp
  have h2 : (Finset.univ.filter (fun a => a ∉ S)) = Sᶜ := by ext; simp
  rw [h1, h2, Finset.card_compl]

theorem prob_forall_mem {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    [inst : SampleableType (α → β)] (S : Finset α) (q : β → Prop) [DecidablePred q] :
    Pr[fun f : α → β => ∀ a ∈ S, q (f a) | ($ᵗ (α → β) : ProbComp (α → β))] =
      (((Finset.univ.filter q).card : ℝ≥0∞) / Fintype.card β) ^ S.card := by
  classical
  rw [probEvent_uniformSample, card_filter_forall_mem, Fintype.card_fun]
  have hk : S.card ≤ Fintype.card α := Finset.card_le_univ S
  have hB0 : (Fintype.card β : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hBt : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : Fintype.card β ^ Fintype.card α =
      Fintype.card β ^ S.card * Fintype.card β ^ (Fintype.card α - S.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hsplit]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ hB0) (ENNReal.pow_ne_top hBt),
    div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

/-! ### The zero test passes with probability at least `2^-h` -/

/-- Campaign T51: the top zero bits are `b_h = 0,0,1,1,2,3,4,5,6,7,8` (#938: `b_h = h`; restated). -/
theorem topZeroBits_eq {h : Nat} (hh : h ≤ 11) : topZeroBits h = topZeroAlloc.getD h 0 := rfl

theorem topZeroBits_le_eight (h : Nat) : topZeroBits h ≤ 9 := by
  unfold topZeroBits
  by_cases hh : h < 12
  · interval_cases h <;> decide
  · rw [List.getD_eq_default _ _ (by simp only [topZeroAlloc, List.length_cons, List.length_nil]; omega)]
    omega

theorem card_pass_digest {h : Nat} (h11 : h ≤ 11) :
    2 ^ (128 - topZeroBits h) ≤
      (Finset.univ.filter (fun d : BitVec 128 => topZeroOk h d = true)).card := by
  by_cases he : h = 11
  · subst he
    have hb : topZeroBits 11 = 9 := rfl
    rw [hb]
    have hc : ((Finset.range (2 ^ 20)) ×ˢ (Finset.range (2 ^ 99))).card = 2 ^ (128 - 9) := by
      rw [Finset.card_product, Finset.card_range, Finset.card_range]; norm_num
    rw [← hc]
    apply Finset.card_le_card_of_injOn (fun p : Nat × Nat => (BitVec.ofNat 128 (p.1 * 2 ^ 108 + p.2) :
      BitVec 128))
    · intro p hp
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hp
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      unfold topZeroOk
      rw [if_pos rfl]
      simp only [BitVec.toNat_ofNat, beq_iff_eq]
      obtain ⟨h1, h2⟩ := hp
      norm_num at h1 h2 ⊢
      omega
    · intro p hp p' hp' heq
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hp hp'
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at this
      obtain ⟨h1, h2⟩ := hp
      obtain ⟨h1', h2'⟩ := hp'
      norm_num at h1 h2 h1' h2' this
      apply Prod.ext <;> omega
  · have hb8 := topZeroBits_le_eight h
    have hlt : 2 ^ (128 - topZeroBits h) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
    have hc : (Finset.range (2 ^ (128 - topZeroBits h))).card = 2 ^ (128 - topZeroBits h) := Finset.card_range _
    rw [← hc]
    apply Finset.card_le_card_of_injOn (fun x : Nat => (BitVec.ofNat 128 x : BitVec 128))
    · intro x hx
      simp only [Finset.coe_range, Set.mem_Iio] at hx
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      unfold topZeroOk
      rw [if_neg he]
      simp only [BitVec.toNat_ofNat, beq_iff_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact Nat.div_eq_of_lt hx
    · intro x hx y hy heq
      simp only [Finset.coe_range, Set.mem_Iio] at hx hy
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- The halves map: injective pairing of two digests into an output with prescribed halves. -/
noncomputable def joinHalves (a b : BitVec 128) : BitVec 256 :=
  (SphincsSecurity.splitHashOutputEquiv 128 (by decide)).symm (a, b)

theorem joinHalves_low (a b : BitVec 128) : (joinHalves a b).extractLsb' 0 128 = a :=
  congrArg Prod.fst (Equiv.apply_symm_apply (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) (a, b))

theorem joinHalves_high (a b : BitVec 128) : (joinHalves a b).extractLsb' 128 128 = b :=
  congrArg Prod.snd (Equiv.apply_symm_apply (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) (a, b))

theorem card_pass_hash (p : Extract.Pos) {h : Nat} (h11 : h ≤ 11) :
    2 ^ (256 - topZeroBits h) ≤
      (Finset.univ.filter (fun v : BitVec 256 => ¬ (topZeroOk h (p.proj v) = false))).card := by
  set P := Finset.univ.filter (fun d : BitVec 128 => topZeroOk h d = true)
  have hP := card_pass_digest h11
  have hcard : (P ×ˢ (Finset.univ : Finset (BitVec 128))).card = P.card * 2 ^ 128 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bitVec]
  have hb8 := topZeroBits_le_eight h
  have h256 : 2 ^ (256 - topZeroBits h) ≤ P.card * 2 ^ 128 := by
    calc 2 ^ (256 - topZeroBits h) = 2 ^ (128 - topZeroBits h) * 2 ^ 128 := by
          rw [← pow_add, show 128 - topZeroBits h + 128 = 256 - topZeroBits h by omega]
      _ ≤ P.card * 2 ^ 128 := Nat.mul_le_mul_right _ hP
  refine h256.trans ?_
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun x : BitVec 128 × BitVec 128 =>
      if p.high then joinHalves x.2 x.1 else joinHalves x.1 x.2)
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_univ, Set.prod_univ, Set.mem_preimage, Finset.mem_coe, P,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    rw [Extract.Pos.proj_eq]
    cases p.high
    · simp only [Bool.false_eq_true, ite_false, joinHalves_low, hx]; decide
    · simp only [ite_true, joinHalves_high, hx]; decide
  · intro x _ y _ heq
    by_cases hp : p.high = true
    · simp only [hp, ite_true] at heq
      have h1 := congrArg (fun v : BitVec 256 => v.extractLsb' 0 128) heq
      have h2 := congrArg (fun v : BitVec 256 => v.extractLsb' 128 128) heq
      simp only [joinHalves_low, joinHalves_high] at h1 h2
      exact Prod.ext h2 h1
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.false_eq_true, ite_false] at heq
      have h1 := congrArg (fun v : BitVec 256 => v.extractLsb' 0 128) heq
      have h2 := congrArg (fun v : BitVec 256 => v.extractLsb' 128 128) heq
      simp only [joinHalves_low, joinHalves_high] at h1 h2
      exact Prod.ext h1 h2

theorem card_fail_hash (p : Extract.Pos) {h : Nat} (h11 : h ≤ 11) :
    (Finset.univ.filter (fun v : BitVec 256 => topZeroOk h (p.proj v) = false)).card +
      2 ^ (256 - topZeroBits h) ≤ 2 ^ 256 := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitVec 256))) (fun v => topZeroOk h (p.proj v) = false)
  rw [Finset.card_univ, Fintype.card_bitVec] at hsum
  have := card_pass_hash p h11
  change _ = 2 ^ 256 at hsum
  omega

theorem ratio_le {Q h : Nat} (hQ : Q + 2 ^ (256 - h) ≤ 2 ^ 256) (hh : h ≤ 256) :
    (Q : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤ ENNReal.ofReal (1 - (1 / 2) ^ h) := by
  rw [← ENNReal.ofReal_natCast Q, ← ENNReal.ofReal_natCast (2 ^ 256),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hQ' : (Q : ℝ) + 2 ^ (256 - h) ≤ 2 ^ 256 := by exact_mod_cast hQ
  have h2 : (2 : ℝ) ^ 256 = 2 ^ (256 - h) * 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hh]
  have hpos : (0 : ℝ) < 2 ^ h := by positivity
  rw [div_le_iff₀ (by positivity), Nat.cast_pow, Nat.cast_ofNat]
  rw [h2] at hQ' ⊢
  have : (1 - (1 / 2 : ℝ) ^ h) * (2 ^ (256 - h) * 2 ^ h) = 2 ^ (256 - h) * 2 ^ h - 2 ^ (256 - h) := by
    rw [one_div_pow]; field_simp
  rw [this]; linarith

/-! ### U16b: the lower ground zero test passes with probability at least `2^-b` -/

theorem lowerZeroBits_le_three (lay heap : Nat) : WCT9.lowerZeroBits lay heap ≤ 4 := by
  unfold WCT9.lowerZeroBits; split_ifs <;> omega

theorem card_pass_digest_low (lay heap : Nat) :
    2 ^ (128 - WCT9.lowerZeroBits lay heap) ≤
      (Finset.univ.filter (fun d : BitVec 128 => WCT9.lowerZeroOk lay heap d = true)).card := by
  have hb3 := lowerZeroBits_le_three lay heap
  have hlt : 2 ^ (128 - WCT9.lowerZeroBits lay heap) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : (Finset.range (2 ^ (128 - WCT9.lowerZeroBits lay heap))).card = 2 ^ (128 - WCT9.lowerZeroBits lay heap) :=
    Finset.card_range _
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun x : Nat => (BitVec.ofNat 128 x : BitVec 128))
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio] at hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    unfold WCT9.lowerZeroOk
    simp only [BitVec.toNat_ofNat, beq_iff_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Nat.div_eq_of_lt hx
  · intro x hx y hy heq
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem card_pass_hash_of (p : Extract.Pos) (ok : BitVec 128 → Bool) {b : Nat} (hb : b ≤ 128)
    (hP : 2 ^ (128 - b) ≤ (Finset.univ.filter (fun d : BitVec 128 => ok d = true)).card) :
    2 ^ (256 - b) ≤ (Finset.univ.filter (fun v : BitVec 256 => ¬ (ok (p.proj v) = false))).card := by
  set P := Finset.univ.filter (fun d : BitVec 128 => ok d = true)
  have hcard : (P ×ˢ (Finset.univ : Finset (BitVec 128))).card = P.card * 2 ^ 128 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bitVec]
  have h256 : 2 ^ (256 - b) ≤ P.card * 2 ^ 128 := by
    calc 2 ^ (256 - b) = 2 ^ (128 - b) * 2 ^ 128 := by
          rw [← pow_add, show 128 - b + 128 = 256 - b by omega]
      _ ≤ P.card * 2 ^ 128 := Nat.mul_le_mul_right _ hP
  refine h256.trans ?_
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun x : BitVec 128 × BitVec 128 =>
      if p.high then joinHalves x.2 x.1 else joinHalves x.1 x.2)
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_univ, Set.prod_univ, Set.mem_preimage, Finset.mem_coe, P,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    rw [Extract.Pos.proj_eq]
    cases p.high
    · simp only [Bool.false_eq_true, ite_false, joinHalves_low, hx]; decide
    · simp only [ite_true, joinHalves_high, hx]; decide
  · intro x _ y _ heq
    by_cases hp : p.high = true
    · simp only [hp, ite_true] at heq
      have h1 := congrArg (fun v : BitVec 256 => v.extractLsb' 0 128) heq
      have h2 := congrArg (fun v : BitVec 256 => v.extractLsb' 128 128) heq
      simp only [joinHalves_low, joinHalves_high] at h1 h2
      exact Prod.ext h2 h1
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.false_eq_true, ite_false] at heq
      have h1 := congrArg (fun v : BitVec 256 => v.extractLsb' 0 128) heq
      have h2 := congrArg (fun v : BitVec 256 => v.extractLsb' 128 128) heq
      simp only [joinHalves_low, joinHalves_high] at h1 h2
      exact Prod.ext h1 h2

theorem card_fail_hash_low (p : Extract.Pos) (lay heap : Nat) :
    (Finset.univ.filter (fun v : BitVec 256 => WCT9.lowerZeroOk lay heap (p.proj v) = false)).card +
      2 ^ (256 - WCT9.lowerZeroBits lay heap) ≤ 2 ^ 256 := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitVec 256))) (fun v => WCT9.lowerZeroOk lay heap (p.proj v) = false)
  rw [Finset.card_univ, Fintype.card_bitVec] at hsum
  have := card_pass_hash_of p (WCT9.lowerZeroOk lay heap) (by have := lowerZeroBits_le_three lay heap; omega)
    (card_pass_digest_low lay heap)
  change _ = 2 ^ 256 at hsum
  omega

/-! ### One position -/

/-- The cap trials of the position of `n`. -/
def trialSet (n : TreeNode) : Finset Node :=
  (Finset.range (trialCap n.1.lay n.1.level.val)).image (fun j => Node.node (withNonce n j))

theorem trialSet_card (n : TreeNode) : (trialSet n).card = trialCap n.1.lay n.1.level.val := by
  unfold trialSet
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hc := trialCap_le n.1.lay n.1.level.val
  have h := congrArg (fun m : TreeNode => m.1.nonce.val) (Node.node.inj hij)
  rwa [withNonce_nonce n (by omega), withNonce_nonce n (by omega)] at h

theorem allFail_iff (labels : Labels) (n : TreeNode) :
    (∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j) ↔
      ∀ a ∈ trialSet n, trialZeroOk n.1.lay n.1.level.val ((Node.node n).toPos.proj (labels a)) = false := by
  unfold trialSet
  constructor
  · intro h a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact h j (Finset.mem_range.mp hj)
  · intro h j hj
    exact h _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)

/-- Campaign T51: the cap of height `h = level + 1` is `104 · 2^b_h` (#938: `104 · 2^h`; restated). -/
theorem trialCap_top {lay : Layer} {level : Nat} (hl : lay = 0) (hlev : level < 11) :
    trialCap lay level = 104 * 2 ^ topZeroBits (level + 1) := by
  unfold trialCap topNonceCap
  rw [if_pos ⟨hl, hlev⟩]

/-- The real cap-failure bound of one position at children level `l` (zero bits `b = topZeroBits (l + 1)`). -/
noncomputable def failR (l : Nat) : ℝ :=
  (1 - (1 / 2) ^ topZeroBits (l + 1)) ^ (104 * 2 ^ topZeroBits (l + 1))

theorem prob_allFail_le (n : TreeNode) (hl : n.1.lay = 0) (hlev : n.1.level.val < 11) :
    Pr[fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal (failR n.1.level.val) := by
  classical
  have hev : (fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j) =
      (fun labels : Labels => ∀ a ∈ trialSet n,
        (fun v => topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj v) = false) (labels a)) := by
    funext labels
    have h := allFail_iff labels n
    unfold trialZeroOk at h
    simp only [if_pos hl] at h
    exact propext h
  rw [hev]
  refine (le_of_eq (prob_forall_mem (α := Node) (β := HashOutput) (inst := instSampleableTypeLabels_capFail)
    (trialSet n) (fun v => topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj v) = false))).trans ?_
  rw [trialSet_card, trialCap_top hl hlev, Fintype.card_bitVec]
  unfold failR
  rw [ENNReal.ofReal_pow (by
    have : (1 / 2 : ℝ) ^ topZeroBits (n.1.level.val + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)]
  gcongr
  have hf := card_fail_hash (Node.node n).toPos (h := n.1.level.val + 1) (by omega)
  have := ratio_le hf (by have := topZeroBits_le_eight (n.1.level.val + 1); omega)
  convert this using 2

/-! ### Union bound over the positions -/

/-- The nonce-0 representatives of the top positions. -/
def topReps : Finset TreeNode :=
  Finset.univ.filter (fun n : TreeNode => n.1.lay = 0 ∧ n.1.level.val < 11 ∧ n.1.nonce.val = 0)

theorem height_zero : height (0 : Layer) = 12 := rfl

theorem card_fiber_le (l : Nat) :
    (topReps.filter (fun n : TreeNode => n.1.level.val = l)).card ≤ 2 ^ (11 - l) := by
  rw [← Finset.card_range (2 ^ (11 - l))]
  apply Finset.card_le_card_of_injOn (fun n : TreeNode => n.1.idx.val)
  · intro n hn
    simp only [topReps, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hn
    obtain ⟨⟨hlay, -, -⟩, hlev⟩ := hn
    have hv := n.2.2.1
    rw [hlay, height_zero, hlev] at hv
    simp only [Finset.coe_range, Set.mem_Iio]
    have : 12 - l - 1 = 11 - l := by omega
    rwa [this] at hv
  · intro n hn m hm heq
    simp only [topReps, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hn hm
    obtain ⟨⟨hlay, -, hnon⟩, hlev⟩ := hn
    obtain ⟨⟨hlay', -, hnon'⟩, hlev'⟩ := hm
    have ht := source_tree_zero n.2.2.2.1 hlay
    have ht' := source_tree_zero m.2.2.2.1 hlay'
    obtain ⟨⟨lay, tree, level, idx, nonce⟩, hv⟩ := n
    obtain ⟨⟨lay', tree', level', idx', nonce'⟩, hv'⟩ := m
    simp only at hlay hlev hnon hlay' hlev' hnon' ht ht' heq
    subst hlay hlay'
    have e1 : tree = tree' := Fin.ext (by omega)
    have e2 : level = level' := Fin.ext (by omega)
    have e3 : idx = idx' := Fin.ext heq
    have e4 : nonce = nonce' := Fin.ext (by omega)
    subst e1 e2 e3 e4
    rfl

/-- U16b: the nonce-0 representatives of the lower ground positions. -/
def lowReps : Finset TreeNode :=
  Finset.univ.filter (fun n : TreeNode => n.1.lay ≠ 0 ∧
    WCT9.lowerZeroBits n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1)) ≠ 0 ∧ n.1.nonce.val = 0)

theorem card_lowReps_le : lowReps.card ≤ 3 * 2 ^ 34 := by
  have hU : (Finset.univ : Finset (Fin 4 × Fin (2 ^ 25) × Fin 12 × Fin 32)).card = 3 * 2 ^ 34 := by
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [← hU]
  apply Finset.card_le_card_of_injOn (fun n : TreeNode =>
    ((⟨n.1.lay.val, n.1.lay.isLt⟩ : Fin 4), (⟨n.1.tree.val % 2 ^ 25, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ 25)),
      n.1.level, (⟨n.1.idx.val % 32, Nat.mod_lt _ (by norm_num)⟩ : Fin 32)))
  · intro n _; simp
  · have key : ∀ n : TreeNode, (n.1.lay ≠ 0 ∧
        WCT9.lowerZeroBits n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1)) ≠ 0 ∧ n.1.nonce.val = 0) →
        n.1.tree.val < 2 ^ 25 ∧ n.1.idx.val < 32 ∧ n.1.nonce.val = 0 := by
      intro n hn
      obtain ⟨-, hb, h0⟩ := hn
      have hv : n.1.level.val < height n.1.lay ∧ n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) ∧
          n.1.tree.val < 2 ^ treeBits n.1.lay ∧ (n.1.lay = 0 ∨ n.1.level.val + 1 < height n.1.lay) := n.2
      refine ⟨lt_of_lt_of_le hv.2.2.1 (Nat.pow_le_pow_right (by norm_num)
        (ClaudeWCT.W9.T3M.Extract.treeBits_le _)), ?_, h0⟩
      have h16 : 2 ^ (height n.1.lay - n.1.level.val - 1) < 32 := by
        by_contra hc
        apply hb
        unfold WCT9.lowerZeroBits
        rw [if_pos (Or.inr (Or.inr (by omega)))]
      exact lt_trans hv.2.1 h16
    intro n hn m hm heq
    simp only [lowReps, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hn hm
    obtain ⟨hnt, hni, hn0⟩ := key n hn
    obtain ⟨hmt, hmi, hm0⟩ := key m hm
    simp only [Prod.mk.injEq, Fin.mk.injEq] at heq
    obtain ⟨h1, h2, h3, h4⟩ := heq
    rw [Nat.mod_eq_of_lt hnt, Nat.mod_eq_of_lt hmt] at h2
    rw [Nat.mod_eq_of_lt hni, Nat.mod_eq_of_lt hmi] at h4
    obtain ⟨⟨lay, tree, level, idx, nonce⟩, hv⟩ := n
    obtain ⟨⟨lay', tree', level', idx', nonce'⟩, hv'⟩ := m
    simp only at h1 h2 h3 h4 hn0 hm0
    have e0 : lay = lay' := Fin.ext h1
    have e1 : tree = tree' := Fin.ext h2
    have e3 : idx = idx' := Fin.ext h4
    have e4 : nonce = nonce' := Fin.ext (by omega)
    subst e0 e1 h3 e3 e4
    rfl

theorem sum_low_arith : ((3 * 2 ^ 34 : Nat) : ℝ) * (36788 / 100000 : ℝ) ^ 128 ≤ 1 / 2 ^ 144 := by
  norm_num

theorem sum_lowReps_le (f : TreeNode → ℝ≥0∞)
    (hf : ∀ n ∈ lowReps, f n ≤ ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128)) :
    ∑ n ∈ lowReps, f n ≤ (2 ^ 144 : ℝ≥0∞)⁻¹ := by
  calc ∑ n ∈ lowReps, f n ≤ ∑ n ∈ lowReps, ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := Finset.sum_le_sum hf
    _ = (lowReps.card : ℝ≥0∞) * ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((3 * 2 ^ 34 : Nat) : ℝ≥0∞) * ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
        gcongr; exact_mod_cast card_lowReps_le
    _ = ENNReal.ofReal (((3 * 2 ^ 34 : Nat) : ℝ) * (36788 / 100000 : ℝ) ^ 128) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 144) := ENNReal.ofReal_le_ofReal sum_low_arith
    _ = (2 ^ 144 : ℝ≥0∞)⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]

theorem half_add_half : (2 ^ 144 : ℝ≥0∞)⁻¹ + (2 ^ 144 : ℝ≥0∞)⁻¹ ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have e : ∀ k : ℕ, (2 ^ k : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ k) := fun k => by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [e, e, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem disjoint_reps : Disjoint topReps lowReps := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [topReps, lowReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn hn'
  exact hn'.1 hn.1

theorem mem_topReps (n : TreeNode) :
    n ∈ topReps ↔ n.1.lay = 0 ∧ n.1.level.val < 11 ∧ n.1.nonce.val = 0 := by
  simp only [topReps, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_lowReps (n : TreeNode) :
    n ∈ lowReps ↔ n.1.lay ≠ 0 ∧
      WCT9.lowerZeroBits n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1)) ≠ 0 ∧ n.1.nonce.val = 0 := by
  simp only [lowReps, Finset.mem_filter, Finset.mem_univ, true_and]

theorem capFail_eq :
    CapFailT = fun labels : Labels =>
      ∃ n ∈ topReps ∪ lowReps, ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j := by
  funext labels
  apply propext
  unfold CapFailT
  simp only [Finset.mem_union, mem_topReps, mem_lowReps]
  constructor
  · rintro ⟨n, hpos, h0, hall⟩
    refine ⟨n, ?_, hall⟩
    rcases hpos with h | h
    · exact Or.inl ⟨h.1, h.2, h0⟩
    · exact Or.inr ⟨h.1, h.2, h0⟩
  · rintro ⟨n, hn, hall⟩
    rcases hn with h | h
    · exact ⟨n, Or.inl ⟨h.1, h.2.1⟩, h.2.2, hall⟩
    · exact ⟨n, Or.inr ⟨h.1, h.2.1⟩, h.2.2, hall⟩

/-! ### Arithmetic -/

/-- Rational bounds on `(1 - 2^-b)^(2^b)`, `b = topZeroBits (l + 1)` (T51: `b = 0,0,1,1,2,3,4,5,6,7,8` for
`l = 0..10`; `b = 0` gives `0`). -/
noncomputable def capR (l : Nat) : ℝ :=
  if l ≤ 1 then 0 else if l ≤ 3 then 3165 / 10000 else if l = 4 then 3437 / 10000 else
    if l = 5 then 3561 / 10000 else if l = 6 then 3622 / 10000 else 36788 / 100000

theorem base_le_exp (h : Nat) : (1 - (1 / 2 : ℝ) ^ h) ^ (2 ^ h) ≤ 36788 / 100000 := by
  have hx0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ h := by
    have : (1 / 2 : ℝ) ^ h ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hx : 1 - (1 / 2 : ℝ) ^ h ≤ Real.exp (-(1 / 2) ^ h) := by
    linarith [Real.add_one_le_exp (-(1 / 2 : ℝ) ^ h)]
  calc (1 - (1 / 2 : ℝ) ^ h) ^ (2 ^ h) ≤ Real.exp (-(1 / 2) ^ h) ^ (2 ^ h) :=
        pow_le_pow_left₀ hx0 hx _
    _ = Real.exp (((2 ^ h : Nat) : ℝ) * (-(1 / 2) ^ h)) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-1) := by
        congr 1; push_cast; rw [one_div_pow, mul_neg, mul_one_div_cancel (by positivity)]
    _ ≤ 36788 / 100000 := by
        rw [Real.exp_neg]
        have he := Real.exp_one_gt_d9
        rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith

theorem failR_le (l : Nat) (r : ℝ)
    (hr : (1 - (1 / 2 : ℝ) ^ topZeroBits (l + 1)) ^ (2 ^ topZeroBits (l + 1)) ≤ r) :
    failR l ≤ r ^ 104 := by
  unfold failR
  have hx0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ topZeroBits (l + 1) := by
    have : (1 / 2 : ℝ) ^ topZeroBits (l + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  rw [mul_comm, pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg hx0 _) hr _

theorem failR_nonneg (l : Nat) : 0 ≤ failR l := by
  unfold failR
  apply pow_nonneg
  have : (1 / 2 : ℝ) ^ topZeroBits (l + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem sum_capR :
    ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * capR l ^ 104 ≤ 1 / 2 ^ 144 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, capR]
  norm_num

theorem sum_failR :
    ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * failR l ≤ 1 / 2 ^ 144 := by
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) sum_capR
  simp only [Finset.mem_range] at hl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply failR_le
  by_cases h8 : 7 ≤ l
  · have : capR l = 36788 / 100000 := by
      unfold capR; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    rw [this]; exact base_le_exp _
  · interval_cases l <;> norm_num [capR, topZeroBits, topZeroAlloc]

/-- U16b: the real cap-failure bound of a lower ground position, `(1 - 2^-b)^(128 · 2^b) ≤ 0.36788^128`. -/
theorem lowFail_le (b : Nat) : (1 - (1 / 2 : ℝ) ^ b) ^ (128 * 2 ^ b) ≤ (36788 / 100000 : ℝ) ^ 128 := by
  have hx0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ b := by
    have : (1 / 2 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  rw [mul_comm, pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg hx0 _) (base_le_exp b) _

theorem prob_lowFail_le (p : Extract.Pos) (lay heap : Nat) (S : Finset Node)
    (hS : S.card = 128 * 2 ^ WCT9.lowerZeroBits lay heap) :
    Pr[fun labels : Labels => ∀ a ∈ S,
        (fun v => WCT9.lowerZeroOk lay heap (p.proj v) = false) (labels a) |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
  classical
  refine (le_of_eq (prob_forall_mem (α := Node) (β := HashOutput) (inst := instSampleableTypeLabels_capFail)
    S (fun v => WCT9.lowerZeroOk lay heap (p.proj v) = false))).trans ?_
  rw [hS, Fintype.card_bitVec]
  have hb3 := lowerZeroBits_le_three lay heap
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (lowFail_le (WCT9.lowerZeroBits lay heap)))
  rw [ENNReal.ofReal_pow (by
    have : (1 / 2 : ℝ) ^ WCT9.lowerZeroBits lay heap ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)]
  gcongr
  have hf := card_fail_hash_low p lay heap
  have := ratio_le hf (by omega)
  convert this using 2

/-- U16b: one lower ground position exhausts its `128 · 2^b` trials with probability at most `0.36788^128`. -/
theorem prob_allFail_le_low (n : TreeNode) (hl : n.1.lay ≠ 0)
    (hb : WCT9.lowerZeroBits n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1)) ≠ 0) :
    Pr[fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
  classical
  have hev : (fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j) =
      (fun labels : Labels => ∀ a ∈ trialSet n,
        (fun v => WCT9.lowerZeroOk n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1))
          ((Node.node n).toPos.proj v) = false) (labels a)) := by
    funext labels
    have h := allFail_iff labels n
    unfold trialZeroOk at h
    simp only [if_neg hl] at h
    exact propext h
  rw [hev]
  apply prob_lowFail_le
  rw [trialSet_card, trialCap_lowerG hl hb]
  rfl

/-! ### E8: the FTS ground positions (`b = ftsZeroBits coord heap ∈ {1, 2}`, cap `128 · 2^b`)
Y7: the ground heaps are `8..15` (level 3) and `16..31` of coordinates `0..3` (level 2, `b = 1`); a trial's zero test
reads the used half of its label (`Extract.Paired.proj`, the high half on even heaps), i.e. the half of a legacy
position `p` (`wHalfPos`). -/

theorem ftsZeroBits_le_two (coord heap : Nat) : WCT9.ftsZeroBits coord heap ≤ 2 := by
  unfold WCT9.ftsZeroBits; split_ifs <;> omega

theorem card_pass_digest_fts (coord heap : Nat) :
    2 ^ (128 - WCT9.ftsZeroBits coord heap) ≤
      (Finset.univ.filter (fun d : BitVec 128 => WCT9.ftsZeroOk coord heap d = true)).card := by
  have hb := ftsZeroBits_le_two coord heap
  have hlt : 2 ^ (128 - WCT9.ftsZeroBits coord heap) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : (Finset.range (2 ^ (128 - WCT9.ftsZeroBits coord heap))).card = 2 ^ (128 - WCT9.ftsZeroBits coord heap) :=
    Finset.card_range _
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun x : Nat => (BitVec.ofNat 128 x : BitVec 128))
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio] at hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    unfold WCT9.ftsZeroOk
    simp only [BitVec.toNat_ofNat, beq_iff_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Nat.div_eq_of_lt hx
  · intro x hx y hy heq
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem card_fail_hash_fts (p : Extract.Pos) (coord heap : Nat) :
    (Finset.univ.filter (fun v : BitVec 256 =>
        WCT9.ftsZeroOk coord heap (p.proj v) = false)).card +
      2 ^ (256 - WCT9.ftsZeroBits coord heap) ≤ 2 ^ 256 := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitVec 256))) (fun v => WCT9.ftsZeroOk coord heap (p.proj v) = false)
  rw [Finset.card_univ, Fintype.card_bitVec] at hsum
  have := card_pass_hash_of p (WCT9.ftsZeroOk coord heap)
    (by have := ftsZeroBits_le_two coord heap; omega) (card_pass_digest_fts coord heap)
  change _ = 2 ^ 256 at hsum
  omega

theorem prob_ftsFail_le (p : Extract.Pos) (coord heap : Nat) (S : Finset Node)
    (hS : S.card = 128 * 2 ^ WCT9.ftsZeroBits coord heap) :
    Pr[fun labels : Labels => ∀ a ∈ S,
        (fun v => WCT9.ftsZeroOk coord heap (p.proj v) = false) (labels a) |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
  classical
  refine (le_of_eq (prob_forall_mem (α := Node) (β := HashOutput) (inst := instSampleableTypeLabels_capFail)
    S (fun v => WCT9.ftsZeroOk coord heap (p.proj v) = false))).trans ?_
  rw [hS, Fintype.card_bitVec]
  have hb := ftsZeroBits_le_two coord heap
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (lowFail_le (WCT9.ftsZeroBits coord heap)))
  rw [ENNReal.ofReal_pow (by
    have : (1 / 2 : ℝ) ^ WCT9.ftsZeroBits coord heap ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)]
  gcongr
  have hf := card_fail_hash_fts p coord heap
  have := ratio_le hf (by omega)
  convert this using 2

/-- Y7: a legacy position with the half of FTS node `m`'s paired projection (`forest 0`: low, `wctNode … 5 …`:
high). -/
def wHalfPos (m : WctNodePos) : Extract.Pos :=
  if Extract.Paired.highNodeAt m.1.coord.val m.1.level.val m.1.idx.val then .wctNode 0 0 5 0 else .forest 0

theorem pairedProj_wHalfPos (m : WctNodePos) :
    Extract.Paired.proj (Node.wctNode m).toPos = (wHalfPos m).proj := by
  funext v
  unfold wHalfPos
  by_cases h : Extract.Paired.highNodeAt m.1.coord.val m.1.level.val m.1.idx.val
  · rw [if_pos h, Extract.Pos.proj_eq]
    simp only [Node.toPos, Extract.Paired.proj, if_pos h, Extract.Pos.high]
    rfl
  · rw [if_neg h, Extract.Pos.proj_eq]
    simp only [Node.toPos, Extract.Paired.proj, if_neg h, Extract.Pos.high]
    rfl

/-- The cap trials of the FTS position of `m`. -/
def wTrialSet (m : WctNodePos) : Finset Node :=
  (Finset.range (wTrialCap m.1.coord.val m.1.level.val)).image (fun j => Node.wctNode (wWithNonce m j))

theorem wTrialSet_card (m : WctNodePos) : (wTrialSet m).card = wTrialCap m.1.coord.val m.1.level.val := by
  unfold wTrialSet
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hc := wTrialCap_le m.1.coord.val m.1.level.val
  have h := congrArg (fun x : WctNodePos => x.1.nonce.val) (Node.wctNode.inj hij)
  rwa [wWithNonce_nonce m (by omega), wWithNonce_nonce m (by omega)] at h

end CapFailBound
#print axioms CapFailBound.wTrialSet_card
end OuterCanonBase.Paired
