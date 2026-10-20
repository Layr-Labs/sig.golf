import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_CanonGraph

/-! # Top-nonce layer: the cap-failure event is negligible (r3-lean-nonsec, subagent C)

`CapFail labels`: some top position (layer 0, children level `< 11`, nonce-0 representative) has every one of its
`trialCap = 104 · 2^h` nonce trials failing the zero test of height `h = level + 1`. Under uniformly random labels the
trials of one position are distinct nodes, so each fails independently with probability at most `1 - 2^-h`; a union
bound over the `2^(12-h)` positions of each height gives `Pr[CapFail] ≤ 2^-142`. -/
namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable

/-- Some top position exhausts its nonce cap: every trial inside the cap fails the zero test. -/
def CapFail (labels : Labels) : Prop :=
  ∃ n : TreeNode, n.1.lay = 0 ∧ n.1.level.val < 11 ∧ n.1.nonce.val = 0 ∧
    ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j

noncomputable local instance instSampleableTypeLabels_capFail : SampleableType Labels :=
  SampleableType.ofFintype _

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

theorem topZeroBits_eq {h : Nat} (hh : h ≤ 11) : topZeroBits h = h := by
  interval_cases h <;> rfl

theorem card_pass_digest {h : Nat} (h11 : h ≤ 11) :
    2 ^ (128 - h) ≤
      (Finset.univ.filter (fun d : BitVec 128 => topZeroOk h d = true)).card := by
  by_cases he : h = 11
  · subst he
    have hc : ((Finset.range (2 ^ 19)) ×ˢ (Finset.range (2 ^ 98))).card = 2 ^ (128 - 11) := by
      rw [Finset.card_product, Finset.card_range, Finset.card_range]; norm_num
    rw [← hc]
    apply Finset.card_le_card_of_injOn (fun p : Nat × Nat => (BitVec.ofNat 128 (p.1 * 2 ^ 109 + p.2) :
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
  · have hlt : 2 ^ (128 - h) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
    have hc : (Finset.range (2 ^ (128 - h))).card = 2 ^ (128 - h) := Finset.card_range _
    rw [← hc]
    apply Finset.card_le_card_of_injOn (fun x : Nat => (BitVec.ofNat 128 x : BitVec 128))
    · intro x hx
      simp only [Finset.coe_range, Set.mem_Iio] at hx
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      unfold topZeroOk
      rw [if_neg he, topZeroBits_eq h11]
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
    2 ^ (256 - h) ≤
      (Finset.univ.filter (fun v : BitVec 256 => ¬ (topZeroOk h (p.proj v) = false))).card := by
  set P := Finset.univ.filter (fun d : BitVec 128 => topZeroOk h d = true)
  have hP := card_pass_digest h11
  have hcard : (P ×ˢ (Finset.univ : Finset (BitVec 128))).card = P.card * 2 ^ 128 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bitVec]
  have h256 : 2 ^ (256 - h) ≤ P.card * 2 ^ 128 := by
    calc 2 ^ (256 - h) = 2 ^ (128 - h) * 2 ^ 128 := by rw [← pow_add, show 128 - h + 128 = 256 - h by omega]
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
      2 ^ (256 - h) ≤ 2 ^ 256 := by
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
      ∀ a ∈ trialSet n, topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj (labels a)) = false := by
  unfold trialSet
  constructor
  · intro h a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact h j (Finset.mem_range.mp hj)
  · intro h j hj
    exact h _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)

theorem trialCap_top {lay : Layer} {level : Nat} (hl : lay = 0) (hlev : level < 11) :
    trialCap lay level = 104 * 2 ^ (level + 1) := by
  unfold trialCap topNonceCap
  rw [if_pos ⟨hl, hlev⟩, topZeroBits_eq (by omega)]

/-- The real cap-failure bound of one position at children level `l`. -/
noncomputable def failR (l : Nat) : ℝ := (1 - (1 / 2) ^ (l + 1)) ^ (104 * 2 ^ (l + 1))

theorem prob_allFail_le (n : TreeNode) (hl : n.1.lay = 0) (hlev : n.1.level.val < 11) :
    Pr[fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal (failR n.1.level.val) := by
  classical
  have hev : (fun labels : Labels => ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j) =
      (fun labels : Labels => ∀ a ∈ trialSet n,
        (fun v => topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj v) = false) (labels a)) := by
    funext labels; exact propext (allFail_iff labels n)
  rw [hev]
  refine (le_of_eq (prob_forall_mem (α := Node) (β := HashOutput) (inst := instSampleableTypeLabels_capFail)
    (trialSet n) (fun v => topZeroOk (n.1.level.val + 1) ((Node.node n).toPos.proj v) = false))).trans ?_
  rw [trialSet_card, trialCap_top hl hlev, Fintype.card_bitVec]
  unfold failR
  rw [ENNReal.ofReal_pow (by
    have : (1 / 2 : ℝ) ^ (n.1.level.val + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)]
  gcongr
  have hf := card_fail_hash (Node.node n).toPos (h := n.1.level.val + 1) (by omega)
  have := ratio_le hf (by omega)
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

theorem capFail_eq :
    CapFail = fun labels : Labels =>
      ∃ n ∈ topReps, ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j := by
  funext labels
  simp only [CapFail, topReps, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]

/-! ### Arithmetic -/

/-- Rational bounds on `(1 - 2^-h)^(2^h)`, `h = l + 1`. -/
noncomputable def capR (l : Nat) : ℝ :=
  if l = 0 then 1 / 4 else if l = 1 then 3165 / 10000 else if l = 2 then 3437 / 10000 else
    if l = 3 then 3561 / 10000 else if l = 4 then 3622 / 10000 else 36788 / 100000

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

theorem failR_le (l : Nat) (r : ℝ) (hr : (1 - (1 / 2 : ℝ) ^ (l + 1)) ^ (2 ^ (l + 1)) ≤ r) :
    failR l ≤ r ^ 104 := by
  unfold failR
  have hx0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ (l + 1) := by
    have : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  rw [mul_comm, pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg hx0 _) hr _

theorem failR_nonneg (l : Nat) : 0 ≤ failR l := by
  unfold failR
  apply pow_nonneg
  have : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem sum_capR :
    ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * capR l ^ 104 ≤ 1 / 2 ^ 142 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, capR]
  norm_num

theorem sum_failR :
    ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * failR l ≤ 1 / 2 ^ 142 := by
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) sum_capR
  simp only [Finset.mem_range] at hl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply failR_le
  by_cases h5 : 5 ≤ l
  · have : capR l = 36788 / 100000 := by
      unfold capR; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    rw [this]; exact base_le_exp _
  · interval_cases l <;> norm_num [capR]

end CapFailBound

open CapFailBound in
/-- **Cap failure is negligible**: under uniformly random labels, some top position exhausts its nonce cap with
probability at most `2^-142`. -/
theorem prob_capFail_le :
    Pr[CapFail | ($ᵗ Labels : ProbComp Labels)] ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  rw [capFail_eq]
  refine (probEvent_exists_finset_le_sum topReps _ _).trans ?_
  calc ∑ n ∈ topReps, Pr[fun labels : Labels =>
          ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j | ($ᵗ Labels : ProbComp Labels)]
      ≤ ∑ n ∈ topReps, ENNReal.ofReal (failR n.1.level.val) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [topReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        exact prob_allFail_le n hn.1 hn.2.1
    _ = ∑ l ∈ Finset.range 11, ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l),
          ENNReal.ofReal (failR n.1.level.val) := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro n hn
        simp only [topReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        exact Finset.mem_range.mpr hn.2.1
    _ ≤ ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ≥0∞) * ENNReal.ofReal (failR l) := by
        apply Finset.sum_le_sum
        intro l _
        have hfib := card_fiber_le l
        calc ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l), ENNReal.ofReal (failR n.1.level.val)
            = ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l), ENNReal.ofReal (failR l) :=
              Finset.sum_congr rfl (fun n hn => by simp only [Finset.mem_filter] at hn; rw [hn.2])
          _ = ((topReps.filter (fun n : TreeNode => n.1.level.val = l)).card : ℝ≥0∞) *
                ENNReal.ofReal (failR l) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by gcongr
    _ = ENNReal.ofReal (∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * failR l) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (by positivity) (failR_nonneg l))]
        apply Finset.sum_congr rfl
        intro l _
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 142) := ENNReal.ofReal_le_ofReal sum_failR
    _ = (2 ^ 142 : ℝ≥0∞)⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]

#print axioms prob_capFail_le

end ClaudeWCT.W9.T3.Security.CanonGraph
