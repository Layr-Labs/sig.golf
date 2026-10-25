import SigGolfCandidate.ClaudeWCT_Numerics_Covariance

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (uniformWordAverage binomialAverage binomialAverage_succ binomialAverage_mono
  binomialAverage_sum binomialAverage_mul_left binomialAverage_mul_right)
open SigGolfResearch.Gate6.Moments (finiteAverage uniformWordAverage_succ)
open SigGolfCandidate.T3.BPORS.History (atIndex atIndex_cons jointCountAverage)
noncomputable def lawAvg {β : Type} [Fintype β] (v : β → ENNReal) : ℕ → (List β → ENNReal) → ENNReal
  | 0, f => f []
  | n + 1, f => ∑ b, v b * lawAvg v n (fun L => f (b :: L))
section Basic
variable {β : Type} [Fintype β] (v : β → ENNReal)
theorem lawAvg_zero (f : List β → ENNReal) : lawAvg v 0 f = f [] := rfl
theorem lawAvg_succ (n : ℕ) (f : List β → ENNReal) :
    lawAvg v (n + 1) f = ∑ b, v b * lawAvg v n (fun L => f (b :: L)) := rfl
theorem lawAvg_add (n : ℕ) (f g : List β → ENNReal) :
    lawAvg v n (fun L => f L + g L) = lawAvg v n f + lawAvg v n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [lawAvg_succ]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [ih, mul_add]
theorem lawAvg_mul_left (n : ℕ) (c : ENNReal) (f : List β → ENNReal) :
    lawAvg v n (fun L => c * f L) = c * lawAvg v n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [lawAvg_succ, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [ih]; ring
theorem lawAvg_sum {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → List β → ENNReal) :
    lawAvg v n (fun L => ∑ i ∈ s, f i L) = ∑ i ∈ s, lawAvg v n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [lawAvg_succ]
    simp_rw [ih, mul_sum]
    exact sum_comm
theorem lawAvg_mono (n : ℕ) {f g : List β → ENNReal} (h : ∀ L, f L ≤ g L) : lawAvg v n f ≤ lawAvg v n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih => exact sum_le_sum fun b _ => mul_le_mul' le_rfl (ih fun L => h (b :: L))
theorem lawAvg_const (hv : ∑ b, v b = 1) (n : ℕ) (c : ENNReal) : lawAvg v n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lawAvg_succ]; simp only [ih]; rw [← sum_mul, hv, one_mul]
theorem lawAvg_steps_mono (hv : ∑ b, v b = 1) (f : List β → ENNReal) (hf : ∀ a L, f L ≤ f (a :: L)) :
    Monotone (fun n => lawAvg v n f) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show lawAvg v n f ≤ lawAvg v (n + 1) f
  rw [lawAvg_succ]
  calc lawAvg v n f = ∑ b, v b * lawAvg v n f := by rw [← sum_mul, hv, one_mul]
    _ ≤ ∑ b, v b * lawAvg v n (fun L => f (b :: L)) :=
      sum_le_sum fun b _ => mul_le_mul' le_rfl (lawAvg_mono v n fun L => hf b L)
omit [Fintype β] in
theorem uniformWordAverage_zero' [SampleableType β] (f : List β → ENNReal) : uniformWordAverage 0 f = f [] := by
  simp [uniformWordAverage, SphincsSecurity.Concrete.sampleUniformProposalWord]
theorem lawAvg_le_uniform [SampleableType β] (κ : ENNReal) (hv : ∀ b, v b ≤ κ * (Fintype.card β : ENNReal)⁻¹)
    (n : ℕ) (f : List β → ENNReal) : lawAvg v n f ≤ κ ^ n * uniformWordAverage n f := by
  induction n generalizing f with
  | zero => rw [pow_zero, one_mul, uniformWordAverage_zero']; exact le_rfl
  | succ n ih =>
    rw [lawAvg_succ, uniformWordAverage_succ, finiteAverage]
    calc ∑ b, v b * lawAvg v n (fun L => f (b :: L))
        ≤ ∑ b, κ * (Fintype.card β : ENNReal)⁻¹ * (κ ^ n * uniformWordAverage n (fun L => f (b :: L))) :=
          sum_le_sum fun b _ => mul_le_mul' (hv b) (ih _)
      _ = κ ^ (n + 1) * ((∑ b, uniformWordAverage n (fun L => f (b :: L))) / (Fintype.card β : ENNReal)) := by
          simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
          refine sum_congr rfl fun b _ => ?_
          ring
end Basic
section Marked
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] (v : β → ENNReal)
noncomputable def marked (p : α × β) : ENNReal := (Fintype.card α : ENNReal)⁻¹ * v p.2
theorem sum_marked {α' : Type} [Fintype α'] [DecidableEq α'] (F : α' × β → ENNReal) :
    ∑ p, marked v p * F p = ∑ a, (Fintype.card α' : ENNReal)⁻¹ * ∑ b, v b * F (a, b) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  simp only [marked]; ring
theorem marked_sum_one [Nonempty α] (hv : ∑ b, v b = 1) : ∑ p, marked (α := α) v p = 1 := by
  have h := sum_marked v (α' := α) (fun _ => (1 : ENNReal))
  simp only [mul_one] at h
  rw [h, hv, mul_one, sum_const, card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by simpa using Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
theorem binomialAverage_lawSum (rate : ENNReal) (T : ℕ) (g : β → ℕ → ENNReal) :
    ∑ b, v b * binomialAverage rate T (g b) = binomialAverage rate T (fun r => ∑ b, v b * g b r) := by
  rw [binomialAverage_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [binomialAverage_mul_left]
omit [Fintype α] [Fintype β] in
theorem atIndex_cons_self (index : α) (b : β) (word : List (α × β)) :
    atIndex index ((index, b) :: word) = b :: atIndex index word := by
  rw [atIndex_cons]; simp
omit [Fintype α] [Fintype β] in
theorem atIndex_cons_ne {index a : α} (h : a ≠ index) (b : β) (word : List (α × β)) :
    atIndex index ((a, b) :: word) = atIndex index word := by
  rw [atIndex_cons]; simp [h]
theorem sum_inv_ite [Nonempty α] (index : α) (X Y : ENNReal) :
    ∑ a : α, (Fintype.card α : ENNReal)⁻¹ * (if a = index then X else Y) =
      (1 - (Fintype.card α : ENNReal)⁻¹) * Y + (Fintype.card α : ENNReal)⁻¹ * X := by
  set p : ENNReal := (Fintype.card α : ENNReal)⁻¹ with hp
  have hc : (Fintype.card α : ENNReal) ≠ 0 := by simpa using Fintype.card_ne_zero
  have hc' : (Fintype.card α : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← add_sum_erase _ _ (mem_univ index), if_pos rfl]
  have hrest : ∑ a ∈ univ.erase index, p * (if a = index then X else Y) = ((Fintype.card α - 1 : ℕ) : ENNReal) * (p * Y) := by
    rw [sum_congr rfl fun a ha => by rw [if_neg (ne_of_mem_erase ha)], sum_const, card_erase_of_mem (mem_univ _),
      card_univ, nsmul_eq_mul]
  rw [hrest]
  have hk : ((Fintype.card α - 1 : ℕ) : ENNReal) * p = 1 - p := by
    have hpos := Fintype.card_pos (α := α)
    have h1 : ((Fintype.card α - 1 : ℕ) : ENNReal) + 1 = Fintype.card α := by
      norm_cast; omega
    have h2 : ((Fintype.card α - 1 : ℕ) : ENNReal) * p + p = 1 := by
      rw [← add_one_mul, h1, hp, ENNReal.mul_inv_cancel hc hc']
    rw [← h2, ENNReal.add_sub_cancel_right (by simp [hp, hc])]
  rw [← mul_assoc, hk]
  ring
theorem law_marked_atIndex [Nonempty α] (hv : ∑ b, v b = 1) (index : α) (T : ℕ) (payoff : List β → ENNReal) :
    lawAvg (marked (α := α) v) T (fun word : List (α × β) => payoff (atIndex index word)) =
      binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v r payoff) := by
  induction T generalizing payoff with
  | zero => simp [lawAvg_zero, atIndex, binomialAverage]
  | succ T ih =>
    rw [lawAvg_succ, sum_marked, binomialAverage_succ]
    have hrow : ∀ a : α, ∑ b, v b * lawAvg (marked (α := α) v) T
        (fun word => payoff (atIndex index ((a, b) :: word))) =
        if a = index then binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v (r + 1) payoff)
        else binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v r payoff) := by
      intro a
      by_cases ha : a = index
      · rw [if_pos ha]
        subst ha
        simp_rw [atIndex_cons_self]
        have hb : ∀ b, lawAvg (marked (α := α) v) T (fun word => payoff (b :: atIndex a word)) =
            binomialAverage (Fintype.card α : ENNReal)⁻¹ T (fun r => lawAvg v r (fun L => payoff (b :: L))) :=
          fun b => ih (fun L => payoff (b :: L))
        simp_rw [hb]
        rw [binomialAverage_lawSum]
        rfl
      · rw [if_neg ha]
        simp_rw [atIndex_cons_ne ha]
        rw [ih, ← sum_mul, hv, one_mul]
    simp_rw [hrow]
    exact sum_inv_ite index _ _
theorem jca_lawSum (first second : α) (T : ℕ) (P : β → ℕ → ℕ → ENNReal) :
    ∑ b, v b * jointCountAverage first second T (P b) =
      jointCountAverage first second T (fun i j => ∑ b, v b * P b i j) := by
  induction T generalizing P with
  | zero => rfl
  | succ T ih =>
    simp only [jointCountAverage, finiteAverage]
    simp_rw [div_eq_mul_inv, ← mul_assoc, ← sum_mul, mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    split_ifs
    · exact ih (fun b i j => P b (i + 1) j)
    · exact ih (fun b i j => P b i (j + 1))
    · exact ih P
theorem law_marked_joint [Nonempty α] (hv : ∑ b, v b = 1) (first second : α) (hne : first ≠ second) (T : ℕ)
    (f g : List β → ENNReal) :
    lawAvg (marked (α := α) v) T (fun word : List (α × β) => f (atIndex first word) * g (atIndex second word)) =
      jointCountAverage first second T (fun i j => lawAvg v i f * lawAvg v j g) := by
  induction T generalizing f g with
  | zero => simp [lawAvg_zero, atIndex, jointCountAverage]
  | succ T ih =>
    rw [lawAvg_succ, sum_marked]
    show _ = finiteAverage _
    unfold finiteAverage
    rw [div_eq_mul_inv, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_comm]
    congr 1
    by_cases hf : a = first
    · subst hf
      rw [if_pos rfl]
      simp_rw [atIndex_cons_self, atIndex_cons_ne hne]
      have hb : ∀ b, lawAvg (marked (α := α) v) T
          (fun word => f (b :: atIndex a word) * g (atIndex second word)) =
          jointCountAverage a second T (fun i j => lawAvg v i (fun L => f (b :: L)) * lawAvg v j g) :=
        fun b => ih (fun L => f (b :: L)) g
      simp_rw [hb]
      rw [jca_lawSum]
      simp_rw [← mul_assoc, ← sum_mul]
      rfl
    · rw [if_neg hf]
      by_cases hs : a = second
      · subst hs
        rw [if_pos rfl]
        simp_rw [atIndex_cons_self, atIndex_cons_ne hf]
        have hb : ∀ b, lawAvg (marked (α := α) v) T
            (fun word => f (atIndex first word) * g (b :: atIndex a word)) =
            jointCountAverage first a T (fun i j => lawAvg v i f * lawAvg v j (fun L => g (b :: L))) :=
          fun b => ih f (fun L => g (b :: L))
        simp_rw [hb]
        rw [jca_lawSum]
        simp_rw [mul_left_comm _ (lawAvg v _ f), ← mul_sum]
        rfl
      · rw [if_neg hs]
        simp_rw [atIndex_cons_ne hf, atIndex_cons_ne hs]
        rw [ih, ← sum_mul, hv, one_mul]
theorem law_marked_negative_correlation [Nonempty α] (hv : ∑ b, v b = 1) (first second : α)
    (hne : first ≠ second) (T : ℕ) (f g : List β → ENNReal) (hf : ∀ a L, f L ≤ f (a :: L))
    (hg : ∀ a L, g L ≤ g (a :: L)) :
    lawAvg (marked (α := α) v) T (fun word : List (α × β) => f (atIndex first word) * g (atIndex second word)) ≤
      lawAvg (marked (α := α) v) T (fun word : List (α × β) => f (atIndex first word)) *
        lawAvg (marked (α := α) v) T (fun word : List (α × β) => g (atIndex second word)) := by
  rw [law_marked_joint v hv first second hne, law_marked_atIndex v hv, law_marked_atIndex v hv]
  exact ClaudeWCT.Numerics.Covariance.joint_pair_bound first second hne T _ _
    (lawAvg_steps_mono v hv f hf) (lawAvg_steps_mono v hv g hg)
end Marked
section Square
variable {γ : Type} [Fintype γ] (w : γ → ENNReal)
theorem lawAvg_sum_square_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : ℕ) (payoff : ι → List γ → ENNReal)
    (hcross : ∀ first second, first ≠ second →
      lawAvg w T (fun word => payoff first word * payoff second word) ≤
        lawAvg w T (payoff first) * lawAvg w T (payoff second)) :
    lawAvg w T (fun word => (∑ index, payoff index word) ^ 2) ≤
      (∑ index, lawAvg w T (payoff index)) ^ 2 + ∑ index, lawAvg w T (fun word => payoff index word ^ 2) := by
  calc
    _ = ∑ first, ∑ second, lawAvg w T (fun word => payoff first word * payoff second word) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [lawAvg_sum]
      simp_rw [lawAvg_sum]
      exact Finset.sum_comm
    _ ≤ ∑ first, ∑ second,
        (lawAvg w T (payoff first) * lawAvg w T (payoff second) +
          if second = first then lawAvg w T (fun word => payoff first word ^ 2) else 0) := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      by_cases heq : first = second
      · subst second
        simp only [↓reduceIte, pow_two]
        exact le_add_self
      · simpa only [if_neg (Ne.symm heq), add_zero] using hcross first second heq
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        pow_two, Finset.sum_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
end Square
section Uniform
variable {β : Type} [Fintype β] [SampleableType β]
theorem lawAvg_uniform (n : ℕ) (f : List β → ENNReal) :
    lawAvg (fun _ => (Fintype.card β : ENNReal)⁻¹) n f = uniformWordAverage n f := by
  induction n generalizing f with
  | zero => rw [lawAvg_zero, uniformWordAverage_zero']
  | succ n ih =>
    rw [lawAvg_succ, uniformWordAverage_succ, finiteAverage, div_eq_mul_inv, sum_mul]
    refine sum_congr rfl fun b _ => ?_
    rw [ih, mul_comm]
end Uniform
end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset

/-- The constant and singleton terms in a nonnegative product expansion. -/
theorem prod_linear_terms_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a d : ι → ENNReal) :
    (∏ i ∈ s, a i) + ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j ≤ ∏ i ∈ s, (a i + d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    have hterm : ∀ i ∈ s, d i * ∏ j ∈ (insert k s).erase i, a j =
        a k * (d i * ∏ j ∈ s.erase i, a j) := by
      intro i hi
      have hki : k ≠ i := fun h => hk (h ▸ hi)
      rw [Finset.erase_insert_of_ne hki, Finset.prod_insert]
      · ring
      · exact fun h => hk (Finset.mem_of_mem_erase h)
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.erase_insert_eq_erase,
      Finset.erase_eq_of_notMem hk, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      Finset.prod_insert hk]
    calc
      a k * (∏ i ∈ s, a i) + (d k * (∏ j ∈ s, a j) + a k * ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j)
          = a k * ((∏ i ∈ s, a i) + ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j) +
            d k * (∏ j ∈ s, a j) := by ring
      _ ≤ a k * (∏ i ∈ s, (a i + d i)) + d k * (∏ i ∈ s, (a i + d i)) :=
        add_le_add (mul_le_mul' le_rfl ih)
          (mul_le_mul' le_rfl (Finset.prod_le_prod' fun _ _ => le_self_add))
      _ = _ := by ring

/-- Mixing one coordinate at a time is bounded by independent coordinate mixtures. -/
theorem exclusive_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ENNReal) (hp : p ≤ 1) (hcard : (Fintype.card ι : ENNReal) * p = 1)
    (a b : ι → ENNReal) (hab : ∀ i, a i ≤ b i) :
    ∑ i, p * (b i * ∏ j ∈ Finset.univ.erase i, a j) ≤
      ∏ i, ((1 - p) * a i + p * b i) := by
  choose d hd using fun i => exists_add_of_le (hab i)
  have hbase : ∀ i, a i * ∏ j ∈ Finset.univ.erase i, a j = ∏ j, a j :=
    fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmix : ∀ i, (1 - p) * a i + p * b i = a i + p * d i := by
    intro i
    rw [hd i, mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hp, one_mul]
  simp_rw [hmix, hd, add_mul, mul_add, hbase]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, hcard, one_mul]
  simpa only [mul_assoc] using prod_linear_terms_le Finset.univ a (fun i => p * d i)

end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (binomialAverage binomialAverage_succ binomialAverage_mono)
open SigGolfCandidate.T3.BPORS.History (atIndex atIndex_cons)

noncomputable def coordAverage {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) (f : List β → ENNReal) : ENNReal :=
  binomialAverage p T (fun r => lawAvg v r f)

theorem coordAverage_mono {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) {f g : List β → ENNReal} (h : ∀ L, f L ≤ g L) :
    coordAverage p v T f ≤ coordAverage p v T g :=
  binomialAverage_mono p T fun r => lawAvg_mono v r h

theorem coordAverage_succ {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) (f : List β → ENNReal) :
    coordAverage p v (T + 1) f = (1 - p) * coordAverage p v T f +
      p * ∑ b, v b * coordAverage p v T (fun L => f (b :: L)) := by
  unfold coordAverage
  rw [binomialAverage_succ, binomialAverage_lawSum]
  rfl

/-- Product negative dependence for marked buckets.  The insertion condition allows
arbitrary symmetric monotone bucket statistics, including capped coverage prices. -/
theorem law_marked_product_le {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (f : α → List β → ENNReal)
    (hf : ∀ i L b R, f i (L ++ R) ≤ f i (L ++ b :: R)) :
    lawAvg (marked (α := α) v) T (fun W => ∏ i, f i (atIndex i W)) ≤
      ∏ i, coordAverage (Fintype.card α : ENNReal)⁻¹ v T (f i) := by
  set p : ENNReal := (Fintype.card α : ENNReal)⁻¹ with hp
  have hp1 : p ≤ 1 := by
    rw [hp]
    exact ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos (α := α))
  have hcard : (Fintype.card α : ENNReal) * p = 1 := by
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)
  induction T generalizing f with
  | zero => simp [lawAvg_zero, coordAverage, binomialAverage, atIndex]
  | succ T ih =>
    let A : α → ENNReal := fun i => coordAverage p v T (f i)
    let B : α → ENNReal := fun i => ∑ b, v b * coordAverage p v T (fun L => f i (b :: L))
    have hAB : ∀ i, A i ≤ B i := by
      intro i
      calc A i = ∑ b, v b * A i := by rw [← Finset.sum_mul, hv, one_mul]
        _ ≤ B i := Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl
          (coordAverage_mono p v T fun L => by simpa using hf i [] b L)
    have hnext : ∀ a b,
        lawAvg (marked (α := α) v) T (fun W => ∏ i, f i (atIndex i ((a, b) :: W))) ≤
          coordAverage p v T (fun L => f a (b :: L)) * ∏ j ∈ Finset.univ.erase a, A j := by
      intro a b
      let g : α → List β → ENNReal := fun i L => if i = a then f i (b :: L) else f i L
      have hg : ∀ i L c R, g i (L ++ R) ≤ g i (L ++ c :: R) := by
        intro i L c R
        by_cases hi : i = a
        · simpa only [g, if_pos hi, List.cons_append] using hf i (b :: L) c R
        · simpa only [g, if_neg hi] using hf i L c R
      have hpoint : (fun W => ∏ i, f i (atIndex i ((a, b) :: W))) =
          (fun W => ∏ i, g i (atIndex i W)) := by
        funext W
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i = a
        · subst i; simp [g, atIndex_cons]
        · simp [g, atIndex_cons, hi, Ne.symm hi]
      rw [hpoint]
      refine (ih g hg).trans_eq ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
      congr 1
      · simp [g]
      · apply Finset.prod_congr rfl
        intro i hi
        simp only [g, if_neg (Finset.ne_of_mem_erase hi)]
        rfl
    rw [lawAvg_succ, sum_marked]
    calc
      (∑ a : α, (Fintype.card α : ENNReal)⁻¹ * ∑ b, v b *
        lawAvg (marked (α := α) v) T (fun W => ∏ i, f i (atIndex i ((a,b) :: W))))
          ≤ ∑ a, p * ∑ b, v b *
            (coordAverage p v T (fun L => f a (b :: L)) * ∏ j ∈ Finset.univ.erase a, A j) :=
        Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl
          (Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (hnext a b))
      _ = ∑ a, p * (B a * ∏ j ∈ Finset.univ.erase a, A j) := by
        simp only [B, Finset.sum_mul, mul_assoc]
      _ ≤ ∏ i, ((1-p) * A i + p * B i) := exclusive_prod_le p hp1 hcard A B hAB
      _ = ∏ i, coordAverage p v (T+1) (f i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (coordAverage_succ p v T (f i)).symm

end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (binomialAverage binomialAverage_add binomialAverage_const)

theorem coordAverage_add {β : Type} [Fintype β] (p : ENNReal) (v : β → ENNReal)
    (T : ℕ) (f g : List β → ENNReal) :
    coordAverage p v T (fun L => f L + g L) = coordAverage p v T f + coordAverage p v T g := by
  unfold coordAverage
  simp_rw [lawAvg_add]
  exact binomialAverage_add p T _ _

theorem coordAverage_const {β : Type} [Fintype β] (p : ENNReal) (hp : p ≤ 1)
    (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ) (c : ENNReal) :
    coordAverage p v T (fun _ => c) = c := by
  unfold coordAverage
  simp_rw [lawAvg_const v hv]
  exact binomialAverage_const hp T c

/-- A convenient exponential-moment consequence of bucket product dependence. -/
theorem law_marked_exp_sum_le {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (Y : α → List β → ENNReal)
    (hY : ∀ i L, Y i L ≤ 1)
    (hmono : ∀ i L b R, Y i (L ++ R) ≤ Y i (L ++ b :: R))
    (hinc : (∑ i, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (8 * (Y i L).toReal)) - 1)) ≤ 8) :
    lawAvg (marked (α := α) v) T (fun W =>
      ENNReal.ofReal (Real.exp (8 * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) ≤
      ENNReal.ofReal (Real.exp 8) := by
  let p : ENNReal := (Fintype.card α : ENNReal)⁻¹
  have hp : p ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos (α := α))
  let F : α → List β → ENNReal := fun i L => ENNReal.ofReal (Real.exp (8 * (Y i L).toReal))
  let M : α → ENNReal := fun i => coordAverage p v T (fun L => F i L - 1)
  have hfin : ∀ i L, Y i L ≠ ⊤ := fun i L => ne_top_of_le_ne_top ENNReal.one_ne_top (hY i L)
  have hF1 : ∀ i L, 1 ≤ F i L := by
    intro i L
    apply ENNReal.one_le_ofReal.mpr
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hFmono : ∀ i L b R, F i (L ++ R) ≤ F i (L ++ b :: R) := by
    intro i L b R
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hfin i _) (hmono i L b R)) (by norm_num)
  have hM : ∑ i, M i ≤ 8 := hinc
  have hMi : ∀ i, M i ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (by finiteness)
      ((Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans hM)
  have hMF : ∀ i, coordAverage p v T (F i) = 1 + M i := by
    intro i
    have heq : F i = fun L => 1 + (F i L - 1) := by
      funext L
      exact (add_tsub_cancel_of_le (hF1 i L)).symm
    rw [heq, coordAverage_add, coordAverage_const p hp v hv]
  have hprod : ∏ i, (1 + M i) ≤ ENNReal.ofReal (Real.exp 8) := by
    calc
      (∏ i, (1 + M i)) ≤ ∏ i, ENNReal.ofReal (Real.exp (M i).toReal) := by
        apply Finset.prod_le_prod'
        intro i _
        rw [← ENNReal.ofReal_toReal (hMi i), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        simpa [add_comm] using Real.add_one_le_exp (M i).toReal
      _ = ENNReal.ofReal (Real.exp ((∑ i, M i).toReal)) := by
        rw [ENNReal.toReal_sum (fun i _ => hMi i), Real.exp_sum,
          ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
      _ ≤ ENNReal.ofReal (Real.exp 8) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        simpa using ENNReal.toReal_mono (by finiteness : (8 : ENNReal) ≠ ⊤) hM
  have heq : (fun W => ENNReal.ofReal (Real.exp
      (8 * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) =
      (fun W => ∏ i, F i (SigGolfCandidate.T3.BPORS.History.atIndex i W)) := by
    funext W
    rw [ENNReal.toReal_sum (fun i _ => hfin i _), Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rw [heq]
  refine (law_marked_product_le v hv T F hFmono).trans ?_
  change (∏ i, coordAverage p v T (F i)) ≤ _
  simpa only [hMF] using hprod

end ClaudeWCT.Numerics.Law

/-! Variable exponential slope and moment budget for paired forest pricing. -/
namespace ClaudeWCT.Numerics.Law
open ENNReal Finset
open SphincsSecurity.Concrete (binomialAverage binomialAverage_add binomialAverage_const)

theorem law_marked_exp_sum_general {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (v : β → ENNReal) (hv : ∑ b, v b = 1) (T : ℕ)
    (Y : α → List β → ENNReal) (t bound : ℝ)
    (ht : 0 ≤ t) (hbound : 0 ≤ bound)
    (hY : ∀ i L, Y i L ≠ ⊤)
    (hmono : ∀ i L b R, Y i (L ++ R) ≤ Y i (L ++ b :: R))
    (hinc : (∑ i, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (t * (Y i L).toReal)) - 1)) ≤ ENNReal.ofReal bound) :
    lawAvg (marked (α := α) v) T (fun W =>
      ENNReal.ofReal (Real.exp (t * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) ≤
      ENNReal.ofReal (Real.exp bound) := by
  let p : ENNReal := (Fintype.card α : ENNReal)⁻¹
  have hp : p ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos (α := α))
  let F : α → List β → ENNReal := fun i L => ENNReal.ofReal (Real.exp (t * (Y i L).toReal))
  let M : α → ENNReal := fun i => coordAverage p v T (fun L => F i L - 1)
  have hfin : ∀ i L, Y i L ≠ ⊤ := hY
  have hF1 : ∀ i L, 1 ≤ F i L := by
    intro i L
    apply ENNReal.one_le_ofReal.mpr
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hFmono : ∀ i L b R, F i (L ++ R) ≤ F i (L ++ b :: R) := by
    intro i L b R
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hfin i _) (hmono i L b R)) ht
  have hM : ∑ i, M i ≤ ENNReal.ofReal bound := hinc
  have hMi : ∀ i, M i ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (by finiteness)
      ((Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans hM)
  have hMF : ∀ i, coordAverage p v T (F i) = 1 + M i := by
    intro i
    have heq : F i = fun L => 1 + (F i L - 1) := by
      funext L
      exact (add_tsub_cancel_of_le (hF1 i L)).symm
    rw [heq, coordAverage_add, coordAverage_const p hp v hv]
  have hprod : ∏ i, (1 + M i) ≤ ENNReal.ofReal (Real.exp bound) := by
    calc
      (∏ i, (1 + M i)) ≤ ∏ i, ENNReal.ofReal (Real.exp (M i).toReal) := by
        apply Finset.prod_le_prod'
        intro i _
        rw [← ENNReal.ofReal_toReal (hMi i), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        simpa [add_comm] using Real.add_one_le_exp (M i).toReal
      _ = ENNReal.ofReal (Real.exp ((∑ i, M i).toReal)) := by
        rw [ENNReal.toReal_sum (fun i _ => hMi i), Real.exp_sum,
          ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
      _ ≤ ENNReal.ofReal (Real.exp bound) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        simpa only [ENNReal.toReal_ofReal hbound] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hM
  have heq : (fun W => ENNReal.ofReal (Real.exp
      (t * (∑ i, Y i (SigGolfCandidate.T3.BPORS.History.atIndex i W)).toReal))) =
      (fun W => ∏ i, F i (SigGolfCandidate.T3.BPORS.History.atIndex i W)) := by
    funext W
    rw [ENNReal.toReal_sum (fun i _ => hfin i _), Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rw [heq]
  refine (law_marked_product_le v hv T F hFmono).trans ?_
  change (∏ i, coordAverage p v T (F i)) ≤ _
  simpa only [hMF] using hprod

end ClaudeWCT.Numerics.Law
