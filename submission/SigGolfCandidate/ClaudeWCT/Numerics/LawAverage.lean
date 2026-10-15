import SigGolfCandidate.ClaudeWCT.Numerics.Covariance

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
