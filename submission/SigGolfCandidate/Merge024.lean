import Mathlib.Data.List.Sort
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.IrreducibleDef
import SigGolfCandidate.Merge005
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge022
import SigGolfCandidate.Merge023

-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeSignerView ====
section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
def selectedFewTimeView (index : Index) (leaves : IndexGroup → FtsLeaf) : FewTimeView :=
  (index, leaves)
noncomputable def signWithView (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature × Option FewTimeView) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => pure (none, none)
  | some (randomness, index, leaves) => do
      let signature ← liftM (signAfterDigest secretKey randomness index leaves)
      pure (signature, some (selectedFewTimeView index leaves))
theorem signWithView_fst (secretKey : SecretKey) (message : Message) :
    Prod.fst <$> signWithView secretKey message = sign secretKey message := by
  rw [sign_eq_digestLoop_afterDigest]
  simp only [signWithView, map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro loopResult
  cases loopResult with
  | none => simp
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      simp
theorem simulateQ_signWithView_fst_run (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$>
        (simulateQ romImpl (signWithView secretKey message)).run cache =
      (simulateQ romImpl (sign secretKey message)).run cache := by
  calc
    _ = (simulateQ romImpl (Prod.fst <$> signWithView secretKey message)).run cache := by
      rw [simulateQ_map, StateT.run_map]
    _ = _ := by rw [signWithView_fst]
set_option linter.constructorNameAsVariable false in
theorem signWithView_support_some
    (secretKey : SecretKey) (message : Message)
    (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature) (view : Option FewTimeView)
    (hmem : ((some signature, view), finalCache) ∈ support
      ((simulateQ romImpl (signWithView secretKey message)).run initialCache)) :
    ∃ (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
        (loopCache : QueryCache HashSpec),
      (some (randomness, index, leaves), loopCache) ∈ support
          ((simulateQ romImpl
            (signDigestLoop digestAttemptLimit secretKey message)).run initialCache)
        ∧ (some signature, finalCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
            (signAfterDigest secretKey randomness index leaves)).run loopCache)
        ∧ view = some (selectedFewTimeView index leaves) := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hfinish⟩ := hmem
  cases loopResult with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at hfinish
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
      obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hfinish
      have hpureEq : ((some signature, view), finalCache) =
          ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      have hresult : some signature = signatureResult :=
        congrArg (fun result => result.1.1) hpureEq
      have hview : view = some (selectedFewTimeView index leaves) :=
        congrArg (fun result => result.1.2) hpureEq
      have hcache : finalCache = signatureCache := congrArg Prod.snd hpureEq
      rw [← hresult, ← hcache] at hsignature
      refine ⟨randomness, index, leaves, loopCache, hloop, ?_, hview⟩
      simpa only [simulateQ_romImpl_liftM] using hsignature
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_AdmissibleCount ====
section

section
namespace SphincsSecurity.Octopus
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1
def xorSum (vs : List Nat) : Nat := (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum
def octH (H : Nat) (vs : List Nat) : Nat := H + 2 + xorSum vs - 2 * vs.length
def octopusSize (vs : List Nat) : Nat :=
  14 + 2 + (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum - 2 * vs.length
theorem octopusSize_eq (vs : List Nat) : octopusSize vs = octH 14 vs := rfl
def sortLeaves (v : List Nat) : List Nat := v.insertionSort (· ≤ ·)
def leafOf (N r : Nat) : Nat := N / 2 ^ (34 + 14 * r) % 2 ^ 14
def leavesOf (N : Nat) : List Nat := (List.range 15).map (leafOf N)
def admissible (N : Nat) : Bool :=
  decide (leavesOf N).Nodup && decide (octopusSize (sortLeaves (leavesOf N)) ≤ 118)
def Nadm : Nat := 587603809105224201844661965127195603157454143488
def pstep (K y M : Nat) (T : List Nat) : List Nat :=
  (List.range (K + 1)).map fun j =>
    (2 * y * T.getD j 0 + ((List.range (j + 1)).map fun i => T.getD i 0 * T.getD (j - i) 0).sum) % M
def piter (K y M : Nat) : Nat → List Nat → List Nat
  | 0, T => T
  | k + 1, T => piter K y M k (pstep K y M T)
def pB : Nat := 224
def packedCount : Nat := ((piter 15 (2 ^ pB) (2 ^ (pB * 119)) 14 [0, 1]).getD 15 0) % (2 ^ pB - 1)
theorem packedCount_eq : packedCount = Nadm := by decide +kernel
end SphincsSecurity.Octopus
end
section
namespace SphincsSecurity.Octopus
open Finset Polynomial
theorem testBit_add_two_pow {z H : ℕ} (hz : z < 2 ^ H) (i : ℕ) :
    (z + 2 ^ H).testBit i = (decide (i = H) || z.testBit i) := by
  rw [Nat.add_comm]
  rcases lt_trichotomy i H with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [h.ne]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz]; simp
  · have hH : 2 ^ (H + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 2 ^ H + z < 2 ^ i := by rw [pow_succ] at hH; omega
    have h2 : z < 2 ^ i := by rw [pow_succ] at hH; omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [h.ne']
theorem xor_shift_shift {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    (x + 2 ^ H) ^^^ (y + 2 ^ H) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_two_pow hx, testBit_add_two_pow hy]
  by_cases h : i = H
  · subst h; simp [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  · simp [h]
theorem xor_cross {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    x ^^^ (y + 2 ^ H) = (x ^^^ y) + 2 ^ H := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_add_two_pow hy, testBit_add_two_pow (Nat.xor_lt_two_pow hx hy),
    Nat.testBit_xor]
  by_cases h : i = H
  · subst h; simp [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  · simp [h]
theorem bitLen_add_two_pow {z H : ℕ} (hz : z < 2 ^ H) : bitLen (z + 2 ^ H) = H + 1 := by
  unfold bitLen
  have h2 : z + 2 ^ H < 2 ^ (H + 1) := by rw [pow_succ]; omega
  rw [if_neg (by positivity),
    (Nat.log2_eq_iff (n := z + 2 ^ H) (k := H) (by positivity)).2 ⟨by omega, h2⟩]
theorem bitLen_cross {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    bitLen (x ^^^ (y + 2 ^ H)) = H + 1 := by
  rw [xor_cross hx hy, bitLen_add_two_pow (Nat.xor_lt_two_pow hx hy)]
@[simp] theorem xorSum_nil : xorSum [] = 0 := rfl
@[simp] theorem xorSum_single (a : ℕ) : xorSum [a] = 0 := rfl
theorem xorSum_cons_cons (a b : ℕ) (t : List ℕ) :
    xorSum (a :: b :: t) = bitLen (a ^^^ b) + xorSum (b :: t) := by
  simp [xorSum]
theorem xorSum_append (a : List ℕ) (x y : ℕ) (b : List ℕ) :
    xorSum (a ++ x :: y :: b) = xorSum (a ++ [x]) + bitLen (x ^^^ y) + xorSum (y :: b) := by
  induction a with
  | nil => simp [xorSum_cons_cons]
  | cons c a ih =>
    cases a with
    | nil => simp [xorSum_cons_cons]; omega
    | cons d a =>
      simp only [List.cons_append] at ih ⊢
      rw [xorSum_cons_cons, ih, xorSum_cons_cons]; omega
theorem xorSum_map_shift {H : ℕ} : ∀ (l : List ℕ), (∀ z ∈ l, z < 2 ^ H) →
    xorSum (l.map (· + 2 ^ H)) = xorSum l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have ih := xorSum_map_shift (b :: t) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons] at ih ⊢
    rw [xorSum_cons_cons, xorSum_cons_cons, ih,
      xor_shift_shift (h a (by simp)) (h b (by simp))]
def glue (H : ℕ) (L R : Finset ℕ) : Finset ℕ := L ∪ R.map (addRightEmbedding (2 ^ H))
def lo (H : ℕ) (S : Finset ℕ) : Finset ℕ := S.filter (· < 2 ^ H)
def hi (H : ℕ) (S : Finset ℕ) : Finset ℕ := (S.filter (2 ^ H ≤ ·)).image (· - 2 ^ H)
def Below (H : ℕ) (S : Finset ℕ) : Prop := ∀ x ∈ S, x < 2 ^ H
theorem below_iff (H : ℕ) (S : Finset ℕ) : Below H S ↔ S ∈ (range (2 ^ H)).powerset := by
  simp [Below, subset_iff]
theorem mem_glue {H : ℕ} {L R : Finset ℕ} {x : ℕ} :
    x ∈ glue H L R ↔ x ∈ L ∨ (2 ^ H ≤ x ∧ x - 2 ^ H ∈ R) := by
  simp only [glue, mem_union, mem_map, addRightEmbedding_apply]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by simpa using ha⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, h2, by omega⟩
theorem glue_below {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R) :
    Below (H + 1) (glue H L R) := by
  intro x hx
  rw [mem_glue] at hx
  rw [pow_succ]
  rcases hx with h | ⟨h1, h2⟩
  · have := hL x h; omega
  · have := hR _ h2; omega
theorem lo_below (H : ℕ) (S : Finset ℕ) : Below H (lo H S) := by
  intro x hx; simp only [lo, mem_filter] at hx; exact hx.2
theorem hi_below {H : ℕ} {S : Finset ℕ} (hS : Below (H + 1) S) : Below H (hi H S) := by
  intro x hx
  simp only [hi, mem_image, mem_filter] at hx
  obtain ⟨a, ⟨ha, h1⟩, rfl⟩ := hx
  have := hS a ha; rw [pow_succ] at this; omega
theorem glue_lo_hi {H : ℕ} {S : Finset ℕ} : glue H (lo H S) (hi H S) = S := by
  ext x
  rw [mem_glue]
  simp only [lo, hi, mem_filter, mem_image]
  constructor
  · rintro (⟨h, _⟩ | ⟨h1, a, ⟨ha, h2⟩, h3⟩)
    · exact h
    · have : a = x := by omega
      exact this ▸ ha
  · intro h
    by_cases hx : x < 2 ^ H
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨by omega, x, ⟨h, by omega⟩, rfl⟩
theorem lo_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) : lo H (glue H L R) = L := by
  ext x
  simp only [lo, mem_filter, mem_glue]
  constructor
  · rintro ⟨h | ⟨h1, _⟩, h2⟩
    · exact h
    · omega
  · intro h; exact ⟨Or.inl h, hL x h⟩
theorem hi_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) : hi H (glue H L R) = R := by
  ext x
  simp only [hi, mem_image, mem_filter, mem_glue]
  constructor
  · rintro ⟨a, ⟨h | ⟨h1, h2⟩, h3⟩, rfl⟩
    · have := hL a h; omega
    · exact h2
  · intro h
    exact ⟨x + 2 ^ H, ⟨Or.inr ⟨by omega, by simpa using h⟩, by omega⟩, by omega⟩
theorem card_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) :
    (glue H L R).card = L.card + R.card := by
  unfold glue
  rw [card_union_of_disjoint, card_map]
  rw [disjoint_left]
  intro x hx hx'
  simp only [mem_map, addRightEmbedding_apply] at hx'
  obtain ⟨a, _, rfl⟩ := hx'
  have := hL _ hx; omega
theorem glue_empty_empty (H : ℕ) : glue H ∅ ∅ = ∅ := by simp [glue]
theorem glue_ne_empty_left {H : ℕ} {L R : Finset ℕ} (h : L ≠ ∅) : glue H L R ≠ ∅ := by
  intro h'
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
  have : x ∈ glue H L R := mem_glue.mpr (Or.inl hx)
  rw [h'] at this; simp at this
theorem glue_ne_empty_right {H : ℕ} {L R : Finset ℕ} (h : R ≠ ∅) : glue H L R ≠ ∅ := by
  intro h'
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
  have : x + 2 ^ H ∈ glue H L R := mem_glue.mpr (Or.inr ⟨by omega, by simpa using hx⟩)
  rw [h'] at this; simp at this
theorem sort_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) :
    (glue H L R).sort = L.sort ++ R.sort.map (· + 2 ^ H) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) (sortedLT_sort _).pairwise
  · rw [List.pairwise_append, List.pairwise_map]
    refine ⟨(sortedLT_sort _).pairwise, (sortedLT_sort _).pairwise.imp (by omega), ?_⟩
    intro a ha b hb
    rw [mem_sort] at ha
    simp only [List.mem_map, mem_sort] at hb
    obtain ⟨c, _, rfl⟩ := hb
    have := hL a ha; omega
  · intro x
    simp only [mem_sort, mem_glue, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x - 2 ^ H, h2, by omega⟩
    · rintro (h | ⟨c, hc, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by simpa using hc⟩
def E (H : ℕ) (S : Finset ℕ) : ℕ := H + 2 + xorSum S.sort
def oc (H : ℕ) (S : Finset ℕ) : ℕ := octH H S.sort
theorem oc_eq (H : ℕ) (S : Finset ℕ) : oc H S = E H S - 2 * S.card := by
  simp [oc, octH, E, length_sort]
theorem E_glue_left {H : ℕ} {L : Finset ℕ} (hL : Below H L) :
    E (H + 1) (glue H L ∅) = E H L + 1 := by
  unfold E
  rw [sort_glue hL]
  simp; omega
theorem E_glue_right {H : ℕ} {R : Finset ℕ} (hR : Below H R) :
    E (H + 1) (glue H ∅ R) = E H R + 1 := by
  unfold E
  rw [sort_glue (by simp [Below])]
  simp only [sort_empty, List.nil_append]
  rw [xorSum_map_shift _ (fun z hz => hR z ((mem_sort _).mp hz))]; omega
theorem E_glue_both {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R)
    (hL0 : L ≠ ∅) (hR0 : R ≠ ∅) : E (H + 1) (glue H L R) = E H L + E H R := by
  unfold E
  rw [sort_glue hL]
  rcases List.eq_nil_or_concat L.sort with h | ⟨a, x, hx⟩
  · exact absurd (by simpa using congrArg List.toFinset h) hL0
  rw [List.concat_eq_append] at hx
  cases hy : R.sort with
  | nil => exact absurd (by simpa using congrArg List.toFinset hy) hR0
  | cons y b =>
    have hxL : x ∈ L := by rw [← mem_sort (r := (· ≤ ·)), hx]; simp
    have hyR : y ∈ R := by rw [← mem_sort (r := (· ≤ ·)), hy]; simp
    have hb : ∀ z ∈ y :: b, z < 2 ^ H := fun z hz => hR z (by rw [← mem_sort (r := (· ≤ ·)), hy]; exact hz)
    rw [hx, List.map_cons, List.append_assoc, List.singleton_append, xorSum_append,
      bitLen_cross (hL x hxL) (hR y hyR)]
    have := xorSum_map_shift (y :: b) hb
    rw [List.map_cons] at this
    rw [this]; omega
theorem below_zero {S : Finset ℕ} (hS : Below 0 S) (h0 : S ≠ ∅) : S = {0} := by
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h0
  ext y
  simp only [mem_singleton]
  constructor
  · intro hy; have := hS y hy; simp at this; exact this
  · rintro rfl; have := hS x hx; simp at this; exact this ▸ hx
theorem two_card_le_E : ∀ (H : ℕ) (S : Finset ℕ), Below H S → S ≠ ∅ → 2 * S.card ≤ E H S
  | 0, S, hS, h0 => by
    rw [below_zero hS h0]; simp [E]
  | H + 1, S, hS, h0 => by
    rw [← glue_lo_hi (H := H) (S := S)] at h0 ⊢
    have hL := lo_below H S
    have hR := hi_below hS
    rw [card_glue hL]
    by_cases hL0 : lo H S = ∅
    · have hR0 : hi H S ≠ ∅ := fun h => h0 (by rw [hL0, h, glue_empty_empty])
      have := two_card_le_E H _ hR hR0
      rw [hL0, E_glue_right hR]; simp; omega
    · by_cases hR0 : hi H S = ∅
      · have := two_card_le_E H _ hL hL0
        rw [hR0, E_glue_left hL]; simp; omega
      · have h1 := two_card_le_E H _ hL hL0
        have h2 := two_card_le_E H _ hR hR0
        rw [E_glue_both hL hR hL0 hR0]; omega
theorem oc_glue_left {H : ℕ} {L : Finset ℕ} (hL : Below H L) (hL0 : L ≠ ∅) :
    oc (H + 1) (glue H L ∅) = oc H L + 1 := by
  have := two_card_le_E H L hL hL0
  rw [oc_eq, oc_eq, E_glue_left hL, card_glue hL]; simp; omega
theorem oc_glue_right {H : ℕ} {R : Finset ℕ} (hR : Below H R) (hR0 : R ≠ ∅) :
    oc (H + 1) (glue H ∅ R) = oc H R + 1 := by
  have := two_card_le_E H R hR hR0
  rw [oc_eq, oc_eq, E_glue_right hR, card_glue (by simp [Below])]; simp; omega
theorem oc_glue_both {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R)
    (hL0 : L ≠ ∅) (hR0 : R ≠ ∅) : oc (H + 1) (glue H L R) = oc H L + oc H R := by
  have h1 := two_card_le_E H L hL hL0
  have h2 := two_card_le_E H R hR hR0
  rw [oc_eq, oc_eq, oc_eq, E_glue_both hL hR hL0 hR0, card_glue hL]; omega
theorem sum_powerset_succ {M : Type*} [AddCommMonoid M] (H : ℕ) (f : Finset ℕ → M) :
    ∑ S ∈ (range (2 ^ (H + 1))).powerset, f S =
      ∑ L ∈ (range (2 ^ H)).powerset, ∑ R ∈ (range (2 ^ H)).powerset, f (glue H L R) := by
  rw [← sum_product']
  refine sum_nbij' (fun S => (lo H S, hi H S)) (fun p => glue H p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [← below_iff] at hS
    rw [mem_product, ← below_iff, ← below_iff]
    exact ⟨lo_below H S, hi_below hS⟩
  · rintro ⟨L, R⟩ h
    rw [mem_product, ← below_iff, ← below_iff] at h
    rw [← below_iff]
    exact glue_below h.1 h.2
  · intro S _; exact glue_lo_hi
  · rintro ⟨L, R⟩ h
    rw [mem_product, ← below_iff, ← below_iff] at h
    simp only [lo_glue h.1, hi_glue h.1]
  · intro S _; simp only [glue_lo_hi]
noncomputable def mono (y H : ℕ) (S : Finset ℕ) : ℕ[X] :=
  if S = ∅ then 0 else monomial S.card (y ^ oc H S)
noncomputable def Q (y H : ℕ) : ℕ[X] := ∑ S ∈ (range (2 ^ H)).powerset, mono y H S
theorem mono_glue (y : ℕ) {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R) :
    mono y (H + 1) (glue H L R) =
      (if R = ∅ then C y * mono y H L else 0) + (if L = ∅ then C y * mono y H R else 0) +
        mono y H L * mono y H R := by
  by_cases hL0 : L = ∅ <;> by_cases hR0 : R = ∅
  · subst hL0; subst hR0; simp [mono, glue_empty_empty]
  · subst hL0
    rw [mono, if_neg (glue_ne_empty_right hR0), card_glue hL, oc_glue_right hR hR0]
    simp only [mono, hR0, if_true, if_false, zero_mul, add_zero, zero_add, C_mul_monomial, pow_succ,
      mul_comm, card_empty]
  · subst hR0
    rw [mono, if_neg (glue_ne_empty_left hL0), card_glue hL, oc_glue_left hL hL0]
    simp only [mono, hL0, if_true, if_false, zero_mul, add_zero, C_mul_monomial, pow_succ,
      mul_comm, card_empty]
  · rw [mono, if_neg (glue_ne_empty_left hL0), card_glue hL, oc_glue_both hL hR hL0 hR0]
    simp [mono, hL0, hR0, monomial_mul_monomial, pow_add]
theorem Q_succ (y H : ℕ) : Q y (H + 1) = C (2 * y) * Q y H + Q y H * Q y H := by
  unfold Q
  rw [sum_powerset_succ]
  have hmem : ∀ S ∈ (range (2 ^ H)).powerset, Below H S := fun S hS => (below_iff H S).mpr hS
  rw [sum_congr rfl fun L hL => sum_congr rfl fun R hR => mono_glue y (hmem L hL) (hmem R hR)]
  simp only [sum_add_distrib]
  rw [sum_mul_sum]
  congr 1
  have e1 : ∀ L ∈ (range (2 ^ H)).powerset, ∑ R ∈ (range (2 ^ H)).powerset,
      (if R = ∅ then C y * mono y H L else 0) = C y * mono y H L := by
    intro L _; rw [sum_ite_eq']; simp
  rw [sum_congr rfl e1, sum_comm]
  rw [sum_congr rfl fun R _ => sum_ite_eq' (range (2 ^ H)).powerset ∅ (fun _ => C y * mono y H R)]
  simp only [empty_mem_powerset, if_true]
  rw [← mul_sum, ← two_mul, ← mul_assoc]
  congr 1
  simp [map_mul]
theorem Q_zero (y : ℕ) : Q y 0 = X := by
  unfold Q
  have : (range (2 ^ 0)).powerset = {∅, {0}} := by decide
  rw [this, sum_pair (by decide)]
  simp [mono, oc, octH, xorSum, X]
theorem coeff_Q_succ (y H j : ℕ) : (Q y (H + 1)).coeff j =
    2 * y * (Q y H).coeff j + ∑ i ∈ range (j + 1), (Q y H).coeff i * (Q y H).coeff (j - i) := by
  rw [Q_succ, coeff_add, coeff_C_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
theorem coeff_Q (y H j : ℕ) (hj : j ≠ 0) :
    (Q y H).coeff j = ∑ S ∈ powersetCard j (range (2 ^ H)), y ^ oc H S := by
  unfold Q
  rw [finsetSum_coeff, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  unfold mono
  by_cases h : S = ∅
  · subst h; simp [Ne.symm hj]
  · simp [h, coeff_monomial]
end SphincsSecurity.Octopus
end
section
namespace SphincsSecurity.Octopus
open Finset Polynomial
theorem list_sum_map_range' (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp
theorem getD_pstep (K y M : ℕ) (T : List ℕ) {j : ℕ} (hj : j ≤ K) :
    (pstep K y M T).getD j 0 =
      (2 * y * T.getD j 0 + ∑ i ∈ range (j + 1), T.getD i 0 * T.getD (j - i) 0) % M := by
  unfold pstep
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp [list_sum_map_range']
def Rep (K y M H : ℕ) (T : List ℕ) : Prop := ∀ j ≤ K, T.getD j 0 = (Q y H).coeff j % M
theorem rep_pstep {K y M H : ℕ} {T : List ℕ} (h : Rep K y M H T) :
    Rep K y M (H + 1) (pstep K y M T) := by
  intro j hj
  rw [getD_pstep K y M T hj, coeff_Q_succ]
  show Nat.ModEq M _ _
  apply Nat.ModEq.add
  · exact Nat.ModEq.mul_left _ (by rw [h j hj]; exact Nat.mod_modEq _ _)
  · refine Nat.ModEq.sum fun i hi => ?_
    have hi' : i ≤ K := by rw [mem_range] at hi; omega
    rw [h i hi', h (j - i) (by omega)]
    exact (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
theorem rep_piter {K y M : ℕ} : ∀ (k H : ℕ) (T : List ℕ), Rep K y M H T →
    Rep K y M (H + k) (piter K y M k T)
  | 0, _, _, h => h
  | k + 1, H, T, h => by
    have := rep_piter k (H + 1) _ (rep_pstep h)
    rwa [show H + 1 + k = H + (k + 1) by omega] at this
theorem rep_zero (K y M : ℕ) (hM : 1 < M) : Rep K y M 0 [0, 1] := by
  intro j _
  rw [Q_zero, coeff_X]
  rcases j with _ | _ | j
  · simp
  · simp [Nat.mod_eq_of_lt hM]
  · simp
theorem mod_pow_sum {y n : ℕ} (hn : 0 < n) (P : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (hP : P.card < y) :
    (∑ S ∈ P, y ^ g S) % y ^ n = ∑ S ∈ P.filter (g · < n), y ^ g S := by
  rw [← sum_filter_add_sum_filter_not P (g · < n)]
  obtain ⟨c, hc⟩ : y ^ n ∣ ∑ S ∈ P.filter (fun S => ¬ g S < n), y ^ g S :=
    dvd_sum fun S hS => pow_dvd_pow y (not_lt.mp (mem_filter.mp hS).2)
  rw [hc, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hy : 1 ≤ y := by omega
  calc ∑ S ∈ P.filter (g · < n), y ^ g S
      ≤ ∑ _S ∈ P.filter (g · < n), y ^ (n - 1) :=
        sum_le_sum fun S hS => Nat.pow_le_pow_right hy (by have := (mem_filter.mp hS).2; omega)
    _ = (P.filter (g · < n)).card * y ^ (n - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ P.card * y ^ (n - 1) := Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ < y * y ^ (n - 1) := Nat.mul_lt_mul_of_pos_right hP (by positivity)
    _ = y ^ n := by rw [← pow_succ']; congr 1; omega
theorem sum_pow_mod_pred {y : ℕ} (hy : 3 ≤ y) (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ) :
    (∑ S ∈ F, y ^ g S) % (y - 1) = F.card % (y - 1) := by
  have hmod : y % (y - 1) = 1 := by
    calc y % (y - 1) = (y - 1 + 1) % (y - 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 1 % (y - 1) := Nat.add_mod_left _ _
      _ = 1 := Nat.mod_eq_of_lt (by omega)
  rw [sum_nat_mod]
  rw [sum_congr rfl fun S _ => by rw [Nat.pow_mod, hmod, one_pow]]
  simp
theorem card_admissibleSets :
    ((powersetCard 15 (range (2 ^ 14))).filter fun S => octH 14 S.sort ≤ 118).card = Nadm := by
  rw [← packedCount_eq]
  unfold packedCount
  have hM : (2 : ℕ) ^ (pB * 119) = (2 ^ pB) ^ 119 := pow_mul 2 pB 119
  have hy3 : 3 ≤ (2 : ℕ) ^ pB := by unfold pB; norm_num
  have hcard : (powersetCard 15 (range (2 ^ 14))).card < 2 ^ pB - 1 := by
    rw [card_powersetCard, card_range]
    exact lt_of_le_of_lt (Nat.choose_le_pow _ _) (by rw [← pow_mul]; unfold pB; norm_num)
  have h15 := rep_piter (K := 15) (y := 2 ^ pB) (M := 2 ^ (pB * 119)) 14 0 [0, 1]
    (rep_zero 15 _ _ (Nat.one_lt_two_pow (by unfold pB; norm_num))) 15 le_rfl
  rw [Nat.zero_add] at h15
  rw [h15, coeff_Q _ _ _ (by norm_num), hM, mod_pow_sum (by norm_num) _ _ (by omega),
    sum_pow_mod_pred hy3, Nat.mod_eq_of_lt (lt_of_le_of_lt (card_filter_le _ _) hcard)]
  exact congrArg card (filter_congr fun S _ => by simp only [oc]; omega)
end SphincsSecurity.Octopus
end
section
namespace SphincsSecurity.Octopus
open Finset
def valList {k n : ℕ} (v : Fin k → Fin n) : List ℕ := List.ofFn fun i => (v i : ℕ)
theorem valList_nodup {k n : ℕ} (v : Fin k → Fin n) :
    (valList v).Nodup ↔ Function.Injective v := by
  unfold valList
  rw [List.nodup_ofFn]
  exact ⟨fun h a b hab => h (by simp [hab]), fun h a b hab => h (Fin.ext hab)⟩
theorem mem_valList {k n : ℕ} (v : Fin k → Fin n) (x : ℕ) :
    x ∈ valList v ↔ ∃ i, (v i : ℕ) = x := by
  simp [valList, List.mem_ofFn]
theorem sortLeaves_eq {l : List ℕ} (hl : l.Nodup) : sortLeaves l = l.toFinset.sort := by
  unfold sortLeaves
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (List.pairwise_insertionSort _ _)
    (pairwise_sort _ _)
  refine (List.perm_insertionSort _ _).trans ?_
  rw [List.perm_ext_iff_of_nodup hl (sort_nodup _ _)]
  intro a; simp
theorem card_fiber (k n : ℕ) (S : Finset ℕ) (hS : S ∈ powersetCard k (range n)) :
    (univ.filter fun v : Fin k → Fin n =>
      Function.Injective v ∧ (valList v).toFinset = S).card = k.factorial := by
  rw [mem_powersetCard] at hS
  obtain ⟨hSn, hSk⟩ := hS
  rw [← Fintype.card_subtype]
  have mem : ∀ v : Fin k → Fin n, (valList v).toFinset = S → ∀ i, (v i : ℕ) ∈ S := by
    intro v hv i; rw [← hv, List.mem_toFinset, mem_valList]; exact ⟨i, rfl⟩
  let E : {v : Fin k → Fin n // Function.Injective v ∧ (valList v).toFinset = S} ≃ (Fin k ≃ S) :=
    { toFun := fun v => Equiv.ofBijective (fun i => ⟨(v.1 i : ℕ), mem v.1 v.2.2 i⟩)
        ⟨fun a b hab => v.2.1 (Fin.ext (by simpa using hab)), fun x => by
          have hx : (x : ℕ) ∈ (valList v.1).toFinset := by rw [v.2.2]; exact x.2
          rw [List.mem_toFinset, mem_valList] at hx
          obtain ⟨i, hi⟩ := hx
          exact ⟨i, Subtype.ext hi⟩⟩
      invFun := fun e => ⟨fun i => ⟨(e i : ℕ), mem_range.mp (hSn (e i).2)⟩, fun a b hab => by
          have : (e a : ℕ) = e b := by simpa using congrArg Fin.val hab
          exact e.injective (Subtype.ext this), by
          ext x
          rw [List.mem_toFinset, mem_valList]
          constructor
          · rintro ⟨i, rfl⟩; exact (e i).2
          · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
      left_inv := fun v => Subtype.ext (funext fun i => Fin.ext rfl)
      right_inv := fun e => Equiv.ext fun i => Subtype.ext rfl }
  rw [Fintype.card_congr E]
  have e0 : Fin k ≃ S := (S.equivFinOfCardEq hSk).symm
  rw [Fintype.card_equiv e0, Fintype.card_fin]
theorem card_inj_filter (k n : ℕ) (P : Finset ℕ → Prop) [DecidablePred P] :
    (univ.filter fun v : Fin k → Fin n =>
      Function.Injective v ∧ P (valList v).toFinset).card =
      k.factorial * ((powersetCard k (range n)).filter P).card := by
  rw [card_eq_sum_card_fiberwise (f := fun v : Fin k → Fin n => (valList v).toFinset)
    (t := (powersetCard k (range n)).filter P)]
  · rw [sum_congr rfl fun S hS => ?_, sum_const, smul_eq_mul, mul_comm]
    rw [mem_filter] at hS
    rw [filter_filter, ← card_fiber k n S hS.1]
    congr 1
    refine filter_congr fun v _ => ?_
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hS.2⟩, h3⟩
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq]
    refine ⟨⟨fun x hx => ?_, ?_⟩, hv.2⟩
    · rw [List.mem_toFinset, mem_valList] at hx
      obtain ⟨i, rfl⟩ := hx
      exact mem_range.mpr (v i).2
    · rw [List.toFinset_card_of_nodup ((valList_nodup v).mpr hv.1)]
      simp [valList]
theorem card_admissibleTuples :
    (univ.filter fun v : Fin 15 → Fin (2 ^ 14) =>
      Function.Injective v ∧ octopusSize (sortLeaves (valList v)) ≤ 118).card =
      Nat.factorial 15 * Nadm := by
  have h := card_inj_filter 15 (2 ^ 14) (fun S => octH 14 S.sort ≤ 118)
  rw [card_admissibleSets] at h
  rw [← h]
  refine congrArg card (filter_congr fun v _ => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [octopusSize_eq, sortLeaves_eq ((valList_nodup v).mpr h1)] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [octopusSize_eq, sortLeaves_eq ((valList_nodup v).mpr h1)]
def fieldsOf (b : ℕ) : List ℕ := (List.range 15).map fun r => b / 2 ^ (14 * r) % 2 ^ 14
def admB (b : ℕ) : Bool :=
  decide (fieldsOf b).Nodup && decide (octopusSize (sortLeaves (fieldsOf b)) ≤ 118)
theorem leavesOf_eq (N : ℕ) : leavesOf N = fieldsOf (N / 2 ^ 34) := by
  unfold leavesOf fieldsOf leafOf
  refine List.map_congr_left fun r _ => ?_
  rw [Nat.div_div_eq_div_mul, ← pow_add]
theorem admissible_eq (N : ℕ) : admissible N = admB (N / 2 ^ 34) := by
  unfold admissible admB; rw [leavesOf_eq]
theorem fieldsOf_add (c d : ℕ) : fieldsOf (c + 2 ^ 210 * d) = fieldsOf c := by
  unfold fieldsOf
  refine List.map_congr_left fun r hr => ?_
  have hr := List.mem_range.mp hr
  have e : (2 : ℕ) ^ 210 * d = 2 ^ (14 * r) * (2 ^ 14 * (2 ^ (196 - 14 * r) * d)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (A B : ℕ) :
    ∑ k ∈ range (A * B), f k = ∑ b ∈ range B, ∑ a ∈ range A, f (a + A * b) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [Nat.add_comm]
theorem count_low (A B : ℕ) (hA : 0 < A) (p : ℕ → Bool) :
    (∑ k ∈ range (A * B), if p (k / A) then 1 else 0) =
      A * ∑ b ∈ range B, if p b then 1 else 0 := by
  rw [sum_range_mul', mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl fun a ha => by
    rw [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt (mem_range.mp ha), Nat.zero_add]]
  simp
theorem count_high (A B : ℕ) (p : ℕ → Bool) (hp : ∀ a b, p (a + A * b) = p a) :
    (∑ k ∈ range (A * B), if p k then 1 else 0) = B * ∑ a ∈ range A, if p a then 1 else 0 := by
  rw [sum_range_mul']
  simp [hp]
theorem fieldsOf_equiv (v : Fin 15 → Fin (2 ^ 14)) :
    fieldsOf (finFunctionFinEquiv v : ℕ) = valList v := by
  unfold fieldsOf valList
  apply List.ext_getElem (by simp)
  intro r h1 _
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv v) ⟨r, by simpa using h1⟩
  rw [Equiv.symm_apply_apply] at this
  rw [this, pow_mul]
theorem count_fields :
    (∑ c ∈ range (2 ^ 210), if admB c then 1 else 0) =
      (univ.filter fun v : Fin 15 → Fin (2 ^ 14) =>
        Function.Injective v ∧ octopusSize (sortLeaves (valList v)) ≤ 118).card := by
  have e : (2 : ℕ) ^ 210 = (2 ^ 14) ^ 15 := by rw [← pow_mul]
  rw [e, sum_range (fun c => if admB c then 1 else 0), card_filter]
  rw [← Equiv.sum_comp finFunctionFinEquiv]
  refine sum_congr rfl fun v _ => ?_
  unfold admB
  simp only [fieldsOf_equiv, valList_nodup, Bool.and_eq_true, decide_eq_true_eq]
theorem card_admissibleDigests :
    ((range (2 ^ 256)).filter fun N => admissible N = true).card =
      2 ^ 46 * (Nat.factorial 15 * Nadm) := by
  rw [card_filter]
  have e : (2 : ℕ) ^ 256 = 2 ^ 34 * (2 ^ 210 * 2 ^ 12) := by rw [← pow_add, ← pow_add]
  rw [e, sum_congr rfl fun N _ => by rw [admissible_eq], count_low _ _ (by positivity),
    count_high _ _ _ (fun a b => by unfold admB; rw [fieldsOf_add]), count_fields,
    card_admissibleTuples, ← mul_assoc, ← pow_add]
end SphincsSecurity.Octopus
end
section
namespace SphincsSecurity.Concrete
open Finset
private instance sortRelTotal (leaves : IndexGroup → FtsLeaf) :
    Std.Total (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val) :=
  ⟨fun a b => le_total _ _⟩
private instance sortRelTrans (leaves : IndexGroup → FtsLeaf) :
    IsTrans IndexGroup (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val) :=
  ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
theorem sortedLeaves_eq_sortLeaves (leaves : IndexGroup → FtsLeaf) :
    sortedLeaves leaves = Octopus.sortLeaves (Octopus.valList (n := 2 ^ 14) (k := 15) leaves) := by
  unfold sortedLeaves sortedSlots Octopus.sortLeaves Octopus.valList
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · rw [List.pairwise_map]
    exact List.pairwise_insertionSort _ _
  · exact List.pairwise_insertionSort _ _
  · refine ((List.perm_insertionSort _ _).map _).trans ?_
    refine List.Perm.trans ?_ (List.perm_insertionSort _ _).symm
    rw [List.ofFn_eq_map]
    rfl
theorem octopusSize_eq_reference (sorted : List Nat) : octopusSize sorted = Octopus.octopusSize sorted := rfl
theorem card_admissibleLeaves :
    (univ.filter AdmissibleLeaves).card = Nat.factorial 15 * Octopus.Nadm := by
  have hfilter : univ.filter AdmissibleLeaves = univ.filter fun v : IndexGroup → FtsLeaf =>
      Function.Injective v ∧ Octopus.octopusSize (Octopus.sortLeaves (Octopus.valList v)) ≤ 118 := by
    apply filter_congr
    intro leaves _
    unfold AdmissibleLeaves
    rw [sortedLeaves_eq_sortLeaves, octopusSize_eq_reference]
    rfl
  rw [hfilter]
  exact Octopus.card_admissibleTuples
theorem card_leafVectors : Fintype.card (IndexGroup → FtsLeaf) = 2 ^ 210 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl
theorem admissibleLeafCount_bounds :
    2 ^ 210 ≤ 2142 * (Nat.factorial 15 * Octopus.Nadm) ∧ 2141 * (Nat.factorial 15 * Octopus.Nadm) ≤ 2 ^ 210 := by
  unfold Octopus.Nadm
  norm_num [Nat.factorial]
open ENNReal in
noncomputable irreducible_def admissibleProbability : ENNReal :=
  ((univ.filter AdmissibleLeaves).card : ENNReal) / (Fintype.card (IndexGroup → FtsLeaf) : ENNReal)
open ENNReal in
theorem admissibleProbability_ge : (2142 : ENNReal)⁻¹ ≤ admissibleProbability := by
  rw [admissibleProbability_def, card_admissibleLeaves, card_leafVectors]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), ← ENNReal.div_eq_inv_mul,
    ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleLeafCount_bounds.1
  rw [mul_comm] at h
  exact_mod_cast h
open ENNReal in
theorem admissibleProbability_le : admissibleProbability ≤ (2141 : ENNReal)⁻¹ := by
  rw [admissibleProbability_def, card_admissibleLeaves, card_leafVectors]
  rw [ENNReal.div_le_iff (by simp) (by simp), ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleLeafCount_bounds.2
  rw [mul_comm] at h
  exact_mod_cast h
theorem admissibleProbability_inv_le : admissibleProbability⁻¹ ≤ 2142 :=
  ENNReal.inv_le_iff_inv_le.mpr admissibleProbability_ge
theorem admissibleProbability_pos : admissibleProbability ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by simp) admissibleProbability_ge)
theorem admissibleProbability_ne_top : admissibleProbability ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) admissibleProbability_le
theorem admissibleProbability_le_one : admissibleProbability ≤ 1 :=
  admissibleProbability_le.trans (ENNReal.inv_le_one.mpr (by norm_num))
theorem card_admissibleLeaves_eq_mul :
    ((univ.filter AdmissibleLeaves).card : ENNReal) =
      admissibleProbability * (Fintype.card (IndexGroup → FtsLeaf) : ENNReal) := by
  rw [admissibleProbability_def, ENNReal.div_mul_cancel (by simp) (by simp)]
noncomputable def cachedIndexRate : ENNReal := admissibleProbability * (Fintype.card Index : ENNReal)⁻¹
theorem cachedIndexRate_ne_top : cachedIndexRate ≠ ⊤ :=
  ENNReal.mul_ne_top admissibleProbability_ne_top (by simp)
theorem cachedIndexRate_le_one : cachedIndexRate ≤ 1 :=
  (mul_le_mul' admissibleProbability_le_one (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos))).trans_eq
    (one_mul 1)
theorem card_mul_cachedIndexRate : (Fintype.card Index : ENNReal) * cachedIndexRate = admissibleProbability := by
  rw [cachedIndexRate, mul_left_comm, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeFresh ====
section

section
set_option autoImplicit true
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity_1 {α : Type} [Fintype α] [Nonempty α] : SampleableType α :=
  SampleableType.ofFintype α
theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    𝒮[(do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right))] =
      𝒮[($ᵗ (α × β) : ProbComp (α × β))] := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]
def listToFunction (count : Nat) (values : List FewTimeView) : Fin count → FewTimeView :=
  fun position => values.getD position.val default
@[simp]
theorem listToFunction_ofFn (values : Fin count → FewTimeView) :
    listToFunction count (List.ofFn values) = values := by
  funext position
  simp [listToFunction, List.getD]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
abbrev HashOutputRest :=
  DigestUnusedBits × BitVec (hashOutputBits - messageDigestBits)
def reorderHashOutputCoordinates :
    (HashOutputRest × FewTimeView) ≃ HashOutputCoordinates where
  toFun value := ((value.2, value.1.1), value.1.2)
  invFun value := ((value.1.2, value.2), value.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
set_option maxRecDepth 100000 in
theorem evalDist_uniformHashOutputCoordinates_bind_reordered {Result : Type}
    (continuation : HashOutputCoordinates → ProbComp Result) :
    𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
      𝒮[($ᵗ HashOutputRest : ProbComp HashOutputRest) >>= fun rest =>
        ($ᵗ FewTimeView : ProbComp FewTimeView) >>= fun view =>
          continuation ((view, rest.1), rest.2)] := by
  let paired : ProbComp (HashOutputRest × FewTimeView) := do
    let rest ← $ᵗ HashOutputRest
    let view ← $ᵗ FewTimeView
    pure (rest, view)
  have hpaired :
      𝒮[paired] = 𝒮[($ᵗ (HashOutputRest × FewTimeView) :
        ProbComp (HashOutputRest × FewTimeView))] := by
    exact evalDist_independent_uniform_pair
  have hreordered :
      𝒮[reorderHashOutputCoordinates <$> paired] =
        𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
    calc
      𝒮[reorderHashOutputCoordinates <$> paired] =
          reorderHashOutputCoordinates <$> 𝒮[paired] := by rw [evalSPMF_map]
      _ = reorderHashOutputCoordinates <$>
          𝒮[($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [hpaired]
      _ = 𝒮[reorderHashOutputCoordinates <$>
          ($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [evalSPMF_map]
      _ = 𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] :=
        evalSPMF_map_bijective_uniform_cross
          (α := HashOutputRest × FewTimeView) (β := HashOutputCoordinates)
          (reorderHashOutputCoordinates : HashOutputRest × FewTimeView →
            HashOutputCoordinates)
          reorderHashOutputCoordinates.bijective
  calc
    𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
        𝒮[(reorderHashOutputCoordinates <$> paired) >>= continuation] := by
      rw [evalSPMF_bind, ← hreordered, ← evalSPMF_bind]
    _ = _ := by
      simp only [paired, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        reorderHashOutputCoordinates, Function.comp_apply]
      rfl
abbrev AdmissibleView := {view : FewTimeView // AdmissibleLeaves view.2}
def admissibleViewEquiv : AdmissibleView ≃ Index × {leaves : IndexGroup → FtsLeaf // AdmissibleLeaves leaves} where
  toFun view := (view.1.1, ⟨view.1.2, view.2⟩)
  invFun value := ⟨(value.1, value.2.1), value.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem card_admissibleView :
    (Fintype.card AdmissibleView : ENNReal) = admissibleProbability * Fintype.card FewTimeView := by
  rw [Fintype.card_congr admissibleViewEquiv, Fintype.card_prod, Fintype.card_subtype, Nat.cast_mul,
    card_admissibleLeaves_eq_mul, Fintype.card_prod, Nat.cast_mul]
  ring
instance : Nonempty AdmissibleView := by
  apply Fintype.card_pos_iff.mp
  have h : (Fintype.card AdmissibleView : ENNReal) ≠ 0 := by
    rw [card_admissibleView]
    exact mul_ne_zero admissibleProbability_pos (by simp)
  exact Nat.pos_of_ne_zero (by exact_mod_cast h)
noncomputable instance : SampleableType AdmissibleView := SampleableType.ofFintype AdmissibleView
noncomputable irreducible_def signerViewSample : ProbComp FewTimeView :=
  Subtype.val <$> ($ᵗ AdmissibleView : ProbComp AdmissibleView)
theorem probOutput_signerViewSample (view : FewTimeView) :
    Pr[= view | signerViewSample] =
      if AdmissibleLeaves view.2 then (admissibleProbability * Fintype.card FewTimeView)⁻¹ else 0 := by
  rw [signerViewSample_def]
  split_ifs with hview
  · rw [show view = (⟨view, hview⟩ : AdmissibleView).val from rfl,
      probOutput_map_injective _ Subtype.val_injective, probOutput_uniformSample, card_admissibleView]
  · rw [probOutput_map_eq_tsum_ite]
    apply ENNReal.tsum_eq_zero.mpr
    intro other
    rw [if_neg]
    rintro rfl
    exact hview other.2
theorem probFailure_signerViewSample : Pr[⊥ | signerViewSample] = 0 := by
  rw [signerViewSample_def, probFailure_map]
  exact probFailure_uniformSample AdmissibleView
theorem probEvent_signerView_index (index : Index) :
    Pr[fun view : FewTimeView => view.1 = index | signerViewSample] = (Fintype.card Index : ENNReal)⁻¹ := by
  classical
  rw [probEvent_eq_tsum_ite, tsum_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single index (fun other _ hother =>
    Finset.sum_eq_zero (fun leaves _ => if_neg hother)) (fun h => (h (Finset.mem_univ _)).elim)]
  simp only [if_true, probOutput_signerViewSample]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_admissibleLeaves_eq_mul]
  have hcard : (Fintype.card FewTimeView : ENNReal) =
      (Fintype.card Index : ENNReal) * Fintype.card (IndexGroup → FtsLeaf) := by
    rw [Fintype.card_prod, Nat.cast_mul]
  rw [hcard, ENNReal.mul_inv (Or.inl admissibleProbability_pos) (Or.inl admissibleProbability_ne_top),
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  calc
    _ = (admissibleProbability * admissibleProbability⁻¹) *
        ((Fintype.card (IndexGroup → FtsLeaf) : ENNReal) * (Fintype.card (IndexGroup → FtsLeaf) : ENNReal)⁻¹) *
          (Fintype.card Index : ENNReal)⁻¹ := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel admissibleProbability_pos admissibleProbability_ne_top,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul, one_mul]
theorem probOutput_uniformFewTimeView (view : FewTimeView) :
    Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] = (Fintype.card FewTimeView : ENNReal)⁻¹ :=
  probOutput_uniformSample FewTimeView view
theorem probOutput_uniformFewTimeView_admissible (view : FewTimeView) :
    (if AdmissibleLeaves view.2 then Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] else 0) =
      admissibleProbability * Pr[= view | signerViewSample] := by
  rw [probOutput_signerViewSample, probOutput_uniformFewTimeView]
  split_ifs
  · rw [ENNReal.mul_inv (Or.inl admissibleProbability_pos) (Or.inl admissibleProbability_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel admissibleProbability_pos admissibleProbability_ne_top, one_mul]
  · rw [mul_zero]
theorem probEvent_uniformFewTimeView_admissible (P : FewTimeView → Prop) :
    Pr[fun view => AdmissibleLeaves view.2 ∧ P view | ($ᵗ FewTimeView : ProbComp FewTimeView)] =
      admissibleProbability * Pr[P | signerViewSample] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro view
  by_cases hP : P view
  · by_cases hadm : AdmissibleLeaves view.2
    · simp only [hP, hadm, and_self, if_true]
      have h := probOutput_uniformFewTimeView_admissible view
      rw [if_pos hadm] at h
      exact h
    · have h := probOutput_uniformFewTimeView_admissible view
      rw [if_neg hadm] at h
      simp only [hP, hadm, and_true, if_false, if_true]
      exact h
  · simp [hP]
theorem probEvent_uniformFewTimeView_admissible_eq :
    Pr[fun view => AdmissibleLeaves view.2 | ($ᵗ FewTimeView : ProbComp FewTimeView)] = admissibleProbability := by
  have h := probEvent_uniformFewTimeView_admissible (fun _ => True)
  simp only [and_true] at h
  rw [h]
  simp
theorem probEvent_uniformFewTimeView_not_admissible :
    Pr[fun view => ¬ AdmissibleLeaves view.2 | ($ᵗ FewTimeView : ProbComp FewTimeView)] =
      1 - admissibleProbability := by
  have hc := probEvent_compl ($ᵗ FewTimeView : ProbComp FewTimeView) (fun view => AdmissibleLeaves view.2)
  rw [probEvent_uniformFewTimeView_admissible_eq] at hc
  simp only [probFailure_uniformSample, tsub_zero] at hc
  exact ENNReal.eq_sub_of_add_eq admissibleProbability_ne_top ((add_comm _ _).trans hc)
theorem probEvent_uniformFewTimeView_bind_le {α : Type} (g : FewTimeView → ProbComp α) (Q : α → Prop)
    (P : FewTimeView → Prop) [DecidablePred P] (bound : ENNReal) (hbound : Pr[P | signerViewSample] ≤ bound)
    (hadmissible : ∀ view, AdmissibleLeaves view.2 → Pr[Q | g view] ≤ if P view then 1 else 0)
    (hrejected : ∀ view, ¬ AdmissibleLeaves view.2 → Pr[Q | g view] ≤ bound) :
    Pr[Q | ($ᵗ FewTimeView : ProbComp FewTimeView) >>= g] ≤ bound := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        ((if AdmissibleLeaves view.2 ∧ P view then 1 else 0) + (if AdmissibleLeaves view.2 then 0 else bound)) := by
      apply ENNReal.tsum_le_tsum
      intro view
      apply mul_le_mul' le_rfl
      by_cases h : AdmissibleLeaves view.2
      · simpa [h] using hadmissible view h
      · simpa [h] using hrejected view h
    _ = Pr[fun view => AdmissibleLeaves view.2 ∧ P view | ($ᵗ FewTimeView : ProbComp FewTimeView)] +
        Pr[fun view => ¬ AdmissibleLeaves view.2 | ($ᵗ FewTimeView : ProbComp FewTimeView)] * bound := by
      simp only [mul_add, ENNReal.tsum_add]
      congr 1
      · rw [probEvent_eq_tsum_ite]
        apply tsum_congr
        intro view
        split_ifs <;> simp
      · rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro view
        split_ifs <;> simp
    _ ≤ admissibleProbability * bound + (1 - admissibleProbability) * bound := by
      rw [probEvent_uniformFewTimeView_admissible, probEvent_uniformFewTimeView_not_admissible]
      gcongr
    _ = bound := by
      rw [← add_mul, add_tsub_cancel_of_le admissibleProbability_le_one, one_mul]
set_option maxRecDepth 100000 in
theorem probEvent_uniformHashOutput_view (P : FewTimeView → Prop) :
    Pr[fun output : HashOutput => P (hashOutputFewTimeView output) | ($ᵗ HashOutput : ProbComp HashOutput)] =
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  let coordinates : HashOutput → FewTimeView × DigestUnusedBits := fun output =>
    digestCoordinates (truncateMessageDigest output)
  calc
    Pr[fun output : HashOutput => P (hashOutputFewTimeView output) | ($ᵗ HashOutput : ProbComp HashOutput)] =
        Pr[fun value => P value.1 | coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun value => P value.1 |
        ($ᵗ (FewTimeView × DigestUnusedBits) : ProbComp (FewTimeView × DigestUnusedBits))] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (by
        simpa only [coordinates] using evalDist_hashOutput_digestCoordinates_uniform)
    _ = Pr[P | Prod.fst <$> ($ᵗ (FewTimeView × DigestUnusedBits) : ProbComp (FewTimeView × DigestUnusedBits))] := by
      rw [probEvent_map]
      rfl
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl) evalSPMF_map_fst_uniformSample_prod
theorem probEvent_uniformHashOutput_admissible_view
    (P : FewTimeView → Prop) :
    Pr[fun output : HashOutput =>
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      admissibleProbability * Pr[P | signerViewSample] := by
  rw [← probEvent_uniformFewTimeView_admissible, ← probEvent_uniformHashOutput_view]
  congr 1
  funext output
  rw [signAttemptResultOfOutput_ne_none_iff, admissible_iff_view]
def OnlyRejectedNewMessageEntries (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) : Prop :=
  ∀ randomness output,
    referenceCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none →
    workingCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output →
    signAttemptResultOfOutput output = none
theorem onlyRejectedNewMessageEntries_self (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) :
    OnlyRejectedNewMessageEntries cache cache secretKey message := by
  intro randomness output hmiss hhit
  rw [hmiss] at hhit
  simp at hhit
theorem onlyRejectedNewMessageEntries_cacheRejected
    (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (output : HashOutput)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message)
    (hrejected : signAttemptResultOfOutput output = none) :
    OnlyRejectedNewMessageEntries referenceCache
      (workingCache.cacheQuery
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled)) output)
      secretKey message := by
  intro randomness found hreferenceFound hfound
  let foundInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : foundInput = sampledInput
  · have hfound' : some output = some found := by
      calc
        some output =
            (workingCache.cacheQuery sampledInput output) sampledInput := by
              rw [QueryCache.cacheQuery_self]
        _ = (workingCache.cacheQuery sampledInput output) foundInput := by rw [hsame]
        _ = some found := by simpa only [foundInput, sampledInput] using hfound
    rw [← Option.some.inj hfound']
    exact hrejected
  · have hworking : workingCache foundInput = some found := by
      rw [QueryCache.cacheQuery_of_ne workingCache output hsame] at hfound
      simpa only [foundInput, sampledInput] using hfound
    exact hinvariant randomness found hreferenceFound hworking
set_option maxRecDepth 100000 in
theorem onlyRejectedNewMessageEntries_of_failed_attempt
    (referenceCache beforeCache afterCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache beforeCache secretKey message)
    (hmem : (none, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message sampled)).run beforeCache)) :
    OnlyRejectedNewMessageEntries referenceCache afterCache secretKey message := by
  intro randomness output hreference hafter
  let target := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : target = sampledInput
  · apply Eq.symm
    have hafterSampled : afterCache sampledInput = some output := by
      change afterCache target = some output at hafter
      rw [← hsame]
      exact hafter
    change afterCache
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message sampled)) = some output at hafterSampled
    exact signAttempt_result_of_cached secretKey message sampled beforeCache afterCache
      none output hafterSampled hmem
  · by_cases hbefore : beforeCache target = none
    · change beforeCache
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none at hbefore
      change (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) ≠
        tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled) at hsame
      have hnone := signAttempt_cache_other_none secretKey message sampled beforeCache afterCache
        none hmem _ hbefore hsame
      rw [hnone] at hafter
      simp at hafter
    · obtain ⟨prior, hprior⟩ := Option.ne_none_iff_exists'.mp hbefore
      have hmemWorld : (none, afterCache) ∈ support
          ((simulateQ romImpl
            (liftM (signAttempt secretKey message sampled :
              OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
                OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))).run
              beforeCache) := by
        rw [simulateQ_romImpl_liftM]
        exact hmem
      have hle : beforeCache ≤ afterCache :=
        simulateQ_romImpl_cache_le
          (liftM (signAttempt secretKey message sampled :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
          beforeCache (none, afterCache) hmemWorld
      have heq : prior = output := Option.some.inj ((hle hprior).symm.trans hafter)
      rw [← heq]
      exact hinvariant randomness prior hreference hprior
def FreshSelectedView (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1 = some (randomness, index, leaves)
      ∧ referenceCache (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)) = none
      ∧ P (selectedFewTimeView index leaves)
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_SubsetTargetAssignment ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def targetTreeMatchCount {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : IndexGroup) : Nat :=
  ∑ slot : Fin n, if ∃ view, views slot = some view ∧ view.1 = target.1 ∧ target.2 tree ∈ Set.range view.2 then 1 else 0
noncomputable def sourceTreeMatch (target source : FewTimeView) (tree : IndexGroup) : Nat :=
  if source.1 = target.1 ∧ target.2 tree ∈ Set.range source.2 then 1 else 0
theorem targetTreeMatchCount_pos_iff {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : IndexGroup) :
    0 < targetTreeMatchCount views target tree ↔ ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ target.2 tree ∈ Set.range view.2 := by
  simp only [targetTreeMatchCount, Finset.sum_pos_iff, Finset.mem_univ, true_and]
  apply exists_congr
  intro slot
  split_ifs <;> simp_all
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def sourceSubsetMatch (target source : FewTimeView) (required : Finset IndexGroup) : Nat :=
  ∏ tree ∈ required, sourceTreeMatch target source tree
theorem sourceTreeMatch_mul_self (target source : FewTimeView) (tree : IndexGroup) :
    sourceTreeMatch target source tree * sourceTreeMatch target source tree = sourceTreeMatch target source tree := by
  unfold sourceTreeMatch
  split_ifs <;> decide
theorem sourceSubsetMatch_mul (target source : FewTimeView) (left right : Finset IndexGroup) :
    sourceSubsetMatch target source left * sourceSubsetMatch target source right =
      sourceSubsetMatch target source (left ∪ right) := by
  induction left using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert tree left hnot ih =>
      by_cases hright : tree ∈ right
      · rw [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right left hright)]
        simp only [sourceSubsetMatch, Finset.prod_insert hnot] at *
        rw [mul_assoc, ih]
        have hmem : tree ∈ left ∪ right := Finset.mem_union_right left hright
        rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem, ← mul_assoc, sourceTreeMatch_mul_self]
      · have hnotunion : tree ∉ left ∪ right := by simp only [Finset.mem_union, not_or]; exact ⟨hnot, hright⟩
        simp only [sourceSubsetMatch, Finset.prod_insert hnot, Finset.insert_union,
          Finset.prod_insert hnotunion] at *
        rw [mul_assoc, ih]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_NormalizedTargetMatches ====
section

section
namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {L : Type} [Fintype L] [Nonempty L]
def LocalTo (coords : Finset IndexGroup) (g : (IndexGroup → L) → ENNReal) : Prop :=
  ∀ first second : IndexGroup → L, (∀ i ∈ coords, first i = second i) → g first = g second
noncomputable def leafAverage (g : (IndexGroup → L) → ENNReal) : ENNReal :=
  ∑ leaves : IndexGroup → L, (Fintype.card (IndexGroup → L) : ENNReal)⁻¹ * g leaves
theorem LocalTo.mono {small large : Finset IndexGroup} {g : (IndexGroup → L) → ENNReal}
    (h : LocalTo small g) (hsub : small ⊆ large) : LocalTo large g :=
  fun first second hagree => h first second (fun i hi => hagree i (hsub hi))
theorem LocalTo.const (coords : Finset IndexGroup) (value : ENNReal) :
    LocalTo (L := L) coords (fun _ => value) := fun _ _ _ => rfl
theorem LocalTo.mul {left right : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo left g) (hh : LocalTo right h) : LocalTo (left ∪ right) (fun leaves => g leaves * h leaves) := by
  intro first second hagree
  dsimp only
  rw [hg first second (fun i hi => hagree i (Finset.mem_union_left _ hi)),
    hh first second (fun i hi => hagree i (Finset.mem_union_right _ hi))]
theorem LocalTo.add {coords : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo coords g) (hh : LocalTo coords h) : LocalTo coords (fun leaves => g leaves + h leaves) := by
  intro first second hagree
  dsimp only
  rw [hg first second hagree, hh first second hagree]
theorem LocalTo.sum {ι : Type} (s : Finset ι) {coords : Finset IndexGroup} {g : ι → (IndexGroup → L) → ENNReal}
    (hg : ∀ x ∈ s, LocalTo coords (g x)) : LocalTo coords (fun leaves => ∑ x ∈ s, g x leaves) := by
  intro first second hagree
  exact Finset.sum_congr rfl (fun x hx => hg x hx first second hagree)
theorem leafAverage_add (g h : (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => g leaves + h leaves) = leafAverage g + leafAverage h := by
  simp only [leafAverage, mul_add, Finset.sum_add_distrib]
theorem leafAverage_mul_left (c : ENNReal) (g : (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => c * g leaves) = c * leafAverage g := by
  simp only [leafAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring
theorem leafAverage_sum {ι : Type} (s : Finset ι) (g : ι → (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => ∑ x ∈ s, g x leaves) = ∑ x ∈ s, leafAverage (g x) := by
  simp only [leafAverage, Finset.mul_sum]
  exact Finset.sum_comm
theorem leafAverage_const (value : ENNReal) : leafAverage (L := L) (fun _ => value) = value := by
  unfold leafAverage
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]
theorem leafAverage_mono {g h : (IndexGroup → L) → ENNReal} (hle : ∀ leaves, g leaves ≤ h leaves) :
    leafAverage g ≤ leafAverage h :=
  Finset.sum_le_sum (fun leaves _ => mul_le_mul' le_rfl (hle leaves))
theorem leafAverage_mul_of_disjoint {left right : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo left g) (hh : LocalTo right h) (hdisjoint : Disjoint left right) :
    leafAverage (fun leaves => g leaves * h leaves) = leafAverage g * leafAverage h := by
  let e := Equiv.piEquivPiSubtypeProd (fun i : IndexGroup => i ∈ left) (fun _ => L)
  let A := ∀ i : {i : IndexGroup // i ∈ left}, L
  let B := ∀ i : {i : IndexGroup // i ∉ left}, L
  obtain ⟨a0⟩ : Nonempty A := inferInstance
  obtain ⟨b0⟩ : Nonempty B := inferInstance
  let g' : A → ENNReal := fun a => g (e.symm (a, b0))
  let h' : B → ENNReal := fun b => h (e.symm (a0, b))
  have hge : ∀ leaves, g leaves = g' (e leaves).1 := by
    intro leaves
    apply hg
    intro i hi
    change leaves i = (e.symm ((e leaves).1, b0)) i
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hhe : ∀ leaves, h leaves = h' (e leaves).2 := by
    intro leaves
    apply hh
    intro i hi
    have hnot : i ∉ left := fun hl => Finset.disjoint_left.mp hdisjoint hl hi
    change leaves i = (e.symm (a0, (e leaves).2)) i
    simp [e, Equiv.piEquivPiSubtypeProd, hnot]
  let w : ENNReal := (Fintype.card (IndexGroup → L) : ENNReal)⁻¹
  have hcard : (Fintype.card (IndexGroup → L) : ENNReal) = (Fintype.card A : ENNReal) * Fintype.card B := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  have hw : w * (Fintype.card A : ENNReal) * Fintype.card B = 1 := by
    rw [mul_assoc, ← hcard]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have hsum : ∀ F : A × B → ENNReal, (∑ leaves : IndexGroup → L, F (e leaves)) = ∑ ab : A × B, F ab :=
    fun F => Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hgh : leafAverage (fun leaves => g leaves * h leaves) = w * ((∑ a, g' a) * ∑ b, h' b) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hge, hhe]
    rw [hsum (fun ab => g' ab.1 * h' ab.2), Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hgavg : leafAverage g = w * ((Fintype.card B : ENNReal) * ∑ a, g' a) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hge]
    rw [hsum (fun ab => g' ab.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hhavg : leafAverage h = w * ((Fintype.card A : ENNReal) * ∑ b, h' b) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hhe]
    rw [hsum (fun ab => h' ab.2), Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hgh, hgavg, hhavg]
  calc
    w * ((∑ a, g' a) * ∑ b, h' b) = (w * (Fintype.card A : ENNReal) * Fintype.card B) * (w * ((∑ a, g' a) * ∑ b, h' b)) := by
      rw [hw, one_mul]
    _ = _ := by ring
theorem leafAverage_coord (i : IndexGroup) (f : L → ENNReal) :
    leafAverage (fun leaves : IndexGroup → L => f (leaves i)) =
      (Fintype.card L : ENNReal)⁻¹ * ∑ x : L, f x := by
  let e := Equiv.piSplitAt i (fun _ : IndexGroup => L)
  let R := ∀ j : {j : IndexGroup // j ≠ i}, L
  have hcard : (Fintype.card (IndexGroup → L) : ENNReal) = (Fintype.card L : ENNReal) * Fintype.card R := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  unfold leafAverage
  rw [← Finset.mul_sum]
  have hsum : (∑ leaves : IndexGroup → L, f (leaves i)) = (Fintype.card R : ENNReal) * ∑ x : L, f x := by
    rw [← Fintype.sum_equiv e.symm (fun value : L × R => f value.1) (fun leaves => f (leaves i))
      (fun value => by simp [e, Equiv.piSplitAt])]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hsum, hcard, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  calc
    _ = (Fintype.card L : ENNReal)⁻¹ * (((Fintype.card R : ENNReal)⁻¹ * Fintype.card R) * ∑ x : L, f x) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
theorem LocalTo.coord (i : IndexGroup) (f : L → ENNReal) :
    LocalTo {i} (fun leaves : IndexGroup → L => f (leaves i)) := by
  intro first second hagree
  dsimp only
  rw [hagree i (Finset.mem_singleton_self i)]
theorem LocalTo.prod {ι : Type} [DecidableEq ι] (s : Finset ι) (coords : ι → Finset IndexGroup)
    {g : ι → (IndexGroup → L) → ENNReal} (hg : ∀ x ∈ s, LocalTo (coords x) (g x)) :
    LocalTo (s.biUnion coords) (fun leaves => ∏ x ∈ s, g x leaves) := by
  intro first second hagree
  apply Finset.prod_congr rfl
  intro x hx
  exact hg x hx first second (fun i hi => hagree i (Finset.mem_biUnion.mpr ⟨x, hx, hi⟩))
theorem leafAverage_prod_coord (U : Finset IndexGroup) (f : IndexGroup → L → ENNReal) :
    leafAverage (fun leaves : IndexGroup → L => ∏ i ∈ U, f i (leaves i)) =
      ∏ i ∈ U, (Fintype.card L : ENNReal)⁻¹ * ∑ x : L, f i x := by
  induction U using Finset.induction_on with
  | empty => simp [leafAverage_const]
  | @insert i U hnot ih =>
      simp only [Finset.prod_insert hnot]
      have hlocal : LocalTo U (fun leaves : IndexGroup → L => ∏ j ∈ U, f j (leaves j)) := by
        have h := LocalTo.prod (L := L) U (fun j => {j}) (g := fun j leaves => f j (leaves j))
          (fun j _ => LocalTo.coord j (f j))
        simpa using h
      rw [leafAverage_mul_of_disjoint (LocalTo.coord i (f i)) hlocal
        (Finset.disjoint_singleton_left.mpr hnot), leafAverage_coord, ih]
theorem leafAverage_prod_disjoint {ι : Type} [DecidableEq ι] (s : Finset ι) (coords : ι → Finset IndexGroup)
    {g : ι → (IndexGroup → L) → ENNReal} (hg : ∀ x ∈ s, LocalTo (coords x) (g x))
    (hdisjoint : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (coords x) (coords y)) :
    leafAverage (fun leaves => ∏ x ∈ s, g x leaves) = ∏ x ∈ s, leafAverage (g x) := by
  induction s using Finset.induction_on with
  | empty => simp [leafAverage_const]
  | @insert a s hnot ih =>
      simp only [Finset.prod_insert hnot]
      have hrest : LocalTo (s.biUnion coords) (fun leaves => ∏ x ∈ s, g x leaves) :=
        LocalTo.prod s coords (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      have hdisj : Disjoint (coords a) (s.biUnion coords) := by
        rw [Finset.disjoint_biUnion_right]
        intro x hx
        exact hdisjoint a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx)
          (fun h => hnot (h ▸ hx))
      rw [leafAverage_mul_of_disjoint (hg a (Finset.mem_insert_self a s)) hrest hdisj,
        ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
          (fun x hx y hy hxy => hdisjoint x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)]
theorem leafAverage_tsum_plain {α : Type} (g : α → (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => ∑' x, g x leaves) = ∑' x, leafAverage (g x) := by
  unfold leafAverage
  simp only [← ENNReal.tsum_mul_left]
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
theorem LocalTo.tsum_plain {α : Type} {coords : Finset IndexGroup} {g : α → (IndexGroup → L) → ENNReal}
    (hg : ∀ x, LocalTo coords (g x)) : LocalTo coords (fun leaves => ∑' x, g x leaves) := by
  intro first second hagree
  exact tsum_congr (fun x => hg x first second hagree)
def ShapeLocal (F : (IndexGroup → L) → TargetShapeVector) : Prop :=
  ∀ groups remaining, TargetShapeValid groups remaining →
    LocalTo (groupCoordinates groups ∪ remaining) (fun leaves => F leaves groups remaining)
def RateLocal (rate : (IndexGroup → L) → TargetRate) : Prop :=
  ∀ coords, LocalTo coords (fun leaves => rate leaves coords)
theorem groupCoordinates_mono {small large : Finset (Finset IndexGroup)} (h : small ⊆ large) :
    groupCoordinates small ⊆ groupCoordinates large :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem mem_groupCoordinates {groups : Finset (Finset IndexGroup)} {i : IndexGroup} :
    i ∈ groupCoordinates groups ↔ ∃ group ∈ groups, i ∈ group := by
  simp [groupCoordinates]
theorem groupCoordinates_insert (selected : Finset IndexGroup) (groups : Finset (Finset IndexGroup)) :
    groupCoordinates (insert selected groups) = selected ∪ groupCoordinates groups := by
  simp [groupCoordinates, Finset.biUnion_insert]
theorem TargetShapeValid.disjoint_step {groups removed : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hremoved : removed ⊆ groups) (hselected : selected ⊆ remaining) :
    Disjoint (groupCoordinates removed ∪ selected) (groupCoordinates (groups \ removed) ∪ (remaining \ selected)) := by
  rw [Finset.disjoint_left]
  intro i hleft hright
  rcases Finset.mem_union.mp hleft with hl | hl <;> rcases Finset.mem_union.mp hright with hr | hr
  · obtain ⟨first, hfirst, hifirst⟩ := mem_groupCoordinates.mp hl
    obtain ⟨second, hsecond, hisecond⟩ := mem_groupCoordinates.mp hr
    have hsecond' := Finset.mem_sdiff.mp hsecond
    have hne : first ≠ second := fun h => hsecond'.2 (h ▸ hfirst)
    exact Finset.disjoint_left.mp (hvalid.disjoint first (hremoved hfirst) second hsecond'.1 hne) hifirst hisecond
  · obtain ⟨first, hfirst, hifirst⟩ := mem_groupCoordinates.mp hl
    exact Finset.disjoint_left.mp (hvalid.remaining first (hremoved hfirst)) hifirst (Finset.mem_sdiff.mp hr).1
  · obtain ⟨second, hsecond, hisecond⟩ := mem_groupCoordinates.mp hr
    exact Finset.disjoint_left.mp (hvalid.remaining second (Finset.mem_sdiff.mp hsecond).1) hisecond (hselected hl)
  · exact (Finset.mem_sdiff.mp hr).2 hl
theorem step_coordinates_subset {groups removed : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hremoved : removed ⊆ groups) (hselected : selected ⊆ remaining) :
    (groupCoordinates removed ∪ selected) ∪ (groupCoordinates (groups \ removed) ∪ (remaining \ selected)) ⊆
      groupCoordinates groups ∪ remaining := by
  intro i hi
  simp only [Finset.mem_union] at hi ⊢
  rcases hi with (hi | hi) | (hi | hi)
  · exact Or.inl (groupCoordinates_mono hremoved hi)
  · exact Or.inr (hselected hi)
  · exact Or.inl (groupCoordinates_mono Finset.sdiff_subset hi)
  · exact Or.inr (Finset.mem_sdiff.mp hi).1
theorem TargetShapeValid.groupCoordinates_nonempty {groups removed : Finset (Finset IndexGroup)}
    {remaining : Finset IndexGroup} (hvalid : TargetShapeValid groups remaining) (hremoved : removed ⊆ groups)
    (hne : removed ≠ ∅) : (groupCoordinates removed).Nonempty := by
  obtain ⟨group, hgroup⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨i, hi⟩ := hvalid.nonempty group (hremoved hgroup)
  exact ⟨i, mem_groupCoordinates.mpr ⟨group, hgroup, hi⟩⟩
theorem reuse_coordinates_subset {groups : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hselected : selected ⊆ remaining) :
    groupCoordinates (insert selected groups) ∪ (remaining \ selected) ⊆ groupCoordinates groups ∪ remaining := by
  rw [groupCoordinates_insert]
  intro i hi
  simp only [Finset.mem_union] at hi ⊢
  rcases hi with (hi | hi) | hi
  · exact Or.inr (hselected hi)
  · exact Or.inl hi
  · exact Or.inr (Finset.mem_sdiff.mp hi).1
theorem shapeLocal_query {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    (hF : ShapeLocal F) (harrival : RateLocal arrival) :
    ShapeLocal (fun leaves => targetShapeQuery (arrival leaves) (F leaves)) := by
  intro groups remaining hvalid
  unfold targetShapeQuery targetArrivalStep
  apply (hF groups remaining hvalid).add
  apply LocalTo.sum
  intro removed hremoved
  have hsub : removed ⊆ groups := Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2
  have h := (harrival (groupCoordinates removed)).mul
    (hF (groups \ removed) remaining (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _)))
  refine h.mono ?_
  have hs := step_coordinates_subset (groups := groups) (remaining := remaining) (selected := ∅) hsub (Finset.empty_subset _)
  simpa only [Finset.union_empty, Finset.sdiff_empty] using hs
theorem shapeLocal_signing {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) (hF : ShapeLocal F) (hrate : RateLocal rate) :
    ShapeLocal (fun leaves => targetShapeSigning (rate leaves) reuse (F leaves)) := by
  intro groups remaining hvalid
  unfold targetShapeSigning targetFreshStep targetReuseStep
  refine ((hF groups remaining hvalid).add ?_).add ?_
  · apply LocalTo.sum
    intro removed hremoved
    apply LocalTo.sum
    intro selected hselected
    have hsubG := Finset.mem_powerset.mp hremoved
    have hsubR := Finset.mem_powerset.mp hselected
    by_cases hempty : removed = ∅ ∧ selected = ∅
    · simp only [hempty, and_self, if_true]
      exact LocalTo.const _ 0
    · simp only [hempty, if_false]
      exact ((hrate _).mul (hF _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))).mono
        (step_coordinates_subset hsubG hsubR)
  · have hsum : LocalTo (groupCoordinates groups ∪ remaining) (fun leaves =>
        ∑ selected ∈ remaining.powerset.erase ∅, F leaves (insert selected groups) (remaining \ selected)) := by
      apply LocalTo.sum
      intro selected hselected
      have hne := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2
      exact (hF _ _ (hvalid.reuse hne hsub)).mono (reuse_coordinates_subset hsub)
    exact ((LocalTo.const ∅ reuse).mul hsum).mono (by rw [Finset.empty_union])
noncomputable def averagedShape (F : (IndexGroup → L) → TargetShapeVector) : TargetShapeVector :=
  fun groups remaining => leafAverage (fun leaves => F leaves groups remaining)
theorem leafAverage_query_le {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    {average : ENNReal} (hF : ShapeLocal F) (harrival : RateLocal arrival)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeQuery (arrival leaves) (F leaves)))
      (targetShapeQuery (constRate average) (averagedShape F)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeQuery targetArrivalStep constRate
  rw [leafAverage_add, leafAverage_sum]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro removed hremoved
  have hsub : removed ⊆ groups := Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2
  have hdisjoint := hvalid.disjoint_step hsub (Finset.empty_subset remaining)
  simp only [Finset.union_empty, Finset.sdiff_empty] at hdisjoint
  rw [leafAverage_mul_of_disjoint (harrival _)
    (hF (groups \ removed) remaining (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _))) hdisjoint]
  exact mul_le_mul' (haverage _ (hvalid.groupCoordinates_nonempty hsub (Finset.mem_erase.mp hremoved).1)) le_rfl
theorem leafAverage_signing_le {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) {average : ENNReal} (hF : ShapeLocal F) (hrate : RateLocal rate)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ average) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeSigning (rate leaves) reuse (F leaves)))
      (targetShapeSigning (constRate average) reuse (averagedShape F)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeSigning targetFreshStep constRate
  rw [leafAverage_add, leafAverage_add, leafAverage_mul_left, leafAverage_sum]
  apply add_le_add (add_le_add le_rfl _) _
  · apply Finset.sum_le_sum
    intro removed hremoved
    rw [leafAverage_sum]
    apply Finset.sum_le_sum
    intro selected hselected
    by_cases hempty : removed = ∅ ∧ selected = ∅
    · simp only [hempty, and_self, if_true]
      rw [leafAverage_const]
    · simp only [hempty, if_false]
      rw [leafAverage_mul_of_disjoint (hrate _)
        (hF _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))
        (hvalid.disjoint_step (Finset.mem_powerset.mp hremoved) (Finset.mem_powerset.mp hselected))]
      apply mul_le_mul' (haverage _ _) le_rfl
      by_cases hr : removed = ∅
      · have hs : selected ≠ ∅ := fun h => hempty ⟨hr, h⟩
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        exact ⟨i, Finset.mem_union_right _ hi⟩
      · obtain ⟨i, hi⟩ := hvalid.groupCoordinates_nonempty (Finset.mem_powerset.mp hremoved) hr
        exact ⟨i, Finset.mem_union_left _ hi⟩
  · unfold targetReuseStep
    rw [leafAverage_sum]
theorem leafAverage_query_iterate_le {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    {average : ENNReal} (hF : ShapeLocal F) (harrival : RateLocal arrival)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average) (queries : Nat) :
    ShapeLocal (fun leaves => (targetShapeQuery (arrival leaves))^[queries] (F leaves)) ∧
      TargetShapeLE (averagedShape (fun leaves => (targetShapeQuery (arrival leaves))^[queries] (F leaves)))
        ((targetShapeQuery (constRate average))^[queries] (averagedShape F)) := by
  induction queries with
  | zero => exact ⟨hF, TargetShapeLE.refl _⟩
  | succ queries ih =>
      simp only [Function.iterate_succ_apply']
      exact ⟨shapeLocal_query ih.1 harrival,
        (leafAverage_query_le ih.1 harrival haverage).trans (targetShapeQuery_mono _ ih.2)⟩
theorem leafAverage_signing_iterate_le {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) {average : ENNReal} (hF : ShapeLocal F) (hrate : RateLocal rate)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ average) (signings : Nat) :
    ShapeLocal (fun leaves => (targetShapeSigning (rate leaves) reuse)^[signings] (F leaves)) ∧
      TargetShapeLE (averagedShape (fun leaves => (targetShapeSigning (rate leaves) reuse)^[signings] (F leaves)))
        ((targetShapeSigning (constRate average) reuse)^[signings] (averagedShape F)) := by
  induction signings with
  | zero => exact ⟨hF, TargetShapeLE.refl _⟩
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact ⟨shapeLocal_signing reuse ih.1 hrate,
        (leafAverage_signing_le reuse ih.1 hrate haverage).trans (targetShapeSigning_mono _ reuse ih.2)⟩
theorem leafAverage_targetShapeEnvelope_le {F : (IndexGroup → L) → TargetShapeVector}
    {rate arrival : (IndexGroup → L) → TargetRate} (reuse : ENNReal) {uniform average : ENNReal}
    (hF : ShapeLocal F) (hrate : RateLocal rate) (harrival : RateLocal arrival)
    (huniform : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ uniform)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average)
    (queries signings : Nat) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeEnvelope (rate leaves) reuse (arrival leaves) queries signings (F leaves)))
      (targetShapeEnvelope (constRate uniform) reuse (constRate average) queries signings (averagedShape F)) := by
  have hq := leafAverage_query_iterate_le hF harrival haverage queries
  have hs := leafAverage_signing_iterate_le reuse hq.1 hrate huniform signings
  exact hs.2.trans (targetShapeSigning_iterate_mono _ reuse signings hq.2)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem expected_uniformHashOutput_admissible_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) =
      admissibleProbability *
        ∑' target, Pr[= target | signerViewSample] * weight target := by
  have hexpand (output : HashOutput) :
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0) =
        ∑' target, if Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target then weight target else 0 := by
    by_cases h : Admissible (truncateMessageDigest output) <;> simp only [h, true_and, false_and, if_true, if_false, tsum_zero]
    simp
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      simp only [← signAttemptResultOfOutput_ne_none_iff]
      rw [probEvent_uniformHashOutput_admissible_view (fun view => view = target),
        probEvent_eq_eq_probOutput, mul_assoc]
theorem expected_uniformHashOutput_view_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * weight (hashOutputFewTimeView output)) =
      ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  have hexpand (output : HashOutput) :
      weight (hashOutputFewTimeView output) =
        ∑' target, if hashOutputFewTimeView output = target then weight target else 0 := by
    rw [tsum_eq_single (hashOutputFewTimeView output) (fun other hother => if_neg (Ne.symm hother)), if_pos rfl]
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => hashOutputFewTimeView output = target | ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      rw [probEvent_uniformHashOutput_view (fun view => view = target), probEvent_eq_eq_probOutput]
theorem expected_uniformHashOutput_admissible_weight_le_uniform (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) ≤
      ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  rw [← expected_uniformHashOutput_view_weight]
  apply ENNReal.tsum_le_tsum
  intro output
  apply mul_le_mul' le_rfl
  split_ifs <;> simp
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def openedLeaves (source : FewTimeView) : Finset FtsLeaf := Finset.univ.image source.2
theorem mem_openedLeaves_iff {source : FewTimeView} {leaf : FtsLeaf} :
    leaf ∈ openedLeaves source ↔ leaf ∈ Set.range source.2 := by
  simp [openedLeaves]
theorem card_openedLeaves_le (source : FewTimeView) : (openedLeaves source).card ≤ ftsOpenings := by
  unfold openedLeaves
  exact Finset.card_image_le.trans (by simp)
theorem sourceSubsetMatch_leaves (index : Index) (leaves : IndexGroup → FtsLeaf) (source : FewTimeView)
    (required : Finset IndexGroup) (hne : required.Nonempty) :
    (sourceSubsetMatch (index, leaves) source required : ENNReal) =
      (if source.1 = index then 1 else 0) *
        ∏ i ∈ required, (if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0) := by
  unfold sourceSubsetMatch sourceTreeMatch
  rw [Nat.cast_prod]
  by_cases hindex : source.1 = index
  · simp only [hindex, true_and, if_true, one_mul, mem_openedLeaves_iff]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  · obtain ⟨i, hi⟩ := hne
    simp only [hindex, false_and, if_false, zero_mul, Nat.cast_zero]
    exact Finset.prod_eq_zero hi rfl
theorem sourceSubsetMatch_local (index : Index) (source : FewTimeView) (required : Finset IndexGroup) :
    LocalTo required (fun leaves : IndexGroup → FtsLeaf =>
      (sourceSubsetMatch (index, leaves) source required : ENNReal)) := by
  intro first second hagree
  dsimp only
  unfold sourceSubsetMatch sourceTreeMatch
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [hagree i hi]
end SphincsSecurity.Concrete
end
section
set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem sourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset IndexGroup) (selected : Finset (Fin m)) :
    (∏ slot ∈ selected, sourceSubsetMatch target source (groups slot)) =
      sourceSubsetMatch target source (selected.biUnion groups) := by
  induction selected using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert slot selected hnot ih =>
      rw [Finset.prod_insert hnot, Finset.biUnion_insert, ih, sourceSubsetMatch_mul]
noncomputable def coverNormalization : ENNReal := (Fintype.card FtsLeaf : ENNReal) / ftsOpenings
theorem coverNormalization_ne_top : coverNormalization ≠ ⊤ :=
  ENNReal.div_ne_top (by simp) (by simp [ftsOpenings])
theorem coverNormalization_ne_zero : coverNormalization ≠ 0 :=
  ENNReal.div_ne_zero.mpr ⟨by simp, by simp⟩
noncomputable def coverScale : ENNReal := (ftsOpenings : ENNReal) / Fintype.card FtsLeaf
theorem coverNormalization_mul_coverScale : coverNormalization * coverScale = 1 := by
  unfold coverNormalization coverScale
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = ((Fintype.card FtsLeaf : ENNReal) * (Fintype.card FtsLeaf : ENNReal)⁻¹) *
        (((ftsOpenings : Nat) : ENNReal)⁻¹ * ftsOpenings) := by ring
    _ = 1 := by
      rw [ENNReal.mul_inv_cancel (by simp) (by simp), ENNReal.inv_mul_cancel (by simp [ftsOpenings]) (by simp), one_mul]
noncomputable def normalizedSourceSubsetMatch (target source : FewTimeView) (required : Finset IndexGroup) : ENNReal :=
  coverNormalization ^ required.card * (sourceSubsetMatch target source required : ENNReal)
theorem normalizedSourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, sourceSubsetMatch_prod, Finset.card_biUnion hdisjoint]
noncomputable def signerRate (target : FewTimeView) : TargetRate := fun coords =>
  ∑' source, Pr[= source | signerViewSample] * normalizedSourceSubsetMatch target source coords
noncomputable def arrivalRate (target : FewTimeView) : TargetRate := fun coords =>
  admissibleProbability * signerRate target coords
theorem expected_signer_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' source, Pr[= source | signerViewSample] *
      ∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      signerRate target (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint, signerRate]
theorem expected_hash_normalizedSourceSubsetMatch (target : FewTimeView) (coords : Finset IndexGroup) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        normalizedSourceSubsetMatch target (hashOutputFewTimeView output) coords else 0)) =
      arrivalRate target coords := by
  rw [expected_uniformHashOutput_admissible_weight (fun source => normalizedSourceSubsetMatch target source coords)]
  rfl
theorem expected_hash_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        ∏ slot ∈ selected, normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0)) =
      arrivalRate target (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint]
  exact expected_hash_normalizedSourceSubsetMatch target _
theorem LocalTo.tsum {α : Type} {coords : Finset IndexGroup} (weight : α → ENNReal)
    {g : α → (IndexGroup → FtsLeaf) → ENNReal} (hg : ∀ x, LocalTo coords (g x)) :
    LocalTo coords (fun leaves => ∑' x, weight x * g x leaves) := by
  intro first second hagree
  exact tsum_congr (fun x => by rw [hg x first second hagree])
theorem leafAverage_tsum {α : Type} (weight : α → ENNReal) (g : α → (IndexGroup → FtsLeaf) → ENNReal) :
    leafAverage (fun leaves => ∑' x, weight x * g x leaves) = ∑' x, weight x * leafAverage (g x) := by
  unfold leafAverage
  simp only [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring
theorem normalizedSourceSubsetMatch_local (index : Index) (source : FewTimeView) (coords : Finset IndexGroup) :
    LocalTo coords (fun leaves => normalizedSourceSubsetMatch (index, leaves) source coords) := by
  intro first second hagree
  dsimp only
  unfold normalizedSourceSubsetMatch
  have h := sourceSubsetMatch_local index source coords first second hagree
  dsimp only at h
  rw [h]
theorem leafAverage_normalizedSourceSubsetMatch_le (index : Index) (source : FewTimeView)
    (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => normalizedSourceSubsetMatch (index, leaves) source coords) ≤
      if source.1 = index then 1 else 0 := by
  unfold normalizedSourceSubsetMatch
  simp only [sourceSubsetMatch_leaves index _ source coords hne]
  have hrewrite : (fun leaves : IndexGroup → FtsLeaf => coverNormalization ^ coords.card *
      ((if source.1 = index then (1 : ENNReal) else 0) *
        ∏ i ∈ coords, if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0)) =
      fun leaves => (coverNormalization ^ coords.card * if source.1 = index then (1 : ENNReal) else 0) *
        ∏ i ∈ coords, if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0 := by
    funext leaves
    ring
  have hprod := leafAverage_prod_coord (L := FtsLeaf) coords
    (fun _ leaf => if leaf ∈ openedLeaves source then (1 : ENNReal) else 0)
  rw [hrewrite, leafAverage_mul_left, hprod]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases hindex : source.1 = index
  · simp only [hindex, if_true, mul_one]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_one'
    intro i _
    have hopened : ((openedLeaves source).card : ENNReal) ≤ ftsOpenings := by
      exact_mod_cast card_openedLeaves_le source
    calc
      coverNormalization * ((Fintype.card FtsLeaf : ENNReal)⁻¹ * ((openedLeaves source).card : ENNReal)) ≤
          coverNormalization * ((Fintype.card FtsLeaf : ENNReal)⁻¹ * ftsOpenings) := by gcongr
      _ = 1 := by
        unfold coverNormalization
        rw [div_eq_mul_inv]
        calc
          _ = ((Fintype.card FtsLeaf : ENNReal) * (Fintype.card FtsLeaf : ENNReal)⁻¹) *
              (((ftsOpenings : Nat) : ENNReal)⁻¹ * ftsOpenings) := by ring
          _ = 1 := by
            rw [ENNReal.mul_inv_cancel (by simp) (by simp), ENNReal.inv_mul_cancel (by simp [ftsOpenings]) (by simp),
              one_mul]
  · simp only [hindex, if_false, mul_zero, zero_mul, le_refl]
theorem signerRate_local (index : Index) : RateLocal (fun leaves => signerRate (index, leaves)) :=
  fun coords => LocalTo.tsum _ (fun source => normalizedSourceSubsetMatch_local index source coords)
theorem arrivalRate_local (index : Index) : RateLocal (fun leaves => arrivalRate (index, leaves)) := by
  intro coords first second hagree
  show admissibleProbability * signerRate (index, first) coords = admissibleProbability * signerRate (index, second) coords
  have h := signerRate_local index coords first second hagree
  dsimp only at h
  rw [h]
theorem leafAverage_signerRate_le (index : Index) (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => signerRate (index, leaves) coords) ≤ (Fintype.card Index : ENNReal)⁻¹ := by
  unfold signerRate
  rw [leafAverage_tsum]
  calc
    _ ≤ ∑' source, Pr[= source | signerViewSample] * (if source.1 = index then 1 else 0) :=
      ENNReal.tsum_le_tsum (fun source => mul_le_mul' le_rfl
        (leafAverage_normalizedSourceSubsetMatch_le index source coords hne))
    _ = _ := by
      rw [← probEvent_signerView_index index, probEvent_eq_tsum_ite]
      apply tsum_congr
      intro source
      split_ifs <;> simp
theorem leafAverage_arrivalRate_le (index : Index) (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => arrivalRate (index, leaves) coords) ≤ cachedIndexRate := by
  unfold arrivalRate
  rw [leafAverage_mul_left]
  exact mul_le_mul' le_rfl (leafAverage_signerRate_le index coords hne)
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_NormalizedTargetCacheQuery ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def cachedTargetSubsetMatch (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset IndexGroup) : ENNReal :=
  cacheMessageWeight parameter (fun input source =>
    if input = targetInput then 0 else (sourceSubsetMatch target source required : ENNReal)) cache
theorem cachedTargetSubsetMatch_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    cachedTargetSubsetMatch parameter (before.cacheQuery input output) targetInput target required =
      cachedTargetSubsetMatch parameter before targetInput target required +
        if FtsProbeSimulation.MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) then
          if input = targetInput then 0 else (sourceSubsetMatch target (hashOutputFewTimeView output) required : ENNReal) else 0 := by
  exact cacheMessageWeight_cacheQuery parameter _ before input output hfresh
theorem cachedTargetSubsetMatch_cacheQuery_self (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (output : HashOutput)
    (hfresh : before targetInput = none) :
    cachedTargetSubsetMatch parameter (before.cacheQuery targetInput output) targetInput target required =
      cachedTargetSubsetMatch parameter before targetInput target required := by
  rw [cachedTargetSubsetMatch_cacheQuery parameter before targetInput target required targetInput output hfresh]
  simp only [if_true, ite_self, add_zero]
end SphincsSecurity.Concrete
end
section
set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def normalizedCachedTargetSubsetMatch (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset IndexGroup) : ENNReal :=
  coverNormalization ^ required.card * cachedTargetSubsetMatch parameter cache targetInput target required
noncomputable def normalizedTargetCacheProduct (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup) : ENNReal :=
  ∏ slot : Fin m, normalizedCachedTargetSubsetMatch parameter cache targetInput target (groups slot)
theorem normalizedCachedTargetSubsetMatch_eq_weight (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset IndexGroup) :
    normalizedCachedTargetSubsetMatch parameter cache targetInput target required =
      cacheMessageWeight parameter (fun input source => if input = targetInput then 0 else normalizedSourceSubsetMatch target source required) cache := by
  unfold normalizedCachedTargetSubsetMatch cachedTargetSubsetMatch
  rw [mul_comm, ← cacheMessageWeight_mul_right]
  congr 1
  funext input source
  split_ifs
  · rw [zero_mul]
  · simp only [normalizedSourceSubsetMatch]
    ring
theorem normalizedCachedTargetSubsetMatch_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    normalizedCachedTargetSubsetMatch parameter (before.cacheQuery input output) targetInput target required =
      normalizedCachedTargetSubsetMatch parameter before targetInput target required +
        if Admissible (truncateMessageDigest output) then normalizedSourceSubsetMatch target (hashOutputFewTimeView output) required else 0 := by
  simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery parameter before targetInput target required input output hfresh,
    hmessage, true_and, if_neg hne, mul_add, mul_ite, mul_zero, normalizedSourceSubsetMatch]
theorem normalizedTargetCacheProduct_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    normalizedTargetCacheProduct parameter (before.cacheQuery input output) targetInput target groups =
      normalizedTargetCacheProduct parameter before targetInput target groups +
        ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
          (if Admissible (truncateMessageDigest output) then
            ∏ slot ∈ selected, normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0) *
              ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot) := by
  unfold normalizedTargetCacheProduct
  simp only [normalizedCachedTargetSubsetMatch_cacheQuery parameter before targetInput target _ input output hfresh hmessage hne]
  rw [show (∏ slot : Fin m, (normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot) +
      if Admissible (truncateMessageDigest output) then normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0)) =
      ∏ slot : Fin m, ((if Admissible (truncateMessageDigest output) then normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0) +
        normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot)) by simp only [add_comm]]
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro selected hselected
  congr 1
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simp only [hadmissible, if_true]
  · simp only [hadmissible, if_false]
    obtain ⟨slot, hslot⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
    exact Finset.prod_eq_zero hslot rfl
theorem expected_normalizedTargetCacheProduct_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (input : HashInput) (hfresh : before input = none)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      normalizedTargetCacheProduct parameter (before.cacheQuery input output) targetInput target groups) =
      normalizedTargetCacheProduct parameter before targetInput target groups +
          ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
            arrivalRate target (selected.biUnion groups) *
              ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot) := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [normalizedTargetCacheProduct_cacheQuery parameter before targetInput target groups input _ hfresh hmessage hne,
    mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  congr 1
  apply Finset.sum_congr rfl
  intro selected hselected
  simp only [← mul_assoc, ENNReal.tsum_mul_right]
  congr 1
  exact expected_hash_normalizedSourceSubsetMatch_prod target groups selected
    (fun i _ j _ hij => hdisjoint hij)
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_TerminalCache ====
section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem CachedRun.messageDigest_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {root : Digest}
    {message : Message} {randomness : Randomness}
    (hrun : CachedRun cache f (messageDigest parameter root message randomness)) :
    cache (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness)) ≠ none := by
  apply hrun
  rw [messageDigest]
  apply queriedInputs_mono_bind_left
  change tweakableHashInput parameter .message
      (messageDigestPayload root message randomness) ∈
    [tweakableHashInput parameter .message (messageDigestPayload root message randomness)]
  simp
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_CachedSigningViews ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem signWithView_successful_cached_output (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Signature) (view : Option FewTimeView)
    (hresult : ((some signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    ∃ output, after (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message signature.randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ view = some (hashOutputFewTimeView output) := by
  obtain ⟨randomness, index, leaves, loopCache, hloop, hfinish, hview⟩ :=
    signWithView_support_some key message before after signature view hresult
  have hrandomness := signAfterDigest_support_some_randomness key randomness index leaves loopCache after signature hfinish
  have hloopLe : loopCache ≤ after :=
    (replay_of_mem_support (signAfterDigest key randomness index leaves) loopCache (some signature) after hfinish
      (fromCache after) (agreesWithFn_fromCache after)).1
  have hf : loopCache.AgreesWithFn (fromCache after) := fun _ _ h => agreesWithFn_fromCache after (hloopLe h)
  have hreplay := replayRom_of_mem_support (signDigestLoop digestAttemptLimit key message) before
    (some (randomness, index, leaves)) loopCache hloop (fromCache after) hf
  have hgood := successfulDigestLoop_of_mem_support (fromCache after) key message digestAttemptLimit randomness index leaves
    before loopCache after hreplay hloopLe (agreesWithFn_fromCache after)
  obtain ⟨_, digest, heval, hadmissible, hindex, hleaves, hcached⟩ := hgood.extract
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hcached)
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    change truncateMessageDigest (fromCache after (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness))) = truncateMessageDigest output
    rw [agreesWithFn_fromCache after houtput]
  refine ⟨output, ?_, hdigest ▸ hadmissible, ?_⟩
  · rw [hrandomness]
    exact houtput
  · simpa only [selectedFewTimeView, hindex, hleaves, hdigest, hashOutputFewTimeView, fullDigestView] using hview
theorem signDigestLoop_new_admissible_selected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)))
    (hresult : (result, after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    ∃ randomness index leaves, result = some (randomness, index, leaves) ∧
      payload = messageDigestPayload key.root message randomness := by
  induction attempts generalizing before after result with
  | zero =>
      have heq : (result, after) = (none, before) := by
        simpa only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hresult
      have hcache : after = before := congrArg Prod.snd heq
      rw [hcache, hbefore] at hafter
      contradiction
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      cases attempt with
      | none =>
          simp only [signDigestLoopContinuation] at hfinish
          by_cases hsame : payload = messageDigestPayload key.root message sampled
          · have hle := simulateQ_romImpl_cache_le (signDigestLoop attempts key message) attemptCache (result, after) hfinish
            have heval := (replay_of_mem_support_of_le (signAttempt key message sampled) before none attemptCache after hattempt hle
              (fromCache after) (agreesWithFn_fromCache after)).1
            have hanswer : fromCache after (tweakableHashInput key.parameter .message
                (messageDigestPayload key.root message sampled)) = output :=
              agreesWithFn_fromCache after (hsame ▸ hafter)
            simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
              hanswer, evalWithAnswerFn_pure, hadmissible, if_pos] at heval
            exact False.elim (by simp only [reduceCtorEq] at heval)
          · have hnone := signAttempt_cache_other_none key message sampled before attemptCache none hattempt
              (tweakableHashInput key.parameter .message payload) hbefore (fun h =>
                hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) h).2)
            exact ih attemptCache after result hfinish hnone hafter
      | some selected =>
          obtain ⟨index, leaves⟩ := selected
          have heq : (result, after) = (some (sampled, index, leaves), attemptCache) := by
            simpa only [signDigestLoopContinuation, support_pure, Set.mem_singleton_iff] using hfinish
          by_cases hsame : payload = messageDigestPayload key.root message sampled
          · exact ⟨sampled, index, leaves, congrArg Prod.fst heq, hsame⟩
          · have hnone := signAttempt_cache_other_none key message sampled before attemptCache (some (index, leaves)) hattempt
              (tweakableHashInput key.parameter .message payload) hbefore (fun h =>
                hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) h).2)
            have hcache : after = attemptCache := congrArg Prod.snd heq
            rw [hcache, hnone] at hafter
            exact False.elim (by simp only [reduceCtorEq] at hafter)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem SigningDigestsCached.mono {parameter : PublicParameter} {root : Digest}
    {before after : QueryCache HashSpec} {log : QueryLog SigningSpec}
    (hsigned : SigningDigestsCached parameter before root log) (hcache : before ≤ after) :
    SigningDigestsCached parameter after root log := by
  intro entry hentry signature hresponse
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned entry hentry signature hresponse)
  exact Option.ne_none_iff_exists'.mpr ⟨output, hcache houtput⟩
theorem eligibleSigningView?_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (payload : HashInput) (entry : SigningEntry)
    (hsigned : ∀ signature, entry.2 = some signature →
      messageAnswers parameter before (messageDigestPayload root entry.1 signature.randomness) ≠ none) :
    eligibleSigningView? (messageAnswers parameter after) root payload entry =
      eligibleSigningView? (messageAnswers parameter before) root payload entry := by
  cases hresponse : entry.2 with
  | none => simp [eligibleSigningView?, hresponse]
  | some signature =>
      obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned signature hresponse)
      have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some output := hcache houtput
      simp [eligibleSigningView?, observedSigningView?, hresponse, houtput, hafter]
theorem SigningDigestsCached.after_signing (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (response : Option Signature) (view : Option FewTimeView)
    (hresult : ((response, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    SigningDigestsCached key.parameter after key.root (log ++ [⟨message, response⟩]) := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before ((response, view), after) hresult
  intro entry hentry signature hresponse
  rcases List.mem_append.mp hentry with hold | hnew
  · exact (hsigned.mono hcache) entry hold signature hresponse
  · obtain rfl := List.mem_singleton.mp hnew
    have hresponse' : response = some signature := hresponse
    rw [hresponse'] at hresult
    obtain ⟨output, houtput, _, _⟩ := signWithView_successful_cached_output key message before after signature view hresult
    exact Option.ne_none_iff_exists'.mpr ⟨output, houtput⟩
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetSigningMatchFactors ====
section

set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem targetTreeMatchCount_log (log : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : IndexGroup) :
    targetTreeMatchCount (fun slot => view (log.get slot)) target tree =
      (log.map (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ target.2 tree ∈ Set.range source.2 then 1 else 0)).sum := by
  rw [targetTreeMatchCount, ← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map log
    (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ target.2 tree ∈ Set.range source.2 then 1 else 0))
theorem targetTreeMatchCount_log_append (log suffix : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : IndexGroup) :
    targetTreeMatchCount (fun slot => view ((log ++ suffix).get slot)) target tree =
      targetTreeMatchCount (fun slot => view (log.get slot)) target tree +
        targetTreeMatchCount (fun slot => view (suffix.get slot)) target tree := by
  simp only [targetTreeMatchCount_log, List.map_append, List.sum_append]
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def normalizedTargetLogMatch (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (tree : IndexGroup) : ENNReal :=
  coverNormalization *
    (targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log) target tree : ENNReal)
noncomputable def normalizedTargetLogProduct (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) : ENNReal :=
  ∏ tree ∈ required, normalizedTargetLogMatch key cache log payload target tree
theorem targetTreeMatchCount_log_append_singleton (log : List α) (entry : α) (view : α → Option FewTimeView)
    (target : FewTimeView) (tree : IndexGroup) :
    targetTreeMatchCount (fun slot => view ((log ++ [entry]).get slot)) target tree =
      targetTreeMatchCount (fun slot => view (log.get slot)) target tree +
        if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ target.2 tree ∈ Set.range source.2 then 1 else 0 := by
  simp only [targetTreeMatchCount_log_append, targetTreeMatchCount_log, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
theorem normalizedSourceSubsetMatch_singleton (target source : FewTimeView) (tree : IndexGroup) :
    normalizedSourceSubsetMatch target source {tree} = coverNormalization * (sourceTreeMatch target source tree : ENNReal) := by
  simp only [normalizedSourceSubsetMatch, Finset.card_singleton, pow_one, sourceSubsetMatch, Finset.prod_singleton]
theorem eligibleSigningViews_cache_stable (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (hcache : before ≤ after)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    eligibleSigningViews (messageAnswers key.parameter after) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root payload log := by
  funext slot
  exact eligibleSigningView?_cache_stable key.parameter key.root before after hcache payload (log.get slot)
    (hsigned _ (List.get_mem _ _))
theorem normalizedTargetLogMatch_le_of_eligibleView (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (payload : HashInput) (target source : FewTimeView) (tree : IndexGroup)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hentry : eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = none ∨
      eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = some source) :
    normalizedTargetLogMatch key after (log ++ [entry]) payload target tree ≤
      normalizedTargetLogMatch key before log payload target tree + normalizedSourceSubsetMatch target source {tree} := by
  have hstable := eligibleSigningViews_cache_stable key before after log payload hcache hsigned
  have hstep := targetTreeMatchCount_log_append_singleton log entry
    (eligibleSigningView? (messageAnswers key.parameter after) key.root payload) target tree
  change targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload (log ++ [entry])) target tree =
    targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload log) target tree + _ at hstep
  rw [hstable] at hstep
  rw [normalizedTargetLogMatch, hstep, Nat.cast_add, mul_add, normalizedSourceSubsetMatch_singleton]
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  apply Nat.cast_le.mpr
  rcases hentry with hnone | hsome
  · simp only [hnone, reduceCtorEq, false_and, exists_false, if_false, Nat.zero_le]
  · simp only [hsome, Option.some.injEq, exists_eq_left', sourceTreeMatch, le_refl]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_ConcreteTargetShapeSigning ====
section

set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable def normalizedTargetMixedMoment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) : ENNReal :=
  normalizedTargetCacheProduct key.parameter cache (tweakableHashInput key.parameter .message payload) target groups *
    normalizedTargetLogProduct key cache log payload target required
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def targetShapeMoments (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) : TargetShapeVector :=
  fun groups remaining =>
    (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
      (tweakableHashInput key.parameter .message payload) target group) *
        normalizedTargetLogProduct key cache log payload target remaining
theorem targetShapeMoments_eq_indexed (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeMoments key cache log payload target groups remaining =
      normalizedTargetMixedMoment key cache log payload target (targetGroupAt groups) remaining := by
  simp only [targetShapeMoments, normalizedTargetMixedMoment, normalizedTargetCacheProduct, prod_targetGroupAt]
theorem targetShapeMoments_cacheLower_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetCacheLower (targetShapeMoments key cache log payload target) groups remaining =
      (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
        ∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed,
          normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload)
            target (targetGroupAt groups slot)) * normalizedTargetLogProduct key cache log payload target remaining := by
  rw [sum_targetGroupAt_removed_products, Finset.sum_mul]
  rfl
theorem targetShapeMoments_reuse_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetReuseStep (targetShapeMoments key cache log payload target) groups remaining =
      (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
        (tweakableHashInput key.parameter .message payload) target group) *
          ∑ selected ∈ remaining.powerset.erase ∅,
            normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
              normalizedTargetLogProduct key cache log payload target (remaining \ selected) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro selected hselected
  have hnot := hvalid.new_group (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2)
  simp only [targetShapeMoments, Finset.prod_insert hnot]
  ring
theorem targetShapeMoments_cross_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
      ∑ trees ∈ remaining.powerset,
        (∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed,
          normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload)
            target (targetGroupAt groups slot)) * normalizedTargetLogProduct key cache log payload target (remaining \ trees)) =
      targetCacheLower (targetShapeMoments key cache log payload target) groups remaining +
        targetCacheLower (targetTreeLower (targetShapeMoments key cache log payload target)) groups remaining := by
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_targetGroupAt_removed_products, Finset.sum_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset remaining)]
  simp only [Finset.sdiff_empty, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rfl
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetShapeCardinality ====
section

namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
theorem sum_proper_subsets_card {α : Type} [DecidableEq α] (s : Finset α) (f : Nat → ENNReal) :
    (∑ kept ∈ s.powerset.erase s, f kept.card) = ∑ degree ∈ Finset.range s.card, (s.card.choose degree : ENNReal) * f degree := by
  have hindicator : (∑ kept ∈ s.powerset.erase s, f kept.card) =
      ∑ kept ∈ s.powerset, if kept.card = s.card then 0 else f kept.card := by
    rw [← Finset.filter_ne', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro kept hkept
    have heq : kept.card = s.card ↔ kept = s := by
      constructor
      · intro hcard
        exact Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hkept) hcard.ge
      · rintro rfl; rfl
    by_cases h : kept = s <;> simp only [heq, h, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]
  rw [hindicator, Finset.sum_powerset_apply_card (fun degree => if degree = s.card then 0 else f degree), Finset.sum_range_succ]
  simp only [if_true, smul_zero, add_zero, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro degree hdegree
  rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hdegree))]
abbrev TargetIndexVector := Nat → Nat → ENNReal
def liftTargetIndexVector (moments : TargetIndexVector) : TargetShapeVector := fun groups remaining => moments groups.card remaining.card
noncomputable def targetIndexCacheLower (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  ∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) * moments lower degree
noncomputable def targetIndexTreeLower (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  ∑ lower ∈ Finset.range degree, (degree.choose lower : ENNReal) * moments power lower
noncomputable def targetIndexReuseStep (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  targetIndexTreeLower moments (power + 1) degree
theorem targetCacheLower_lift (moments : TargetIndexVector) :
    targetCacheLower (liftTargetIndexVector moments) = liftTargetIndexVector (targetIndexCacheLower moments) := by
  funext groups remaining
  exact sum_proper_subsets_card groups (fun power => moments power remaining.card)
theorem targetTreeLower_lift (moments : TargetIndexVector) :
    targetTreeLower (liftTargetIndexVector moments) = liftTargetIndexVector (targetIndexTreeLower moments) := by
  funext groups remaining
  unfold targetTreeLower liftTargetIndexVector targetIndexTreeLower
  rw [sum_nonempty_sdiff_eq_proper remaining (fun kept => moments groups.card kept.card)]
  exact sum_proper_subsets_card remaining (moments groups.card)
theorem targetReuseStep_lift (moments : TargetIndexVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup)
    (hvalid : TargetShapeValid groups remaining) :
    targetReuseStep (liftTargetIndexVector moments) groups remaining = liftTargetIndexVector (targetIndexReuseStep moments) groups remaining := by
  unfold targetReuseStep liftTargetIndexVector
  have hcard (selected : Finset IndexGroup) (hselected : selected ∈ remaining.powerset.erase ∅) : (insert selected groups).card = groups.card + 1 :=
    Finset.card_insert_of_notMem (hvalid.new_group (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
      (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2))
  rw [Finset.sum_congr rfl (fun selected hselected => congrArg (fun power => moments power (remaining \ selected).card) (hcard selected hselected))]
  rw [sum_nonempty_sdiff_eq_proper remaining (fun kept => moments (groups.card + 1) kept.card)]
  exact sum_proper_subsets_card remaining (moments (groups.card + 1))
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_FreshTargetShapeAverage ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def targetIndexMoments (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) : ENNReal :=
  ∑ index : Index, cachedIndexMultiplicity key.parameter cache index ^ power *
    ((signingSlotsAtIndex (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root log) index).card : ENNReal) ^ degree
noncomputable def indexPowerMoments (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (index : Index) : TargetIndexVector := fun power degree =>
  cachedIndexMultiplicity key.parameter cache index ^ power *
    ((signingSlotsAtIndex (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root log) index).card : ENNReal) ^ degree
theorem normalizedCachedTargetSubsetMatch_local (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (index : Index) (group : Finset IndexGroup) :
    LocalTo group (fun leaves => normalizedCachedTargetSubsetMatch parameter cache targetInput (index, leaves) group) := by
  intro first second hagree
  dsimp only
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  congr 1
  funext input source
  split_ifs
  · rfl
  · have h := normalizedSourceSubsetMatch_local index source group first second hagree
    dsimp only at h
    exact h
theorem leafAverage_normalizedCachedTargetSubsetMatch_le (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (index : Index) (group : Finset IndexGroup) (hgroup : group.Nonempty) :
    leafAverage (fun leaves => normalizedCachedTargetSubsetMatch parameter cache targetInput (index, leaves) group) ≤
      cachedIndexMultiplicity parameter cache index := by
  simp only [normalizedCachedTargetSubsetMatch_eq_weight, cachedIndexMultiplicity, cacheMessageWeight]
  rw [leafAverage_tsum_plain]
  apply ENNReal.tsum_le_tsum
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => rw [leafAverage_const]
  | some output =>
      simp only
      by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output)
      · simp only [if_pos hmessage]
        by_cases hsame : input = targetInput
        · simp only [hsame, if_true]
          rw [leafAverage_const]
          exact zero_le
        · simp only [hsame, if_false]
          exact leafAverage_normalizedSourceSubsetMatch_le index _ group hgroup
      · simp only [if_neg hmessage]
        rw [leafAverage_const]
theorem normalizedTargetLogMatch_eq_sum (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (tree : IndexGroup) :
    normalizedTargetLogMatch key cache log payload target tree =
      ∑ slot : Fin log.length, (eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot).elim 0
        (fun source => normalizedSourceSubsetMatch target source {tree}) := by
  unfold normalizedTargetLogMatch targetTreeMatchCount
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  cases hview : eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot with
  | none => simp
  | some source =>
      simp only [Option.elim_some, normalizedSourceSubsetMatch_singleton, sourceTreeMatch, Option.some.injEq,
        exists_eq_left']
      try (split_ifs <;> simp)
theorem normalizedTargetLogMatch_local (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (index : Index) (tree : IndexGroup) :
    LocalTo {tree} (fun leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree) := by
  intro first second hagree
  dsimp only
  simp only [normalizedTargetLogMatch_eq_sum]
  apply Finset.sum_congr rfl
  intro slot _
  cases eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot with
  | none => rfl
  | some source =>
      have h := normalizedSourceSubsetMatch_local index source {tree} first second hagree
      dsimp only at h
      exact h
theorem leafAverage_normalizedTargetLogMatch_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (index : Index) (tree : IndexGroup) :
    leafAverage (fun leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree) ≤
      ((signingSlotsAtIndex (eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log) index).card : ENNReal) := by
  simp only [normalizedTargetLogMatch_eq_sum]
  rw [leafAverage_sum, signingSlotsAtIndex, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro slot _
  cases hview : eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot with
  | none =>
      simp only [Option.elim_none]
      rw [leafAverage_const]
      exact zero_le
  | some source =>
      simp only [Option.elim_some]
      refine (leafAverage_normalizedSourceSubsetMatch_le index source {tree} (Finset.singleton_nonempty tree)).trans ?_
      by_cases hindex : source.1 = index <;> simp [hindex]
theorem targetShapeMoments_shapeLocal (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (index : Index) :
    ShapeLocal (fun leaves => targetShapeMoments key cache log payload (index, leaves)) := by
  intro groups remaining _
  unfold targetShapeMoments normalizedTargetLogProduct
  apply LocalTo.mul
  · have h := LocalTo.prod (L := FtsLeaf) groups id
      (g := fun group leaves => normalizedCachedTargetSubsetMatch key.parameter cache
        (tweakableHashInput key.parameter .message payload) (index, leaves) group)
      (fun group _ => normalizedCachedTargetSubsetMatch_local key.parameter cache _ index group)
    exact h
  · have h := LocalTo.prod (L := FtsLeaf) remaining (fun tree => {tree})
      (g := fun tree leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree)
      (fun tree _ => normalizedTargetLogMatch_local key cache log payload index tree)
    simpa using h
theorem averagedShape_targetShapeMoments_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (index : Index) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeMoments key cache log payload (index, leaves)))
      (liftTargetIndexVector (indexPowerMoments key cache log index)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeMoments normalizedTargetLogProduct liftTargetIndexVector indexPowerMoments
  have hgroupsLocal : LocalTo (groupCoordinates groups) (fun leaves => ∏ group ∈ groups,
      normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) (index, leaves) group) :=
    LocalTo.prod (L := FtsLeaf) groups id
      (fun group _ => normalizedCachedTargetSubsetMatch_local key.parameter cache _ index group)
  have hremainingLocal : LocalTo remaining (fun leaves => ∏ tree ∈ remaining,
      normalizedTargetLogMatch key cache log payload (index, leaves) tree) := by
    have h := LocalTo.prod (L := FtsLeaf) remaining (fun tree => {tree})
      (g := fun tree leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree)
      (fun tree _ => normalizedTargetLogMatch_local key cache log payload index tree)
    simpa using h
  have hdisjoint : Disjoint (groupCoordinates groups) remaining := by
    rw [Finset.disjoint_left]
    intro i hi hr
    obtain ⟨group, hgroup, hig⟩ := mem_groupCoordinates.mp hi
    exact Finset.disjoint_left.mp (hvalid.remaining group hgroup) hig hr
  rw [leafAverage_mul_of_disjoint hgroupsLocal hremainingLocal hdisjoint,
    leafAverage_prod_disjoint groups id
      (fun group _ => normalizedCachedTargetSubsetMatch_local key.parameter cache _ index group)
      (fun first hfirst second hsecond hne => hvalid.disjoint first hfirst second hsecond hne),
    leafAverage_prod_disjoint remaining (fun tree => {tree})
      (fun tree _ => normalizedTargetLogMatch_local key cache log payload index tree)
      (fun first _ second _ hne => Finset.disjoint_singleton.mpr hne)]
  rw [← eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log payload hfresh hsigned]
  apply mul_le_mul'
  · exact Finset.prod_le_pow_card _ _ _ (fun group hgroup =>
      leafAverage_normalizedCachedTargetSubsetMatch_le key.parameter cache _ index group (hvalid.nonempty group hgroup))
  · exact Finset.prod_le_pow_card _ _ _ (fun tree _ => leafAverage_normalizedTargetLogMatch_le key cache log payload index tree)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_CacheSize ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
theorem QueryCache.enncard_mono {first second : QueryCache HashSpec}
    (hle : first ≤ second) : QueryCache.enncard first ≤ QueryCache.enncard second := by
  exact ENat.toENNReal_mono (Set.encard_le_encard (QueryCache.toSet_mono hle))
theorem romImpl_uniform_query_enncard_eq
    (input : unifSpec.Domain) (cache : QueryCache HashSpec)
    (result : unifSpec.Range input × QueryCache HashSpec)
    (hmem : result ∈ support ((romImpl (.inl input)).run cache)) :
    QueryCache.enncard result.2 = QueryCache.enncard cache := by
  change result ∈ support ((unifFwdImpl HashSpec input).run cache) at hmem
  have hrun : (unifFwdImpl HashSpec input).run cache =
      (fun sample => (sample, cache)) <$>
        (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec)
        (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) cache)
  rw [hrun, support_map] at hmem
  obtain ⟨sample, _hsample, rfl⟩ := hmem
  rfl
theorem romImpl_hash_query_enncard_le
    (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hmem : result ∈ support ((romImpl (.inr input)).run cache)) :
    QueryCache.enncard result.2 ≤ QueryCache.enncard cache + 1 := by
  change result ∈ support ((randomOracle input).run cache) at hmem
  by_cases hcache : cache input = none
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache,
      support_map] at hmem
    obtain ⟨output, _houtput, rfl⟩ := hmem
    exact QueryCache.enncard_cacheQuery_le cache input output
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcache
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ houtput,
      support_pure, Set.mem_singleton_iff] at hmem
    subst result
    exact le_add_right le_rfl
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Reference_SigningTrace ====
section

namespace SphincsSecurity
open OracleComp OracleSpec
def signingLogFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : QueryLog SigningSpec :=
  match input with
  | .inl _ => []
  | .inr request => [⟨request, output⟩]
def signingLogUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalCache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) : QueryLog SigningSpec :=
  log ++ signingLogFragment input output
noncomputable def unloggedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec) ProbComp) := by
  intro input
  cases input with
  | inl worldInput => exact romImpl worldInput
  | inr request => exact simulateQ romImpl (Concrete.scheme.sign secretKey request)
theorem unloggedMappedAdversaryImpl_cache_le
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hmem : result ∈ support
      ((unloggedMappedAdversaryImpl secretKey input).run initialCache)) :
    initialCache ≤ result.2 := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have hrun :
              (unifFwdImpl HashSpec uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          change result ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
          rw [hrun, support_map] at hmem
          obtain ⟨sample, _, heq⟩ := hmem
          exact le_of_eq (congrArg Prod.snd heq)
      | inr hashInput =>
          change result ∈ support
            ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hmem
          exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache result hmem
  | inr request =>
      change result ∈ support
        ((simulateQ romImpl (Concrete.scheme.sign secretKey request)).run initialCache) at hmem
      exact simulateQ_romImpl_cache_le (Concrete.scheme.sign secretKey request)
        initialCache result hmem
noncomputable def logTracedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × QueryLog SigningSpec) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl secretKey) signingLogUpdate
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimePrehit ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
noncomputable local instance instSampleableTypeRandomness_1 : SampleableType Randomness :=
  Concrete.randomnessSampleableType
def cachedMessageInputSetWhere (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) (P : Concrete.FewTimeView → Prop) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cachedMessageInputSet cache parameter root message |
    Concrete.signAttemptResultOfOutput entry.2 ≠ none
      ∧ P (Concrete.hashOutputFewTimeView entry.2)}
noncomputable def cachedMessageEntryCountWhere (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (P : Concrete.FewTimeView → Prop) : ℝ≥0∞ :=
  (((cachedMessageInputSetWhere cache parameter root message P).encard : ENat) : ℝ≥0∞)
theorem cachedMessageEntryCountWhere_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≤
      QueryCache.enncard cache := by
  have hsubset : cachedMessageInputSetWhere cache parameter root message P ⊆ cache.toSet := by
    intro entry hentry
    exact hentry.1.1
  simpa only [cachedMessageEntryCountWhere, QueryCache.enncard] using
    ENat.toENNReal_mono (Set.encard_le_encard hsubset)
def Concrete.PrehitSelectedView (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : Concrete.FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1 = some (randomness, index, leaves)
      ∧ ∃ output, referenceCache
        (tweakableHashInput secretKey.parameter .message
          (Concrete.messageDigestPayload secretKey.root message randomness)) = some output
        ∧ Concrete.signAttemptResultOfOutput output = some (index, leaves)
        ∧ P (Concrete.hashOutputFewTimeView output)
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.signDigestLoop_initial_cached_result
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (initialCache finalCache : QueryCache HashSpec) (output : HashOutput)
    (hcached : initialCache
      (tweakableHashInput secretKey.parameter .message
        (Concrete.messageDigestPayload secretKey.root message randomness)) = some output)
    (hmem : (some (randomness, index, leaves), finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.signDigestLoop attempts secretKey message)).run initialCache)) :
    Concrete.signAttemptResultOfOutput output = some (index, leaves) := by
  induction attempts generalizing initialCache finalCache with
  | zero =>
      simp [Concrete.signDigestLoop] at hmem
  | succ attempts ih =>
      rw [Concrete.signDigestLoop_run_succ_eq, mem_support_bind_iff] at hmem
      obtain ⟨sampled, _hsampled, hrest⟩ := hmem
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      have hattempt' : (attempt, attemptCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (Concrete.signAttempt secretKey message sampled)).run initialCache) := by
        exact hattempt
      have hle : initialCache ≤ attemptCache :=
        simulateQ_romImpl_cache_le
          (liftM (Concrete.signAttempt secretKey message sampled :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
          initialCache (attempt, attemptCache) (by
            rw [simulateQ_romImpl_liftM]
            exact hattempt)
      cases hattemptResult : attempt with
      | none =>
          have hfuture : (some (randomness, index, leaves), finalCache) ∈ support
              ((simulateQ romImpl
                (Concrete.signDigestLoop attempts secretKey message)).run attemptCache) := by
            simpa only [Concrete.signDigestLoopContinuation, hattemptResult] using hfinish
          exact ih attemptCache finalCache (hle hcached) hfuture
      | some selected =>
          rcases selected with ⟨selectedIndex, selectedLeaves⟩
          have hfinishEq :
              (some (randomness, index, leaves), finalCache) =
                (some (sampled, selectedIndex, selectedLeaves), attemptCache) := by
            simpa only [Concrete.signDigestLoopContinuation, hattemptResult, support_pure,
              Set.mem_singleton_iff] using hfinish
          have htuple : (randomness, index, leaves) =
              (sampled, selectedIndex, selectedLeaves) :=
            Option.some.inj (congrArg Prod.fst hfinishEq)
          have hrandomness : randomness = sampled := congrArg Prod.fst htuple
          have hcached' : attemptCache
              (tweakableHashInput secretKey.parameter .message
                (Concrete.messageDigestPayload secretKey.root message sampled)) = some output :=
            hle (by
              rw [← hrandomness]
              exact hcached)
          have hattemptSelected : (some (selectedIndex, selectedLeaves), attemptCache) ∈ support
              ((simulateQ (randomOracle : QueryImpl HashSpec _)
                (Concrete.signAttempt secretKey message sampled)).run initialCache) := by
            have heq : (attempt, attemptCache) =
                (some (selectedIndex, selectedLeaves), attemptCache) :=
              Prod.ext hattemptResult rfl
            rw [← heq]
            exact hattempt'
          have hselectedResult :=
            (Concrete.signAttempt_result_of_cached secretKey message sampled initialCache
              attemptCache (some (selectedIndex, selectedLeaves)) output hcached'
              hattemptSelected).symm
          exact hselectedResult.trans (congrArg some (congrArg Prod.snd htuple).symm)
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeWeightedOriginRace ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
theorem digestRaceSuccessRate_ne_zero_of_budget_lt
    (budget : Nat) (hbudget : budget < 2 ^ randomnessBits) :
    (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      Concrete.admissibleProbability ≠ 0 := by
  have hfraction : (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, ENNReal.div_lt_iff (by left; positivity) (by left; finiteness), one_mul]
    exact_mod_cast hbudget
  exact mul_ne_zero (ne_of_gt (tsub_pos_iff_lt.mpr hfraction)) Concrete.admissibleProbability_pos
end SphincsSecurity
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
namespace Concrete
noncomputable def digestReuseWeight (q : Nat) : ℝ≥0∞ :=
  ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ /
    ((1 - ((q + digestAttemptLimit : Nat) : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) *
      Concrete.admissibleProbability)
theorem digestReuseWeight_ne_top (q : Nat) (hq : q ≤ 2 ^ 127) :
    digestReuseWeight q ≠ ∞ := by
  apply ENNReal.div_ne_top (by finiteness)
  apply digestRaceSuccessRate_ne_zero_of_budget_lt
  norm_num [digestAttemptLimit, randomnessBits] at *
  omega
end Concrete
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Base_RomQueryCharge ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
def hashQueryCharge (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (cache : QueryCache HashSpec) : OracleWorld.Domain → ℝ≥0∞ :=
  Sum.elim (fun _ => 0) (charge cache)
noncomputable def expectedQueryCharge {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (computation : OracleComp OracleWorld α) : QueryCache HashSpec → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ => 0)
    (fun query _ next cache =>
      hashQueryCharge charge cache query +
        ∑' result, Pr[= result | (romImpl query).run cache] * next result.1 result.2)
    computation
@[simp] theorem expectedQueryCharge_pure {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (value : α) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (pure value) cache = 0 := rfl
theorem expectedQueryCharge_query_bind {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (query : OracleWorld.Domain)
    (next : OracleWorld.Range query → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (OracleSpec.query query >>= next) cache =
      hashQueryCharge charge cache query +
        ∑' result, Pr[= result | (romImpl query).run cache] *
          expectedQueryCharge charge (next result.1) result.2 := by
  cases query <;> rfl
theorem romImpl_query_mass (query : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (romImpl query).run cache]) = 1 := by
  cases query with
  | inl input =>
      change (∑' result, Pr[= result | ((unifFwdImpl HashSpec) input).run cache]) = 1
      have hrun := unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp _) cache
      simp only [simulateQ_spec_query] at hrun
      rw [hrun]
      simp
  | inr input =>
      change (∑' result, Pr[= result | (randomOracle input).run cache]) = 1
      by_cases hfresh : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh]
        simp [uniformSampleImpl]
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer]
        simp
theorem finite_of_mem_support_romImpl {query : OracleWorld.Domain}
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {result : OracleWorld.Range query × QueryCache HashSpec}
    (hresult : result ∈ support ((romImpl query).run cache)) : Finite result.2 := by
  cases query with
  | inl input =>
      apply Finite.of_enncard_le (q := {input | cache input ≠ none}.ncard)
      rw [romImpl_uniform_query_enncard_eq input cache result hresult,
        hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  | inr input =>
      apply Finite.of_enncard_le (q := {input | cache input ≠ none}.ncard + 1)
      push_cast
      rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
      exact romImpl_hash_query_enncard_le input cache result hresult
theorem expected_potential_simulateQ_le_queryCharge {α : Type}
    (potential : QueryCache HashSpec → ℝ≥0∞)
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (hstep : ∀ (query : OracleWorld.Domain) (cache : QueryCache HashSpec), Finite cache →
      (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) ≤
        potential cache + hashQueryCharge charge cache query)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * potential result.2) ≤
      potential cache + expectedQueryCharge charge computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedQueryCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (potential result.2 + expectedQueryCharge charge (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((romImpl query).run cache)
          · exact mul_le_mul' le_rfl
              (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 := by
          simp_rw [mul_add, ENNReal.tsum_add]
        _ ≤ (potential cache +
              hashQueryCharge charge cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 :=
          add_le_add (hstep query cache hfinite) le_rfl
        _ = _ := by rw [add_assoc]
theorem expectedQueryCharge_mul {α : Type}
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞) (factor : ℝ≥0∞)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun cache input => charge cache input * factor) computation cache =
      expectedQueryCharge charge computation cache * factor := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      simp only [expectedQueryCharge_query_bind, ih]
      simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
      cases query <;> simp only [hashQueryCharge, Sum.elim_inl, Sum.elim_inr] <;> ring
theorem expected_potential_romImpl_le_charge
    (potential : QueryCache HashSpec → ℝ≥0∞)
    (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (hfresh : ∀ cache : QueryCache HashSpec, Finite cache → ∀ input : HashInput,
      cache input = none →
      (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potential (cache.cacheQuery input answer)) ≤ potential cache + charge cache input)
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) ≤
      potential cache + hashQueryCharge charge cache query := by
  cases query with
  | inl input =>
      change (∑' result, Pr[= result | ((unifFwdImpl HashSpec) input).run cache] * potential result.2) ≤
        potential cache + 0
      have hrun := unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp _) cache
      simp only [simulateQ_spec_query] at hrun
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right, add_zero]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr input =>
      change (∑' result, Pr[= result | (randomOracle input).run cache] * potential result.2) ≤
        potential cache + charge cache input
      by_cases huncached : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ huncached,
          tsum_probOutput_map_mul]
        exact hfresh cache hfinite input huncached
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp huncached
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer]
        simp
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_InterleavedCoverStep ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
abbrev CoverLogState := QueryCache HashSpec × QueryLog SigningSpec
theorem logTracedMappedAdversaryImpl_run_map (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState) :
    (logTracedMappedAdversaryImpl key input).run state =
      (fun result => (result.1, (result.2, state.2 ++ signingLogFragment input result.1))) <$>
        (unloggedMappedAdversaryImpl key input).run state.1 := by
  rw [logTracedMappedAdversaryImpl, QueryImpl.extendState_apply]
  simp only [signingLogUpdate, bind_pure_comp]
theorem logTracedMappedAdversaryImpl_cache_le (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) : state.1 ≤ result.2.1 := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, hbase, rfl⟩ := hresult
  exact unloggedMappedAdversaryImpl_cache_le key input state.1 base hbase
theorem logTracedMappedAdversaryImpl_signingDigestsCached (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    SigningDigestsCached key.parameter result.2.1 key.root result.2.2 := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, hbase, rfl⟩ := hresult
  cases input with
  | inl world =>
      simpa only [signingLogFragment, List.append_nil] using hsigned.mono
        (unloggedMappedAdversaryImpl_cache_le key (.inl world) state.1 base hbase)
  | inr message =>
      change base ∈ support ((simulateQ romImpl (sign key message)).run state.1) at hbase
      rw [← simulateQ_signWithView_fst_run, support_map] at hbase
      obtain ⟨viewed, hviewed, rfl⟩ := hbase
      exact SigningDigestsCached.after_signing key message state.1 viewed.2 state.2 hsigned viewed.1.1 viewed.1.2 hviewed
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_ReuseRawEnvelope ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable def observedRawIndexShapeVector (key : SecretKey) (state : CoverLogState) : TargetShapeVector :=
  liftTargetIndexVector (targetIndexMoments key state.1 state.2)
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def reuseRawEnvelope (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (constRate (Fintype.card Index : ENNReal)⁻¹) reuse (constRate cachedIndexRate) queries signatures
    (observedRawIndexShapeVector key state)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetIndexEnvelope ====
section

namespace SphincsSecurity.Concrete
open ENNReal
noncomputable def targetIndexQuery (arrival : ENNReal) (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  moments power degree + arrival * targetIndexCacheLower moments power degree
noncomputable def targetIndexSigning (uniform reuse : ENNReal) (moments : TargetIndexVector) (power degree : Nat) : ENNReal :=
  moments power degree + uniform *
    (targetIndexCacheLower moments power degree + targetIndexTreeLower moments power degree + targetIndexCacheLower (targetIndexTreeLower moments) power degree) +
      reuse * targetIndexReuseStep moments power degree
noncomputable def targetIndexEnvelope (uniform reuse arrival : ENNReal) (queries signings : Nat) (moments : TargetIndexVector) : TargetIndexVector :=
  (targetIndexSigning uniform reuse)^[signings] ((targetIndexQuery arrival)^[queries] moments)
theorem targetShapeQuery_lift (arrival : ENNReal) (moments : TargetIndexVector) :
    targetShapeQuery (constRate arrival) (liftTargetIndexVector moments) = liftTargetIndexVector (targetIndexQuery arrival moments) := by
  funext groups remaining
  simp only [targetShapeQuery_const, targetCacheLower_lift, liftTargetIndexVector, targetIndexQuery]
theorem targetShapeSigning_lift (uniform reuse : ENNReal) (moments : TargetIndexVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetShapeSigning (constRate uniform) reuse (liftTargetIndexVector moments) groups remaining =
      liftTargetIndexVector (targetIndexSigning uniform reuse moments) groups remaining := by
  simp only [targetShapeSigning_const, targetTreeLower_lift, targetCacheLower_lift, targetReuseStep_lift moments groups remaining hvalid,
    liftTargetIndexVector, targetIndexSigning]
theorem targetShapeSigning_congr (uniform : TargetRate) (reuse : ENNReal) {f g : TargetShapeVector}
    (heq : ∀ G R, TargetShapeValid G R → f G R = g G R)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetShapeSigning uniform reuse f groups remaining = targetShapeSigning uniform reuse g groups remaining :=
  le_antisymm (targetShapeSigning_mono uniform reuse (fun G R hv => (heq G R hv).le) groups remaining hvalid)
    (targetShapeSigning_mono uniform reuse (fun G R hv => (heq G R hv).ge) groups remaining hvalid)
theorem targetShapeEnvelope_congr (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signings : Nat) {f g : TargetShapeVector}
    (heq : ∀ G R, TargetShapeValid G R → f G R = g G R)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings f groups remaining =
      targetShapeEnvelope uniform reuse arrival queries signings g groups remaining :=
  le_antisymm (targetShapeEnvelope_mono uniform reuse arrival queries signings (fun G R hv => (heq G R hv).le) groups remaining hvalid)
    (targetShapeEnvelope_mono uniform reuse arrival queries signings (fun G R hv => (heq G R hv).ge) groups remaining hvalid)
theorem targetShapeQuery_iterate_lift (arrival : ENNReal) (queries : Nat) (moments : TargetIndexVector) :
    (targetShapeQuery (constRate arrival))^[queries] (liftTargetIndexVector moments) = liftTargetIndexVector ((targetIndexQuery arrival)^[queries] moments) := by
  induction queries with
  | zero => rfl
  | succ queries ih => simp only [Function.iterate_succ_apply', ih, targetShapeQuery_lift]
theorem targetShapeSigning_iterate_lift (uniform reuse : ENNReal) (signings : Nat) (moments : TargetIndexVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (targetShapeSigning (constRate uniform) reuse)^[signings] (liftTargetIndexVector moments) groups remaining =
      liftTargetIndexVector ((targetIndexSigning uniform reuse)^[signings] moments) groups remaining := by
  induction signings generalizing groups remaining with
  | zero => rfl
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      rw [targetShapeSigning_congr (constRate uniform) reuse ih groups remaining hvalid]
      exact targetShapeSigning_lift uniform reuse _ groups remaining hvalid
theorem targetShapeEnvelope_lift (uniform reuse arrival : ENNReal) (queries signings : Nat) (moments : TargetIndexVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope (constRate uniform) reuse (constRate arrival) queries signings (liftTargetIndexVector moments) groups remaining =
      targetIndexEnvelope uniform reuse arrival queries signings moments groups.card remaining.card := by
  unfold targetShapeEnvelope targetIndexEnvelope
  rw [targetShapeQuery_iterate_lift]
  exact targetShapeSigning_iterate_lift uniform reuse signings _ groups remaining hvalid
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeTargetCompletion ====
section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
def freshSelectedLoopView?
    (referenceCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : Option FewTimeView :=
  match result.1 with
  | none => none
  | some (randomness, index, leaves) =>
      if referenceCache (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none then
        some (selectedFewTimeView index leaves)
      else none
noncomputable def completeFreshSelectedLoopView
    (referenceCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : ProbComp FewTimeView :=
  match freshSelectedLoopView? referenceCache secretKey message result with
  | some view => pure view
  | none => signerViewSample
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_completeFreshSelectedLoopView_le_uniform
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message) :
    Pr[P | (simulateQ romImpl (signDigestLoop attempts secretKey message)).run workingCache >>=
      completeFreshSelectedLoopView referenceCache secretKey message] ≤
      Pr[P | signerViewSample] := by
  classical
  induction attempts generalizing workingCache with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, pure_bind, completeFreshSelectedLoopView,
        freshSelectedLoopView?]
      exact le_rfl
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq]
      rw [bind_assoc]
      refine probEvent_bind_le_of_forall_le fun randomness _hrandomness => ?_
      let input := tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)
      by_cases hreference : referenceCache input = none
      · by_cases hworking : workingCache input = none
        · let continuation := signDigestLoopContinuation attempts secretKey message randomness
          have hcoordinates := evalDist_signAttempt_fresh_bind_coordinates
            secretKey message randomness workingCache (by simpa only [input] using hworking)
            continuation
          change Pr[P |
              ((simulateQ randomOracle
                (signAttempt secretKey message randomness :
                  OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))).run
                workingCache >>= continuation) >>=
                  completeFreshSelectedLoopView referenceCache secretKey message] ≤ _
          have hcoordinates' :
              𝒮[((simulateQ randomOracle
                  (signAttempt secretKey message randomness :
                    OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))).run
                    workingCache >>= continuation) >>=
                    completeFreshSelectedLoopView referenceCache secretKey message] =
                𝒮[(do
                  let coordinates ← $ᵗ HashOutputCoordinates
                  let output := hashOutputCoordinatesEquiv.symm coordinates
                  continuation (signAttemptResultOfOutput output,
                    workingCache.cacheQuery input output)) >>=
                    completeFreshSelectedLoopView referenceCache secretKey message] := by
            rw [evalSPMF_bind, hcoordinates, ← evalSPMF_bind]
          rw [probEvent_congr' (fun _ _ => Iff.rfl) hcoordinates']
          rw [bind_assoc]
          have hreorder := evalDist_uniformHashOutputCoordinates_bind_reordered
            (fun coordinates =>
              let output := hashOutputCoordinatesEquiv.symm coordinates
              continuation (signAttemptResultOfOutput output,
                workingCache.cacheQuery input output) >>=
                  completeFreshSelectedLoopView referenceCache secretKey message)
          rw [probEvent_congr' (fun _ _ => Iff.rfl) hreorder]
          refine probEvent_bind_le_of_forall_le fun rest _hrest => ?_
          apply probEvent_uniformFewTimeView_bind_le _ P P _ le_rfl
          · intro view hadmissible
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hsuccessful : signAttemptResultOfOutput output ≠ none := by
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff]
              exact hadmissible
            obtain ⟨indexLeaves, hindexLeaves⟩ := Option.ne_none_iff_exists'.mp hsuccessful
            rcases indexLeaves with ⟨index, leaves⟩
            have hviewEq : selectedFewTimeView index leaves = view :=
              signAttemptResultOfOutput_coordinates_view coordinates index leaves
                (by simpa only [output] using hindexLeaves)
            dsimp only
            rw [show signAttemptResultOfOutput
                (hashOutputCoordinatesEquiv.symm ((view, rest.1), rest.2)) =
                some (index, leaves) by
              simpa only [coordinates, output] using hindexLeaves]
            simp only [continuation, signDigestLoopContinuation, pure_bind]
            rw [completeFreshSelectedLoopView, freshSelectedLoopView?]
            have hreference' : referenceCache
                (tweakableHashInput secretKey.parameter .message
                  (messageDigestPayload secretKey.root message randomness)) = none := by
              simpa only [input] using hreference
            simp [hreference', hviewEq]
          · intro view hadmissible
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hrejected : signAttemptResultOfOutput output = none := by
              apply Option.eq_none_iff_forall_not_mem.mpr
              intro selected hselected
              have hne : signAttemptResultOfOutput output ≠ none := by
                rw [hselected]
                simp
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff] at hne
              exact hadmissible hne
            have hinvariant' := onlyRejectedNewMessageEntries_cacheRejected
              referenceCache workingCache secretKey message randomness output hinvariant
              hrejected
            simpa only [coordinates, output, continuation, hrejected,
              signDigestLoopContinuation] using
              ih (workingCache.cacheQuery input output) hinvariant'
        · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hworking
          have hrejected := hinvariant randomness output
            (by simpa only [input] using hreference) (by simpa only [input] using houtput)
          rw [bind_assoc]
          refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
          have hle : workingCache ≤ attemptResult.2 :=
            simulateQ_romImpl_cache_le
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
                  OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
              workingCache attemptResult (by
                rw [simulateQ_romImpl_liftM]
                exact hattempt)
          have hattemptResult : attemptResult.1 = none :=
            (signAttempt_result_of_cached secretKey message randomness workingCache
              attemptResult.2 attemptResult.1 output
              (hle (by simpa only [input] using houtput)) hattempt).trans hrejected
          have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
            referenceCache workingCache attemptResult.2 secretKey message randomness
            hinvariant (by
              have heq : attemptResult = (none, attemptResult.2) :=
                Prod.ext hattemptResult rfl
              rw [← heq]
              exact hattempt)
          simpa only [hattemptResult, signDigestLoopContinuation] using
            ih attemptResult.2 hinvariant'
      · rw [bind_assoc]
        refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
        cases hattemptResult : attemptResult.1 with
        | none =>
            have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
              referenceCache workingCache attemptResult.2 secretKey message randomness
              hinvariant (by
                have heq : attemptResult = (none, attemptResult.2) :=
                  Prod.ext hattemptResult rfl
                rw [← heq]
                exact hattempt)
            simpa only [hattemptResult, signDigestLoopContinuation] using
              ih attemptResult.2 hinvariant'
        | some selected =>
            rcases selected with ⟨index, leaves⟩
            have hreference' : referenceCache
                (tweakableHashInput secretKey.parameter .message
                  (messageDigestPayload secretKey.root message randomness)) ≠ none := by
              simpa only [input] using hreference
            simp only [signDigestLoopContinuation, hattemptResult, pure_bind, completeFreshSelectedLoopView,
              freshSelectedLoopView?, if_neg hreference']
            exact le_rfl
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeRace ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
noncomputable local instance instSampleableTypeRandomness_2 : SampleableType Randomness :=
  Concrete.randomnessSampleableType
theorem cachedMessageEntryCount_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) :
    cachedMessageEntryCount cache parameter root message ≤ QueryCache.enncard cache := by
  have hsubset : cachedMessageInputSet cache parameter root message ⊆ cache.toSet := by
    intro entry hentry
    exact hentry.1
  simpa only [cachedMessageEntryCount, QueryCache.enncard] using
    ENat.toENNReal_mono (Set.encard_le_encard hsubset)
set_option maxRecDepth 100000 in
theorem Concrete.probEvent_signAttempt_fresh_success_eq
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec)
    (hcache : cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none) :
    Pr[fun result => result.1 ≠ none |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run cache] =
      admissibleProbability := by
  have hcoordinates := evalDist_signAttempt_fresh_bind_coordinates
    secretKey message randomness cache hcache
    (fun result => pure result)
  simp only [bind_pure] at hcoordinates
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hcoordinates]
  change Pr[fun result => result.1 ≠ none |
    ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
      pure ∘ fun coordinates =>
        (signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates),
          cache.cacheQuery
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness))
            (hashOutputCoordinatesEquiv.symm coordinates))] = _
  rw [probEvent_bind_pure_comp]
  calc
    Pr[fun coordinates : HashOutputCoordinates =>
        (signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates),
          cache.cacheQuery
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness))
            (hashOutputCoordinatesEquiv.symm coordinates)).1 ≠ none |
        ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] =
        Pr[fun output : HashOutput => signAttemptResultOfOutput output ≠ none ∧ True |
          hashOutputCoordinatesEquiv.symm <$> ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
      rw [probEvent_map]
      simp only [and_true]
      rfl
    _ = Pr[fun output : HashOutput => signAttemptResultOfOutput output ≠ none ∧ True |
          ($ᵗ HashOutput : ProbComp HashOutput)] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (evalSPMF_map_bijective_uniform_cross (α := HashOutputCoordinates) (β := HashOutput)
          hashOutputCoordinatesEquiv.symm hashOutputCoordinatesEquiv.symm.bijective)
    _ = _ := by
      rw [probEvent_uniformHashOutput_admissible_view (fun _ => True)]
      simp only [probEvent_True_eq_sub, probFailure_of_liftM_PMF, tsub_zero]
      rw [mul_one]
noncomputable def Concrete.signDigestAttemptPrefix
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    ProbComp (Randomness ×
      (Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)) :=
  ($ᵗ Randomness) >>= fun randomness =>
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt secretKey message randomness)).run cache >>= fun result =>
        pure (randomness, result)
theorem Concrete.signDigestLoop_run_succ_eq_attemptPrefix
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (signDigestLoop (attempts + 1) secretKey message)).run cache =
      signDigestAttemptPrefix secretKey message cache >>= fun attempt =>
        signDigestLoopContinuation attempts secretKey message attempt.1 attempt.2 := by
  rw [signDigestLoop_run_succ_eq, signDigestAttemptPrefix]
  simp only [bind_assoc, pure_bind]
def Concrete.FavorablePrehitAttempt (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (attempt : Randomness ×
      (Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)) : Prop :=
  ∃ output, referenceCache
    (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message attempt.1)) = some output
    ∧ signAttemptResultOfOutput output ≠ none
    ∧ P (hashOutputFewTimeView output)
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_DigestAttemptExpectation ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_2 : SampleableType Randomness := Concrete.randomnessSampleableType
attribute [local irreducible] signAttempt signDigestAttemptPrefix
abbrev DigestAttemptResult := Randomness × (Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)
noncomputable def cachedDigestAttemptRate (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) : ENNReal :=
  Pr[fun randomness : Randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) | ($ᵗ Randomness : ProbComp Randomness)]
noncomputable def digestAttemptExpectation : Nat → SecretKey → Message → QueryCache HashSpec → ENNReal
  | 0, _, _, _ => 0
  | attempts + 1, key, message, cache => 1 +
      ∑' result, Pr[= result | signDigestAttemptPrefix key message cache] *
        if result.2.1 = none then digestAttemptExpectation attempts key message result.2.2 else 0
theorem signDigestAttemptPrefix_support_attempt (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result : DigestAttemptResult)
    (hr : result ∈ support (signDigestAttemptPrefix key message cache)) :
    result.2 ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt key message result.1)).run cache) := by
  rw [signDigestAttemptPrefix, mem_support_bind_iff] at hr
  obtain ⟨randomness, _, hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨attempt, ha, hr⟩ := hr
  simp only [mem_support_pure_iff] at hr
  have hfirst := congrArg Prod.fst hr
  have hsecond := congrArg Prod.snd hr
  rw [hfirst, hsecond]
  exact ha
theorem signDigestAttemptPrefix_cache_le (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result : DigestAttemptResult)
    (hr : result ∈ support (signDigestAttemptPrefix key message cache)) : cache ≤ result.2.2 := by
  apply simulateQ_romImpl_cache_le (liftM (signAttempt key message result.1 :
    OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) cache result.2
  rw [simulateQ_romImpl_liftM]
  exact signDigestAttemptPrefix_support_attempt key message cache result hr
theorem signDigestAttemptPrefix_cached_result (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result : DigestAttemptResult) (output : HashOutput)
    (hr : result ∈ support (signDigestAttemptPrefix key message cache))
    (hc : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message result.1)) = some output) :
    result.2.1 = signAttemptResultOfOutput output :=
  signAttempt_result_of_cached key message result.1 cache result.2.2 result.2.1 output
    ((signDigestAttemptPrefix_cache_le key message cache result hr) hc)
    (signDigestAttemptPrefix_support_attempt key message cache result hr)
theorem probEvent_signDigestAttemptPrefix_favorablePrehit_eq
    (referenceCache workingCache : QueryCache HashSpec) (key : SecretKey) (message : Message) (P : FewTimeView → Prop) :
    Pr[FavorablePrehitAttempt referenceCache key message P | signDigestAttemptPrefix key message workingCache] =
      cachedDigestAttemptRate key message referenceCache P := by
  rw [signDigestAttemptPrefix, probEvent_bind_eq_tsum, cachedDigestAttemptRate, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro randomness
  rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
    probEvent_bind_pure_comp]
  change Pr[= randomness | ($ᵗ Randomness : ProbComp Randomness)] *
    Pr[fun _ => ∃ output, referenceCache (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = some output ∧ signAttemptResultOfOutput output ≠ none ∧
        P (hashOutputFewTimeView output) |
      (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run workingCache] = _
  rw [probEvent_const]
  rw [probFailure_of_liftM_PMF, tsub_zero]
  split_ifs <;> simp only [mul_one, mul_zero]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_CachedDigestRate ====
section

section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem probEvent_completeOption_eq {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop) :
    Pr[P | comp >>= fun result => (selected result).elim fallback pure] =
      Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] +
        Pr[fun result => selected result = none | comp] * Pr[P | fallback] := by
  rw [probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite comp (fun result => ∃ value, selected result = some value ∧ P value),
    probEvent_eq_tsum_ite comp (fun result => selected result = none),
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  cases selected result with
  | none => simp [Option.elim]
  | some value => simp [Option.elim, probEvent_pure, mul_ite]
theorem probEvent_selectedOption_le_mass_mul {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop)
    (hfail : Pr[⊥ | comp] = 0)
    (hcomplete : Pr[P | comp >>= fun result => (selected result).elim fallback pure] ≤
      Pr[P | fallback]) :
    Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] ≤
      Pr[fun result => selected result ≠ none | comp] * Pr[P | fallback] := by
  have hmass : Pr[fun result => selected result ≠ none | comp] +
      Pr[fun result => selected result = none | comp] = 1 := by
    simpa only [not_not, hfail, tsub_zero] using
      probEvent_compl comp (fun result => selected result ≠ none)
  apply ENNReal.le_of_add_le_add_right (a :=
    Pr[fun result => selected result = none | comp] * Pr[P | fallback])
    (ENNReal.mul_ne_top probEvent_ne_top probEvent_ne_top)
  calc
    _ = Pr[P | comp >>= fun result => (selected result).elim fallback pure] :=
      (probEvent_completeOption_eq comp selected fallback P).symm
    _ ≤ Pr[P | fallback] := hcomplete
    _ = _ := by rw [← add_mul, hmass, one_mul]
theorem probEvent_selectedOption_eq_mass_mul {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop)
    (hfail : Pr[⊥ | comp] = 0) (hfallback : Pr[⊥ | fallback] = 0)
    (hcomplete : ∀ Q : β → Prop,
      Pr[Q | comp >>= fun result => (selected result).elim fallback pure] ≤ Pr[Q | fallback]) :
    Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] =
      Pr[fun result => selected result ≠ none | comp] * Pr[P | fallback] := by
  have hparts :
      Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] +
        Pr[fun result => ∃ value, selected result = some value ∧ ¬ P value | comp] =
      Pr[fun result => selected result ≠ none | comp] := by
    simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    cases selected result with
    | none => simp
    | some value => by_cases hP : P value <;> simp [hP]
  have hfallbackMass : Pr[P | fallback] + Pr[fun value => ¬ P value | fallback] = 1 := by
    simpa only [hfallback, tsub_zero] using probEvent_compl fallback P
  apply le_antisymm (probEvent_selectedOption_le_mass_mul comp selected fallback P hfail (hcomplete P))
  apply ENNReal.le_of_add_le_add_right (a :=
    Pr[fun result => selected result ≠ none | comp] * Pr[fun value => ¬ P value | fallback])
    (ENNReal.mul_ne_top probEvent_ne_top probEvent_ne_top)
  calc
    _ = Pr[fun result => selected result ≠ none | comp] := by
      rw [← mul_add, hfallbackMass, mul_one]
    _ = _ := hparts.symm
    _ ≤ _ := add_le_add le_rfl (probEvent_selectedOption_le_mass_mul comp selected fallback
      (fun value => ¬ P value) hfail (hcomplete _))
theorem freshSelectedLoopView?_satisfies_iff
    (referenceCache : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (P : FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    (∃ view, freshSelectedLoopView? referenceCache key message result = some view ∧ P view) ↔
      FreshSelectedView referenceCache key message P result := by
  cases hresult : result.1 with
  | none => simp [freshSelectedLoopView?, FreshSelectedView, hresult]
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      by_cases hfresh : referenceCache (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message randomness)) = none
      · simp [freshSelectedLoopView?, FreshSelectedView, hresult, hfresh]
      · simp [freshSelectedLoopView?, FreshSelectedView, hresult, hfresh]
theorem completeFreshSelectedLoopView_eq_elim
    (referenceCache : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    completeFreshSelectedLoopView referenceCache key message result =
      (freshSelectedLoopView? referenceCache key message result).elim
        signerViewSample pure := by
  unfold completeFreshSelectedLoopView
  cases freshSelectedLoopView? referenceCache key message result <;> rfl
theorem probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache key message) :
    Pr[FreshSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] =
      Pr[fun result => freshSelectedLoopView? referenceCache key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] *
          Pr[P | signerViewSample] := by
  have h := probEvent_selectedOption_eq_mass_mul
    ((simulateQ romImpl (signDigestLoop attempts key message)).run workingCache)
    (freshSelectedLoopView? referenceCache key message) signerViewSample P
    (by simp) probFailure_signerViewSample (by
      intro Q
      simpa only [funext (completeFreshSelectedLoopView_eq_elim referenceCache key message)] using
        (probEvent_completeFreshSelectedLoopView_le_uniform attempts key message
          referenceCache workingCache Q hinvariant))
  simpa only [freshSelectedLoopView?_satisfies_iff] using h
noncomputable def freshDigestSelectionProbability
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun result => freshSelectedLoopView? cache key message result ≠ none |
    (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache]
theorem freshDigestSelectionProbability_le_one
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache ≤ 1 := probEvent_le_one
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix
private theorem probEvent_digestContinuation_prehit_eq
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) (result : DigestAttemptResult)
    (hr : result ∈ support (signDigestAttemptPrefix key message workingCache)) :
    Pr[PrehitSelectedView referenceCache key message P |
      signDigestLoopContinuation attempts key message result.1 result.2] =
      (if FavorablePrehitAttempt referenceCache key message P result then 1 else 0) +
        (if result.2.1 = none then Pr[PrehitSelectedView referenceCache key message P |
          (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0) := by
  cases hresult : result.2.1 with
  | none =>
      have hnot : ¬ FavorablePrehitAttempt referenceCache key message P result := by
        rintro ⟨output, hc, ha, _⟩
        have heq := signDigestAttemptPrefix_cached_result key message workingCache result output hr (hreference hc)
        exact ha (heq.symm.trans hresult)
      simp only [signDigestLoopContinuation, hresult, if_true, if_neg hnot, zero_add]
  | some selected =>
      obtain ⟨index, leaves⟩ := selected
      have hiff : PrehitSelectedView referenceCache key message P
          (some (result.1, index, leaves), result.2.2) ↔ FavorablePrehitAttempt referenceCache key message P result := by
        constructor
        · rintro ⟨randomness, foundIndex, foundLeaves, hfound, output, hc, ho, hP⟩
          have hfirst := congrArg Prod.fst (Option.some.inj hfound)
          refine ⟨output, ?_, ?_, hP⟩
          · rw [hfirst]
            exact hc
          · rw [ho]
            exact Option.some_ne_none _
        · rintro ⟨output, hc, _, hP⟩
          have heq := signDigestAttemptPrefix_cached_result key message workingCache result output hr (hreference hc)
          exact ⟨result.1, index, leaves, rfl, output, hc, heq.symm.trans hresult, hP⟩
      simp only [signDigestLoopContinuation, hresult, probEvent_pure, Option.some_ne_none, if_false, add_zero, hiff]
theorem probEvent_signDigestLoop_prehit_recurrence
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop (attempts + 1) key message)).run workingCache] =
      cachedDigestAttemptRate key message referenceCache P +
        ∑' result, Pr[= result | signDigestAttemptPrefix key message workingCache] *
          if result.2.1 = none then Pr[PrehitSelectedView referenceCache key message P |
            (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  rw [signDigestLoop_run_succ_eq_attemptPrefix, probEvent_bind_eq_tsum,
    ← probEvent_signDigestAttemptPrefix_favorablePrehit_eq referenceCache workingCache key message P,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ support (signDigestAttemptPrefix key message workingCache)
  · rw [probEvent_digestContinuation_prehit_eq attempts key message referenceCache workingCache hreference P result hr]
    split_ifs <;> ring
  · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, ite_self, zero_add]
theorem probEvent_signDigestLoop_prehit_eq_rate_mul_attempts
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] =
      cachedDigestAttemptRate key message referenceCache P * digestAttemptExpectation attempts key message workingCache := by
  induction attempts generalizing workingCache with
  | zero =>
      simp [signDigestLoop, PrehitSelectedView, digestAttemptExpectation]
  | succ attempts ih =>
      rw [probEvent_signDigestLoop_prehit_recurrence attempts key message referenceCache workingCache hreference P,
        digestAttemptExpectation, mul_add, mul_one, ← ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support (signDigestAttemptPrefix key message workingCache)
      · by_cases hnone : result.2.1 = none
        · rw [if_pos hnone, if_pos hnone, ih result.2.2
            (hreference.trans (signDigestAttemptPrefix_cache_le key message workingCache result hr))]
          ring
        · simp only [if_neg hnone, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, mul_zero]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
private theorem digestSelection_partition (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result)
    (hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)) :
    (if freshSelectedLoopView? cache key message result ≠ none then (1 : ENNReal) else 0) +
      (if PrehitSelectedView cache key message (fun _ => True) result then 1 else 0) +
      (if result.1 = none then 1 else 0) = 1 := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp [freshSelectedLoopView?, PrehitSelectedView]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      cases hc : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => simp [freshSelectedLoopView?, PrehitSelectedView, hc]
      | some output =>
          have hp : PrehitSelectedView cache key message (fun _ => True) (some (randomness, index, leaves), after) :=
            ⟨randomness, index, leaves, rfl, output, hc,
              signDigestLoop_initial_cached_result attempts key message randomness index leaves cache after output hc hr, trivial⟩
          simp only [freshSelectedLoopView?, hc, Option.some_ne_none, if_false, ne_eq, not_true_eq_false, hp,
            if_true, zero_add, add_zero]
theorem probEvent_signDigestLoop_selection_mass (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun result => freshSelectedLoopView? cache key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] +
      Pr[PrehitSelectedView cache key message (fun _ => True) |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] +
      Pr[fun result => result.1 = none | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] = 1 := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ = ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] := by
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)
      · have h := congrArg (fun value => Pr[= result | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] * value)
          (digestSelection_partition attempts key message cache result hr)
        simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
      · simp only [probOutput_eq_zero_of_not_mem_support hr, ite_self, zero_add]
    _ = 1 := tsum_probOutput_of_liftM_PMF _
noncomputable def digestExhaustionProbability (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun result => result.1 = none | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache]
theorem freshSelection_add_cachedAttempts_add_exhaustion (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache +
      cachedDigestAttemptRate key message cache (fun _ => True) * digestAttemptExpectation digestAttemptLimit key message cache +
      digestExhaustionProbability key message cache = 1 := by
  have h := probEvent_signDigestLoop_selection_mass digestAttemptLimit key message cache
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message cache cache le_rfl] at h
  exact h
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_3 : SampleableType Randomness := Concrete.randomnessSampleableType
attribute [local irreducible] signAttempt signDigestAttemptPrefix
theorem cachedDigestAttemptRate_eq_count (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    cachedDigestAttemptRate key message cache P =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output)
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSetWhere cache key.parameter key.root message P
  let embedding : (targets : Set Randomness) ↪ fiber :=
    ⟨fun randomness =>
      ⟨⟨tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness.1),
          Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
        ⟨⟨(Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).1, ⟨randomness.1, rfl⟩⟩,
          (Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).2⟩⟩,
      fun left right heq => Subtype.ext <|
        (messageDigestPayload_injective key.root <|
          (tweakableHashInput_injective key.parameter (by trivial) (by trivial) <|
            congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
  have hsurjective : Function.Surjective embedding := by
    rintro ⟨⟨input, output⟩, ⟨hcached, randomness, hinput⟩, hadmissible, hP⟩
    change input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) at hinput
    subst input
    have hh : hit randomness := ⟨output, hcached, hadmissible, hP⟩
    let target : (targets : Set Randomness) := ⟨randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    refine ⟨target, Subtype.ext ?_⟩
    have hout := Option.some.inj ((Classical.choose_spec (Finset.mem_filter.mp target.2).2).1.symm.trans hcached)
    exact Sigma.ext (by rfl) (heq_of_eq hout)
  have hcard : (targets.card : ENNReal) = cachedMessageEntryCountWhere cache key.parameter key.root message P := by
    have h := Set.encard_congr (Equiv.ofBijective embedding ⟨embedding.injective, hsurjective⟩)
    simpa only [cachedMessageEntryCountWhere, fiber, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      congrArg ENat.toENNReal h
  rw [cachedDigestAttemptRate, probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ = _
  rw [hcard]
noncomputable def exactDigestReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  digestAttemptExpectation digestAttemptLimit key message cache * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹
theorem probEvent_signDigestLoop_prehit_eq_count_mul_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView cache key message P |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * exactDigestReuseWeight key message cache := by
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message cache cache le_rfl,
    cachedDigestAttemptRate_eq_count, exactDigestReuseWeight]
  ring
theorem freshSelection_add_count_exactWeight_add_exhaustion (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache +
      digestExhaustionProbability key message cache = 1 := by
  have h := freshSelection_add_cachedAttempts_add_exhaustion key message cache
  rw [cachedDigestAttemptRate_eq_count] at h
  unfold exactDigestReuseWeight
  convert h using 1; ring
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_FreshDigestHazard ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop
def FreshDigestAttempt (reference : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (result : DigestAttemptResult) : Prop :=
  reference (tweakableHashInput key.parameter .message (messageDigestPayload key.root message result.1)) = none ∧
    result.2.1 ≠ none
private theorem probEvent_digestContinuation_fresh_eq
    (attempts : Nat) (key : SecretKey) (message : Message)
    (reference : QueryCache HashSpec) (result : DigestAttemptResult) :
    Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
      signDigestLoopContinuation attempts key message result.1 result.2] =
      (if FreshDigestAttempt reference key message result then 1 else 0) +
        if result.2.1 = none then
          Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
            (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  cases hr : result.2.1 with
  | none => simp only [signDigestLoopContinuation, FreshDigestAttempt, hr, ne_eq, not_true_eq_false,
      and_false, if_false, if_true, zero_add]
  | some selected =>
      obtain ⟨index, leaves⟩ := selected
      by_cases hc : reference (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message result.1)) = none
      · simp [signDigestLoopContinuation, FreshDigestAttempt, freshSelectedLoopView?, hr, hc]
      · simp [signDigestLoopContinuation, FreshDigestAttempt, freshSelectedLoopView?, hr, hc]
theorem probEvent_signDigestLoop_fresh_recurrence
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec) :
    Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
      (simulateQ romImpl (signDigestLoop (attempts + 1) key message)).run cache] =
      Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] +
        ∑' result, Pr[= result | signDigestAttemptPrefix key message cache] *
          if result.2.1 = none then
            Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
              (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  rw [signDigestLoop_run_succ_eq_attemptPrefix, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  rw [probEvent_digestContinuation_fresh_eq]
  split_ifs <;> ring
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_RawProposalMomentBound ====
section

section





section
namespace SphincsSecurity.Concrete
open ENNReal
noncomputable def indexPowerVector (cache signings : ENNReal) : TargetIndexVector :=
  fun power degree => cache ^ power * signings ^ degree
def TargetIndexDegreeLE (bound : Nat) (first second : TargetIndexVector) : Prop :=
  ∀ power degree, power + degree ≤ bound → first power degree ≤ second power degree
theorem targetIndexCacheLower_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexCacheLower first) (targetIndexCacheLower second) := by
  intro power degree hdegree
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h lower degree (by have := Finset.mem_range.mp hlower; omega)
theorem targetIndexTreeLower_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexTreeLower first) (targetIndexTreeLower second) := by
  intro power degree hdegree
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h power lower (by have := Finset.mem_range.mp hlower; omega)
theorem targetIndexReuseStep_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexReuseStep first) (targetIndexReuseStep second) := by
  intro power degree hdegree
  unfold targetIndexReuseStep targetIndexTreeLower
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h (power + 1) lower (by have := Finset.mem_range.mp hlower; omega)
theorem targetIndexSigning_degree_mono (uniform reuse : ENNReal)
    {bound : Nat} {first second : TargetIndexVector} (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexSigning uniform reuse first) (targetIndexSigning uniform reuse second) := by
  intro power degree hdegree
  exact add_le_add
    (add_le_add (h power degree hdegree) (mul_le_mul' le_rfl
      (add_le_add (add_le_add (targetIndexCacheLower_degree_mono h power degree hdegree)
        (targetIndexTreeLower_degree_mono h power degree hdegree))
        (targetIndexCacheLower_degree_mono (targetIndexTreeLower_degree_mono h) power degree hdegree))))
    (mul_le_mul' le_rfl (targetIndexReuseStep_degree_mono h power degree hdegree))
theorem targetIndexSigning_iterate_degree_mono (uniform reuse : ENNReal) (signings : Nat)
    {bound : Nat} {first second : TargetIndexVector} (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound ((targetIndexSigning uniform reuse)^[signings] first)
      ((targetIndexSigning uniform reuse)^[signings] second) := by
  induction signings with
  | zero => exact h
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact targetIndexSigning_degree_mono uniform reuse ih
theorem ennreal_add_one_pow (value : ENNReal) (degree : Nat) :
    (value + 1) ^ degree = value ^ degree +
      ∑ lower ∈ Finset.range degree, (degree.choose lower : ENNReal) * value ^ lower := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
  rw [add_comm]
  apply congrArg (value ^ degree + ·)
  apply Finset.sum_congr rfl
  intro lower _
  exact mul_comm _ _
theorem indexPowerVector_cache_succ (cache signings : ENNReal) (power degree : Nat) :
    indexPowerVector (cache + 1) signings power degree =
      indexPowerVector cache signings power degree + targetIndexCacheLower (indexPowerVector cache signings) power degree := by
  simp only [indexPowerVector, ennreal_add_one_pow, add_mul, Finset.sum_mul, targetIndexCacheLower]
  congr 1
  apply Finset.sum_congr rfl
  intro lower _
  ring
theorem targetIndexQuery_power {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (power degree : Nat) :
    targetIndexQuery rate (indexPowerVector cache signings) power degree =
      (1 - rate) * indexPowerVector cache signings power degree +
        rate * indexPowerVector (cache + 1) signings power degree := by
  rw [indexPowerVector_cache_succ, bernoulli_mix_increment hrate]
  rfl
theorem targetIndexQuery_binomialAverage (arrival rate : ENNReal) (steps : Nat)
    (moments : Nat → TargetIndexVector) (power degree : Nat) :
    targetIndexQuery arrival (fun p d => binomialAverage rate steps (fun count => moments count p d)) power degree =
      binomialAverage rate steps (fun count => targetIndexQuery arrival (moments count) power degree) := by
  simp only [targetIndexQuery, targetIndexCacheLower, binomialAverage_add,
    binomialAverage_mul_left, binomialAverage_sum]
theorem targetIndexQuery_iterate_power {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (queries power degree : Nat) :
    (targetIndexQuery rate)^[queries] (indexPowerVector cache signings) power degree =
      binomialAverage rate queries (fun count => indexPowerVector (cache + count) signings power degree) := by
  induction queries generalizing power degree with
  | zero => simp [binomialAverage_zero]
  | succ queries ih =>
      have hfun : (targetIndexQuery rate)^[queries] (indexPowerVector cache signings) =
          fun p d => binomialAverage rate queries (fun count => indexPowerVector (cache + count) signings p d) := by
        funext p d
        exact ih p d
      rw [Function.iterate_succ_apply', hfun, targetIndexQuery_binomialAverage]
      simp_rw [targetIndexQuery_power hrate]
      rw [binomialAverage_add, binomialAverage_mul_left, binomialAverage_mul_left, binomialAverage_succ]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
theorem targetIndexQuery_iterate_power_le {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (queries bound : Nat) :
    TargetIndexDegreeLE bound ((targetIndexQuery rate)^[queries] (indexPowerVector cache signings))
      (indexPowerVector (cache + queries * rate + bound) signings) := by
  intro power degree hdegree
  rw [targetIndexQuery_iterate_power hrate]
  simp only [indexPowerVector, binomialAverage_mul_right]
  apply mul_le_mul' _ le_rfl
  exact (binomialAverage_shifted_power_le hrate cache queries power).trans
    (pow_le_pow_left' (add_le_add le_rfl (Nat.cast_le.mpr (by omega : power ≤ bound))) power)
theorem targetIndexEnvelope_power_query_shift_le {rate : ENNReal} (hrate : rate ≤ 1)
    (uniform reuse cache signings : ENNReal) (queries signatures bound power degree : Nat)
    (hdegree : power + degree ≤ bound) :
    targetIndexEnvelope uniform reuse rate queries signatures (indexPowerVector cache signings) power degree ≤
      (targetIndexSigning uniform reuse)^[signatures]
        (indexPowerVector (cache + queries * rate + bound) signings) power degree :=
  targetIndexSigning_iterate_degree_mono uniform reuse signatures
    (targetIndexQuery_iterate_power_le hrate cache signings queries bound) power degree hdegree
theorem targetShapeEnvelope_sum_indexPower {α : Type} [Fintype α]
    (uniform reuse arrival : ENNReal) (queries signatures : Nat) (cache signings : α → ENNReal)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope (constRate uniform) reuse (constRate arrival) queries signatures
      (fun G R => ∑ i, indexPowerVector (cache i) (signings i) G.card R.card) groups remaining =
      ∑ i, targetIndexEnvelope uniform reuse arrival queries signatures
        (indexPowerVector (cache i) (signings i)) groups.card remaining.card := by
  have hsum : (fun G R => ∑ i, indexPowerVector (cache i) (signings i) G.card R.card) =
      fun G R => ∑' i, liftTargetIndexVector (indexPowerVector (cache i) (signings i)) G R := by
    funext G R
    rw [tsum_fintype]
    rfl
  rw [hsum, targetShapeEnvelope_tsum, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact targetShapeEnvelope_lift uniform reuse arrival queries signatures _ groups remaining hvalid
theorem reuseRawEnvelope_query_shift_le (key : SecretKey) (reuse : ENNReal)
    (queries signatures bound : Nat) (state : CoverLogState)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup)
    (hvalid : TargetShapeValid groups remaining) (hdegree : groups.card + remaining.card ≤ bound) :
    reuseRawEnvelope key reuse queries signatures state groups remaining ≤
      ∑ index : Index, (targetIndexSigning (Fintype.card Index : ENNReal)⁻¹ reuse)^[signatures]
        (indexPowerVector
          (cachedIndexMultiplicity key.parameter state.1 index +
            (queries : ENNReal) * cachedIndexRate + bound)
          ((signingSlotsAtIndex (observedOptionalSigningViews
            (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal))
        groups.card remaining.card := by
  have hrate : cachedIndexRate ≤ 1 := cachedIndexRate_le_one
  unfold reuseRawEnvelope observedRawIndexShapeVector liftTargetIndexVector targetIndexMoments
  change targetShapeEnvelope _ _ _ queries signatures
    (fun G R => ∑ index : Index, indexPowerVector _ _ G.card R.card) groups remaining ≤ _
  rw [targetShapeEnvelope_sum_indexPower _ _ _ _ _ _ _ groups remaining hvalid]
  apply Finset.sum_le_sum
  intro index _
  exact targetIndexEnvelope_power_query_shift_le hrate _ _ _ _ queries signatures bound _ _ hdegree
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open ENNReal
theorem targetIndexSigning_add (uniform reuse : ENNReal) (first second : TargetIndexVector) :
    targetIndexSigning uniform reuse (fun p d => first p d + second p d) =
      fun p d => targetIndexSigning uniform reuse first p d + targetIndexSigning uniform reuse second p d := by
  funext power degree
  simp only [targetIndexSigning, targetIndexCacheLower, targetIndexTreeLower, targetIndexReuseStep,
    mul_add, Finset.sum_add_distrib]
  ring
theorem targetIndexSigning_mul (uniform reuse scalar : ENNReal) (moments : TargetIndexVector) :
    targetIndexSigning uniform reuse (fun p d => scalar * moments p d) =
      fun p d => scalar * targetIndexSigning uniform reuse moments p d := by
  have hcache (values : TargetIndexVector) (p d : Nat) :
      targetIndexCacheLower (fun p d => scalar * values p d) p d =
        scalar * targetIndexCacheLower values p d := by
    simp only [targetIndexCacheLower, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  have htree (values : TargetIndexVector) : targetIndexTreeLower (fun p d => scalar * values p d) =
      fun p d => scalar * targetIndexTreeLower values p d := by
    funext p d
    simp only [targetIndexTreeLower, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  funext power degree
  simp only [targetIndexSigning, hcache, htree, targetIndexReuseStep]
  ring
theorem targetIndexSigning_iterate_add (uniform reuse : ENNReal) (steps : Nat) (first second : TargetIndexVector) :
    (targetIndexSigning uniform reuse)^[steps] (fun p d => first p d + second p d) =
      fun p d => (targetIndexSigning uniform reuse)^[steps] first p d +
        (targetIndexSigning uniform reuse)^[steps] second p d := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [Function.iterate_succ_apply', ih, targetIndexSigning_add]
theorem targetIndexSigning_iterate_mul (uniform reuse scalar : ENNReal) (steps : Nat) (moments : TargetIndexVector) :
    (targetIndexSigning uniform reuse)^[steps] (fun p d => scalar * moments p d) =
      fun p d => scalar * (targetIndexSigning uniform reuse)^[steps] moments p d := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [Function.iterate_succ_apply', ih, targetIndexSigning_mul]
theorem indexPowerVector_signing_succ (cache signings : ENNReal) :
    indexPowerVector cache (signings + 1) =
      fun p d => indexPowerVector cache signings p d + targetIndexTreeLower (indexPowerVector cache signings) p d := by
  funext power degree
  simp only [indexPowerVector, ennreal_add_one_pow, mul_add, Finset.mul_sum, targetIndexTreeLower]
  congr 1
  apply Finset.sum_congr rfl
  intro lower _
  ring
theorem indexPowerVector_diagonal_succ (cache signings : ENNReal) (power degree : Nat) :
    indexPowerVector (cache + 1) (signings + 1) power degree =
      indexPowerVector cache signings power degree + targetIndexCacheLower (indexPowerVector cache signings) power degree +
        targetIndexTreeLower (indexPowerVector cache signings) power degree +
        targetIndexCacheLower (targetIndexTreeLower (indexPowerVector cache signings)) power degree := by
  rw [indexPowerVector_cache_succ, indexPowerVector_signing_succ]
  simp only [targetIndexCacheLower, mul_add, Finset.sum_add_distrib]
  ring
theorem targetIndexReuseStep_power (cache signings : ENNReal) (power degree : Nat) :
    targetIndexReuseStep (indexPowerVector cache signings) power degree =
      cache * targetIndexTreeLower (indexPowerVector cache signings) power degree := by
  simp only [targetIndexReuseStep, targetIndexTreeLower, indexPowerVector, pow_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  ring
theorem targetIndexSigning_power {uniform reuse cache : ENNReal}
    (hprob : uniform + reuse * cache ≤ 1) (signings : ENNReal) (power degree : Nat) :
    targetIndexSigning uniform reuse (indexPowerVector cache signings) power degree =
      (1 - (uniform + reuse * cache)) * indexPowerVector cache signings power degree +
        uniform * indexPowerVector (cache + 1) (signings + 1) power degree +
        reuse * cache * indexPowerVector cache (signings + 1) power degree := by
  rw [indexPowerVector_diagonal_succ, indexPowerVector_signing_succ]
  simp only [targetIndexSigning, targetIndexReuseStep_power]
  have hsum : 1 - (uniform + reuse * cache) + (uniform + reuse * cache) = 1 :=
    tsub_add_cancel_of_le hprob
  calc
    _ = (1 - (uniform + reuse * cache) + (uniform + reuse * cache)) *
        indexPowerVector cache signings power degree + uniform *
          (targetIndexCacheLower (indexPowerVector cache signings) power degree +
            targetIndexTreeLower (indexPowerVector cache signings) power degree +
            targetIndexCacheLower (targetIndexTreeLower (indexPowerVector cache signings)) power degree) +
          reuse * cache * targetIndexTreeLower (indexPowerVector cache signings) power degree := by
      rw [hsum]
      ring
    _ = _ := by ring
noncomputable def indexSigningAverage (uniform reuse : ENNReal) :
    Nat → (ENNReal → ENNReal → ENNReal) → ENNReal → ENNReal → ENNReal
  | 0, f, cache, signings => f cache signings
  | steps + 1, f, cache, signings =>
      (1 - (uniform + reuse * cache)) * indexSigningAverage uniform reuse steps f cache signings +
        uniform * indexSigningAverage uniform reuse steps f (cache + 1) (signings + 1) +
        reuse * cache * indexSigningAverage uniform reuse steps f cache (signings + 1)
theorem targetIndexSigning_iterate_power {uniform reuse cache : ENNReal}
    (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ 1)
    (signings : ENNReal) (power degree : Nat) :
    (targetIndexSigning uniform reuse)^[steps] (indexPowerVector cache signings) power degree =
      indexSigningAverage uniform reuse steps (fun c s => indexPowerVector c s power degree) cache signings := by
  induction steps generalizing cache signings power degree with
  | zero => rfl
  | succ steps ih =>
      have hbase : uniform + reuse * cache ≤ 1 :=
        (add_le_add le_rfl (mul_le_mul' le_rfl le_self_add)).trans hprob
      have hstay : uniform + reuse * (cache + steps) ≤ 1 := by
        apply le_trans _ hprob
        gcongr
        exact Nat.le_succ steps
      have hnext : uniform + reuse * (cache + 1 + steps) ≤ 1 := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hprob
      have hfun : targetIndexSigning uniform reuse (indexPowerVector cache signings) =
          fun p d => (1 - (uniform + reuse * cache)) * indexPowerVector cache signings p d +
            uniform * indexPowerVector (cache + 1) (signings + 1) p d +
            reuse * cache * indexPowerVector cache (signings + 1) p d := by
        funext p d
        exact targetIndexSigning_power hbase signings p d
      rw [Function.iterate_succ_apply, hfun]
      simp only [targetIndexSigning_iterate_add, targetIndexSigning_iterate_mul]
      rw [ih hstay, ih hnext, ih hstay]
      rfl
theorem bernoulli_mix_rate_mono {rate nextRate first second : ENNReal}
    (hrate : rate ≤ nextRate) (hnext : nextRate ≤ 1) (hvalue : first ≤ second) :
    (1 - rate) * first + rate * second ≤ (1 - nextRate) * first + nextRate * second := by
  have hsum : first + (second - first) = second := add_tsub_cancel_of_le hvalue
  calc
    _ = first + rate * (second - first) := by
      conv_lhs => rhs; rw [← hsum]
      exact bernoulli_mix_increment (hrate.trans hnext) _ _
    _ ≤ first + nextRate * (second - first) := add_le_add le_rfl (mul_le_mul' hrate le_rfl)
    _ = _ := by
      rw [← bernoulli_mix_increment hnext, hsum]
theorem indexSigningAverage_le_binomialAverage {uniform reuse rate cache : ENNReal}
    (hrate : rate ≤ 1) (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ rate)
    (f : ENNReal → ENNReal) (hmono : Monotone f) (signings : ENNReal) :
    indexSigningAverage uniform reuse steps (fun _ s => f s) cache signings ≤
      binomialAverage rate steps (fun count => f (signings + count)) := by
  induction steps generalizing cache signings with
  | zero => simp only [indexSigningAverage, binomialAverage_zero, Nat.cast_zero, add_zero, le_refl]
  | succ steps ih =>
      have hbase : uniform + reuse * cache ≤ rate :=
        (add_le_add le_rfl (mul_le_mul' le_rfl le_self_add)).trans hprob
      have hstay : uniform + reuse * (cache + steps) ≤ rate := by
        apply le_trans _ hprob
        gcongr
        exact Nat.le_succ steps
      have hnext : uniform + reuse * (cache + 1 + steps) ≤ rate := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hprob
      have hvalue : binomialAverage rate steps (fun count => f (signings + count)) ≤
          binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
        binomialAverage_mono rate steps (fun _ => hmono (add_le_add le_self_add le_rfl))
      calc
        _ ≤ (1 - (uniform + reuse * cache)) *
              binomialAverage rate steps (fun count => f (signings + count)) +
            uniform * binomialAverage rate steps (fun count => f (signings + 1 + count)) +
            reuse * cache * binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
          add_le_add (add_le_add (mul_le_mul' le_rfl (ih hstay signings))
            (mul_le_mul' le_rfl (ih hnext (signings + 1))))
            (mul_le_mul' le_rfl (ih hstay (signings + 1)))
        _ = (1 - (uniform + reuse * cache)) *
              binomialAverage rate steps (fun count => f (signings + count)) +
            (uniform + reuse * cache) *
              binomialAverage rate steps (fun count => f (signings + 1 + count)) := by ring
        _ ≤ (1 - rate) * binomialAverage rate steps (fun count => f (signings + count)) +
            rate * binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
          bernoulli_mix_rate_mono hbase hrate hvalue
        _ = _ := by
          simp only [binomialAverage_succ, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]
theorem targetIndexSigning_iterate_power_le_binomialAverage {uniform reuse rate cache : ENNReal}
    (hrate : rate ≤ 1) (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ rate)
    (signings : ENNReal) (degree : Nat) :
    (targetIndexSigning uniform reuse)^[steps] (indexPowerVector cache signings) 0 degree ≤
      binomialAverage rate steps (fun count => (signings + count) ^ degree) := by
  rw [targetIndexSigning_iterate_power steps (hprob.trans hrate)]
  simp only [indexPowerVector, pow_zero, one_mul]
  exact indexSigningAverage_le_binomialAverage hrate steps hprob (fun s => s ^ degree)
    (fun _ _ h => pow_le_pow_left' h degree) signings
end SphincsSecurity.Concrete
end
end

section







section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_4 : SampleableType Randomness := Concrete.randomnessSampleableType
theorem uniform_randomness_messageInput_cacheHit_eq_count
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output |
      ($ᵗ Randomness : ProbComp Randomness)] =
      cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSet cache key.parameter key.root message
  let embedding : (targets : Set Randomness) ↪ fiber :=
    ⟨fun randomness =>
      ⟨⟨tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness.1),
          Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
        (Classical.choose_spec (Finset.mem_filter.mp randomness.2).2), ⟨randomness.1, rfl⟩⟩,
      fun left right heq => Subtype.ext <|
        (messageDigestPayload_injective key.root <|
          (tweakableHashInput_injective key.parameter (by trivial) (by trivial) <|
            congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
  have hsurjective : Function.Surjective embedding := by
    rintro ⟨⟨input, output⟩, hcached, randomness, hinput⟩
    change input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) at hinput
    subst input
    have hh : hit randomness := ⟨output, hcached⟩
    let target : (targets : Set Randomness) := ⟨randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    refine ⟨target, Subtype.ext ?_⟩
    have hout := Option.some.inj ((Classical.choose_spec (Finset.mem_filter.mp target.2).2).symm.trans hcached)
    exact Sigma.ext (by rfl) (heq_of_eq hout)
  have hcard : (targets.card : ENNReal) = cachedMessageEntryCount cache key.parameter key.root message := by
    have h := Set.encard_congr (Equiv.ofBijective embedding ⟨embedding.injective, hsurjective⟩)
    simpa only [cachedMessageEntryCount, fiber, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      congrArg ENat.toENNReal h
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ = _
  rw [hcard]
noncomputable def messageInputMissProbability (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun randomness : Randomness => cache (tweakableHashInput key.parameter .message
    (messageDigestPayload key.root message randomness)) = none | ($ᵗ Randomness : ProbComp Randomness)]
theorem messageInputMissProbability_eq_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageInputMissProbability key message cache =
      1 - cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let miss : Randomness → Prop := fun randomness => cache (tweakableHashInput key.parameter .message
    (messageDigestPayload key.root message randomness)) = none
  have hnot : Pr[fun randomness => ¬ miss randomness | ($ᵗ Randomness : ProbComp Randomness)] =
      cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    apply Eq.trans ?_ (uniform_randomness_messageInput_cacheHit_eq_count key message cache)
    apply probEvent_congr'
    · intro randomness _
      exact Option.ne_none_iff_exists'
    · rfl
  have h := probEvent_compl ($ᵗ Randomness : ProbComp Randomness) miss
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  have heq := ENNReal.eq_sub_of_add_eq probEvent_ne_top h
  rw [hnot] at heq
  exact heq
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem cachedMessageEntryCount_cacheQuery_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) :
    cachedMessageEntryCount (cache.cacheQuery input output) parameter root message ≤
      cachedMessageEntryCount cache parameter root message + 1 := by
  have hsubset : cachedMessageInputSet (cache.cacheQuery input output) parameter root message ⊆
      insert ⟨input, output⟩ (cachedMessageInputSet cache parameter root message) := by
    intro entry hentry
    rcases QueryCache.toSet_cacheQuery_subset_insert cache input output hentry.1 with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  exact (ENat.toENNReal_mono (Set.encard_le_encard hsubset)).trans
    (by simpa only [cachedMessageEntryCount, ENat.toENNReal_add, ENat.toENNReal_one] using
      ENat.toENNReal_mono (Set.encard_insert_le (cachedMessageInputSet cache parameter root message) ⟨input, output⟩))
theorem randomOracle_cachedMessageEntryCount_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (input : HashInput) (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hr : result ∈ support ((randomOracle input).run cache)) :
    cachedMessageEntryCount result.2 parameter root message ≤ cachedMessageEntryCount cache parameter root message + 1 := by
  cases hc : cache input with
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨output, _, rfl⟩ := hr
      exact cachedMessageEntryCount_cacheQuery_le parameter root message cache input output
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hr
      subst result
      exact le_self_add
namespace Concrete
theorem signAttempt_cachedMessageEntryCount_le (key : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (result : Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache)) :
    cachedMessageEntryCount result.2 key.parameter key.root message ≤ cachedMessageEntryCount cache key.parameter key.root message + 1 := by
  rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hr
  obtain ⟨oracleResult, horacle, hpure⟩ := hr
  simp only [mem_support_pure_iff] at hpure
  subst result
  exact randomOracle_cachedMessageEntryCount_le key.parameter key.root message
    (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) cache oracleResult horacle
end Concrete
end SphincsSecurity
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_6 : SampleableType Randomness := Concrete.randomnessSampleableType
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop
theorem probEvent_signDigestAttemptPrefix_fresh_ge_messageMiss
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec) (hreference : reference ≤ cache) :
    messageInputMissProbability key message cache * Concrete.admissibleProbability ≤
      Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] := by
  rw [signDigestAttemptPrefix]
  apply mul_le_probEvent_bind
  · exact le_rfl
  · intro randomness _ hmiss
    have hrefMiss : reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none := by
      cases hc : reference (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => rfl
      | some output => simpa only [hmiss, reduceCtorEq] using hreference hc
    rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
      probEvent_bind_pure_comp]
    change Concrete.admissibleProbability ≤
      Pr[fun result => reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache]
    simpa only [hrefMiss, true_and] using (probEvent_signAttempt_fresh_success_eq key message randomness cache hmiss).ge
theorem digestAttemptExpectation_mul_message_rate_le_freshSelection
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hreference : reference ≤ cache) (budget rate : ENNReal)
    (hrate : rate ≤ (1 - budget * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * Concrete.admissibleProbability)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + (attempts : ENNReal) ≤ budget) :
    digestAttemptExpectation attempts key message cache * rate ≤
      Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] := by
  induction attempts generalizing cache with
  | zero => simp only [digestAttemptExpectation, zero_mul]; exact zero_le
  | succ attempts ih =>
      rw [digestAttemptExpectation, add_mul, one_mul, ← ENNReal.tsum_mul_right, probEvent_signDigestLoop_fresh_recurrence]
      apply add_le_add
      · apply hrate.trans (le_trans ?_ (probEvent_signDigestAttemptPrefix_fresh_ge_messageMiss key message reference cache hreference))
        rw [messageInputMissProbability_eq_count]
        exact mul_le_mul' (tsub_le_tsub_left (mul_le_mul' (le_self_add.trans hbudget) le_rfl) _) le_rfl
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
        · by_cases hnone : result.2.1 = none
          · rw [if_pos hnone, if_pos hnone, mul_assoc]
            apply mul_le_mul' le_rfl
            apply ih result.2.2 (hreference.trans (signDigestAttemptPrefix_cache_le key message cache result hr))
            have hgrowth := signAttempt_cachedMessageEntryCount_le key message result.1 cache result.2
              (signDigestAttemptPrefix_support_attempt key message cache result hr)
            calc
              _ ≤ (cachedMessageEntryCount cache key.parameter key.root message + 1) + (attempts : ENNReal) :=
                add_le_add hgrowth le_rfl
              _ = cachedMessageEntryCount cache key.parameter key.root message + ((attempts + 1 : Nat) : ENNReal) := by
                push_cast; ring
              _ ≤ _ := hbudget
          · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
        · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, le_refl]
noncomputable def messageDigestFreshRate (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  (1 - (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)) *
    ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * Concrete.admissibleProbability
noncomputable def messageDigestReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / messageDigestFreshRate key message cache
theorem messageDigestFreshRate_ge_budget (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    (1 - ((q + digestAttemptLimit : Nat) : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      Concrete.admissibleProbability ≤ messageDigestFreshRate key message cache := by
  unfold messageDigestFreshRate
  rw [Nat.cast_add]
  exact mul_le_mul' (tsub_le_tsub_left (mul_le_mul' (add_le_add
    ((cachedMessageEntryCount_le_enncard cache key.parameter key.root message).trans hcache) le_rfl) le_rfl) _) le_rfl
theorem messageDigestFreshRate_ne_zero (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestFreshRate key message cache ≠ 0 := by
  apply ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ?_) (messageDigestFreshRate_ge_budget key message cache q hcache))
  apply digestRaceSuccessRate_ne_zero_of_budget_lt
  norm_num [digestAttemptLimit, randomnessBits] at *
  omega
theorem messageDigestFreshRate_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageDigestFreshRate key message cache ≠ ⊤ := by
  unfold messageDigestFreshRate
  exact ENNReal.mul_ne_top (by finiteness) admissibleProbability_ne_top
theorem messageDigestReuseWeight_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestReuseWeight key message cache ≤ digestReuseWeight q :=
  ENNReal.div_le_div_left (messageDigestFreshRate_ge_budget key message cache q hcache) _
theorem messageDigestReuseWeight_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestReuseWeight key message cache ≠ ⊤ :=
  ne_top_of_le_ne_top (digestReuseWeight_ne_top q hq) (messageDigestReuseWeight_le key message cache q hcache)
theorem exactDigestReuseWeight_le_fresh_mul_messageReuseWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache := by
  have hcancel : messageDigestFreshRate key message cache * messageDigestReuseWeight key message cache =
      ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    unfold messageDigestReuseWeight
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel
      (messageDigestFreshRate_ne_zero key message cache q hq hcache) (messageDigestFreshRate_ne_top key message cache), mul_one]
  have h := mul_le_mul' (digestAttemptExpectation_mul_message_rate_le_freshSelection digestAttemptLimit key message cache cache le_rfl
    (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal))
    (messageDigestFreshRate key message cache) le_rfl le_rfl) (le_refl (messageDigestReuseWeight key message cache))
  rw [mul_assoc, hcancel] at h
  exact h
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def normalizedMessageReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  messageDigestReuseWeight key message cache /
    (1 + cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * messageDigestReuseWeight key message cache)
theorem normalizedMessageReuseWeight_eq_inv (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache =
      (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) +
        messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))⁻¹ := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let reuse := messageDigestReuseWeight key message cache
  have hreuseTop : reuse ≠ ⊤ := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hreuseZero : reuse ≠ 0 := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness))
      (ENNReal.inv_ne_zero.mpr (messageDigestFreshRate_ne_top key message cache))
  have hinv : reuse⁻¹ = messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (by finiteness)))
      (Or.inl (ENNReal.inv_ne_top.mpr (by positivity))), inv_inv, inv_inv, mul_comm]
  have hfactor : 1 + count * reuse = reuse * (count + reuse⁻¹) := by
    rw [mul_add, ENNReal.mul_inv_cancel hreuseZero hreuseTop]
    ring
  change reuse * (1 + count * reuse)⁻¹ = _
  rw [hfactor, ENNReal.mul_inv (Or.inl hreuseZero) (Or.inl hreuseTop), ← mul_assoc,
    ENNReal.mul_inv_cancel hreuseZero hreuseTop, one_mul, hinv]
theorem exactDigestReuseWeight_le_normalizedMessage (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ normalizedMessageReuseWeight key message cache := by
  have hcount : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness)
      ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache)
  have hreuse := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hmass : freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  unfold normalizedMessageReuseWeight
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  calc
    _ = exactDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by ring
    _ ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache :=
      add_le_add (exactDigestReuseWeight_le_fresh_mul_messageReuseWeight key message cache q hq hcache) le_rfl
    _ = (freshDigestSelectionProbability key message cache +
        cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by rw [add_mul]
    _ ≤ _ := mul_le_of_le_one_left' hmass
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def messageAdmissibleDeficit (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  cachedMessageEntryCount cache key.parameter key.root message * admissibleProbability -
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
theorem messageDigestFreshRate_balance (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) +
      (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)) *
        admissibleProbability = ((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability := by
  let count := cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)
  let space : ENNReal := (2 ^ randomnessBits : Nat)
  let admissible : ENNReal := admissibleProbability
  have hcount : count ≤ space := by
    apply (add_le_add ((cachedMessageEntryCount_le_enncard cache key.parameter key.root message).trans hcache) le_rfl).trans
    change (q : ENNReal) + (digestAttemptLimit : ENNReal) ≤ ((2 ^ randomnessBits : Nat) : ENNReal)
    rw [← Nat.cast_add]
    exact_mod_cast (show q + digestAttemptLimit ≤ 2 ^ randomnessBits by norm_num [digestAttemptLimit, randomnessBits] at *; omega)
  have hzero : space ≠ 0 := by dsimp only [space]; positivity
  have htop : space ≠ ⊤ := by dsimp only [space]; finiteness
  have hfraction : count * space⁻¹ ≤ 1 :=
    (mul_le_mul' hcount le_rfl).trans_eq (ENNReal.mul_inv_cancel hzero htop)
  have hcancel : (count * space⁻¹) * (space * admissible) = count * admissible := by
    rw [mul_assoc, ← mul_assoc space⁻¹, ENNReal.inv_mul_cancel hzero htop, one_mul]
  change ((1 - count * space⁻¹) * admissible) * space + count * admissible = _
  calc
    _ = ((1 - count * space⁻¹) + count * space⁻¹) * (space * admissible) := by rw [← hcancel]; ring
    _ = space * admissible := by rw [tsub_add_cancel_of_le hfraction, one_mul]
theorem normalizedMessageReuseWeight_le_deficit (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache ≤
      ((((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability) - ((digestAttemptLimit : ENNReal) * admissibleProbability +
        messageAdmissibleDeficit key message cache))⁻¹ := by
  rw [normalizedMessageReuseWeight_eq_inv key message cache q hq hcache]
  apply ENNReal.inv_le_inv.mpr
  apply tsub_le_iff_left.mpr
  rw [← messageDigestFreshRate_balance key message cache q hq hcache, add_mul]
  have hcount : cachedMessageEntryCount cache key.parameter key.root message * admissibleProbability ≤
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + messageAdmissibleDeficit key message cache :=
    le_add_tsub
  have h := add_le_add (add_le_add (le_refl (messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))) hcount)
    (le_refl ((digestAttemptLimit : ENNReal) * admissibleProbability))
  convert h using 1 <;> first | rfl | ring
theorem normalizedMessageReuseWeight_le_near_uniform_of_deficit
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q)
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    normalizedMessageReuseWeight key message cache ≤
      (1025 / 1024 : ENNReal) * (((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability)⁻¹ := by
  apply (normalizedMessageReuseWeight_le_deficit key message cache q hq hcache).trans
  apply (ENNReal.inv_le_inv.mpr (tsub_le_tsub_left (add_le_add le_rfl hdeficit) _)).trans
  have hp := admissibleProbability_ne_top
  have hlow := (ENNReal.toReal_le_toReal (by simp) hp).mpr admissibleProbability_ge
  have hhigh := (ENNReal.toReal_le_toReal hp (by simp)).mpr admissibleProbability_le
  rw [ENNReal.toReal_inv] at hlow hhigh
  norm_num at hlow hhigh
  have hsmall : (digestAttemptLimit : ENNReal) * admissibleProbability + ((2 ^ 83 : Nat) : ENNReal) <
      ((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, digestAttemptLimit, randomnessBits]
    push_cast
    nlinarith
  apply (ENNReal.toReal_le_toReal (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hsmall))) (by
    exact ENNReal.mul_ne_top (by finiteness) (ENNReal.inv_ne_top.mpr (mul_ne_zero (by simp) admissibleProbability_pos)))).mp
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hsmall.le (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, digestAttemptLimit, randomnessBits]
  push_cast
  set x := admissibleProbability.toReal
  have hx : 0 < x := by linarith
  rw [inv_le_iff_one_le_mul₀ (by nlinarith)]
  have hax : 0 < (2 : ℝ) ^ 128 * x := by positivity
  have hy : ((2 : ℝ) ^ 128 * x)⁻¹ * (2 ^ 128 * x) = 1 := inv_mul_cancel₀ hax.ne'
  have hypos : 0 < ((2 : ℝ) ^ 128 * x)⁻¹ := inv_pos.mpr hax
  have h1 : (2 : ℝ) ^ 128 * x - (2 ^ 20 * x + 2 ^ 83) ≥ 2 ^ 128 * x * (1024 / 1025) := by nlinarith
  norm_num at hy hypos h1 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 hypos.le]
theorem exactDigestReuseWeight_le_near_uniform_of_deficit
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q)
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    exactDigestReuseWeight key message cache ≤
      (1025 / 1024 : ENNReal) * (((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability)⁻¹ :=
  (exactDigestReuseWeight_le_normalizedMessage key message cache q hq hcache).trans
    (normalizedMessageReuseWeight_le_near_uniform_of_deficit key message cache q hq hcache hdeficit)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem cachedMessageEntryCount_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    cachedMessageEntryCount cache parameter root message ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCount_le_enncard cache parameter root message)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
theorem cachedMessageEntryCountWhere_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCountWhere_le_enncard cache parameter root message P)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
noncomputable def messageDeficitScore (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) : ℝ :=
  (cachedMessageEntryCount cache parameter root message).toReal * Concrete.admissibleProbability.toReal -
    (cachedMessageEntryCountWhere cache parameter root message (fun _ => True)).toReal
theorem messageDeficitScore_of_no_inputs (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hcount : cachedMessageEntryCount cache parameter root message = 0) :
    messageDeficitScore parameter root message cache ≤ 0 := by
  simp only [messageDeficitScore, hcount, ENNReal.toReal_zero, zero_mul, zero_sub]
  exact neg_nonpos.mpr ENNReal.toReal_nonneg
theorem messageDeficitScore_ofReal_eq (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    ENNReal.ofReal (messageDeficitScore key.parameter key.root message cache) =
      Concrete.messageAdmissibleDeficit key message cache := by
  have hcount := cachedMessageEntryCount_ne_top_of_finite key.parameter key.root message cache hfinite
  have hadmissible := cachedMessageEntryCountWhere_ne_top_of_finite key.parameter key.root message cache hfinite (fun _ => True)
  rw [messageDeficitScore, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hcount, ENNReal.ofReal_toReal hadmissible,
    ENNReal.ofReal_toReal Concrete.admissibleProbability_ne_top]
  rfl
end SphincsSecurity
end
section
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def positiveScoreMoment (score : ℝ) (power : Nat) : ENNReal :=
  ENNReal.ofReal (max score 0 ^ power)
theorem positiveScoreMoment_ne_top (score : ℝ) (power : Nat) : positiveScoreMoment score power ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top
theorem positiveScoreMoment_zero_of_nonpos (score : ℝ) (hscore : score ≤ 0) (power : Nat) (hpower : power ≠ 0) :
    positiveScoreMoment score power = 0 := by
  simp [positiveScoreMoment, max_eq_right hscore, zero_pow hpower]
end SphincsSecurity
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) : ENNReal :=
  ∑ message : Message, positiveScoreMoment (messageDeficitScore parameter root message cache) power
theorem positiveScoreMoment_le_messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) (message : Message) :
    positiveScoreMoment (messageDeficitScore parameter root message cache) power ≤
      messageDeficitMoment parameter root cache power := by
  unfold messageDeficitMoment
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun message : Message => positiveScoreMoment (messageDeficitScore parameter root message cache) power)
    (fun _ _ => zero_le) (Finset.mem_univ message)
theorem messageDeficitMoment_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hcount : ∀ message, cachedMessageEntryCount cache parameter root message = 0)
    (power : Nat) (hpower : power ≠ 0) : messageDeficitMoment parameter root cache power = 0 := by
  apply Finset.sum_eq_zero
  intro message _
  exact positiveScoreMoment_zero_of_nonpos _
    (messageDeficitScore_of_no_inputs parameter root message cache (hcount message)) power hpower
end SphincsSecurity
end
section
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
def MessageDeficitExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  ∃ message, ((2 ^ 83 : Nat) : ENNReal) < Concrete.messageAdmissibleDeficit key message cache
theorem positiveScoreMoment_eq_pow_ofReal (score : ℝ) (power : Nat) :
    positiveScoreMoment score power = ENNReal.ofReal score ^ power := by
  rw [positiveScoreMoment, ENNReal.ofReal_pow (le_max_right _ _)]
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show 0 ≤ ENNReal.ofReal score from zero_le)]
theorem cachedMessageEntryCount_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hnone : ∀ payload, cache (tweakableHashInput parameter .message payload) = none)
    (message : Message) : cachedMessageEntryCount cache parameter root message = 0 := by
  have hempty : cachedMessageInputSet cache parameter root message = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨input, answer⟩ ⟨hcached, randomness, hinput⟩
    change cache input = some answer at hcached
    have h := hnone (Concrete.messageDigestPayload root message randomness)
    rw [← hinput, hcached] at h
    cases h
  simp only [cachedMessageEntryCount, hempty, Set.encard_empty, ENat.toENNReal_zero]
end SphincsSecurity
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem TargetShapeValid.empty (remaining : Finset IndexGroup) : TargetShapeValid ∅ remaining := by
  constructor <;> intro group hgroup <;> exact (Finset.notMem_empty group hgroup).elim
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def nearUniformDigestReuseWeight : ENNReal :=
  (1025 / 1024 : ENNReal) * (((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability)⁻¹
theorem exactDigestReuseWeight_le_near_uniform_of_clean_cache (key : SecretKey) (cache : QueryCache HashSpec)
    (cap : Nat) (hcap : cap ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ cap)
    (hclean : ¬ MessageDeficitExceptional key cache) (message : Message) :
    exactDigestReuseWeight key message cache ≤ nearUniformDigestReuseWeight :=
  exactDigestReuseWeight_le_near_uniform_of_deficit key message cache cap hcap hcache
    (le_of_not_gt (fun h => hclean ⟨message, h⟩))
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open ENNReal
theorem reuseRawEnvelope_le_binomialAverage (key : SecretKey) (reuse rate : ENNReal)
    (hrate : rate ≤ 1) (queries signatures bound : Nat) (state : CoverLogState)
    (remaining : Finset IndexGroup) (hdegree : remaining.card ≤ bound)
    (hprob : ∀ index : Index,
      (Fintype.card Index : ENNReal)⁻¹ + reuse *
        (cachedIndexMultiplicity key.parameter state.1 index +
          (queries : ENNReal) * cachedIndexRate + bound + signatures) ≤ rate) :
    reuseRawEnvelope key reuse queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage rate signatures (fun count =>
        (((signingSlotsAtIndex (observedOptionalSigningViews
          (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal) + count) ^
          remaining.card) := by
  apply (reuseRawEnvelope_query_shift_le key reuse queries signatures bound state ∅ remaining
    (TargetShapeValid.empty _) (by simpa only [Finset.card_empty, Nat.zero_add] using hdegree)).trans
  apply Finset.sum_le_sum
  intro index _
  exact targetIndexSigning_iterate_power_le_binomialAverage hrate signatures (hprob index) _ remaining.card
noncomputable def targetProposalOverhead : ENNReal := 49185 / 32768
noncomputable def targetProposalIndexRate : ENNReal :=
  targetProposalOverhead * (Fintype.card Index : ENNReal)⁻¹
theorem targetProposalIndexRate_le_one : targetProposalIndexRate ≤ 1 := by
  unfold targetProposalIndexRate targetProposalOverhead
  norm_num only [Index, totalHeight, Fintype.card_fin]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, Index, totalHeight]
theorem targetProposalRate_of_cache_bound (cache : ENNReal) (spent queries signatures bound : Nat)
    (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit) (hbound : bound ≤ 15)
    (hcache : cache ≤ (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)) :
    (Fintype.card Index : ENNReal)⁻¹ + nearUniformDigestReuseWeight *
      (cache + (queries : ENNReal) * cachedIndexRate + bound + signatures) ≤
        targetProposalIndexRate := by
  have hsize : cache + (queries : ENNReal) * cachedIndexRate + bound + signatures ≤
      ((2 ^ 127 : Nat) : ENNReal) * cachedIndexRate +
        ((2 ^ 72 : Nat) : ENNReal) + 15 + signatureLimit := by
    calc
      _ ≤ (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal) +
          (queries : ENNReal) * cachedIndexRate + bound + signatures := by
        gcongr
      _ = ((spent + queries : Nat) : ENNReal) * cachedIndexRate +
          ((2 ^ 72 : Nat) : ENNReal) + bound + signatures := by
        push_cast
        ring
      _ ≤ _ := by
        exact add_le_add
          (add_le_add (add_le_add (mul_le_mul' (Nat.cast_le.mpr hqueries) le_rfl) le_rfl)
            (by exact_mod_cast hbound)) (Nat.cast_le.mpr hsignatures)
  apply (add_le_add le_rfl (mul_le_mul' le_rfl hsize)).trans
  unfold nearUniformDigestReuseWeight targetProposalIndexRate targetProposalOverhead cachedIndexRate
  have hp := admissibleProbability_ne_top
  have hlow := (ENNReal.toReal_le_toReal (by simp) hp).mpr admissibleProbability_ge
  have hhigh := (ENNReal.toReal_le_toReal hp (by simp)).mpr admissibleProbability_le
  rw [ENNReal.toReal_inv] at hlow hhigh
  norm_num at hlow hhigh
  have hpos : admissibleProbability ≠ 0 := admissibleProbability_pos
  norm_num only [Index, totalHeight, Fintype.card_fin, signatureLimit, randomnessBits]
  have hprod : ((2 : ENNReal) ^ 128 * admissibleProbability) ≠ 0 := mul_ne_zero (by simp) hpos
  have hprodTop : ((2 : ENNReal) ^ 128 * admissibleProbability) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hp
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  set x := admissibleProbability.toReal
  have hx : 0 < x := by linarith
  have hinv : ((2 : ℝ) ^ 128 * x)⁻¹ * (2 ^ 128 * x) = 1 := inv_mul_cancel₀ (by positivity)
  have hinvpos : 0 < ((2 : ℝ) ^ 128 * x)⁻¹ := by positivity
  have hsmall : ((2 : ℝ) ^ 128 * x)⁻¹ * (2 ^ 72 + 15 + 2 ^ 32) ≤ 3 / 10 ^ 14 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  norm_num at hinv hinvpos hsmall ⊢
  nlinarith [mul_pos hinvpos hx]
theorem reuseRawEnvelope_le_proposalIndexAverage (key : SecretKey)
    (spent queries signatures bound : Nat) (state : CoverLogState) (remaining : Finset IndexGroup)
    (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit)
    (hdegree : remaining.card ≤ bound) (hbound : bound ≤ 15)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage targetProposalIndexRate signatures (fun count =>
        (((signingSlotsAtIndex (observedOptionalSigningViews
          (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal) + count) ^
          remaining.card) :=
  reuseRawEnvelope_le_binomialAverage key nearUniformDigestReuseWeight targetProposalIndexRate
    targetProposalIndexRate_le_one queries signatures bound state remaining hdegree
    (fun index => targetProposalRate_of_cache_bound _ spent queries signatures bound hqueries hsignatures hbound (hcache index))
theorem proposalIndexAverage_le_uniformAverage (signatures proposals degree : Nat)
    {signings consumed : ENNReal} (hcounts : signings ≤ consumed)
    (hroom : targetProposalOverhead * signatures + degree ≤ ((proposals + 1 : Nat) : ENNReal)) :
    binomialAverage targetProposalIndexRate signatures (fun count => (signings + count) ^ degree) ≤
      binomialAverage (Fintype.card Index : ENNReal)⁻¹ proposals (fun count => (consumed + count) ^ degree) := by
  apply binomialAverage_shifted_power_le_of_room targetProposalIndexRate_le_one
    (by norm_num [Index, totalHeight]) hcounts signatures proposals degree (mass := targetProposalOverhead * signatures)
  · unfold targetProposalIndexRate
    exact le_of_eq (by ring)
  · exact hroom
theorem reuseRawEnvelope_le_uniformProposalAverage (key : SecretKey)
    (spent queries signatures bound proposals : Nat) (state : CoverLogState) (remaining : Finset IndexGroup)
    (consumed : Index → Nat) (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit)
    (hdegree : remaining.card ≤ bound) (hbound : bound ≤ 15)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumed index)
    (hroom : targetProposalOverhead * signatures + remaining.card ≤ ((proposals + 1 : Nat) : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage (Fintype.card Index : ENNReal)⁻¹ proposals
        (fun count => ((consumed index : ENNReal) + count) ^ remaining.card) := by
  apply (reuseRawEnvelope_le_proposalIndexAverage key spent queries signatures bound state remaining
    hqueries hsignatures hdegree hbound hcache).trans
  apply Finset.sum_le_sum
  intro index _
  exact proposalIndexAverage_le_uniformAverage signatures proposals remaining.card
    (Nat.cast_le.mpr (hcounts index)) hroom
end SphincsSecurity.Concrete
end
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_UniformProposalMoments ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
noncomputable def sampleUniformProposalWord (α : Type) [SampleableType α] : Nat → ProbComp (List α)
  | 0 => pure []
  | steps + 1 => do
      let next ← $ᵗ α
      let rest ← sampleUniformProposalWord α steps
      pure (next :: rest)
theorem expected_uniformSample_choice {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (index : α) (hit miss : ENNReal) :
    (∑' next : α, Pr[= next | ($ᵗ α : ProbComp α)] * (if next = index then hit else miss)) =
      (1 - (Fintype.card α : ENNReal)⁻¹) * miss + (Fintype.card α : ENNReal)⁻¹ * hit := by
  classical
  have hmiss : Pr[fun next => next ≠ index | ($ᵗ α : ProbComp α)] =
      1 - (Fintype.card α : ENNReal)⁻¹ := by
    apply ENNReal.eq_sub_of_add_eq' (by finiteness)
    have h := probEvent_compl ($ᵗ α : ProbComp α) (fun next => next = index)
    simpa only [probEvent_eq_eq_probOutput, probOutput_uniformSample, probFailure_uniformSample, tsub_zero,
      add_comm] using h
  calc
    _ = (∑' next : α, (if next = index then Pr[= next | ($ᵗ α : ProbComp α)] else 0)) * hit +
        (∑' next : α, (if next ≠ index then Pr[= next | ($ᵗ α : ProbComp α)] else 0)) * miss := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      apply tsum_congr
      intro next
      by_cases h : next = index <;> simp [h]
    _ = _ := by
      rw [← probEvent_eq_tsum_ite, ← probEvent_eq_tsum_ite, probEvent_eq_eq_probOutput,
        probOutput_uniformSample, hmiss, add_comm]
theorem expected_uniformProposalWord_count {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (index : α) (steps : Nat) (f : Nat → ENNReal) :
    (∑' word : List α, Pr[= word | sampleUniformProposalWord α steps] * f (word.count index)) =
      binomialAverage (Fintype.card α : ENNReal)⁻¹ steps f := by
  induction steps generalizing f with
  | zero => simp only [sampleUniformProposalWord, tsum_probOutput_pure_mul, List.count_nil, binomialAverage_zero]
  | succ steps ih =>
      rw [sampleUniformProposalWord, tsum_probOutput_bind_mul]
      simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      have hinner (next : α) :
          (∑' word : List α, Pr[= word | sampleUniformProposalWord α steps] * f ((next :: word).count index)) =
            if next = index then binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => f (count + 1))
              else binomialAverage (Fintype.card α : ENNReal)⁻¹ steps f := by
        by_cases h : next = index
        · subst next
          simpa only [List.count_cons_self, ↓reduceIte] using ih (fun count => f (count + 1))
        · simpa only [List.count_cons_of_ne h, if_neg h] using ih f
      simp_rw [hinner]
      exact expected_uniformSample_choice index _ _
theorem expected_uniformProposalWord_power_sum {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (steps degree : Nat) (consumed : α → Nat) :
    (∑' word : List α, Pr[= word | sampleUniformProposalWord α steps] *
      ∑ index : α, ((consumed index : ENNReal) + word.count index) ^ degree) =
      ∑ index : α, binomialAverage (Fintype.card α : ENNReal)⁻¹ steps
        (fun count => ((consumed index : ENNReal) + count) ^ degree) := by
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro index _
  exact expected_uniformProposalWord_count index steps (fun count => ((consumed index : ENNReal) + count) ^ degree)
theorem reuseRawEnvelope_le_expected_uniformProposalWord (key : SecretKey)
    (spent queries signatures bound proposals : Nat) (state : CoverLogState) (remaining : Finset IndexGroup)
    (consumed : Index → Nat) (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit)
    (hdegree : remaining.card ≤ bound) (hbound : bound ≤ 15)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumed index)
    (hroom : targetProposalOverhead * signatures + remaining.card ≤ ((proposals + 1 : Nat) : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries signatures state ∅ remaining ≤
      ∑' word : List Index, Pr[= word | sampleUniformProposalWord Index proposals] *
        ∑ index : Index, ((consumed index : ENNReal) + word.count index) ^ remaining.card := by
  rw [expected_uniformProposalWord_power_sum]
  exact reuseRawEnvelope_le_uniformProposalAverage key spent queries signatures bound proposals state remaining
    consumed hqueries hsignatures hdegree hbound hcache hcounts hroom
theorem targetProposalRoom_of_prefix (completed signatures total used degree slack : Nat)
    (hsignatures : completed + signatures ≤ signatureLimit) (hdegree : degree ≤ 15)
    (htotal : targetProposalOverhead * signatureLimit + slack + 14 ≤ (total : ENNReal))
    (hused : (used : ENNReal) ≤ targetProposalOverhead * completed + slack) :
    targetProposalOverhead * signatures + degree ≤ ((total - used + 1 : Nat) : ENNReal) := by
  have hcompleted : completed ≤ signatureLimit := (Nat.le_add_right completed signatures).trans hsignatures
  have husedTotal : used ≤ total := by
    apply (Nat.cast_le (α := ENNReal)).mp
    exact hused.trans ((add_le_add (mul_le_mul' le_rfl (Nat.cast_le.mpr hcompleted)) le_rfl).trans
      ((le_self_add : targetProposalOverhead * signatureLimit + slack ≤
        targetProposalOverhead * signatureLimit + slack + 14).trans htotal))
  have hcapacity : (used : ENNReal) + (targetProposalOverhead * signatures + degree) ≤ (total : ENNReal) + 1 := by
    calc
      _ ≤ targetProposalOverhead * completed + slack + (targetProposalOverhead * signatures + degree) :=
        add_le_add hused le_rfl
      _ = targetProposalOverhead * ((completed + signatures : Nat) : ENNReal) + slack + degree := by
        push_cast
        ring
      _ ≤ targetProposalOverhead * signatureLimit + slack + 15 :=
        add_le_add (add_le_add (mul_le_mul' le_rfl (Nat.cast_le.mpr hsignatures)) le_rfl)
          (by exact_mod_cast hdegree)
      _ = (targetProposalOverhead * signatureLimit + slack + 14) + 1 := by ring
      _ ≤ _ := add_le_add htotal le_rfl
  have hsum : ((total - used + 1 : Nat) : ENNReal) + (used : ENNReal) = (total : ENNReal) + 1 := by
    exact_mod_cast (show total - used + 1 + used = total + 1 by omega)
  apply ENNReal.le_of_add_le_add_right (a := (used : ENNReal)) (by finiteness)
  calc
    _ = (used : ENNReal) + (targetProposalOverhead * signatures + degree) := add_comm _ _
    _ ≤ (total : ENNReal) + 1 := hcapacity
    _ = _ := hsum.symm
theorem targetProposalPoolMinimum_eq :
    targetProposalOverhead * signatureLimit + (proposalPrefixSlack : ENNReal) + 14 = (fixedProposalLength : ENNReal) := by
  unfold targetProposalOverhead
  rw [proposalPrefixSlack_def, fixedProposalLength_def]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
  norm_num [signatureLimit]
theorem reuseRawEnvelope_le_expected_terminalProposalWord (key : SecretKey)
    (spent queries completed total : Nat) (state : CoverLogState) (remaining : Finset IndexGroup)
    (consumedWord : List Index) (hqueries : spent + queries ≤ 2 ^ 127) (hcompleted : completed ≤ signatureLimit)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumedWord.count index)
    (htotal : fixedProposalLength ≤ total)
    (hprefix : (consumedWord.length : ENNReal) ≤ targetProposalOverhead * completed + (proposalPrefixSlack : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries (signatureLimit - completed) state ∅ remaining ≤
      ∑' word : List Index, Pr[= word | sampleUniformProposalWord Index (total - consumedWord.length)] *
        ∑ index : Index, ((consumedWord ++ word).count index : ENNReal) ^ remaining.card := by
  have hdegree : remaining.card ≤ 15 := by
    exact (Finset.card_le_univ remaining).trans_eq (by simp [ftsOpenings] : Fintype.card IndexGroup = 15)
  have hroom : targetProposalOverhead * (signatureLimit - completed : Nat) + remaining.card ≤
      ((total - consumedWord.length + 1 : Nat) : ENNReal) :=
    targetProposalRoom_of_prefix completed (signatureLimit - completed) total consumedWord.length remaining.card proposalPrefixSlack
      (by omega) hdegree
      (by rw [targetProposalPoolMinimum_eq]; exact_mod_cast htotal) hprefix
  have h := reuseRawEnvelope_le_expected_uniformProposalWord key spent queries (signatureLimit - completed) 15
    (total - consumedWord.length) state remaining (fun index => consumedWord.count index) hqueries (Nat.sub_le _ _)
    hdegree le_rfl hcache hcounts hroom
  simpa only [List.count_append, Nat.cast_add] using h
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_UniformProposalMixedMoments ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
noncomputable def uniformWordAverage {α : Type} [SampleableType α]
    (steps : Nat) (payoff : List α → ENNReal) : ENNReal :=
  ∑' word, Pr[= word | sampleUniformProposalWord α steps] * payoff word
theorem uniformWordAverage_add {α : Type} [SampleableType α]
    (steps : Nat) (first second : List α → ENNReal) :
    uniformWordAverage steps (fun word => first word + second word) =
      uniformWordAverage steps first + uniformWordAverage steps second := by
  simp only [uniformWordAverage, mul_add, ENNReal.tsum_add]
theorem uniformWordAverage_mul_left {α : Type} [SampleableType α]
    (steps : Nat) (factor : ENNReal) (payoff : List α → ENNReal) :
    uniformWordAverage steps (fun word => factor * payoff word) =
      factor * uniformWordAverage steps payoff := by
  simp only [uniformWordAverage, mul_left_comm _ factor, ENNReal.tsum_mul_left]
theorem uniformWordAverage_sum {α β : Type} [SampleableType α]
    (steps : Nat) (set : Finset β) (payoff : β → List α → ENNReal) :
    uniformWordAverage steps (fun word => ∑ index ∈ set, payoff index word) =
      ∑ index ∈ set, uniformWordAverage steps (payoff index) := by
  simp only [uniformWordAverage, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
theorem uniformWordAverage_count_descFactorial {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (index : α) (steps degree : Nat) :
    uniformWordAverage steps (fun word : List α => (word.count index).descFactorial degree) =
      (steps.descFactorial degree : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ^ degree := by
  letI : Nonempty α := ⟨index⟩
  rw [uniformWordAverage, expected_uniformProposalWord_count index steps
    (fun count => (count.descFactorial degree : ENNReal))]
  exact binomialAverage_descFactorial (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos)) steps degree
theorem descFactorial_succ_add (count degree : Nat) :
    (count + 1).descFactorial (degree + 1) =
      count.descFactorial (degree + 1) + (degree + 1) * count.descFactorial degree := by
  rw [Nat.succ_descFactorial_succ]
  calc
    _ = count * count.descFactorial degree + count.descFactorial degree := by ring
    _ = _ := by rw [mul_descFactorial_eq]; ring
private theorem expected_uniformSample_two_increments {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (base left right : ENNReal) :
    (∑' next : α, Pr[= next | ($ᵗ α : ProbComp α)] *
      (base + (if next = first then left else 0) + (if next = second then right else 0))) =
      base + (Fintype.card α : ENNReal)⁻¹ * left + (Fintype.card α : ENNReal)⁻¹ * right := by
  simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_zero]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, probFailure_uniformSample, tsub_zero, one_mul]
  simp only [tsum_ite_eq, probOutput_uniformSample]
theorem uniformWordAverage_mixed_descFactorial {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (hdistinct : first ≠ second)
    (steps left right : Nat) :
    uniformWordAverage steps (fun word : List α =>
      ((word.count first).descFactorial left : ENNReal) * (word.count second).descFactorial right) =
      (steps.descFactorial (left + right) : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ^ (left + right) := by
  induction steps generalizing left right with
  | zero =>
      cases left <;> cases right <;>
        simp [uniformWordAverage, sampleUniformProposalWord]
  | succ steps ih =>
      cases left with
      | zero =>
          simpa only [Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.zero_add] using
            uniformWordAverage_count_descFactorial second (steps + 1) right
      | succ left =>
          cases right with
          | zero =>
              simpa only [Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.add_zero] using
                uniformWordAverage_count_descFactorial first (steps + 1) (left + 1)
          | succ right =>
              have hpoint (word : List α) (next : α) :
                  (((next :: word).count first).descFactorial (left + 1) : ENNReal) *
                    ((next :: word).count second).descFactorial (right + 1) =
                  ((word.count first).descFactorial (left + 1) : ENNReal) *
                    (word.count second).descFactorial (right + 1) +
                  (if next = first then (left + 1 : ENNReal) *
                    ((word.count first).descFactorial left * (word.count second).descFactorial (right + 1)) else 0) +
                  (if next = second then (right + 1 : ENNReal) *
                    ((word.count first).descFactorial (left + 1) * (word.count second).descFactorial right) else 0) := by
                by_cases hfirst : next = first
                · subst next
                  simp only [List.count_cons_self, List.count_cons_of_ne hdistinct,
                    descFactorial_succ_add, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
                    ↓reduceIte, if_neg hdistinct, add_zero]
                  ring
                · by_cases hsecond : next = second
                  · subst next
                    simp only [List.count_cons_self, List.count_cons_of_ne hfirst,
                      descFactorial_succ_add, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
                      ↓reduceIte, if_neg hfirst, add_zero]
                    ring
                  · simp only [List.count_cons_of_ne hfirst, List.count_cons_of_ne hsecond,
                      if_neg hfirst, if_neg hsecond, add_zero]
              rw [uniformWordAverage, sampleUniformProposalWord, tsum_probOutput_bind_mul]
              simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
              simp_rw [← ENNReal.tsum_mul_left]
              rw [ENNReal.tsum_comm]
              simp_rw [← mul_assoc]
              have hreorder :
                  (∑' word : List α, ∑' next : α, Pr[= next | ($ᵗ α : ProbComp α)] *
                    Pr[= word | sampleUniformProposalWord α steps] *
                    (((next :: word).count first).descFactorial (left + 1) : ENNReal) *
                    ((next :: word).count second).descFactorial (right + 1)) =
                  uniformWordAverage steps (fun word : List α =>
                    ((word.count first).descFactorial (left + 1) : ENNReal) *
                      (word.count second).descFactorial (right + 1) +
                    (Fintype.card α : ENNReal)⁻¹ * (left + 1) *
                      ((word.count first).descFactorial left * (word.count second).descFactorial (right + 1)) +
                    (Fintype.card α : ENNReal)⁻¹ * (right + 1) *
                      ((word.count first).descFactorial (left + 1) * (word.count second).descFactorial right)) := by
                unfold uniformWordAverage
                apply tsum_congr
                intro word
                calc
                  _ = Pr[= word | sampleUniformProposalWord α steps] * ∑' next : α,
                      Pr[= next | ($ᵗ α : ProbComp α)] *
                        ((((next :: word).count first).descFactorial (left + 1) : ENNReal) *
                          ((next :: word).count second).descFactorial (right + 1)) := by
                    rw [← ENNReal.tsum_mul_left]
                    apply tsum_congr
                    intro next
                    ring
                  _ = _ := by
                    simp_rw [hpoint, expected_uniformSample_two_increments]
                    ring
              rw [hreorder, uniformWordAverage_add, uniformWordAverage_add,
                uniformWordAverage_mul_left, uniformWordAverage_mul_left, ih, ih, ih]
              have hdegree : left + 1 + (right + 1) = (left + right + 1) + 1 := by omega
              rw [hdegree, descFactorial_succ_add]
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, pow_succ]
              have hexp : left + (right + 1) = left + right + 1 := by omega
              simp only [hexp, Nat.add_right_comm left 1 right, pow_succ]
              ring
theorem descFactorial_add_le_mul (steps left right : Nat) :
    steps.descFactorial (left + right) ≤ steps.descFactorial left * steps.descFactorial right := by
  have h := Nat.descFactorial_mul_descFactorial (n := steps) (k := left) (m := left + right)
    (Nat.le_add_right left right)
  rw [Nat.add_sub_cancel_left] at h
  rw [← h, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.descFactorial_le right (Nat.sub_le steps left))
theorem uniformWordAverage_mixed_descFactorial_le_product {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (hdistinct : first ≠ second)
    (steps left right : Nat) :
    uniformWordAverage steps (fun word : List α =>
      ((word.count first).descFactorial left : ENNReal) * (word.count second).descFactorial right) ≤
      uniformWordAverage steps (fun word : List α => (word.count first).descFactorial left) *
        uniformWordAverage steps (fun word : List α => (word.count second).descFactorial right) := by
  rw [uniformWordAverage_mixed_descFactorial first second hdistinct,
    uniformWordAverage_count_descFactorial, uniformWordAverage_count_descFactorial]
  calc
    _ ≤ ((steps.descFactorial left : ENNReal) * steps.descFactorial right) *
        (Fintype.card α : ENNReal)⁻¹ ^ (left + right) := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast descFactorial_add_le_mul steps left right
    _ = _ := by rw [pow_add]; ring
theorem uniformWordAverage_mono {α : Type} [SampleableType α]
    (steps : Nat) {first second : List α → ENNReal} (hle : ∀ word, first word ≤ second word) :
    uniformWordAverage steps first ≤ uniformWordAverage steps second :=
  ENNReal.tsum_le_tsum fun word => mul_le_mul' le_rfl (hle word)
theorem uniformWordAverage_mixed_power_le_product {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (first second : α) (hdistinct : first ≠ second)
    (steps left right : Nat) :
    uniformWordAverage steps (fun word : List α => (word.count first : ENNReal) ^ left *
      (word.count second : ENNReal) ^ right) ≤
      uniformWordAverage steps (fun word : List α => (word.count first : ENNReal) ^ left) *
        uniformWordAverage steps (fun word : List α => (word.count second : ENNReal) ^ right) := by
  have hpower (count degree : Nat) : (count : ENNReal) ^ degree =
      ∑ order ∈ Finset.range (degree + 1),
        (Nat.stirlingSecond degree order : ENNReal) * count.descFactorial order := by
    exact_mod_cast power_eq_stirling_descFactorial count degree
  simp_rw [hpower, Finset.sum_mul, Finset.mul_sum, uniformWordAverage_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hfactor :
      (fun word : List α =>
        ((Nat.stirlingSecond left a : ENNReal) * (word.count first).descFactorial a) *
          ((Nat.stirlingSecond right b : ENNReal) * (word.count second).descFactorial b)) =
      (fun word : List α =>
        ((Nat.stirlingSecond left a : ENNReal) * Nat.stirlingSecond right b) *
          ((word.count first).descFactorial a * (word.count second).descFactorial b)) := by
    funext word
    ring
  rw [hfactor, uniformWordAverage_mul_left, uniformWordAverage_mul_left, uniformWordAverage_mul_left]
  exact (mul_le_mul' le_rfl
    (uniformWordAverage_mixed_descFactorial_le_product first second hdistinct steps a b)).trans_eq (by ring)
noncomputable def stirlingPowerMoment (rate : ENNReal) (degree : Nat) : ENNReal :=
  ∑ order ∈ Finset.range (degree + 1), (Nat.stirlingSecond degree order : ENNReal) * rate ^ order
theorem uniformWordAverage_power_le_stirling {α : Type} [SampleableType α]
    [Fintype α] [DecidableEq α] (index : α) (steps degree : Nat) (rate : ENNReal)
    (hrate : (steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ≤ rate) :
    uniformWordAverage steps (fun word : List α => (word.count index : ENNReal) ^ degree) ≤
      stirlingPowerMoment rate degree := by
  letI : Nonempty α := ⟨index⟩
  rw [uniformWordAverage, expected_uniformProposalWord_count index steps (fun count => (count : ENNReal) ^ degree),
    binomialAverage_power (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos))]
  apply Finset.sum_le_sum
  intro order _
  calc
    _ ≤ (Nat.stirlingSecond degree order : ENNReal) * (steps : ENNReal) ^ order *
        (Fintype.card α : ENNReal)⁻¹ ^ order := by
      apply mul_le_mul' (mul_le_mul' le_rfl _) le_rfl
      exact_mod_cast Nat.descFactorial_le_pow steps order
    _ = (Nat.stirlingSecond degree order : ENNReal) *
        ((steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹) ^ order := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left' hrate order)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_UniformProposalVariance ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
theorem uniformWordAverage_sum_square_le {α β : Type} [SampleableType α] [Fintype β] [DecidableEq β]
    (steps : Nat) (payoff : β → List α → ENNReal)
    (hcross : ∀ first second, first ≠ second →
      uniformWordAverage steps (fun word => payoff first word * payoff second word) ≤
        uniformWordAverage steps (payoff first) * uniformWordAverage steps (payoff second)) :
    uniformWordAverage steps (fun word => (∑ index, payoff index word) ^ 2) ≤
      (∑ index, uniformWordAverage steps (payoff index)) ^ 2 +
        ∑ index, uniformWordAverage steps (fun word => payoff index word ^ 2) := by
  calc
    _ = ∑ first, ∑ second, uniformWordAverage steps
        (fun word => payoff first word * payoff second word) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, uniformWordAverage_sum]
      exact Finset.sum_comm
    _ ≤ ∑ first, ∑ second,
        (uniformWordAverage steps (payoff first) * uniformWordAverage steps (payoff second) +
          if second = first then uniformWordAverage steps (fun word => payoff first word ^ 2) else 0) := by
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
noncomputable def proposalPowerSum {α : Type} [Fintype α] [DecidableEq α]
    (degree : Nat) (word : List α) : ENNReal :=
  ∑ index : α, (word.count index : ENNReal) ^ degree
theorem uniformWordAverage_powerSum_le {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (steps degree : Nat) (rate : ENNReal)
    (hrate : (steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ≤ rate) :
    uniformWordAverage steps (proposalPowerSum (α := α) degree) ≤
      (Fintype.card α : ENNReal) * stirlingPowerMoment rate degree := by
  unfold proposalPowerSum
  rw [uniformWordAverage_sum]
  calc
    _ ≤ ∑ _index : α, stirlingPowerMoment rate degree :=
      Finset.sum_le_sum fun index _ => uniformWordAverage_power_le_stirling index steps degree rate hrate
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
theorem uniformWordAverage_powerSum_square_le {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (steps degree : Nat) (rate : ENNReal)
    (hrate : (steps : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ≤ rate) :
    uniformWordAverage steps (fun word => proposalPowerSum (α := α) degree word ^ 2) ≤
      uniformWordAverage steps (proposalPowerSum (α := α) degree) ^ 2 +
        (Fintype.card α : ENNReal) * stirlingPowerMoment rate (degree * 2) := by
  have h := uniformWordAverage_sum_square_le steps
    (fun index (word : List α) => (word.count index : ENNReal) ^ degree)
    (fun first second hne => uniformWordAverage_mixed_power_le_product first second hne steps degree degree)
  rw [← uniformWordAverage_sum] at h
  apply h.trans
  apply add_le_add le_rfl
  simp_rw [← pow_mul]
  calc
    _ ≤ ∑ _index : α, stirlingPowerMoment rate (degree * 2) :=
      Finset.sum_le_sum fun index _ => uniformWordAverage_power_le_stirling index steps (degree * 2) rate hrate
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end SphincsSecurity.Concrete
end
-- ==== merged from T3_Gate6_BankMoments ====
section

namespace SigGolfResearch.Gate6.Moments
open OracleComp OracleSpec ENNReal
open scoped BigOperators
open SphincsSecurity.Concrete (binomialAverage binomialAverage_add binomialAverage_mul_left
  binomialAverage_descFactorial)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def Covered {k n : Nat} (exposed : Finset (Fin n)) (draw : Fin k → Fin n) : Prop :=
  Function.Injective draw ∧ ∀ i, draw i ∈ exposed
noncomputable def coveredEquiv {k n : Nat} (exposed : Finset (Fin n)) :
    {draw : Fin k → Fin n // Covered exposed draw} ≃ (Fin k ↪ exposed) where
  toFun draw := ⟨fun i => ⟨draw.1 i,draw.2.2 i⟩,fun _i _j h => draw.2.1 (congrArg Subtype.val h)⟩
  invFun embedding := ⟨fun i => (embedding i).val,
    fun _i _j h => embedding.injective (Subtype.ext h),fun i => (embedding i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem covered_count (k n : Nat) (exposed : Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin k → Fin n => Covered exposed draw).card =
      exposed.card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (coveredEquiv exposed),Fintype.card_embedding_eq]
  simp only [Fintype.card_fin,Fintype.card_coe]
theorem covered_probability (k n : Nat) [NeZero n] (exposed : Finset (Fin n)) :
    Pr[Covered exposed | ($ᵗ (Fin k → Fin n) : ProbComp _)] =
      (exposed.card.descFactorial k : ENNReal)/(n : ENNReal)^k := by
  classical
  rw [probEvent_uniformSample,covered_count]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
theorem covered_probability_le (k n r : Nat) [NeZero n]
    (exposed : Finset (Fin n)) (hsize : exposed.card≤k*r) :
    Pr[Covered exposed | ($ᵗ (Fin k → Fin n) : ProbComp _)] ≤
      ((k*r).descFactorial k : ENNReal)/(n : ENNReal)^k := by
  rw [covered_probability k n]
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.descFactorial_le k hsize
theorem covered_product_count {d k n : Nat} (exposed : Fin d → Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin d → (Fin k → Fin n) =>
      ∀ c, Covered (exposed c) (draw c)).card =
        ∏ c, (exposed c).card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr Equiv.subtypePiEquivPi,Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  rw [Fintype.card_subtype,covered_count]
theorem three_openings_polynomial (r : Nat) :
    (3*r).descFactorial 3 =
      6*r.descFactorial 1+54*r.descFactorial 2+27*r.descFactorial 3 := by
  rcases r with _|_|r
  · decide
  · decide
  · simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.mul_one]
    simp only [Nat.sub_zero,Nat.add_sub_cancel]
    rw [show 3*(r+1+1)-2=3*r+4 by omega,show 3*(r+1+1)-1=3*r+5 by omega,
      show r+1+1-2=r by omega]
    ring
theorem two_openings_polynomial (r : Nat) :
    (3*r).descFactorial 2 = 6*r.descFactorial 1+9*r.descFactorial 2 := by
  rcases r with _|r
  · decide
  · simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.mul_one]
    simp only [Nat.sub_zero,Nat.add_sub_cancel]
    rw [show 3*(r+1)-1=3*r+2 by omega]
    ring
theorem bucket_thinning (p : ENNReal) (hp : p≤1) (r : Nat) :
    binomialAverage p r (fun count => ((3*count).descFactorial 3 : ENNReal)) =
      6*(r.descFactorial 1 : ENNReal)*p+
      54*(r.descFactorial 2 : ENNReal)*p^2+
      27*(r.descFactorial 3 : ENNReal)*p^3 := by
  simp_rw [three_openings_polynomial,Nat.cast_add,Nat.cast_mul]
  rw [binomialAverage_add,binomialAverage_add]
  simp_rw [binomialAverage_mul_left,binomialAverage_descFactorial hp]
  norm_num only [Nat.cast_ofNat,pow_one]
  ring
theorem near_bucket_thinning (p : ENNReal) (hp : p≤1) (r : Nat) :
    binomialAverage p r (fun count => ((3*count).descFactorial 2 : ENNReal)) =
      6*(r.descFactorial 1 : ENNReal)*p+9*(r.descFactorial 2 : ENNReal)*p^2 := by
  simp_rw [two_openings_polynomial,Nat.cast_add,Nat.cast_mul]
  rw [binomialAverage_add]
  simp_rw [binomialAverage_mul_left,binomialAverage_descFactorial hp]
  norm_num only [Nat.cast_ofNat,pow_one]
  ring
noncomputable def bucketCoveredEquiv {b k n : Nat} (exposed : Fin b → Finset (Fin n)) :
    {draw : Fin b × (Fin k → Fin n) // Covered (exposed draw.1) draw.2} ≃
      (bucket : Fin b) × {draw : Fin k → Fin n // Covered (exposed bucket) draw} where
  toFun draw := ⟨draw.1.1,draw.1.2,draw.2⟩
  invFun draw := ⟨(draw.1,draw.2.1),draw.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem bucket_covered_count {b k n : Nat} (exposed : Fin b → Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin b × (Fin k → Fin n) =>
      Covered (exposed draw.1) draw.2).card = ∑ bucket, (exposed bucket).card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (bucketCoveredEquiv exposed),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro bucket _
  rw [Fintype.card_subtype,covered_count]
theorem bucket_covered_probability {b k n : Nat} [NeZero b] [NeZero n]
    (exposed : Fin b → Finset (Fin n)) :
    Pr[fun draw : Fin b × (Fin k → Fin n) => Covered (exposed draw.1) draw.2 |
      ($ᵗ (Fin b × (Fin k → Fin n)) : ProbComp _)] =
      (∑ bucket, ((exposed bucket).card.descFactorial k : ENNReal))/
        ((b : ENNReal)*(n : ENNReal)^k) := by
  classical
  rw [probEvent_uniformSample,bucket_covered_count]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_sum]
theorem bucket_product_count {d b k n : Nat} (exposed : Fin d → Fin b → Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin d → (Fin b × (Fin k → Fin n)) =>
      ∀ c, Covered (exposed c (draw c).1) (draw c).2).card =
        ∏ c, ∑ bucket, (exposed c bucket).card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun (c : Fin d) (draw : Fin b × (Fin k → Fin n)) => Covered (exposed c draw.1) draw.2)),Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  rw [Fintype.card_subtype,bucket_covered_count]
theorem bpors_covered_probability (exposed : Fin 7 → Fin 16 → Finset (Fin 128)) :
    Pr[fun draw : Fin 7 → (Fin 16 × (Fin 3 → Fin 128)) =>
      ∀ c, Covered (exposed c (draw c).1) (draw c).2 |
      ($ᵗ (Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : ProbComp _)] =
        ∏ c : Fin 7, ((∑ bucket : Fin 16, ((exposed c bucket).card.descFactorial 3 : ENNReal))/(16*128^3)) := by
  classical
  rw [probEvent_uniformSample,bucket_product_count]
  simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Nat.cast_pow,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_prod,Nat.cast_sum,div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]
noncomputable def envelope (coefficients : List Nat) (count : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range coefficients.length,
    (coefficients.getD degree 0 : ENNReal)*count.descFactorial degree
theorem distinct_bucket_cross_moment {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (first second : α) (hdistinct : first≠second) (steps : Nat) (a b : List Nat) :
    SphincsSecurity.Concrete.uniformWordAverage steps (fun word : List α =>
      envelope a (word.count first)*envelope b (word.count second)) =
      ∑ i ∈ Finset.range a.length, ∑ j ∈ Finset.range b.length,
        ((a.getD i 0 : ENNReal)*b.getD j 0)*
          ((steps.descFactorial (i+j) : ENNReal)*(Fintype.card α : ENNReal)⁻¹^(i+j)) := by
  simp only [envelope,Finset.sum_mul,Finset.mul_sum,
    SphincsSecurity.Concrete.uniformWordAverage_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun word : List α =>
      ((a.getD i 0 : ENNReal)*(word.count first).descFactorial i)*
        ((b.getD j 0 : ENNReal)*(word.count second).descFactorial j)) =
      (fun word : List α => ((a.getD i 0 : ENNReal)*b.getD j 0)*
        ((word.count first).descFactorial i*(word.count second).descFactorial j)) := by
    funext word;ring
  rw [he,SphincsSecurity.Concrete.uniformWordAverage_mul_left,
    SphincsSecurity.Concrete.uniformWordAverage_mixed_descFactorial first second hdistinct]
def natEnvelope (coefficients : List Nat) (count : Nat) : Nat :=
  ∑ degree ∈ Finset.range coefficients.length, coefficients.getD degree 0*count.descFactorial degree
noncomputable def factorialPolynomial (coefficients : List Nat) : Polynomial Int :=
  ∑ degree ∈ Finset.range coefficients.length,
    Polynomial.C (coefficients.getD degree 0 : Int)*descPochhammer Int degree
theorem envelope_cast (coefficients : List Nat) (count : Nat) :
    envelope coefficients count=(natEnvelope coefficients count : ENNReal) := by
  simp only [envelope,natEnvelope,Nat.cast_sum,Nat.cast_mul]
theorem factorialPolynomial_eval (coefficients : List Nat) (count : Nat) :
    (factorialPolynomial coefficients).eval (count : Int)=(natEnvelope coefficients count : Int) := by
  simp only [factorialPolynomial,natEnvelope,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,descPochhammer_eval_eq_descFactorial,Nat.cast_sum,Nat.cast_mul]
def fullCoefficients : List Nat := [0,6,54,27]
def squareCoefficients : List Nat := [0,36,7164,35154,33858,9477,729]
theorem full_envelope (count : Nat) :
    natEnvelope fullCoefficients count=(3*count).descFactorial 3 := by
  rw [three_openings_polynomial]
  norm_num [natEnvelope,fullCoefficients,Finset.sum_range_succ]
theorem square_polynomial :
    factorialPolynomial fullCoefficients^2=factorialPolynomial squareCoefficients := by
  norm_num [factorialPolynomial,fullCoefficients,squareCoefficients,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring
theorem full_square_envelope (count : Nat) :
    ((3*count).descFactorial 3 : ENNReal)^2=envelope squareCoefficients count := by
  have he := congrArg (fun p : Polynomial Int => p.eval (count : Int)) square_polynomial
  rw [Polynomial.eval_pow,factorialPolynomial_eval,factorialPolynomial_eval] at he
  have hn : (natEnvelope fullCoefficients count)^2=natEnvelope squareCoefficients count := by
    exact_mod_cast he
  rw [full_envelope] at hn
  rw [envelope_cast]
  exact_mod_cast hn
theorem envelope_thinning (p : ENNReal) (hp : p≤1) (steps : Nat) (coefficients : List Nat) :
    binomialAverage p steps (envelope coefficients) =
      ∑ degree ∈ Finset.range coefficients.length,
        (coefficients.getD degree 0 : ENNReal)*(steps.descFactorial degree : ENNReal)*p^degree := by
  change binomialAverage p steps (fun count => envelope coefficients count)=_
  simp only [envelope,SphincsSecurity.Concrete.binomialAverage_sum,
    binomialAverage_mul_left,binomialAverage_descFactorial hp,mul_assoc]
theorem same_bucket_second_moment (steps : Nat) :
    binomialAverage (1/16) steps (fun count => ((3*count).descFactorial 3 : ENNReal)^2) =
      ∑ degree ∈ Finset.range squareCoefficients.length,
        (squareCoefficients.getD degree 0 : ENNReal)*(steps.descFactorial degree : ENNReal)*(1/16)^degree := by
  simp_rw [full_square_envelope]
  exact envelope_thinning (1/16) (by norm_num) steps squareCoefficients
theorem different_bucket_second_moment (first second : Fin 16) (hne : first≠second) (steps : Nat) :
    SphincsSecurity.Concrete.uniformWordAverage steps (fun word : List (Fin 16) =>
      ((3*word.count first).descFactorial 3 : ENNReal)*
        (3*word.count second).descFactorial 3) =
      ∑ i ∈ Finset.range fullCoefficients.length, ∑ j ∈ Finset.range fullCoefficients.length,
        ((fullCoefficients.getD i 0 : ENNReal)*fullCoefficients.getD j 0)*
          ((steps.descFactorial (i+j) : ENNReal)*(1/16)^(i+j)) := by
  have he := distinct_bucket_cross_moment first second hne steps fullCoefficients fullCoefficients
  simpa only [envelope_cast,full_envelope,Fintype.card_fin,Nat.cast_ofNat,one_div] using he
open SphincsSecurity.Concrete (uniformWordAverage uniformWordAverage_sum uniformWordAverage_mul_left)
noncomputable def diagonalMoment (steps : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range squareCoefficients.length,
    (squareCoefficients.getD degree 0 : ENNReal)*(steps.descFactorial degree : ENNReal)*(1/16)^degree
noncomputable def crossMoment (steps : Nat) : ENNReal :=
  ∑ i ∈ Finset.range fullCoefficients.length, ∑ j ∈ Finset.range fullCoefficients.length,
    ((fullCoefficients.getD i 0 : ENNReal)*fullCoefficients.getD j 0)*
      ((steps.descFactorial (i+j) : ENNReal)*(1/16)^(i+j))
noncomputable def bucketMass (word : List (Fin 16)) (bucket : Fin 16) : ENNReal :=
  (3*word.count bucket).descFactorial 3
noncomputable def coordinateEnvelope (word : List (Fin 16)) : ENNReal :=
  (∑ bucket, bucketMass word bucket)/16
theorem bucket_pair_moment (steps : Nat) (a b : Fin 16) :
    uniformWordAverage steps (fun word => bucketMass word a*bucketMass word b)=
      if a=b then diagonalMoment steps else crossMoment steps := by
  classical
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl]
    simp only [bucketMass,← pow_two,uniformWordAverage]
    rw [SphincsSecurity.Concrete.expected_uniformProposalWord_count a steps
      (fun count => ((3*count).descFactorial 3 : ENNReal)^2)]
    simpa only [Fintype.card_fin,Nat.cast_ofNat,one_div,diagonalMoment] using same_bucket_second_moment steps
  · rw [if_neg hab]
    exact different_bucket_second_moment a b hab steps
theorem coordinate_second_moment (steps : Nat) :
    uniformWordAverage steps (fun word => coordinateEnvelope word^2)=
      (diagonalMoment steps+15*crossMoment steps)/16 := by
  classical
  have hpoint (word : List (Fin 16)) : coordinateEnvelope word^2=
      (16 : ENNReal)⁻¹^2*(∑ a : Fin 16, ∑ b : Fin 16, bucketMass word a*bucketMass word b) := by
    unfold coordinateEnvelope
    calc
      _ = (16 : ENNReal)⁻¹^2*((∑ a : Fin 16, bucketMass word a)*(∑ b : Fin 16, bucketMass word b)) := by
        rw [div_eq_mul_inv];ring
      _ = _ := by
        congr 1
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
  simp_rw [hpoint]
  rw [uniformWordAverage_mul_left]
  simp_rw [uniformWordAverage_sum,bucket_pair_moment]
  have hrow (a : Fin 16) :
      (∑ b : Fin 16, if a=b then diagonalMoment steps else crossMoment steps)=
        diagonalMoment steps+15*crossMoment steps := by
    rw [Finset.sum_ite]
    have hy : (Finset.univ.filter fun b : Fin 16 => a=b)={a} := by ext b;simp [eq_comm]
    have hn : (Finset.univ.filter fun b : Fin 16 => ¬a=b)=Finset.univ.erase a := by ext b;simp [eq_comm]
    rw [hy,hn,Finset.sum_singleton,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ a)]
    norm_num only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [hrow]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,div_eq_mul_inv,Nat.cast_ofNat]
  have he : (16 : ENNReal)⁻¹^2*16=16⁻¹ := by
    rw [pow_two,mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by finiteness),mul_one]
  rw [← mul_assoc,he]
  ring
open OracleComp.EvalDist
noncomputable def finiteAverage {α : Type} [Fintype α] (f : α → ENNReal) : ENNReal :=
  (∑ x, f x)/(Fintype.card α : ENNReal)
theorem expected_uniform_eq_finiteAverage {α : Type} [Fintype α] [SampleableType α]
    (f : α → ENNReal) : expectedValue ($ᵗ α : ProbComp α) f=finiteAverage f := by
  simp only [expectedValue_def,probOutput_uniformSample,tsum_fintype,finiteAverage,
    div_eq_mul_inv,← Finset.mul_sum]
  exact mul_comm _ _
theorem finiteAverage_product {α : Type} [Fintype α] (d : Nat) (f : Fin d → α → ENNReal) :
    finiteAverage (fun x : Fin d → α => ∏ i, f i (x i))=∏ i, finiteAverage (f i) := by
  simp only [finiteAverage,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,div_eq_mul_inv,
    ENNReal.inv_pow,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Fintype.prod_sum]
theorem uniform_coordinate_product (steps : Nat) (f : Fin 7 → (Fin steps → Fin 16) → ENNReal) :
    expectedValue ($ᵗ (Fin 7 → (Fin steps → Fin 16)) : ProbComp _)
      (fun table => ∏ c, f c (table c))=
      ∏ c, expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _) (f c) := by
  simp_rw [expected_uniform_eq_finiteAverage]
  exact finiteAverage_product 7 f
theorem finiteAverage_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ENNReal) :
    finiteAverage (fun x => f (e x))=finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.card_congr e,Equiv.sum_comp]
theorem finiteAverage_pair {α β : Type} [Fintype α] [Fintype β] (f : α × β → ENNReal) :
    finiteAverage f=finiteAverage (fun a => finiteAverage (fun b => f (a,b))) := by
  simp only [finiteAverage,Fintype.card_prod,Nat.cast_mul,div_eq_mul_inv,Fintype.sum_prod_type]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [Finset.sum_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring
open SphincsSecurity.Concrete (uniformWordAverage sampleUniformProposalWord)
theorem uniformWordAverage_succ {α : Type} [Fintype α] [SampleableType α]
    (steps : Nat) (f : List α → ENNReal) :
    uniformWordAverage (steps+1) f =
      finiteAverage (fun a => uniformWordAverage steps (fun word => f (a::word))) := by
  change expectedValue (sampleUniformProposalWord α (steps+1)) f=_
  rw [sampleUniformProposalWord,expectedValue_bind]
  simp_rw [expectedValue_bind,expectedValue_pure]
  exact expected_uniform_eq_finiteAverage _
theorem word_array_average {α : Type} [Fintype α] [SampleableType α]
    (steps : Nat) (f : List α → ENNReal) :
    uniformWordAverage steps f=finiteAverage (fun word : Fin steps → α => f (List.ofFn word)) := by
  classical
  induction steps generalizing f with
  | zero =>
      simp [uniformWordAverage,sampleUniformProposalWord,finiteAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ]
      simp_rw [ih]
      rw [← finiteAverage_equiv (Fin.consEquiv (fun _ : Fin (steps+1) => α))]
      rw [finiteAverage_pair]
      congr 1
      funext a
      congr 1
      funext word
      simp [Fin.consEquiv,List.ofFn_succ]
theorem seven_coordinate_second_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → (Fin steps → Fin 16)) : ProbComp _)
      (fun table => (∏ c, coordinateEnvelope (List.ofFn (table c)))^2)=
        ((diagonalMoment steps+15*crossMoment steps)/16)^7 := by
  simp_rw [← Finset.prod_pow]
  rw [uniform_coordinate_product steps (fun _ word => coordinateEnvelope (List.ofFn word)^2)]
  have hcolumn : expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _)
      (fun word => coordinateEnvelope (List.ofFn word)^2)=
        (diagonalMoment steps+15*crossMoment steps)/16 := by
    rw [expected_uniform_eq_finiteAverage,← word_array_average steps (fun word => coordinateEnvelope word^2)]
    exact coordinate_second_moment steps
  simp_rw [hcolumn]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
noncomputable def firstMoment (steps : Nat) : ENNReal :=
  6*(steps.descFactorial 1 : ENNReal)*(1/16)+
    54*(steps.descFactorial 2 : ENNReal)*(1/16)^2+
    27*(steps.descFactorial 3 : ENNReal)*(1/16)^3
theorem bucket_first_moment (steps : Nat) (bucket : Fin 16) :
    uniformWordAverage steps (fun word => bucketMass word bucket)=firstMoment steps := by
  unfold uniformWordAverage bucketMass
  rw [SphincsSecurity.Concrete.expected_uniformProposalWord_count bucket steps
    (fun count => ((3*count).descFactorial 3 : ENNReal))]
  simpa only [firstMoment,Fintype.card_fin,Nat.cast_ofNat,one_div] using
    bucket_thinning (1/16) (by norm_num) steps
theorem coordinate_first_moment (steps : Nat) :
    uniformWordAverage steps coordinateEnvelope=firstMoment steps := by
  change uniformWordAverage steps (fun word => coordinateEnvelope word)=_
  simp only [coordinateEnvelope,ENNReal.div_eq_inv_mul]
  rw [SphincsSecurity.Concrete.uniformWordAverage_mul_left]
  simp_rw [SphincsSecurity.Concrete.uniformWordAverage_sum,bucket_first_moment]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  rw [← mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by finiteness),one_mul]
theorem seven_coordinate_first_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → (Fin steps → Fin 16)) : ProbComp _)
      (fun table => ∏ c, coordinateEnvelope (List.ofFn (table c)))=firstMoment steps^7 := by
  rw [uniform_coordinate_product steps (fun _ word => coordinateEnvelope (List.ofFn word))]
  have hcolumn : expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _)
      (fun word => coordinateEnvelope (List.ofFn word))=firstMoment steps := by
    rw [expected_uniform_eq_finiteAverage,← word_array_average steps coordinateEnvelope]
    exact coordinate_first_moment steps
  simp_rw [hcolumn]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
end SigGolfResearch.Gate6.Moments
end
-- ==== merged from T3_Gate6_MomentNumeric ====
section

namespace SigGolfResearch.Gate6.Moments.Numeric
open OracleComp OracleSpec ENNReal
open scoped BigOperators
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
def childCoefficients : List Nat := [0,1536,864,27]
def childSquareCoefficients : List Nat := [0,37748736,504889344,0xaf4a000,21109248,851472,11664]
def nearChildCoefficients : List Nat := [0,96,9]
def meanCoeffs : List Nat := [0,0x4458000000000000000,0x18438e6e23060000000000,0x51e93f9a5d51993f39516c0,0x35d2708af7f6ff4e4a96e940,0xc3fcd9d6f66c079baeb62360,0x14659717f87175719f2b78ee0,0x12335cfa3d63e7d20ec035b50,0x99ed4fba2a30d20673cc0b50,0x338f31f1a931a77ab9250c20,0xb793d30e52a125609abe150,0x1c11d8f2e3500aa7da22bd0,0x30533154e101d2e1ac90d0,0x3b7fe86dd9e1dbc6e7a6e,0x34e35d15239cbac5fe72,0x2208db69296fb163b95,0xfc85f0972b74ee705,0x532fa173d477c373,0x12ea774bce2ae00,0x2d038ef351d5e,0x3eddb916ac7,0x26f7c52b3]
def varianceCoeffs : List Nat := [0,0x123ede400000000000000000000000000000000000000,0x227c35f84275e0aae180000000000000000000000000000000000,0x27542eb77a71e82e309700713d4e558a000000000000000000000000,0x207eeb8469a11b8dd8d2242f623535e7709f9a00000000000000000000,0x554954ec123155638f775b953db5c4abdad3880e2c23708400000000000,0x4dbf9873e281edc7dfd6a530a0321e6a5cd8450aa415f0f7c00000000000,0x20ab487d06a46d60f5a8c6cb03df9283fd471b625326ceda2800000000000,0x77a411b2767b27baea41436059fe631ac0ed06e122067bb60400000000000,0x10a1430e00d654a780de1834979c536c64d75e11bcc6fbb64d880000000000,0x1839814fe69bc0a8642fbfd9203a9c254b4a38de8073b6c8d6780000000000,0x186d044e9f00bcd0c9b724b82400a79be7bbf7e3e200f42404580000000000,0x11c6b293119158f796edeefa4ec8cc1386401f8e73c64cb20b400000000000,0x9a58a1049daaa4ac5497c847747b5dc8f37d11970e5a61380bd0000000000,0x4019671c8300534c2bf6ed08d7a1d2fb48729f2fc87027b171b0000000000,0x14cdf1e0a2bc6cb095cffbb76eee70ec13a07c6111739fd9e8a0000000000,0x55e7cd6f15a9cd8a1a071d809c2d0c30dc490e37b3940b317d0000000000,0x11e1d225c52b3e4ebc710795ba94db813ddfaf3df5b6c6e5a1c000000000,0x309db4eebb87a741bcee4030783c0b9044c3b1364a638c05e4000000000,0x6cfa1b32bf5080fd82d5263c9016fc99f778b347c16295dec000000000,0xcb1ce41373dbdda41629d98687387cd8489da5dd8a078978000000000,0x13cfd95686c3f97bf0f9af136eb52ac221d9918001096d86000000000,0x1a0ae70944e8432aec35c36bc0f837ce1444dd94d89f596000000000,0x1cf8c75ac4c13ee7c312d92e44f8c3b7111bda2baaed69000000000,0x1b61d9049cd250f673423e01b137e1178649231b978e5000000000,0x160d46c6d1039897a55547fd3e4934eb0db1653d2988d80000000,0xf2a011e2b45d03296db5ce4b0a087835fd1ec62c12280000000,0x8ea44ba526a42158c39773a3254133a4403e91d78480000000,0x47b9a88ab1be86b5d740b18c586ea8a372585c64000000000,0x1ed4e40fe09029ca73a8514bd43345a8785eac8790000000,0xb5023ff2d973832426c528b4e451cc3e348134f0000000,0x388c8d238702dbf4ac1045bbf49a1574b8c9fa0000000,0xefbd06156273b3ffde2d0798ea3e92c50df10000000,0x3595e195bbac23d0712fe7475bd9eb3587b0000000,0xa0788237df51f0064ad3fe01388850efd0000000,0x18e6f490fefdf369e5c70024300e61400000000,0x3294c68eb55b91de60e5ea22baa2a80000000,0x52839d2e1a5674e9d97eabbb56b20000000,0x69522efb931f62fe8e672df4a80000000,0x652c0e11a88068197280a0f20000000,0x44b20587131cf4ebc3f8070000000,0x1d5b5b4807add038b5eb0000000,0x5ee7e56e3721f29290000000]
def nearCoeffs : List Nat := [0,0x445800000000000000,0x10faced9e551000000000,0x2ccd148330ca1ce52fb640,0x183a3624ed10cc82ba249c0,0x4aa1c80383fec5e84b3f320,0x6ad17b90e445c20419dc9a0,0x52b3e819af70dfc34427290,0x262076fbe8c9f1a8e7fe850,0xb296555782b98be20c83f0,0x22b75122f67f7cbe7e8740,0x49f94728e86bf5dddf870,0x6e4f51ec1346e59a8ee0,0x74a328ecfd2b887282e,0x57ef380a207efd2e72,0x2f2657c7928cdb789,0x11c1570213f04701,0x491ba8924efe70,0xc3284df9687f,0x12f5a9991fb,0xcfd41b91]
theorem mean_polynomial : factorialPolynomial childCoefficients^7=factorialPolynomial meanCoeffs := by
  norm_num [factorialPolynomial,childCoefficients,meanCoeffs,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring
theorem variance_polynomial : factorialPolynomial childSquareCoefficients^7=factorialPolynomial varianceCoeffs := by
  norm_num [factorialPolynomial,childSquareCoefficients,varianceCoeffs,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring
theorem near_polynomial : factorialPolynomial childCoefficients^6*factorialPolynomial nearChildCoefficients=
    factorialPolynomial nearCoeffs := by
  norm_num [factorialPolynomial,childCoefficients,nearChildCoefficients,nearCoeffs,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring
theorem envelope_power {a b : List Nat} (power count : Nat)
    (h : factorialPolynomial a^power=factorialPolynomial b) :
    envelope a count^power=envelope b count := by
  have he := congrArg (fun p : Polynomial Int => p.eval (count : Int)) h
  rw [Polynomial.eval_pow,factorialPolynomial_eval,factorialPolynomial_eval] at he
  have hn : (natEnvelope a count)^power=natEnvelope b count := by exact_mod_cast he
  simp_rw [envelope_cast]
  exact_mod_cast hn
theorem mean_envelope_power (count : Nat) :
    envelope childCoefficients count^7=envelope meanCoeffs count :=
  envelope_power 7 count mean_polynomial
theorem variance_envelope_power (count : Nat) :
    envelope childSquareCoefficients count^7=envelope varianceCoeffs count :=
  envelope_power 7 count variance_polynomial
theorem firstMoment_coefficients (count : Nat) :
    firstMoment count=envelope childCoefficients count/2^12 := by
  unfold firstMoment envelope
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [childCoefficients,Finset.sum_range_succ]
  ring
theorem secondMoment_coefficients (count : Nat) :
    (diagonalMoment count+15*crossMoment count)/16=envelope childSquareCoefficients count/2^28 := by
  unfold diagonalMoment crossMoment envelope
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [fullCoefficients,squareCoefficients,childSquareCoefficients,Finset.sum_range_succ]
  ring
theorem firstMoment_power_coefficients (count : Nat) :
    firstMoment count^7=envelope meanCoeffs count/2^84 := by
  rw [firstMoment_coefficients,div_eq_mul_inv,mul_pow,mean_envelope_power,div_eq_mul_inv,
    ENNReal.inv_pow,ENNReal.inv_pow,← pow_mul]
theorem secondMoment_power_coefficients (count : Nat) :
    ((diagonalMoment count+15*crossMoment count)/16)^7=envelope varianceCoeffs count/2^196 := by
  rw [secondMoment_coefficients,div_eq_mul_inv,mul_pow,variance_envelope_power,div_eq_mul_inv,
    ENNReal.inv_pow,ENNReal.inv_pow,← pow_mul]
theorem binomial_envelope_le_poisson (p : ENNReal) (hp : p≤1) (trials : Nat) (a : List Nat) :
    SphincsSecurity.Concrete.binomialAverage p trials (envelope a) ≤
      ∑ degree ∈ Finset.range a.length, (a.getD degree 0 : ENNReal)*((trials : ENNReal)*p)^degree := by
  rw [envelope_thinning p hp]
  apply Finset.sum_le_sum
  intro degree _
  calc
    _ ≤ (a.getD degree 0 : ENNReal)*(trials : ENNReal)^degree*p^degree := by
      gcongr
      exact_mod_cast Nat.descFactorial_le_pow trials degree
    _ = _ := by rw [mul_pow,mul_assoc]
open OracleComp.EvalDist SphincsSecurity.Concrete
noncomputable def forestEnvelope {steps : Nat} (table : Fin 7 → Fin steps → Fin 16) : ENNReal :=
  (∏ c, coordinateEnvelope (List.ofFn (table c)))/2^150
theorem forest_first_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) forestEnvelope =
      envelope meanCoeffs steps/2^234 := by
  change expectedValue _ (fun table => forestEnvelope table)=_
  simp only [forestEnvelope,div_eq_mul_inv]
  rw [expectedValue_mul_const,seven_coordinate_first_moment,firstMoment_power_coefficients,
    div_eq_mul_inv,ENNReal.inv_pow,ENNReal.inv_pow,ENNReal.inv_pow,mul_assoc,← pow_add]
theorem forest_second_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _)
      (fun table => forestEnvelope table^2)=envelope varianceCoeffs steps/2^496 := by
  simp only [forestEnvelope,div_eq_mul_inv,mul_pow]
  rw [expectedValue_mul_const,seven_coordinate_second_moment,secondMoment_power_coefficients,
    div_eq_mul_inv,ENNReal.inv_pow,ENNReal.inv_pow,ENNReal.inv_pow,← pow_mul,mul_assoc,← pow_add]
noncomputable def poissonEnvelope (a : List Nat) (mean : ENNReal) : ENNReal :=
  ∑ degree ∈ Finset.range a.length, (a.getD degree 0 : ENNReal)*mean^degree
theorem forest_binomial_first_bound (p : ENNReal) (hp : p≤1) (trials : Nat) :
    binomialAverage p trials (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) forestEnvelope) ≤
        poissonEnvelope meanCoeffs ((trials : ENNReal)*p)/2^234 := by
  simp_rw [forest_first_moment,div_eq_mul_inv]
  rw [binomialAverage_mul_right]
  exact mul_le_mul' (binomial_envelope_le_poisson p hp trials meanCoeffs) le_rfl
theorem forest_binomial_second_bound (p : ENNReal) (hp : p≤1) (trials : Nat) :
    binomialAverage p trials (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _)
        (fun table => forestEnvelope table^2)) ≤
        poissonEnvelope varianceCoeffs ((trials : ENNReal)*p)/2^496 := by
  simp_rw [forest_second_moment,div_eq_mul_inv]
  rw [binomialAverage_mul_right]
  exact mul_le_mul' (binomial_envelope_le_poisson p hp trials varianceCoeffs) le_rfl
def proposalLength : Nat := 4303355904
theorem poisson_mean_bound :
    (2 : ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234 ≤ 37/64 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [meanCoeffs,proposalLength,Finset.sum_range_succ]
theorem poisson_excess_bound :
    (2 : ENNReal)^225*poissonEnvelope varianceCoeffs (proposalLength/2^31)/2^496 ≤ 18400/100000000 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [varianceCoeffs,proposalLength,Finset.sum_range_succ]
theorem poisson_near_bound :
    21*(2 : ENNReal)^128*poissonEnvelope nearCoeffs (proposalLength/2^31)/2^223 ≤ 404 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [nearCoeffs,proposalLength,Finset.sum_range_succ]
theorem poisson_near_tight_bound :
    21*(2 : ENNReal)^128*poissonEnvelope nearCoeffs (proposalLength/2^31)/2^223 ≤ 6463/16 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [nearCoeffs,proposalLength,Finset.sum_range_succ]
noncomputable def nearCoordinateEnvelope (word : List (Fin 16)) : ENNReal :=
  (∑ bucket : Fin 16, ((3*word.count bucket).descFactorial 2 : ENNReal))/16
theorem near_coordinate_first_moment (steps : Nat) :
    uniformWordAverage steps nearCoordinateEnvelope=envelope nearChildCoefficients steps/2^8 := by
  change uniformWordAverage steps (fun word => nearCoordinateEnvelope word)=_
  simp only [nearCoordinateEnvelope,ENNReal.div_eq_inv_mul]
  rw [uniformWordAverage_mul_left]
  simp_rw [uniformWordAverage_sum]
  have hb (bucket : Fin 16) : uniformWordAverage steps
      (fun word => ((3*word.count bucket).descFactorial 2 : ENNReal))=
      6*(steps.descFactorial 1 : ENNReal)*(1/16)+9*(steps.descFactorial 2 : ENNReal)*(1/16)^2 := by
    unfold uniformWordAverage
    rw [expected_uniformProposalWord_count bucket steps (fun count => ((3*count).descFactorial 2 : ENNReal))]
    simpa only [Fintype.card_fin,Nat.cast_ofNat,one_div] using
      near_bucket_thinning (1/16) (by norm_num) steps
  simp_rw [hb]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  rw [← mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by finiteness),one_mul]
  unfold envelope
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one,
    ENNReal.toReal_inv]
  norm_num [nearChildCoefficients,Finset.sum_range_succ]
  ring
noncomputable def nearForestEnvelope {steps : Nat} (missing : Fin 7)
    (table : Fin 7 → Fin steps → Fin 16) : ENNReal :=
  (∏ c, if c=missing then nearCoordinateEnvelope (List.ofFn (table c))
    else coordinateEnvelope (List.ofFn (table c)))/2^143
theorem near_envelope_product (count : Nat) :
    envelope childCoefficients count^6*envelope nearChildCoefficients count=envelope nearCoeffs count := by
  have he := congrArg (fun p : Polynomial Int => p.eval (count : Int)) near_polynomial
  rw [Polynomial.eval_mul,Polynomial.eval_pow,factorialPolynomial_eval,factorialPolynomial_eval,
    factorialPolynomial_eval] at he
  have hn : (natEnvelope childCoefficients count)^6*natEnvelope nearChildCoefficients count=
      natEnvelope nearCoeffs count := by exact_mod_cast he
  simp_rw [envelope_cast]
  exact_mod_cast hn
theorem near_forest_first_moment (steps : Nat) (missing : Fin 7) :
    expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)=
      envelope nearCoeffs steps/2^223 := by
  change expectedValue _ (fun table => nearForestEnvelope missing table)=_
  simp only [nearForestEnvelope,div_eq_mul_inv]
  rw [expectedValue_mul_const,uniform_coordinate_product steps (fun c word =>
    if c=missing then nearCoordinateEnvelope (List.ofFn word) else coordinateEnvelope (List.ofFn word))]
  have he (c : Fin 7) : expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _)
      (fun word => if c=missing then nearCoordinateEnvelope (List.ofFn word)
        else coordinateEnvelope (List.ofFn word)) =
      if c=missing then envelope nearChildCoefficients steps/2^8 else firstMoment steps := by
    by_cases h : c=missing
    · simp only [h,ite_true]
      rw [expected_uniform_eq_finiteAverage,← word_array_average steps nearCoordinateEnvelope,
        near_coordinate_first_moment]
    · simp only [h,ite_false]
      rw [expected_uniform_eq_finiteAverage,← word_array_average steps coordinateEnvelope,
        coordinate_first_moment]
  simp_rw [he]
  rw [Finset.prod_ite]
  have hy : (Finset.univ.filter fun c : Fin 7 => c=missing)={missing} := by ext c;simp
  have hn : (Finset.univ.filter fun c : Fin 7 => ¬c=missing)=Finset.univ.erase missing := by ext c;simp [eq_comm]
  rw [hy,hn,Finset.prod_singleton,Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ missing)]
  simp only [Finset.card_univ,Fintype.card_fin]
  rw [firstMoment_coefficients]
  simp only [div_eq_mul_inv,mul_pow,ENNReal.inv_pow,← pow_mul]
  calc
    _ = (envelope childCoefficients steps^6*envelope nearChildCoefficients steps)*
      ((2 : ENNReal)⁻¹^(12*6)*2⁻¹^8*2⁻¹^143) := by ring
    _ = _ := by rw [near_envelope_product,← pow_add,← pow_add]
theorem near_forest_binomial_bound (p : ENNReal) (hp : p≤1) (trials : Nat) (missing : Fin 7) :
    binomialAverage p trials (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)) ≤
        poissonEnvelope nearCoeffs ((trials : ENNReal)*p)/2^223 := by
  simp_rw [near_forest_first_moment,div_eq_mul_inv]
  rw [binomialAverage_mul_right]
  exact mul_le_mul' (binomial_envelope_le_poisson p hp trials nearCoeffs) le_rfl
theorem uniform_history_mean_bound :
    (2 : ENNReal)^128*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) forestEnvelope) ≤ 37/64 := by
  calc
    _ ≤ (2 : ENNReal)^128*(poissonEnvelope meanCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^234) :=
      mul_le_mul' le_rfl (forest_binomial_first_bound (1/2^31) (by norm_num) proposalLength)
    _ = (2 : ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234 := by
      simp only [div_eq_mul_inv,mul_one,one_mul,mul_assoc]
    _ ≤ _ := poisson_mean_bound
theorem uniform_history_excess_bound :
    (2 : ENNReal)^225*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (fun table => forestEnvelope table^2)) ≤
        18400/100000000 := by
  calc
    _ ≤ (2 : ENNReal)^225*(poissonEnvelope varianceCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^496) :=
      mul_le_mul' le_rfl (forest_binomial_second_bound (1/2^31) (by norm_num) proposalLength)
    _ = (2 : ENNReal)^225*poissonEnvelope varianceCoeffs (proposalLength/2^31)/2^496 := by
      simp only [div_eq_mul_inv,mul_one,one_mul,mul_assoc]
    _ ≤ _ := poisson_excess_bound
theorem uniform_history_near_bound (missing : Fin 7) :
    21*(2 : ENNReal)^128*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)) ≤ 404 := by
  calc
    _ ≤ 21*(2 : ENNReal)^128*(poissonEnvelope nearCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^223) :=
      mul_le_mul' le_rfl (near_forest_binomial_bound (1/2^31) (by norm_num) proposalLength missing)
    _ = 21*(2 : ENNReal)^128*poissonEnvelope nearCoeffs (proposalLength/2^31)/2^223 := by
      simp only [div_eq_mul_inv,mul_one,one_mul,mul_assoc]
    _ ≤ _ := poisson_near_bound
end SigGolfResearch.Gate6.Moments.Numeric
end
-- ==== merged from T3_Gate6_Coverage ====
section

namespace SigGolfResearch.Gate6
open OracleComp ENNReal Finset
open Moments
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
abbrev CoordinateDraw := Bank → Bucket × Triple
abbrev GatedDraw := CoordinateDraw × Padding
def rawDraw (raw : RawRecord) : GatedDraw :=
  ((fun c => (raw.1.2 c,raw.2.1 c)),raw.2.2.1)
noncomputable def rawEventEquiv (event : GatedDraw → Prop) :
    {raw : RawRecord // event (rawDraw raw)} ≃
      Address × ({draw : GatedDraw // event draw} × Unused) where
  toFun r := (r.1.1.1,(⟨rawDraw r.1,r.2⟩,r.1.2.2.2))
  invFun r := ⟨((r.1,fun c => (r.2.1.1.1 c).1),
    (fun c => (r.2.1.1.1 c).2,(r.2.1.1.2,r.2.2))),r.2.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem gatedDraw_card : Fintype.card GatedDraw=2^178 := by
  norm_num [GatedDraw,CoordinateDraw,Bank,Bucket,Triple,Padding,
    Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
theorem raw_draw_event (event : GatedDraw → Prop) :
    Pr[fun raw => event (rawDraw raw) | ($ᵗ RawRecord : ProbComp RawRecord)] =
      Pr[event | ($ᵗ GatedDraw : ProbComp GatedDraw)] := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (rawEventEquiv event),
    Fintype.card_prod,Fintype.card_prod,rawRecord_card,
    probEvent_uniformSample,←Fintype.card_subtype,gatedDraw_card]
  simp only [Address,Unused,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num
  ring
def CoordinateCovered (exposed : Bank → Bucket → Finset (Fin 128))
    (draw : CoordinateDraw) : Prop := ∀ c, Covered (exposed c (draw c).1) (draw c).2
def GatedCovered (exposed : Bank → Bucket → Finset (Fin 128)) (draw : GatedDraw) : Prop :=
  draw.2=0 ∧ CoordinateCovered exposed draw.1
noncomputable def gatedCoveredEquiv (exposed : Bank → Bucket → Finset (Fin 128)) :
    {draw : GatedDraw // GatedCovered exposed draw} ≃
      {draw : CoordinateDraw // CoordinateCovered exposed draw} where
  toFun d := ⟨d.1.1,d.2.2⟩
  invFun d := ⟨(d.1,0),rfl,d.2⟩
  left_inv d := by apply Subtype.ext;exact Prod.ext rfl d.2.1.symm
  right_inv _ := rfl
theorem gated_covered_probability (exposed : Bank → Bucket → Finset (Fin 128)) :
    Pr[GatedCovered exposed | ($ᵗ GatedDraw : ProbComp GatedDraw)] =
      (Pr[CoordinateCovered exposed | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/8 := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (gatedCoveredEquiv exposed),
    probEvent_uniformSample,←Fintype.card_subtype]
  simp only [GatedDraw,Fintype.card_prod,Padding,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_ofNat]
  rw [div_div]
theorem digest_gate_covered_probability (exposed : Bank → Bucket → Finset (Fin 128)) :
    Pr[fun output => GatedCovered exposed (rawDraw (digestRecord output)) |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (∏ c : Bank, ((∑ b : Bucket, ((exposed c b).card.descFactorial 3 : ENNReal))/(16*128^3)))/8 := by
  rw [digest_event (fun raw => GatedCovered exposed (rawDraw raw)),raw_draw_event,
    gated_covered_probability]
  exact congrArg (fun p : ENNReal => p/8) (bpors_covered_probability exposed)
theorem accepted_covered_le_gate (exposed : Bank → Bucket → Finset (Fin 128)) :
    Pr[fun output => DigestAccepted output ∧
      CoordinateCovered exposed (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤
    Pr[fun output => GatedCovered exposed (rawDraw (digestRecord output)) |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
  apply probEvent_mono
  intro output _ h
  exact ⟨h.1.1,h.2⟩
theorem accepted_covered_le_forestEnvelope {steps : Nat}
    (table : Fin 7 → Fin steps → Fin 16) (exposed : Bank → Bucket → Finset (Fin 128))
    (hsize : ∀ c bucket, (exposed c bucket).card ≤ 3*(List.ofFn (table c)).count bucket) :
    Pr[fun output => DigestAccepted output ∧
      CoordinateCovered exposed (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤ Moments.Numeric.forestEnvelope table := by
  refine (accepted_covered_le_gate exposed).trans ?_
  rw [digest_gate_covered_probability]
  have he : (∏ c : Bank,
      ((∑ bucket : Bucket, ((3*(List.ofFn (table c)).count bucket).descFactorial 3 : ENNReal))/(16*128^3)))/8 =
      Moments.Numeric.forestEnvelope table := by
    simp only [Moments.Numeric.forestEnvelope,coordinateEnvelope,bucketMass,div_eq_mul_inv,
      Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Bank,Fintype.card_fin]
    rw [mul_assoc,mul_assoc]
    congr 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_mul]
  rw [←he]
  apply ENNReal.div_le_div_right
  gcongr with c hc bucket hb
  exact hsize c bucket
end SigGolfResearch.Gate6
end
-- ==== merged from T3_Gate6_BPORSPrefix ====
section

section

namespace SigGolfResearch.Gate6.Excess
open ENNReal
theorem theta_excess_le_square (v m : ENNReal) (hv : v ≠ ⊤) (hm : m ≤ 37/64) :
    (13/8)*(v-63/64)+2*m*v ≤ v^2+m^2 := by
  have hmf : m ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hm
  have hmr : m.toReal ≤ 37/64 := by
    have h := (ENNReal.toReal_le_toReal hmf (by finiteness)).mpr hm
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h
  by_cases hsmall : v ≤ 63/64
  · rw [tsub_eq_zero_of_le hsmall,mul_zero,zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_add,ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (v.toReal-m.toReal)]
  · have hlarge : 63/64 ≤ v := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hv,ENNReal.toReal_div,ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (v.toReal-m.toReal-13/16)]
end SigGolfResearch.Gate6.Excess
end

section





section
namespace SigGolfResearch.Gate6.Source
open SigGolfCandidate.T3 OracleComp ENNReal OracleComp.EvalDist Finset
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 1000000
theorem actual_accepted_mark_weight (payoff : MarkedLabel → ENNReal) :
    expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      (fun output => if digestAdmissible output then payoff (digestRecord output).1 else 0)=
        Moments.finiteAverage payoff*acceptance := by
  have hs (output : BitVec 256) :
      (if digestAdmissible output then payoff (digestRecord output).1 else 0)=
        ∑ mark : MarkedLabel,
          (if digestAdmissible output=true ∧ (digestRecord output).1=mark then 1 else 0)*payoff mark := by
    by_cases ha : digestAdmissible output=true
    · simp [ha,eq_comm]
    · simp [ha]
  simp only [expectedValue_def]
  simp_rw [hs,Finset.mul_sum,←mul_assoc,mul_ite,mul_one,mul_zero]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [ENNReal.tsum_mul_right,←probEvent_eq_tsum_ite,actual_mark_joint_exact]
  simp only [Moments.finiteAverage,markedLabel_card,Nat.cast_pow,Nat.cast_ofNat,
    div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mark _
  ring
end SigGolfResearch.Gate6.Source
end
section
namespace SigGolfCandidate.T3.DigestSampling
open OracleComp OracleSpec ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
abbrev RawView := Fin (2^31) × (Fin 7 → Fin 16 × (Fin 3 → Fin 128))
abbrev Coordinates := RawView × BitVec 50
def rawView (output : HashOutput) : RawView :=
  ((output.extractLsb' 0 31).toFin, fun c =>
    ((output.extractLsb' (31+25*c.val) 4).toFin,
      fun j => (output.extractLsb' (31+25*c.val+4+7*j.val) 7).toFin))
def coordinates (output : HashOutput) : Coordinates :=
  (rawView output,output.extractLsb' 206 50)
theorem coordinates_injective : Function.Injective coordinates := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hindex : position<31
  · have hc := congrArg (fun x : Coordinates => BitVec.ofFin x.1.1) heq
    change left.extractLsb' 0 31=right.extractLsb' 0 31 at hc
    have hb := congrArg (fun bits : BitVec 31 => bits.getLsbD position) hc
    simpa only [BitVec.getLsbD_extractLsb',hindex,decide_true,Bool.true_and,Nat.zero_add] using hb
  · by_cases hslots : position<206
    · let c : Fin 7 := ⟨(position-31)/25,by omega⟩
      let within := (position-31)%25
      have hwithin : within<25 := by dsimp [within];omega
      have hoff : 31+25*c.val+within=position := by dsimp [c,within];omega
      by_cases hbucket : within<4
      · have hc := congrArg (fun x : Coordinates => (BitVec.ofFin (x.1.2 c).1 : BitVec 4)) heq
        change left.extractLsb' (31+25*c.val) 4=right.extractLsb' (31+25*c.val) 4 at hc
        have hb := congrArg (fun bits : BitVec 4 => bits.getLsbD within) hc
        simpa only [BitVec.getLsbD_extractLsb',hbucket,decide_true,Bool.true_and,hoff] using hb
      · let j : Fin 3 := ⟨(within-4)/7,by omega⟩
        let bit := (within-4)%7
        have hbit : bit<7 := by dsimp [bit];omega
        have hoff' : 31+25*c.val+4+7*j.val+bit=position := by dsimp [j,bit];omega
        have hc := congrArg (fun x : Coordinates => (BitVec.ofFin ((x.1.2 c).2 j) : BitVec 7)) heq
        change left.extractLsb' (31+25*c.val+4+7*j.val) 7=
          right.extractLsb' (31+25*c.val+4+7*j.val) 7 at hc
        have hb := congrArg (fun bits : BitVec 7 => bits.getLsbD bit) hc
        simpa only [BitVec.getLsbD_extractLsb',hbit,decide_true,Bool.true_and,hoff'] using hb
    · have hc := congrArg Prod.snd heq
      change left.extractLsb' 206 50=right.extractLsb' 206 50 at hc
      have hb := congrArg (fun bits : BitVec 50 => bits.getLsbD (position-206)) hc
      have hbit : position-206<50 := by omega
      have hoff : 206+(position-206)=position := by omega
      simpa only [BitVec.getLsbD_extractLsb',hbit,decide_true,Bool.true_and,hoff] using hb
theorem coordinates_bijective : Function.Bijective coordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨coordinates_injective,?_⟩
  simp only [Coordinates,RawView,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bitVec]
  rfl
noncomputable def coordinatesEquiv : HashOutput ≃ Coordinates :=
  Equiv.ofBijective coordinates coordinates_bijective
theorem uniform_coordinates :
    𝒮[coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)]=
      𝒮[($ᵗ Coordinates : ProbComp Coordinates)] :=
  evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := Coordinates) coordinates coordinates_bijective
def rawSelections (view : RawView) : List Selection :=
  List.ofFn fun c : Fin 7 =>
    ⟨(view.2 c).1.val,(List.ofFn fun j : Fin 3 => ((view.2 c).2 j).val).mergeSort (· ≤ ·)⟩
theorem rawView_index (output : HashOutput) : (rawView output).1.val=output.toNat%2^31 := by
  simp [rawView,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem rawView_bucket (output : HashOutput) (c : Fin 7) :
    ((rawView output).2 c).1.val=output.toNat/2^(31+25*c.val)%16 := by
  simp [rawView,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem rawView_leaf (output : HashOutput) (c : Fin 7) (j : Fin 3) :
    (((rawView output).2 c).2 j).val=output.toNat/2^(31+25*c.val)/2^(4+7*j.val)%128 := by
  simp only [rawView,BitVec.val_toFin,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul,← Nat.pow_add]
  congr 3
  omega
theorem rawSelections_eq_selections (output : HashOutput) :
    rawSelections (rawView output)=selections output := by
  apply List.ext_getElem
  · simp [rawSelections,selections]
  · intro c hc hc'
    simp only [rawSelections,List.getElem_ofFn,selections,List.getElem_map,List.getElem_range]
    congr 1
    · exact rawView_bucket output ⟨c,by simpa [rawSelections] using hc⟩
    · congr 1
      apply List.ext_getElem
      · simp
      · intro j hj hj'
        simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
        exact rawView_leaf output ⟨c,by simpa [rawSelections] using hc⟩ ⟨j,by simpa using hj⟩
abbrev LeafChoices := Fin 7 → Fin 3 → Fin 128
def leafSelections (leaves : LeafChoices) : List Selection :=
  List.ofFn fun c : Fin 7 =>
    ⟨0,(List.ofFn fun j : Fin 3 => (leaves c j).val).mergeSort (· ≤ ·)⟩
def leafAdmissible (leaves : LeafChoices) : Bool := admissible (leafSelections leaves)
theorem raw_admissible (view : RawView) :
    admissible (rawSelections view)=leafAdmissible (fun c => (view.2 c).2) := by
  simpa only [rawSelections,leafAdmissible,leafSelections,List.map_ofFn,Function.comp_def] using
    (admissible_bucket_map (rawSelections view) (fun _ => 0)).symm
theorem source_admissible (output : HashOutput) :
    admissible (selections output)=leafAdmissible (fun c => ((rawView output).2 c).2) := by
  rw [← rawSelections_eq_selections]
  exact raw_admissible _
end SigGolfCandidate.T3.DigestSampling
namespace SigGolfCandidate.T3.DigestSampling
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfResearch.Gate6.Moments
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
abbrev IndexBuckets := Fin (2^31) × (Fin 7 → Fin 16)
abbrev SamplingData := IndexBuckets × LeafChoices
def regroup : Coordinates ≃ SamplingData × BitVec 50 where
  toFun x := (((x.1.1,fun c => (x.1.2 c).1),fun c => (x.1.2 c).2),x.2)
  invFun x := ((x.1.1.1,fun c => (x.1.1.2 c,x.1.2 c)),x.2)
  left_inv x := by rcases x with ⟨⟨idx,columns⟩,unused⟩;rfl
  right_inv x := by rcases x with ⟨⟨⟨idx,buckets⟩,leaves⟩,unused⟩;rfl
def samplingData (output : HashOutput) : SamplingData := (regroup (coordinates output)).1
theorem uniform_samplingData :
    𝒮[samplingData <$> ($ᵗ HashOutput : ProbComp HashOutput)]=
      𝒮[($ᵗ SamplingData : ProbComp SamplingData)] := by
  have hwhole : 𝒮[(fun output => regroup (coordinates output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)]=
      𝒮[($ᵗ (SamplingData × BitVec 50) : ProbComp _)] :=
    evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := SamplingData × BitVec 50)
      _ (regroup.bijective.comp coordinates_bijective)
  change 𝒮[(fun output => (regroup (coordinates output)).1) <$> ($ᵗ HashOutput : ProbComp _)]=_
  rw [show (fun output => (regroup (coordinates output)).1) <$> ($ᵗ HashOutput : ProbComp _)=
    Prod.fst <$> ((fun output => regroup (coordinates output)) <$> ($ᵗ HashOutput : ProbComp _)) by
      simp only [Functor.map_map,Function.comp_def]]
  rw [evalSPMF_map,hwhole,← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod
theorem samplingData_expectedValue (payoff : SamplingData → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output => payoff (samplingData output))=
      expectedValue ($ᵗ SamplingData : ProbComp SamplingData) payoff := by
  rw [← expectedValue_map]
  unfold expectedValue probOutput
  rw [uniform_samplingData]
theorem finiteAverage_mul_const {α : Type} [Fintype α] (f : α → ENNReal) (c : ENNReal) :
    finiteAverage (fun x => f x*c)=finiteAverage f*c := by
  simp only [finiteAverage,Finset.sum_mul,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro x _
  ring
theorem finiteAverage_const_mul {α : Type} [Fintype α] (c : ENNReal) (f : α → ENNReal) :
    finiteAverage (fun x => c*f x)=c*finiteAverage f := by
  simpa only [mul_comm] using finiteAverage_mul_const f c
theorem finiteAverage_pair_product {α β : Type} [Fintype α] [Fintype β]
    (f : α → ENNReal) (g : β → ENNReal) :
    finiteAverage (fun pair : α × β => f pair.1*g pair.2)=finiteAverage f*finiteAverage g := by
  rw [finiteAverage_pair]
  simp_rw [finiteAverage_const_mul,finiteAverage_mul_const]
noncomputable def acceptanceProbability : ENNReal := SigGolfResearch.Gate6.acceptance
theorem samplingData_mark (output : HashOutput) :
    (samplingData output).1=(SigGolfResearch.Gate6.digestRecord output).1 := rfl
theorem accepted_samplingData (payoff : IndexBuckets → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => if digestAdmissible output then payoff (samplingData output).1 else 0)=
        finiteAverage payoff*acceptanceProbability := by
  simp only [samplingData_mark,acceptanceProbability]
  exact SigGolfResearch.Gate6.Source.actual_accepted_mark_weight payoff
theorem fresh_digest_coordinates {Result : Type} (input : SphincsSecurity.HashInput)
    (cache : QueryCache SphincsSecurity.HashSpec) (hcache : cache input=none)
    (continuation : SphincsSecurity.HashOutput × QueryCache SphincsSecurity.HashSpec → ProbComp Result) :
    𝒮[(randomOracle input).run cache >>= continuation]=
      𝒮[($ᵗ Coordinates : ProbComp Coordinates) >>= fun pieces =>
        let output := coordinatesEquiv.symm pieces
        continuation (output,cache.cacheQuery input output)] := by
  rw [OracleSpec.randomOracle,QueryImpl.withCaching_run_none _ hcache]
  change 𝒮[((fun output : HashOutput => (output,cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation]=_
  have hcomp : ((fun output : HashOutput => (output,cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation=
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output => continuation (output,cache.cacheQuery input output) := by
    rw [map_eq_bind_pure_comp,LawfulMonad.bind_assoc]
    simp only [Function.comp_def,LawfulMonad.pure_bind,Equiv.symm_apply_apply]
  rw [hcomp]
  have hback : (coordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)) >>=
      (fun pieces => continuation (coordinatesEquiv.symm pieces,cache.cacheQuery input (coordinatesEquiv.symm pieces)))=
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output => continuation (output,cache.cacheQuery input output) := by
    rw [map_eq_bind_pure_comp,LawfulMonad.bind_assoc]
    simp only [Function.comp_def,LawfulMonad.pure_bind,Equiv.symm_apply_apply]
  rw [← hback,evalSPMF_bind]
  change (𝒮[coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] >>= _)=_
  rw [uniform_coordinates,← evalSPMF_bind]
theorem digest_trial_inputs_injective (rho : Digest) (message : Message) (start fuel : Nat)
    (hlimit : start+fuel≤2^32) :
    Function.Injective (fun trial : Fin fuel => digestInput rho message (BitVec.ofNat 32 (start+trial.val))) := by
  intro i j he
  have hc := (digestInput_injective he).2.2
  have hi : start+i.val<2^32 := by omega
  have hj : start+j.val<2^32 := by omega
  have hn := congrArg BitVec.toNat hc
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at hn
  exact Fin.ext (by omega)
end SigGolfCandidate.T3.DigestSampling
end
section
namespace SigGolfCandidate.T3.BPORS
export SigGolfResearch.Gate6.Moments (Covered coveredEquiv covered_count covered_probability covered_probability_le covered_product_count three_openings_polynomial two_openings_polynomial bucket_thinning near_bucket_thinning bucketCoveredEquiv bucket_covered_count bucket_covered_probability bucket_product_count bpors_covered_probability envelope distinct_bucket_cross_moment natEnvelope factorialPolynomial envelope_cast factorialPolynomial_eval fullCoefficients squareCoefficients full_envelope square_polynomial full_square_envelope envelope_thinning same_bucket_second_moment different_bucket_second_moment diagonalMoment crossMoment bucketMass coordinateEnvelope bucket_pair_moment coordinate_second_moment finiteAverage expected_uniform_eq_finiteAverage finiteAverage_product uniform_coordinate_product finiteAverage_equiv finiteAverage_pair uniformWordAverage_succ word_array_average seven_coordinate_second_moment firstMoment bucket_first_moment coordinate_first_moment seven_coordinate_first_moment)
namespace Numeric
export SigGolfResearch.Gate6.Moments.Numeric (childCoefficients childSquareCoefficients nearChildCoefficients meanCoeffs varianceCoeffs nearCoeffs mean_polynomial variance_polynomial near_polynomial envelope_power mean_envelope_power variance_envelope_power firstMoment_coefficients secondMoment_coefficients firstMoment_power_coefficients secondMoment_power_coefficients binomial_envelope_le_poisson forestEnvelope forest_first_moment forest_second_moment poissonEnvelope forest_binomial_first_bound forest_binomial_second_bound proposalLength poisson_mean_bound poisson_excess_bound poisson_near_bound poisson_near_tight_bound nearCoordinateEnvelope near_coordinate_first_moment nearForestEnvelope near_envelope_product near_forest_first_moment near_forest_binomial_bound uniform_history_mean_bound uniform_history_excess_bound uniform_history_near_bound)
end Numeric
end SigGolfCandidate.T3.BPORS
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SphincsSecurity.Concrete
open SigGolfCandidate.T3.DigestSampling
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
noncomputable def atIndex {α β : Type} [DecidableEq α] (index : α) (word : List (α × β)) : List β :=
  word.filterMap fun pair => if pair.1=index then some pair.2 else none
theorem atIndex_cons {α β : Type} [DecidableEq α] (index : α) (next : α × β) (word : List (α × β)) :
    atIndex index (next::word)=if next.1=index then next.2::atIndex index word else atIndex index word := by
  unfold atIndex
  split <;> simp_all
theorem finiteAverage_constant {α : Type} [Fintype α] [SampleableType α] (value : ENNReal) :
    finiteAverage (fun _ : α => value)=value := by
  rw [← expected_uniform_eq_finiteAverage]
  exact expectedValue_const (by simp) value
theorem average_binomial_commute {β : Type} [Fintype β]
    (p : ENNReal) (steps : Nat) (f : β → Nat → ENNReal) :
    finiteAverage (fun value => binomialAverage p steps (f value))=
      binomialAverage p steps (fun count => finiteAverage (fun value => f value count)) := by
  unfold finiteAverage
  simp only [div_eq_mul_inv]
  rw [binomialAverage_mul_right,binomialAverage_sum]
theorem finiteAverage_choice {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (index : α) (hit miss : ENNReal) :
    finiteAverage (fun next => if next=index then hit else miss)=
      (1-(Fintype.card α : ENNReal)⁻¹)*miss+(Fintype.card α : ENNReal)⁻¹*hit := by
  rw [← expected_uniform_eq_finiteAverage]
  exact expected_uniformSample_choice index hit miss
theorem uniform_marked_word_atIndex {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (index : α) (steps : Nat) (payoff : List β → ENNReal) :
    uniformWordAverage steps (fun word : List (α × β) => payoff (atIndex index word))=
      binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => uniformWordAverage count payoff) := by
  induction steps generalizing payoff with
  | zero => simp [uniformWordAverage,sampleUniformProposalWord,atIndex,binomialAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ,finiteAverage_pair]
      have hm (next : α) :
          finiteAverage (fun mark : β => uniformWordAverage steps
            (fun word : List (α × β) => payoff (atIndex index ((next,mark)::word))))=
          if next=index then
            binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => uniformWordAverage (count+1) payoff)
          else binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => uniformWordAverage count payoff) := by
        by_cases h : next=index
        · simp only [atIndex_cons,h,ite_true]
          have hmark (mark : β) : uniformWordAverage steps
              (fun word => payoff (mark::atIndex index word))=
              binomialAverage (Fintype.card α : ENNReal)⁻¹ steps
                (fun count => uniformWordAverage count (fun word => payoff (mark::word))) :=
            ih (fun word => payoff (mark::word))
          simp_rw [hmark]
          rw [average_binomial_commute]
          simp_rw [← uniformWordAverage_succ]
        · simp only [atIndex_cons,h,ite_false]
          rw [ih,finiteAverage_constant]
      simp_rw [hm]
      rw [finiteAverage_choice]
      rfl
abbrev Buckets := Fin 7 → Fin 16
noncomputable def wordEnvelope (word : List Buckets) : ENNReal :=
  (∏ c, coordinateEnvelope (word.map fun row => row c))/2^150
theorem word_forest_moment (steps power : Nat) :
    uniformWordAverage steps (fun word => wordEnvelope word^power)=
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _)
        (fun table => Numeric.forestEnvelope table^power) := by
  rw [word_array_average,expected_uniform_eq_finiteAverage]
  rw [← finiteAverage_equiv (Equiv.piComm (fun (_ : Fin 7) (_ : Fin steps) => Fin 16))]
  congr 1
  funext table
  simp only [wordEnvelope,Numeric.forestEnvelope,List.map_ofFn,Function.comp_def,Equiv.piComm_apply]
theorem uniform_proposal_forest_moment (index : Fin (2^31)) (steps power : Nat) :
    uniformWordAverage steps
      (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex index word)^power)=
      binomialAverage (1/2^31) steps (fun count =>
        expectedValue ($ᵗ (Fin 7 → Fin count → Fin 16) : ProbComp _) (fun table => Numeric.forestEnvelope table^power)) := by
  rw [uniform_marked_word_atIndex index steps (fun word => wordEnvelope word^power)]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,one_div]
  simp_rw [word_forest_moment]
theorem uniform_proposal_mean_bound (index : Fin (2^31)) :
    (2 : ENNReal)^128*uniformWordAverage Numeric.proposalLength
      (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex index word)) ≤ 37/64 := by
  have h := uniform_proposal_forest_moment index Numeric.proposalLength 1
  simp only [pow_one] at h
  rw [h]
  exact Numeric.uniform_history_mean_bound
theorem uniform_proposal_excess_bound (index : Fin (2^31)) :
    (2 : ENNReal)^225*uniformWordAverage Numeric.proposalLength
      (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex index word)^2) ≤ 18400/100000000 := by
  rw [uniform_proposal_forest_moment]
  exact Numeric.uniform_history_excess_bound
noncomputable def nearWordEnvelope (missing : Fin 7) (word : List Buckets) : ENNReal :=
  (∏ c, if c=missing then Numeric.nearCoordinateEnvelope (word.map fun row => row c)
    else coordinateEnvelope (word.map fun row => row c))/2^143
theorem word_near_forest_moment (steps : Nat) (missing : Fin 7) :
    uniformWordAverage steps (nearWordEnvelope missing)=
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (Numeric.nearForestEnvelope missing) := by
  rw [word_array_average,expected_uniform_eq_finiteAverage]
  rw [← finiteAverage_equiv (Equiv.piComm (fun (_ : Fin 7) (_ : Fin steps) => Fin 16))]
  congr 1
  funext table
  simp only [nearWordEnvelope,Numeric.nearForestEnvelope,List.map_ofFn,Function.comp_def,Equiv.piComm_apply]
theorem uniform_proposal_near_bound (index : Fin (2^31)) (missing : Fin 7) :
    21*(2 : ENNReal)^128*uniformWordAverage Numeric.proposalLength
      (fun word : List (Fin (2^31) × Buckets) => nearWordEnvelope missing (atIndex index word)) ≤ 404 := by
  rw [uniform_marked_word_atIndex index Numeric.proposalLength (nearWordEnvelope missing)]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  simp_rw [word_near_forest_moment]
  simpa only [one_div] using Numeric.uniform_history_near_bound missing
def exposedLeaves (history : List (Buckets × LeafChoices)) (c : Fin 7) (bucket : Fin 16) : Finset (Fin 128) :=
  ((history.filter fun row => row.1 c==bucket).flatMap fun row => List.ofFn (row.2 c)).toFinset
theorem exposedLeaves_card_le (history : List (Buckets × LeafChoices)) (c : Fin 7) (bucket : Fin 16) :
    (exposedLeaves history c bucket).card ≤ 3*(history.map fun row => row.1 c).count bucket := by
  calc
    _ ≤ ((history.filter fun row => row.1 c==bucket).flatMap fun row => List.ofFn (row.2 c)).length :=
      List.toFinset_card_le _
    _ = 3*(history.filter fun row => row.1 c==bucket).length := by
      simp [List.length_flatMap,List.length_ofFn,List.sum_replicate,Nat.mul_comm]
    _ = _ := by
      simp only [List.count_eq_countP,List.countP_map]
      rw [List.countP_eq_length_filter]
      rfl
def wordTable (word : List Buckets) : Fin 7 → Fin word.length → Fin 16 :=
  fun c i => word.get i c
theorem wordTable_column (word : List Buckets) (c : Fin 7) :
    List.ofFn (wordTable word c)=word.map (fun row => row c) := by
  exact List.ofFn_getElem_eq_map word (fun row => row c)
theorem wordTable_envelope (word : List Buckets) :
    Numeric.forestEnvelope (wordTable word)=wordEnvelope word := by
  simp only [Numeric.forestEnvelope,wordEnvelope,wordTable_column]
theorem history_covered_probability_le (history : List (Buckets × LeafChoices)) :
    Pr[fun output : HashOutput => digestAdmissible output=true ∧
      SigGolfResearch.Gate6.CoordinateCovered (exposedLeaves history)
        (SigGolfResearch.Gate6.rawDraw (SigGolfResearch.Gate6.digestRecord output)).1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ wordEnvelope (history.map Prod.fst) := by
  simp_rw [SigGolfResearch.Gate6.Source.actual_predicate_iff]
  rw [←wordTable_envelope]
  apply SigGolfResearch.Gate6.accepted_covered_le_forestEnvelope
  intro c bucket
  rw [wordTable_column]
  simpa only [List.map_map,Function.comp_def] using exposedLeaves_card_le history c bucket
end SigGolfCandidate.T3.BPORS.History
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SphincsSecurity.Concrete SigGolfCandidate.T3.DigestSampling
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
noncomputable def jointCountAverage {α : Type} [Fintype α] [DecidableEq α]
    (first second : α) : Nat → (Nat → Nat → ENNReal) → ENNReal
  | 0, payoff => payoff 0 0
  | steps+1, payoff => finiteAverage fun next : α =>
      if next=first then jointCountAverage first second steps (fun i j => payoff (i+1) j)
      else if next=second then jointCountAverage first second steps (fun i j => payoff i (j+1))
      else jointCountAverage first second steps payoff
theorem finiteAverage_commute {α β : Type} [Fintype α] [Fintype β] (f : α → β → ENNReal) :
    finiteAverage (fun a => finiteAverage (f a))=
      finiteAverage (fun b => finiteAverage (fun a => f a b)) := by
  rw [← finiteAverage_pair (fun pair : α × β => f pair.1 pair.2),
    ← finiteAverage_pair (fun pair : β × α => f pair.2 pair.1)]
  exact (finiteAverage_equiv (Equiv.prodComm β α) (fun pair : α × β => f pair.1 pair.2)).symm
theorem average_joint_commute {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    (first second : α) (steps : Nat) (payoff : β → Nat → Nat → ENNReal) :
    finiteAverage (fun mark => jointCountAverage first second steps (payoff mark))=
      jointCountAverage first second steps (fun i j => finiteAverage (fun mark => payoff mark i j)) := by
  induction steps generalizing payoff with
  | zero => rfl
  | succ steps ih =>
      simp only [jointCountAverage]
      rw [finiteAverage_commute]
      congr 1
      funext next
      by_cases hf : next=first
      · simp only [hf,ite_true]
        exact ih (fun mark i j => payoff mark (i+1) j)
      · by_cases hs : next=second
        · subst next
          simp only [hf,ite_false,ite_true]
          exact ih (fun mark i j => payoff mark i (j+1))
        · simp only [hf,hs,ite_false]
          exact ih payoff
theorem uniform_word_joint_count {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (first second : α) (hne : first≠second) (steps : Nat) (payoff : Nat → Nat → ENNReal) :
    uniformWordAverage steps (fun word : List α => payoff (word.count first) (word.count second))=
      jointCountAverage first second steps payoff := by
  induction steps generalizing payoff with
  | zero => simp [uniformWordAverage,sampleUniformProposalWord,jointCountAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ,jointCountAverage]
      congr 1
      funext next
      by_cases hf : next=first
      · subst next
        simp only [List.count_cons_self,List.count_cons_of_ne hne,ite_true]
        exact ih (fun i j => payoff (i+1) j)
      · by_cases hs : next=second
        · subst next
          simp only [List.count_cons_self,List.count_cons_of_ne hne.symm,if_neg hf,ite_true]
          exact ih (fun i j => payoff i (j+1))
        · simp only [List.count_cons_of_ne hf,List.count_cons_of_ne hs,if_neg hf,if_neg hs]
          exact ih payoff
theorem uniform_marked_word_joint {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (first second : α) (hne : first≠second) (steps : Nat)
    (f g : List β → ENNReal) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word)*g (atIndex second word))=
      jointCountAverage first second steps (fun i j => uniformWordAverage i f*uniformWordAverage j g) := by
  induction steps generalizing f g with
  | zero => simp [uniformWordAverage,sampleUniformProposalWord,atIndex,jointCountAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ,finiteAverage_pair,jointCountAverage]
      congr 1
      funext next
      by_cases hf : next=first
      · subst next
        simp only [atIndex_cons,if_pos rfl,if_neg hne,ite_true]
        have hm (mark : β) :
            uniformWordAverage steps (fun word : List (α × β) =>
              f (mark::atIndex first word)*g (atIndex second word))=
            jointCountAverage first second steps (fun i j =>
              uniformWordAverage i (fun word => f (mark::word))*uniformWordAverage j g) :=
          ih (fun word => f (mark::word)) g
        simp_rw [hm]
        rw [average_joint_commute]
        simp_rw [finiteAverage_mul_const,← uniformWordAverage_succ]
      · by_cases hs : next=second
        · subst next
          simp only [atIndex_cons,if_neg hf,if_pos rfl,ite_true]
          have hm (mark : β) :
              uniformWordAverage steps (fun word : List (α × β) =>
                f (atIndex first word)*g (mark::atIndex second word))=
              jointCountAverage first second steps (fun i j =>
                uniformWordAverage i f*uniformWordAverage j (fun word => g (mark::word))) :=
            ih f (fun word => g (mark::word))
          simp_rw [hm]
          rw [average_joint_commute]
          simp_rw [finiteAverage_const_mul,← uniformWordAverage_succ]
        · simp only [atIndex_cons,if_neg hf,if_neg hs]
          rw [ih,finiteAverage_constant]
theorem uniform_envelope_negative_correlation {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (first second : α) (hne : first≠second) (steps : Nat) (a b : List Nat) :
    uniformWordAverage steps (fun word : List α => envelope a (word.count first)*envelope b (word.count second)) ≤
      uniformWordAverage steps (fun word : List α => envelope a (word.count first))*
        uniformWordAverage steps (fun word : List α => envelope b (word.count second)) := by
  simp only [envelope,Finset.sum_mul,Finset.mul_sum,uniformWordAverage_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  have hp (word : List α) :
      ((a.getD i 0 : ENNReal)*(word.count first).descFactorial i)*
        ((b.getD j 0 : ENNReal)*(word.count second).descFactorial j)=
      ((a.getD i 0 : ENNReal)*b.getD j 0)*
        ((word.count first).descFactorial i*(word.count second).descFactorial j) := by ring
  simp_rw [hp,uniformWordAverage_mul_left]
  calc
    _ ≤ ((a.getD i 0 : ENNReal)*b.getD j 0)*
        (uniformWordAverage steps (fun word : List α => (word.count first).descFactorial i)*
          uniformWordAverage steps (fun word : List α => (word.count second).descFactorial j)) :=
      mul_le_mul' le_rfl (uniformWordAverage_mixed_descFactorial_le_product first second hne steps i j)
    _ = _ := by ring
theorem uniformWordAverage_mul_right {α : Type} [SampleableType α]
    (steps : Nat) (factor : ENNReal) (payoff : List α → ENNReal) :
    uniformWordAverage steps (fun word => payoff word*factor)=uniformWordAverage steps payoff*factor := by
  simpa only [mul_comm] using uniformWordAverage_mul_left steps factor payoff
theorem marked_marginal_envelope {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (index : α) (steps : Nat) (f : List β → ENNReal)
    (a : List Nat) (scale : ENNReal) (hf : ∀ n, uniformWordAverage n f=envelope a n*scale) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex index word))=
      uniformWordAverage steps (fun word : List α => envelope a (word.count index))*scale := by
  rw [uniform_marked_word_atIndex]
  simp_rw [hf]
  rw [← uniformWordAverage_mul_right]
  exact (expected_uniformProposalWord_count index steps (fun n => envelope a n*scale)).symm
theorem marked_envelope_negative_correlation {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (first second : α) (hne : first≠second) (steps : Nat)
    (f g : List β → ENNReal) (a b : List Nat) (u v : ENNReal)
    (hf : ∀ n, uniformWordAverage n f=envelope a n*u)
    (hg : ∀ n, uniformWordAverage n g=envelope b n*v) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word)*g (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word))*
        uniformWordAverage steps (fun word : List (α × β) => g (atIndex second word)) := by
  rw [uniform_marked_word_joint first second hne,
    ← uniform_word_joint_count first second hne]
  simp_rw [hf,hg]
  rw [marked_marginal_envelope first steps f a u hf,marked_marginal_envelope second steps g b v hg]
  have hp (word : List α) :
      (envelope a (word.count first)*u)*(envelope b (word.count second)*v)=
        (envelope a (word.count first)*envelope b (word.count second))*(u*v) := by ring
  simp_rw [hp]
  rw [uniformWordAverage_mul_right]
  calc
    _ ≤ (uniformWordAverage steps (fun word : List α => envelope a (word.count first))*
        uniformWordAverage steps (fun word : List α => envelope b (word.count second)))*(u*v) :=
      mul_le_mul' (uniform_envelope_negative_correlation first second hne steps a b) le_rfl
    _ = _ := by ring
theorem word_first_moment (steps : Nat) :
    uniformWordAverage steps wordEnvelope=envelope Numeric.meanCoeffs steps/2^234 := by
  have h := word_forest_moment steps 1
  simpa only [pow_one,Numeric.forest_first_moment] using h
theorem forest_negative_correlation (first second : Fin (2^31)) (hne : first≠second) (steps : Nat) :
    uniformWordAverage steps (fun word : List (Fin (2^31) × Buckets) =>
      wordEnvelope (atIndex first word)*wordEnvelope (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex first word))*
        uniformWordAverage steps (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex second word)) := by
  apply marked_envelope_negative_correlation first second hne steps wordEnvelope wordEnvelope
    Numeric.meanCoeffs Numeric.meanCoeffs ((2^234 : ENNReal)⁻¹) ((2^234 : ENNReal)⁻¹)
  · intro n;simpa only [div_eq_mul_inv] using word_first_moment n
  · intro n;simpa only [div_eq_mul_inv] using word_first_moment n
end SigGolfCandidate.T3.BPORS.History
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SphincsSecurity.Concrete SigGolfCandidate.T3.DigestSampling
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
abbrev Proposal := Fin (2^31) × Buckets
noncomputable def fullPrice (word : List Proposal) : ENNReal :=
  2^97*∑ index : Fin (2^31), wordEnvelope (atIndex index word)
theorem fullPrice_ne_top (word : List Proposal) : fullPrice word≠⊤ := by
  unfold fullPrice
  apply ENNReal.mul_ne_top (by finiteness)
  apply ENNReal.sum_ne_top.mpr
  intro index _
  unfold wordEnvelope coordinateEnvelope bucketMass
  apply ENNReal.div_ne_top ?_ (by norm_num)
  apply ENNReal.prod_ne_top
  intro c _
  apply ENNReal.div_ne_top ?_ (by norm_num)
  apply ENNReal.sum_ne_top.mpr
  intro bucket _
  exact ENNReal.natCast_ne_top _
theorem fullPrice_mean (steps : Nat) :
    uniformWordAverage steps fullPrice=
      (2 : ENNReal)^128*binomialAverage (1/2^31) steps (fun count =>
        expectedValue ($ᵗ (Fin 7 → Fin count → Fin 16) : ProbComp _) Numeric.forestEnvelope) := by
  have hm (index : Fin (2^31)) := uniform_proposal_forest_moment index steps 1
  simp only [pow_one] at hm
  unfold fullPrice
  rw [uniformWordAverage_mul_left,uniformWordAverage_sum]
  simp_rw [hm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_assoc,← pow_add]
theorem fullPrice_mean_bound :
    uniformWordAverage Numeric.proposalLength fullPrice ≤ 37/64 := by
  rw [fullPrice_mean]
  exact Numeric.uniform_history_mean_bound
theorem fullPrice_secondMoment_bound :
    uniformWordAverage Numeric.proposalLength (fun word => fullPrice word^2) ≤
      uniformWordAverage Numeric.proposalLength fullPrice^2+(18400/100000000) := by
  have hs := uniformWordAverage_sum_square_le Numeric.proposalLength
    (fun index (word : List Proposal) => wordEnvelope (atIndex index word))
    (fun first second hne => forest_negative_correlation first second hne Numeric.proposalLength)
  have hscaled := mul_le_mul' (a := ((2 : ENNReal)^97)^2) le_rfl hs
  have hdiag :
      ((2 : ENNReal)^97)^2*(∑ index : Fin (2^31), uniformWordAverage Numeric.proposalLength
        (fun word : List Proposal => wordEnvelope (atIndex index word)^2)) ≤ (18400/100000000) := by
    simp_rw [uniform_proposal_forest_moment]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [← pow_mul,← mul_assoc,← pow_add]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using Numeric.uniform_history_excess_bound
  calc
    _ = ((2 : ENNReal)^97)^2*uniformWordAverage Numeric.proposalLength
        (fun word : List Proposal => (∑ index,wordEnvelope (atIndex index word))^2) := by
      simp only [fullPrice,mul_pow,uniformWordAverage_mul_left]
    _ ≤ ((2 : ENNReal)^97)^2*((∑ index : Fin (2^31),uniformWordAverage Numeric.proposalLength
        (fun word : List Proposal => wordEnvelope (atIndex index word)))^2+
        ∑ index : Fin (2^31),uniformWordAverage Numeric.proposalLength
          (fun word : List Proposal => wordEnvelope (atIndex index word)^2)) := hscaled
    _ = uniformWordAverage Numeric.proposalLength fullPrice^2+
        ((2 : ENNReal)^97)^2*(∑ index : Fin (2^31),uniformWordAverage Numeric.proposalLength
          (fun word : List Proposal => wordEnvelope (atIndex index word)^2)) := by
      unfold fullPrice
      simp only [uniformWordAverage_mul_left,uniformWordAverage_sum,mul_pow,mul_add]
    _ ≤ _ := add_le_add le_rfl hdiag
theorem unit_excess_le_square (value mean : ENNReal) (hvalue : value≠⊤) (hmean : mean≤37/64) :
    (13/8)*(value-1)+2*mean*value ≤ value^2+mean^2 := by
  have hx : value-1≤value-63/64 := tsub_le_tsub_left (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]) value
  exact (add_le_add (mul_le_mul' le_rfl hx) le_rfl).trans
    (SigGolfResearch.Gate6.Excess.theta_excess_le_square value mean hvalue hmean)
theorem uniformWordAverage_constant {α : Type} [Fintype α] [SampleableType α]
    (steps : Nat) (value : ENNReal) : uniformWordAverage steps (fun _ : List α => value)=value := by
  rw [word_array_average]
  exact finiteAverage_constant value
theorem fullPrice_excess_of_pointwise (threshold : ENNReal)
    (hpointwise : ∀ value mean : ENNReal,value≠⊤ → mean≤37/64 →
      (13/8)*(value-threshold)+2*mean*value≤value^2+mean^2) :
    uniformWordAverage Numeric.proposalLength (fun word => fullPrice word-threshold) ≤ 11324/100000000 := by
  let mean := uniformWordAverage Numeric.proposalLength fullPrice
  have hm : mean≠⊤ := ne_top_of_le_ne_top (by finiteness) fullPrice_mean_bound
  have h := uniformWordAverage_mono Numeric.proposalLength (fun word =>
    hpointwise (fullPrice word) mean (fullPrice_ne_top word) fullPrice_mean_bound)
  rw [uniformWordAverage_add,uniformWordAverage_add,uniformWordAverage_mul_left,
    uniformWordAverage_mul_left,uniformWordAverage_constant] at h
  have hcancel : (13/8:ENNReal)*uniformWordAverage Numeric.proposalLength
      (fun word => fullPrice word-threshold)≤18400/100000000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2*mean^2) (by finiteness)
    calc
      _ = (13/8:ENNReal)*uniformWordAverage Numeric.proposalLength (fun word => fullPrice word-threshold)+
          2*mean*uniformWordAverage Numeric.proposalLength fullPrice := by
        change _=_+2*mean*mean
        ring
      _ ≤ uniformWordAverage Numeric.proposalLength (fun word => fullPrice word^2)+mean^2 := h
      _ ≤ (mean^2+18400/100000000)+mean^2 := add_le_add fullPrice_secondMoment_bound le_rfl
      _ = _ := by ring
  have hi : (8/13:ENNReal)*(13/8)=1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_div]
  calc
    _ = (8/13:ENNReal)*((13/8)*uniformWordAverage Numeric.proposalLength
        (fun word => fullPrice word-threshold)) := by rw [←mul_assoc,hi,one_mul]
    _ ≤ (8/13:ENNReal)*(18400/100000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div]
theorem fullPrice_excess_bound :
    uniformWordAverage Numeric.proposalLength (fun word => fullPrice word-1) ≤ 11324/100000000 :=
  fullPrice_excess_of_pointwise 1 unit_excess_le_square
noncomputable def fullNearPrice (word : List Proposal) : ENNReal :=
  3*2^97*∑ index : Fin (2^31), ∑ missing : Fin 7, nearWordEnvelope missing (atIndex index word)
theorem near_mean_at_index (index : Fin (2^31)) (missing : Fin 7) (steps : Nat) :
    uniformWordAverage steps (fun word : List Proposal => nearWordEnvelope missing (atIndex index word))=
      binomialAverage (1/2^31) steps (fun count => envelope Numeric.nearCoeffs count/2^223) := by
  rw [uniform_marked_word_atIndex index steps (nearWordEnvelope missing)]
  simp_rw [word_near_forest_moment,Numeric.near_forest_first_moment]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,one_div]
theorem fullNearPrice_bound : uniformWordAverage Numeric.proposalLength fullNearPrice ≤ 404 := by
  have h := Numeric.uniform_history_near_bound (0 : Fin 7)
  simp_rw [Numeric.near_forest_first_moment] at h
  have he : uniformWordAverage Numeric.proposalLength fullNearPrice=
      21*(2 : ENNReal)^128*binomialAverage (1/2^31) Numeric.proposalLength
        (fun count => envelope Numeric.nearCoeffs count/2^223) := by
    unfold fullNearPrice
    rw [uniformWordAverage_mul_left]
    simp_rw [uniformWordAverage_sum,near_mean_at_index]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [show (2 : ENNReal)^128=2^97*2^31 by rw [← pow_add]]
    ring
  rw [he]
  exact h
end SigGolfCandidate.T3.BPORS.History
end
end
end
