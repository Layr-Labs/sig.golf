import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-! Mathematical interface for a restricted, witness-selected encoding half.
This module is not yet connected to the signature's adaptive security proof.
`blocked` contains the low words which force use of the low half. -/
namespace SigGolfCandidate.Choice.Gated

variable {α : Type*} [Fintype α] [DecidableEq α]

def accepted (good blocked : Finset α) : Finset (α × α) :=
  good ×ˢ Finset.univ ∪ (Finset.univ \ (blocked ∪ good)) ×ˢ good

theorem mem_accepted (good blocked : Finset α) (a : α × α) :
    a ∈ accepted good blocked ↔ a.1 ∈ good ∨ (a.1 ∉ blocked ∧ a.2 ∈ good) := by
  simp only [accepted, Finset.mem_union, Finset.mem_product,
    Finset.mem_sdiff, Finset.mem_univ, and_true, true_and]
  tauto

theorem accepted_card (good blocked : Finset α) :
    (accepted good blocked).card = good.card * Fintype.card α +
      (Fintype.card α - (blocked ∪ good).card) * good.card := by
  have hd : Disjoint (good ×ˢ (Finset.univ : Finset α))
      ((Finset.univ \ (blocked ∪ good)) ×ˢ good) := by
    apply Finset.disjoint_left.mpr
    intro x h₁ h₂
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp h₂).1).2
      (Finset.mem_union_right _ (Finset.mem_product.mp h₁).1)
  rw [accepted, Finset.card_union_of_disjoint hd]
  simp only [Finset.card_product, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]

theorem accepted_card_upper (good blocked : Finset α) :
    (accepted good blocked).card ≤
      good.card * (Fintype.card α + (Fintype.card α - blocked.card)) := by
  rw [accepted_card]
  have hm : blocked.card ≤ (blocked ∪ good).card :=
    Finset.card_le_card Finset.subset_union_left
  calc _ ≤ good.card * Fintype.card α + (Fintype.card α - blocked.card) * good.card := by
        gcongr
    _ = _ := by ring

theorem accepted_card_lower (good blocked : Finset α) :
    good.card * Fintype.card α +
      (Fintype.card α - blocked.card - good.card) * good.card ≤
        (accepted good blocked).card := by
  rw [accepted_card]
  have hm := Finset.card_union_le blocked good
  exact Nat.add_le_add_left (Nat.mul_le_mul_right good.card (by omega)) _

/-- At a blocked low word the witness cannot request the high half. -/
def read (blocked : Finset α) (high : Bool) (a : α × α) : α :=
  if high ∧ a.1 ∉ blocked then a.2 else a.1

theorem read_mem (good blocked : Finset α) (high : Bool) (a : α × α)
    (h : read blocked high a ∈ good) : a ∈ accepted good blocked := by
  rw [mem_accepted]
  unfold read at h
  split_ifs at h with hc
  · exact Or.inr ⟨hc.2, h⟩
  · exact Or.inl h

/-- The producer always prefers a usable low half. -/
def choose (good blocked : Finset α) (a : α × α) : α :=
  if a.1 ∈ good ∨ a.1 ∈ blocked then a.1 else a.2

theorem choose_mem (good blocked : Finset α) (a : α × α) :
    choose good blocked a ∈ good ↔ a ∈ accepted good blocked := by
  rw [mem_accepted]
  by_cases hg : a.1 ∈ good <;> by_cases hb : a.1 ∈ blocked <;>
    simp [choose, hg, hb]

theorem read_implies_choose (good blocked : Finset α) (high : Bool) (a : α × α)
    (h : read blocked high a ∈ good) : choose good blocked a ∈ good :=
  (choose_mem good blocked a).mpr (read_mem good blocked high a h)

/-- A target-dependent residual probe accounts for both allowed witness choices. -/
def targetRead (blocked : Finset α) (target : α) (a : α × α) : α :=
  if a.1 = target ∨ a.1 ∈ blocked then a.1 else a.2

omit [Fintype α] in
theorem targetRead_hit (blocked : Finset α) (target : α) (a : α × α) :
    targetRead blocked target a = target ↔
      a.1 = target ∨ (a.1 ∉ blocked ∧ a.2 = target) := by
  by_cases ht : a.1 = target <;> by_cases hb : a.1 ∈ blocked <;>
    simp [targetRead, ht, hb]

theorem read_hit_implies_probe_hit (blocked : Finset α) (target : α) (high : Bool)
    (a : α × α) (h : read blocked high a = target) : targetRead blocked target a = target := by
  rw [targetRead_hit]
  simpa only [Finset.mem_singleton] using
    (mem_accepted {target} blocked a).mp
      (read_mem {target} blocked high a (by simpa using h))

/-- Honest failed rows cannot contain an allowed opening of any producer word.
This is the condition needed to extend the first-success prefix coupling. -/
theorem rejected_row_no_read (good blocked : Finset α) (a : α × α)
    (h : choose good blocked a ∉ good) (high : Bool) : read blocked high a ∉ good :=
  fun hr => h (read_implies_choose good blocked high a hr)

theorem target_hit_implies_choose (good blocked : Finset α) (target : α) (a : α × α)
    (ht : target ∈ good) (hit : targetRead blocked target a = target) :
    choose good blocked a ∈ good := by
  rw [choose_mem, mem_accepted]
  rcases (targetRead_hit blocked target a).mp hit with hl | ⟨hb, hh⟩
  · exact Or.inl (hl.symm ▸ ht)
  · exact Or.inr ⟨hb, hh.symm ▸ ht⟩

/-- The widened contact test cannot fire at an earlier rejected honest row. -/
theorem prefix_hit_eq_reference (good blocked : Finset α) (target : α)
    (rows : Nat → α × α) (reference counter : Nat)
    (before : ∀ i < reference, choose good blocked (rows i) ∉ good)
    (hcounter : counter ≤ reference) (ht : target ∈ good)
    (hit : targetRead blocked target (rows counter) = target) : counter = reference := by
  by_contra hne
  have hlt : counter < reference := by omega
  exact before counter hlt (target_hit_implies_choose good blocked target _ ht hit)

section Quarter
variable (good blocked : Finset α) (D : Nat)
  (hspace : Fintype.card α = 4 * D) (hblocked : blocked.card = D)
include hspace hblocked

theorem quarter_upper : (accepted good blocked).card ≤ good.card * (7 * D) := by
  have h := accepted_card_upper good blocked
  rw [hspace, hblocked] at h
  have he : 4 * D + (4 * D - D) = 7 * D := by omega
  rwa [he] at h

theorem quarter_lower : good.card * (7 * D - good.card) ≤ (accepted good blocked).card := by
  have h := accepted_card_lower good blocked
  rw [hspace, hblocked] at h
  have he : good.card * (7 * D - good.card) ≤
      good.card * (4 * D) + (4 * D - D - good.card) * good.card := by
    calc _ ≤ good.card * (4 * D + (4 * D - D - good.card)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  exact he.trans h
end Quarter

end SigGolfCandidate.Choice.Gated

#print axioms SigGolfCandidate.Choice.Gated.quarter_upper
#print axioms SigGolfCandidate.Choice.Gated.quarter_lower
#print axioms SigGolfCandidate.Choice.Gated.rejected_row_no_read
#print axioms SigGolfCandidate.Choice.Gated.read_hit_implies_probe_hit
#print axioms SigGolfCandidate.Choice.Gated.prefix_hit_eq_reference
