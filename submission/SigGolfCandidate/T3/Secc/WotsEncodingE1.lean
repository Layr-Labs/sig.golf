import SigGolfCandidate.T3.Secc.WotsEncodingMatch

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
section Assembly
variable (adversary : AdversaryP) (q : Nat)
theorem tsum_uniform_prod {α β : Type} {iP : Fintype (α × β)} [Nonempty (α × β)] (iA : Fintype α) (iB : Fintype β)
    [Nonempty α] [Nonempty β] (G : α × β → ENNReal) :
    ∑' R, @PMF.uniformOfFintype (α × β) iP _ R * G R =
      ∑' a, @PMF.uniformOfFintype α iA _ a * ∑' b, @PMF.uniformOfFintype β iB _ b * G (a, b) := by
  obtain rfl : iP = @instFintypeProd α β iA iB := Subsingleton.elim _ _
  rw [ENNReal.tsum_prod (f := fun a b => @PMF.uniformOfFintype (α × β) (@instFintypeProd α β iA iB) _ (a, b) *
    G (a, b))]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (by simp) (by simp), mul_assoc]
theorem weighted_le {α : Type} (μ : α → ENNReal) (left right : α → ENNReal) (rate : ENNReal)
    (h : ∀ x, left x ≤ rate * right x) : ∑' x, μ x * left x ≤ rate * ∑' x, μ x * right x := by
  calc _ ≤ ∑' x, μ x * (rate * right x) := ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => mul_left_comm _ _ _
end Assembly
end Enc
end SigGolfCandidate.T3.Security.Wots
