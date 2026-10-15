import SigGolfCandidate.T3.Nonbinary.Counting

namespace SigGolfResearch.NonbinaryTop.Cost
open scoped BigOperators
open Codec Counting
set_option maxHeartbeats 100000
def credit5 (d : Triple5) : Nat := ∑ i,if 3≤(d i).val then 1 else 0
def credit8 (d : Triple8) : Nat := ∑ i,if 6≤(d i).val then 1 else 0
def credit (w : Word) : Nat := (∑ i,credit5 (w.1 i))+credit8 w.2
theorem triple5_sum_le (d : Triple5) : tripleSum5 d≤6+2*credit5 d := by
  have h : ∀ i : Fin 3,(d i).val≤2+2*(if 3≤(d i).val then 1 else 0) := by
    intro i; have := (d i).isLt; split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) => h i)
  simpa [tripleSum5,credit5,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm] using hs
theorem triple8_sum_le (d : Triple8) : tripleSum8 d≤15+2*credit8 d := by
  have h : ∀ i : Fin 3,(d i).val≤5+2*(if 6≤(d i).val then 1 else 0) := by
    intro i; have := (d i).isLt; split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) => h i)
  simpa [tripleSum8,credit8,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm] using hs
theorem weight_le_credit (w : Word) : weight w≤117+2*credit w := by
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 17))) => triple5_sum_le (w.1 i))
  have ht : (∑ i,tripleSum5 (w.1 i))≤102+2*(∑ i,credit5 (w.1 i)) := by
    simpa [Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm] using hs
  have hq := triple8_sum_le w.2
  unfold weight credit
  omega
theorem accepted_credit_ge_fourteen (w : Word) (h : weight w=144) : 14≤credit w := by
  have := weight_le_credit w
  omega
end SigGolfResearch.NonbinaryTop.Cost
#print axioms SigGolfResearch.NonbinaryTop.Cost.weight_le_credit
#print axioms SigGolfResearch.NonbinaryTop.Cost.accepted_credit_ge_fourteen
