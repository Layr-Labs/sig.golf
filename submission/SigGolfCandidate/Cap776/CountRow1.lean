import SigGolfCandidate.Cap776.CountInput
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open Lean Elab Term
open ClaudeWCT.Numerics
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open SigGolfResearch.ProbabilityRows
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
attribute [local irreducible] ProbabilityRows.row SharedPathList.coordinate SharedPathPacked.product SharedPathPacked.addFirst
noncomputable def Count_1_0 : Nat := prob_row% 1 0
theorem count_1_0 : rowFast cache64 1 0=Count_1_0 := by decide +kernel
noncomputable def Count_1_1 : Nat := prob_row% 1 1
theorem count_1_1 : rowFast cache64 1 1=Count_1_1 := by decide +kernel
noncomputable def countRow_1 (t : Nat) : Nat :=
  match t with
  | 0 => Count_1_0
  | 1 => Count_1_1
  | _ => 0
theorem countRow_1_checked (t : Nat) (ht : t≤1) : row 1 t=countRow_1 t := by
  rw [row_eq 1 t (by omega) ht]
  interval_cases t
  · exact count_1_0
  · exact count_1_1
noncomputable def Pair_1 : Nat := prob_pair% 1
theorem pair_1_checked : pairPacked 1=Pair_1 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (1+1), Nat.choose 1 t*countRow_1 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_1_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
