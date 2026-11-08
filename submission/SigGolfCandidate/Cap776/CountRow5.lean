import SigGolfCandidate.Cap776.CountRow4
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
noncomputable def Count_5_0 : Nat := prob_row% 5 0
theorem count_5_0 : rowFast cache64 5 0=Count_5_0 := by decide +kernel
noncomputable def Count_5_1 : Nat := prob_row% 5 1
theorem count_5_1 : rowFast cache64 5 1=Count_5_1 := by decide +kernel
noncomputable def Count_5_2 : Nat := prob_row% 5 2
theorem count_5_2 : rowFast cache64 5 2=Count_5_2 := by decide +kernel
noncomputable def Count_5_3 : Nat := prob_row% 5 3
theorem count_5_3 : rowFast cache64 5 3=Count_5_3 := by decide +kernel
noncomputable def Count_5_4 : Nat := prob_row% 5 4
theorem count_5_4 : rowFast cache64 5 4=Count_5_4 := by decide +kernel
noncomputable def Count_5_5 : Nat := prob_row% 5 5
theorem count_5_5 : rowFast cache64 5 5=Count_5_5 := by decide +kernel
noncomputable def countRow_5 (t : Nat) : Nat :=
  match t with
  | 0 => Count_5_0
  | 1 => Count_5_1
  | 2 => Count_5_2
  | 3 => Count_5_3
  | 4 => Count_5_4
  | 5 => Count_5_5
  | _ => 0
theorem countRow_5_checked (t : Nat) (ht : t≤5) : row 5 t=countRow_5 t := by
  rw [row_eq 5 t (by omega) ht]
  interval_cases t
  · exact count_5_0
  · exact count_5_1
  · exact count_5_2
  · exact count_5_3
  · exact count_5_4
  · exact count_5_5
noncomputable def Pair_5 : Nat := prob_pair% 5
theorem pair_5_checked : pairPacked 5=Pair_5 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (5+1), Nat.choose 5 t*countRow_5 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_5_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
