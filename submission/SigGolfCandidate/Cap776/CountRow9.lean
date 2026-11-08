import SigGolfCandidate.Cap776.CountRow8
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
noncomputable def Count_9_0 : Nat := prob_row% 9 0
theorem count_9_0 : rowFast cache64 9 0=Count_9_0 := by decide +kernel
noncomputable def Count_9_1 : Nat := prob_row% 9 1
theorem count_9_1 : rowFast cache64 9 1=Count_9_1 := by decide +kernel
noncomputable def Count_9_2 : Nat := prob_row% 9 2
theorem count_9_2 : rowFast cache64 9 2=Count_9_2 := by decide +kernel
noncomputable def Count_9_3 : Nat := prob_row% 9 3
theorem count_9_3 : rowFast cache64 9 3=Count_9_3 := by decide +kernel
noncomputable def Count_9_4 : Nat := prob_row% 9 4
theorem count_9_4 : rowFast cache64 9 4=Count_9_4 := by decide +kernel
noncomputable def Count_9_5 : Nat := prob_row% 9 5
theorem count_9_5 : rowFast cache64 9 5=Count_9_5 := by decide +kernel
noncomputable def Count_9_6 : Nat := prob_row% 9 6
theorem count_9_6 : rowFast cache64 9 6=Count_9_6 := by decide +kernel
noncomputable def Count_9_7 : Nat := prob_row% 9 7
theorem count_9_7 : rowFast cache64 9 7=Count_9_7 := by decide +kernel
noncomputable def Count_9_8 : Nat := prob_row% 9 8
theorem count_9_8 : rowFast cache64 9 8=Count_9_8 := by decide +kernel
noncomputable def Count_9_9 : Nat := prob_row% 9 9
theorem count_9_9 : rowFast cache64 9 9=Count_9_9 := by decide +kernel
noncomputable def countRow_9 (t : Nat) : Nat :=
  match t with
  | 0 => Count_9_0
  | 1 => Count_9_1
  | 2 => Count_9_2
  | 3 => Count_9_3
  | 4 => Count_9_4
  | 5 => Count_9_5
  | 6 => Count_9_6
  | 7 => Count_9_7
  | 8 => Count_9_8
  | 9 => Count_9_9
  | _ => 0
theorem countRow_9_checked (t : Nat) (ht : t≤9) : row 9 t=countRow_9 t := by
  rw [row_eq 9 t (by omega) ht]
  interval_cases t
  · exact count_9_0
  · exact count_9_1
  · exact count_9_2
  · exact count_9_3
  · exact count_9_4
  · exact count_9_5
  · exact count_9_6
  · exact count_9_7
  · exact count_9_8
  · exact count_9_9
noncomputable def Pair_9 : Nat := prob_pair% 9
theorem pair_9_checked : pairPacked 9=Pair_9 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (9+1), Nat.choose 9 t*countRow_9 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_9_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
