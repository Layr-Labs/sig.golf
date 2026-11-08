import SigGolfCandidate.Cap776.CountRow10
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
noncomputable def Count_11_0 : Nat := prob_row% 11 0
theorem count_11_0 : rowFast cache64 11 0=Count_11_0 := by decide +kernel
noncomputable def Count_11_1 : Nat := prob_row% 11 1
theorem count_11_1 : rowFast cache64 11 1=Count_11_1 := by decide +kernel
noncomputable def Count_11_2 : Nat := prob_row% 11 2
theorem count_11_2 : rowFast cache64 11 2=Count_11_2 := by decide +kernel
noncomputable def Count_11_3 : Nat := prob_row% 11 3
theorem count_11_3 : rowFast cache64 11 3=Count_11_3 := by decide +kernel
noncomputable def Count_11_4 : Nat := prob_row% 11 4
theorem count_11_4 : rowFast cache64 11 4=Count_11_4 := by decide +kernel
noncomputable def Count_11_5 : Nat := prob_row% 11 5
theorem count_11_5 : rowFast cache64 11 5=Count_11_5 := by decide +kernel
noncomputable def Count_11_6 : Nat := prob_row% 11 6
theorem count_11_6 : rowFast cache64 11 6=Count_11_6 := by decide +kernel
noncomputable def Count_11_7 : Nat := prob_row% 11 7
theorem count_11_7 : rowFast cache64 11 7=Count_11_7 := by decide +kernel
noncomputable def Count_11_8 : Nat := prob_row% 11 8
theorem count_11_8 : rowFast cache64 11 8=Count_11_8 := by decide +kernel
noncomputable def Count_11_9 : Nat := prob_row% 11 9
theorem count_11_9 : rowFast cache64 11 9=Count_11_9 := by decide +kernel
noncomputable def Count_11_10 : Nat := prob_row% 11 10
theorem count_11_10 : rowFast cache64 11 10=Count_11_10 := by decide +kernel
noncomputable def Count_11_11 : Nat := prob_row% 11 11
theorem count_11_11 : rowFast cache64 11 11=Count_11_11 := by decide +kernel
noncomputable def countRow_11 (t : Nat) : Nat :=
  match t with
  | 0 => Count_11_0
  | 1 => Count_11_1
  | 2 => Count_11_2
  | 3 => Count_11_3
  | 4 => Count_11_4
  | 5 => Count_11_5
  | 6 => Count_11_6
  | 7 => Count_11_7
  | 8 => Count_11_8
  | 9 => Count_11_9
  | 10 => Count_11_10
  | 11 => Count_11_11
  | _ => 0
theorem countRow_11_checked (t : Nat) (ht : t≤11) : row 11 t=countRow_11 t := by
  rw [row_eq 11 t (by omega) ht]
  interval_cases t
  · exact count_11_0
  · exact count_11_1
  · exact count_11_2
  · exact count_11_3
  · exact count_11_4
  · exact count_11_5
  · exact count_11_6
  · exact count_11_7
  · exact count_11_8
  · exact count_11_9
  · exact count_11_10
  · exact count_11_11
noncomputable def Pair_11 : Nat := prob_pair% 11
theorem pair_11_checked : pairPacked 11=Pair_11 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (11+1), Nat.choose 11 t*countRow_11 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_11_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
