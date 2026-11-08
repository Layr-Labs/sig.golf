import SigGolfCandidate.Cap776.CountRow9
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
noncomputable def Count_10_0 : Nat := prob_row% 10 0
theorem count_10_0 : rowFast cache64 10 0=Count_10_0 := by decide +kernel
noncomputable def Count_10_1 : Nat := prob_row% 10 1
theorem count_10_1 : rowFast cache64 10 1=Count_10_1 := by decide +kernel
noncomputable def Count_10_2 : Nat := prob_row% 10 2
theorem count_10_2 : rowFast cache64 10 2=Count_10_2 := by decide +kernel
noncomputable def Count_10_3 : Nat := prob_row% 10 3
theorem count_10_3 : rowFast cache64 10 3=Count_10_3 := by decide +kernel
noncomputable def Count_10_4 : Nat := prob_row% 10 4
theorem count_10_4 : rowFast cache64 10 4=Count_10_4 := by decide +kernel
noncomputable def Count_10_5 : Nat := prob_row% 10 5
theorem count_10_5 : rowFast cache64 10 5=Count_10_5 := by decide +kernel
noncomputable def Count_10_6 : Nat := prob_row% 10 6
theorem count_10_6 : rowFast cache64 10 6=Count_10_6 := by decide +kernel
noncomputable def Count_10_7 : Nat := prob_row% 10 7
theorem count_10_7 : rowFast cache64 10 7=Count_10_7 := by decide +kernel
noncomputable def Count_10_8 : Nat := prob_row% 10 8
theorem count_10_8 : rowFast cache64 10 8=Count_10_8 := by decide +kernel
noncomputable def Count_10_9 : Nat := prob_row% 10 9
theorem count_10_9 : rowFast cache64 10 9=Count_10_9 := by decide +kernel
noncomputable def Count_10_10 : Nat := prob_row% 10 10
theorem count_10_10 : rowFast cache64 10 10=Count_10_10 := by decide +kernel
noncomputable def countRow_10 (t : Nat) : Nat :=
  match t with
  | 0 => Count_10_0
  | 1 => Count_10_1
  | 2 => Count_10_2
  | 3 => Count_10_3
  | 4 => Count_10_4
  | 5 => Count_10_5
  | 6 => Count_10_6
  | 7 => Count_10_7
  | 8 => Count_10_8
  | 9 => Count_10_9
  | 10 => Count_10_10
  | _ => 0
theorem countRow_10_checked (t : Nat) (ht : t≤10) : row 10 t=countRow_10 t := by
  rw [row_eq 10 t (by omega) ht]
  interval_cases t
  · exact count_10_0
  · exact count_10_1
  · exact count_10_2
  · exact count_10_3
  · exact count_10_4
  · exact count_10_5
  · exact count_10_6
  · exact count_10_7
  · exact count_10_8
  · exact count_10_9
  · exact count_10_10
noncomputable def Pair_10 : Nat := prob_pair% 10
theorem pair_10_checked : pairPacked 10=Pair_10 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (10+1), Nat.choose 10 t*countRow_10 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_10_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
