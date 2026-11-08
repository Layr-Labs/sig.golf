import SigGolfCandidate.Cap776.CountRow6
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
noncomputable def Count_7_0 : Nat := prob_row% 7 0
theorem count_7_0 : rowFast cache64 7 0=Count_7_0 := by decide +kernel
noncomputable def Count_7_1 : Nat := prob_row% 7 1
theorem count_7_1 : rowFast cache64 7 1=Count_7_1 := by decide +kernel
noncomputable def Count_7_2 : Nat := prob_row% 7 2
theorem count_7_2 : rowFast cache64 7 2=Count_7_2 := by decide +kernel
noncomputable def Count_7_3 : Nat := prob_row% 7 3
theorem count_7_3 : rowFast cache64 7 3=Count_7_3 := by decide +kernel
noncomputable def Count_7_4 : Nat := prob_row% 7 4
theorem count_7_4 : rowFast cache64 7 4=Count_7_4 := by decide +kernel
noncomputable def Count_7_5 : Nat := prob_row% 7 5
theorem count_7_5 : rowFast cache64 7 5=Count_7_5 := by decide +kernel
noncomputable def Count_7_6 : Nat := prob_row% 7 6
theorem count_7_6 : rowFast cache64 7 6=Count_7_6 := by decide +kernel
noncomputable def Count_7_7 : Nat := prob_row% 7 7
theorem count_7_7 : rowFast cache64 7 7=Count_7_7 := by decide +kernel
noncomputable def countRow_7 (t : Nat) : Nat :=
  match t with
  | 0 => Count_7_0
  | 1 => Count_7_1
  | 2 => Count_7_2
  | 3 => Count_7_3
  | 4 => Count_7_4
  | 5 => Count_7_5
  | 6 => Count_7_6
  | 7 => Count_7_7
  | _ => 0
theorem countRow_7_checked (t : Nat) (ht : t≤7) : row 7 t=countRow_7 t := by
  rw [row_eq 7 t (by omega) ht]
  interval_cases t
  · exact count_7_0
  · exact count_7_1
  · exact count_7_2
  · exact count_7_3
  · exact count_7_4
  · exact count_7_5
  · exact count_7_6
  · exact count_7_7
noncomputable def Pair_7 : Nat := prob_pair% 7
theorem pair_7_checked : pairPacked 7=Pair_7 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (7+1), Nat.choose 7 t*countRow_7 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_7_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
