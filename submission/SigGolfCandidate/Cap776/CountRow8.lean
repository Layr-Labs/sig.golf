import SigGolfCandidate.Cap776.CountRow7
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
noncomputable def Count_8_0 : Nat := prob_row% 8 0
theorem count_8_0 : rowFast cache64 8 0=Count_8_0 := by decide +kernel
noncomputable def Count_8_1 : Nat := prob_row% 8 1
theorem count_8_1 : rowFast cache64 8 1=Count_8_1 := by decide +kernel
noncomputable def Count_8_2 : Nat := prob_row% 8 2
theorem count_8_2 : rowFast cache64 8 2=Count_8_2 := by decide +kernel
noncomputable def Count_8_3 : Nat := prob_row% 8 3
theorem count_8_3 : rowFast cache64 8 3=Count_8_3 := by decide +kernel
noncomputable def Count_8_4 : Nat := prob_row% 8 4
theorem count_8_4 : rowFast cache64 8 4=Count_8_4 := by decide +kernel
noncomputable def Count_8_5 : Nat := prob_row% 8 5
theorem count_8_5 : rowFast cache64 8 5=Count_8_5 := by decide +kernel
noncomputable def Count_8_6 : Nat := prob_row% 8 6
theorem count_8_6 : rowFast cache64 8 6=Count_8_6 := by decide +kernel
noncomputable def Count_8_7 : Nat := prob_row% 8 7
theorem count_8_7 : rowFast cache64 8 7=Count_8_7 := by decide +kernel
noncomputable def Count_8_8 : Nat := prob_row% 8 8
theorem count_8_8 : rowFast cache64 8 8=Count_8_8 := by decide +kernel
noncomputable def countRow_8 (t : Nat) : Nat :=
  match t with
  | 0 => Count_8_0
  | 1 => Count_8_1
  | 2 => Count_8_2
  | 3 => Count_8_3
  | 4 => Count_8_4
  | 5 => Count_8_5
  | 6 => Count_8_6
  | 7 => Count_8_7
  | 8 => Count_8_8
  | _ => 0
theorem countRow_8_checked (t : Nat) (ht : t≤8) : row 8 t=countRow_8 t := by
  rw [row_eq 8 t (by omega) ht]
  interval_cases t
  · exact count_8_0
  · exact count_8_1
  · exact count_8_2
  · exact count_8_3
  · exact count_8_4
  · exact count_8_5
  · exact count_8_6
  · exact count_8_7
  · exact count_8_8
noncomputable def Pair_8 : Nat := prob_pair% 8
theorem pair_8_checked : pairPacked 8=Pair_8 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (8+1), Nat.choose 8 t*countRow_8 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_8_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
