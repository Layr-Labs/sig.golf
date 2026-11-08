import SigGolfCandidate.Cap776.CountRow11
import SigGolfCandidate.Cap776.ForestInput
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
noncomputable def Count_12_0 : Nat := prob_row% 12 0
theorem count_12_0 : rowFast cache64 12 0=Count_12_0 := by decide +kernel
noncomputable def Count_12_1 : Nat := prob_row% 12 1
theorem count_12_1 : rowFast cache64 12 1=Count_12_1 := by decide +kernel
noncomputable def Count_12_2 : Nat := prob_row% 12 2
theorem count_12_2 : rowFast cache64 12 2=Count_12_2 := by decide +kernel
noncomputable def Count_12_3 : Nat := prob_row% 12 3
theorem count_12_3 : rowFast cache64 12 3=Count_12_3 := by decide +kernel
noncomputable def Count_12_4 : Nat := prob_row% 12 4
theorem count_12_4 : rowFast cache64 12 4=Count_12_4 := by decide +kernel
noncomputable def Count_12_5 : Nat := prob_row% 12 5
theorem count_12_5 : rowFast cache64 12 5=Count_12_5 := by decide +kernel
noncomputable def Count_12_6 : Nat := prob_row% 12 6
theorem count_12_6 : rowFast cache64 12 6=Count_12_6 := by decide +kernel
noncomputable def Count_12_7 : Nat := prob_row% 12 7
theorem count_12_7 : rowFast cache64 12 7=Count_12_7 := by decide +kernel
noncomputable def Count_12_8 : Nat := prob_row% 12 8
theorem count_12_8 : rowFast cache64 12 8=Count_12_8 := by decide +kernel
noncomputable def Count_12_9 : Nat := prob_row% 12 9
theorem count_12_9 : rowFast cache64 12 9=Count_12_9 := by decide +kernel
noncomputable def Count_12_10 : Nat := prob_row% 12 10
theorem count_12_10 : rowFast cache64 12 10=Count_12_10 := by decide +kernel
noncomputable def Count_12_11 : Nat := prob_row% 12 11
theorem count_12_11 : rowFast cache64 12 11=Count_12_11 := by decide +kernel
noncomputable def Count_12_12 : Nat := prob_row% 12 12
theorem count_12_12 : rowFast cache64 12 12=Count_12_12 := by decide +kernel
noncomputable def countRow_12 (t : Nat) : Nat :=
  match t with
  | 0 => Count_12_0
  | 1 => Count_12_1
  | 2 => Count_12_2
  | 3 => Count_12_3
  | 4 => Count_12_4
  | 5 => Count_12_5
  | 6 => Count_12_6
  | 7 => Count_12_7
  | 8 => Count_12_8
  | 9 => Count_12_9
  | 10 => Count_12_10
  | 11 => Count_12_11
  | 12 => Count_12_12
  | _ => 0
theorem countRow_12_checked (t : Nat) (ht : t≤12) : row 12 t=countRow_12 t := by
  rw [row_eq 12 t (by omega) ht]
  interval_cases t
  · exact count_12_0
  · exact count_12_1
  · exact count_12_2
  · exact count_12_3
  · exact count_12_4
  · exact count_12_5
  · exact count_12_6
  · exact count_12_7
  · exact count_12_8
  · exact count_12_9
  · exact count_12_10
  · exact count_12_11
  · exact count_12_12
noncomputable def Pair_12 : Nat := prob_pair% 12
theorem pair_12_checked : pairPacked 12=Pair_12 :=
  (pair_of_rows 12 countRow_12 countRow_12_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
