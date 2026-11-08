import SigGolfCandidate.Cap776.CountRow15
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
noncomputable def Count_16_0 : Nat := prob_row% 16 0
theorem count_16_0 : rowFast cache64 16 0=Count_16_0 := by decide +kernel
noncomputable def Count_16_1 : Nat := prob_row% 16 1
theorem count_16_1 : rowFast cache64 16 1=Count_16_1 := by decide +kernel
noncomputable def Count_16_2 : Nat := prob_row% 16 2
theorem count_16_2 : rowFast cache64 16 2=Count_16_2 := by decide +kernel
noncomputable def Count_16_3 : Nat := prob_row% 16 3
theorem count_16_3 : rowFast cache64 16 3=Count_16_3 := by decide +kernel
noncomputable def Count_16_4 : Nat := prob_row% 16 4
theorem count_16_4 : rowFast cache64 16 4=Count_16_4 := by decide +kernel
noncomputable def Count_16_5 : Nat := prob_row% 16 5
theorem count_16_5 : rowFast cache64 16 5=Count_16_5 := by decide +kernel
noncomputable def Count_16_6 : Nat := prob_row% 16 6
theorem count_16_6 : rowFast cache64 16 6=Count_16_6 := by decide +kernel
noncomputable def Count_16_7 : Nat := prob_row% 16 7
theorem count_16_7 : rowFast cache64 16 7=Count_16_7 := by decide +kernel
noncomputable def Count_16_8 : Nat := prob_row% 16 8
theorem count_16_8 : rowFast cache64 16 8=Count_16_8 := by decide +kernel
noncomputable def Count_16_9 : Nat := prob_row% 16 9
theorem count_16_9 : rowFast cache64 16 9=Count_16_9 := by decide +kernel
noncomputable def Count_16_10 : Nat := prob_row% 16 10
theorem count_16_10 : rowFast cache64 16 10=Count_16_10 := by decide +kernel
noncomputable def Count_16_11 : Nat := prob_row% 16 11
theorem count_16_11 : rowFast cache64 16 11=Count_16_11 := by decide +kernel
noncomputable def Count_16_12 : Nat := prob_row% 16 12
theorem count_16_12 : rowFast cache64 16 12=Count_16_12 := by decide +kernel
noncomputable def Count_16_13 : Nat := prob_row% 16 13
theorem count_16_13 : rowFast cache64 16 13=Count_16_13 := by decide +kernel
noncomputable def Count_16_14 : Nat := prob_row% 16 14
theorem count_16_14 : rowFast cache64 16 14=Count_16_14 := by decide +kernel
noncomputable def Count_16_15 : Nat := prob_row% 16 15
theorem count_16_15 : rowFast cache64 16 15=Count_16_15 := by decide +kernel
noncomputable def Count_16_16 : Nat := prob_row% 16 16
theorem count_16_16 : rowFast cache64 16 16=Count_16_16 := by decide +kernel
noncomputable def countRow_16 (t : Nat) : Nat :=
  match t with
  | 0 => Count_16_0
  | 1 => Count_16_1
  | 2 => Count_16_2
  | 3 => Count_16_3
  | 4 => Count_16_4
  | 5 => Count_16_5
  | 6 => Count_16_6
  | 7 => Count_16_7
  | 8 => Count_16_8
  | 9 => Count_16_9
  | 10 => Count_16_10
  | 11 => Count_16_11
  | 12 => Count_16_12
  | 13 => Count_16_13
  | 14 => Count_16_14
  | 15 => Count_16_15
  | 16 => Count_16_16
  | _ => 0
theorem countRow_16_checked (t : Nat) (ht : t≤16) : row 16 t=countRow_16 t := by
  rw [row_eq 16 t (by omega) ht]
  interval_cases t
  · exact count_16_0
  · exact count_16_1
  · exact count_16_2
  · exact count_16_3
  · exact count_16_4
  · exact count_16_5
  · exact count_16_6
  · exact count_16_7
  · exact count_16_8
  · exact count_16_9
  · exact count_16_10
  · exact count_16_11
  · exact count_16_12
  · exact count_16_13
  · exact count_16_14
  · exact count_16_15
  · exact count_16_16
noncomputable def Pair_16 : Nat := prob_pair% 16
theorem pair_16_checked : pairPacked 16=Pair_16 :=
  (pair_of_rows 16 countRow_16 countRow_16_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
