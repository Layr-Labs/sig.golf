import SigGolfCandidate.Cap776.CountRow18
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
noncomputable def Count_19_0 : Nat := prob_row% 19 0
theorem count_19_0 : rowFast cache64 19 0=Count_19_0 := by decide +kernel
noncomputable def Count_19_1 : Nat := prob_row% 19 1
theorem count_19_1 : rowFast cache64 19 1=Count_19_1 := by decide +kernel
noncomputable def Count_19_2 : Nat := prob_row% 19 2
theorem count_19_2 : rowFast cache64 19 2=Count_19_2 := by decide +kernel
noncomputable def Count_19_3 : Nat := prob_row% 19 3
theorem count_19_3 : rowFast cache64 19 3=Count_19_3 := by decide +kernel
noncomputable def Count_19_4 : Nat := prob_row% 19 4
theorem count_19_4 : rowFast cache64 19 4=Count_19_4 := by decide +kernel
noncomputable def Count_19_5 : Nat := prob_row% 19 5
theorem count_19_5 : rowFast cache64 19 5=Count_19_5 := by decide +kernel
noncomputable def Count_19_6 : Nat := prob_row% 19 6
theorem count_19_6 : rowFast cache64 19 6=Count_19_6 := by decide +kernel
noncomputable def Count_19_7 : Nat := prob_row% 19 7
theorem count_19_7 : rowFast cache64 19 7=Count_19_7 := by decide +kernel
noncomputable def Count_19_8 : Nat := prob_row% 19 8
theorem count_19_8 : rowFast cache64 19 8=Count_19_8 := by decide +kernel
noncomputable def Count_19_9 : Nat := prob_row% 19 9
theorem count_19_9 : rowFast cache64 19 9=Count_19_9 := by decide +kernel
noncomputable def Count_19_10 : Nat := prob_row% 19 10
theorem count_19_10 : rowFast cache64 19 10=Count_19_10 := by decide +kernel
noncomputable def Count_19_11 : Nat := prob_row% 19 11
theorem count_19_11 : rowFast cache64 19 11=Count_19_11 := by decide +kernel
noncomputable def Count_19_12 : Nat := prob_row% 19 12
theorem count_19_12 : rowFast cache64 19 12=Count_19_12 := by decide +kernel
noncomputable def Count_19_13 : Nat := prob_row% 19 13
theorem count_19_13 : rowFast cache64 19 13=Count_19_13 := by decide +kernel
noncomputable def Count_19_14 : Nat := prob_row% 19 14
theorem count_19_14 : rowFast cache64 19 14=Count_19_14 := by decide +kernel
noncomputable def Count_19_15 : Nat := prob_row% 19 15
theorem count_19_15 : rowFast cache64 19 15=Count_19_15 := by decide +kernel
noncomputable def Count_19_16 : Nat := prob_row% 19 16
theorem count_19_16 : rowFast cache64 19 16=Count_19_16 := by decide +kernel
noncomputable def Count_19_17 : Nat := prob_row% 19 17
theorem count_19_17 : rowFast cache64 19 17=Count_19_17 := by decide +kernel
noncomputable def Count_19_18 : Nat := prob_row% 19 18
theorem count_19_18 : rowFast cache64 19 18=Count_19_18 := by decide +kernel
noncomputable def Count_19_19 : Nat := prob_row% 19 19
theorem count_19_19 : rowFast cache64 19 19=Count_19_19 := by decide +kernel
noncomputable def countRow_19 (t : Nat) : Nat :=
  match t with
  | 0 => Count_19_0
  | 1 => Count_19_1
  | 2 => Count_19_2
  | 3 => Count_19_3
  | 4 => Count_19_4
  | 5 => Count_19_5
  | 6 => Count_19_6
  | 7 => Count_19_7
  | 8 => Count_19_8
  | 9 => Count_19_9
  | 10 => Count_19_10
  | 11 => Count_19_11
  | 12 => Count_19_12
  | 13 => Count_19_13
  | 14 => Count_19_14
  | 15 => Count_19_15
  | 16 => Count_19_16
  | 17 => Count_19_17
  | 18 => Count_19_18
  | 19 => Count_19_19
  | _ => 0
theorem countRow_19_checked (t : Nat) (ht : t≤19) : row 19 t=countRow_19 t := by
  rw [row_eq 19 t (by omega) ht]
  interval_cases t
  · exact count_19_0
  · exact count_19_1
  · exact count_19_2
  · exact count_19_3
  · exact count_19_4
  · exact count_19_5
  · exact count_19_6
  · exact count_19_7
  · exact count_19_8
  · exact count_19_9
  · exact count_19_10
  · exact count_19_11
  · exact count_19_12
  · exact count_19_13
  · exact count_19_14
  · exact count_19_15
  · exact count_19_16
  · exact count_19_17
  · exact count_19_18
  · exact count_19_19
noncomputable def Pair_19 : Nat := prob_pair% 19
theorem pair_19_checked : pairPacked 19=Pair_19 :=
  (pair_of_rows 19 countRow_19 countRow_19_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
