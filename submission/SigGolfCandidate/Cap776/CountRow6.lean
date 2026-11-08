import SigGolfCandidate.Cap776.CountRow5
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
noncomputable def Count_6_0 : Nat := prob_row% 6 0
theorem count_6_0 : rowFast cache64 6 0=Count_6_0 := by decide +kernel
noncomputable def Count_6_1 : Nat := prob_row% 6 1
theorem count_6_1 : rowFast cache64 6 1=Count_6_1 := by decide +kernel
noncomputable def Count_6_2 : Nat := prob_row% 6 2
theorem count_6_2 : rowFast cache64 6 2=Count_6_2 := by decide +kernel
noncomputable def Count_6_3 : Nat := prob_row% 6 3
theorem count_6_3 : rowFast cache64 6 3=Count_6_3 := by decide +kernel
noncomputable def Count_6_4 : Nat := prob_row% 6 4
theorem count_6_4 : rowFast cache64 6 4=Count_6_4 := by decide +kernel
noncomputable def Count_6_5 : Nat := prob_row% 6 5
theorem count_6_5 : rowFast cache64 6 5=Count_6_5 := by decide +kernel
noncomputable def Count_6_6 : Nat := prob_row% 6 6
theorem count_6_6 : rowFast cache64 6 6=Count_6_6 := by decide +kernel
noncomputable def countRow_6 (t : Nat) : Nat :=
  match t with
  | 0 => Count_6_0
  | 1 => Count_6_1
  | 2 => Count_6_2
  | 3 => Count_6_3
  | 4 => Count_6_4
  | 5 => Count_6_5
  | 6 => Count_6_6
  | _ => 0
theorem countRow_6_checked (t : Nat) (ht : t≤6) : row 6 t=countRow_6 t := by
  rw [row_eq 6 t (by omega) ht]
  interval_cases t
  · exact count_6_0
  · exact count_6_1
  · exact count_6_2
  · exact count_6_3
  · exact count_6_4
  · exact count_6_5
  · exact count_6_6
noncomputable def Pair_6 : Nat := prob_pair% 6
theorem pair_6_checked : pairPacked 6=Pair_6 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (6+1), Nat.choose 6 t*countRow_6 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_6_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
