import SigGolfCandidate.Cap776.CountRow2
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
noncomputable def Count_3_0 : Nat := prob_row% 3 0
theorem count_3_0 : rowFast cache64 3 0=Count_3_0 := by decide +kernel
noncomputable def Count_3_1 : Nat := prob_row% 3 1
theorem count_3_1 : rowFast cache64 3 1=Count_3_1 := by decide +kernel
noncomputable def Count_3_2 : Nat := prob_row% 3 2
theorem count_3_2 : rowFast cache64 3 2=Count_3_2 := by decide +kernel
noncomputable def Count_3_3 : Nat := prob_row% 3 3
theorem count_3_3 : rowFast cache64 3 3=Count_3_3 := by decide +kernel
noncomputable def countRow_3 (t : Nat) : Nat :=
  match t with
  | 0 => Count_3_0
  | 1 => Count_3_1
  | 2 => Count_3_2
  | 3 => Count_3_3
  | _ => 0
theorem countRow_3_checked (t : Nat) (ht : t≤3) : row 3 t=countRow_3 t := by
  rw [row_eq 3 t (by omega) ht]
  interval_cases t
  · exact count_3_0
  · exact count_3_1
  · exact count_3_2
  · exact count_3_3
noncomputable def Pair_3 : Nat := prob_pair% 3
theorem pair_3_checked : pairPacked 3=Pair_3 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (3+1), Nat.choose 3 t*countRow_3 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_3_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
