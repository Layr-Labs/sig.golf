import SigGolfCandidate.Cap776.CountRow1
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
noncomputable def Count_2_0 : Nat := prob_row% 2 0
theorem count_2_0 : rowFast cache64 2 0=Count_2_0 := by decide +kernel
noncomputable def Count_2_1 : Nat := prob_row% 2 1
theorem count_2_1 : rowFast cache64 2 1=Count_2_1 := by decide +kernel
noncomputable def Count_2_2 : Nat := prob_row% 2 2
theorem count_2_2 : rowFast cache64 2 2=Count_2_2 := by decide +kernel
noncomputable def countRow_2 (t : Nat) : Nat :=
  match t with
  | 0 => Count_2_0
  | 1 => Count_2_1
  | 2 => Count_2_2
  | _ => 0
theorem countRow_2_checked (t : Nat) (ht : t≤2) : row 2 t=countRow_2 t := by
  rw [row_eq 2 t (by omega) ht]
  interval_cases t
  · exact count_2_0
  · exact count_2_1
  · exact count_2_2
noncomputable def Pair_2 : Nat := prob_pair% 2
theorem pair_2_checked : pairPacked 2=Pair_2 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (2+1), Nat.choose 2 t*countRow_2 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_2_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
