import SigGolfCandidate.Cap776.CountRow3
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
noncomputable def Count_4_0 : Nat := prob_row% 4 0
theorem count_4_0 : rowFast cache64 4 0=Count_4_0 := by decide +kernel
noncomputable def Count_4_1 : Nat := prob_row% 4 1
theorem count_4_1 : rowFast cache64 4 1=Count_4_1 := by decide +kernel
noncomputable def Count_4_2 : Nat := prob_row% 4 2
theorem count_4_2 : rowFast cache64 4 2=Count_4_2 := by decide +kernel
noncomputable def Count_4_3 : Nat := prob_row% 4 3
theorem count_4_3 : rowFast cache64 4 3=Count_4_3 := by decide +kernel
noncomputable def Count_4_4 : Nat := prob_row% 4 4
theorem count_4_4 : rowFast cache64 4 4=Count_4_4 := by decide +kernel
noncomputable def countRow_4 (t : Nat) : Nat :=
  match t with
  | 0 => Count_4_0
  | 1 => Count_4_1
  | 2 => Count_4_2
  | 3 => Count_4_3
  | 4 => Count_4_4
  | _ => 0
theorem countRow_4_checked (t : Nat) (ht : t≤4) : row 4 t=countRow_4 t := by
  rw [row_eq 4 t (by omega) ht]
  interval_cases t
  · exact count_4_0
  · exact count_4_1
  · exact count_4_2
  · exact count_4_3
  · exact count_4_4
noncomputable def Pair_4 : Nat := prob_pair% 4
theorem pair_4_checked : pairPacked 4=Pair_4 := by
  unfold pairPacked
  calc _ = ∑ t ∈ Finset.range (4+1), Nat.choose 4 t*countRow_4 t := by
         apply Finset.sum_congr rfl
         intro t ht
         rw [countRow_4_checked t (by have h := Finset.mem_range.mp ht; omega)]
       _ = _ := by decide +kernel

end SigGolfResearch.ProbabilityCache
