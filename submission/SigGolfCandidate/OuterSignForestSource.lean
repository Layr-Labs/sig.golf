import SigGolfCandidate.OuterSignCoordinateSource
import SigGolfCandidate.OuterSignForest
import SigGolfCandidate.OuterForestMoment
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignForestSource
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research
open ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate
def buildNine (index : Nat) (selected : Nat → WCT9.Child) (words : Nat → WCT9.Rank) : M (List Row) :=
  (List.range 9).foldlM (fun acc c=>do
    let built←OuterForestBudget.buildCoord (SharedLeaf.first c) index c (selected c) (words c)
      (priorPads c (acc.getD (c-1) emptyRow).1)
    pure (acc++[built])) []

theorem forestProgram_source (a : BitVec 256) (ranks : Nat → WCT9.Rank) :
    OuterSignForest.forestProgram a ranks=buildNine (WCT9.digestIndex a) (fun c=>⟨chosen c a,chosen_lt c a⟩) ranks := by
  unfold OuterSignForest.forestProgram buildNine
  apply WCT9.foldlM_congr_mem
  intro acc c hc
  unfold OuterSignForest.step
  dsimp only
  rw[OuterSignCoordinateSource.source c (WCT9.digestIndex a) (List.mem_range.mp hc) ⟨chosen c a,chosen_lt c a⟩ (ranks c) (priorPads c (acc.getD (c-1) emptyRow).1)]

theorem buildNine_grouped (index : Nat) (selected : SharedForest.ForestSelection) (words : SharedForest.ForestWords) :
    forestAssembly selected <$> buildNine index (childFamily selected) (wordFamily words)=
      OuterForestMoment.forest index selected words := by
  have hn:List.range 9=[0,1,2,3,4,5,6,7,8]:=by decide
  have hp:List.finRange 4=[0,1,2,3]:=by decide
  simp only[buildNine,OuterForestMoment.forest,hn,hp,List.foldlM_cons,List.foldlM_nil,
    OuterForestMoment.pair,OuterForestMoment.singleton,bind_assoc,pure_bind,map_eq_bind_pure_comp,Function.comp_def]
  apply bind_congr
  intro row0
  apply bind_congr
  intro row1
  apply bind_congr
  intro row2
  apply bind_congr
  intro row3
  apply bind_congr
  intro row4
  apply bind_congr
  intro row5
  apply bind_congr
  intro row6
  apply bind_congr
  intro row7
  apply bind_congr
  intro row8
  apply congrArg pure
  unfold forestAssembly
  apply Prod.ext
  · refine congrArg₂ SharedForest.ForestOpening.mk ?_ rfl
    funext p
    fin_cases p <;> rfl
  · rfl
theorem forestProgram_output (a : BitVec 256) :
    forestAssembly (SharedForest.forestSelectionFromOutput a) <$>
      OuterSignForest.forestProgram a (SharedForest.forestRank a) =
      OuterForestMoment.forest (WCT9.digestIndex a) (SharedForest.forestSelectionFromOutput a)
        (SharedForest.forestWordsFromOutput a) := by
  rw [forestProgram_source]
  have h : buildNine (WCT9.digestIndex a) (fun c=>⟨chosen c a,chosen_lt c a⟩)
      (SharedForest.forestRank a) = buildNine (WCT9.digestIndex a)
      (childFamily (SharedForest.forestSelectionFromOutput a))
      (wordFamily (SharedForest.forestWordsFromOutput a)) := by
    unfold buildNine
    apply WCT9.foldlM_congr_mem
    intro acc c hc
    rw [childFamily_output a c (List.mem_range.mp hc),wordFamily_output a c (List.mem_range.mp hc)]
  rw [h,buildNine_grouped]

#print axioms forestProgram_source
#print axioms buildNine_grouped
#print axioms forestProgram_output
end OuterSignForestSource
