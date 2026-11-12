import SigGolfCandidate.OuterResidualMessageLaws
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualDependencyLaws
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues OuterResidualPadModel
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (childTrialDeps)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (childWTrialDeps padCoord)
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (RouterState)
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (Known childTrialDeps_keygen childWTrialDeps_keygen)
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.RouterState (known)
open OuterResidualGroundChildren (childSlots keygenDisclosed)
attribute [local instance] Classical.propDecidable

theorem padTrialDeps_keygen {index : Fin (2^31)} {coord : Fin 9} {branch : Nat} {side : Fin 2} {c : Coord}
    (hc : c∈padTrialDeps index coord branch side) : c∈keygenDisclosed := by
  unfold padTrialDeps at hc
  split at hc
  · exact OuterResidualMessageDeps.wTrialDeps_keygen hc
  · cases hc

theorem padDeps_keygen {index : Fin (2^31)} {coord : Fin 9} {branch : Nat} {c : Coord}
    (hc : c∈padDeps index coord branch) : c∈keygenDisclosed := by
  rcases List.mem_append.mp hc with hc|hc <;> exact padTrialDeps_keygen hc

theorem cellDepsP_known (st : RouterState) {N : Node}
    (hall : ∀cs∈childSlots N,OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.RouterState.known st cs.1) : ∀c∈cellDepsP N,OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.RouterState.known st c := by
  intro c hc
  cases N with
  | node n=>
    simp only [cellDepsP,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.cellDeps,OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.cellDeps.match_1,List.mem_append] at hc
    change c ∈ _ ++ _ ++ _ ++ _ at hc
    simp only [List.mem_append] at hc
    rcases hc with ((hc|hc)|hc)|hc
    · obtain ⟨cs,hcs,rfl⟩:=List.mem_map.mp hc;exact hall cs hcs
    · exact Known.base (Or.inl (OuterResidualMessageDeps.trialDeps_keygen hc))
    · exact Known.base (Or.inl (childTrialDeps_keygen hc))
    · exact Known.base (Or.inl (childTrialDeps_keygen hc))
  | wctNode n=>
    simp only [cellDepsP,List.mem_append] at hc
    rcases hc with (((hc|hc)|hc)|hc)|hc
    · obtain ⟨cs,hcs,rfl⟩:=List.mem_map.mp hc;exact hall cs hcs
    · exact Known.base (Or.inl (OuterResidualMessageDeps.wTrialDeps_keygen hc))
    · exact Known.base (Or.inl (childWTrialDeps_keygen hc))
    · exact Known.base (Or.inl (childWTrialDeps_keygen hc))
    · exact Known.base (Or.inl (padDeps_keygen hc))
  | wctLeaf L=>
    rcases List.mem_append.mp hc with hc|hc
    · obtain ⟨cs,hcs,rfl⟩:=List.mem_map.mp hc;exact hall cs hcs
    · exact Known.base (Or.inl (padDeps_keygen hc))
  | _=>obtain ⟨cs,hcs,rfl⟩:=List.mem_map.mp hc;exact hall cs hcs
#print axioms cellDepsP_known
theorem cellDepsP_sub_base (M : Node) : ∀c∈cellDepsP M,c∈cellDepsP M.base := by
  intro c hc
  cases M with
  | node m=>
    change c∈OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.cellDeps (.node m) at hc
    change c∈OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.cellDeps (.node (withNonce m 0))
    unfold OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.cellDeps at hc ⊢
    change c∈_++_++_++_ at hc
    change c∈_++_++_++_
    simp only [List.mem_append] at hc ⊢
    rcases hc with ((hc|hc)|hc)|hc
    · obtain ⟨cs,hcs,rfl⟩:=List.mem_map.mp hc
      exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨cs,OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots_sub_base (.node m) cs hcs,rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr hc))
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  | wctNode m=>
    change c∈_++_++_++_++_ at hc
    change c∈_++_++_++_++_
    simp only [List.mem_append] at hc ⊢
    rcases hc with (((hc|hc)|hc)|hc)|hc
    · obtain ⟨cs,hcs,rfl⟩:=List.mem_map.mp hc
      exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨cs,OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.childSlots_sub_base (.wctNode m) cs hcs,rfl⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
    · exact Or.inl (Or.inl (Or.inr hc))
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  | _=>exact hc
#print axioms cellDepsP_sub_base
end OuterResidualDependencyLaws
