import SigGolfCandidate.OuterResidualDependencyLaws
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualPadCongruence
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues OuterResidualPadModel
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (wTrialDeps wTrialCoord mem_wTrialDeps)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (padCoord ftsChild)
attribute [local instance] Classical.propDecidable

theorem padCoord_nonce {index : Fin (2^31)} {coord : Fin 9} {branch : Nat} {side : Fin 2} {c : Coord}
    (hc : padCoord index coord branch side=some c) : ∃n : WctNodePos,c=.inl (.wctNode n) ∧ n.1.nonce.val=0 := by
  unfold padCoord at hc
  split_ifs at hc with hz ho
  all_goals
    unfold ftsChild at hc
    simp only [if_false,show (5:Nat)≠0 by decide,show (6:Nat)≠0 by decide,ite_false] at hc
    obtain ⟨n,hn,he⟩:=Option.map_eq_some_iff.mp hc
    refine ⟨n,he.symm,?_⟩
    unfold ftsNodeAt at hn
    split_ifs at hn
    cases hn
    rfl

private theorem map_eq_of_pointwise (o : Option Coord) (f g : Coord → Digest)
    (h : ∀c,o=some c → f c=g c) : o.map f=o.map g := by
  cases o with
  | none=>rfl
  | some c=>exact congrArg some (h c rfl)

theorem selectedWct_congr (v w : Coord → Digest) (n : WctNodePos) (hn : n.1.nonce.val=0)
    (h0 : v (.inl (.wctNode n))=w (.inl (.wctNode n)))
    (ht : ∀j<Paired.wTrialCap n.1.coord.val n.1.level.val,
      Paired.wTrialCap n.1.coord.val n.1.level.val≠1 → v (wTrialCoord n j)=w (wTrialCoord n j)) :
    selVals v (.inl (.wctNode n))=selVals w (.inl (.wctNode n)) := by
  change v (.inl (.wctNode (Paired.wWithNonce n (wSelNonceV v n))))=
    w (.inl (.wctNode (Paired.wWithNonce n (wSelNonceV w n))))
  by_cases h1 : Paired.wTrialCap n.1.coord.val n.1.level.val=1
  · rw [OuterResidualValueLaws.wSelNonceV_cap_one (v:=v) h1,OuterResidualValueLaws.wSelNonceV_cap_one (v:=w) h1]
    have hself:=Paired.wWithNonce_self n
    rw [hn] at hself
    rw [hself]
    exact h0
  · rw [OuterResidualValueLaws.wSelNonceV_congr (fun j hj=>ht j hj h1)]
    exact ht _ (OuterResidualValueLaws.wSelNonceV_lt w n) h1

theorem padValue_congr (v w : Coord → Digest) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (side : Fin 2)
    (h0 : ∀c,padCoord index coord branch side=some c → v c=w c)
    (hd : ∀c∈padTrialDeps index coord branch side,v c=w c) :
    ((padCoord index coord branch side).map (selVals v)).getD 0=
      ((padCoord index coord branch side).map (selVals w)).getD 0 := by
  apply congrArg (fun o : Option Digest=>o.getD 0)
  apply map_eq_of_pointwise
  intro c hp
  obtain ⟨n,he,hn⟩:=padCoord_nonce hp
  have hp' : padCoord index coord branch side=some (.inl (.wctNode n)):=hp.trans (congrArg some he)
  rw [he]
  apply selectedWct_congr v w n hn
  · exact h0 _ hp'
  · intro j hj h1
    apply hd
    unfold padTrialDeps
    rw [hp']
    exact mem_wTrialDeps h1 hj
#print axioms padValue_congr
end OuterResidualPadCongruence
