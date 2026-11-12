import SigGolfCandidate.OuterCanonPairedTables
import SigGolfCandidate.OuterGroundDeterministic
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction

def Agrees (answers : Answers) (labels : Labels) : Prop :=
  ∀node,answers (.inl (.inr (cell (secretsOf answers) node labels)))=labels node
theorem wctSeed_secrets (answers : Answers) (a : WctAddr) :
    Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val=wctSeedsOf (secretsOf answers) a := by
  rw [secretsOf_wct]
  rfl
section Honest
variable {answers : Answers} {labels : Labels}
theorem wctValue_eq (h : Agrees answers labels) (a : WctAddr) (s : Nat) (hs : s ≤ 4) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s = wctValueL (secretsOf answers) labels a s := by
  induction s with
  | zero =>
      unfold Extract.wctValue
      rw [WCT9.eval_chain_walk]
      change Extract.wctSeed answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val = _
      rw [wctSeed_secrets]
      rfl
  | succ s ih =>
      have ih' := ih (by omega)
      unfold Extract.wctValue at ih' ⊢
      rw [WCT9.eval_chain_walk] at ih' ⊢
      change WCT9.projAnswer answers (WCT9.ftsChainHigh a.2.2.2.val (0 + s))
        (WCT9.ftsChainInputW a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val (0 + s) (WCT9.walk _ 0 s _)) = _
      rw [ih', Nat.zero_add]
      have hcell := h (.wctChain (a, ⟨s, by omega⟩))
      simp only [cell,OuterCanonBase.cell] at hcell
      unfold WCT9.projAnswer
      rw [hcell]
      have hnode : (Node.wctChain (a, ⟨(s + 1 - 1) % 4, Nat.mod_lt _ (by decide)⟩) : Node) =
          .wctChain (a, ⟨s, by omega⟩) := by
        congr
        simp only [Nat.add_sub_cancel]
        exact Nat.mod_eq_of_lt (by omega)
      have hs4 : (s + 1 - 1) % 4 = s := by omega
      unfold wctValueL
      rw [if_neg (by omega), hnode, hs4]
theorem wctEnd_eq (h : Agrees answers labels) (a : WctAddr) :
    Extract.wctValue answers a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val 4 = wctEndLabel labels a := by
  rw [wctValue_eq h a 4 le_rfl, wctValueL_three]
theorem wctEnds_eq (h : Agrees answers labels) (L : WctLeafPos) :
    Extract.wctEnds answers L.index.val L.coord.val L.child.val =
      List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t) := by
  unfold Extract.wctEnds
  congr 1
  funext t
  exact wctEnd_eq h (L.index, L.coord, L.child, t)

end Honest
#print axioms wctEnds_eq
end OuterCanonBase.Paired
