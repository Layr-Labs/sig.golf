import SigGolfCandidate.OuterCanonFiltered
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonWorldBase
open ClaudeWCT
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs
open OuterCanonBase
open Correctness (Answers)
def Hidden (node : Node) : Prop := ∃ a : WctAddr, ∃ q : Fin 4, q.val < 3 ∧ node = .wctChain (a, q)
theorem treeLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold treeLabel
  split_ifs with hzero
  · cases leafAt lay tree c with
    | none => rfl
    | some L => simp only; rw [hn _ (fun _ => Node.noConfusion)]
  · cases treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n => simp only; rw [selNode_label_congr (fun j _ => hn _ (fun _ => Node.noConfusion))]
theorem ftsLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  have hn : ∀ node : Node, (∀ q, node ≠ .wctChain q) → left node = right node := fun node hq =>
    h node (fun ⟨a, q, _, he⟩ => hq (a, q) he)
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [hn _ (fun _ => Node.noConfusion)]
  · rfl
  all_goals
    cases ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n => simp only; rw [hn _ (fun _ => Node.noConfusion)]
theorem ftsPrevLabel_outer (left right : Labels) (h : ∀ node, ¬Hidden node → left node = right node)
    (index : Fin (2^31)) (coord : Fin 9) :
    ftsPrevLabel left index coord = ftsPrevLabel right index coord := by
  unfold ftsPrevLabel
  split_ifs
  · rfl
  · rw [ftsLabel_outer left right h, ftsLabel_outer left right h]
theorem cell_outer (secrets secrets' : Secrets) (labels labels' : Labels)
    (hs : ∀ a, secrets (.inl a) = secrets' (.inl a)) (hl : ∀ node, ¬Hidden node → labels node = labels' node)
    (node : Node) (hnode : ∀ q, node ≠ .wctChain q) :
    cell secrets node labels = cell secrets' node labels' := by
  have hseeds : seedsOf secrets = seedsOf secrets' := by
    have hf : leafFamily secrets = leafFamily secrets' :=
      funext fun lay => funext fun tree => funext fun leaf => funext fun j => hs _
    funext a
    unfold seedsOf
    rw [hf]
  have hchain : chainLabels labels = chainLabels labels' :=
    funext fun point => hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he)
  cases node with
  | chain p =>
      change inputW (seedsOf secrets) p (chainLabels labels) =
        inputW (seedsOf secrets') p (chainLabels labels')
      rw [hseeds, hchain]
  | leaf L =>
      have hends : (List.range (chainCount L.1.lay)).map (endLabel secrets labels L.1) =
          (List.range (chainCount L.1.lay)).map (endLabel secrets' labels' L.1) := by
        apply List.map_congr_left
        intro i _
        unfold endLabel
        rw [hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he)]
      simp only [cell, hends]
  | node n =>
      have ha : Active labels n ↔ Active labels' n :=
        activeCongr labels labels' n (fun j _ => hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he))
      simp only [cell, treeLabel_outer labels labels' hl, ha]
  | wctChain p => exact absurd rfl (hnode p)
  | wctLeaf L =>
      have hends : (List.ofFn fun t : Fin 6 => wctEndLabel labels (L.index, L.coord, L.child, t)) =
          (List.ofFn fun t : Fin 6 => wctEndLabel labels' (L.index, L.coord, L.child, t)) := by
        congr 1
        funext t
        unfold wctEndLabel
        rw [hl _ (fun ⟨a, q, hq, he⟩ => by
          simp only [Node.wctChain.injEq, Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he
          exact absurd hq (by decide))]
      simp only [cell, hends, ftsPrevLabel_outer labels labels' hl]
  | wctNode n =>
      have ha : WActive labels n ↔ WActive labels' n :=
        wActiveCongr labels labels' n (fun j _ => hl _ (fun ⟨a, q, _, he⟩ => Node.noConfusion he))
      simp only [cell, ftsLabel_outer labels labels' hl, ftsPrevLabel_outer labels labels' hl, ha]
  | forest index =>
      simp only [cell, ftsLabel_outer labels labels' hl]

#print axioms cell_outer
end OuterCanonWorldBase
