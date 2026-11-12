import SigGolfCandidate.OuterCanonWorldBase
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonWorld
open ClaudeWCT
open OracleComp OracleSpec
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs
open OuterCanonBase
open Correctness (Answers)
abbrev Hidden:=OuterCanonWorldBase.Hidden

theorem treeLabel_outer (left right : Labels) (h : ∀node,¬Hidden node→left node=right node)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel left lay tree level c=treeLabel right lay tree level c :=
  OuterCanonWorldBase.treeLabel_outer left right h lay tree level c

theorem ftsLabel_outer (left right : Labels) (h : ∀node,¬Hidden node→left node=right node)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    Paired.ftsLabel left index coord level c=Paired.ftsLabel right index coord level c := by
  have hn : ∀node : Node,(∀q,node≠.wctChain q)→left node=right node:=fun node hq=>
    h node (fun ⟨a,q,_,he⟩=>hq (a,q) he)
  unfold Paired.ftsLabel
  split_ifs with hz hc
  · rw [hn _ (fun _=>Node.noConfusion)]
  · rfl
  all_goals
    cases ftsNodeAt index coord (level-1) c with
    | none=>rfl
    | some n=>
      simp only
      rw [Paired.wSelNode_label_congr (fun j _=>hn _ (fun _=>Node.noConfusion))]

theorem ftsPrevLabel_outer (left right : Labels) (h : ∀node,¬Hidden node→left node=right node)
    (index : Fin (2^31)) (coord : Fin 9) :
    ftsPrevLabel left index coord=ftsPrevLabel right index coord :=
  OuterCanonWorldBase.ftsPrevLabel_outer left right h index coord

theorem pads_outer (left right : Labels) (h : ∀node,¬Hidden node→left node=right node)
    (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) :
    Paired.pads left index coord branch=Paired.pads right index coord branch := by
  unfold Paired.pads
  split
  · rfl
  · split <;> dsimp only <;> rw [ftsLabel_outer left right h,ftsLabel_outer left right h]

theorem cell_outer (secrets secrets' : Secrets) (labels labels' : Labels)
    (hs : ∀a,secrets (.inl a)=secrets' (.inl a))
    (hl : ∀node,¬Hidden node→labels node=labels' node)
    (node : Node) (hnode : ∀q,node≠.wctChain q) :
    Paired.cell secrets node labels=Paired.cell secrets' node labels' := by
  have hb:=OuterCanonWorldBase.cell_outer secrets secrets' labels labels' hs hl node hnode
  cases node with
  | wctLeaf L=>
    have he : (List.ofFn fun t : Fin 6=>wctEndLabel labels (L.index,L.coord,L.child,t))=
        (List.ofFn fun t : Fin 6=>wctEndLabel labels' (L.index,L.coord,L.child,t)) := by
      congr 1
      funext t
      unfold wctEndLabel
      rw [hl _ (fun ⟨a,q,hq,he⟩=>by
        simp only [Node.wctChain.injEq,Prod.mk.injEq] at he
        obtain ⟨-,rfl⟩:=he
        exact absurd hq (by decide))]
    simp only [Paired.cell,he,pads_outer labels labels' hl]
  | wctNode n=>
    have ha : Paired.WActive labels n↔Paired.WActive labels' n:=
      Paired.wActiveCongr labels labels' n (fun j _=>hl _ (fun ⟨a,q,_,he⟩=>Node.noConfusion he))
    simp only [Paired.cell,ftsLabel_outer labels labels' hl,pads_outer labels labels' hl,ha]
  | chain p=>exact hb
  | leaf p=>exact hb
  | node p=>exact hb
  | wctChain p=>exact (hnode p rfl).elim
  | forest p=>exact hb
#print axioms ftsLabel_outer
#print axioms cell_outer
end OuterCanonWorld
