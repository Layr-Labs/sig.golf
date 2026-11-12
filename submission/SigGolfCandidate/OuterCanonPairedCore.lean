import SigGolfCandidate.OuterCanonBase
import SigGolfCandidate.OuterExtractBounds
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option maxErrors 30
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
attribute [local instance] Classical.propDecidable
def wTrialCap (coord level : Nat) : Nat :=
  if level=5 ∧ Extract.Paired.first coord=false then OuterGroundCore.cap coord else OuterCanonBase.wTrialCap coord level

theorem wTrialCap_pos (coord level : Nat) : 0<wTrialCap coord level := by
  unfold wTrialCap
  split
  · unfold OuterGroundCore.cap; positivity
  · exact OuterCanonBase.wTrialCap_pos coord level

theorem wTrialCap_le (coord level : Nat) : wTrialCap coord level≤4096 := by
  unfold wTrialCap
  split
  · unfold OuterGroundCore.cap OuterGroundCore.width; split <;> norm_num
  · exact (OuterCanonBase.wTrialCap_le coord level).trans (by decide)
def wWithNonce (n : WctNodePos) (j : Nat) : WctNodePos :=
  ⟨{ n.1 with nonce := ⟨j % 4096, Nat.mod_lt _ (by decide)⟩ }, n.2⟩
theorem wWithNonce_nonce (n : WctNodePos) {j : Nat} (hj : j < 4096) : (wWithNonce n j).1.nonce.val = j := by
  simp [wWithNonce, Nat.mod_eq_of_lt hj]
@[simp] theorem wWithNonce_index (n : WctNodePos) (j : Nat) : (wWithNonce n j).1.index = n.1.index := rfl
@[simp] theorem wWithNonce_coord (n : WctNodePos) (j : Nat) : (wWithNonce n j).1.coord = n.1.coord := rfl
@[simp] theorem wWithNonce_level (n : WctNodePos) (j : Nat) : (wWithNonce n j).1.level = n.1.level := rfl
@[simp] theorem wWithNonce_idx (n : WctNodePos) (j : Nat) : (wWithNonce n j).1.idx = n.1.idx := rfl
theorem wWithNonce_wWithNonce (n : WctNodePos) (i j : Nat) : wWithNonce (wWithNonce n i) j = wWithNonce n j := rfl
theorem wWithNonce_self (n : WctNodePos) : wWithNonce n n.1.nonce.val = n := by
  obtain ⟨⟨index, coord, level, idx, nonce⟩, hv⟩ := n
  simp [wWithNonce, Nat.mod_eq_of_lt nonce.isLt]
/-- Two FTS nodes of one position with the same nonce coincide. -/
theorem wctNode_eq_of {n m : WctNodePos} (hb : wWithNonce n 0 = wWithNonce m 0)
    (hk : n.1.nonce.val = m.1.nonce.val) : n = m := by
  rw [← wWithNonce_self n, ← wWithNonce_self m, ← wWithNonce_wWithNonce n 0, ← wWithNonce_wWithNonce m 0, hb, hk]
/-- Trial `j` of the position of `n` fails the ground zero test of its level (on the used half of its label). -/
def wTrialFails (labels : Labels) (n : WctNodePos) (j : Nat) : Prop :=
  (if n.1.level.val=5 then OuterGroundCore.zeroOk n.1.coord.val else
    WCT9.ftsZeroOk n.1.coord.val (2 ^ (6 - n.1.level.val)))
    (Extract.Paired.proj (Node.wctNode n).toPos (labels (.wctNode (wWithNonce n j)))) = false
instance (labels : Labels) (n : WctNodePos) (j : Nat) : Decidable (wTrialFails labels n j) := by
  unfold wTrialFails; infer_instance
/-- FTS node `n` is an active trial: inside the cap, and every earlier trial of its position failed. -/
def WActive (labels : Labels) (n : WctNodePos) : Prop :=
  n.1.nonce.val < wTrialCap n.1.coord.val n.1.level.val ∧ ∀ j < n.1.nonce.val, wTrialFails labels n j
instance (labels : Labels) (n : WctNodePos) : Decidable (WActive labels n) := by unfold WActive; infer_instance
/-- The selected nonce of the position of `n`: the first passing trial, the last trial when none passes. -/
def wSelNonce (labels : Labels) (n : WctNodePos) : Nat :=
  ((List.range (wTrialCap n.1.coord.val n.1.level.val)).find? fun j => !decide (wTrialFails labels n j)).getD
    (wTrialCap n.1.coord.val n.1.level.val - 1)
/-- The selected trial of the position of `n`. -/
def wSelNode (labels : Labels) (n : WctNodePos) : WctNodePos := wWithNonce n (wSelNonce labels n)
def PhantomAt (node : Node) (labels : Labels) : Prop :=
  (∃ n, node = .node n ∧ ¬ Active labels n) ∨ (∃ m, node = .wctNode m ∧ ¬ WActive labels m)
/-- The phantom cell of a tree or FTS node. -/

theorem phantomOf_length {node : Node} {labels : Labels} (h : PhantomAt node labels) :
    (phantomOf node).length = 192 := by
  rcases h with ⟨n, rfl, -⟩ | ⟨m, rfl, -⟩
  · exact phantom_length n
  · exact wphantom_length m

theorem posOf_phantomOf {node : Node} {labels : Labels} (h : PhantomAt node labels) :
    Extract.posOf (phantomOf node) = none := by
  rcases h with ⟨n, rfl, -⟩ | ⟨m, rfl, -⟩
  · exact posOf_phantom n
  · exact posOf_wphantom m

theorem phantomOf_inj {left right : Node} {before after : Labels} (hl : PhantomAt left before)
    (hr : PhantomAt right after) (h : phantomOf left = phantomOf right) : left = right := by
  rcases hl with ⟨n, rfl, -⟩ | ⟨m, rfl, -⟩ <;> rcases hr with ⟨n', rfl, -⟩ | ⟨m', rfl, -⟩
  · exact congrArg Node.node (phantom_injective h)
  · exact absurd h (phantom_ne_wphantom n m')
  · exact absurd h.symm (phantom_ne_wphantom n' m)
  · exact congrArg Node.wctNode (wphantom_injective h)

theorem not_phantomAt_node {n : TreeNode} {labels : Labels} (h : Active labels n) : ¬ PhantomAt (.node n) labels := by
  rintro (⟨m, hm, hn⟩ | ⟨m, hm, -⟩)
  · cases hm
    exact hn h
  · cases hm

theorem not_phantomAt_wctNode {n : WctNodePos} {labels : Labels} (h : WActive labels n) :
    ¬ PhantomAt (.wctNode n) labels := by
  rintro (⟨m, hm, -⟩ | ⟨m, hm, hn⟩)
  · cases hm
  · cases hm
    exact hn h

theorem active_of_not_phantomAt {n : TreeNode} {labels : Labels} (h : ¬ PhantomAt (.node n) labels) :
    Active labels n := by
  by_contra ha; exact h (Or.inl ⟨n, rfl, ha⟩)

theorem wActive_of_not_phantomAt {n : WctNodePos} {labels : Labels} (h : ¬ PhantomAt (.wctNode n) labels) :
    WActive labels n := by
  by_contra ha; exact h (Or.inr ⟨n, rfl, ha⟩)
/-- Every non-phantom cell has its position's honest length (length-aware decoding, C3). -/

theorem wActive_nonce_zero {labels : Labels} {n : WctNodePos} (h : WActive labels n)
    (h3 : ¬OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val) : n.1.nonce.val=0 := by
  have houter : ¬(n.1.level.val=5 ∧ Extract.Paired.first n.1.coord.val=false):=fun ho=>h3 (Or.inr ho)
  have ho : ¬Extract.Paired.ftsNonceLevel n.1.coord.val n.1.level.val:=fun h=>h3 (Or.inl h)
  have hh:=h.1
  simp only [wTrialCap,if_neg houter,OuterCanonBase.wTrialCap,if_neg ho] at hh
  omega
theorem wctNode_eq_of_pad {n m : WctNodePos} {before after : Labels} (ha : WActive before n) (hb : WActive after m)
    (hw : wWithNonce n 0 = wWithNonce m 0)
    (hp : OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val →
      BitVec.ofNat 128 (n.1.nonce.val % 2 ^ 64) = BitVec.ofNat 128 (m.1.nonce.val % 2 ^ 64)) : n = m := by
  apply wctNode_eq_of hw
  have hl : n.1.level = m.1.level := by
    have := congrArg (fun x : WctNodePos => x.1.level) hw
    exact this
  have hc : n.1.coord = m.1.coord := by
    have := congrArg (fun x : WctNodePos => x.1.coord) hw
    exact this
  by_cases h3 : OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val
  · exact ofNat_nonce_inj n.1.nonce.isLt m.1.nonce.isLt (hp h3)
  · rw [wActive_nonce_zero ha h3, wActive_nonce_zero hb (by rw [← hl, ← hc]; exact h3)]
/-- Separation of the trial-node graph (phantoms included). -/
def first (coord : Nat) : Prop := coord<8 ∧ coord%2=0
instance (coord : Nat) : Decidable (first coord) := by unfold first;infer_instance
/-- Inverse of the fixed physical placement used by B and C trees. -/
def rawLeaf (coord physical : Nat) : Nat :=
  if first coord then physical else 2*(physical%64)+physical/64

def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (level physical : Nat) : Digest :=
  if level=0 then
    if h:rawLeaf coord.val physical<128 then
      Extract.Paired.proj (.wctLeaf index.val coord.val (rawLeaf coord.val physical))
        (labels (.wctLeaf ⟨index,coord,⟨rawLeaf coord.val physical,h⟩⟩))
    else 0
  else
    match ftsNodeAt index coord (level-1) physical with
    | some n=>Extract.Paired.proj (.wctNode index.val coord.val (level-1) physical)
        (labels (.wctNode (wSelNode labels n)))
    | none=>0

/-- A and C bind the preceding pair; B binds the selected A branch. -/
def pads (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) : Digest×Digest :=
  if h:coord.val=0 then (0,0) else
    let previous : Fin 9:=⟨coord.val-1,by have:=coord.isLt;omega⟩
    if coord.val%2=1 then
      (ftsLabel labels index previous 5 (2*branch),ftsLabel labels index previous 5 (2*branch+1))
    else (ftsLabel labels index previous 6 0,ftsLabel labels index previous 6 1)

def cell (secrets : Secrets) : Node→Labels→HashInput
  | .wctLeaf L,labels=>pad64 (Extract.wctLeafInputP L.index.val L.coord.val L.child.val
      (pads labels L.index L.coord (L.child.val%2)).1
      (List.ofFn fun t:Fin 6=>wctEndLabel labels (L.index,L.coord,L.child,t)))
  | .wctNode n,labels=>if WActive labels n then pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2^(7-n.1.level.val-1)+n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val))
      (if n.1.level.val=4 then (pads labels n.1.index n.1.coord (n.1.idx.val/2)).2
        else if OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val then
          BitVec.ofNat 128 (n.1.nonce.val % 2 ^ 64) else 0)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1))) else wphantom n
  | node,labels=>OuterCanonBase.cell secrets node labels

theorem cell_wctNode_active {secrets : Secrets} {n : WctNodePos} {labels : Labels} (h : WActive labels n) :
    cell secrets (.wctNode n) labels = pad64 (nodeInputP 3 (WCT9.nodeLayer n.1.coord.val) n.1.index.val
      (2^(7-n.1.level.val-1)+n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val))
      (if n.1.level.val=4 then (pads labels n.1.index n.1.coord (n.1.idx.val/2)).2
        else if OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val then
          BitVec.ofNat 128 (n.1.nonce.val % 2 ^ 64) else 0)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1))) := by
  simp only [cell, if_pos h]
theorem cell_wctNode_inactive {secrets : Secrets} {n : WctNodePos} {labels : Labels} (h : ¬ WActive labels n) :
    cell secrets (.wctNode n) labels = wphantom n := by
  simp only [cell, if_neg h]
/-- The Paired cell of a phantom node is its phantom cell. -/
theorem cell_of_phantomAt {secrets : Secrets} {node : Node} {labels : Labels} (h : PhantomAt node labels) :
    cell secrets node labels = phantomOf node := by
  rcases h with ⟨n, rfl, hn⟩ | ⟨m, rfl, hm⟩
  · exact OuterCanonBase.cell_node_inactive (secrets := secrets) hn
  · exact cell_wctNode_inactive hm

theorem base_nonPhantom {node : Node} {labels : Labels} (h : ¬PhantomAt node labels)
    (hn : ∀n,node≠Node.wctNode n) : ¬OuterCanonBase.PhantomAt node labels := by
  rintro (⟨n,rfl,ha⟩|⟨n,he,_⟩)
  · exact h (Or.inl ⟨n,rfl,ha⟩)
  · exact hn n he

theorem hdrBlock_cell (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    Extract.hdrBlock (cell secrets node labels)=bytesLE 16 node.toPos.hdr := by
  cases node with
  | wctLeaf L=>
    simp only [cell]
    rw [Extract.hdrBlock_wctLeafInputP]
    rfl
  | wctNode n=>
    rw [cell_wctNode_active (wActive_of_not_phantomAt hp), Extract.hdrBlock_nodeInputP]
    rfl
  | chain v=>exact OuterCanonBase.hdrBlock_cell secrets (.chain v) labels (base_nonPhantom hp (by intro n he;cases he))
  | leaf v=>exact OuterCanonBase.hdrBlock_cell secrets (.leaf v) labels (base_nonPhantom hp (by intro n he;cases he))
  | node v=>exact OuterCanonBase.hdrBlock_cell secrets (.node v) labels (base_nonPhantom hp (by intro n he;cases he))
  | wctChain v=>exact OuterCanonBase.hdrBlock_cell secrets (.wctChain v) labels (base_nonPhantom hp (by intro n he;cases he))
  | forest v=>exact OuterCanonBase.hdrBlock_cell secrets (.forest v) labels (base_nonPhantom hp (by intro n he;cases he))

theorem cell_length (secrets : Secrets) (node : Node) (labels : Labels) (hp : ¬ PhantomAt node labels) :
    (cell secrets node labels).length=node.toPos.len := by
  cases node with
  | wctLeaf L=>
    simp only [cell,Extract.wctLeafInputP,Node.toPos,Extract.Pos.len]
    rw [Cost.pad64_length,Extract.listInput_length']
    simp only [List.length_cons,List.length_drop,List.length_ofFn]
  | wctNode n=>
    rw [cell_wctNode_active (wActive_of_not_phantomAt hp)]
    simp only [Node.toPos,Extract.Pos.len]
    rw [pad64_nodeInputP,nodeInputP,block4]
    simp only [List.length_append,bytesLE_length]
  | chain v=>exact OuterCanonBase.cell_length secrets (.chain v) labels (base_nonPhantom hp (by intro n he;cases he))
  | leaf v=>exact OuterCanonBase.cell_length secrets (.leaf v) labels (base_nonPhantom hp (by intro n he;cases he))
  | node v=>exact OuterCanonBase.cell_length secrets (.node v) labels (base_nonPhantom hp (by intro n he;cases he))
  | wctChain v=>exact OuterCanonBase.cell_length secrets (.wctChain v) labels (base_nonPhantom hp (by intro n he;cases he))
  | forest v=>exact OuterCanonBase.cell_length secrets (.forest v) labels (base_nonPhantom hp (by intro n he;cases he))

/-- The Paired cell differs from the base cell only on FTS leaves and nodes (never phantoms). -/
theorem cell_node (secrets : Secrets) (n : TreeNode) (labels : Labels) :
    cell secrets (.node n) labels = OuterCanonBase.cell secrets (.node n) labels := rfl
theorem cell_separated (secrets : Secrets) : Separated (cell secrets) := by
  intro left right hne before after heq
  -- A tree node with the same cell: both are tree nodes (phantoms only collide with phantoms; a non-phantom
  -- tree-node cell decodes to a tree position). Reduce to the base separation there.
  by_cases hl : PhantomAt left before
  · have hn := cell_of_phantomAt (secrets := secrets) hl
    by_cases hr : PhantomAt right after
    · have hm := cell_of_phantomAt (secrets := secrets) hr
      rw [hn, hm] at heq
      exact hne (phantomOf_inj hl hr heq)
    · have h1 := cell_length secrets right after hr
      rw [← heq, hn, phantomOf_length hl] at h1
      exact Pos.len_ne_192 _ h1.symm
  · by_cases hr : PhantomAt right after
    · have hm := cell_of_phantomAt (secrets := secrets) hr
      have h1 := cell_length secrets left before hl
      rw [heq, hm, phantomOf_length hr] at h1
      exact Pos.len_ne_192 _ h1.symm
    · have h1 := hdrBlock_cell secrets left before hl
      have h2 := hdrBlock_cell secrets right after hr
      have hlen : left.toPos.len = right.toPos.len := by
        rw [← cell_length secrets left before hl, ← cell_length secrets right after hr, heq]
      rw [heq] at h1
      have hpos := Extract.Pos.hdr_injective (toPos_bounded left) (toPos_bounded right) hlen
        (bytesLE_injective (h1.symm.trans h2))
      have hb := toPos_injective_base hpos
      cases left with
      | node n =>
          cases right with
          | node m => exact OuterCanonBase.cell_separated secrets _ _ hne before after heq
          | _ => simp [Node.base] at hb
      | wctNode n =>
          cases right with
          | wctNode m =>
              have ha := wActive_of_not_phantomAt hl
              have hb' := wActive_of_not_phantomAt hr
              have hw : wWithNonce n 0 = wWithNonce m 0 := Node.wctNode.inj hb
              have hlv : n.1.level = m.1.level := by
                have := congrArg (fun x : WctNodePos => x.1.level) hw
                exact this
              rw [cell_wctNode_active ha, cell_wctNode_active hb', pad64_nodeInputP, pad64_nodeInputP] at heq
              apply hne
              have hco : n.1.coord = m.1.coord := by
                have := congrArg (fun x : WctNodePos => x.1.coord) hw
                exact this
              rw [wctNode_eq_of_pad ha hb' hw (fun h3 => by
                have hp := nodeInputP_pad_eq heq
                have hne4 : n.1.level.val≠4 := by
                  rcases h3 with h|h
                  · unfold Extract.Paired.ftsNonceLevel at h;omega
                  · omega
                have h3' : OuterExtractGround.ftsNonceLevel m.1.coord.val m.1.level.val := by rw [← hlv, ← hco]; exact h3
                rwa [if_neg (show n.1.level.val ≠ 4 by omega), if_pos h3,
                  if_neg (show m.1.level.val ≠ 4 by rw [← hlv]; omega), if_pos h3'] at hp)]
          | _ => simp [Node.base] at hb
      | _ =>
          cases right <;> first
            | exact hne hb
            | (simp [Node.base] at hb)


#print axioms cell_separated
end OuterCanonBase.Paired
