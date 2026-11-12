import SigGolfCandidate.OuterCanonGraphBase
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterCanonGraph
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT
open ClaudeWCT.W9.T3M
open SphincsSecurity (bytesLE)
def Node.toPos : Node → Extract.Pos
  | .chain p => .chain p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val
  | .leaf L => .leaf L.1.lay L.1.tree.val L.1.leaf.val
  | .node n => .node n.1.lay n.1.tree.val n.1.level.val n.1.idx.val
  | .wctChain p => .wctChain p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
  | .wctLeaf L => .wctLeaf L.index.val L.coord.val L.child.val
  | .wctNode n => .wctNode n.1.index.val n.1.coord.val n.1.level.val n.1.idx.val
  | .forest index => .forest index.val

def wTrialCap (coord level : Nat) : Nat :=
  if level=5 then OuterGroundCore.cap coord else ClaudeWCT.W9.T3.Security.CanonGraph.wTrialCap coord level

theorem wTrialCap_pos (coord level : Nat) : 0<wTrialCap coord level := by
  unfold wTrialCap
  split
  · unfold OuterGroundCore.cap; positivity
  · exact ClaudeWCT.W9.T3.Security.CanonGraph.wTrialCap_pos coord level

theorem wTrialCap_le (coord level : Nat) : wTrialCap coord level≤4096 := by
  unfold wTrialCap
  split
  · unfold OuterGroundCore.cap OuterGroundCore.width; split <;> norm_num
  · exact (ClaudeWCT.W9.T3.Security.CanonGraph.wTrialCap_le coord level).trans (by decide)
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
/-- The 192-byte phantom cell of an inactive FTS node (first block `254`, distinct from the tree phantoms). -/
def wPhantomCode (n : WctNodePos) : Nat :=
  n.1.coord.val + 9 * (n.1.level.val + 6 * (n.1.idx.val + 64 * (n.1.nonce.val + 4096 * n.1.index.val)))
def wphantom (n : WctNodePos) : HashInput :=
  List.replicate 16 254 ++ bytesLE 16 (BitVec.ofNat 128 (wPhantomCode n)) ++ List.replicate 160 0

#print axioms wTrialCap_le
#print axioms wWithNonce_self
end OuterCanonGraph
