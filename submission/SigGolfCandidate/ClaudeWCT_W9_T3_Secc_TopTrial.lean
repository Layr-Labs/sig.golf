import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_CanonGraph
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEvents
set_option Elab.async false

/-! # Top-nonce layer: the honest nonce search agrees with the trial graph (r3-lean-nonsec)

Under agreement on tree nodes, the keygen nonce search of a top position returns the selected trial `selNonce`, and
the honest tree value of a position is the used half of its selected trial's label (`tree_step`). Every trial up to
the selected one is active, so its cell is the honest trial input. -/
namespace ClaudeWCT.W9.T3.Security.CanonGraph
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem trialFails_withNonce (labels : Labels) (n : TreeNode) (k j : Nat) :
    trialFails labels (withNonce n k) j ↔ trialFails labels n j := Iff.rfl

theorem selNonce_spec (labels : Labels) (n : TreeNode) :
    (∀ j < selNonce labels n, trialFails labels n j) ∧
      (¬ trialFails labels n (selNonce labels n) ∨
        selNonce labels n = trialCap n.1.lay n.1.level.val - 1) := by
  unfold selNonce
  cases hf : (List.range (trialCap n.1.lay n.1.level.val)).find? (fun j => !decide (trialFails labels n j)) with
  | none =>
      have hall : ∀ i, i < trialCap n.1.lay n.1.level.val → trialFails labels n i := by
        intro i hi
        have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
        simpa using this
      have hpos := trialCap_pos n.1.lay n.1.level.val
      refine ⟨fun j hj => hall j ?_, Or.inr rfl⟩
      simp only [Option.getD_none] at hj
      omega
  | some i =>
      rw [List.find?_range_eq_some] at hf
      obtain ⟨hp, -, hlt⟩ := hf
      simp only [Option.getD_some]
      exact ⟨fun j hj => by simpa using hlt j hj, Or.inl (by simpa using hp)⟩

/-- Every trial up to the selected one is active. -/
theorem active_trial_of_le {labels : Labels} {n : TreeNode} {k : Nat} (hk : k ≤ selNonce labels n) :
    Active labels (withNonce n k) := by
  have hs := selNonce_lt labels n
  have hc := trialCap_le n.1.lay n.1.level.val
  refine ⟨?_, fun j hj => ?_⟩
  · rw [withNonce_nonce n (by omega)]; exact lt_of_le_of_lt hk hs
  · rw [withNonce_nonce n (by omega)] at hj
    exact (trialFails_withNonce labels n k j).2 ((selNonce_spec labels n).1 j (by omega))

/-- The nonce search returns the first passing trial `s` (or the last one) once its values are known up to `s`. -/
theorem eval_topNonceSearch_eq (answers : Answers) (h heap : Nat) (left right : Digest) (v : Nat → Digest)
    (hv : ∀ k, evalWithAnswerFn answers (topNodeHashN heap k left right) = v k) :
    ∀ fuel n s, n ≤ s → s ≤ n + fuel → (∀ k, n ≤ k → k < s → topZeroOk h (v k) = false) →
      (topZeroOk h (v s) = true ∨ s = n + fuel) →
      evalWithAnswerFn answers (topNonceSearch h heap left right fuel n) = (s, v s) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n s h1 h2 _ _
      have : s = n := by omega
      subst this
      simp only [topNonceSearch, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hv]
  | succ fuel ih =>
      intro n s h1 h2 hfail hend
      simp only [topNonceSearch, evalWithAnswerFn_bind, hv]
      by_cases hs : s = n
      · subst hs
        have hok : topZeroOk h (v s) = true := by
          rcases hend with h' | h'
          · exact h'
          · omega
        rw [if_pos hok, evalWithAnswerFn_pure]
      · have hf : topZeroOk h (v n) = false := hfail n le_rfl (by omega)
        rw [if_neg (by rw [hf]; decide)]
        exact ih (n + 1) s (by omega) (by omega) (fun k hk1 hk2 => hfail k (by omega) hk2)
          (by rcases hend with h' | h'
              · exact Or.inl h'
              · right; omega)

/-- Agreement on tree nodes (implied by `Agrees`, `Paired.Agrees` and `Filtered.Agrees`). -/
def NodeAgrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ m : TreeNode, answers (.inl (.inr (cell (secretsOf answers) (.node m) labels))) = labels (.node m)

theorem proj_node_eq (n : TreeNode) (o : HashOutput) :
    (Node.node n).toPos.proj o =
      WCT9.halfOf (WCT9.lowerHigh n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)) o := by
  rfl

/-- One level of the honest tree under node agreement: the honest nonce is the selected trial, and the honest
value is the used half of the selected trial's label. -/
theorem tree_step {answers : Answers} {labels : Labels} (hag : NodeAgrees answers labels)
    (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (n : TreeNode)
    (hn : treeNodeAt lay tree level c = some n)
    (hl : treeValue (WCT9.wotsTree answers lay tree.val) level (2 * c) = treeLabel labels lay tree level (2 * c))
    (hr : treeValue (WCT9.wotsTree answers lay tree.val) level (2 * c + 1) =
      treeLabel labels lay tree level (2 * c + 1)) :
    WCT9.honestNonce answers lay tree.val level c = selNonce labels n ∧
      treeValue (WCT9.wotsTree answers lay tree.val) (level + 1) c =
        (Node.node n).toPos.proj (labels (.node (selNode labels n))) := by
  have hlay := treeNodeAt_lay hn
  have hlev := treeNodeAt_level hn
  have hnon := treeNodeAt_nonce hn
  have hv : level < height lay ∧ c < 2 ^ (height lay - level - 1) := by
    unfold treeNodeAt at hn
    split_ifs at hn with hv
    exact ⟨hv.1, hv.2.1⟩
  have hidx : n.1.idx.val = c := by
    unfold treeNodeAt at hn
    split_ifs at hn with hv
    cases hn
    rfl
  have htree : n.1.tree = tree := by
    unfold treeNodeAt at hn
    split_ifs at hn with hv
    cases hn
    rfl
  set heap := 2 ^ (height lay - level - 1) + c with hheap
  set L := treeLabel labels lay tree level (2 * c)
  set R := treeLabel labels lay tree level (2 * c + 1)
  -- Trial values: for `k ≤ sel`, the honest trial hash is the used half of trial `k`'s label.
  have htrial : ∀ k ≤ selNonce labels n,
      evalWithAnswerFn answers (WCT9.halfHash (WCT9.lowerHigh lay.val heap)
        (WCT9.merkleNodeInputN lay.val tree.val heap k L R)) =
        (Node.node n).toPos.proj (labels (.node (withNonce n k))) := by
    intro k hk
    have hcap := trialCap_le n.1.lay n.1.level.val
    have hks := selNonce_lt labels n
    have ha := active_trial_of_le hk
    have hcell := cell_node_active (secrets := secretsOf answers) ha
    rw [withNonce_nonce n (by omega)] at hcell
    simp only [withNonce_lay, withNonce_tree, withNonce_level, withNonce_idx] at hcell
    rw [hlay, hlev, hidx, htree] at hcell
    rw [Wots.eval_halfHash', ← hcell, hag, proj_node_eq, hlay, hlev, hidx]
  have hsel : WCT9.honestNonce answers lay tree.val level c = selNonce labels n := by
    by_cases htop : lay = 0 ∧ level < 11
    · obtain ⟨h0, h11⟩ := htop
      have hcapeq : trialCap n.1.lay n.1.level.val = topNonceCap (level + 1) := by
        unfold trialCap; rw [hlay, hlev, if_pos ⟨h0, h11⟩]
      unfold WCT9.honestNonce
      rw [if_pos ⟨h0, h11⟩, hl, hr]
      unfold topNodeAt
      have hspec := selNonce_spec labels n
      have hslt := selNonce_lt labels n
      rw [hcapeq] at hspec hslt
      have hpos : 0 < topNonceCap (level + 1) := by unfold topNonceCap; positivity
      -- the search values below `sel` are the trial labels
      have hvals : ∀ k ≤ selNonce labels n, evalWithAnswerFn answers (topNodeHashN heap k L R) =
          (Node.node n).toPos.proj (labels (.node (withNonce n k))) := by
        intro k hk
        rw [← htrial k hk]
        subst h0
        unfold topNodeHashN
        rw [← WCT9.merkleNodeInputN_top tree.val heap k L R, ← WCT9.lowerHigh_top_eq_nodeHalfHigh,
          WCT9.halfHash_eq_projHash]
        rfl
      have hres := eval_topNonceSearch_eq answers (level + 1) heap L R
        (fun k => evalWithAnswerFn answers (topNodeHashN heap k L R)) (fun _ => rfl)
        (topNonceCap (level + 1) - 1) 0 (selNonce labels n) (Nat.zero_le _) (by omega)
        (fun k _ hk => by
          rw [hvals k (by omega)]
          have := hspec.1 k hk
          unfold trialFails at this
          rw [hlev] at this
          exact this)
        (by
          rcases hspec.2 with h' | h'
          · left
            rw [hvals _ le_rfl]
            unfold trialFails at h'
            rw [hlev] at h'
            simpa using h'
          · right; omega)
      exact congrArg Prod.fst hres
    · have hcap1 : trialCap n.1.lay n.1.level.val = 1 := by
        unfold trialCap; rw [hlay, hlev, if_neg htop]
      rw [selNonce_of_cap_one hcap1]
      unfold WCT9.honestNonce
      rw [if_neg htop]
  refine ⟨hsel, ?_⟩
  rw [WCT9.wotsTree_node_any answers lay tree.val level c hv.1 hv.2, hsel, hl, hr]
  exact htrial _ le_rfl

/-- The selected representative of a node's position (tree nodes: the selected trial; others: the node). -/
def Node.sel (labels : Labels) : Node → Node
  | .chain p => .chain p
  | .leaf L => .leaf L
  | .node n => .node (selNode labels n)
  | .wctChain p => .wctChain p
  | .wctLeaf L => .wctLeaf L
  | .wctNode n => .wctNode n
  | .forest i => .forest i
theorem toPos_sel (labels : Labels) (node : Node) : (node.sel labels).toPos = node.toPos := by
  cases node <;> rfl

theorem treeNodeAt_of_node (n : TreeNode) :
    treeNodeAt n.1.lay n.1.tree n.1.level.val n.1.idx.val = some (withNonce n 0) := by
  have hv : n.1.level.val < height n.1.lay ∧ n.1.idx.val < 2 ^ (height n.1.lay - n.1.level.val - 1) ∧
      n.1.tree.val < 2 ^ treeBits n.1.lay ∧ (n.1.lay = 0 ∨ n.1.level.val + 1 < height n.1.lay) := n.2
  unfold treeNodeAt
  rw [dif_pos hv]
  rfl

theorem selNonce_withNonce (labels : Labels) (n : TreeNode) (k : Nat) :
    selNonce labels (withNonce n k) = selNonce labels n := rfl

/-- The honest input of a tree position is the cell of its selected trial (given the children). -/
theorem honestInput_node_sel {answers : Answers} {labels : Labels} (hag : NodeAgrees answers labels) (n : TreeNode)
    (hl : treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val) =
      treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val))
    (hr : treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val + 1) =
      treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)) :
    Extract.honestInput answers (Node.node n).toPos =
      cell (secretsOf answers) (.node (selNode labels n)) labels := by
  obtain ⟨hsel, -⟩ := tree_step hag n.1.lay n.1.tree n.1.level.val n.1.idx.val (withNonce n 0)
    (treeNodeAt_of_node n) hl hr
  rw [selNonce_withNonce] at hsel
  have ha : Active labels (withNonce n (selNonce labels n)) := active_trial_of_le le_rfl
  have hs := selNonce_lt labels n
  have hc := trialCap_le n.1.lay n.1.level.val
  rw [show selNode labels n = withNonce n (selNonce labels n) from rfl, cell_node_active ha,
    withNonce_nonce n (by omega)]
  simp only [withNonce_lay, withNonce_tree, withNonce_level, withNonce_idx]
  change pad64 (WCT9.merkleNodeInputN n.1.lay.val n.1.tree.val (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
    (WCT9.honestNonce answers n.1.lay n.1.tree.val n.1.level.val n.1.idx.val)
    (treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val))
    (treeValue (WCT9.wotsTree answers n.1.lay n.1.tree.val) n.1.level.val (2 * n.1.idx.val + 1))) = _
  rw [hsel, hl, hr]

end ClaudeWCT.W9.T3.Security.CanonGraph
