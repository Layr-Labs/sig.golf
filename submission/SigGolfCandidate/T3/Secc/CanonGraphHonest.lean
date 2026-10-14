import SigGolfCandidate.T3.Secc.CanonGraph

namespace SigGolfCandidate.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot leafValue)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
  SigGolfCandidate.T3.buildLevels Correctness.builtTree Correctness.ftsRows
def ftsSecretNat (answers : Answers) (index coord leaf : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (leaf / 2))
  if leaf % 2 = 0 then pair.1 else pair.2
theorem eval_ftsRows_secrets (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.length = 2048 ∧
      ∀ leaf, leaf < 2048 →
        (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.getD leaf 0 =
          ftsSecretNat answers index coord leaf := by
  unfold Correctness.ftsRows
  refine Correctness.eval_foldlM_range_inv answers 1024 _
    (fun pairs (rows : List Digest × List Digest) => rows.2.length = 2 * pairs ∧
      ∀ leaf, leaf < 2 * pairs → rows.2.getD leaf 0 = ftsSecretNat answers index coord leaf)
    ([], []) ⟨rfl, fun leaf h => by omega⟩ (fun pair _ rows hrows => ?_)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  obtain ⟨hlen, hget⟩ := hrows
  refine ⟨by simp [hlen]; omega, ?_⟩
  intro leaf hleaf
  by_cases hold : leaf < 2 * pair
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hold)]
    exact hget leaf hold
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    have he : leaf = 2 * pair ∨ leaf = 2 * pair + 1 := by omega
    rcases he with rfl | rfl
    · simp only [Nat.sub_self, List.getD_cons_zero, ftsSecretNat]
      rw [show 2 * pair / 2 = pair by omega, if_pos (by omega)]
    · simp only [show 2 * pair + 1 - 2 * pair = 1 by omega, ftsSecretNat]
      rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega)]
      rfl
theorem ftsSecret_nat (answers : Answers) (index coord leaf : Nat) (hleaf : leaf < 2048) :
    Extract.ftsSecret answers index coord leaf = ftsSecretNat answers index coord leaf := by
  unfold Extract.ftsSecret
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).2 leaf hleaf
theorem ftsSecret_eq (answers : Answers) (f : FtsLeafPos) :
    Extract.ftsSecret answers f.index.val f.coord.val f.leaf.val = ftsOf (secretsOf answers) f :=
  ftsSecret_nat answers _ _ _ f.leaf.isLt
section Honest
variable {answers : Answers} {labels : Labels}
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    honestChainValue answers a.layer a.tree.val a.leaf.val a.chain.val
      (leafSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a step :=
  ChainGraph.source_prefix answers (chainLabels labels) (agrees_chain h) a step hstep
theorem leafEnd_eq (h : Agrees answers labels) (L : LeafPos) (i : Nat) (hi : i < 58) :
    leafEnd answers L.lay L.tree.val L.leaf.val i = endLabel (secretsOf answers) labels L i := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hx := ChainGraph.source_endpoint answers (chainLabels labels) (agrees_chain h) ⟨L.lay, L.tree, L.leaf, fin58 i⟩
  simp only [hval] at hx
  exact hx
theorem leafEnds_eq (h : Agrees answers labels) (L : LeafPos) :
    (List.range (chainCount L.lay)).map (leafEnd answers L.lay L.tree.val L.leaf.val) =
      (List.range (chainCount L.lay)).map (endLabel (secretsOf answers) labels L) := by
  apply List.map_congr_left
  intro i hi
  exact leafEnd_eq h L i (lt_of_lt_of_le (List.mem_range.mp hi) (chainCount_bound L.lay))
theorem treeNodeAt_some (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hlevel : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) :
    ∃ n : TreeNode, treeNodeAt lay tree level c = some n ∧ n.1.lay = lay ∧ n.1.tree = tree ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold treeNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem ftsNodeAt_some (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) (hlevel : level < 11)
    (hc : c < 2 ^ (11 - level - 1)) :
    ∃ n : FtsNodePos, ftsNodeAt index coord level c = some n ∧ n.1.index = index ∧ n.1.coord = coord ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold ftsNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
end Honest
end SigGolfCandidate.T3.Security.CanonGraph
