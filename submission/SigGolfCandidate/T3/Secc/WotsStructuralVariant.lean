import SigGolfCandidate.T3.Secc.WotsStructuralHonest

namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
theorem eval_query_bind {α : Type} (T : Answers) (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) :
    evalWithAnswerFn T (liftM (T3.Spec.query input) >>= next) = evalWithAnswerFn T (next (T input)) := by
  rw [evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn T (liftM (T3.Spec.query input)) = T input from simulateQ_spec_query T input]
theorem congr_of_queried {α : Type} (T T' : Answers) (program : M α)
    (h : ∀ q ∈ SourceReplay.queried T program, T q = T' q) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program := by
  induction program using OracleComp.inductionOn with
  | pure x => exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      rw [SourceReplay.queried_query_bind] at h
      have h0 : T input = T' input := h input List.mem_cons_self
      have ih' := ih (T input) (fun q hq => h q (List.mem_cons_of_mem _ hq))
      refine ⟨?_, ?_⟩
      · rw [eval_query_bind, eval_query_bind, ← h0]
        exact ih'.1
      · rw [SourceReplay.queried_query_bind, SourceReplay.queried_query_bind, ← h0, ih'.2]
structure Variant (labels : CanonGraph.Labels) (T T' : Answers) : Prop where
  agrees : CanonGraph.Agrees T labels
  coin : ∀ n, T (.inl (.inl n)) = T' (.inl (.inl n))
  priv : ∀ c, T (.inr c) = T' (.inr c)
  pub : ∀ x : HashInput, (∀ node : CanonGraph.Node, Extract.posOf x = some node.toPos →
    x = CanonGraph.cell (CanonGraph.secretsOf T) node labels) → T (.inl (.inr x)) = T' (.inl (.inr x))
theorem posOf_honestInput (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    Extract.posOf (Extract.honestInput T p) = some p :=
  Extract.posOf_eq hp (Extract.hdrBlock_honestInput T p)
theorem Variant.honest {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') :
    ∀ q, HonestQuery T q → T q = T' q
  | .inl (.inl n), _ => hv.coin n
  | .inr c, _ => hv.priv c
  | .inl (.inr x), Or.inl hnone => hv.pub x (fun node h => by rw [hnone] at h; cases h)
  | .inl (.inr x), Or.inr ⟨p, hp, hx⟩ => hv.pub x (fun node h => by
      rw [hx, posOf_honestInput T p hp] at h
      cases h
      rw [hx]
      exact CanonGraph.honestInput_eq hv.agrees node)
theorem Variant.congr {labels : CanonGraph.Labels} {T T' : Answers} (hv : Variant labels T T') {α : Type}
    {program : M α} (hp : QueriesSat T (HonestQuery T) program) :
    evalWithAnswerFn T program = evalWithAnswerFn T' program ∧
      SourceReplay.queried T program = SourceReplay.queried T' program :=
  congr_of_queried T T' program (fun q hq => hv.honest q (hp q hq))
section Game
variable {labels : CanonGraph.Labels} {T T' : Answers}
end Game
theorem leafTweak_alias (lay : Layer) {tree tree' : Nat} (h : tree % 2 ^ 40 = tree' % 2 ^ 40) (leaf : Nat) :
    leafTweak lay tree leaf = leafTweak lay tree' leaf := by
  have h32 : tree % 2 ^ 32 = tree' % 2 ^ 32 := by
    rw [← Nat.mod_mod_of_dvd tree (show 2 ^ 32 ∣ 2 ^ 40 by norm_num),
      ← Nat.mod_mod_of_dvd tree' (show 2 ^ 32 ∣ 2 ^ 40 by norm_num), h]
  have hr : (tree * 2 ^ height lay + leaf) % 2 ^ 32 = (tree' * 2 ^ height lay + leaf) % 2 ^ 32 :=
    ((Nat.ModEq.mul_right (2 ^ height lay) h32).add_right leaf)
  unfold leafTweak hyperWord
  rw [hr]
theorem nodeTweak_alias (tag lay : Nat) {tree tree' : Nat} (h : tree % 2 ^ 40 = tree' % 2 ^ 40) (heap : Nat) :
    nodeTweak tag lay tree heap = nodeTweak tag lay tree' heap := by
  have h32 : tree % 2 ^ 32 = tree' % 2 ^ 32 := by
    rw [← Nat.mod_mod_of_dvd tree (show 2 ^ 32 ∣ 2 ^ 40 by norm_num),
      ← Nat.mod_mod_of_dvd tree' (show 2 ^ 32 ∣ 2 ^ 40 by norm_num), h]
  have h31 : tree % 2 ^ 31 = tree' % 2 ^ 31 := by
    rw [← Nat.mod_mod_of_dvd tree (show 2 ^ 31 ∣ 2 ^ 40 by norm_num),
      ← Nat.mod_mod_of_dvd tree' (show 2 ^ 31 ∣ 2 ^ 40 by norm_num), h]
  unfold nodeTweak hyperWord ftsNodeWord
  rw [h32, h31, Mask.header_congr rfl h rfl]
section Alias
variable (T : Answers) (lay : Layer) {tree tree' : Nat} (h : tree % 2 ^ 40 = tree' % 2 ^ 40)
include h
theorem leafEnd_alias (leaf i : Nat) : leafEnd T lay tree leaf i = leafEnd T lay tree' leaf i := by
  have hal : Mask.LeafAlias lay tree leaf ⟨lay, tree', leaf⟩ := ⟨rfl, h, rfl⟩
  unfold Correctness.leafEnd
  rw [Mask.chain_alias hal, Mask.leafSeed_alias T hal]
theorem leafRoot_alias (leaf : Nat) : leafRoot T lay tree leaf = leafRoot T lay tree' leaf := by
  unfold Correctness.leafRoot
  have hends : (List.range (chainCount lay)).map (leafEnd T lay tree leaf) =
      (List.range (chainCount lay)).map (leafEnd T lay tree' leaf) :=
    List.map_congr_left fun i _ => leafEnd_alias T lay h leaf i
  rw [hends]
  unfold leafHash leafInput
  rw [leafTweak_alias lay h]
omit h in
theorem buildLevels_alias (tag lay' : Nat) {tree tree' : Nat} (h : tree % 2 ^ 40 = tree' % 2 ^ 40) (height : Nat)
    (leaves : List Digest) :
    T3.buildLevels tag lay' tree height leaves = T3.buildLevels tag lay' tree' height leaves := by
  have hn : T3.nodeHash tag lay' tree = T3.nodeHash tag lay' tree' := by
    funext heap left right
    unfold T3.nodeHash
    rw [nodeTweak_alias tag lay' h]
  have hl : T3.buildLevel tag lay' tree = T3.buildLevel tag lay' tree' := by
    funext height level nodes
    unfold T3.buildLevel
    rw [hn]
  unfold T3.buildLevels
  rw [hl]
theorem builtTree_alias : builtTree T lay tree = builtTree T lay tree' := by
  unfold Correctness.builtTree
  have hr : leafRoot T lay tree = leafRoot T lay tree' := funext (leafRoot_alias T lay h)
  rw [hr, buildLevels_alias 3 lay.val h]
theorem honestRoot_alias : Extract.honestRoot T lay tree = Extract.honestRoot T lay tree' := by
  unfold Extract.honestRoot
  rw [builtTree_alias T lay h]
end Alias
section Depth
variable {labels : CanonGraph.Labels} {T T' : Answers}
theorem honestForest_variant (hv : Variant labels T T') (index : Nat) (hindex : index < 2 ^ 40) :
    Extract.honestForest T index = Extract.honestForest T' index := by
  rw [Mask.honestForest_eq T, Mask.honestForest_eq T']
  have hfts : ∀ c ∈ List.range 7, evalWithAnswerFn T (buildFts index c) = evalWithAnswerFn T' (buildFts index c) :=
    fun c hc => (hv.congr (sat_buildFts T index c hindex (List.mem_range.mp hc))).1
  have hroots : ((List.range 7).map fun c => treeValue (evalWithAnswerFn T' (buildFts index c)).1 11 0) =
      Correctness.forestRoots T index 7 :=
    List.map_congr_left fun c hc => by rw [hfts c hc]
  rw [hroots]
  exact (hv.congr (sat_forestPk T index hindex)).1
end Depth
end SigGolfCandidate.T3.Security.Wots.Structural
