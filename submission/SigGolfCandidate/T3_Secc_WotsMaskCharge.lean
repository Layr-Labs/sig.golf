import SigGolfCandidate.T3_Secc_WotsMask

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Mask
theorem queried_length_bind (T : Answers) {α β : Type} (p : M α) (f : α → M β) :
    (SourceReplay.queried T (p >>= f)).length =
      (SourceReplay.queried T p).length + (SourceReplay.queried T (f (evalWithAnswerFn T p))).length := by
  rw [SourceReplay.queried_bind, List.length_append]
theorem queried_length_pure (T : Answers) {α : Type} (x : α) :
    (SourceReplay.queried T (pure x : M α)).length = 0 := rfl
theorem queried_length_shortHash (T : Answers) (input : HashInput) :
    (SourceReplay.queried T (shortHash input)).length = 1 := rfl
theorem queried_length_projHash (T : Answers) (high : Bool) (input : HashInput) :
    (SourceReplay.queried T (projHash high input)).length = 1 := rfl
theorem queried_length_privatePair (T : Answers) (tag lay tree position index : Nat) :
    (SourceReplay.queried T (privatePair tag lay tree position index)).length = 1 := rfl
theorem queried_length_foldlM (T : Answers) {β γ : Type} (l : List β) (f : γ → β → M γ) (c : β → Nat)
    (hf : ∀ x ∈ l, ∀ s, (SourceReplay.queried T (f s x)).length = c x) :
    ∀ init, (SourceReplay.queried T (l.foldlM f init)).length = (l.map c).sum := by
  induction l with
  | nil => intro init; rfl
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons, queried_length_bind, hf x List.mem_cons_self,
        ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s), List.map_cons, List.sum_cons]
theorem queried_length_mapM (T : Answers) {α β : Type} (l : List α) (f : α → M β) (c : α → Nat)
    (hf : ∀ x ∈ l, (SourceReplay.queried T (f x)).length = c x) :
    (SourceReplay.queried T (l.mapM f)).length = (l.map c).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.mapM_cons, queried_length_bind, queried_length_bind, queried_length_pure,
        hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem x hy)), List.map_cons, List.sum_cons,
        Nat.add_zero]
theorem sum_map_one {β : Type} (l : List β) : (l.map fun _ => 1).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
theorem queried_length_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (chain lay tree leaf i start count v)).length = count := by
  unfold chain
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => queried_length_shortHash _ _), sum_map_one,
    List.length_range']
theorem queried_length_topChain (T : Answers) (leaf i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (topChain leaf i start count v)).length = count := by
  unfold topChain
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => queried_length_projHash _ _ _), sum_map_one,
    List.length_range']
def halfCount (lay : Layer) (digits : List Nat) (signatureOnly : Bool) (i : Nat) : Nat :=
  if chainCount lay ≤ i then 0
  else digits.getD i 0 + (if signatureOnly then 0 else maxDigit lay i - digits.getD i 0)
def leafCount (lay : Layer) (digits : List Nat) (signatureOnly : Bool) : Nat :=
  ((List.range ((chainCount lay + 1) / 2)).map fun pair =>
      1 + ((List.range 2).map fun half => halfCount lay digits signatureOnly (2 * pair + half)).sum).sum +
    (if signatureOnly then 0 else 1)
theorem queried_length_leafHalf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) (pair : Nat) (seeds : Digest × Digest) (rows : List Digest × List Digest) (half : Nat) :
    (SourceReplay.queried T (Correctness.leafHalf lay tree leaf digits signatureOnly pair seeds rows half)).length =
      halfCount lay digits signatureOnly (2 * pair + half) := by
  unfold Correctness.leafHalf halfCount
  by_cases hi : chainCount lay ≤ 2 * pair + half
  · simp only [hi, ↓reduceIte]
    rfl
  · simp only [hi, ↓reduceIte]
    rw [queried_length_bind, queried_length_chain]
    cases signatureOnly
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [queried_length_bind, queried_length_chain, queried_length_pure, Nat.add_zero]
    · simp only [↓reduceIte]
      rw [queried_length_pure]
theorem queried_length_leafRows (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (Correctness.leafRows lay tree leaf digits signatureOnly)).length =
      ((List.range ((chainCount lay + 1) / 2)).map fun pair =>
        1 + ((List.range 2).map fun half => halfCount lay digits signatureOnly (2 * pair + half)).sum).sum := by
  unfold Correctness.leafRows
  refine queried_length_foldlM T _ _ _ (fun pair _ rows => ?_) _
  rw [queried_length_bind, queried_length_privatePair,
    queried_length_foldlM T _ _ _ (fun half _ s => queried_length_leafHalf T lay tree leaf digits signatureOnly
      pair _ s half)]
theorem queried_length_buildLeaf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (buildLeaf lay tree leaf digits signatureOnly)).length =
      leafCount lay digits signatureOnly := by
  rw [Correctness.buildLeaf_eq, queried_length_bind, queried_length_leafRows]
  unfold leafCount
  cases signatureOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [queried_length_bind, queried_length_pure]
    rfl
  · simp only [↓reduceIte]
    rfl
def treeRowsCount (lay : Layer) (selected : Nat) (digits : List Nat) : Nat :=
  ((List.range (2 ^ height lay)).map fun leaf => leafCount lay (if leaf = selected then digits else []) false).sum
theorem queried_length_treeRows (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    (SourceReplay.queried T (Correctness.treeRows lay tree selected digits)).length =
      treeRowsCount lay selected digits := by
  unfold Correctness.treeRows
  refine queried_length_foldlM T _ _ _ (fun leaf _ rows => ?_) _
  rw [queried_length_bind, queried_length_buildLeaf]
  rfl
def topPathCount : Nat := ((List.range 12).map fun _ => 1).sum
theorem queried_length_topPath (T : Answers) (cache : Cache) (leaf : Nat) :
    (SourceReplay.queried T (topPath cache leaf)).length = topPathCount := by
  unfold topPath topPathCount
  exact queried_length_mapM T _ _ (fun _ => 1) (fun level _ => by
    unfold mask pairedMask
    simp only [queried_length_bind, queried_length_privatePair, queried_length_pure])
/-! ### Top leaves (campaign T8D: family seeds, `buildLeafTop`) -/
def topChainCount (digits : List Nat) (signatureOnly : Bool) (i : Nat) : Nat :=
  digits.getD i 0 + (if signatureOnly then 0 else maxDigit 0 i - digits.getD i 0)
def topLeafCountC (digits : List Nat) (signatureOnly : Bool) : Nat :=
  ((List.range (chainCount 0)).map (topChainCount digits signatureOnly)).sum + (if signatureOnly then 0 else 1)
def topLeafCount (digits : List Nat) (signatureOnly : Bool) : Nat :=
  topCoefPairs + topLeafCountC digits signatureOnly
theorem queried_length_topPairsFrom (T : Answers) (first start : Nat) (init : List Digest) :
    (SourceReplay.queried T (topPairsFrom first start init)).length = topCoefPairs - start := by
  unfold topPairsFrom
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun j _ acc => by
    unfold topSeedPair
    rw [queried_length_bind, queried_length_privatePair, queried_length_pure]), sum_map_one, List.length_range']
theorem queried_length_topCoefs (T : Answers) (leaf : Nat) :
    (SourceReplay.queried T (topCoefs leaf)).length = topCoefPairs := by
  unfold topCoefs
  rw [queried_length_bind, queried_length_topPairsFrom, queried_length_pure]
  rfl
theorem queried_length_topLeafStep (T : Answers) (leaf : Nat) (digits : List Nat) (signatureOnly : Bool)
    (coefs : List Digest) (state : List Digest × List Digest) (i : Nat) :
    (SourceReplay.queried T (Correctness.topLeafStep leaf digits signatureOnly coefs state i)).length =
      topChainCount digits signatureOnly i := by
  unfold Correctness.topLeafStep topChainCount
  rw [queried_length_bind, queried_length_topChain]
  cases signatureOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [queried_length_bind, queried_length_topChain, queried_length_pure, Nat.add_zero]
  · simp only [↓reduceIte]
    rw [queried_length_pure]
theorem queried_length_buildLeafTopC (T : Answers) (leaf : Nat) (coefs : List Digest) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (buildLeafTopC leaf coefs digits signatureOnly)).length =
      topLeafCountC digits signatureOnly := by
  rw [Correctness.buildLeafTopC_eq, queried_length_bind,
    queried_length_foldlM T _ _ (topChainCount digits signatureOnly)
      (fun i _ s => queried_length_topLeafStep T leaf digits signatureOnly _ s i)]
  unfold topLeafCountC
  cases signatureOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [queried_length_bind, queried_length_pure, leafHash, queried_length_projHash]
  · simp only [↓reduceIte]
    rw [queried_length_pure]
theorem queried_length_buildLeafTop (T : Answers) (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    (SourceReplay.queried T (buildLeafTop leaf digits signatureOnly)).length = topLeafCount digits signatureOnly := by
  unfold buildLeafTop
  rw [queried_length_bind, queried_length_topCoefs, queried_length_buildLeafTopC]
  rfl
theorem queried_length_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat) :
    (SourceReplay.queried T (signTop cache leaf digits)).length = topLeafCount digits true + topPathCount := by
  unfold signTop
  simp only [queried_length_bind, queried_length_buildLeafTop, queried_length_topPath, queried_length_pure,
    Nat.add_zero]
theorem queried_length_buildLevel (T : Answers) (tag lay tree h level : Nat) (nodes : List Digest) :
    (SourceReplay.queried T (buildLevel tag lay tree h level nodes)).length = nodes.length / 2 := by
  unfold buildLevel
  rw [queried_length_mapM T _ _ (fun _ => 1) (fun i _ => by unfold nodeHash; exact queried_length_projHash _ _ _),
    sum_map_one, List.length_range]
theorem getD_length_of_map {xs ys : List (List Digest)} (h : xs.map List.length = ys.map List.length) (i : Nat) :
    (xs.getD i []).length = (ys.getD i []).length := by
  have := congrArg (fun l : List Nat => l.getD i 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
  cases hx : xs[i]? <;> cases hy : ys[i]? <;> simp_all
/-- The query count of `buildLevels` only depends on the length of its leaves. -/
theorem queried_length_buildLevels_congr (T T' : Answers) (tag lay tree h : Nat) (leaves leaves' : List Digest)
    (hlen : leaves.length = leaves'.length) :
    (SourceReplay.queried T (buildLevels tag lay tree h leaves)).length =
      (SourceReplay.queried T' (buildLevels tag lay tree h leaves')).length := by
  unfold buildLevels
  suffices H : ∀ (ls : List Nat) (s s' : List (List Digest)), s.map List.length = s'.map List.length →
      (SourceReplay.queried T (ls.foldlM (fun levels level => do
        let nodes ← buildLevel tag lay tree h level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s)).length =
      (SourceReplay.queried T' (ls.foldlM (fun levels level => do
        let nodes ← buildLevel tag lay tree h level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s')).length from H _ _ _ (by simp [hlen])
  intro ls
  induction ls with
  | nil => intro s s' _; rfl
  | cons level ls ih =>
      intro s s' hs
      simp only [List.foldlM_cons, queried_length_bind, queried_length_buildLevel, queried_length_pure,
        Nat.add_zero, getD_length_of_map hs]
      congr 1
      apply ih
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.map_append, List.map_cons, List.map_nil,
        Correctness.eval_buildLevel_length, hs, getD_length_of_map hs]
/-- img-v6 keygen top leaves: the family coefficients (`topCoefsK` at the first leaf of each family) and the leaf. -/
def topStepCount (leaf : Nat) : Nat :=
  (if leaf % 4 = 0 then topCoefPairs - leaf / 4 % 2 else 0) + topLeafCountC [] false
theorem queried_length_topTreeStep (T : Answers) (st : List Digest × List Digest × Digest) (leaf : Nat) :
    (SourceReplay.queried T (topTreeStep st leaf)).length = topStepCount leaf := by
  unfold topTreeStep topFamilyCoefs topStepCount
  rw [queried_length_bind, queried_length_bind, queried_length_buildLeafTopC, queried_length_pure, Nat.add_zero]
  split
  · unfold topCoefsK
    rw [queried_length_bind, queried_length_topPairsFrom, queried_length_pure, Nat.add_zero]
  · rw [queried_length_pure]
theorem queried_length_topLeaves (T : Answers) :
    (SourceReplay.queried T ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0))).length =
      ((List.range (2 ^ height 0)).map topStepCount).sum :=
  queried_length_foldlM T _ _ topStepCount (fun leaf _ st => queried_length_topTreeStep T st leaf) _
/-- Top node (nonce trial) queries carry the node tweak in bytes `16..32`: they are no chain row. -/
theorem respects_topNodeHashN (a : ChainAddr) (heap n : Nat) (left right : Digest) :
    Respects (Untouched a) (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  apply Respects.projHash
  refine untouched_of_hdr a _ (nodeTweak 3 0 0 heap) ?_
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_nodeTweak _ _ _ _ _ _ _ _ _))
  rw [Extract.hdrBlock_pad64 _ (by simp [topNodeInput, nonceBytes, bytesLE_length])]
  unfold topNodeInput
  rw [List.append_assoc]
  exact Extract.hdrBlock_prefix _ _ _
theorem respects_topNonceSearch (a : ChainAddr) (h heap : Nat) (left right : Digest) :
    ∀ fuel n, Respects (Untouched a) (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact Respects.bind (respects_topNodeHashN a _ _ _ _) fun _ => Respects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine Respects.bind (respects_topNodeHashN a _ _ _ _) fun _ => ?_
      split
      · exact Respects.pure' _
      · exact respects_topNonceSearch a h heap left right fuel (n + 1)
theorem respects_buildTopLevels (a : ChainAddr) (leaves : List Digest) :
    Respects (Untouched a) (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine Respects.foldlM _ _ (fun level _ levels => Respects.bind ?_ fun _ => Respects.pure' _) _
  unfold buildTopLevel
  refine Respects.mapM _ _ fun i _ => ?_
  split
  · exact respects_nodeHash a _ _ _ _ _ _ (by decide)
  · unfold topNodeAt
    exact Respects.map _ (respects_topNonceSearch a _ _ _ _ _ _)
/-- The leaves of the top tree are the first level of `buildTopLevels`. -/
theorem eval_buildTopLevels_head (T : Answers) (leaves : List Digest) :
    (evalWithAnswerFn T (buildTopLevels leaves)).getD 0 [] = leaves := by
  unfold buildTopLevels
  suffices H : ∀ (ls : List Nat) (s : List (List Digest)), s ≠ [] → s.getD 0 [] = leaves →
      (evalWithAnswerFn T (ls.foldlM (fun levels level => do
        let nodes ← buildTopLevel level (levels.getD (level - 1) [])
        pure (levels ++ [nodes])) s)).getD 0 [] = leaves from H _ _ (List.cons_ne_nil _ _) rfl
  intro ls
  induction ls with
  | nil => intro s _ hs; exact hs
  | cons level ls ih =>
      intro s hne hs
      rw [List.foldlM_cons, evalWithAnswerFn_bind]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      cases s with
      | nil => exact absurd rfl hne
      | cons x xs => exact ih _ (by simp) (by simpa using hs)
/-- img-v6: the keygen top tree's query count depends on the tables only through its nonce trials, i.e. through
the answers at top node queries. Two tables that agree on every query some `S` contains (with `S` respected by
the node levels) and produce the same top tree issue the same number of queries. -/
theorem queried_length_buildTopTree_of {S : Spec.Domain → Prop} (hS : ∀ leaves, Respects S (buildTopLevels leaves))
    (T T' : Answers) (hT : ∀ q, S q → T q = T' q)
    (hb : evalWithAnswerFn T buildTopTree = evalWithAnswerFn T' buildTopTree) :
    (SourceReplay.queried T buildTopTree).length = (SourceReplay.queried T' buildTopTree).length := by
  have hroots : (evalWithAnswerFn T ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0))).1 =
      (evalWithAnswerFn T' ((List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0))).1 := by
    have h := congrArg (fun l : List (List Digest) => l.getD 0 []) hb
    simp only [buildTopTree, evalWithAnswerFn_bind, eval_buildTopLevels_head] at h
    exact h
  unfold buildTopTree
  rw [queried_length_bind, queried_length_bind, queried_length_topLeaves, queried_length_topLeaves, hroots,
    (hS _).queried_eq hT]
variable (answers : Answers) (a : ChainAddr)
theorem count_bind_of {T T' : Answers} {α β : Type} {p : M α} {f : α → M β}
    (hp : evalWithAnswerFn T' p = evalWithAnswerFn T p)
    (hcp : (SourceReplay.queried T' p).length = (SourceReplay.queried T p).length)
    (hf : (SourceReplay.queried T' (f (evalWithAnswerFn T p))).length =
      (SourceReplay.queried T (f (evalWithAnswerFn T p))).length) :
    (SourceReplay.queried T' (p >>= f)).length = (SourceReplay.queried T (p >>= f)).length := by
  rw [queried_length_bind, queried_length_bind, hp, hcp, hf]
def maskCount : Nat := ((List.range' 0 12).map fun level => ((List.range (2 ^ (11 - level))).map fun _ => 1).sum).sum
theorem queried_length_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    (SourceReplay.queried T (maskedLevel nodes level)).length =
      ((List.range (2 ^ (11-level))).map fun _ => 1).sum := by
  unfold maskedLevel pairedMask
  rw [queried_length_bind, queried_length_pure, Nat.add_zero]
  exact queried_length_mapM T _ _ (fun _ => 1) (fun pair _ => by
    simp only [queried_length_bind, queried_length_privatePair, queried_length_pure])
theorem queried_length_cachePayload (T : Answers) (builder : M (List (List Digest))) :
    (SourceReplay.queried T (Correctness.cachePayloadProgram builder)).length =
      (SourceReplay.queried T builder).length + maskCount := by
  unfold Correctness.cachePayloadProgram
  rw [queried_length_bind]
  generalize evalWithAnswerFn T builder = levels
  rw [queried_length_bind, queried_length_pure, Nat.add_zero,
    queried_length_mapM _ _ _ (fun level => ((List.range (2 ^ (11 - level))).map fun _ => 1).sum)
      (fun level _ => queried_length_maskedLevel _ _ _)]
  rfl
/-- Keygen's payload: same query count for two tables that agree on `S` and build the same top tree (img-v6:
nonce trials). -/
theorem queried_length_keygenPayload_congr {S : Spec.Domain → Prop} (hS : ∀ leaves, Respects S (buildTopLevels leaves))
    (T T' : Answers) (hT : ∀ q, S q → T q = T' q)
    (hb : evalWithAnswerFn T buildTopTree = evalWithAnswerFn T' buildTopTree) :
    (SourceReplay.queried T keygenPayload).length = (SourceReplay.queried T' keygenPayload).length := by
  rw [Correctness.keygenPayload_eq, queried_length_cachePayload, queried_length_cachePayload,
    queried_length_buildTopTree_of hS T T' hT hb]
end Mask
namespace Mask
variable (answers : Answers) (a : ChainAddr)
end Mask
end SigGolfCandidate.T3.Security.Wots
