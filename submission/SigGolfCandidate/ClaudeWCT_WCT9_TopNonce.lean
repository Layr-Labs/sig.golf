import SigGolfCandidate.ClaudeWCT_WCT9_Limits
import SigGolfCandidate.ClaudeWCT_WCT9_TopDecode
import SigGolfCandidate.T3_Proofs

/-! Top-bytes layer: the verifier's top path with witness nonces agrees with the expander's nonce re-derivation
(`topFoldN`), and the honest top path through the nonce-searched top tree. -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem eval_foldlM_eq {α β : Type} (answers : Answers) (f : α → β → M α) :
    ∀ (l : List β) (a : α),
      evalWithAnswerFn answers (l.foldlM f a) = l.foldl (fun s x => evalWithAnswerFn answers (f s x)) a
  | [], a => by simp [evalWithAnswerFn_pure]
  | x :: l, a => by
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_foldlM_eq answers f l]
      rfl

theorem eval_topNonceSearch_hash (answers : Answers) (h heap : Nat) (left right : Digest) :
    ∀ fuel n, evalWithAnswerFn answers
        (topNodeHashN heap (evalWithAnswerFn answers (topNonceSearch h heap left right fuel n)).1 left right) =
      (evalWithAnswerFn answers (topNonceSearch h heap left right fuel n)).2
  | 0, n => by
      simp only [topNonceSearch, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  | fuel+1, n => by
      simp only [topNonceSearch, evalWithAnswerFn_bind]
      split
      · simp only [evalWithAnswerFn_pure]
      · exact eval_topNonceSearch_hash answers h heap left right fuel (n+1)

theorem eval_topNodeAt_hash (answers : Answers) (h heap : Nat) (left right : Digest) :
    evalWithAnswerFn answers
        (topNodeHashN heap (evalWithAnswerFn answers (topNodeAt h heap left right)).1 left right) =
      (evalWithAnswerFn answers (topNodeAt h heap left right)).2 :=
  eval_topNonceSearch_hash answers h heap left right _ 0

/-- The evaluated recovery step (`topStepN`). -/
def rstep (answers : Answers) (sig : Signature) (index : Nat) (st : Digest × List Nat) (j : Fin (height 0)) :
    Digest × List Nat :=
  evalWithAnswerFn answers (topStepN sig index st j)

theorem rstep_prefix (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ (js : List (Fin (height 0))) (st : Digest × List Nat) (k : Nat), k < st.2.length →
      (js.foldl (rstep answers sig index) st).2.getD k 0 = st.2.getD k 0
  | [], _, _, _ => rfl
  | j :: rest, st, k, hk => by
      rw [List.foldl_cons, rstep_prefix answers sig index rest _ k (by
        simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
          List.length_singleton]; omega)]
      simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      rw [List.getD_append _ _ _ _ hk]

theorem rstep_length (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ (js : List (Fin (height 0))) (st : Digest × List Nat),
      (js.foldl (rstep answers sig index) st).2.length = st.2.length + js.length
  | [], _ => by simp
  | j :: rest, st => by
      rw [List.foldl_cons, rstep_length answers sig index rest]
      simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
        List.length_cons, List.length_nil]
      omega

/-- The verifier's step with nonce list `N` (heights ≤ 11). -/
def vstep (answers : Answers) (sig : Signature) (index : Nat) (N : List Nat) (value : Digest)
    (j : Fin (height 0)) : Digest :=
  let other := (sig.layers 0).path j
  let pair := if (route index 0).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
  evalWithAnswerFn answers (topNodeHashN (2 ^ (height 0 - j.val - 1) + (route index 0).1 / 2 ^ (j.val + 1))
    (N.getD j.val 0) pair.1 pair.2)

theorem vstep_fold (answers : Answers) (sig : Signature) (index : Nat) (N : List Nat) :
    ∀ (js : List (Fin (height 0))) (st : Digest × List Nat),
      js.map Fin.val = List.range' st.2.length js.length →
      (∀ k, k < st.2.length + js.length → N.getD k 0 = (js.foldl (rstep answers sig index) st).2.getD k 0) →
      js.foldl (vstep answers sig index N) st.1 = (js.foldl (rstep answers sig index) st).1
  | [], _, _, _ => rfl
  | j :: rest, st, hjs, hN => by
      have hj : j.val = st.2.length := by
        simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hjs
        exact hjs.1
      have hrest : rest.map Fin.val = List.range' (st.2.length + 1) rest.length := by
        simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hjs
        exact hjs.2
      rw [List.foldl_cons, List.foldl_cons]
      have hstep : vstep answers sig index N st.1 j = (rstep answers sig index st j).1 := by
        have hn := hN st.2.length (by simp)
        rw [List.foldl_cons, rstep_prefix answers sig index rest _ st.2.length (by
          simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
            List.length_singleton]; omega)] at hn
        simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_append_right _ _ _ _ le_rfl,
          Nat.sub_self, List.getD_cons_zero] at hn
        simp only [vstep, rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hj, hn]
        exact eval_topNodeAt_hash answers _ _ _ _
      rw [hstep]
      apply vstep_fold answers sig index N rest
      · simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
          List.length_singleton]
        exact hrest
      · intro k hk
        rw [hN k (by
          simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
            List.length_singleton] at hk ⊢
          simp only [List.length_cons]; omega), List.foldl_cons]

theorem topLevelNode_lt (answers : Answers) {level : Nat} (hl : level ≠ 12) (heap : Nat) (left right : Digest) :
    topLevelNode answers level heap left right = (evalWithAnswerFn answers (topNodeAt level heap left right)).2 := by
  unfold topLevelNode; rw [if_neg hl]

/-- The expander's nonce fold climbs the honest (nonce-searched) top tree up to level 11. -/
theorem eval_topFoldN_steps_honest (answers : Answers) (sig : Signature) (index : Nat)
    (levels leaves : _) (htree : TopTreeLevels answers leaves 12 levels)
    (hleaf : (route index 0).1 < 2 ^ 12)
    (hpath : ∀ j : Fin (height 0), (sig.layers 0).path j =
      treeValue levels j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) (acc : List Nat) :
    (evalWithAnswerFn answers (((List.finRange (height 0)).take 11).foldlM (topStepN sig index)
      (treeValue levels 0 (route index 0).1, acc))).1 = treeValue levels 11 ((route index 0).1 / 2 ^ 11) := by
  have hi := eval_foldlM_list_inv answers ((List.finRange (height 0)).take 11) (topStepN sig index)
    (fun i (st : Digest × List Nat) => st.1 = treeValue levels i ((route index 0).1 / 2 ^ i))
    (treeValue levels 0 (route index 0).1, acc) (by simp) (fun i hi st hv => ?_)
  · have hl : ((List.finRange (height 0)).take 11).length = 11 := by decide
    rw [hl] at hi
    exact hi
  · have hi' : i < 11 := by
      have h' := hi
      simp only [List.length_take, List.length_finRange] at h'
      change i < min 11 12 at h'
      omega
    generalize hj : ((List.finRange (height 0)).take 11)[i]'hi = j
    have hjv : j.val = i := by
      subst hj
      simp [List.getElem_take]
    simp only [topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hpath, hv, hjv]
    rw [sibling_pair (fun k => treeValue levels i k), div_pow_succ]
    have hp := htree.2.2 i (by omega) ((route index 0).1 / 2 ^ (i+1))
      (by simpa only [Nat.zero_add] using
        div_pow_bound (height := 12) (start := 0) (level := i+1) (by omega) (by simpa using hleaf))
    rw [topLevelNode_lt answers (level := i+1) (by omega)] at hp
    have hh : height 0 - i - 1 = 12 - (i+1) := by
      change 12 - i - 1 = 12 - (i+1); omega
    rw [hh]
    simpa only [treeValue] using hp.symm

theorem eval_verifyTopN_topFoldN (answers : Answers) (sig : Signature) (index : Nat) {answer : Digest}
    {digits : List Nat} (h : decode 0 answer = some digits) :
    evalWithAnswerFn answers (verifyTopN sig (evalWithAnswerFn answers (topFoldN sig index digits)).2 index answer) =
      some (evalWithAnswerFn answers (topNode index (evalWithAnswerFn answers (topFoldN sig index digits)).1
        ((sig.layers 0).path topJ))) := by
  have hsplit : List.finRange (height 0) = (List.finRange (height 0)).take 11 ++ [topJ] := by decide
  have hlt : ∀ j ∈ (List.finRange (height 0)).take 11, j.val < 11 := by decide
  have hmap : ((List.finRange (height 0)).take 11).map Fin.val = List.range' 0 11 := by decide
  unfold verifyTopN
  rw [topDecodeRun_of_decode h]
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_bind, topFoldN, eval_foldlM_eq]
  generalize hv0 : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
    (evalWithAnswerFn answers (topEnds sig index digits))) = v0
  have hv0' : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
      (evalWithAnswerFn answers ((List.finRange (chainCount 0)).mapM fun i =>
        SigGolfCandidate.T3.layChain 0 (route index 0).2 (route index 0).1 i.val (digits.getD i.val 0)
          (maxDigit 0 i.val - digits.getD i.val 0) ((sig.layers 0).values i)))) = v0 := hv0
  rw [hv0']
  generalize hR : List.foldl (fun s x => evalWithAnswerFn answers (topStepN sig index s x)) (v0, [])
    ((List.finRange (height 0)).take 11) = R
  conv_lhs => rw [hsplit, List.foldl_append]
  rw [List.foldl_ext _ (vstep answers sig index R.2) v0 (fun a b hb => by
    rw [if_pos (hlt b hb)]; rfl)]
  have hv := vstep_fold answers sig index R.2 ((List.finRange (height 0)).take 11) (v0, [])
    (by rw [hmap]; rfl) (fun k _ => by rw [← hR]; rfl)
  simp only at hv
  rw [show List.foldl (rstep answers sig index) (v0, []) ((List.finRange (height 0)).take 11) = R from hR] at hv
  rw [hv]
  rfl
/-- Top-bytes layer: on an honest top signature the expander's nonce fold followed by the root node reproduces the
keygen top tree's root. -/
theorem eval_topNode_topFoldN_honest (answers : Answers) (sig : Signature) (index : Nat) (hindex : index < 2 ^ 31)
    (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (hvalues : ∀ i, (sig.layers 0).values i = leafValue answers 0 0 (route index 0).1 digits i.val)
    (hpath : ∀ j : Fin (height 0), (sig.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) :
    evalWithAnswerFn answers (topNode index (evalWithAnswerFn answers (topFoldN sig index digits)).1
      ((sig.layers 0).path topJ)) = treeValue (builtTree answers 0 0) 12 0 := by
  have ht : (route index 0).2 = 0 := route_top_tree index hindex
  have hleaf : (route index 0).1 < 2 ^ 12 := route_leaf_bound index 0
  have htree := builtTopTree_correct answers 0
  have hends : evalWithAnswerFn answers (topEnds sig index digits) =
      (List.range (chainCount 0)).map (leafEnd answers 0 0 (route index 0).1) := by
    unfold topEnds
    rw [ht]
    exact eval_chains_honest answers 0 0 _ digits hvalid _ hvalues
  have hroot : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
      (evalWithAnswerFn answers (topEnds sig index digits))) =
      treeValue (builtTree answers 0 0) 0 (route index 0).1 := by
    rw [hends, ht, builtTree_leaf answers 0 0 _ hleaf]
    rfl
  have hfold : (evalWithAnswerFn answers (topFoldN sig index digits)).1 =
      treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11) := by
    unfold topFoldN
    simp only [evalWithAnswerFn_bind]
    rw [hroot]
    exact eval_topFoldN_steps_honest answers sig index _ _ htree hleaf hpath []
  rw [hfold, hpath topJ]
  unfold topNode
  have hpair := sibling_pair (fun k => treeValue (builtTree answers 0 0) 11 k) ((route index 0).1 / 2 ^ 11)
  have hz : (route index 0).1 / 2 ^ 11 / 2 = 0 := by
    rw [div_pow_succ]; exact Nat.div_eq_of_lt (by simpa using hleaf)
  rw [hz] at hpair
  change evalWithAnswerFn answers (nodeHash 3 0 (route index 0).2 (2 ^ (12 - 11 - 1) + (route index 0).1 / 2 ^ (11 + 1))
    (if (route index 0).1 / 2 ^ 11 % 2 = 0 then
        (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1))
      else (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11))).1
    (if (route index 0).1 / 2 ^ 11 % 2 = 0 then
        (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1))
      else (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11))).2) = _
  rw [hpair, ht, show (route index 0).1 / 2 ^ (11 + 1) = 0 by rw [← div_pow_succ]; exact hz]
  have hp := htree.2.2 11 (by decide) 0 (by decide)
  simp only [treeValue] at hp ⊢
  rw [hp]
  simp [topLevelNode]

end ClaudeWCT.WCT9
