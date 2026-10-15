import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.ClaudeWCT.WCT9.TopDecode

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def shortAnswer (answers : Answers) (input : HashInput) : Digest :=
  (answers (.inl (.inr input))).extractLsb' 0 128
theorem chain_add (index coord selected i start a b : Nat) (initial : Digest) :
    chain index coord selected i start (a + b) initial =
      (chain index coord selected i start a initial >>=
        chain index coord selected i (start + a) b) := by
  unfold chain
  rw [← List.range'_append_1, List.foldlM_append]
theorem eval_chain_add (answers : Answers) (index coord selected i start a b : Nat)
    (initial : Digest) :
    evalWithAnswerFn answers (chain index coord selected i start (a + b) initial) =
      evalWithAnswerFn answers (chain index coord selected i (start + a) b
        (evalWithAnswerFn answers (chain index coord selected i start a initial))) := by
  rw [chain_add, evalWithAnswerFn_bind]
theorem chainInput_length (index coord selected i step : Nat) (value : Digest) :
    (chainInput index coord selected i step value).length = 64 := by
  simp only [chainInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem eval_short (answers : Answers) (input : HashInput) (hlen : input.length = 64) :
    evalWithAnswerFn answers (shortHash input) = shortAnswer answers input := by
  have hpad : pad64 input = input := by simp only [pad64, hlen]; simp
  change (answers (.inl (.inr (pad64 input)))).extractLsb' 0 128 =
    (answers (.inl (.inr input))).extractLsb' 0 128
  rw [hpad]
theorem eval_chain_walk (answers : Answers) (index coord selected i start count : Nat)
    (initial : Digest) :
    evalWithAnswerFn answers (chain index coord selected i start count initial) =
      walk (fun step current => shortAnswer answers
        (chainInput index coord selected i step current)) start count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [eval_chain_add]
    change evalWithAnswerFn answers (shortHash (chainInput index coord selected i
      (start + count) (evalWithAnswerFn answers
        (chain index coord selected i start count initial)))) = _
    rw [eval_short _ _ (chainInput_length _ _ _ _ _ _), ih]
    rfl
def CarryOk (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest) : Prop :=
  q % 2 = 1 → carry = (evalWithAnswerFn answers (pairQuery (q / 2))).2
theorem eval_packedSecret (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest)
    (hcarry : CarryOk answers pairQuery q carry) :
    evalWithAnswerFn answers (packedSecret pairQuery q carry) =
      (seedHalf (evalWithAnswerFn answers (pairQuery (q / 2))) q,
        (evalWithAnswerFn answers (pairQuery (q / 2))).2) := by
  unfold packedSecret seedHalf
  by_cases h : q % 2 = 0
  · rw [if_pos h, if_pos h, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  · rw [if_neg h, if_neg h, evalWithAnswerFn_pure, hcarry (by omega)]
theorem carryOk_next (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) :
    CarryOk answers pairQuery (q + 1) (evalWithAnswerFn answers (pairQuery (q / 2))).2 := by
  intro h
  have : (q + 1) / 2 = q / 2 := by omega
  rw [this]
theorem carryOk_even (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest)
    (h : q % 2 = 0) : CarryOk answers pairQuery q carry := by
  intro h1; omega
theorem eval_ftsCoefs_range (answers : Answers) (index coord : Nat) :
    evalWithAnswerFn answers (ftsCoefs index coord) = (List.range (2 * ftsCoefPairs)).map
      (fun j => seedHalf (evalWithAnswerFn answers (ftsSeedPair index coord (j / 2))) j) := by
  unfold ftsCoefs
  refine eval_foldlM_range_inv answers ftsCoefPairs _
    (fun n acc => acc = (List.range (2 * n)).map
      (fun j => seedHalf (evalWithAnswerFn answers (ftsSeedPair index coord (j / 2))) j)) [] rfl ?_
  intro n _ acc hacc
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, hacc]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.range_succ, List.range_succ, List.map_append,
    List.map_append, List.append_assoc]
  have h0 : 2 * n / 2 = n := by omega
  have h1 : (2 * n + 1) / 2 = n := by omega
  simp [seedHalf, h0, h1]
/-- The coefficient list the signer reads is `List.ofFn (ftsCoef answers index coord)`. -/
theorem eval_ftsCoefs (answers : Answers) (index coord : Nat) :
    evalWithAnswerFn answers (ftsCoefs index coord) = List.ofFn (ftsCoef answers index coord) := by
  rw [eval_ftsCoefs_range]
  apply List.ext_getElem (by simp [ftsCoefPairs])
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, ftsCoef]
/-- Answer-level FTS seed of chain `i` of child `selected`: the seed family of `(index, coord)` evaluated at
`ftsPoint selected i`. -/
def seed (answers : Answers) (index coord selected : Nat) (i : Fin 6) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (ftsCoef answers index coord)) (ftsPoint selected i.val)
theorem seed_eq_family (answers : Answers) (index coord selected : Nat) (i : Fin 6) :
    seed answers index coord selected i =
      ftsFamilySeed (evalWithAnswerFn answers (ftsCoefs index coord)) selected i.val := by
  rw [eval_ftsCoefs]; rfl
def chainValue (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) : Digest :=
  evalWithAnswerFn answers (chain index coord selected i.val 0
    (4 - wordDigit word i) (seed answers index coord selected i))
def chainEnd (answers : Answers) (index coord selected : Nat) (i : Fin 6) : Digest :=
  evalWithAnswerFn answers (chain index coord selected i.val 0 4
    (seed answers index coord selected i))
theorem value_completes (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) :
    evalWithAnswerFn answers (chain index coord selected i.val
      (4 - wordDigit word i) (wordDigit word i) (chainValue answers index coord selected word i)) =
      chainEnd answers index coord selected i := by
  unfold chainValue chainEnd
  have hd := wordDigit_le_four word i
  have hc := eval_chain_add answers index coord selected i.val 0
    (4 - wordDigit word i) (wordDigit word i) (seed answers index coord selected i)
  rw [Nat.zero_add, Nat.sub_add_cancel hd] at hc
  exact hc.symm
def stepFn (answers : Answers) (index coord selected : Nat) (t : Fin 6) :
    Nat → Digest → Digest :=
  fun step current => shortAnswer answers (chainInput index coord selected t.val step current)
theorem chainValue_eq_opening (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) :
    chainValue answers index coord selected word i =
      opening (stepFn answers index coord selected) (seed answers index coord selected) (embed word) i := by
  unfold chainValue opening stepFn
  exact eval_chain_walk _ _ _ _ _ _ _ _
theorem chainEnd_eq_walk (answers : Answers) (index coord selected : Nat) (i : Fin 6) :
    chainEnd answers index coord selected i =
      walk (stepFn answers index coord selected i) 0 4 (seed answers index coord selected i) := by
  unfold chainEnd stepFn
  exact eval_chain_walk _ _ _ _ _ _ _ _
theorem recover_eq (answers : Answers) (index coord selected : Nat) (word : Rank)
    (values : Fin 6 → Digest) (i : Fin 6) :
    evalWithAnswerFn answers (chain index coord selected i.val (4 - wordDigit word i)
      (wordDigit word i) (values i)) =
      recover (stepFn answers index coord selected) (embed word) values i := by
  unfold recover stepFn
  exact eval_chain_walk _ _ _ _ _ _ _ _
theorem getD_append_singleton {α : Type} (xs : List α) (x d : α) (n : Nat) :
    (xs ++ [x]).getD n d = if n < xs.length then xs.getD n d else if n = xs.length then x else d := by
  by_cases hn : n < xs.length
  · rw [if_pos hn, List.getD_append _ _ _ _ hn]
  · rw [if_neg hn, List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : n = xs.length
    · subst he; simp
    · rw [if_neg he]
      rw [List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega)]
def Rows (answers : Answers) (index coord selected : Nat) (word : Rank)
    (done : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧ rows.2.length = done ∧
    (∀ i : Fin 6, i.val < done → rows.1.getD i.val 0 = chainEnd answers index coord selected i) ∧
    (∀ i : Fin 6, i.val < done →
      rows.2.getD i.val 0 = chainValue answers index coord selected word i)
def childStep (index coord selected : Nat) (word : Rank) (coefs : List Digest) (state : List Digest × List Digest)
    (i : Fin 6) : M (List Digest × List Digest) := do
  let secret := ftsFamilySeed coefs selected i.val
  let deficit := wordDigit word i
  let value ← chain index coord selected i.val 0 (4 - deficit) secret
  let last ← chain index coord selected i.val (4 - deficit) deficit value
  pure (state.1 ++ [last], state.2 ++ [value])
def childRows (index coord selected : Nat) (word : Rank) (coefs : List Digest) :
    M (List Digest × List Digest) :=
  (List.finRange 6).foldlM (childStep index coord selected word coefs) ([], [])
theorem buildChildF_factor (index coord selected : Nat) (word : Rank) (coefs : List Digest) :
    buildChildF index coord selected word coefs = (do
      let rows ← childRows index coord selected word coefs
      let root ← leafHash index coord selected rows.1
      pure (root, rows.2)) := by
  rfl
theorem rows_step (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) (rows : List Digest × List Digest)
    (hrows : Rows answers index coord selected word i.val rows) :
    Rows answers index coord selected word (i.val + 1)
      (evalWithAnswerFn answers (childStep index coord selected word
        (List.ofFn (ftsCoef answers index coord)) rows i)) := by
  rcases hrows with ⟨he, hv, hend, hval⟩
  unfold childStep
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change Rows answers index coord selected word (i.val + 1)
    (rows.1 ++ [evalWithAnswerFn answers (chain index coord selected i.val
      (4 - wordDigit word i) (wordDigit word i) (chainValue answers index coord selected word i))],
     rows.2 ++ [chainValue answers index coord selected word i])
  rw [value_completes]
  refine ⟨by simp [he], by simp [hv], ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, he]
    by_cases hji : j.val < i.val
    · rw [if_pos hji]; exact hend j hji
    · have hji' : j = i := Fin.ext (by omega)
      subst j
      simp
  · intro j hj
    rw [getD_append_singleton, hv]
    by_cases hji : j.val < i.val
    · rw [if_pos hji]; exact hval j hji
    · have hji' : j = i := Fin.ext (by omega)
      subst j
      simp
theorem eval_childRows (answers : Answers) (index coord selected : Nat) (word : Rank) :
    Rows answers index coord selected word 6
      (evalWithAnswerFn answers (childRows index coord selected word (List.ofFn (ftsCoef answers index coord)))) := by
  unfold childRows
  have key := eval_foldlM_list_inv answers (List.finRange 6)
    (childStep index coord selected word (List.ofFn (ftsCoef answers index coord)))
    (fun i rows => Rows answers index coord selected word i rows) ([], [])
    (by simp [Rows]) (by
      intro i hi rows hrows
      have hi7 : i < 6 := by simpa using hi
      simp only [List.getElem_finRange, Fin.cast_mk]
      exact rows_step answers index coord selected word ⟨i, hi7⟩ rows hrows)
  simp only [List.length_finRange] at key
  exact key
def childRoot (answers : Answers) (index coord selected : Nat) : Digest :=
  evalWithAnswerFn answers (leafHash index coord selected
    (List.ofFn (fun i : Fin 6 => chainEnd answers index coord selected i)))
theorem buildChildF_result (answers : Answers) (index coord selected : Nat) (word : Rank) :
    evalWithAnswerFn answers (buildChildF index coord selected word (List.ofFn (ftsCoef answers index coord))) =
      (childRoot answers index coord selected,
        List.ofFn (fun i : Fin 6 => chainValue answers index coord selected word i)) := by
  let rows := evalWithAnswerFn answers (childRows index coord selected word
    (List.ofFn (ftsCoef answers index coord)))
  have hr : Rows answers index coord selected word 6 rows :=
    eval_childRows answers index coord selected word
  rcases hr with ⟨he, hv, hend, hval⟩
  have hends : rows.1 = List.ofFn (fun i : Fin 6 => chainEnd answers index coord selected i) := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using he)
    intro i hi hj
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using
      hend ⟨i, by omega⟩ (by omega)
  have hvals : rows.2 = List.ofFn (fun i : Fin 6 => chainValue answers index coord selected word i) := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using hv)
    intro i hi hj
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using
      hval ⟨i, by omega⟩ (by omega)
  rw [buildChildF_factor, evalWithAnswerFn_bind]
  change (evalWithAnswerFn answers (leafHash index coord selected rows.1), rows.2) = _
  rw [hends, hvals]
  rfl
theorem childRoot_word_independent (answers : Answers) (index coord selected : Nat) (left right : Rank) :
    (evalWithAnswerFn answers (buildChildF index coord selected left (List.ofFn (ftsCoef answers index coord)))).1 =
      (evalWithAnswerFn answers (buildChildF index coord selected right
        (List.ofFn (ftsCoef answers index coord)))).1 := by
  rw [buildChildF_result, buildChildF_result]
def HeapInv (answers : Answers) (index coord : Nat) (leaves : List Digest)
    (done : Nat) (nodes : Array Digest) : Prop :=
  nodes.size = 256 ∧
    (∀ i, 128 ≤ i → i < 256 → nodes.getD i 0 = leaves.getD (i - 128) 0) ∧
    (∀ i, 2 ≤ i → i < 128 → 128 - done ≤ i → nodes.getD i 0 =
      evalWithAnswerFn answers (wctNodeHash coord index i
        (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)))
theorem getD_set_self (nodes : Array Digest) (i : Nat) (v : Digest) (hi : i < nodes.size) :
    (nodes.set! i v).getD i 0 = v := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt hi, Option.getD_some]
theorem getD_set_other (nodes : Array Digest) (i j : Nat) (v : Digest) (hij : i ≠ j) :
    (nodes.set! i v).getD j 0 = nodes.getD j 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne hij]
theorem heap_order (i : Nat) (hi : i < 126) :
    ((List.range' 2 126).reverse)[i]'(by simpa using hi) = 127 - i := by
  rw [List.getElem_reverse]
  simp only [List.length_range', List.getElem_range', Nat.one_mul]
  omega
theorem heap_initial (answers : Answers) (index coord : Nat) (leaves : List Digest)
    (hlen : leaves.length = 128) :
    HeapInv answers index coord leaves 0 ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro i hlo hhi
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate]
  · intro i _ hi hlo
    omega
theorem heap_step (answers : Answers) (index coord : Nat) (leaves : List Digest) (done : Nat)
    (hdone : done < 126) (nodes : Array Digest)
    (hinv : HeapInv answers index coord leaves done nodes) :
    HeapInv answers index coord leaves (done + 1)
      (nodes.set! (127 - done) (evalWithAnswerFn answers (wctNodeHash coord index (127 - done)
        (nodes.getD (2 * (127 - done)) 0) (nodes.getD (2 * (127 - done) + 1) 0)))) := by
  let heap := 127 - done
  let v := evalWithAnswerFn answers (wctNodeHash coord index heap
    (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0))
  change HeapInv answers index coord leaves (done + 1) (nodes.set! heap v)
  rcases hinv with ⟨hsize, hleaf, hnode⟩
  have hh : 2 ≤ heap ∧ heap < 128 := by dsimp only [heap]; omega
  refine ⟨by rw [Array.size_set!, hsize], ?_, ?_⟩
  · intro i hlo hhi
    rw [getD_set_other nodes heap i v (by omega)]
    exact hleaf i hlo hhi
  · intro i hlo hhi hdone'
    have hheap : heap ≤ i := by dsimp only [heap]; omega
    have hl : (nodes.set! heap v).getD (2 * i) 0 = nodes.getD (2 * i) 0 :=
      getD_set_other nodes heap (2 * i) v (by omega)
    have hr : (nodes.set! heap v).getD (2 * i + 1) 0 = nodes.getD (2 * i + 1) 0 :=
      getD_set_other nodes heap (2 * i + 1) v (by omega)
    rw [hl, hr]
    by_cases he : i = heap
    · subst i
      rw [getD_set_self nodes heap v (by omega)]
    · rw [getD_set_other nodes heap i v (Ne.symm he)]
      exact hnode i hlo hhi (by dsimp only [heap] at he hheap; omega)
theorem heap_complete (answers : Answers) (index coord : Nat) (leaves : List Digest)
    (hlen : leaves.length = 128) :
    HeapInv answers index coord leaves 126 (evalWithAnswerFn answers (heapBuild index coord leaves)) := by
  unfold heapBuild
  refine eval_foldlM_list_inv answers (List.range' 2 126).reverse _
    (HeapInv answers index coord leaves) _ (heap_initial answers index coord leaves hlen) ?_
  intro done hdone nodes hinv
  have hd : done < 126 := by simpa only [List.length_reverse, List.length_range'] using hdone
  rw [heap_order done hd]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact heap_step answers index coord leaves done hd nodes hinv
def coordRows (index : Nat) (coord : Coord) (selected : Child) (word : Rank) (coefs : List Digest) :
    M (List Digest × List Digest) :=
  (List.range 128).foldlM (fun (state : List Digest × List Digest) j => do
    let (root, values) ← buildChildF index coord.val j word coefs
    pure (state.1 ++ [root], (if j = selected.val then values else state.2))) ([], [])
def CoordRows (answers : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) (done : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧
    (∀ j, j < done → rows.1.getD j 0 = childRoot answers index coord.val j) ∧
    rows.2 = (if selected.val < done then
      List.ofFn (fun i : Fin 6 => chainValue answers index coord.val selected.val word i)
      else [])
def coordLeaves (answers : Answers) (index : Nat) (coord : Coord) : List Digest :=
  List.ofFn (fun j : Fin 128 => childRoot answers index coord.val j.val)
def coordNodes (answers : Answers) (index : Nat) (coord : Coord) : Array Digest :=
  evalWithAnswerFn answers (heapBuild index coord.val (coordLeaves answers index coord))
def coordinatePair (answers : Answers) (index : Nat) (coord : Coord) : Digest × Digest :=
  ((coordNodes answers index coord).getD 2 0, (coordNodes answers index coord).getD 3 0)
theorem coordRows_step (answers : Answers) (index : Nat) (coord : Coord)
    (selected : Child) (word : Rank) (done : Nat) (rows : List Digest × List Digest)
    (hrows : CoordRows answers index coord selected word done rows) :
    CoordRows answers index coord selected word (done + 1)
      (rows.1 ++ [childRoot answers index coord.val done],
       (if done = selected.val then
         List.ofFn (fun i : Fin 6 => chainValue answers index coord.val done word i)
       else rows.2)) := by
  rcases hrows with ⟨hlen, hroot, hvalues⟩
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected.val
    · subst hs; simp
    · have hs' : selected.val < done + 1 ↔ selected.val < done := by omega
      simp only [if_neg hs, hvalues, hs']
theorem eval_coordRows (answers : Answers) (index : Nat) (coord : Coord)
    (selected : Child) (word : Rank) :
    CoordRows answers index coord selected word 128
      (evalWithAnswerFn answers (coordRows index coord selected word
        (List.ofFn (ftsCoef answers index coord.val)))) := by
  unfold coordRows
  refine eval_foldlM_range_inv answers 128 _ (CoordRows answers index coord selected word)
    ([], []) ?_ ?_
  · simp [CoordRows]
  · intro done _ rows hrows
    simp only [evalWithAnswerFn_bind, buildChildF_result, evalWithAnswerFn_pure]
    exact coordRows_step answers index coord selected word done rows hrows
theorem buildCoordinateF_factor (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    buildCoordinateF index coord selected word = (do
      let coefs ← ftsCoefs index coord.val
      let rows ← coordRows index coord selected word coefs
      let heap ← heapBuild index coord.val rows.1
      pure (heapLevels heap, rows.2)) := by
  rfl
theorem buildCoordinateF_result (answers : Answers) (index : Nat) (coord : Coord)
    (selected : Child) (word : Rank) :
    evalWithAnswerFn answers (buildCoordinateF index coord selected word) =
      (heapLevels (coordNodes answers index coord),
       List.ofFn (fun i : Fin 6 => chainValue answers index coord.val selected.val word i)) := by
  let rows := evalWithAnswerFn answers (coordRows index coord selected word
    (List.ofFn (ftsCoef answers index coord.val)))
  have hr : CoordRows answers index coord selected word 128 rows :=
    eval_coordRows answers index coord selected word
  rcases hr with ⟨hlen, hroot, hvalues⟩
  have hroots : rows.1 = coordLeaves answers index coord := by
    apply List.ext_getElem (by simpa only [coordLeaves, List.length_ofFn] using hlen)
    intro j hj hk
    simpa only [coordLeaves, List.getD_eq_getElem _ _ hj, List.getElem_ofFn] using
      hroot j (by omega)
  rw [if_pos selected.isLt] at hvalues
  rw [buildCoordinateF_factor, evalWithAnswerFn_bind, eval_ftsCoefs]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (heapLevels (evalWithAnswerFn answers (heapBuild index coord.val rows.1)), rows.2) = _
  rw [hroots, hvalues]
  rfl
theorem coordNodes_graph (answers : Answers) (index : Nat) (coord : Coord) :
    HeapInv answers index coord.val (coordLeaves answers index coord) 126
      (coordNodes answers index coord) :=
  heap_complete answers index coord.val _ (by simp [coordLeaves])
theorem heapLevels_value (heap : Array Digest) (level j : Nat) (hl : level < 7)
    (hj : j < 2 ^ (7 - level)) :
    treeValue (heapLevels heap) level j = heap.getD (2 ^ (7 - level) + j) 0 := by
  unfold treeValue heapLevels
  rw [List.getD_eq_getElem _ [] (by simp only [List.length_map, List.length_range]; exact hl)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hj)]
  simp only [List.getElem_map, List.getElem_range]
theorem coordinate_treeLevels (answers : Answers) (index : Nat) (coord : Coord) :
    TreeLevels answers 3 (nodeLayer coord.val) index 7 (coordLeaves answers index coord) 6
      (heapLevels (coordNodes answers index coord)) := by
  have hg := coordNodes_graph answers index coord
  refine ⟨⟨by simp only [heapLevels, List.length_map, List.length_range], ?_⟩, ?_, ?_⟩
  · intro j hj
    unfold heapLevels
    rw [List.getD_eq_getElem _ [] (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  · have h0 : (heapLevels (coordNodes answers index coord)).getD 0 [] =
        (List.range 128).map (fun i => (coordNodes answers index coord).getD (128 + i) 0) := rfl
    rw [h0]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, coordLeaves, List.length_ofFn]
    · intro i hi hj
      have hi' : i < 128 := by simpa only [List.length_map, List.length_range] using hi
      simp only [List.getElem_map, List.getElem_range, coordLeaves, List.getElem_ofFn]
      rw [hg.2.1 (128 + i) (by omega) (by omega), Nat.add_sub_cancel_left, coordLeaves,
        List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hi'), List.getElem_ofFn]
  · intro level hlevel node hnode
    have hpow : 2 ^ (7 - level) = 2 * 2 ^ (7 - (level + 1)) := by
      rw [show 7 - level = 7 - (level + 1) + 1 by omega, pow_succ]
      omega
    have hpos : 2 ≤ 2 ^ (7 - (level + 1)) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (7 - (level + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have hle : 2 ^ (7 - (level + 1)) ≤ 64 :=
      Nat.pow_le_pow_right (by decide) (by omega : 7 - (level + 1) ≤ 6) |>.trans (by decide)
    have hv := heapLevels_value (coordNodes answers index coord) (level + 1) node (by omega) hnode
    unfold treeValue at hv
    rw [hv]
    have hl := heapLevels_value (coordNodes answers index coord) level (2 * node) (by omega)
      (by omega)
    have hr := heapLevels_value (coordNodes answers index coord) level (2 * node + 1) (by omega)
      (by omega)
    unfold treeValue at hl hr
    rw [hl, hr]
    have hn := hg.2.2 (2 ^ (7 - (level + 1)) + node) (by omega) (by omega) (by omega)
    rw [hn]
    have e1 : 2 * (2 ^ (7 - (level + 1)) + node) = 2 ^ (7 - level) + 2 * node := by omega
    simp only [e1, Nat.add_assoc]
    rfl
theorem built_pair (answers : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) :
    (((evalWithAnswerFn answers (buildCoordinateF index coord selected word)).1.getD 6 []).getD 0 0,
      ((evalWithAnswerFn answers (buildCoordinateF index coord selected word)).1.getD 6 []).getD 1 0) =
      coordinatePair answers index coord := by
  rw [buildCoordinateF_result]
  have h0 := heapLevels_value (coordNodes answers index coord) 6 0 (by decide) (by decide)
  have h1 := heapLevels_value (coordNodes answers index coord) 6 1 (by decide) (by decide)
  unfold treeValue at h0 h1
  rw [h0, h1]
  rfl
theorem eval_merklePath_le (answers : Answers) (tag lay tree h completed start n node : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree h leaves completed levels)
    (hc : completed ≤ h) (hsteps : start + n ≤ completed) (hnode : node < 2 ^ (h - start))
    (path : Fin n → Digest)
    (hpath : ∀ j, path j = treeValue levels (start + j.val) (node / 2 ^ j.val ^^^ 1)) :
    evalWithAnswerFn answers ((List.finRange n).foldlM (fun value j => do
      let other := path j
      let pair := if node / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      nodeHash tag lay tree (2 ^ (h - (start + j.val + 1)) + node / 2 ^ (j.val + 1)) pair.1 pair.2)
      (treeValue levels start node)) = treeValue levels (start + n) (node / 2 ^ n) := by
  have hi := eval_foldlM_list_inv answers (List.finRange n)
    (fun value j => do
      let other := path j
      let pair := if node / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      nodeHash tag lay tree (2 ^ (h - (start + j.val + 1)) + node / 2 ^ (j.val + 1)) pair.1 pair.2)
    (fun i value => value = treeValue levels (start + i) (node / 2 ^ i))
    (treeValue levels start node) (by simp) (fun i hi value hv => ?_)
  · simpa only [List.length_finRange] using hi
  · simp only [List.length_finRange] at hi
    simp only [List.getElem_finRange, Fin.val_cast, hpath, hv]
    rw [sibling_pair, div_pow_succ]
    have hp := htree.2.2 (start + i) (by omega) (node / 2 ^ (i + 1))
      (div_pow_bound (start := start) (level := i + 1) (by omega) hnode)
    simpa only [treeValue, Nat.add_assoc] using hp.symm
def honestOpening (built : List (List Digest) × List Digest) (selected : Child) : Opening :=
  let path := (List.range 7).map fun level =>
    (built.1.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
  ⟨fun i => built.2.getD i.val 0, fun i => path.getD i.val 0⟩
def expectedOpening (answers : Answers) (index : Nat) (output : HashOutput) (coord : Coord) :
    Opening :=
  honestOpening (evalWithAnswerFn answers
    (buildCoordinateF index coord (child output coord) (rank output coord))) (child output coord)
theorem order_pair (levels : List (List Digest)) (selected : Nat) (hs : selected < 128) :
    (if selected / 2 ^ 6 % 2 = 0 then (treeValue levels 6 (selected / 2 ^ 6), treeValue levels 6 (selected / 2 ^ 6 ^^^ 1))
      else (treeValue levels 6 (selected / 2 ^ 6 ^^^ 1), treeValue levels 6 (selected / 2 ^ 6))) =
      (treeValue levels 6 0, treeValue levels 6 1) := by
  have hq : selected / 2 ^ 6 < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    norm_num; omega
  rcases (show selected / 2 ^ 6 = 0 ∨ selected / 2 ^ 6 = 1 by omega) with h | h <;> rw [h] <;> rfl
theorem recoverCoordinate_honest (answers : Answers) (sig : Signature) (index : Nat)
    (output : HashOutput) (coord : Coord)
    (hopen : sig.openings coord = expectedOpening answers index output coord) :
    evalWithAnswerFn answers (recoverCoordinate sig index output coord) =
      coordinatePair answers index coord := by
  let selected := child output coord
  let word := rank output coord
  let levels := heapLevels (coordNodes answers index coord)
  have hbuilt := buildCoordinateF_result answers index coord selected word
  have hvalues : ∀ i : Fin 6, (sig.openings coord).values i =
      chainValue answers index coord.val selected.val word i := by
    intro i
    rw [hopen]
    simp only [expectedOpening, honestOpening]
    change (evalWithAnswerFn answers (buildCoordinateF index coord selected word)).2.getD i.val 0 = _
    rw [hbuilt]
    change (List.ofFn _).getD i.val 0 = _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  have hpath7 : ∀ j : Fin 7, (sig.openings coord).path j =
      treeValue levels j.val (selected.val / 2 ^ j.val ^^^ 1) := by
    intro j
    rw [hopen]
    simp only [expectedOpening, honestOpening]
    change ((List.range 7).map fun level =>
      ((evalWithAnswerFn answers (buildCoordinateF index coord selected word)).1.getD level []).getD
        (selected.val / 2 ^ level ^^^ 1) 0).getD j.val 0 = _
    rw [hbuilt]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [treeValue, levels]
  have hpath : ∀ j : Fin 6, (sig.openings coord).path j.castSucc =
      treeValue levels (0 + j.val) (selected.val / 2 ^ j.val ^^^ 1) := by
    intro j
    rw [hpath7, Nat.zero_add]
    rfl
  have hends : (List.finRange 6).map (fun i => evalWithAnswerFn answers
      (chain index coord.val selected.val i.val (4 - wordDigit word i) (wordDigit word i)
        ((sig.openings coord).values i))) =
      List.ofFn (fun i : Fin 6 => chainEnd answers index coord.val selected.val i) := by
    simp_rw [hvalues, value_completes]
    exact List.ofFn_eq_map.symm
  have hleaf : childRoot answers index coord.val selected.val = treeValue levels 0 selected.val := by
    have ht := (coordinate_treeLevels answers index coord).2.1
    unfold treeValue
    change _ = ((heapLevels (coordNodes answers index coord)).getD 0 []).getD selected.val 0
    rw [ht]
    unfold coordLeaves
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact selected.isLt),
      List.getElem_ofFn]
  have hmerkle := eval_merklePath_le answers 3 (nodeLayer coord.val) index 7 6 0 6 selected.val levels
    (coordLeaves answers index coord) (coordinate_treeLevels answers index coord)
    (by decide) (by decide) (by simp only [Nat.sub_zero]; exact selected.isLt)
    (fun j => (sig.openings coord).path j.castSucc) hpath
  have hfun : (fun (value : Digest) (level : Fin 6) => do
      let other := (sig.openings coord).path level.castSucc
      let pair := if selected.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      wctNodeHash coord.val index (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1))
        pair.1 pair.2) =
      (fun value j => do
      let other := (fun j : Fin 6 => (sig.openings coord).path j.castSucc) j
      let pair := if selected.val / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      nodeHash 3 (nodeLayer coord.val) index (2 ^ (7 - (0 + j.val + 1)) + selected.val / 2 ^ (j.val + 1))
        pair.1 pair.2) := by
    funext value j
    have hj : 7 - (0 + j.val + 1) = 6 - j.val := by omega
    rw [hj]
    rfl
  have hother : (sig.openings coord).path 6 = treeValue levels 6 (selected.val / 2 ^ 6 ^^^ 1) := hpath7 6
  have hroot : evalWithAnswerFn answers (leafHash index coord.val selected.val
      (List.ofFn fun i : Fin 6 => chainEnd answers index coord.val selected.val i)) =
      treeValue levels 0 selected.val := hleaf
  simp only [Nat.zero_add, show ∀ j : Nat, 7 - (j + 1) = 6 - j from fun j => by omega] at hmerkle
  unfold recoverCoordinate
  simp only [evalWithAnswerFn_bind, eval_mapM, evalWithAnswerFn_pure, wctNodeHash]
  rw [hends, hroot, hmerkle, hother, order_pair levels selected.val selected.isLt]
  have h0 := heapLevels_value (coordNodes answers index coord) 6 0 (by decide) (by decide)
  have h1 := heapLevels_value (coordNodes answers index coord) 6 1 (by decide) (by decide)
  rw [h0, h1]
  rfl
theorem recoverFts_honest (answers : Answers) (sig : Signature) (index : Nat)
    (output : HashOutput)
    (hopen : ∀ coord, sig.openings coord = expectedOpening answers index output coord) :
    evalWithAnswerFn answers (recoverFts sig index output) =
      evalWithAnswerFn answers (forestPk index (List.ofFn (coordinatePair answers index))) := by
  unfold recoverFts
  simp only [evalWithAnswerFn_bind, eval_mapM]
  have hpairs : (List.finRange 9).map
      (fun coord => evalWithAnswerFn answers (recoverCoordinate sig index output coord)) =
      List.ofFn (coordinatePair answers index) := by
    simp_rw [fun coord => recoverCoordinate_honest answers sig index output coord (hopen coord)]
    exact List.ofFn_eq_map.symm
  rw [hpairs]
theorem layerEncodingInput_forest (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32) :
    layerEncodingInput lay tree leaf (.forest root) counter = encodingInput lay tree leaf root counter := rfl
theorem layerCounterSearch_some_search (answers : Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter found digits, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) = some (found, digits) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        producerDecode lay (evalWithAnswerFn answers (shortHash (layerEncodingInput lay tree leaf msg found))) =
          some digits := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits _ he
      simp [layerCounterSearch] at he
  | succ fuel ih =>
      intro counter found digits hlimit he
      simp only [layerCounterSearch, evalWithAnswerFn_bind] at he
      cases hd : producerDecode lay (evalWithAnswerFn answers
        (shortHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd] at he
          obtain ⟨hlo, hhi, hgood⟩ := ih (counter + 1) found digits (by omega) he
          exact ⟨by omega, by omega, hgood⟩
      | some values =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hcount : (BitVec.ofNat 32 counter).toNat = counter := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact ⟨by rw [hcount], by rw [hcount]; omega, hd⟩
theorem layerCounterSearch_some (answers : Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter found digits, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) = some (found, digits) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        decode lay (evalWithAnswerFn answers (shortHash (layerEncodingInput lay tree leaf msg found))) =
          some digits := by
  intro fuel counter found digits hlimit he
  obtain ⟨h1, h2, h3⟩ := layerCounterSearch_some_search answers lay tree leaf msg fuel counter found digits hlimit he
  exact ⟨h1, h2, producerDecode_decode h3⟩
theorem ofNat_layer_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt hn
theorem expandLayersBC_verified (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg root counters,
      evalWithAnswerFn answers (expandLayersBC sig index n msg) = some (root, counters) →
      counters.length = n ∧ ∀ w : Witness, w.signature = sig →
        (∀ lay : Layer, lay.val < n → w.counters lay = counters.getD lay.val 0) →
        evalWithAnswerFn answers (verifyLayersBC w index n msg) = some root := by
  intro n
  induction n with
  | zero =>
      intro _ msg root counters he
      simp [expandLayersBC] at he
  | succ n ih =>
      intro hn msg root counters he
      simp only [expandLayersBC, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hdecode⟩ := layerCounterSearch_some answers (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            (searchLimit (Fin.ofNat 4 n)) 0 counter digits (by unfold counterLimit at hlim; omega) hs
          have hnot : ¬counter.toNat ≥ verifyWindow := ctr_not_ge_verifyWindow counter
          have hlay := ofNat_layer_val n (by omega)
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq,
              Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            refine ⟨rfl, fun w hw hc => ?_⟩
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            simp only [verifyLayersBC, hcounter, hnot, ite_false, evalWithAnswerFn_bind, if_true]
            rw [verifyTop_of_decode _ _ hdecode, evalWithAnswerFn_map, hw]
            rfl
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            cases hr : evalWithAnswerFn answers (expandLayersBC sig index n
              (.pair (evalWithAnswerFn answers (recoverLayerPair sig index (Fin.ofNat 4 n) digits)).1
                (evalWithAnswerFn answers (recoverLayerPair sig index (Fin.ofNat 4 n) digits)).2)) with
            | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                obtain ⟨previousRoot, previousCounters⟩ := previous
                simp only [hr, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                obtain ⟨hlen, hverify⟩ := ih (by omega) _ _ _ hr
                refine ⟨by simp [hlen], fun w hw hc => ?_⟩
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previousCounters [counter] 0 n (by omega), hlen]
                  simp
                simp only [verifyLayersBC, hcounter, hnot, ite_false, evalWithAnswerFn_bind, hdecode, hn0, hw]
                apply hverify w hw
                intro lay hsmall
                rw [hc lay (by omega), List.getD_append previousCounters [counter] 0 lay.val (by omega)]
/-- Stage B: coefficient `j` of the seed family of a lower leaf, the packed half `lowerCoefOrdinal leaf j` of
`lowerSeedPair lay tree`. -/
def lowerCoefN (answers : Answers) (lay : Layer) (tree leaf j : Nat) : Digest :=
  seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree (lowerCoefOrdinal leaf j / 2))) (lowerCoefOrdinal leaf j)
def lowerCoef (answers : Answers) (lay : Layer) (tree leaf : Nat) (j : Fin 17) : Digest :=
  lowerCoefN answers lay tree leaf j.val
/-- Stage B: the lower WOTS seed of chain `i` is the leaf's degree-16 family evaluated at `lowerPoint i`. -/
def lowerSeed (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (lowerCoef answers lay tree leaf)) (lowerPoint i)
/-! ### Campaign T8D: one seed family per leaf at every layer (security-facing view)
Top leaves (24 coefficients, `Correctness.topCoefN`) and lower leaves (17 coefficients, `lowerCoefN`) are both read
through the cells `lowerSeedPair lay tree (famOrdinal lay leaf j / 2)`, half `famOrdinal lay leaf j % 2`, and the seed
of chain `i` is the family evaluated at `i + 1` (`wotsSeed_fam`). -/
def famCount (lay : Layer) : Nat := if lay = 0 then topCoefCount else lowerCoefCount
def famOrdinal (lay : Layer) (leaf j : Nat) : Nat := famCount lay * leaf + j
def famCoefN (answers : Answers) (lay : Layer) (tree leaf j : Nat) : Digest :=
  seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree (famOrdinal lay leaf j / 2))) (famOrdinal lay leaf j)
def famCoef (answers : Answers) (lay : Layer) (tree leaf : Nat) (j : Fin (famCount lay)) : Digest :=
  famCoefN answers lay tree leaf j.val
theorem famCount_top : famCount 0 = 24 := rfl
theorem famCount_lower {lay : Layer} (h : lay ≠ 0) : famCount lay = 17 := by
  unfold famCount; rw [if_neg h]; rfl
theorem famCount_ge (lay : Layer) : 17 ≤ famCount lay := by
  unfold famCount; split_ifs <;> decide
theorem famCount_le (lay : Layer) : famCount lay ≤ 24 := by
  unfold famCount; split_ifs <;> decide
theorem famOrdinal_div_lt {lay : Layer} {leaf j : Nat} (hl : leaf < 2 ^ 24) (hj : j < famCount lay) :
    famOrdinal lay leaf j / 2 < 2 ^ 32 := by
  have h24 := famCount_le lay
  have : famCount lay * leaf ≤ 24 * leaf := Nat.mul_le_mul_right _ h24
  unfold famOrdinal
  omega
theorem famOrdinal_inj {lay : Layer} {l l' j j' : Nat} (hj : j < famCount lay) (hj' : j' < famCount lay)
    (h : famOrdinal lay l j = famOrdinal lay l' j') : l = l' ∧ j = j' := by
  unfold famOrdinal at h
  rcases Nat.lt_or_ge l l' with hlt | hge
  · exfalso
    have : famCount lay * l + famCount lay ≤ famCount lay * l' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rcases Nat.lt_or_ge l' l with hlt' | hge'
    · exfalso
      have : famCount lay * l' + famCount lay ≤ famCount lay * l := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt'
      omega
    · have hll : l = l' := by omega
      subst hll
      exact ⟨rfl, by omega⟩
/-- The WOTS seed of chain `i` of leaf `(lay, tree, leaf)`: its leaf family evaluated at `i + 1` (campaign T8D: every
layer; the cells are tree-indexed, `lowerSeedPair lay tree`, so at the top only tree `0` is the keygen tree,
`wotsSeed_top`). -/
def wotsSeed (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (famCoef answers lay tree leaf)) (i + 1)
theorem wotsSeed_fam (answers : Answers) (lay : Layer) (tree leaf i : Nat) :
    wotsSeed answers lay tree leaf i =
      ClaudeWCT.Arith.familyEval (List.ofFn (famCoef answers lay tree leaf)) (i + 1) := rfl
def wotsValue (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) : Digest :=
  evalWithAnswerFn answers (SigGolfCandidate.T3.chain lay tree leaf i 0 (digits.getD i 0)
    (wotsSeed answers lay tree leaf i))
def wotsEnd (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  evalWithAnswerFn answers (SigGolfCandidate.T3.chain lay tree leaf i 0 (maxDigit lay i)
    (wotsSeed answers lay tree leaf i))
def wotsRoot (answers : Answers) (lay : Layer) (tree leaf : Nat) : Digest :=
  evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash lay tree leaf
    ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf)))
def wotsTree (answers : Answers) (lay : Layer) (tree : Nat) : List (List Digest) :=
  evalWithAnswerFn answers (buildLevels 3 lay.val tree (height lay)
    ((List.range (2 ^ height lay)).map (wotsRoot answers lay tree)))
def wotsPieces (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : Pieces :=
  ((List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits),
   (List.range (height lay)).map fun j => treeValue (wotsTree answers lay tree) j (leaf / 2 ^ j ^^^ 1))
/-- The keygen top tree (tree `0`): the family seeds of `T3.Correctness.leafSeed` (`topLeafSeed`). -/
theorem wotsSeed_top (answers : Answers) (leaf i : Nat) :
    wotsSeed answers 0 0 leaf i = leafSeed answers 0 0 leaf i := by
  rw [leafSeed_top]
  rfl
theorem wotsSeed_lower (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf i : Nat) :
    wotsSeed answers lay tree leaf i = lowerSeed answers lay tree leaf i := by
  unfold wotsSeed lowerSeed lowerPoint
  have e : List.ofFn (famCoef answers lay tree leaf) = List.ofFn (lowerCoef answers lay tree leaf) := by
    apply List.ext_getElem (by simp [famCount_lower hlay])
    intro j h1 h2
    simp only [List.getElem_ofFn, famCoef, lowerCoef, famCoefN, lowerCoefN, famOrdinal, lowerCoefOrdinal,
      famCount_lower hlay, lowerCoefCount, Fin.coe_cast]
  rw [e]
theorem wotsValue_top (answers : Answers) (leaf : Nat) (digits : List Nat) :
    wotsValue answers 0 0 leaf digits = leafValue answers 0 0 leaf digits := by
  funext i; unfold wotsValue leafValue; rw [wotsSeed_top]
theorem wotsEnd_top (answers : Answers) (leaf : Nat) :
    wotsEnd answers 0 0 leaf = leafEnd answers 0 0 leaf := by
  funext i; unfold wotsEnd leafEnd; rw [wotsSeed_top]
theorem wotsRoot_top (answers : Answers) :
    wotsRoot answers 0 0 = leafRoot answers 0 0 := by
  funext leaf; unfold wotsRoot leafRoot; rw [wotsEnd_top]
theorem wotsTree_top (answers : Answers) :
    wotsTree answers 0 0 = builtTree answers 0 0 := by
  unfold wotsTree builtTree; rw [wotsRoot_top]
theorem wotsPieces_top (answers : Answers) (leaf : Nat) (digits : List Nat) :
    wotsPieces answers 0 0 leaf digits = honestPieces answers 0 0 leaf digits := by
  unfold wotsPieces honestPieces; rw [wotsValue_top, wotsTree_top]
theorem wotsValue_completes (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits) (i : Nat) (hi : i < chainCount lay) :
    evalWithAnswerFn answers (SigGolfCandidate.T3.chain lay tree leaf i (digits.getD i 0)
      (maxDigit lay i - digits.getD i 0) (wotsValue answers lay tree leaf digits i)) =
      wotsEnd answers lay tree leaf i := by
  unfold wotsValue wotsEnd
  have hd := hvalid i hi
  have hc := SigGolfCandidate.T3.Correctness.eval_chain_add answers lay tree leaf i 0 (digits.getD i 0)
    (maxDigit lay i - digits.getD i 0) (wotsSeed answers lay tree leaf i)
  rw [Nat.zero_add, Nat.add_sub_of_le hd] at hc
  exact hc.symm
def coefCarry (answers : Answers) (lay : Layer) (tree leaf : Nat) (carry : Digest) (done : Nat) : Digest :=
  if done = 0 then carry
  else (evalWithAnswerFn answers (lowerSeedPair lay tree (lowerCoefOrdinal leaf (done - 1) / 2))).2
def CoefRows (answers : Answers) (lay : Layer) (tree leaf : Nat) (carry : Digest) (done : Nat)
    (rows : List Digest × Digest) : Prop :=
  rows.1 = (List.range done).map (lowerCoefN answers lay tree leaf) ∧ rows.2 = coefCarry answers lay tree leaf carry done
theorem eval_lowerCoefs_inv (answers : Answers) (lay : Layer) (tree leaf : Nat) (carry : Digest)
    (hcarry : CarryOk answers (lowerSeedPair lay tree) (lowerCoefOrdinal leaf 0) carry) :
    CoefRows answers lay tree leaf carry lowerCoefCount (evalWithAnswerFn answers (lowerCoefs lay tree leaf carry)) := by
  unfold lowerCoefs
  refine eval_foldlM_range_inv answers lowerCoefCount _ (CoefRows answers lay tree leaf carry) ([], carry)
    ⟨rfl, by simp [coefCarry]⟩ ?_
  intro j _ rows hrows
  obtain ⟨h1, h2⟩ := hrows
  have hok : CarryOk answers (lowerSeedPair lay tree) (lowerCoefOrdinal leaf j) rows.2 := by
    rw [h2]
    unfold coefCarry
    by_cases h0 : j = 0
    · rw [if_pos h0, h0]; exact hcarry
    · rw [if_neg h0]
      have := carryOk_next answers (lowerSeedPair lay tree) (lowerCoefOrdinal leaf (j - 1))
      have hq : lowerCoefOrdinal leaf (j - 1) + 1 = lowerCoefOrdinal leaf j := by
        unfold lowerCoefOrdinal; omega
      rwa [hq] at this
  simp only [evalWithAnswerFn_bind, eval_packedSecret answers _ _ _ hok, evalWithAnswerFn_pure]
  refine ⟨?_, ?_⟩
  · rw [h1, List.range_succ, List.map_append]
    rfl
  · unfold coefCarry
    rw [if_neg (by omega), Nat.add_sub_cancel]
theorem ofFn_lowerCoef (answers : Answers) (lay : Layer) (tree leaf : Nat) :
    List.ofFn (lowerCoef answers lay tree leaf) = (List.range lowerCoefCount).map (lowerCoefN answers lay tree leaf) := by
  apply List.ext_getElem (by simp [lowerCoefCount])
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, lowerCoef]
/-- The carry left by the coefficient loop of a leaf: the high half of the pair of its last coefficient. -/
def leafCarryOut (answers : Answers) (lay : Layer) (tree leaf : Nat) : Digest :=
  (evalWithAnswerFn answers (lowerSeedPair lay tree (lowerCoefOrdinal leaf (lowerCoefCount - 1) / 2))).2
theorem eval_lowerCoefs (answers : Answers) (lay : Layer) (tree leaf : Nat) (carry : Digest)
    (hcarry : CarryOk answers (lowerSeedPair lay tree) (lowerCoefOrdinal leaf 0) carry) :
    evalWithAnswerFn answers (lowerCoefs lay tree leaf carry) =
      (List.ofFn (lowerCoef answers lay tree leaf), leafCarryOut answers lay tree leaf) := by
  obtain ⟨h1, h2⟩ := eval_lowerCoefs_inv answers lay tree leaf carry hcarry
  rw [ofFn_lowerCoef]
  refine Prod.ext h1 ?_
  rw [h2]
  unfold coefCarry leafCarryOut
  rw [if_neg (by decide)]
theorem lowerFamilySeed_eq (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf i : Nat) :
    lowerFamilySeed (List.ofFn (lowerCoef answers lay tree leaf)) i = wotsSeed answers lay tree leaf i := by
  rw [wotsSeed_lower answers hlay]
  rfl
def LeafRowsF (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (done : Nat)
    (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧ rows.2.length = done ∧
    (∀ i, i < done → rows.1.getD i 0 = wotsEnd answers lay tree leaf i) ∧
    (∀ i, i < done → rows.2.getD i 0 = wotsValue answers lay tree leaf digits i)
def leafStepF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Nat) : M (List Digest × List Digest) := do
  let digit := digits.getD i 0
  let value ← SigGolfCandidate.T3.chain lay tree leaf i 0 digit (lowerFamilySeed coefs i)
  let last ← SigGolfCandidate.T3.chain lay tree leaf i digit (maxDigit lay i - digit) value
  pure (state.1 ++ [last], state.2 ++ [value])
def leafRowsF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest) :
    M (List Digest × List Digest) :=
  (List.range (chainCount lay)).foldlM (leafStepF lay tree leaf digits coefs) ([], [])
theorem buildLeafPF_factor (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : Digest) :
    buildLeafPF lay tree leaf digits carry = (do
      let coefs ← lowerCoefs lay tree leaf carry
      let rows ← leafRowsF lay tree leaf digits coefs.1
      let root ← SigGolfCandidate.T3.leafHash lay tree leaf rows.1
      pure ((root, rows.2), coefs.2)) := by
  rfl
theorem leafStepF_inv (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (i : Nat) (hi : i < chainCount lay) (rows : List Digest × List Digest)
    (hrows : LeafRowsF answers lay tree leaf digits i rows) :
    LeafRowsF answers lay tree leaf digits (i + 1)
      (evalWithAnswerFn answers (leafStepF lay tree leaf digits (List.ofFn (lowerCoef answers lay tree leaf)) rows i)) := by
  rcases hrows with ⟨he, hv, hend, hval⟩
  unfold leafStepF
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [lowerFamilySeed_eq answers hlay]
  change LeafRowsF answers lay tree leaf digits (i + 1)
    (rows.1 ++ [evalWithAnswerFn answers (SigGolfCandidate.T3.chain lay tree leaf i (digits.getD i 0)
      (maxDigit lay i - digits.getD i 0) (wotsValue answers lay tree leaf digits i))],
     rows.2 ++ [wotsValue answers lay tree leaf digits i])
  rw [wotsValue_completes answers lay tree leaf digits hvalid i hi]
  refine ⟨by simp [he], by simp [hv], ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, he]
    by_cases hji : j < i
    · rw [if_pos hji]; exact hend j hji
    · have hji' : j = i := by omega
      subst j
      simp
  · intro j hj
    rw [getD_append_singleton, hv]
    by_cases hji : j < i
    · rw [if_pos hji]; exact hval j hji
    · have hji' : j = i := by omega
      subst j
      simp
theorem eval_leafRowsF (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    evalWithAnswerFn answers (leafRowsF lay tree leaf digits (List.ofFn (lowerCoef answers lay tree leaf))) =
      ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf),
        (List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits)) := by
  have hr : LeafRowsF answers lay tree leaf digits (chainCount lay)
      (evalWithAnswerFn answers (leafRowsF lay tree leaf digits (List.ofFn (lowerCoef answers lay tree leaf)))) := by
    unfold leafRowsF
    exact eval_foldlM_range_inv answers (chainCount lay) _ (LeafRowsF answers lay tree leaf digits) ([], [])
      (by simp [LeafRowsF]) (fun i hi rows hrows => leafStepF_inv answers hlay tree leaf digits hvalid i hi rows hrows)
  rcases hr with ⟨he, hv, hend, hval⟩
  exact Prod.ext (list_eq_range_map _ _ _ he hend) (list_eq_range_map _ _ _ hv hval)
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
theorem buildLeafPF_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (carry : Digest)
    (hcarry : CarryOk answers (lowerSeedPair lay tree) (lowerCoefOrdinal leaf 0) carry) :
    evalWithAnswerFn answers (buildLeafPF lay tree leaf digits carry) =
      ((wotsRoot answers lay tree leaf, (List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits)),
       leafCarryOut answers lay tree leaf) := by
  rw [buildLeafPF_factor, evalWithAnswerFn_bind, eval_lowerCoefs answers lay tree leaf carry hcarry]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_leafRowsF answers hlay tree leaf digits hvalid]
  rfl
def treeCarry (answers : Answers) (lay : Layer) (tree leaf : Nat) : Digest :=
  if leaf = 0 then 0 else leafCarryOut answers lay tree (leaf - 1)
theorem carryOk_treeCarry (answers : Answers) (lay : Layer) (tree leaf : Nat) :
    CarryOk answers (lowerSeedPair lay tree) (lowerCoefOrdinal leaf 0) (treeCarry answers lay tree leaf) := by
  unfold treeCarry
  by_cases h : leaf = 0
  · rw [if_pos h]; exact carryOk_even _ _ _ _ (by subst h; simp [lowerCoefOrdinal])
  · rw [if_neg h]
    have := carryOk_next answers (lowerSeedPair lay tree) (lowerCoefOrdinal (leaf - 1) (lowerCoefCount - 1))
    have hq : lowerCoefOrdinal (leaf - 1) (lowerCoefCount - 1) + 1 = lowerCoefOrdinal leaf 0 := by
      unfold lowerCoefOrdinal lowerCoefCount
      omega
    rwa [hq] at this
def treeRowsP (lay : Layer) (tree selected : Nat) (digits : List Nat) : M (List Digest × List Digest × Digest) :=
  (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × Digest) leaf => do
      let ((root, values), carry) ← buildLeafPF lay tree leaf (if leaf = selected then digits else []) state.2.2
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), carry)) ([], [], 0)
theorem buildTreeP_factor (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    buildTreeP lay tree selected digits = (do
      let rows ← treeRowsP lay tree selected digits
      let levels ← buildLevelsBelow 3 lay.val tree (height lay) rows.1
      pure (levels, rows.2.1)) := by
  rfl
theorem buildLevels_eq_below (tag lay tree h : Nat) (leaves : List Digest) (hh : 1 ≤ h) :
    buildLevels tag lay tree h leaves = (buildLevelsBelow tag lay tree h leaves >>= fun levels => do
      let nodes ← buildLevel tag lay tree h h (levels.getD (h - 1) [])
      pure (levels ++ [nodes])) := by
  unfold buildLevels buildLevelsBelow
  rw [show h = (h - 1) + 1 from by omega, ← List.range'_append_1, List.foldlM_append]
  simp only [show 1 + (h - 1) = h - 1 + 1 by omega, List.range'_one, List.foldlM_cons, List.foldlM_nil, bind_pure,
    Nat.add_sub_cancel]
theorem eval_buildLevelsBelow (answers : Answers) (tag lay tree h : Nat) (leaves : List Digest)
    (hlen : leaves.length = 2 ^ h) (hh : 1 ≤ h) :
    evalWithAnswerFn answers (buildLevelsBelow tag lay tree h leaves) =
      (evalWithAnswerFn answers (buildLevels tag lay tree h leaves)).take h := by
  have hfull := (eval_buildLevels_correct answers tag lay tree h leaves hlen).1.1
  rw [buildLevels_eq_below tag lay tree h leaves hh] at hfull ⊢
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hfull ⊢
  generalize evalWithAnswerFn answers (buildLevelsBelow tag lay tree h leaves) = L at hfull ⊢
  simp only [List.length_append, List.length_singleton] at hfull
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
theorem getD_take_of_lt {α : Type} (L : List α) {n j : Nat} (hj : j < n) (d : α) :
    (L.take n).getD j d = L.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
theorem topPair_take (lay : Layer) (L : List (List Digest)) : topPair lay (L.take (height lay)) = topPair lay L := by
  have : 1 ≤ height lay := by fin_cases lay <;> decide
  unfold topPair
  rw [getD_take_of_lt L (by omega)]
theorem map_range_take_path (L : List (List Digest)) (h : Nat) (f : Nat → Nat) :
    (List.range h).map (fun j => ((L.take h).getD j []).getD (f j) 0) =
      (List.range h).map (fun j => (L.getD j []).getD (f j) 0) :=
  List.map_congr_left fun j hj => by rw [getD_take_of_lt L (List.mem_range.mp hj)]
theorem treeValue_take (L : List (List Digest)) {n j : Nat} (hj : j < n) (x : Nat) :
    treeValue (L.take n) j x = treeValue L j x := by
  unfold treeValue
  rw [getD_take_of_lt L hj]
def TreeRowsP (answers : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat) (done : Nat)
    (rows : List Digest × List Digest × Digest) : Prop :=
  rows.1.length = done ∧ (∀ j, j < done → rows.1.getD j 0 = wotsRoot answers lay tree j) ∧
    rows.2.1 = (if selected < done then (List.range (chainCount lay)).map (wotsValue answers lay tree selected digits)
      else []) ∧
    rows.2.2 = treeCarry answers lay tree done
theorem eval_treeRowsP (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    TreeRowsP answers lay tree selected digits (2 ^ height lay)
      (evalWithAnswerFn answers (treeRowsP lay tree selected digits)) := by
  unfold treeRowsP
  refine eval_foldlM_range_inv answers (2 ^ height lay) _ (TreeRowsP answers lay tree selected digits)
    ([], [], 0) (by simp [TreeRowsP, treeCarry]) ?_
  intro done _ rows hrows
  rcases hrows with ⟨hlen, hroot, hvalues, hc⟩
  have hv : Cost.ValidDigits lay (if done = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  simp only [evalWithAnswerFn_bind, hc,
    buildLeafPF_result answers hlay tree done _ hv _ (carryOk_treeCarry answers lay tree done),
    evalWithAnswerFn_pure]
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected
    · subst hs; simp
    · have hs' : selected < done + 1 ↔ selected < done := by omega
      simp only [if_neg hs, hvalues, hs']
  · show leafCarryOut answers lay tree done = treeCarry answers lay tree (done + 1)
    unfold treeCarry
    rw [if_neg (show done + 1 ≠ 0 by omega), Nat.add_sub_cancel]
theorem eval_buildTreeP_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits) (hsel : selected < 2 ^ height lay) :
    evalWithAnswerFn answers (buildTreeP lay tree selected digits) =
      ((wotsTree answers lay tree).take (height lay),
        (List.range (chainCount lay)).map (wotsValue answers lay tree selected digits)) := by
  let rows := evalWithAnswerFn answers (treeRowsP lay tree selected digits)
  have hr : TreeRowsP answers lay tree selected digits (2 ^ height lay) rows :=
    eval_treeRowsP answers hlay tree selected digits hvalid
  rcases hr with ⟨hlen, hroot, hvalues, -⟩
  have hroots : rows.1 = (List.range (2 ^ height lay)).map (wotsRoot answers lay tree) :=
    list_eq_range_map _ _ _ hlen hroot
  rw [if_pos hsel] at hvalues
  rw [buildTreeP_factor, evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (evalWithAnswerFn answers (buildLevelsBelow 3 lay.val tree (height lay) rows.1), rows.2.1) = _
  rw [hroots, hvalues, eval_buildLevelsBelow answers 3 lay.val tree (height lay) _ (by simp)
    (by fin_cases lay <;> decide)]
  rfl
theorem wotsTree_correct (answers : Answers) (lay : Layer) (tree : Nat) :
    TreeLevels answers 3 lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (wotsRoot answers lay tree)) (height lay) (wotsTree answers lay tree) :=
  eval_buildLevels_correct answers 3 lay.val tree (height lay) _ (by simp)
theorem wotsTree_leaf (answers : Answers) (lay : Layer) (tree leaf : Nat) (hleaf : leaf < 2 ^ height lay) :
    treeValue (wotsTree answers lay tree) 0 leaf = wotsRoot answers lay tree leaf := by
  unfold treeValue
  rw [(wotsTree_correct answers lay tree).2.1]
  simp [List.getD_eq_getElem, hleaf]
theorem eval_wots_chains_honest (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (values : Fin (chainCount lay) → Digest)
    (hvalues : ∀ i, values i = wotsValue answers lay tree leaf digits i.val) :
    evalWithAnswerFn answers ((List.finRange (chainCount lay)).mapM fun i =>
      SigGolfCandidate.T3.chain lay tree leaf i.val (digits.getD i.val 0)
        (maxDigit lay i.val - digits.getD i.val 0) (values i)) =
      (List.range (chainCount lay)).map (wotsEnd answers lay tree leaf) := by
  rw [eval_mapM]
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.length_map, List.length_finRange] at hi
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, hvalues, Fin.val_cast, Fin.val_mk]
  exact wotsValue_completes answers lay tree leaf digits hvalid i hi
def builtPair (answers : Answers) (lay : Layer) (tree : Nat) : Digest × Digest :=
  topPair lay (wotsTree answers lay tree)
theorem height_pos (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem eval_recoverLayerPair_honest (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hvalues : ∀ i, (sig.layers lay).values i =
      wotsValue answers lay (route index lay).2 (route index lay).1 digits i.val)
    (hpath : ∀ j, (sig.layers lay).path j = treeValue (wotsTree answers lay (route index lay).2)
      j.val ((route index lay).1 / 2 ^ j.val ^^^ 1)) :
    evalWithAnswerFn answers (recoverLayerPair sig index lay digits) =
      builtPair answers lay (route index lay).2 := by
  have hh := height_pos lay
  have hleafB := route_leaf_bound index lay
  have hp := eval_merklePath answers 3 lay.val (route index lay).2 (height lay) 0 (height lay - 1)
    (route index lay).1 (wotsTree answers lay (route index lay).2)
    ((List.range (2 ^ height lay)).map (wotsRoot answers lay (route index lay).2))
    (wotsTree_correct answers lay (route index lay).2) (by omega)
    (by simpa using hleafB) (fun j => (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j))
    (fun j => by rw [hpath, Nat.zero_add]; rfl)
  rw [wotsTree_leaf answers lay _ _ hleafB] at hp
  simp only [Nat.zero_add] at hp
  have hother : (sig.layers lay).path (topLevel lay) =
      treeValue (wotsTree answers lay (route index lay).2) (height lay - 1)
        ((route index lay).1 / 2 ^ (height lay - 1) ^^^ 1) := hpath (topLevel lay)
  have hq : (route index lay).1 / 2 ^ (height lay - 1) < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    have he : 2 ^ (height lay - 1) * 2 = 2 ^ height lay := by
      rw [← pow_succ, Nat.sub_add_cancel hh]
    rw [Nat.mul_comm, he]
    exact hleafB
  have hq2 : (route index lay).1 / 2 ^ (height lay - 1) = 0 ∨
      (route index lay).1 / 2 ^ (height lay - 1) = 1 := by
    generalize (route index lay).1 / 2 ^ (height lay - 1) = q at hq ⊢
    omega
  have hlr : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash lay (route index lay).2 (route index lay).1
      ((List.range (chainCount lay)).map (wotsEnd answers lay (route index lay).2 (route index lay).1))) =
      wotsRoot answers lay (route index lay).2 (route index lay).1 := rfl
  unfold recoverLayerPair
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Nat.sub_sub]
  rw [eval_wots_chains_honest answers lay _ _ digits hvalid _ hvalues, hlr, hp, hother]
  unfold builtPair topPair
  rcases hq2 with h | h <;> rw [h] <;> rfl
def TopSearchesSucceedBC (answers : Answers) : Prop :=
  ∀ index, index < 2 ^ 31 → ∀ msg : LayerMsg, ∃ found,
    evalWithAnswerFn answers (layerCounterSearch (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
      (route index (Fin.ofNat 4 0)).1 msg 0 counterLimit) = some found
theorem signLayersBC_length (answers : Answers) (cache : Cache) (index : Nat) :
    ∀ n msg pieces, evalWithAnswerFn answers (signLayersBC cache index n msg) = some pieces →
      pieces.length = n := by
  intro n
  induction n with
  | zero =>
      intro msg pieces he
      simp only [signLayersBC, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst pieces
      rfl
  | succ n ih =>
      intro msg pieces he
      by_cases hn0 : n = 0
      · subst n
        unfold signLayersBC at he
        rw [evalWithAnswerFn_bind] at he
        rw [if_pos rfl, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
        subst pieces
        rfl
      · simp only [signLayersBC, evalWithAnswerFn_bind] at he
        cases hs : evalWithAnswerFn answers (layerCounterSearch (Fin.ofNat 4 n)
          (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
        | none => simp only [hs, hn0, if_false, evalWithAnswerFn_pure, reduceCtorEq] at he
        | some found =>
            obtain ⟨counter, digits⟩ := found
            have hlim := searchLimit_le (Fin.ofNat 4 n)
            have hd := (layerCounterSearch_some answers (Fin.ofNat 4 n)
              (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
              (searchLimit (Fin.ofNat 4 n)) 0 counter digits (by unfold counterLimit at hlim; omega) hs).2.2
            have hvalid := Cost.validDigits_decode hd
            simp only [hs] at he
            simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            generalize evalWithAnswerFn answers (buildTreeP (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
              (route index (Fin.ofNat 4 n)).1 digits) = built at he
            obtain ⟨levels, values⟩ := built
            simp only [evalWithAnswerFn_bind] at he
            cases hp : evalWithAnswerFn answers (signLayersBC cache index n
              (.pair (topPair (Fin.ofNat 4 n) levels).1 (topPair (Fin.ofNat 4 n) levels).2)) with
            | none => simp only [hp, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                simp only [hp, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst pieces
                simp [ih _ previous hp]
theorem signLayersBC_expandLayersBC (answers : Answers) (cache : Cache) (index : Nat)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (htop : TopSearchesSucceedBC answers) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg pieces,
      evalWithAnswerFn answers (signLayersBC cache index n msg) = some pieces →
      pieces.length = n ∧ ∀ sig : Signature, PiecesAgree (toT3Signature sig) pieces n →
        ∃ counters : List (BitVec 32), counters.length = n ∧
          evalWithAnswerFn answers (expandLayersBC sig index n msg) =
            some (treeValue (builtTree answers 0 0) 12 0, counters) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro _ hn msg pieces he
      simp only [signLayersBC, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
      | none =>
          by_cases hn0 : n = 0
          · subst n
            obtain ⟨found, hf⟩ := htop index hindex msg
            rw [show searchLimit (Fin.ofNat 4 0) = counterLimit from rfl, hf] at hs
            cases hs
          · simp only [hs, hn0, if_false, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          have hd := (layerCounterSearch_some answers (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            (searchLimit (Fin.ofNat 4 n)) 0 counter digits (by unfold counterLimit at hlim; omega) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq,
              Option.map_some, Option.getD_some] at he
            subst pieces
            refine ⟨rfl, ?_⟩
            intro sig hagree
            have hp := hagree 0 (by decide)
            simp only [Fin.val_zero, List.getD_cons_zero] at hp
            rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl] at hp
            rw [eval_signTop_honest answers cache _ digits hcache (route_leaf_bound index 0) hvalid] at hp
            have ht : (route index 0).2 = 0 := route_top_tree index hindex
            have hr := recoverLayer_honestPieces answers (toT3Signature sig) index 0 digits hvalid
              (by simpa only [ht] using hp)
            refine ⟨[counter], rfl, ?_⟩
            simp only [expandLayersBC, evalWithAnswerFn_bind, hs, if_true, evalWithAnswerFn_pure]
            change some (evalWithAnswerFn answers (recoverLayer (toT3Signature sig) index 0 digits), [counter]) =
              some (treeValue (builtTree answers 0 0) 12 0, [counter])
            rw [hr, ht]
            rfl
          · have hlay0 : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h0 => hn0 (by
              have h1 := congrArg Fin.val h0
              rwa [ofNat_layer_val n (by omega)] at h1)
            simp only [hn0, if_false, evalWithAnswerFn_bind,
              eval_buildTreeP_result answers hlay0 _ _ digits hvalid (route_leaf_bound index _), topPair_take,
              map_range_take_path] at he
            cases hp : evalWithAnswerFn answers (signLayersBC cache index n
              (.pair (topPair (Fin.ofNat 4 n) (wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).1
                (topPair (Fin.ofNat 4 n) (wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).2)) with
            | none => simp only [hp, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                simp only [hp, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst pieces
                obtain ⟨hlen, hprevious⟩ := ih (by omega) (by omega) _ previous hp
                refine ⟨by simp [hlen], ?_⟩
                intro sig hagree
                change PiecesAgree (toT3Signature sig) (previous ++ [wotsPieces answers (Fin.ofNat 4 n)
                  (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits]) (n + 1) at hagree
                have hlayer := PiecesAgree.last hlen (by omega) hagree
                have hrecover : evalWithAnswerFn answers (recoverLayerPair sig index (Fin.ofNat 4 n) digits) =
                    builtPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
                  apply eval_recoverLayerPair_honest answers sig index (Fin.ofNat 4 n) digits hvalid
                  · intro i
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).values i = _
                    rw [hlayer]
                    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
                  · intro j
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).path j = _
                    rw [hlayer]
                    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]
                obtain ⟨counters, hc, hreplay⟩ := hprevious sig (PiecesAgree.prefix hlen hagree)
                refine ⟨counters ++ [counter], by simp [hc], ?_⟩
                simp only [expandLayersBC, evalWithAnswerFn_bind, hs, hn0, if_false, hrecover]
                unfold builtPair at hrecover
                simp only [builtPair, hreplay, evalWithAnswerFn_pure]
theorem digestSearch_some_good (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter found output, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (digestSearch rho message counter fuel) = some (found, output) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        evalWithAnswerFn answers (digest rho message found) = output ∧
        producerAdmissible output = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found output _ he
      simp [digestSearch] at he
  | succ fuel ih =>
      intro counter found output hlimit he
      simp only [digestSearch, evalWithAnswerFn_bind] at he
      split at he
      · rename_i hgood
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hcount : (BitVec.ofNat 32 counter).toNat = counter := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact ⟨by rw [hcount], by rw [hcount]; omega, rfl, hgood⟩
      · obtain ⟨hlo, hhi, hrest⟩ := ih (counter + 1) found output (by omega) he
        exact ⟨by omega, by omega, hrest⟩
theorem expand_implies_verify (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true := by
  simp only [expand, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch sig.rho message 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (expandLayersBC sig (digestIndex output) 4
          (.forest (evalWithAnswerFn answers (recoverFts sig (digestIndex output) output)))) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · rename_i hroot
            have hroot : root = pk := by simpa using hroot
            simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
            subst w
            obtain ⟨_, hcounter, houtput, hprod⟩ := digestSearch_some_good answers sig.rho message
              attemptLimit 0 counter output (by decide) hd
            have hadm := admissible_of_producer hprod
            have hnot : ¬counter.toNat ≥ attemptLimit := by omega
            have hverified := (expandLayersBC_verified answers sig
              (digestIndex output) 4 (by decide) _ root counters hl).2
              ⟨sig, counter, fun lay => counters.getD lay.val 0⟩ rfl (fun _ _ => rfl)
            simp only [verify, hnot, ite_false, evalWithAnswerFn_bind, houtput, hadm,
              Bool.not_true, Bool.false_eq_true, hverified, evalWithAnswerFn_pure, hroot,
              beq_self_eq_true]
end ClaudeWCT.WCT9
