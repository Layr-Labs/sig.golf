import SigGolfCandidate.T3_Secc_WotsStructuralHonest
import SigGolfCandidate.T3_Proofs
import SigGolfCandidate.ClaudeWCT_WCT9_TopNonce
set_option Elab.async false

/-! Top-bytes layer: every query of the nonce-searched top tree `buildTopLevels` satisfies a predicate `P`,
given `P` on every trial input of every nonce search (up to the found nonce) and on the zero-nonce root input. -/
namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000

theorem topNonceSearch_fst_ge (T : Answers) (h heap : Nat) (left right : Digest) :
    ∀ fuel n, n ≤ (evalWithAnswerFn T (topNonceSearch h heap left right fuel n)).1
  | 0, n => by
      simp [topNonceSearch]
  | fuel + 1, n => by
      simp only [topNonceSearch, evalWithAnswerFn_bind]
      split
      · simp [evalWithAnswerFn_pure]
      · exact Nat.le_of_succ_le (topNonceSearch_fst_ge T h heap left right fuel (n + 1))

theorem eval_topNonceSearch_succ_of_not (T : Answers) (h heap : Nat) (left right : Digest) (fuel n : Nat)
    (hz : ¬ topZeroOk h (evalWithAnswerFn T (topNodeHashN heap n left right)) = true) :
    evalWithAnswerFn T (topNonceSearch h heap left right (fuel + 1) n) =
      evalWithAnswerFn T (topNonceSearch h heap left right fuel (n + 1)) := by
  simp only [topNonceSearch, evalWithAnswerFn_bind]
  rw [if_neg hz]

/-- (1) Generic nonce-search lemma. -/
theorem sat_topNonceSearch (T : Answers) (P : SigGolfCandidate.T3.Spec.Domain → Prop) (h heap : Nat)
    (left right : Digest) :
    ∀ fuel n, (∀ k, n ≤ k → k ≤ (evalWithAnswerFn T (topNonceSearch h heap left right fuel n)).1 →
        P (.inl (.inr (pad64 (topNodeInput heap k left right))))) →
      QueriesSat T P (topNonceSearch h heap left right fuel n)
  | 0, n, hk => by
      have h1 := hk n le_rfl (topNonceSearch_fst_ge T h heap left right 0 n)
      unfold topNonceSearch
      exact QueriesSat.bind (sat_projHash _ _ h1) (QueriesSat.pure' _)
  | fuel + 1, n, hk => by
      have h1 := hk n le_rfl (topNonceSearch_fst_ge T h heap left right (fuel + 1) n)
      have hrec : ¬ topZeroOk h (evalWithAnswerFn T (topNodeHashN heap n left right)) = true →
          QueriesSat T P (topNonceSearch h heap left right fuel (n + 1)) := fun hz =>
        sat_topNonceSearch T P h heap left right fuel (n + 1) (fun k hk1 hk2 => hk k (by omega) (by
          rw [eval_topNonceSearch_succ_of_not T h heap left right fuel n hz]
          exact hk2))
      unfold topNonceSearch
      refine QueriesSat.bind (sat_projHash _ _ h1) ?_
      split
      · exact QueriesSat.pure' _
      · next hz => exact hrec hz

def topLevelsStep (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← buildTopLevel level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])

def topLevelsFold (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM topLevelsStep [leaves]

theorem buildTopLevels_eq_fold (leaves : List Digest) : buildTopLevels leaves = topLevelsFold leaves 12 := rfl

theorem eval_topLevelsStep (T : Answers) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (topLevelsStep levels level) =
      levels ++ [evalWithAnswerFn T (buildTopLevel level (levels.getD (level - 1) []))] := by
  simp only [topLevelsStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

theorem eval_topLevelsSteps_append (T : Answers) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM topLevelsStep state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_topLevelsStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (buildTopLevel x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (buildTopLevel x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩

theorem topLevelsFold_succ (leaves : List Digest) (n : Nat) :
    topLevelsFold leaves (n + 1) =
      (topLevelsFold leaves n >>= fun state => topLevelsStep state (1 + n)) := by
  unfold topLevelsFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]

theorem topLevelsFold_length (T : Answers) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (topLevelsFold leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [topLevelsFold_succ, evalWithAnswerFn_bind, eval_topLevelsStep, List.length_append, ih]
      simp

theorem topLevelsFold_prefix (T : Answers) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (topLevelsFold leaves m) =
      evalWithAnswerFn T (topLevelsFold leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold topLevelsFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_topLevelsSteps_append T _ _

theorem nonceBytes_zero : nonceBytes 0 = zero16 := by decide

theorem nodeHash_root_eq (heap : Nat) (left right : Digest) :
    nodeHash 3 0 0 heap left right = topNodeHashN heap 0 left right := by
  unfold nodeHash topNodeHashN topNodeInput
  rw [nonceBytes_zero]

/-- (2) Every query of `buildTopLevels` satisfies `P`. -/
theorem sat_buildTopLevels (T : Answers) (P : SigGolfCandidate.T3.Spec.Domain → Prop) (leaves : List Digest)
    (hlen : leaves.length = 2 ^ 12)
    (hroot : P (.inl (.inr (pad64 (topNodeInput 1 0
      (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) 11 0)
      (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) 11 1))))))
    (htrial : ∀ level c k, level < 11 → c < 2 ^ (11 - level) →
      k ≤ (evalWithAnswerFn T (topNodeAt (level + 1) (2 ^ (11 - level) + c)
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c))
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c + 1)))).1 →
      P (.inl (.inr (pad64 (topNodeInput (2 ^ (11 - level) + c) k
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c))
        (Correctness.treeValue (evalWithAnswerFn T (buildTopLevels leaves)) level (2 * c + 1))))))) :
    QueriesSat T P (buildTopLevels leaves) := by
  have hfin := Correctness.eval_buildTopLevels_correct T leaves hlen
  rw [buildTopLevels_eq_fold] at hroot htrial hfin ⊢
  unfold topLevelsFold
  refine QueriesSat.foldlM_range' 1 12 _
    (fun i state => state = evalWithAnswerFn T (topLevelsFold leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold topLevelsStep
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    have hlen' := topLevelsFold_length T leaves i
    obtain ⟨extra, hext⟩ := topLevelsFold_prefix T leaves i 12 (by omega)
    have hget : (evalWithAnswerFn T (topLevelsFold leaves 12)).getD i [] =
        (evalWithAnswerFn T (topLevelsFold leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have hw : ((evalWithAnswerFn T (topLevelsFold leaves 12)).getD i []).length = 2 ^ (12 - i) :=
      hfin.1.2 i (by omega)
    have h1 : 1 + i - 1 = i := by omega
    rw [h1, ← hget]
    unfold buildTopLevel
    refine QueriesSat.mapM _ _ (fun c hc => ?_)
    rw [List.mem_range, hw] at hc
    split
    · next h12 =>
      have hi11 : i = 11 := by omega
      subst hi11
      have hc0 : c = 0 := by norm_num at hc; omega
      subst hc0
      rw [nodeHash_root_eq, show 2 ^ (12 - (1 + 11)) + 0 = 1 by norm_num]
      refine sat_projHash _ _ ?_
      simpa only [treeValue, Nat.mul_zero, Nat.zero_add] using hroot
    · next h12 =>
      have hi11 : i < 11 := by omega
      rw [show 12 - i = 11 - i + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)] at hc
      rw [show 1 + i = i + 1 by omega, show 12 - (i + 1) = 11 - i by omega]
      refine QueriesSat.map _ (sat_topNonceSearch T P _ _ _ _ _ 0 (fun k _ hk => ?_))
      exact htrial i c k hi11 hc hk
  · rw [topLevelsFold_succ, evalWithAnswerFn_bind]

end SigGolfCandidate.T3.Security.Wots.Structural

#print axioms SigGolfCandidate.T3.Security.Wots.Structural.sat_topNonceSearch
#print axioms SigGolfCandidate.T3.Security.Wots.Structural.sat_buildTopLevels
