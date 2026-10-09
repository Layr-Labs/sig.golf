import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.T3.Secc.WotsMask
import SigGolfCandidate.T3.Secc.CanonGraphHonest

namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
def QueriesSat (T : Answers) (Q : T3.Spec.Domain → Prop) {α : Type} (program : M α) : Prop :=
  ∀ q ∈ SourceReplay.queried T program, Q q
section QueriesSat
variable {T : Answers} {Q : T3.Spec.Domain → Prop}
theorem QueriesSat.pure' {α : Type} (x : α) : QueriesSat T Q (pure x : M α) := by
  intro q hq
  simp at hq
theorem QueriesSat.bind {α β : Type} {p : M α} {f : α → M β} (hp : QueriesSat T Q p)
    (hf : QueriesSat T Q (f (evalWithAnswerFn T p))) : QueriesSat T Q (p >>= f) := by
  intro q hq
  rw [SourceReplay.queried_bind, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hp q hq
  · exact hf q hq
theorem QueriesSat.map {α β : Type} {p : M α} (f : α → β) (hp : QueriesSat T Q p) : QueriesSat T Q (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact QueriesSat.bind hp (QueriesSat.pure' _)
theorem QueriesSat.query {q : T3.Spec.Domain} (h : Q q) : QueriesSat T Q (liftM (T3.Spec.query q)) := by
  intro q' hq'
  have he : SourceReplay.queried T (liftM (T3.Spec.query q) : M _) = [q] := by
    have := SourceReplay.queried_query_bind T q (fun x => (pure x : M _))
    simpa only [bind_pure, SourceReplay.queried_pure] using this
  rw [he, List.mem_singleton] at hq'
  rw [hq']
  exact h
theorem QueriesSat.foldlM_list {β γ : Type} (items : List β) (f : γ → β → M γ) (Inv : Nat → γ → Prop)
    (initial : γ) (h0 : Inv 0 initial)
    (hs : ∀ i (hi : i < items.length) state, Inv i state →
      QueriesSat T Q (f state items[i]) ∧ Inv (i + 1) (evalWithAnswerFn T (f state items[i]))) :
    QueriesSat T Q (items.foldlM f initial) := by
  induction items generalizing Inv initial with
  | nil => exact QueriesSat.pure' _
  | cons x xs ih =>
      rw [List.foldlM_cons]
      obtain ⟨hq, hi⟩ := hs 0 (by simp) initial h0
      refine QueriesSat.bind hq ?_
      exact ih (fun i => Inv (i + 1)) _ hi (fun i hi state hstate => hs (i + 1) (by simp; omega) state hstate)
theorem QueriesSat.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → M γ) (Inv : Nat → γ → Prop) (initial : γ)
    (h0 : Inv 0 initial)
    (hs : ∀ i, i < n → ∀ state, Inv i state →
      QueriesSat T Q (f state i) ∧ Inv (i + 1) (evalWithAnswerFn T (f state i))) :
    QueriesSat T Q ((List.range n).foldlM f initial) :=
  QueriesSat.foldlM_list (List.range n) f Inv initial h0 (fun i hi state hstate => by
    simp only [List.getElem_range]
    exact hs i (by simpa using hi) state hstate)
theorem QueriesSat.foldlM_range' {γ : Type} (start n : Nat) (f : γ → Nat → M γ) (Inv : Nat → γ → Prop)
    (initial : γ) (h0 : Inv 0 initial)
    (hs : ∀ i, i < n → ∀ state, Inv i state →
      QueriesSat T Q (f state (start + i)) ∧ Inv (i + 1) (evalWithAnswerFn T (f state (start + i)))) :
    QueriesSat T Q ((List.range' start n).foldlM f initial) :=
  QueriesSat.foldlM_list (List.range' start n) f Inv initial h0 (fun i hi state hstate => by
    simp only [List.getElem_range', Nat.one_mul]
    exact hs i (by simpa using hi) state hstate)
theorem QueriesSat.mapM {α β : Type} (items : List α) (f : α → M β) (hf : ∀ x ∈ items, QueriesSat T Q (f x)) :
    QueriesSat T Q (items.mapM f) := by
  induction items with
  | nil => exact QueriesSat.pure' _
  | cons x xs ih =>
      rw [List.mapM_cons]
      exact QueriesSat.bind (hf x List.mem_cons_self) (QueriesSat.bind
        (ih fun y hy => hf y (List.mem_cons_of_mem x hy)) (QueriesSat.pure' _))
theorem QueriesSat.mono {α : Type} {Q' : T3.Spec.Domain → Prop} {p : M α} (hp : QueriesSat T Q p)
    (h : ∀ q, Q q → Q' q) : QueriesSat T Q' p := fun q hq => h q (hp q hq)
end QueriesSat
theorem queried_shortHash' (T : Answers) (input : HashInput) :
    SourceReplay.queried T (shortHash input) = [.inl (.inr (pad64 input))] := rfl
theorem sat_shortHash {T : Answers} {Q : T3.Spec.Domain → Prop} (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (shortHash input) := by
  intro q hq
  rw [queried_shortHash', List.mem_singleton] at hq
  rw [hq]
  exact h
theorem sat_publicHash {T : Answers} {Q : T3.Spec.Domain → Prop} (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (publicHash input) :=
  QueriesSat.query h
def HonestQuery (T : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ ∃ p : Extract.Pos, p.Bounded ∧ x = Extract.honestInput T p
  | _ => True
theorem chain_zero (lay : Layer) (tree leaf i start : Nat) (v : Digest) :
    chain lay tree leaf i start 0 v = pure v := rfl
theorem queried_chain_one (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    SourceReplay.queried T (chain lay tree leaf i s 1 v) = [.inl (.inr (pad64 (chainInput lay tree leaf i s v)))] := rfl
theorem eval_honestChain (T : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (start count : Nat) :
    evalWithAnswerFn T (chain lay tree leaf i start count (honestChainValue T lay tree leaf i seed start)) =
      honestChainValue T lay tree leaf i seed (start + count) := by
  unfold honestChainValue
  rw [Correctness.eval_chain_add]
  simp only [Nat.zero_add]
theorem honestChainValue_zero (T : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValue T lay tree leaf i seed 0 = seed := rfl
def nodeQuery (tag lay tree heap : Nat) (left right : Digest) : T3.Spec.Domain :=
  .inl (.inr (pad64 (nodeInputP tag lay tree heap left 0 right)))
theorem sat_nodeHash {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree heap : Nat) (left right : Digest)
    (h : Q (nodeQuery tag lay tree heap left right)) : QueriesSat T Q (T3.nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_shortHash]
  exact sat_shortHash _ h
theorem sat_buildLevel {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree h level : Nat)
    (nodes : List Digest)
    (hq : ∀ i, i < nodes.length / 2 →
      Q (nodeQuery tag lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))) :
    QueriesSat T Q (T3.buildLevel tag lay tree h level nodes) := by
  unfold T3.buildLevel
  exact QueriesSat.mapM _ _ (fun i hi => sat_nodeHash _ _ _ _ _ _ (hq i (List.mem_range.mp hi)))
def levelsStep (tag lay tree h : Nat) (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← T3.buildLevel tag lay tree h level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])
def levelsFold (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM (levelsStep tag lay tree h) [leaves]
theorem buildLevels_eq_fold (tag lay tree h : Nat) (leaves : List Digest) :
    T3.buildLevels tag lay tree h leaves = levelsFold tag lay tree h leaves h := rfl
theorem eval_levelsStep (T : Answers) (tag lay tree h : Nat) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (levelsStep tag lay tree h levels level) =
      levels ++ [evalWithAnswerFn T (T3.buildLevel tag lay tree h level (levels.getD (level - 1) []))] := by
  simp only [levelsStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem eval_levelsSteps_append (T : Answers) (tag lay tree h : Nat) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM (levelsStep tag lay tree h) state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_levelsStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (T3.buildLevel tag lay tree h x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (T3.buildLevel tag lay tree h x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩
theorem levelsFold_succ (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    levelsFold tag lay tree h leaves (n + 1) =
      (levelsFold tag lay tree h leaves n >>= fun state => levelsStep tag lay tree h state (1 + n)) := by
  unfold levelsFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem levelsFold_length (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (levelsFold tag lay tree h leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [levelsFold_succ, evalWithAnswerFn_bind, eval_levelsStep, List.length_append, ih]
      simp
theorem levelsFold_prefix (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (levelsFold tag lay tree h leaves m) =
      evalWithAnswerFn T (levelsFold tag lay tree h leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold levelsFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_levelsSteps_append T tag lay tree h _ _
theorem sat_buildLevels {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree h : Nat)
    (leaves : List Digest)
    (hq : ∀ level, level < h → ∀ node,
      node < ((evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)).getD level []).length / 2 →
      Q (nodeQuery tag lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)) level (2 * node))
        (treeValue (evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)) level (2 * node + 1)))) :
    QueriesSat T Q (T3.buildLevels tag lay tree h leaves) := by
  rw [buildLevels_eq_fold] at hq ⊢
  unfold levelsFold
  refine QueriesSat.foldlM_range' 1 h _
    (fun i state => state = evalWithAnswerFn T (levelsFold tag lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold levelsStep
    refine QueriesSat.bind (sat_buildLevel _ _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := levelsFold_length T tag lay tree h leaves i
    obtain ⟨extra, hext⟩ := levelsFold_prefix T tag lay tree h leaves i h (by omega)
    have hget : (evalWithAnswerFn T (levelsFold tag lay tree h leaves h)).getD i [] =
        (evalWithAnswerFn T (levelsFold tag lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i hi node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [levelsFold_succ, evalWithAnswerFn_bind]
end SigGolfCandidate.T3.Security.Wots.Structural
