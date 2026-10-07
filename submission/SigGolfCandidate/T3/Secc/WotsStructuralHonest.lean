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
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    HonestQuery T (.inl (.inr (Extract.honestInput T p))) := Or.inr ⟨p, hp, rfl⟩
theorem sat_privateHash (T : Answers) (c : Coordinate) :
    QueriesSat T (HonestQuery T) (T3.privateHash c) :=
  QueriesSat.query (honestQuery_private T c)
theorem sat_privatePair (T : Answers) (tag lay tree position index : Nat) :
    QueriesSat T (HonestQuery T) (T3.privatePair tag lay tree position index) := by
  unfold T3.privatePair
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem sat_mask (T : Answers) (level index : Nat) : QueriesSat T (HonestQuery T) (T3.mask level index) := by
  unfold T3.mask T3.pairedMask
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_privateMac (T : Answers) (region : Region) : QueriesSat T (HonestQuery T) (T3.privateMac region) := by
  unfold T3.privateMac T3.privateMacKey
  exact QueriesSat.bind (QueriesSat.bind (sat_privateHash T _) (QueriesSat.bind
    (sat_privateHash T _) (QueriesSat.pure' _))) (QueriesSat.pure' _)
theorem sat_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    QueriesSat T (HonestQuery T) (T3.maskedLevel nodes level) := by
  unfold T3.maskedLevel T3.pairedMask
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun _ _ =>
    QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)) (QueriesSat.pure' _)
theorem sat_privateNonce (T : Answers) (message : Message) :
    QueriesSat T (HonestQuery T) (T3.privateNonce message) := by
  unfold T3.privateNonce
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem posOf_eq_none {x : HashInput}
    (h : ∀ p : Extract.Pos, p.Bounded →
      Extract.canonicalHeader (Extract.hdrBlock x) ≠ bytesLE 16 p.hdr) : Extract.posOf x = none := by
  unfold Extract.posOf
  rw [dif_neg]
  rintro ⟨p, hb, he⟩
  exact h p hb he
private theorem canonicalHeader_low (hdr : Digest) :
    (Extract.canonicalHeader (bytesLE 16 hdr)).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, Extract.bytesLE_header_words]
  unfold Extract.canonicalHeader
  split_ifs <;> simp [List.take_append, bytesLE_length]
private theorem low_ne_of_firstByte (x y : BitVec 128)
    (hc : 128 ≤ x.toNat % 256) (hr : y.toNat % 256 = 1) :
    x.extractLsb' 0 64 ≠ y.extractLsb' 0 64 := by
  intro he
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] at hv
  omega
private theorem chain_low_ne_header (lay : Layer) (tree leaf i step tag roleLay roleTree pos ix : Nat) :
    (chainHeader lay tree leaf i step).extractLsb' 0 64 ≠
      (header tag roleLay roleTree pos ix).extractLsb' 0 64 :=
  low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
    (header_firstByte tag roleLay roleTree pos ix)
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
theorem sat_ftsRows (T : Answers) (index coord : Nat) (hindex : index < 2 ^ 40) (hcoord : coord < 256) :
    QueriesSat T (HonestQuery T) (Correctness.ftsRows index coord) := by
  unfold Correctness.ftsRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun pair hpair state _ => ⟨?_, trivial⟩)
  refine QueriesSat.bind (sat_privatePair T _ _ _ _ _) ?_
  generalize hp : evalWithAnswerFn T (T3.privatePair 8 coord index 0 pair) = lr
  obtain ⟨left, right⟩ := lr
  have hleft : left = CanonGraph.ftsSecretNat T index coord (2 * pair) := by
    unfold CanonGraph.ftsSecretNat
    rw [show 2 * pair / 2 = pair by omega, if_pos (by omega), hp]
  have hright : right = CanonGraph.ftsSecretNat T index coord (2 * pair + 1) := by
    unfold CanonGraph.ftsSecretNat
    rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega), hp]
  have hleaf : ∀ leaf secret, leaf < 2048 → secret = CanonGraph.ftsSecretNat T index coord leaf →
      QueriesSat T (HonestQuery T) (ftsLeaf index coord leaf secret) := by
    intro leaf secret hl hs
    rw [ftsLeaf_eq_shortHash]
    refine sat_shortHash _ (Or.inr ⟨.ftsLeaf index coord leaf, ⟨hcoord, hindex, by omega⟩, ?_⟩)
    show pad64 (ftsLeafInputP index coord leaf 0 secret 0) =
      pad64 (ftsLeafInputP index coord leaf 0 (Extract.ftsSecret T index coord leaf) 0)
    rw [CanonGraph.ftsSecret_nat T index coord leaf hl, hs]
  exact QueriesSat.bind (hleaf _ _ (by omega) hleft) (QueriesSat.bind (hleaf _ _ (by omega) hright)
    (QueriesSat.pure' _))
theorem sat_buildFts (T : Answers) (index coord : Nat) (hindex : index < 2 ^ 40) (hcoord : coord < 7) :
    QueriesSat T (HonestQuery T) (buildFts index coord) := by
  rw [Correctness.buildFts_eq]
  refine QueriesSat.bind (sat_ftsRows T index coord hindex (by omega)) ?_
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  have hrows := Correctness.eval_ftsRows_correct T index coord
  have hlevels := Correctness.eval_buildLevels_correct T 10 coord index 11
    (evalWithAnswerFn T (Correctness.ftsRows index coord)).1 (by rw [hrows.1]; rfl)
  have hR : evalWithAnswerFn T (T3.buildLevels 10 coord index 11 (evalWithAnswerFn T (Correctness.ftsRows index coord)).1) =
      (evalWithAnswerFn T (buildFts index coord)).1 := by
    rw [Correctness.buildFts_eq]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  apply sat_buildLevels
  intro level hlevel node hnode
  have hw := hlevels.1.2 level (by omega)
  have hpow : 2 ^ (11 - level) = 2 * 2 ^ (11 - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hw, hpow] at hnode
  have hnode' : node < 2 ^ (11 - level - 1) := by omega
  refine Or.inr ⟨.ftsNode index coord level node, ⟨by omega, hindex, hlevel, hnode'⟩, ?_⟩
  show pad64 (nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node) _ 0 _) =
    pad64 (nodeInputP 10 coord index (2 ^ (11 - level - 1) + node)
      (treeValue (Extract.ftsLevels T index coord) level (2 * node)) 0
      (treeValue (Extract.ftsLevels T index coord) level (2 * node + 1)))
  rw [CanonGraph.ftsLevels_built T index coord level (2 * node) hlevel (by omega),
    CanonGraph.ftsLevels_built T index coord level (2 * node + 1) hlevel (by omega), hR, Nat.sub_sub]
theorem sat_signForest (T : Answers) (index : Nat) (hindex : index < 2 ^ 40) (chosen : List Selection) :
    QueriesSat T (HonestQuery T) (Correctness.signForest index chosen) := by
  unfold Correctness.signForest
  refine QueriesSat.foldlM_range 7 _ (fun _ _ => True) _ trivial (fun coord hc state _ => ⟨?_, trivial⟩)
  refine QueriesSat.bind (sat_buildFts T index coord hindex hc) ?_
  generalize evalWithAnswerFn T (buildFts index coord) = x
  obtain ⟨levels, secrets⟩ := x
  exact QueriesSat.pure' _
theorem sat_forestPk (T : Answers) (index : Nat) (hindex : index < 2 ^ 40) :
    QueriesSat T (HonestQuery T) (forestPk index (Correctness.forestRoots T index 7)) := by
  rw [Extract.forestPk_eq_shortHash]
  refine sat_shortHash _ (Or.inr ⟨.forest index, hindex, ?_⟩)
  show pad64 (Extract.forestInput index (Correctness.forestRoots T index 7)) =
    pad64 (Extract.forestInput index (Extract.ftsRootsHonest T index))
  rw [CanonGraph.ftsRoots_built]
  rfl
theorem sat_topPath (T : Answers) (cache : Cache) (leaf : Nat) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (topPath cache leaf) := by
  unfold topPath
  exact QueriesSat.mapM _ _ fun level _ => QueriesSat.bind (sat_mask T _ _) (QueriesSat.pure' _)
end SigGolfCandidate.T3.Security.Wots.Structural
