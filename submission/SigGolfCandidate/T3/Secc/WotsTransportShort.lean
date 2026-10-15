import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.T3.Secc.WotsExtractVerify

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def ShortQuery : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr input) => input.length ≤ SeccLaw.maxInputLength
  | .inr _ => True
def ShortAgree (A T : Answers) : Prop := ∀ query, ShortQuery query → A query = T query
theorem ShortAgree.symm {A T : Answers} (h : ShortAgree A T) : ShortAgree T A :=
  fun query hq => (h query hq).symm
theorem ShortAgree.public {A T : Answers} (h : ShortAgree A T) (input : HashInput)
    (hinput : input.length ≤ SeccLaw.maxInputLength) : A (.inl (.inr input)) = T (.inl (.inr input)) :=
  h _ hinput
theorem ShortAgree.priv {A T : Answers} (h : ShortAgree A T) (coordinate : Coordinate) :
    A (.inr coordinate) = T (.inr coordinate) := h _ trivial
def ShortRespects {α : Type} (program : M α) : Prop :=
  ∀ A T : Answers, ShortAgree A T → evalWithAnswerFn A program = evalWithAnswerFn T program
theorem ShortRespects.pure' {α : Type} (x : α) : ShortRespects (pure x : M α) := fun _ _ _ => rfl
theorem ShortRespects.bind {α β : Type} {p : M α} {f : α → M β} (hp : ShortRespects p)
    (hf : ∀ x, ShortRespects (f x)) : ShortRespects (p >>= f) := by
  intro A T h
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hp A T h]
  exact hf _ A T h
theorem ShortRespects.map {α β : Type} {p : M α} (f : α → β) (hp : ShortRespects p) :
    ShortRespects (f <$> p) := by
  intro A T h
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map, hp A T h]
theorem ShortRespects.shortHash (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    ShortRespects (T3.shortHash input) := by
  intro A T hAT
  rw [eval_shortHash, eval_shortHash, hAT.public _ h]
/-- C4: `T3.projHash` (either half) respects short-input agreement like `shortHash`. -/
theorem ShortRespects.projHash (high : Bool) (input : HashInput)
    (h : (pad64 input).length ≤ SeccLaw.maxInputLength) : ShortRespects (T3.projHash high input) := by
  intro A T hAT
  have e : ∀ X : Answers, evalWithAnswerFn X (T3.projHash high input) =
      T3.projHalf high (X (.inl (.inr (pad64 input)))) := fun _ => rfl
  rw [e, e, hAT.public _ h]
theorem ShortRespects.privatePair (tag lay tree position index : Nat) :
    ShortRespects (T3.privatePair tag lay tree position index) := by
  intro A T hAT
  unfold T3.privatePair T3.privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [show evalWithAnswerFn A (liftM (T3.Spec.query (.inr (.inl (header tag lay tree position index))))) =
      A (.inr (.inl (header tag lay tree position index))) from simulateQ_spec_query A _,
    show evalWithAnswerFn T (liftM (T3.Spec.query (.inr (.inl (header tag lay tree position index))))) =
      T (.inr (.inl (header tag lay tree position index))) from simulateQ_spec_query T _,
    hAT.priv]
theorem ShortRespects.foldlM {β γ : Type} (l : List β) (f : γ → β → M γ)
    (hf : ∀ x ∈ l, ∀ s, ShortRespects (f s x)) : ∀ init, ShortRespects (l.foldlM f init) := by
  induction l with
  | nil => intro init; exact ShortRespects.pure' init
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons]
      exact ShortRespects.bind (hf x List.mem_cons_self init)
        fun s => ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s) s
theorem ShortRespects.mapM {α β : Type} (l : List α) (f : α → M β) (hf : ∀ x ∈ l, ShortRespects (f x)) :
    ShortRespects (l.mapM f) := by
  intro A T h
  rw [Correctness.eval_mapM, Correctness.eval_mapM]
  exact List.map_congr_left fun x hx => hf x hx A T h
theorem pad64_length_le (input : HashInput) : (pad64 input).length ≤ input.length + 63 := by
  rw [Cost.pad64_length]
  omega
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by
  fin_cases lay <;> decide
theorem chainInput_length (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    (chainInput lay tree leaf i step value).length = 64 := by
  simp [chainInput, zero16, bytesLE_length]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (Extract.listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [Extract.listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem short_of_le (input : HashInput) (h : input.length ≤ 4033) :
    (pad64 input).length ≤ SeccLaw.maxInputLength := by
  have := pad64_length_le input
  unfold SeccLaw.maxInputLength
  omega
theorem chain_respects (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ShortRespects (chain lay tree leaf i start count value) := by
  unfold chain
  exact ShortRespects.foldlM _ _ (fun step _ v => ShortRespects.shortHash _
    (short_of_le _ (by rw [chainInput_length]; omega))) value
theorem leafHash_respects (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length ≤ 200) :
    ShortRespects (leafHash lay tree leaf ends) := by
  unfold leafHash
  apply ShortRespects.projHash
  apply short_of_le
  rw [leafInput_length]
  split_ifs <;> omega
theorem nodeHash_respects (tag lay tree heap : Nat) (left right : Digest) :
    ShortRespects (nodeHash tag lay tree heap left right) := by
  unfold nodeHash
  apply ShortRespects.projHash
  apply short_of_le
  simp [zero16, bytesLE_length]
theorem buildLevel_respects (tag lay tree h level : Nat) (nodes : List Digest) :
    ShortRespects (buildLevel tag lay tree h level nodes) := by
  unfold buildLevel
  exact ShortRespects.mapM _ _ fun i _ => nodeHash_respects _ _ _ _ _ _
theorem buildLevels_respects (tag lay tree h : Nat) (leaves : List Digest) :
    ShortRespects (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact ShortRespects.foldlM _ _ (fun level _ levels =>
    ShortRespects.bind (buildLevel_respects _ _ _ _ _ _) fun _ => ShortRespects.pure' _) _
theorem ftsLeaf_respects (index coord leaf : Nat) (secret : Digest) :
    ShortRespects (ftsLeaf index coord leaf secret) := by
  unfold ftsLeaf
  apply ShortRespects.shortHash
  apply short_of_le
  simp [zero16, bytesLE_length]
theorem buildFts_respects (index coord : Nat) : ShortRespects (buildFts index coord) := by
  unfold buildFts
  refine ShortRespects.bind (ShortRespects.foldlM _ _ (fun pair _ state => ?_) _) fun state =>
    ShortRespects.bind (buildLevels_respects _ _ _ _ _) fun _ => ShortRespects.pure' _
  refine ShortRespects.bind (ShortRespects.privatePair _ _ _ _ _) fun seeds => ?_
  rcases seeds with ⟨left, right⟩
  exact ShortRespects.bind (ftsLeaf_respects _ _ _ _) fun _ =>
    ShortRespects.bind (ftsLeaf_respects _ _ _ _) fun _ => ShortRespects.pure' _
theorem forestPk_respects (index : Nat) (roots : List Digest) (hlen : roots.length ≤ 200) :
    ShortRespects (forestPk index roots) := by
  unfold forestPk
  apply ShortRespects.shortHash
  apply short_of_le
  simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop]
  omega
theorem counterSearch_respects (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    ShortRespects (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold counterSearch
      refine ShortRespects.bind (ShortRespects.shortHash _ (short_of_le _ ?_)) fun answer => ?_
      · simp [encodingInput, bytesLE_length]
      · cases searchDecode lay answer with
        | none => exact ih _
        | some digits => exact ShortRespects.pure' _
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem leafSeed_short (lay : Layer) (tree leaf i : Nat) : leafSeed A lay tree leaf i = leafSeed T lay tree leaf i := by
  unfold leafSeed
  split_ifs
  · unfold Correctness.topLeafSeed Correctness.topCoefList
    congr 2
    funext j
    unfold Correctness.topCoef Correctness.topCoefN topSeedPair
    rw [ShortRespects.privatePair 0 0 0 _ 0 A T hAT]
  all_goals rw [ShortRespects.privatePair 0 lay.val tree (i / 2) leaf A T hAT]
theorem chainValue_short (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    evalWithAnswerFn A (chain lay tree leaf i start count value) =
      evalWithAnswerFn T (chain lay tree leaf i start count value) :=
  chain_respects lay tree leaf i start count value A T hAT
theorem honestChainValue_short (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    honestChainValue A lay tree leaf i seed step = honestChainValue T lay tree leaf i seed step :=
  chainValue_short hAT lay tree leaf i 0 step seed
theorem leafEnd_short (lay : Layer) (tree leaf i : Nat) : leafEnd A lay tree leaf i = leafEnd T lay tree leaf i := by
  unfold leafEnd
  rw [leafSeed_short hAT]
  exact chainValue_short hAT _ _ _ _ _ _ _
theorem leafRoot_short (lay : Layer) (tree leaf : Nat) : leafRoot A lay tree leaf = leafRoot T lay tree leaf := by
  unfold leafRoot
  rw [List.map_congr_left (fun i _ => leafEnd_short hAT lay tree leaf i)]
  apply leafHash_respects
  · simp only [List.length_map, List.length_range]
    have := chainCount_le lay
    omega
  · exact hAT
theorem builtTree_short (lay : Layer) (tree : Nat) : builtTree A lay tree = builtTree T lay tree := by
  unfold builtTree
  rw [List.map_congr_left (fun leaf _ => leafRoot_short hAT lay tree leaf)]
  exact buildLevels_respects _ _ _ _ _ A T hAT
theorem honestRoot_short (lay : Layer) (tree : Nat) : Extract.honestRoot A lay tree = Extract.honestRoot T lay tree := by
  unfold Extract.honestRoot
  rw [builtTree_short hAT]
theorem buildFts_short (index coord : Nat) :
    evalWithAnswerFn A (buildFts index coord) = evalWithAnswerFn T (buildFts index coord) :=
  buildFts_respects index coord A T hAT
end objects
end SigGolfCandidate.T3.Security.Wots.Ref
