import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.T3.Secc.WotsExtractWord

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
theorem ShortRespects.shortHash (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    ShortRespects (T3.shortHash input) := by
  intro A T hAT
  rw [eval_shortHash, eval_shortHash, hAT.public _ h]
theorem ShortRespects.projHash (high : Bool) (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    ShortRespects (T3.projHash high input) := by
  intro A T hAT
  rw [SigGolfCandidate.T3M.SecurityExtraction.eval_projHash, SigGolfCandidate.T3M.SecurityExtraction.eval_projHash,
    hAT.public _ h]
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
theorem short_of_le (input : HashInput) (h : input.length ≤ 4033) :
    (pad64 input).length ≤ SeccLaw.maxInputLength := by
  have := pad64_length_le input
  unfold SeccLaw.maxInputLength
  omega
theorem chain_respects (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ShortRespects (chain lay tree leaf i start count value) := by
  unfold chain
  exact ShortRespects.foldlM _ _ (fun step _ v => ShortRespects.projHash _ _
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
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem chainValue_short (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    evalWithAnswerFn A (chain lay tree leaf i start count value) =
      evalWithAnswerFn T (chain lay tree leaf i start count value) :=
  chain_respects lay tree leaf i start count value A T hAT
theorem honestChainValue_short (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    honestChainValue A lay tree leaf i seed step = honestChainValue T lay tree leaf i seed step :=
  chainValue_short hAT lay tree leaf i 0 step seed
end objects
end SigGolfCandidate.T3.Security.Wots.Ref
