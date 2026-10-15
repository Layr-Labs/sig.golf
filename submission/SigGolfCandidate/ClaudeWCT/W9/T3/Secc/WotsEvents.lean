import SigGolfCandidate.ClaudeWCT.W9.New.G3a_PaddedWitness
import SigGolfCandidate.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.New.BC.Rows
import SigGolfCandidate.Choice.Probability

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
noncomputable def leafMsg (answers : Answers) (L : LeafAddr) : WCT9.LayerMsg :=
  if h : L.lay.val < 3 then
    .pair (Extract.honestPair answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)).1
      (Extract.honestPair answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)).2
  else .pair (Extract.honestTop answers ((L.tree * 2 ^ height L.lay + L.leaf) % 2 ^ 31)).1
    (Extract.honestTop answers ((L.tree * 2 ^ height L.lay + L.leaf) % 2 ^ 31)).2
theorem msgFits_leafMsg (answers : Answers) (L : LeafAddr) : Extract.msgFits L.lay (leafMsg answers L) := by
  unfold leafMsg
  split_ifs <;> trivial
/-- Encoding-row witness pads: bytes 36..48, the (unused since nested FTS) forest right slot, and (C2/C3 FULL) the
row tweak's high word as an XOR mask on its honest value 1, so the zero pad is the honest row. -/
abbrev RowPad := BitVec 96 × Digest × BitVec 64
def encRow (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : RowPad) : HashInput :=
  pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter pad.1 pad.2.1 (pad.2.2 ^^^ 1))
theorem encRow_zero (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    encRow L msg counter 0 = pad64 (WCT9.layerEncodingInput L.lay L.tree L.leaf msg counter) := by
  show pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter 0 0 ((0 : BitVec 64) ^^^ 1)) = _
  rw [show ((0 : BitVec 64) ^^^ 1 : BitVec 64) = 1 by decide]
  exact BC.pad64_layerEncodingInputP_zero _ _ _ _ _
theorem searchLimit_fits (lay : Layer) : 0 + WCT9.searchLimit lay ≤ 2 ^ 32 := by
  have := WCT9.searchLimit_le lay
  unfold counterLimit at this
  omega
noncomputable def referenceSearch (answers : Answers) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  evalWithAnswerFn answers (WCT9.layerCounterSearch L.lay L.tree L.leaf (leafMsg answers L) 0 (WCT9.searchLimit L.lay))
noncomputable def referenceDigits (answers : Answers) (L : LeafAddr) : List Nat :=
  ((referenceSearch answers L).map Prod.snd).getD (dummyDigits L.lay)
noncomputable def depth (answers : Answers) (a : ChainAddr) : Nat :=
  (referenceDigits answers a.key).getD a.chain 0
/-! ### C3 (FULL): the honest chain of the current scheme (`WCT9.chainW`, chain 0 of a lower layer keeps the HIGH
half of its last step) and chain rows read through the half their step uses. -/
/-- The half of a chain row's output that chain `a` reads after `step`. -/
def rowHalf (a : ChainAddr) (step : Nat) (output : HashOutput) : Digest :=
  WCT9.halfOf (WCT9.chainHigh a.key.lay a.chain step) output
/-- A trace row of chain `a` at `step` with input value `value` whose used half is `out`. -/
def SeenRowW (trace : List Entry) (a : ChainAddr) (step : Nat) (value out : Digest) : Prop :=
  ∃ answer, (chainRow a step value, answer) ∈ trace ∧ rowHalf a step answer = out
theorem seenRowW_mono {trace trace' : List Entry} {a : ChainAddr} {step : Nat} {value out : Digest}
    (h : SeenRowW trace a step value out) (hsub : ∀ e ∈ trace, e ∈ trace') : SeenRowW trace' a step value out := by
  obtain ⟨answer, hm, hl⟩ := h
  exact ⟨answer, hsub _ hm, hl⟩
/-- The honest value of chain `(lay, tree, leaf, i)` after `step` steps from `seed` (current scheme). -/
noncomputable def honestChainValueW (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest)
    (step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 step seed)
theorem chainW_add' (lay : Layer) (tree leaf i start m n : Nat) (value : Digest) :
    WCT9.chainW lay tree leaf i start (m + n) value =
      (WCT9.chainW lay tree leaf i start m value >>= WCT9.chainW lay tree leaf i (start + m) n) := by
  unfold WCT9.chainW
  rw [← List.range'_append_1, List.foldlM_append]
theorem eval_chainW_add' (answers : Answers) (lay : Layer) (tree leaf i start m n : Nat) (value : Digest) :
    evalWithAnswerFn answers (WCT9.chainW lay tree leaf i start (m + n) value) =
      evalWithAnswerFn answers (WCT9.chainW lay tree leaf i (start + m) n
        (evalWithAnswerFn answers (WCT9.chainW lay tree leaf i start m value))) := by
  rw [chainW_add', evalWithAnswerFn_bind]
theorem eval_halfHash' (answers : Answers) (high : Bool) (input : HashInput) :
    evalWithAnswerFn answers (WCT9.halfHash high input) = WCT9.halfOf high (answers (.inl (.inr (pad64 input)))) := by
  cases high <;> rfl
theorem queried_halfHash' (answers : Answers) (high : Bool) (input : HashInput) :
    queried answers (WCT9.halfHash high input) = [.inl (.inr (pad64 input))] := by
  cases high <;> rfl
@[simp] theorem chainW_zero' (lay : Layer) (tree leaf i start : Nat) (value : Digest) :
    WCT9.chainW lay tree leaf i start 0 value = pure value := rfl
theorem chainW_one' (lay : Layer) (tree leaf i start : Nat) (value : Digest) :
    WCT9.chainW lay tree leaf i start 1 value =
      WCT9.halfHash (WCT9.chainHigh lay i start) (chainInput lay tree leaf i start value) := by
  unfold WCT9.chainW
  simp only [List.range'_one, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem eval_chainW_one' (answers : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn answers (WCT9.chainW lay tree leaf i s 1 v) =
      WCT9.halfOf (WCT9.chainHigh lay i s) (answers (.inl (.inr (pad64 (chainInput lay tree leaf i s v))))) := by
  rw [chainW_one', eval_halfHash']
theorem honestChainValueW_zero (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValueW answers lay tree leaf i seed 0 = seed := rfl
theorem honestChainValueW_succ (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    WCT9.halfOf (WCT9.chainHigh lay i step) (answers (.inl (.inr (pad64 (chainInput lay tree leaf i step
      (honestChainValueW answers lay tree leaf i seed step)))))) =
        honestChainValueW answers lay tree leaf i seed (step + 1) := by
  unfold honestChainValueW
  rw [eval_chainW_add', Nat.zero_add, eval_chainW_one']
/-- Below the last step of a chain, or off chain 0 of a lower layer, the current chain is the legacy chain. -/
theorem honestChainValueW_eq {answers : Answers} {lay : Layer} {tree leaf i : Nat} {seed : Digest} {step : Nat}
    (h : lay = 0 ∨ i ≠ 0 ∨ step ≤ 6) :
    honestChainValueW answers lay tree leaf i seed step = honestChainValue answers lay tree leaf i seed step := by
  unfold honestChainValueW honestChainValue
  have hl : ∀ s, 0 ≤ s → s < 0 + step → WCT9.chainHigh lay i s = false := by
    intro s _ hs
    apply WCT9.chainHigh_eq_false
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by omega))
  rw [WCT9.chainW_of_low hl tree leaf seed]
theorem rowHalf_of_low {a : ChainAddr} {step : Nat} (h : WCT9.chainHigh a.key.lay a.chain step = false)
    (output : HashOutput) : rowHalf a step output = low output := by
  unfold rowHalf; rw [h]; rfl
/-- An output whose `high`-selected half is `v` and whose other half is `o`. -/
noncomputable def joinHalf (high : Bool) (v o : Digest) : HashOutput :=
  if high then SigGolfCandidate.T3.Security.ChainGraph.joinOutput o v else SigGolfCandidate.T3.Security.ChainGraph.joinOutput v o
theorem halfOf_joinHalf (high : Bool) (v o : Digest) : WCT9.halfOf high (joinHalf high v o) = v := by
  cases high
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_low _ _
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_high _ _
theorem halfOf_not_joinHalf (high : Bool) (v o : Digest) : WCT9.halfOf (!high) (joinHalf high v o) = o := by
  cases high
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_high _ _
  · exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_low _ _
theorem joinHalf_halfOf (high : Bool) (y : HashOutput) :
    joinHalf high (WCT9.halfOf high y) (WCT9.halfOf (!high) y) = y := by
  cases high <;> exact SigGolfCandidate.T3.Security.ChainGraph.joinOutput_parts _
@[simp] theorem halfOf_zero (high : Bool) : WCT9.halfOf high (0 : HashOutput) = 0 := by
  cases high <;> rfl
noncomputable def frontierValue (answers : Answers) (a : ChainAddr) : Digest :=
  honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
    (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers a)
def ContactAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers a ∧ ∃ value, SeenRowW trace a (depth answers a - 1) value (frontierValue answers a)
def TwoEdgeAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers a ∧ ∃ start middle, SeenRowW trace a (depth answers a - 2) start middle ∧
    SeenRowW trace a (depth answers a - 1) middle (frontierValue answers a)
noncomputable def referenceInput (answers : Answers) (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers L).map fun selected => encRow L (leafMsg answers L) selected.1 0
def EncodingMatchAt (answers : Answers) (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter pad answer, Extract.msgFits L.lay message ∧ (encRow L message counter pad, answer) ∈ trace ∧
    referenceInput answers L ≠ some (encRow L message counter pad) ∧
    WCT9.encodingCanDecode L.lay answer (referenceDigits answers L)
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter pad answer digits, Extract.msgFits a.key.lay message ∧
    (encRow a.key message counter pad, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encRow a.key message counter pad) ∧
    WCT9.encodingCanDecode a.key.lay answer digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers a.key).getD i 0 ≤ digits.getD i 0
def OtherChainRow (answers : Answers) (input : HashInput) : Prop :=
  ∃ (a : ChainAddr) (step : Nat), Extract.posOf input =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
    ((∀ value, input ≠ chainRow a step value) ∨ depth answers a ≤ step)
def StructuralClass (answers : Answers) (input : HashInput) (position : Extract.Pos) : Prop :=
  match position with
  | .chain _ _ _ _ _ => OtherChainRow answers input
  | _ => True
def StructuralHit (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input
def WotsPrimitive (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, EncodingMatchAt answers trace L) ∨ StructuralHit answers trace ∨
    (∃ a, TwoEdgeAt answers trace a) ∨
    (∃ a b, a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, MarkerAt answers trace a ∧ ContactAt answers trace a)
end ClaudeWCT.W9.T3.Security.Wots
namespace ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
def SourceLeaf7 (L : LeafAddr) : Prop := L.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits L.lay ∧ L.leaf < 2 ^ height L.lay
def SourceChain7 (a : ChainAddr) : Prop := SourceLeaf7 a.key ∧ a.chain < chainCount a.key.lay
theorem SourceLeaf7.tree_lt {L : LeafAddr} (h : SourceLeaf7 L) : L.tree < 2 ^ 31 :=
  lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by decide)
    (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
end ClaudeWCT.W9.T3.Security.WotsExtract
