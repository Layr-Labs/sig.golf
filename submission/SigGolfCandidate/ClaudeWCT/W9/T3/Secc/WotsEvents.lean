import SigGolfCandidate.ClaudeWCT.W9.New.G3a.PaddedWitness
import SigGolfCandidate.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.New.BC.Rows

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
    decode L.lay (WCT9.encodingAnswer L.lay answer) = some (referenceDigits answers L)
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter pad answer digits, Extract.msgFits a.key.lay message ∧
    (encRow a.key message counter pad, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encRow a.key message counter pad) ∧
    decode a.key.lay (WCT9.encodingAnswer a.key.lay answer) = some digits ∧
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

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Security.Wots

/-- The unique WOTS leaf authenticating the tree containing `L`. The value at
    layer zero is unused; recursive calls are made only for positive layers. -/
def parent (L : LeafAddr) : LeafAddr :=
  let lay : Layer := ⟨L.lay.val - 1, by have := L.lay.isLt; omega⟩
  ⟨lay, L.tree / 2 ^ height lay, L.tree % 2 ^ height lay⟩

theorem parent_layer_lt (L : LeafAddr) (h : L.lay.val ≠ 0) : (parent L).lay.val < L.lay.val := by
  simp only [parent]
  omega

abbrev Search := LeafAddr → Nat → Option (BitVec 32 × List Nat)
abbrev Credit := Layer → List Nat → Nat

/-- Remaining credit after the canonical search at a leaf. The recursion goes
    from a leaf to its ancestors and never depends on a descendant or an FTS
    digest. Failure of an ancestor propagates to the descendant. -/
def after (search : Search) (credit : Credit) (L : LeafAddr) : Option Nat :=
  (if L.lay.val = 0 then some 63 else after search credit (parent L)).bind fun remaining =>
    (search L remaining).map fun found => remaining - credit L.lay found.2
termination_by L.lay.val
decreasing_by exact parent_layer_lt L (by assumption)

def context (search : Search) (credit : Credit) (L : LeafAddr) : Option Nat :=
  if L.lay.val = 0 then some 63 else after search credit (parent L)

def selected (search : Search) (credit : Credit) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  (context search credit L).bind (search L)

theorem after_eq (search : Search) (credit : Credit) (L : LeafAddr) :
    after search credit L = (context search credit L).bind fun remaining =>
      (search L remaining).map fun found => remaining - credit L.lay found.2 := by
  rw [after]
  rfl

theorem context_top (search : Search) (credit : Credit) (L : LeafAddr) (h : L.lay.val = 0) :
    context search credit L = some 63 := by simp only [context, if_pos h]

theorem context_parent (search : Search) (credit : Credit) (L : LeafAddr) (h : L.lay.val ≠ 0) :
    context search credit L = after search credit (parent L) := by simp only [context, if_neg h]

/-- Preserving each canonical successful search (and each canonical failure)
    preserves every descendant's threshold context. Equality is needed only at
    the original canonical context, rather than at every possible threshold. -/
theorem after_congr {search search' : Search} (credit : Credit)
    (hsearch : ∀ L remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) (L : LeafAddr) :
    after search' credit L = after search credit L := by
  have hall : ∀ n, ∀ L : LeafAddr, L.lay.val = n → after search' credit L = after search credit L := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro L hL
        have hc : context search' credit L = context search credit L := by
          unfold context
          by_cases hzero : L.lay.val = 0
          · rw [if_pos hzero, if_pos hzero]
          · rw [if_neg hzero, if_neg hzero]
            exact ih (parent L).lay.val (hL ▸ parent_layer_lt L hzero) (parent L) rfl
        rw [after_eq, after_eq, hc]
        cases he : context search credit L with
        | none => rfl
        | some remaining =>
            simp only [Option.bind_some]
            rw [hsearch L remaining he]
  exact hall L.lay.val L rfl

theorem context_congr {search search' : Search} (credit : Credit)
    (hsearch : ∀ L remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) (L : LeafAddr) :
    context search' credit L = context search credit L := by
  unfold context
  split
  · rfl
  · exact after_congr credit hsearch (parent L)

theorem selected_congr {search search' : Search} (credit : Credit)
    (hsearch : ∀ L remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) (L : LeafAddr) :
    selected search' credit L = selected search credit L := by
  unfold selected
  rw [context_congr credit hsearch L]
  cases he : context search credit L with
  | none => rfl
  | some remaining => exact hsearch L remaining he

/-- A finite source universe suffices when it is closed under parent leaves. -/
theorem after_congr_on {search search' : Search} (credit : Credit)
    (allowed : LeafAddr → Prop)
    (hparent : ∀ L, allowed L → L.lay.val ≠ 0 → allowed (parent L))
    (hsearch : ∀ L, allowed L → ∀ remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) {L : LeafAddr} (hL : allowed L) :
    after search' credit L = after search credit L := by
  have hall : ∀ n, ∀ L : LeafAddr, L.lay.val = n → allowed L →
      after search' credit L = after search credit L := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro L hn hL
        have hc : context search' credit L = context search credit L := by
          unfold context
          by_cases hzero : L.lay.val = 0
          · rw [if_pos hzero, if_pos hzero]
          · rw [if_neg hzero, if_neg hzero]
            exact ih (parent L).lay.val (hn ▸ parent_layer_lt L hzero) (parent L) rfl
              (hparent L hL hzero)
        rw [after_eq, after_eq, hc]
        cases he : context search credit L with
        | none => rfl
        | some remaining =>
            simp only [Option.bind_some]
            rw [hsearch L hL remaining he]
  exact hall L.lay.val L rfl hL

theorem context_congr_on {search search' : Search} (credit : Credit)
    (allowed : LeafAddr → Prop)
    (hparent : ∀ L, allowed L → L.lay.val ≠ 0 → allowed (parent L))
    (hsearch : ∀ L, allowed L → ∀ remaining, context search credit L = some remaining →
      search' L remaining = search L remaining) {L : LeafAddr} (hL : allowed L) :
    context search' credit L = context search credit L := by
  unfold context
  split_ifs with hzero
  · rfl
  · exact after_congr_on credit allowed hparent hsearch (hparent L hL hzero)

/-- The message family is explicit so the same canonical search applies to the
    paired forest and to the original forest during the transition. -/
noncomputable def searchOf (answers : SigGolfCandidate.T3.Correctness.Answers)
    (messages : LeafAddr → WCT9.LayerMsg) : Search := fun L remaining =>
  evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay
    (WCT9.CanonicalPolicy.threshold L.lay.val remaining) L.tree L.leaf
    (messages L) 0 (WCT9.searchLimit L.lay))

noncomputable def referenceContext (answers : SigGolfCandidate.T3.Correctness.Answers)
    (messages : LeafAddr → WCT9.LayerMsg) : LeafAddr → Option Nat :=
  context (searchOf answers messages) WCT9.CanonicalPolicy.credit

noncomputable def referenceSearch (answers : SigGolfCandidate.T3.Correctness.Answers)
    (messages : LeafAddr → WCT9.LayerMsg) : LeafAddr → Option (BitVec 32 × List Nat) :=
  selected (searchOf answers messages) WCT9.CanonicalPolicy.credit

theorem referenceSearch_congr
    {answers answers' : SigGolfCandidate.T3.Correctness.Answers}
    {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hsearch : ∀ L remaining, referenceContext answers messages L = some remaining →
      searchOf answers' messages' L remaining = searchOf answers messages L remaining) (L : LeafAddr) :
    referenceSearch answers' messages' L = referenceSearch answers messages L :=
  selected_congr WCT9.CanonicalPolicy.credit hsearch L

theorem referenceContext_congr
    {answers answers' : SigGolfCandidate.T3.Correctness.Answers}
    {messages messages' : LeafAddr → WCT9.LayerMsg}
    (hsearch : ∀ L remaining, referenceContext answers messages L = some remaining →
      searchOf answers' messages' L remaining = searchOf answers messages L remaining) :
    referenceContext answers' messages' = referenceContext answers messages := by
  funext L
  exact context_congr WCT9.CanonicalPolicy.credit hsearch L

noncomputable def decodeRow (answers : SigGolfCandidate.T3.Correctness.Answers)
    (L : LeafAddr) (floor : Nat) (message : WCT9.LayerMsg) (counter : Nat) : Option (List Nat) :=
  WCT9.CanonicalPolicy.producerDecodeAt L.lay floor
    (evalWithAnswerFn answers (WCT9.encodingHash L.lay
      (WCT9.layerEncodingInput L.lay L.tree L.leaf message (BitVec.ofNat 32 counter))))

/-- It suffices to preserve decisions on the original reached prefix. In
    particular, replacing a rejected answer by another rejected answer leaves
    the canonical counter and digit word unchanged. -/
theorem search_congr (answers answers' : SigGolfCandidate.T3.Correctness.Answers)
    (L : LeafAddr) (floor : Nat) (message : WCT9.LayerMsg) : ∀ fuel start,
    (∀ c < fuel, (∀ c' < c, decodeRow answers L floor message (start + c') = none) →
      decodeRow answers' L floor message (start + c) = decodeRow answers L floor message (start + c)) →
    evalWithAnswerFn answers' (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message start fuel) =
      evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start _; rfl
  | succ fuel ih =>
      intro start h
      have hzero : decodeRow answers' L floor message start = decodeRow answers L floor message start := by
        have h0 := h 0 (Nat.zero_lt_succ _) (fun c hc => absurd hc (Nat.not_lt_zero _))
        simpa only [Nat.add_zero] using h0
      have hrest (hnone : decodeRow answers L floor message start = none) :
          evalWithAnswerFn answers' (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel) =
            evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel) := by
        apply ih (start + 1)
        intro c hc hprev
        have hnext := h (c + 1) (by omega) (fun c' hc' => by
          cases c' with
          | zero => simpa only [Nat.add_zero] using hnone
          | succ c' =>
              have hp := hprev c' (by omega)
              simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hp)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
      rw [WCT9.CanonicalPolicy.layerCounterSearchAt]
      conv_lhs => rw [evalWithAnswerFn_bind]
      conv_rhs => rw [evalWithAnswerFn_bind]
      change evalWithAnswerFn answers' (match decodeRow answers' L floor message start with
        | none => WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel
        | some digits => pure (some (BitVec.ofNat 32 start, digits))) =
        evalWithAnswerFn answers (match decodeRow answers L floor message start with
        | none => WCT9.CanonicalPolicy.layerCounterSearchAt L.lay floor L.tree L.leaf message (start + 1) fuel
        | some digits => pure (some (BitVec.ofNat 32 start, digits)))
      rw [hzero]
      cases hd : decodeRow answers L floor message start with
      | none => exact hrest hd
      | some digits => rfl

theorem reference_congr_of_decisions
    (answers answers' : SigGolfCandidate.T3.Correctness.Answers)
    (messages messages' : LeafAddr → WCT9.LayerMsg)
    (allowed : LeafAddr → Prop)
    (hparent : ∀ L, allowed L → L.lay.val ≠ 0 → allowed (parent L))
    (hmessages : ∀ L, allowed L → messages' L = messages L)
    (hdecisions : ∀ L, allowed L → ∀ remaining, referenceContext answers messages L = some remaining →
      ∀ c < WCT9.searchLimit L.lay,
        (∀ c' < c, decodeRow answers L (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (messages L) c' = none) →
        decodeRow answers' L (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (messages L) c =
          decodeRow answers L (WCT9.CanonicalPolicy.threshold L.lay.val remaining) (messages L) c)
    {L : LeafAddr} (hL : allowed L) :
    referenceContext answers' messages' L = referenceContext answers messages L ∧
      referenceSearch answers' messages' L = referenceSearch answers messages L := by
  have hs : ∀ L, allowed L → ∀ remaining, referenceContext answers messages L = some remaining →
      searchOf answers' messages' L remaining = searchOf answers messages L remaining := by
    intro L hL remaining hc
    unfold searchOf
    rw [hmessages L hL]
    apply search_congr answers answers' L _ _ _ 0
    simpa only [Nat.zero_add] using hdecisions L hL remaining hc
  have hc := context_congr_on WCT9.CanonicalPolicy.credit allowed hparent hs hL
  refine ⟨hc, ?_⟩
  unfold referenceSearch selected
  rw [hc]
  cases he : context (searchOf answers messages) WCT9.CanonicalPolicy.credit L with
  | none => rfl
  | some remaining => exact hs L hL remaining he

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
namespace ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
def SourceLeaf7 (L : LeafAddr) : Prop := L.tree < 2 ^ ClaudeWCT.W9.T3M.Extract.treeBits L.lay ∧ L.leaf < 2 ^ height L.lay
def SourceChain7 (a : ChainAddr) : Prop := SourceLeaf7 a.key ∧ a.chain < chainCount a.key.lay
theorem SourceLeaf7.tree_lt {L : LeafAddr} (h : SourceLeaf7 L) : L.tree < 2 ^ 31 :=
  lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by decide)
    (le_trans (ClaudeWCT.W9.T3M.Extract.treeBits_le _) (by decide)))
end ClaudeWCT.W9.T3.Security.WotsExtract

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable def referenceDigits (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) : List Nat :=
  ((referenceSearch answers messages L).map Prod.snd).getD
    (dummyDigits (WCT9.CanonicalPolicy.normalLayer L.lay))

noncomputable def depth (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) : Nat := (referenceDigits answers messages a.key).getD a.chain 0

/-- C3 (#866): the frontier is the honest chain of the current scheme (`honestChainValueW`: lower chain 0's last
step keeps the HIGH half). -/
noncomputable def frontierValue (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (a : ChainAddr) : Digest :=
  ClaudeWCT.W9.T3.Security.Wots.honestChainValueW answers a.key.lay a.key.tree a.key.leaf a.chain
    (WCT9.wotsSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers messages a)

noncomputable def referenceInput (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers messages L).map fun selected => encRow L (messages L) selected.1 0


end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M

/-- C3 (#866): chain rows are read through the half their step keeps (`SeenRowW`). -/
def ContactAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers messages a ∧ ∃ value,
    ClaudeWCT.W9.T3.Security.Wots.SeenRowW trace a (depth answers messages a - 1) value
      (frontierValue answers messages a)

def TwoEdgeAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers messages a ∧ ∃ start middle,
    ClaudeWCT.W9.T3.Security.Wots.SeenRowW trace a (depth answers messages a - 2) start middle ∧
    ClaudeWCT.W9.T3.Security.Wots.SeenRowW trace a (depth answers messages a - 1) middle
      (frontierValue answers messages a)

def EncodingMatchAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter pad answer, Extract.msgFits L.lay message ∧ (encRow L message counter pad, answer) ∈ trace ∧
    referenceInput answers messages L ≠ some (encRow L message counter pad) ∧
    WCT9.CanonicalPolicy.decode L.lay (WCT9.encodingAnswer L.lay answer) = some (referenceDigits answers messages L)

def MarkerAt (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter pad answer digits, Extract.msgFits a.key.lay message ∧
    (encRow a.key message counter pad, answer) ∈ trace ∧
    referenceInput answers messages a.key ≠ some (encRow a.key message counter pad) ∧
    WCT9.CanonicalPolicy.decode a.key.lay (WCT9.encodingAnswer a.key.lay answer) = some digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers messages a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers messages a.key).getD i 0 ≤ digits.getD i 0

def OtherChainRow (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg) (input : HashInput) : Prop :=
  ∃ (a : ChainAddr) (step : Nat), Extract.posOf input =
      some (.chain a.key.lay a.key.tree a.key.leaf a.chain step) ∧
    ((∀ value, input ≠ chainRow a step value) ∨ depth answers messages a ≤ step)

def StructuralClass (answers : Answers) (messages : LeafAddr → WCT9.LayerMsg)
    (input : HashInput) (position : Extract.Pos) : Prop :=
  match position with
  | .chain _ _ _ _ _ => OtherChainRow answers messages input
  | _ => True
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
