import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest
import SigGolfCandidate.SphincsSecurity.Proof.Base.FirstSuccessFamily
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableOverwrite

namespace ClaudeWCT.W9.T3.Security.CanonEncoding
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev EncLeaf := {L : LeafPos // L.Source}
def EncLeaf.toWots (L : EncLeaf) : Wots.LeafAddr := ⟨L.1.lay, L.1.tree.val, L.1.leaf.val⟩
theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ treeBits lay :=
  Extract.route_tree_treeBits index hindex lay
theorem route_source (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    ∃ L : EncLeaf, L.toWots = ⟨lay, (route index lay).2, (route index lay).1⟩ := by
  have hleaf := route_leaf_bound index lay
  have htree := route_tree_lt index hindex lay
  have ht31 : (route index lay).2 < 2 ^ 31 := lt_of_lt_of_le htree
    (Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide))
  have hl4096 : (route index lay).1 < 4096 := lt_of_lt_of_le hleaf (by
    calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le lay)
      _ = 4096 := by norm_num)
  exact ⟨⟨⟨lay, ⟨(route index lay).2, ht31⟩, ⟨(route index lay).1, hl4096⟩⟩, htree, hleaf⟩, rfl⟩
theorem childIndex_lt (L : EncLeaf) : L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val < 2 ^ 31 := by
  obtain ⟨⟨lay, tree, leaf⟩, ht, hl⟩ := L
  change tree.val < 2 ^ treeBits lay at ht
  change leaf.val < 2 ^ height lay at hl
  change tree.val * 2 ^ height lay + leaf.val < 2 ^ 31
  fin_cases lay <;> simp [treeBits, height] at ht hl ⊢ <;> omega
def childIndex (L : EncLeaf) : Fin (2^31) :=
  ⟨L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val, childIndex_lt L⟩
theorem childIndex_treeBits (L : EncLeaf) (hlay : L.1.lay.val < 3) :
    (childIndex L).val < 2 ^ treeBits ⟨L.1.lay.val + 1, by omega⟩ := by
  obtain ⟨⟨lay, tree, leaf⟩, ht, hl⟩ := L
  change tree.val < 2 ^ treeBits lay at ht
  change leaf.val < 2 ^ height lay at hl
  change lay.val < 3 at hlay
  change tree.val * 2 ^ height lay + leaf.val < 2 ^ treeBits ⟨lay.val + 1, by omega⟩
  fin_cases lay <;> simp [treeBits, height] at ht hl hlay ⊢ <;> omega
def msgLabel (labels : Labels) (L : EncLeaf) : WCT9.LayerMsg :=
  if h : L.1.lay.val < 3 then
    .pair (treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩ - 1) 0)
      (treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩ - 1) 1)
  else .forest ((labels (.forest (childIndex L))).extractLsb' 0 128)
theorem leafMsg_eq {answers : Answers} {labels : Labels} (h : Agrees answers labels) (L : EncLeaf) :
    Wots.leafMsg answers L.toWots = msgLabel labels L := by
  unfold Wots.leafMsg msgLabel EncLeaf.toWots
  dsimp only
  split_ifs with hlay
  · rw [show L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val = (childIndex L).val from rfl,
      honestPair_eq h ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L hlay)]
  · rw [show L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val = (childIndex L).val from rfl,
      Nat.mod_eq_of_lt (childIndex L).isLt, honestForest_eq h (childIndex L)]
def encKey (labels : Labels) (x : EncLeaf × Fin (2^22)) : EncKey :=
  ((x.1.1.lay, x.1.1.tree, x.1.1.leaf, msgLabel labels x.1), x.2)
theorem hdrBlock_encQuery (key : EncKey) :
    Extract.hdrBlock (encQuery key) = bytesLE 16 (rowTweak key.1.1 key.1.2.1.val key.1.2.2.1.val) :=
  BC.hdrBlock_layerEncodingInput _ _ _ _ _
theorem row_ne_hdr (lay : Layer) (tree leaf : Nat) (node : Node) : rowTweak lay tree leaf ≠ node.toPos.hdr :=
  Extract.rowTweak_ne_hdr lay tree leaf (toPos_bounded node)
theorem encodingQuery_ne_cell (key : EncKey) (secrets : Secrets) (node : Node) (labels : Labels) :
    encQuery key ≠ cell secrets node labels := by
  intro heq
  have h1 := hdrBlock_encQuery key
  rw [heq, hdrBlock_cell] at h1
  exact row_ne_hdr _ _ _ node (bytesLE_injective h1).symm
noncomputable def encCell (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (x : EncLeaf × Fin (2^22)) : U :=
  ⟨encQuery (encKey labels x), hE (encQuery_mem _)⟩
theorem encCell_val (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) (x : EncLeaf × Fin (2^22)) :
    (encCell U hE labels x).val = pad64 (WCT9.layerEncodingInput x.1.1.lay x.1.1.tree.val x.1.1.leaf.val
      (msgLabel labels x.1) (BitVec.ofNat 32 x.2.val)) := rfl
theorem encCell_injective (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) :
    Function.Injective (encCell U hE labels) := by
  rintro ⟨⟨⟨lay, tree, leaf⟩, hL⟩, c⟩ ⟨⟨⟨lay', tree', leaf'⟩, hL'⟩, c'⟩ heq
  have hv := congrArg Subtype.val heq
  rw [encCell_val, encCell_val, ← BC.pad64_layerEncodingInputP_zero, ← BC.pad64_layerEncodingInputP_zero] at hv
  obtain ⟨e1, e2, e3, e4⟩ := BC.layerEncodingRow_coords hL.routed.1 hL.routed.2 hL'.routed.1 hL'.routed.2 hv
  simp only at e1 e2 e3 e4
  subst e1
  have e2' : tree = tree' := Fin.ext e2
  have e3' : leaf = leaf' := Fin.ext e3
  subst e2' e3'
  have e4' : c = c' := by
    have h1 := congrArg BitVec.toNat e4
    simp only [BitVec.toNat_ofNat] at h1
    exact Fin.ext (by rw [Nat.mod_eq_of_lt (lt_trans c.isLt (by norm_num)),
      Nat.mod_eq_of_lt (lt_trans c'.isLt (by norm_num))] at h1; exact h1)
  subst e4'
  rfl
def decodeAt (L : EncLeaf) (answer : HashOutput) : Option Digest :=
  if (WCT9.producerDecode L.1.lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none
theorem decodeAt_eq_some (L : EncLeaf) (answer : HashOutput) (d : Digest) :
    decodeAt L answer = some d ↔ answer.extractLsb' 0 128 = d ∧ (WCT9.producerDecode L.1.lay d).isSome := by
  unfold decodeAt
  split_ifs with hs
  · constructor
    · intro he; cases he; exact ⟨rfl, hs⟩
    · rintro ⟨rfl, -⟩; rfl
  · constructor
    · intro he; cases he
    · rintro ⟨rfl, h⟩; exact absurd h hs
theorem decodeAt_eq_none (L : EncLeaf) (answer : HashOutput) :
    decodeAt L answer = none ↔ WCT9.producerDecode L.1.lay (answer.extractLsb' 0 128) = none := by
  unfold decodeAt
  split_ifs with hs
  · simp only [false_iff]
    intro hn; rw [hn] at hs; exact absurd hs (by decide)
  · simp only [true_iff]
    cases hd : WCT9.producerDecode L.1.lay (answer.extractLsb' 0 128) with
    | none => rfl
    | some w => rw [hd] at hs; exact absurd rfl hs
abbrev Selection := Option (Fin (2^22) × Digest)
abbrev Selections := EncLeaf → Selection
noncomputable def rawSelectionsOf (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (table : U → HashOutput) : Selections :=
  fun L => FirstSuccessTable.select (decodeAt L) (fun c => table (encCell U hE labels (L, c)))
def capSel (L : EncLeaf) (s : Selection) : Selection :=
  s.filter fun r => decide (r.1.val < WCT9.searchLimit L.1.lay)
theorem capSel_eq_some {L : EncLeaf} {s : Selection} {r : Fin (2^22) × Digest} :
    capSel L s = some r ↔ s = some r ∧ r.1.val < WCT9.searchLimit L.1.lay := by
  cases s with
  | none => simp [capSel]
  | some r' =>
      by_cases h : r'.1.val < WCT9.searchLimit L.1.lay
      · simp only [capSel, Option.filter, h, decide_true, if_true, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨rfl, h⟩
        · rintro ⟨rfl, -⟩
          rfl
      · simp only [capSel, Option.filter, h, decide_false, Bool.false_eq_true, if_false, Option.some.injEq]
        constructor
        · intro hc
          cases hc
        · rintro ⟨rfl, h'⟩
          exact absurd h' h
noncomputable def selectionsOf (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (table : U → HashOutput) : Selections :=
  fun L => capSel L (rawSelectionsOf U hE labels table L)
theorem counterSearch_select (answers : Answers) (lay : Layer) (tree leaf : Nat) (message : WCT9.LayerMsg)
    (decodeLay : HashOutput → Option Digest)
    (hdecode : ∀ answer, decodeLay answer =
      if (WCT9.producerDecode lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none) :
    ∀ fuel start, evalWithAnswerFn answers (WCT9.layerCounterSearch lay tree leaf message start fuel) =
      (FirstSuccessTable.select decodeLay (fun i : Fin fuel =>
          answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
            (BitVec.ofNat 32 (start + i.val)))))))).bind
        fun r => (WCT9.producerDecode lay r.2).map fun digits => (BitVec.ofNat 32 (start + r.1.val), digits) := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
      intro start
      simp only [WCT9.layerCounterSearch, evalWithAnswerFn_bind, eval_shortHash]
      rw [FirstSuccessTable.select]
      have h0 : answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
          (BitVec.ofNat 32 (start + (0 : Fin (fuel + 1)).val)))))) =
          answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message (BitVec.ofNat 32 start))))) := by
        simp only [Fin.val_zero, Nat.add_zero]
      rw [h0, hdecode]
      generalize answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
        (BitVec.ofNat 32 start))))) = A
      cases hd : WCT9.producerDecode lay (A.extractLsb' 0 128) with
      | some digits =>
          simp only [hd, Option.isSome_some, if_true, evalWithAnswerFn_pure, Option.bind_some, Option.map_some,
            Fin.val_zero, Nat.add_zero]
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          rw [ih (start + 1)]
          have htail : (fun i : Fin fuel => answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
              (BitVec.ofNat 32 (start + (i.succ).val))))))) =
              (fun i : Fin fuel => answers (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf message
                (BitVec.ofNat 32 (start + 1 + i.val))))))) := by
            funext i
            rw [Fin.val_succ, show start + (i.val + 1) = start + 1 + i.val by omega]
          rw [htail]
          cases FirstSuccessTable.select decodeLay (fun i : Fin fuel => answers (.inl (.inr
              (pad64 (WCT9.layerEncodingInput lay tree leaf message (BitVec.ofNat 32 (start + 1 + i.val))))))) with
          | none => rfl
          | some r =>
              simp only [Option.map_some, Option.bind_some, Fin.val_succ,
                show start + (r.1.val + 1) = start + 1 + r.1.val by omega]
theorem answers_encCell (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x)
    (x : EncLeaf × Fin (2^22)) :
    answers (.inl (.inr (encCell U hE labels x).val)) = residual (encCell U hE labels x) := by
  rw [hpub]
  apply programmed_other
  intro node heq
  exact encodingQuery_ne_cell _ _ node labels heq
theorem select_castLE_bind {Answer Value β : Type} (decode : Answer → Option Value) {n m : Nat} (h : n ≤ m)
    (table : Fin m → Answer) (g : Nat → Value → Option β) :
    (FirstSuccessTable.select decode (fun i : Fin n => table (Fin.castLE h i))).bind (fun r => g r.1.val r.2) =
      ((FirstSuccessTable.select decode table).filter fun r => decide (r.1.val < n)).bind
        (fun r => g r.1.val r.2) := by
  cases hs : FirstSuccessTable.select decode table with
  | none =>
      have hall := (FirstSuccessTable.select_none_iff decode table).mp hs
      have hp : FirstSuccessTable.select decode (fun i : Fin n => table (Fin.castLE h i)) = none :=
        (FirstSuccessTable.select_none_iff _ _).mpr fun i => hall _
      rw [hp]
      rfl
  | some r =>
      obtain ⟨i, v⟩ := r
      obtain ⟨hv, hbefore⟩ := (FirstSuccessTable.select_some_iff decode table i v).mp hs
      by_cases hlt : i.val < n
      · have hp : FirstSuccessTable.select decode (fun j : Fin n => table (Fin.castLE h j)) =
            some (⟨i.val, hlt⟩, v) := by
          apply (FirstSuccessTable.select_some_iff _ _ _ _).mpr
          refine ⟨?_, fun j hj => hbefore _ ?_⟩
          · have he : Fin.castLE h ⟨i.val, hlt⟩ = i := Fin.ext rfl
            rw [he]
            exact hv
          · rw [Fin.lt_def] at hj ⊢
            simpa using hj
        rw [hp]
        simp [Option.filter, hlt]
      · have hp : FirstSuccessTable.select decode (fun j : Fin n => table (Fin.castLE h j)) = none := by
          apply (FirstSuccessTable.select_none_iff _ _).mpr
          intro j
          apply hbefore
          rw [Fin.lt_def]
          simp only [Fin.coe_castLE]
          omega
        rw [hp]
        simp [Option.filter, hlt]
theorem referenceSearch_eq (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x)
    (L : EncLeaf) :
    Wots.referenceSearch answers L.toWots =
      (selectionsOf U hE labels residual L).bind fun r =>
        (WCT9.producerDecode L.1.lay r.2).map fun digits => (BitVec.ofNat 32 r.1.val, digits) := by
  have hagrees := agrees_of_programmed U hU answers labels residual hpub
  unfold Wots.referenceSearch
  rw [leafMsg_eq hagrees L]
  change evalWithAnswerFn answers (WCT9.layerCounterSearch L.1.lay L.1.tree.val L.1.leaf.val (msgLabel labels L) 0
    (WCT9.searchLimit L.1.lay)) = _
  rw [counterSearch_select answers L.1.lay L.1.tree.val L.1.leaf.val (msgLabel labels L) (decodeAt L)
    (fun _ => rfl) (WCT9.searchLimit L.1.lay) 0]
  have hle : WCT9.searchLimit L.1.lay ≤ 2 ^ 22 := WCT9.searchLimit_le L.1.lay
  have hrows : (fun i : Fin (WCT9.searchLimit L.1.lay) => answers (.inl (.inr (pad64 (WCT9.layerEncodingInput
      L.1.lay L.1.tree.val L.1.leaf.val (msgLabel labels L) (BitVec.ofNat 32 (0 + i.val))))))) =
      fun i => residual (encCell U hE labels (L, Fin.castLE hle i)) := by
    funext c
    rw [Nat.zero_add]
    exact answers_encCell U hU hE answers labels residual hpub (L, Fin.castLE hle c)
  rw [hrows]
  simp only [Nat.zero_add]
  unfold selectionsOf rawSelectionsOf capSel
  exact select_castLE_bind (decodeAt L) hle (fun c => residual (encCell U hE labels (L, c)))
    (fun k v => (WCT9.producerDecode L.1.lay v).map fun digits => (BitVec.ofNat 32 k, digits))
end ClaudeWCT.W9.T3.Security.CanonEncoding
