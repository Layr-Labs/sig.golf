import SigGolfCandidate.T3.Secc.CanonGraphHonest
import SigGolfCandidate.SphincsSecurity.Proof.Base.FirstSuccessFamily
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableOverwrite

namespace SigGolfCandidate.T3.Security.CanonEncoding
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev EncLeaf := {L : LeafPos // L.Source}
def EncLeaf.toWots (L : EncLeaf) : Wots.LeafAddr := ⟨L.1.lay, L.1.tree.val, L.1.leaf.val⟩
theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ treeBits lay := by
  fin_cases lay <;> simp [route, treeBits, height] <;> omega
theorem route_source (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    ∃ L : EncLeaf, L.toWots = ⟨lay, (route index lay).2, (route index lay).1⟩ := by
  have hleaf := route_leaf_bound index lay
  have htree := route_tree_lt index hindex lay
  have ht31 : (route index lay).2 < 2 ^ 31 := lt_of_lt_of_le htree
    (Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide))
  have hl4096 : (route index lay).1 < 4096 := lt_of_lt_of_le hleaf (by
    calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
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
def msgLabel (labels : Labels) (L : EncLeaf) : Digest :=
  if h : L.1.lay.val < 3 then
    treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩) 0
  else (labels (.forest (childIndex L))).extractLsb' 0 128
theorem leafMsg_eq {answers : Answers} {labels : Labels} (h : Agrees answers labels) (L : EncLeaf) :
    Wots.leafMsg answers L.toWots = msgLabel labels L := by
  unfold Wots.leafMsg msgLabel EncLeaf.toWots
  dsimp only
  split_ifs with hlay
  · exact honestRoot_eq h ⟨L.1.lay.val + 1, by omega⟩ (childIndex L)
  · exact honestForest_eq h (childIndex L)
def decodeAt (L : EncLeaf) (answer : HashOutput) : Option Digest :=
  if (searchDecode L.1.lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none
theorem decodeAt_eq_some (L : EncLeaf) (answer : HashOutput) (d : Digest) :
    decodeAt L answer = some d ↔ answer.extractLsb' 0 128 = d ∧ (searchDecode L.1.lay d).isSome := by
  unfold decodeAt
  split_ifs with hs
  · constructor
    · intro he; cases he; exact ⟨rfl, hs⟩
    · rintro ⟨rfl, -⟩; rfl
  · constructor
    · intro he; cases he
    · rintro ⟨rfl, h⟩; exact absurd h hs
theorem decodeAt_eq_none (L : EncLeaf) (answer : HashOutput) :
    decodeAt L answer = none ↔ searchDecode L.1.lay (answer.extractLsb' 0 128) = none := by
  unfold decodeAt
  split_ifs with hs
  · simp only [false_iff]
    intro hn; rw [hn] at hs; exact absurd hs (by decide)
  · simp only [true_iff]
    cases hd : searchDecode L.1.lay (answer.extractLsb' 0 128) with
    | none => rfl
    | some w => rw [hd] at hs; exact absurd rfl hs
abbrev Selection := Option (Fin (2^22) × Digest)
abbrev Selections := EncLeaf → Selection
noncomputable def selectionLaw : PMF Selections :=
  FinitePmfProduct.law (fun L => FirstSuccessTable.selected (decodeAt L) (2^22))
noncomputable def rowsLaw (selections : Selections) : PMF (EncLeaf → Fin (2^22) → HashOutput) :=
  FinitePmfProduct.law (fun L => FirstSuccessTable.afterSelect (decodeAt L) (2^22) (selections L))
theorem rowsLaw_apply (selections : Selections) (rows : EncLeaf → Fin (2^22) → HashOutput) :
    rowsLaw selections rows =
      ∏ L, FirstSuccessTable.afterSelect (decodeAt L) (2^22) (selections L) (rows L) :=
  FinitePmfProduct.apply _ _
theorem afterSelect_some (L : EncLeaf) (i : Fin (2^22)) (d : Digest) :
    FirstSuccessTable.afterSelect (decodeAt L) (2^22) (some (i, d)) =
      FirstSuccessTable.constrained (FirstSuccessTable.allowed (decodeAt L) i d) := rfl
theorem afterSelect_none (L : EncLeaf) :
    FirstSuccessTable.afterSelect (decodeAt L) (2^22) none =
      FirstSuccessTable.constrained (fun _ => FirstSuccessTable.invalid (decodeAt L)) := rfl
theorem mem_allowed (L : EncLeaf) (i : Fin (2^22)) (d : Digest) (c : Fin (2^22)) (answer : HashOutput) :
    answer ∈ FirstSuccessTable.allowed (decodeAt L) i d c ↔
      (c < i → searchDecode L.1.lay (answer.extractLsb' 0 128) = none) ∧
        (c = i → answer.extractLsb' 0 128 = d ∧ (searchDecode L.1.lay d).isSome) := by
  unfold FirstSuccessTable.allowed
  split_ifs with hlt heq
  · rw [FirstSuccessTable.mem_invalid, decodeAt_eq_none]
    exact ⟨fun h => ⟨fun _ => h, fun he => absurd (he ▸ hlt) (lt_irrefl _)⟩, fun h => h.1 hlt⟩
  · subst heq
    rw [FirstSuccessTable.mem_fiber, decodeAt_eq_some]
    exact ⟨fun h => ⟨fun h' => absurd h' (lt_irrefl _), fun _ => h⟩, fun h => h.2 rfl⟩
  · simp only [Finset.mem_univ, true_iff]
    exact ⟨fun h => absurd h hlt, fun h => absurd h heq⟩
theorem selected_mul_rowsLaw (results : Selections) (tables : EncLeaf → Fin (2^22) → HashOutput) :
    selectionLaw results * rowsLaw results tables =
      if (fun L => FirstSuccessTable.select (decodeAt L) (tables L)) = results then
        PMF.uniformOfFintype (EncLeaf → Fin (2^22) → HashOutput) tables else 0 := by
  rw [selectionLaw, rowsLaw, FinitePmfProduct.apply, FinitePmfProduct.apply, ← Finset.prod_mul_distrib]
  simp only [FirstSuccessTable.selected_mul_afterSelect]
  by_cases h : (fun L => FirstSuccessTable.select (decodeAt L) (tables L)) = results
  · rw [if_pos h]
    have hcoordinate (L : EncLeaf) : FirstSuccessTable.select (decodeAt L) (tables L) = results L := congrFun h L
    simp only [hcoordinate, if_true, FirstSuccessTable.full_eq_uniform]
    rw [← FinitePmfProduct.apply (fun _ : EncLeaf => PMF.uniformOfFintype (Fin (2^22) → HashOutput)) tables,
      FinitePmfProduct.uniform]
  · rw [if_neg h]
    have hex : ∃ L, FirstSuccessTable.select (decodeAt L) (tables L) ≠ results L := by
      by_contra! hall
      exact h (funext hall)
    obtain ⟨L, hL⟩ := hex
    exact Finset.prod_eq_zero (by simp) (if_neg hL)
theorem uniform_bind_eq_selected {Result : Type}
    (next : Selections → (EncLeaf → Fin (2^22) → HashOutput) → PMF Result) :
    (PMF.uniformOfFintype (EncLeaf → Fin (2^22) → HashOutput)).bind
        (fun tables => next (fun L => FirstSuccessTable.select (decodeAt L) (tables L)) tables) =
      selectionLaw.bind (fun results => (rowsLaw results).bind (next results)) := by
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, selected_mul_rowsLaw, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun tables => ?_
  rw [tsum_eq_single (fun L => FirstSuccessTable.select (decodeAt L) (tables L))]
  · rw [if_pos rfl]
  · intro results hne
    rw [if_neg (Ne.symm hne)]
section SelectionBind
noncomputable local instance instSampleableTypeHashOutput_canonEncoding : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonEncoding (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
noncomputable local instance instFintypeCoordinate_canonEncoding : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_canonEncoding : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeLabels_canonEncoding : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSecrets_canonEncoding : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeOtherHalves_canonEncoding : SampleableType OtherHalves := SampleableType.ofFintype _
end SelectionBind
theorem counterSearch_select (answers : Answers) (lay : Layer) (tree leaf : Nat) (message : Digest)
    (decodeLay : HashOutput → Option Digest)
    (hdecode : ∀ answer, decodeLay answer =
      if (searchDecode lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none) :
    ∀ fuel start, evalWithAnswerFn answers (counterSearch lay tree leaf message start fuel) =
      (FirstSuccessTable.select decodeLay (fun i : Fin fuel =>
          answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message (start + i.val)))))).bind
        fun r => (searchDecode lay r.2).map fun digits => (BitVec.ofNat 32 (start + r.1.val), digits) := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
      intro start
      simp only [counterSearch, evalWithAnswerFn_bind, eval_shortHash]
      rw [FirstSuccessTable.select]
      have h0 : answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message (start + (0 : Fin (fuel + 1)).val)))) =
          answers (.inl (.inr (pad64 (encodingInput lay tree leaf message (BitVec.ofNat 32 start))))) := by
        simp only [Fin.val_zero, Nat.add_zero, Sampling.encodingTrial]
      rw [h0, hdecode]
      generalize answers (.inl (.inr (pad64 (encodingInput lay tree leaf message (BitVec.ofNat 32 start))))) = A
      cases hd : searchDecode lay (A.extractLsb' 0 128) with
      | some digits =>
          simp only [hd, Option.isSome_some, if_true, evalWithAnswerFn_pure, Option.bind_some, Option.map_some,
            Fin.val_zero, Nat.add_zero]
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          rw [ih (start + 1)]
          have htail : (fun i : Fin fuel => answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message
              (start + (i.succ).val))))) =
              (fun i : Fin fuel => answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message
                (start + 1 + i.val))))) := by
            funext i
            rw [Fin.val_succ, show start + (i.val + 1) = start + 1 + i.val by omega]
          rw [htail]
          cases FirstSuccessTable.select decodeLay (fun i : Fin fuel => answers (.inl (.inr
              (Sampling.encodingTrial lay tree leaf message (start + 1 + i.val))))) with
          | none => rfl
          | some r =>
              simp only [Option.map_some, Option.bind_some, Fin.val_succ,
                show start + (r.1.val + 1) = start + 1 + r.1.val by omega]
end SigGolfCandidate.T3.Security.CanonEncoding
