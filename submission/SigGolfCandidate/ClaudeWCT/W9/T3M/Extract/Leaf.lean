import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.HdrBlocks
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Queries

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsSeed wotsEnd wotsValue wotsRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem flatMap_bytes_injective : ∀ {xs ys : List Digest}, xs.length = ys.length →
    xs.flatMap (bytesLE 16) = ys.flatMap (bytesLE 16) → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, hrest⟩ := List.append_inj h (by simp only [bytesLE_length])
      rw [bytesLE_injective hxy, flatMap_bytes_injective (by simpa using hlen) hrest]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem listInput_injective {first first' : Digest} {hdr hdr' : BitVec 128} {rest rest' : List Digest}
    (hlen : rest.length = rest'.length) (h : listInput first hdr rest = listInput first' hdr' rest') :
    first = first' ∧ hdr = hdr' ∧ rest = rest' := by
  unfold listInput at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hf, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hf, bytesLE_injective hh, flatMap_bytes_injective hlen hr⟩
theorem list_head_drop : ∀ (xs : List Digest), 0 < xs.length → xs.getD 0 0 :: xs.drop 1 = xs
  | _ :: _, _ => rfl
theorem listInput_lists {xs ys : List Digest} {hdr hdr' : BitVec 128} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr' (ys.drop 1))) :
    xs = ys ∧ hdr = hdr' := by
  have hl : (listInput (xs.getD 0 0) hdr (xs.drop 1)).length = (listInput (ys.getD 0 0) hdr' (ys.drop 1)).length := by
    rw [listInput_length, listInput_length, List.length_drop, List.length_drop, hlen]
  obtain ⟨hf, hh, hr⟩ := listInput_injective (by rw [List.length_drop, List.length_drop, hlen])
    (Sampling.pad64_inj_of_length hl h)
  refine ⟨?_, hh⟩
  rw [← list_head_drop xs (by omega), ← list_head_drop ys hpos, hf, hr]
theorem hdrBlock_prefix (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
theorem hdrBlock_pad64 (input : HashInput) (h : 32 ≤ input.length) : hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem hdrBlock_block4 (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix a b _
theorem hdrBlock_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  rw [hdrBlock_pad64 _ (by rw [listInput_length]; omega)]
  exact hdrBlock_prefix first hdr _
private theorem hdrBlock_forestInput_leaf (index : Nat) (pairs : List (Digest × Digest)) :
    hdrBlock (pad64 (forestInput index pairs)) = bytesLE 16 (header 15 0 index 0 0) := by
  rw [hdrBlock_pad64 _ (by simp only [forestInput, WCT9.forestInput, zero16, List.length_append,
    List.length_replicate, bytesLE_length]; omega)]
  unfold forestInput WCT9.forestInput
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
  exact hdrBlock_prefix 0 _ _
theorem leafHash_eq_shortHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := rfl
theorem forestPk_eq_shortHash (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestPk index pairs = shortHash (forestInput index pairs) := rfl
theorem forestInput_pairs_injective {index : Nat} {ps qs : List (Digest × Digest)} (hl : ps.length = qs.length)
    (h : pad64 (forestInput index ps) = pad64 (forestInput index qs)) : ps = qs := by
  have hlen : (forestInput index ps).length = (forestInput index qs).length := by
    simp only [forestInput, WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length,
      WCT9.pairs_bytes_length, hl]
  have h := Sampling.pad64_inj_of_length hlen h
  unfold forestInput WCT9.forestInput at h
  obtain ⟨-, hp⟩ := List.append_inj h (by simp only [zero16, List.length_append, List.length_replicate,
    bytesLE_length])
  exact WCT9.pairs_bytes_injective hl hp
theorem listHash_extract (answers : Answers) (hdr : BitVec 128) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (hpos : 0 < ys.length)
    (reaches : evalWithAnswerFn answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1))) =
      evalWithAnswerFn answers (shortHash (listInput (ys.getD 0 0) hdr (ys.drop 1)))) :
    xs = ys ∨
      (HashHit answers (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1)))
          (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1))) ∧
        SameHeader (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))
          (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))) ∧
        .inl (.inr (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))) ∈
          queried answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1)))) := by
  by_cases heq : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))
  · exact Or.inl (listInput_lists hlen hpos heq).1
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · refine SameHeader.of_hdrBlock (pad64_length_congr ?_) (by rw [hdrBlock_listInput, hdrBlock_listInput])
      simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop, hlen]
    · rw [queried_shortHash]
      exact List.mem_singleton_self _
theorem leafInput_lists {lay : Layer} {tree leaf : Nat} {xs ys : List Digest} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (leafInput lay tree leaf xs) = pad64 (leafInput lay tree leaf ys)) : xs = ys := by
  unfold leafInput SigGolfCandidate.T3.leafInput at h
  split at h
  · have hl : (zero16 ++ bytesLE 16 (leafTweak lay tree leaf) ++ xs.flatMap (bytesLE 16)).length =
        (zero16 ++ bytesLE 16 (leafTweak lay tree leaf) ++ ys.flatMap (bytesLE 16)).length := by
      simp only [List.length_append, digest_list_bytes_length, hlen]
    have h' := Sampling.pad64_inj_of_length hl h
    obtain ⟨-, hr⟩ := List.append_inj h' (by simp only [List.length_append, bytesLE_length])
    exact flatMap_bytes_injective hlen hr
  · exact (listInput_lists (hdr := leafTweak lay tree leaf) (hdr' := leafTweak lay tree leaf) hlen hpos h).1
theorem leafHash_extract (answers : Answers) (lay : Layer) (tree leaf : Nat) (ends honest : List Digest)
    (hlen : ends.length = honest.length) (hpos : 0 < honest.length)
    (reaches : evalWithAnswerFn answers (leafHash lay tree leaf ends) =
      evalWithAnswerFn answers (leafHash lay tree leaf honest)) :
    ends = honest ∨
      (HashHit answers (pad64 (leafInput lay tree leaf honest)) (pad64 (leafInput lay tree leaf ends)) ∧
        SameHeader (pad64 (leafInput lay tree leaf ends)) (pad64 (leafInput lay tree leaf honest)) ∧
        .inl (.inr (pad64 (leafInput lay tree leaf ends))) ∈ queried answers (leafHash lay tree leaf ends)) := by
  by_cases heq : pad64 (leafInput lay tree leaf ends) = pad64 (leafInput lay tree leaf honest)
  · exact Or.inl (leafInput_lists hlen hpos heq)
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [leafHash_eq_shortHash, leafHash_eq_shortHash, eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · refine SameHeader.of_hdrBlock (pad64_length_congr ?_) (by rw [hdrBlock_leafInput, hdrBlock_leafInput])
      unfold leafInput
      rw [SigGolfCandidate.T3.leafInput_length, SigGolfCandidate.T3.leafInput_length, hlen]
    · rw [leafHash_eq_shortHash, queried_shortHash]
      exact List.mem_singleton_self _
theorem forestPk_extract (answers : Answers) (index : Nat) (pairs honest : List (Digest × Digest))
    (hlen : pairs.length = honest.length)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index pairs) =
      evalWithAnswerFn answers (WCT9.forestPk index honest)) :
    pairs = honest ∨
      (HashHit answers (pad64 (forestInput index honest)) (pad64 (forestInput index pairs)) ∧
        SameHeader (pad64 (forestInput index pairs)) (pad64 (forestInput index honest)) ∧
        .inl (.inr (pad64 (forestInput index pairs))) ∈ queried answers (WCT9.forestPk index pairs)) := by
  by_cases heq : pad64 (forestInput index pairs) = pad64 (forestInput index honest)
  · exact Or.inl (forestInput_pairs_injective hlen heq)
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [forestPk_eq_shortHash, forestPk_eq_shortHash, eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · refine SameHeader.of_hdrBlock (pad64_length_congr ?_)
        (by rw [hdrBlock_forestInput_leaf, hdrBlock_forestInput_leaf])
      simp only [forestInput, WCT9.forestInput, List.length_append, zero16, List.length_replicate, bytesLE_length,
        List.length_flatMap]
      simp [Function.comp_def, bytesLE_length, hlen]
    · rw [forestPk_eq_shortHash, queried_shortHash]
      exact List.mem_singleton_self _
theorem forestPk_honest_extract (answers : Answers) (index : Nat) (hidx : index < 2 ^ 40)
    (pairs : List (Digest × Digest)) (hlen : pairs.length = 9)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index pairs) = honestForest answers index) :
    pairs = ftsPairsHonest answers index ∨ HitIn answers (queried answers (WCT9.forestPk index pairs)) := by
  rcases forestPk_extract answers index pairs (ftsPairsHonest answers index)
      (by rw [hlen, ftsPairsHonest_length]) reaches with h | ⟨hh, hs, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨.forest index, _, hidx, hq, hh, hs⟩
theorem queried_mapM_mem {α β : Type} (answers : Answers) (f : α → M β) :
    ∀ (l : List α), ∀ a ∈ l, ∀ q ∈ queried answers (f a), q ∈ queried answers (l.mapM f)
  | [], _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, a, ha, q, hq => by
      rw [List.mapM_cons, queried_bind, queried_bind]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_append_left _ (queried_mapM_mem answers f xs a ha q hq))
/-! ### C2/C3 (FULL): half-aware hash paths and pads (shared with the Secc consumers, S2-6)
`hashPathW high input` is `hashPath input` with step `s` keeping the half `high s` (`WCT9.halfHash`). A hit on the
half `high` is `HashHitH answers high`; for a position `pos` it is `HashHitAt` (`hashHitAt_iff`, `pos.high`). -/
section halfPath
open ClaudeWCT.WCT9 (halfHash halfOf)
def hashPathW (high : Nat → Bool) (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) : M Digest :=
  (List.range count).foldlM (fun value step => halfHash (high step) (input step value)) initial
def pathValueW (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput) (initial : Digest)
    (count : Nat) : Digest :=
  evalWithAnswerFn answers (hashPathW high input count initial)
def pathInputW (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput) (initial : Digest)
    (step : Nat) : HashInput := input step (pathValueW answers high input initial step)
theorem eval_halfHash (answers : Answers) (high : Bool) (input : HashInput) :
    evalWithAnswerFn answers (halfHash high input) = halfOf high (answers (.inl (.inr (pad64 input)))) := by
  cases high <;> rfl
@[simp] theorem queried_halfHash (answers : Answers) (high : Bool) (input : HashInput) :
    queried answers (halfHash high input) = [.inl (.inr (pad64 input))] := by
  cases high <;> rfl
theorem hashPathW_succ (high : Nat → Bool) (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPathW high input (count + 1) initial =
      (hashPathW high input count initial >>= fun value => halfHash (high count) (input count value)) := by
  simp [hashPathW, List.range_succ, List.foldlM_append]
@[simp] theorem pathValueW_zero (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) : pathValueW answers high input initial 0 = initial := rfl
theorem pathValueW_succ (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) :
    pathValueW answers high input initial (step + 1) =
      evalWithAnswerFn answers (halfHash (high step) (pathInputW answers high input initial step)) := by
  simp only [pathValueW, hashPathW_succ, evalWithAnswerFn_bind, pathInputW]
theorem pathInputW_queried (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (initial : Digest) (count step : Nat) (hstep : step < count) :
    .inl (.inr (pad64 (pathInputW answers high input initial step))) ∈
      queried answers (hashPathW high input count initial) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [hashPathW_succ, queried_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
      · exact List.mem_append_left _ (ih hlt)
      · apply List.mem_append_right
        simp only [queried_halfHash, List.mem_singleton]
        rfl
theorem hashPathW_false (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPathW (fun _ => false) input count initial = hashPath input count initial := rfl
/-- A hit on the half `high`: a different input whose output agrees with the honest one on that half. -/
def HashHitH (answers : Answers) (high : Bool) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧ halfOf high (answers (.inl (.inr actual))) = halfOf high (answers (.inl (.inr honest)))
theorem hashHitAt_iff (answers : Answers) (pos : Pos) (honest actual : HashInput) :
    HashHitAt answers pos honest actual ↔ HashHitH answers pos.high honest actual := Iff.rfl
theorem hashHitH_false {answers : Answers} {honest actual : HashInput} :
    HashHitH answers false honest actual ↔ HashHit answers honest actual := Iff.rfl
theorem hashPathW_extract (answers : Answers) (high : Nat → Bool) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (halfHash (high step) (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValueW answers high input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count → Good step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputW answers high input initial step))) ∈
          queried answers (hashPathW high input count initial) ∧
        HashHitH answers (high step) (pad64 (honestInput step)) (pad64 (pathInputW answers high input initial step)) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInputW answers high input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hhit⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact hgood
        · exact Or.inr ⟨step, by omega, pathInputW_queried answers high input initial _ _ (by omega), hhit⟩
      · right
        refine ⟨count, by omega, pathInputW_queried answers high input initial _ _ (by omega), heq, ?_⟩
        have hr := reference count (by omega)
        rw [pathValueW_succ, eval_halfHash] at reaches
        rw [eval_halfHash] at hr
        exact reaches.trans hr.symm
/-! #### Chains (C3: lower chain 0's step 6 keeps the high half) -/
/-- The honest chain value of the current scheme after `step` steps (`WCT9.chainW`). -/
def honestChainValueW (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) : Digest :=
  evalWithAnswerFn answers (WCT9.chainW lay tree leaf i 0 step seed)
theorem honestChainValueW_succ (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    evalWithAnswerFn answers (halfHash (WCT9.chainHigh lay i step) (chainInput lay tree leaf i step
      (honestChainValueW answers lay tree leaf i seed step))) =
        honestChainValueW answers lay tree leaf i seed (step + 1) := by
  unfold honestChainValueW
  rw [WCT9.eval_chainW_add]
  simp [WCT9.chainW]
/-- Before step 6 the chain of the current scheme is the legacy chain. -/
theorem honestChainValueW_eq (answers : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) {step : Nat}
    (hs : step ≤ 6) :
    honestChainValueW answers lay tree leaf i seed step = honestChainValue answers lay tree leaf i seed step := by
  unfold honestChainValueW honestChainValue
  rw [WCT9.chainW_of_low (fun s _ hs' => WCT9.chainHigh_eq_false (Or.inr (Or.inr (by omega))))]
theorem wotsValue_eqW (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) :
    wotsValue answers lay tree leaf digits i =
      honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i) (digits.getD i 0) := rfl
theorem wotsEnd_eqW (answers : Answers) (lay : Layer) (tree leaf i : Nat) :
    wotsEnd answers lay tree leaf i =
      honestChainValueW answers lay tree leaf i (wotsSeed answers lay tree leaf i) (maxDigit lay i) := rfl
theorem chainPW_eq_hashPathW (lay : Layer) (tree leaf i start count : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (initial : Digest) :
    chainPW lay tree leaf i start count pad0 pad1 headerPad initial =
      hashPathW (fun s => WCT9.chainHigh lay i (start + s)) (chainPathInput lay tree leaf i start pad0 pad1 headerPad)
        count initial := by
  unfold chainPW hashPathW chainPathInput
  rw [List.range'_eq_map_range, List.foldlM_map]
theorem chainPathW_extract (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2 ^ 31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : pathValueW answers (fun s => WCT9.chainHigh lay i (start + s))
        (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value count =
      honestChainValueW answers lay tree leaf i seed (start + count)) :
    (value = honestChainValueW answers lay tree leaf i seed start ∧
      (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputW answers (fun s => WCT9.chainHigh lay i (start + s))
          (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
          queried answers (hashPathW (fun s => WCT9.chainHigh lay i (start + s))
            (chainPathInput lay tree leaf i start pad0 pad1 headerPad) count value) ∧
        HashHitH answers (WCT9.chainHigh lay i (start + step))
          (pad64 (chainInput lay tree leaf i (start + step)
            (honestChainValueW answers lay tree leaf i seed (start + step))))
          (pad64 (pathInputW answers (fun s => WCT9.chainHigh lay i (start + s))
            (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) := by
  have h := hashPathW_extract answers (fun s => WCT9.chainHigh lay i (start + s))
    (chainPathInput lay tree leaf i start pad0 pad1 headerPad)
    (fun step => chainInput lay tree leaf i (start + step)
      (honestChainValueW answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValueW answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) value count
    (fun step _ => by simpa only [Nat.add_assoc] using
      honestChainValueW_succ answers lay tree leaf i seed (start + step))
    (fun step hstep current heq => by
      have hs : start + step < 8 := by rcases hsteps with hz | hb <;> omega
      simp only [chainPathInput, chainInput_eq_zero _ _ _ _ _ _ ht hl hi hs, pad64_chainInputP] at heq
      have hhp := chainInputP_headerPad_eq heq
      obtain ⟨hp0, _, hp1, hv⟩ := chainInputP_fields heq
      exact ⟨hv, hp0, hp1, hhp⟩) reaches
  rcases h with ⟨hvalue, hpads⟩ | hhit
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => hpads 0 hcount⟩
  · exact Or.inr hhit
/-! #### Lower Merkle folds (C2: packed node word with a witness high word, half by heap parity) -/
/-- Fold input `step` of a lower path (`layerPairP`). -/
def merkleInputW (lay tree height leaf : Nat) (path : Nat → Digest) (hpads : Nat → BitVec 64) (pads : Nat → Digest)
    (step : Nat) (value : Digest) : HashInput :=
  let pair := if leaf / 2 ^ step % 2 = 0 then (value, path step) else (path step, value)
  WCT9.lowerNodeInputP lay tree (2 ^ (height - step - 1) + leaf / 2 ^ (step + 1)) pair.1 (hpads step) (pads step) pair.2
/-- The half kept by fold `step` of a lower path. -/
def merkleHighW (lay height leaf step : Nat) : Bool := WCT9.lowerHigh lay (2 ^ (height - step - 1) + leaf / 2 ^ (step + 1))
theorem lowerNodeInputP_length (lay tree heap : Nat) (l : Digest) (hp : BitVec 64) (p r : Digest) :
    (WCT9.lowerNodeInputP lay tree heap l hp p r).length = 64 := by
  simp [WCT9.lowerNodeInputP, bytesLE_length]
@[simp] theorem pad64_lowerNodeInputP (lay tree heap : Nat) (l : Digest) (hp : BitVec 64) (p r : Digest) :
    pad64 (WCT9.lowerNodeInputP lay tree heap l hp p r) = WCT9.lowerNodeInputP lay tree heap l hp p r := by
  simp [pad64, lowerNodeInputP_length]
theorem lowerNodeInputP_fields {lay tree heap : Nat} {l l' p p' r r' : Digest} {hp hp' : BitVec 64}
    (h : WCT9.lowerNodeInputP lay tree heap l hp p r = WCT9.lowerNodeInputP lay tree heap l' hp' p' r') :
    l = l' ∧ hp = hp' ∧ p = p' ∧ r = r' := by
  unfold WCT9.lowerNodeInputP at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hpd⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hl, ht⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hl, (append64_inj (bytesLE_injective ht)).1, bytesLE_injective hpd, bytesLE_injective hr⟩
theorem merkleInputW_parse (lay tree height leaf step : Nat) (path honestPath : Nat → Digest)
    (hpads : Nat → BitVec 64) (pads : Nat → Digest) (current target : Digest)
    (heq : pad64 (merkleInputW lay tree height leaf path hpads pads step current) =
      pad64 (merkleInputW lay tree height leaf honestPath (fun _ => 0) (fun _ => 0) step target)) :
    current = target ∧ path step = honestPath step ∧ hpads step = 0 ∧ pads step = 0 := by
  unfold merkleInputW at heq
  split at heq <;> simp only [pad64_lowerNodeInputP] at heq
  · obtain ⟨hc, hh, hp, hs⟩ := lowerNodeInputP_fields heq
    exact ⟨hc, hs, hh, hp⟩
  · obtain ⟨hs, hh, hp, hc⟩ := lowerNodeInputP_fields heq
    exact ⟨hc, hs, hh, hp⟩
theorem merklePathW_extract (answers : Answers) (lay tree height leaf count : Nat)
    (path honestPath target : Nat → Digest) (hpads : Nat → BitVec 64) (pads : Nat → Digest) (value : Digest)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (halfHash (merkleHighW lay height leaf step)
        (merkleInputW lay tree height leaf honestPath (fun _ => 0) (fun _ => 0) step (target step))) =
          target (step + 1))
    (reaches : pathValueW answers (merkleHighW lay height leaf) (merkleInputW lay tree height leaf path hpads pads)
      value count = target count) :
    (value = target 0 ∧ ∀ step, step < count → path step = honestPath step ∧ hpads step = 0 ∧ pads step = 0) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInputW answers (merkleHighW lay height leaf)
          (merkleInputW lay tree height leaf path hpads pads) value step))) ∈
          queried answers (hashPathW (merkleHighW lay height leaf) (merkleInputW lay tree height leaf path hpads pads)
            count value) ∧
        HashHitH answers (merkleHighW lay height leaf step)
          (pad64 (merkleInputW lay tree height leaf honestPath (fun _ => 0) (fun _ => 0) step (target step)))
          (pad64 (pathInputW answers (merkleHighW lay height leaf) (merkleInputW lay tree height leaf path hpads pads)
            value step)) :=
  hashPathW_extract answers _ _ _ target _ value count reference
    (fun step _ current => merkleInputW_parse lay tree height leaf step path honestPath hpads pads current
      (target step)) reaches
theorem merkleInputW_tree_reference (answers : Answers) (lay tree height leaf : Nat) (hlay : lay ≠ 0)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : WCT9.TreeLevelsL answers lay tree height leaves height levels)
    (hleaf : leaf < 2 ^ height) (step : Nat) (hstep : step < height) :
    evalWithAnswerFn answers (halfHash (merkleHighW lay height leaf step)
      (merkleInputW lay tree height leaf (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) := by
  unfold merkleInputW merkleHighW
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ, WCT9.lowerNodeInputP_zero hlay]
  have hparent : leaf / 2 ^ (step + 1) < 2 ^ (height - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2 ^ (step + 1)) hparent
  simpa only [treeValue, Nat.sub_sub, WCT9.lowerNodeHash, WCT9.lowerHash] using hp.symm
/-! #### Leaves (C3: witness pads in the leaf header block) -/
theorem leafInput_padded_length (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (hc : ends.length = chainCount lay) :
    (pad64 (leafInput lay tree leaf ends)).length = if lay = 0 then 896 else 704 := by
  unfold leafInput
  rw [pad64_length_of_mod] <;> rw [SigGolfCandidate.T3.leafInput_length, hc] <;> fin_cases lay <;> decide
theorem hdrBlock_leafInputW (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    hdrBlock (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)) = bytesLE 16 (WCT9.leafTweakW lay tree leaf hi) := by
  unfold WCT9.leafInputW
  split
  · rw [hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix _ _ _
  · rw [hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), List.append_assoc]
    exact hdrBlock_prefix _ _ _
theorem leafInputW_parse {lay : Layer} {tree leaf : Nat} {pad : Digest} {hi : BitVec 64} {ends honest : List Digest}
    (hlen : ends.length = honest.length) (hpos : 0 < honest.length)
    (h : pad64 (WCT9.leafInputW lay tree leaf pad hi ends) = pad64 (leafInput lay tree leaf honest)) :
    ends = honest ∧ hi = 0 ∧ (lay = 0 → pad = 0) := by
  rw [leafInput, ← WCT9.leafInputW_zero] at h
  unfold WCT9.leafInputW at h
  split at h
  · have hl : (bytesLE 16 pad ++ bytesLE 16 (WCT9.leafTweakW lay tree leaf hi) ++ ends.flatMap (bytesLE 16)).length =
        (bytesLE 16 (0 : Digest) ++ bytesLE 16 (WCT9.leafTweakW lay tree leaf 0) ++
          honest.flatMap (bytesLE 16)).length := by
      simp only [List.length_append, bytesLE_length, digest_list_bytes_length, hlen]
    have h' := Sampling.pad64_inj_of_length hl h
    obtain ⟨h1, hr⟩ := List.append_inj h' (by simp only [List.length_append, bytesLE_length])
    obtain ⟨hp, ht⟩ := List.append_inj h1 (by simp only [bytesLE_length])
    exact ⟨flatMap_bytes_injective hlen hr, (append64_inj (bytesLE_injective ht)).1, fun _ => bytesLE_injective hp⟩
  · rename_i h0
    obtain ⟨he, hh⟩ := listInput_lists (hdr := WCT9.leafTweakW lay tree leaf hi)
      (hdr' := WCT9.leafTweakW lay tree leaf 0) hlen hpos h
    exact ⟨he, (append64_inj hh).1, fun e => absurd e h0⟩
theorem leafHashW_extract (answers : Answers) (lay : Layer) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (ends honest : List Digest) (hlen : ends.length = honest.length) (hc : honest.length = chainCount lay)
    (reaches : evalWithAnswerFn answers (WCT9.leafHashW lay tree leaf pad hi ends) =
      evalWithAnswerFn answers (WCT9.lowerLeafHash lay tree leaf honest)) :
    (ends = honest ∧ hi = 0 ∧ (lay = 0 → pad = 0)) ∨
      (HashHitH answers (WCT9.lowerHigh lay.val leaf) (pad64 (leafInput lay tree leaf honest))
          (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)) ∧
        SameHeader (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)) (pad64 (leafInput lay tree leaf honest)) ∧
        .inl (.inr (pad64 (WCT9.leafInputW lay tree leaf pad hi ends))) ∈
          queried answers (WCT9.leafHashW lay tree leaf pad hi ends)) := by
  have hpos : 0 < honest.length := by rw [hc]; fin_cases lay <;> decide
  by_cases heq : pad64 (WCT9.leafInputW lay tree leaf pad hi ends) = pad64 (leafInput lay tree leaf honest)
  · exact Or.inl (leafInputW_parse hlen hpos heq)
  · right
    refine ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [WCT9.lowerLeafHash_eq] at reaches
      unfold WCT9.leafHashW WCT9.lowerHash at reaches
      rw [eval_halfHash, eval_halfHash] at reaches
      exact reaches
    · have hl : (pad64 (WCT9.leafInputW lay tree leaf pad hi ends)).length =
          (pad64 (leafInput lay tree leaf honest)).length :=
        pad64_length_congr (by
          rw [leafInputW_length]; unfold leafInput
          rw [SigGolfCandidate.T3.leafInput_length, SigGolfCandidate.T3.leafInput_length, hlen])
      have hll : (pad64 (leafInput lay tree leaf honest)).length = 704 ∨
          (pad64 (leafInput lay tree leaf honest)).length = 896 := by
        rw [leafInput_padded_length lay tree leaf honest hc]; split <;> simp
      refine ⟨hl, ?_⟩
      unfold hdrKey
      rw [if_pos (by rw [hl]; exact hll), if_pos hll, hdrBlock_leafInputW, hdrBlock_leafInput]
      unfold WCT9.leafTweakW leafTweak
      rw [SigGolfCandidate.T3M.Extract.bytesLE_header_words, SigGolfCandidate.T3M.Extract.bytesLE_header_words,
        List.take_left' (bytesLE_length 8 _), List.take_left' (bytesLE_length 8 _)]
    · unfold WCT9.leafHashW WCT9.lowerHash
      rw [queried_halfHash]
      exact List.mem_singleton_self _
end halfPath
end ClaudeWCT.W9.T3M.Extract
