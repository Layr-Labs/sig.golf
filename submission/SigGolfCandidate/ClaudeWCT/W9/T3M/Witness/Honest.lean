import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Encode
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.TopLayer
import SigGolfCandidate.ClaudeWCT.WCT9.Correctness
import SigGolfCandidate.ClaudeWCT.WCT9.Omit
import SigGolfCandidate.Choice.Witness

section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (chainP nodeHashP recoverLayerP chainP_zero_route nodeHashP_zero bytesLE_zero16)
open SphincsSecurity (bytesLE)
set_option linter.unusedSimpArgs false
@[simp] theorem Pads.zero_wctChain (k : WCT9.Coord) (t : Fin 6) : (0 : Pads).wctChain k t = (0, 0) := rfl
@[simp] theorem Pads.zero_wctChainHigh (k : WCT9.Coord) (t : Fin 6) : (0 : Pads).wctChainHigh k t = 0 := rfl
@[simp] theorem Pads.zero_wctMerkle (k : WCT9.Coord) (l : Fin 7) : (0 : Pads).wctMerkle k l = 0 := rfl
@[simp] theorem Pads.zero_wctMerkleHigh (k : WCT9.Coord) (l : Fin 7) : (0 : Pads).wctMerkleHigh k l = 0 := rfl
@[simp] theorem Pads.zero_wctLeaf (k : WCT9.Coord) : (0 : Pads).wctLeaf k = 0 := rfl
@[simp] theorem Pads.zero_chain' (lay : Layer) (i : Fin (chainCount lay)) : (0 : Pads).chain lay i = (0, 0) := rfl
@[simp] theorem Pads.zero_merkle' (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkle lay j = 0 := rfl
@[simp] theorem Pads.zero_chainHeader (lay : Layer) (i : Fin (chainCount lay)) :
    (0 : Pads).chainHeader lay i = 0 := rfl
@[simp] theorem Pads.zero_bc (lay : Layer) : (0 : Pads).bc lay = 0 := rfl
@[simp] theorem Pads.zero_bcRight : (0 : Pads).bcRight = 0 := rfl
@[simp] theorem Pads.zero_toT3 : (0 : Pads).toT3 = 0 := rfl
@[simp] theorem Pads.zero_merkleHigh (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkleHigh lay j = 0 := rfl
@[simp] theorem Pads.zero_topLeaf : (0 : Pads).topLeaf = 0 := rfl
@[simp] theorem Pads.zero_leafHigh (lay : Layer) : (0 : Pads).leafHigh lay = 0 := rfl
@[simp] theorem Pads.zero_bcHigh (lay : Layer) : (0 : Pads).bcHigh lay ^^^ 1 = 1 := by
  show (0 : BitVec 64) ^^^ 1 = 1; decide
/-- C3: the verifier chain with zero pads on a routed leaf is the chain of the current scheme. -/
theorem chainPW_zero_route (index : Nat) (lay : Layer) (i : Fin (chainCount lay))
    (digit : Nat) (value : Digest) (hindex : index < 2 ^ 31) :
    chainPW lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) 0 0 0 value =
    WCT9.chainW lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) value := by
  have hi := i.isLt
  have ht : (route index lay).2 < 2 ^ 31 := by fin_cases lay <;> simp [route, height] <;> omega
  have hl : (route index lay).1 < 4096 := by fin_cases lay <;> simp [route, height] <;> omega
  have hi64 : i.val < 64 := by fin_cases lay <;> simp [chainCount] at hi <;> omega
  have hm : maxDigit lay i.val ≤ 7 := by unfold maxDigit; split_ifs <;> decide
  unfold chainPW WCT9.chainW
  apply WCT9.foldlM_congr_of_mem
  intro s hs v
  have hs8 : s < 8 := by have := List.mem_range'_1.mp hs; omega
  simp only [SigGolfCandidate.T3M.chainInputP, chainInput, bytesLE_zero16,
    SigGolfCandidate.T3M.chainHeaderP_zero _ _ _ _ _ ht hl hi64 hs8]
theorem leafHashW_zero (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    WCT9.leafHashW lay tree leaf 0 0 ends = WCT9.lowerLeafHash lay tree leaf ends := rfl
theorem wctChainInputP_zero (index coord child t step : Nat) (value : Digest) :
    wctChainInputP index coord child t step 0 0 0 value = WCT9.chainInput index coord child t step value := by
  simp only [wctChainInputP, WCT9.chainInput, WCT9.ftsChainHeader, bytesLE_zero16]
@[simp] theorem wctChainP_zero (index coord child t start count : Nat) (value : Digest) :
    wctChainP index coord child t start count 0 0 0 value = WCT9.chain index coord child t start count value := by
  simp only [wctChainP, WCT9.chain, wctChainInputP_zero]
@[simp] theorem wctNodeHashP_zero (coord index heap : Nat) (left right : Digest) :
    wctNodeHashP coord index heap left 0 0 right = WCT9.wctNodeHash coord index heap left right := by
  simp only [wctNodeHashP, SigGolfCandidate.T3M.SecurityInputs.nodeInputPH_zero, WCT9.wctNodeHash,
    SigGolfCandidate.T3M.SecurityInputs.nodeInputP, SigGolfCandidate.T3M.SecurityInputs.block4, bytesLE_zero16,
    WCT9.wctNodeHeader]
theorem recoverCoordinateP_zero (sig : WCT9.Signature) (index : Nat) (output : HashOutput) (coord : WCT9.Coord)
    (prev : Digest × Digest) :
    recoverCoordinateP sig 0 index output coord prev = WCT9.recoverCoordinate sig index output coord prev := by
  simp only [recoverCoordinateP, WCT9.recoverCoordinate, Pads.zero_wctChain, Pads.zero_wctChainHigh,
    Pads.zero_wctMerkle, Pads.zero_wctMerkleHigh, Pads.zero_wctLeaf, wctChainP_zero,
    wctNodeHashP_zero]
theorem recoverFtsP_zero (sig : WCT9.Signature) (index : Nat) (output : HashOutput) :
    recoverFtsP sig 0 index output = WCT9.recoverFts sig index output := by
  unfold recoverFtsP WCT9.recoverFts WCT9.recoverFtsFrom
  simp only [recoverCoordinateP_zero]
  rfl
theorem shortHash_congr {x y : HashInput} (h : pad64 x = pad64 y) : shortHash x = shortHash y := by
  have hp : publicHash x = publicHash y := by
    unfold publicHash
    rw [h]
  unfold shortHash
  rw [hp]
theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32) :
    pad64 (encodingInput lay tree leaf root counter) = WCT9.pairEncodingInputP lay tree leaf root 0 counter 0 := by
  have h12 : bytesLE 12 (0 : BitVec 96) = List.replicate 12 0 := by decide
  unfold encodingInput WCT9.pairEncodingInputP pad64
  simp only [List.length_append, SphincsSecurity.bytesLE_length, bytesLE_zero16, h12, zero16, List.append_assoc,
    List.replicate_append_replicate]
theorem encodingHash_layerEncodingInputP_zero (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter 0 0 1) =
      ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter) := by
  cases msg with
  | forest root =>
      show WCT9.encodingHash lay (WCT9.pairEncodingInputP lay tree leaf root 0 counter 0) =
        WCT9.encodingHash lay (encodingInput lay tree leaf root counter)
      apply WCT9.encodingHash_congr
      have hlen : (WCT9.pairEncodingInputP lay tree leaf root 0 counter 0).length = 64 := by
        simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
      rw [pad64_encodingInput]
      simp only [pad64, hlen]
      simp
  | pair left right => rfl
theorem verificationHash_layerEncodingInputP_zero (lay : Layer) (hint : BitVec 64) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    ClaudeWCT.WCT9.verificationHash lay hint (layerEncodingInputP lay tree leaf msg counter 0 0 1) =
      ClaudeWCT.WCT9.verificationHash lay hint (WCT9.layerEncodingInput lay tree leaf msg counter) := by
  cases msg with
  | forest root =>
      show WCT9.verificationHash lay hint (WCT9.pairEncodingInputP lay tree leaf root 0 counter 0) =
        WCT9.verificationHash lay hint (encodingInput lay tree leaf root counter)
      apply WCT9.verificationHash_congr
      have hlen : (WCT9.pairEncodingInputP lay tree leaf root 0 counter 0).length = 64 := by
        simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
      rw [pad64_encodingInput]
      simp only [pad64, hlen]
      simp
  | pair left right => rfl
theorem recoverLayerPairP_zero (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hindex : index < 2 ^ 31) (hlay : lay ≠ 0) :
    recoverLayerPairP sig 0 index lay digits = WCT9.recoverLayerPair sig index lay digits := by
  have hv : lay.val ≠ 0 := fun e => hlay (Fin.ext e)
  simp only [recoverLayerPairP, WCT9.recoverLayerPair, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    chainPW_zero_route _ _ _ _ _ hindex, Pads.zero_merkle', Pads.zero_merkleHigh, Pads.zero_topLeaf,
    Pads.zero_leafHigh, leafHashW_zero, ← WCT9.lowerNodeHash_eqP hv]
private theorem mapM_congr_guard {α β : Type} {f g : α → M β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
      rw [List.mapM_cons, List.mapM_cons, h x (by simp),
        mapM_congr_guard l (fun y hy => h y (by simp [hy]))]
theorem recoverLayerPairGuardP_zero (sig : WCT9.Signature) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) (hindex : index < 2 ^ 31) (hlay : lay ≠ 0) :
    recoverLayerPairGuardP sig 0 index lay answer digits =
      WCT9.recoverLayerPairGuard sig index lay answer digits := by
  simp only [recoverLayerPairGuardP, WCT9.recoverLayerPairGuard, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    recoverLayerPairP_zero _ _ _ _ hindex hlay]
  unfold WCT9.lowerGuardedRun
  split_ifs
  · rfl
  · apply congrArg (fun p : M (List Digest) => p >>= fun _ => pure none)
    apply mapM_congr_guard
    intro i hi
    have hi' : i < chainCount lay := by
      have hb := WCT9.lowerFirstBad_le answer
      have := List.mem_range.mp hi
      have hc : 43 ≤ chainCount lay := by fin_cases lay <;> decide
      omega
    exact chainPW_zero_route index lay ⟨i, hi'⟩ _ _ hindex
theorem verifyTopP_zero (sig : WCT9.Signature) (index : Nat) (answer : Digest) (hindex : index < 2 ^ 31) :
    verifyTopP sig 0 index answer = WCT9.verifyTop sig index answer := by
  simp only [verifyTopP, WCT9.verifyTop, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    chainP_zero_route _ _ _ _ _ hindex, Pads.zero_merkle', Pads.zero_merkleHigh, ← WCT9.lowerNodeHash_eqP',
    Fin.val_zero, WCT9.lowerNodeHash_top, Pads.zero_topLeaf, Pads.zero_leafHigh, leafHashW_zero,
    WCT9.lowerLeafHash_top]
theorem verifyLayersBCP_zero (w : WCT9.Witness) (index : Nat) (hindex : index < 2 ^ 31) : ∀ n, n ≤ 4 → ∀ msg,
    verifyLayersBCP w 0 index n msg = WCT9.verifyLayersBC w index n msg := by
  intro n
  induction n with
  | zero => intro _ msg; rfl
  | succ n ih =>
      intro hn4 msg
      by_cases hn : n = 0
      · subst hn
        simp only [verifyLayersBCP, WCT9.verifyLayersBC, Pads.zero_bc, Pads.zero_bcRight, Pads.zero_bcHigh,
          verificationHash_layerEncodingInputP_zero, verifyTopP_zero _ _ _ hindex, ↓reduceIte]
      · have hl : (Fin.ofNat 4 n : Layer) ≠ 0 := by
          intro h
          have h' := congrArg Fin.val h
          simp only [Fin.val_ofNat, Fin.val_zero] at h'
          omega
        simp only [verifyLayersBCP, WCT9.verifyLayersBC, Pads.zero_bc, Pads.zero_bcRight, Pads.zero_bcHigh,
          verificationHash_layerEncodingInputP_zero, recoverLayerPairGuardP_zero _ _ _ _ _ hindex hl,
          ih (by omega), hn, ↓reduceIte]
        rfl
theorem verifyPads_zero (m : Message) (pk : Digest) (w : WCT9.Witness) :
    verifyPads m pk w 0 = WCT9.Rev3.verify m pk w := by
  unfold verifyPads verifyPadsTail WCT9.Rev3.verify WCT9.verifyWith
  simp only [recoverFtsP_zero, verifyLayersBCP_zero _ _ (WCT9.digestIndex_lt _) 4 le_rfl]
  rfl
theorem layerPairP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat) :
    layerPairP w (WCT9.digestIndex N) lay digits =
      recoverLayerPairP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) lay digits := by
  unfold layerPairP recoverLayerPairP
  have hm : ∀ j : Fin (height lay - 1),
      (padDecP N w).merkle lay (Fin.castLE (Nat.sub_le _ _) j) =
        wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val := by
    intro j
    simp only [padDecP, Fin.val_castLE]
    rw [if_pos (Or.inl (by omega))]
  have hmh : ∀ j : Fin (height lay - 1),
      (padDecP N w).merkleHigh lay (Fin.castLE (Nat.sub_le _ _) j) =
        wmerkleHigh w lay (route (WCT9.digestIndex N) lay).1 j.val := by
    intro j
    simp only [padDecP, Fin.val_castLE]
    rw [if_pos (by omega)]
  simp only [hm, hmh, valueP_dec]
  rfl
theorem layerGuardedPairP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (answer : Digest)
    (digits : List Nat) :
    layerGuardedPairP w (WCT9.digestIndex N) lay answer digits =
      recoverLayerPairGuardP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) lay answer digits := by
  unfold layerGuardedPairP recoverLayerPairGuardP layerChainP
  rw [layerPairP_dec N w]
  simp only [valueP_dec]
  rfl
theorem topLayerP_dec (N : HashOutput) (w : WBytes) (answer : Digest) :
    topLayerP w (WCT9.digestIndex N) answer =
      verifyTopP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) answer := by
  unfold topLayerP verifyTopP topChainP topFinishP
  simp only [valueP_dec]
  simp only [padDecP, witDecP, Fin.val_zero, or_true, ↓reduceIte]
theorem padDecP_bcHigh (N : HashOutput) (w : WBytes) (lay : Layer) :
    (padDecP N w).bcHigh lay ^^^ 1 = wbcHigh w (WCT9.digestIndex N) lay := by
  simp only [padDecP, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
theorem layersBC_dec (N : HashOutput) (w : WBytes) : ∀ n msg,
    layersBC w (WCT9.digestIndex N) n msg =
      verifyLayersBCP (witDecP N w) (padDecP N w) (WCT9.digestIndex N) n msg := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
      intro msg
      unfold layersBC verifyLayersBCP
      simp only [padDecP_bcHigh]
      by_cases hn : n = 0
      · subst n
        simp only [if_true, topLayerP_dec N w]
        rfl
      · simp only [hn, if_false, layerGuardedPairP_dec N w, ih]
        rfl
theorem wctStep_none (w : WBytes) (N : HashOutput) (coord : WCT9.Coord) : wctStep w N none coord = pure none := rfl
theorem foldlM_wctStep_none (w : WBytes) (N : HashOutput) :
    ∀ l : List WCT9.Coord, l.foldlM (wctStep w N) none = pure none
  | [] => rfl
  | k :: ks => by rw [List.foldlM_cons, wctStep_none, pure_bind, foldlM_wctStep_none w N ks]
theorem wctCoordP_dec (N : HashOutput) (w : WBytes) (index : Nat) (coord : WCT9.Coord) (prev : Digest × Digest) :
    wctCoordP w index coord (WCT9.child N coord) (WCT9.rank N coord) prev =
      recoverCoordinateP (witDecP N w).signature (padDecP N w) index N coord prev := by
  unfold wctCoordP recoverCoordinateP
  have hm : ∀ level : Fin 5,
      (padDecP N w).wctMerkle coord (Fin.castLE (by decide) level) =
        wmpad w coord.val (WCT9.child N coord).val level.val := by
    intro level
    simp only [padDecP, Fin.val_castLE]
    rw [if_pos (Or.inl level.isLt)]
  have hh : ∀ level : Fin 5,
      (padDecP N w).wctMerkleHigh coord (Fin.castLE (by decide) level) =
        wmhpad w coord.val (WCT9.child N coord).val level.val := by
    intro level
    simp only [padDecP, Fin.val_castLE]
  simp only [hm, hh]
  rfl
/-- The decoded pads of coordinate 0 are the free witness slots read by `wctP`. -/
theorem wmpad_five (w : WBytes) (k c : Nat) : wmpad w k c 5 = wdig w (regionBase k + 864) := by
  unfold wmpad authPadOff; rw [authBase_five]
theorem padDecP_start (N : HashOutput) (w : WBytes) : (padDecP N w).start = wctStart w := by
  simp [Pads.start, wctStart, padDecP, wmpad_five]
theorem foldlM_wctStep_ok (w : WBytes) (N : HashOutput) (hok : ∀ k, fieldOk N k = true) :
    ∀ (l : List WCT9.Coord) (acc : List (Digest × Digest)),
      l.foldlM (wctStep w N) (some acc) =
        some <$> l.foldlM (fun (pairs : List (Digest × Digest)) k => do
          let pair ← wctCoordP w (WCT9.digestIndex N) k (WCT9.child N k) (WCT9.rank N k)
            (WCT9.prevPair (wctStart w) pairs)
          pure (pairs ++ [pair])) acc
  | [], acc => by simp
  | k :: ks, acc => by
      rw [List.foldlM_cons, List.foldlM_cons]
      have hs : wctStep w N (some acc) k =
          (fun pair => some (acc ++ [pair])) <$>
            wctCoordP w (WCT9.digestIndex N) k (WCT9.child N k) (WCT9.rank N k) (WCT9.prevPair (wctStart w) acc) := by
        simp only [wctStep, hok k, Bool.not_true, Bool.false_eq_true, if_false, map_eq_bind_pure_comp]
        rfl
      rw [hs, bind_map_left, map_bind, bind_assoc]
      congr 1; funext pair
      rw [foldlM_wctStep_ok w N hok ks (acc ++ [pair]), pure_bind]
theorem fieldOk_of_admissible {N : HashOutput} (h : WCT9.admissible N = true) (k : WCT9.Coord) :
    fieldOk N k = true := by
  have := ((WCT9.admissible_iff N).1 h).2 k
  exact decide_eq_true this
theorem gateOk_of_admissible {N : HashOutput} (h : WCT9.admissible N = true) : gateOk N = true := by
  unfold gateOk
  apply decide_eq_true
  simpa only [WCT9.gateLimit] using ((WCT9.admissible_iff N).1 h).1
theorem admissible_of_ok {N : HashOutput} (hg : gateOk N = true) (hf : ∀ k, fieldOk N k = true) :
    WCT9.admissible N = true := by
  unfold gateOk at hg
  have hgate := of_decide_eq_true hg
  rw [WCT9.admissible_iff]
  refine ⟨by simpa only [WCT9.gateLimit] using hgate, fun k => ?_⟩
  have := hf k
  exact of_decide_eq_true this
theorem wctP_shaped (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    wctP w N = some <$> recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N := by
  unfold wctP recoverFtsP
  rw [foldlM_wctStep_ok w N (fieldOk_of_admissible h) _ [], bind_map_left, map_bind, padDecP_start]
  simp only [wctCoordP_dec, map_pure]
theorem foldlM_wctStep_bad (w : WBytes) (N : HashOutput) :
    ∀ (l : List WCT9.Coord) (st : Option (List (Digest × Digest))),
    (∃ k ∈ l, fieldOk N k = false) → ∀ r ∈ support (l.foldlM (wctStep w N) st), r = none := by
  intro l
  induction l with
  | nil => intro st h; obtain ⟨k, hk, -⟩ := h; simp at hk
  | cons k ks ih =>
      intro st h r hr
      rw [List.foldlM_cons, mem_support_bind_iff] at hr
      obtain ⟨s, hs, hr⟩ := hr
      by_cases hk : fieldOk N k = false
      · have h0 : wctStep w N st k = pure none := by
          rcases st with _ | roots
          · rfl
          · simp only [wctStep, hk, Bool.not_false, if_true]
        rw [h0] at hs
        simp only [support_pure, Set.mem_singleton_iff] at hs
        subst hs
        rw [foldlM_wctStep_none] at hr
        simpa using hr
      · obtain ⟨k', hk', hbad⟩ := h
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact absurd hbad hk
        · exact ih s ⟨k', hk', hbad⟩ r hr
theorem wctP_bad (w : WBytes) (N : HashOutput) (h : ∃ k, fieldOk N k = false) :
    ∀ r ∈ support (wctP w N), r = none := by
  intro r hr
  unfold wctP at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨s, hs, hr⟩ := hr
  obtain ⟨k, hk⟩ := h
  have := foldlM_wctStep_bad w N _ _ ⟨k, List.mem_finRange k, hk⟩ s hs
  subst this
  simpa using hr
theorem verifyP_eq_tail (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w = ((do
      let some N ← digestP m w | pure false
      verifyTailP pk w N) : M Bool) := rfl
theorem verifyTailP_shaped (pk : Digest) (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    verifyTailP pk w N = verifyPadsTail pk N (witDecP N w) (padDecP N w) := by
  unfold verifyTailP verifyPadsTail
  have hg := gateOk_of_admissible h
  have ha : WCT9.admissible N = true := h
  simp only [hg, ha, Bool.not_true, Bool.false_eq_true, if_false]
  rw [wctP_shaped N w h, bind_map_left]
  refine bind_congr (fun root => ?_)
  dsimp only
  rw [layersBC_dec]
  rfl
theorem rejectTail_false (w : WBytes) (N : HashOutput) : ∀ b ∈ support (rejectTail w N), b = false := by
  intro b hb
  unfold rejectTail at hb
  split at hb
  · simpa using hb
  · rw [support_map] at hb
    obtain ⟨_, _, rfl⟩ := hb
    rfl
theorem verifyP_normal (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w =
      if (wdc w).toNat ≥ WCT9.digestVerifyWindow then pure false else (do
        let N ← digest (wrho w) m (wdc w)
        if Shaped N w then verifyPadsTail pk N (witDecP N w) (padDecP N w) else rejectTail w N) := by
  rw [verifyP_eq_tail]
  unfold digestP
  split_ifs with h
  · simp
  · rw [bind_map_left]
    refine bind_congr (fun N => ?_)
    dsimp only
    split_ifs with hS
    · exact verifyTailP_shaped pk N w hS
    · unfold verifyTailP rejectTail
      by_cases hg : gateOk N = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, if_false]
        have hbad : ∃ k, fieldOk N k = false := by
          by_contra hall
          push Not at hall
          exact hS (admissible_of_ok hg fun k => by simpa using hall k)
        rw [map_eq_bind_pure_comp]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro r hr
        rw [wctP_bad w N hbad r hr]
        rfl
      · simp [hg]
end ClaudeWCT.W9.T3M
end
section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff zeros
  layerBytes layerBytes_length layerBytes_merkle layerBytes_chain
  window window_append_left window_append_right window_flatMap window_flatMap_const window_full window_zeros
  window_take readDigest_zeros readLE_bytesLE_32 extract_readLE readLE_append)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
theorem zeros_len (n : Nat) : (zeros n).length = n := List.length_replicate ..
theorem ite_slot_length (p : Prop) [Decidable p] (d : Digest) :
    (if p then bytesLE 16 d else zeros 16).length = 16 := by
  split <;> simp [zeros, bytesLE_length]
theorem headerBytes_length (N : HashOutput) (w : WCT9.Witness) : (headerBytes N w).length = 176 := by
  simp only [headerBytes, List.length_append, ite_slot_length, zeros_len, bytesLE_length]
theorem merkleBytes_length (c : Nat) (op : WCT9.Opening) : (merkleBytes c op).length = 320 := by
  simp [merkleBytes]
theorem chainBytes_length (op : WCT9.Opening) : (chainBytes op).length = 320 := by
  simp [chainBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
theorem leafBytes_length' (op : WCT9.Opening) (pad : List UInt8) :
    (leafBytes op pad).length = 112 + pad.length := by
  simp [leafBytes, zeros, bytesLE_length, List.length_flatMap, List.sum_replicate]
  omega
theorem leafBytes_length (op : WCT9.Opening) (pad : List UInt8) (h : pad.length = 16) :
    (leafBytes op pad).length = 128 := by
  rw [leafBytes_length', h]
theorem topBlockBytes_length (c : Nat) (op : WCT9.Opening) (pad : List UInt8) (h : pad.length = 16) :
    (topBlockBytes c op pad).length = 64 := by
  simp only [topBlockBytes, List.length_append, ite_slot_length, zeros_len, h]
theorem regionBytes_length (c : Nat) (op : WCT9.Opening) (padL padZ : List UInt8) (hL : padL.length = 16)
    (hZ : padZ.length = 16) : (regionBytes c op padL padZ).length = 896 := by
  simp only [regionBytes, List.length_append, merkleBytes_length, chainBytes_length, leafBytes_length _ _ hL,
    topBlockBytes_length _ _ _ hZ, zeros, List.length_replicate]
theorem prevSibL_length (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : (prevSibL N sig k).length = 16 := by
  unfold prevSibL; split
  · simp [zeros]
  · exact ite_slot_length _ _
theorem prevSibZ_length (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : (prevSibZ N sig k).length = 16 := by
  unfold prevSibZ; split
  · simp [zeros]
  · exact ite_slot_length _ _
def regionLen (k : WCT9.Coord) : Nat := if k.val = 0 then 912 else 896
/-- One cell of `wctBytes`: the region of coordinate `k`, followed by 16 zero bytes for `k = 0`. -/
def regionCell (N : HashOutput) (sig : WCT9.Signature) (k : WCT9.Coord) : List UInt8 :=
  regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val) ++
    (if k.val = 0 then zeros 16 else [])
theorem wctBytes_eq (N : HashOutput) (sig : WCT9.Signature) :
    wctBytes N sig = (List.finRange 9).reverse.flatMap (regionCell N sig) := rfl
theorem regionCell_length (N : HashOutput) (sig : WCT9.Signature) (k : WCT9.Coord) :
    (regionCell N sig k).length = regionLen k := by
  unfold regionCell regionLen
  rw [List.length_append, regionBytes_length _ _ _ _ (prevSibL_length N sig _) (prevSibZ_length N sig _)]
  split <;> simp [zeros]
theorem wct_prefix (k : WCT9.Coord) :
    ((((List.finRange 9).reverse).take (8 - k.val)).map regionLen).sum = 896 * (8 - k.val) := by
  fin_cases k <;> decide
theorem wctBytes_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytes N sig).length = 8080 := by
  rw [wctBytes_eq, List.length_flatMap, List.map_congr_left (fun k _ => regionCell_length N sig k)]
  decide
theorem height_pos' (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem lowerPathBytes_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (lowerPathBytes lay leaf ls ctr).length = 16 * pathSlots lay := by
  simp [lowerPathBytes]
theorem topPathBytes_length {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) :
    (topPathBytes leaf ls).length = 16 * pathSlots lay := by
  simp [topPathBytes]
theorem layerRegion_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegion N w lay).length = 16 * pathSlots lay + 64 * chainCount lay := by
  unfold layerRegion; split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    rw [List.length_append, topPathBytes_length, List.length_drop, layerBytes_length]
    omega
  · rw [List.length_append, lowerPathBytes_length, List.length_drop, layerBytes_length]
    omega
theorem endpointBytes_length (sig : WCT9.Signature) (lay : Layer) :
    (endpointBytes sig lay).length = 16 * chainCount lay := by
  simp [endpointBytes, List.length_flatMap, bytesLE_length, List.sum_replicate, Nat.mul_comm]
def leafBufferLen (lay : Layer) : Nat := if lay = 0 then 912 else 736
theorem leafBufferBytes_length (sig : WCT9.Signature) (lay : Layer) :
    (leafBufferBytes sig lay).length = leafBufferLen lay := by
  fin_cases lay <;> simp [leafBufferBytes, leafBufferLen, endpointBytes_length, zeros, chainCount]
theorem leafBuffersBytes_length (sig : WCT9.Signature) : (leafBuffersBytes sig).length = 3120 := by
  simp only [leafBuffersBytes, List.length_flatMap, leafBufferBytes_length]
  decide
theorem tailBytes_length (w : WCT9.Witness) : (tailBytes w).length = 32 := by
  simp [tailBytes, zeros, bytesLE_length]
theorem layers_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegion N w)).length = 13424 := by
  simp only [List.length_flatMap, layerRegion_length]
  decide
theorem witList_length_eq (N : HashOutput) (w : WCT9.Witness) : (witList N w).length = 24832 := by
  unfold witList
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, leafBuffersBytes_length,
    tailBytes_length]
theorem extract_readLE_lt (L : List UInt8) (n : Nat) (hlt : readLE L < 2 ^ (8 * n)) (off k : Nat) :
    (BitVec.ofNat (8 * n) (readLE L)).extractLsb' (8 * off) (8 * k) =
      BitVec.ofNat (8 * k) (readLE ((L.drop off).take k)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.shiftRight_eq_div_pow, show 2 ^ (8 * off) = 256 ^ off by rw [pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop,
    show 2 ^ (8 * k) = 256 ^ k by rw [pow_mul]; norm_num, SigGolfCandidate.T3M.readLE_take]
  rw [Nat.mod_eq_of_lt]
  have := SigGolfCandidate.T3M.readLE_lt ((L.drop off).take k)
  calc readLE ((L.drop off).take k) < 256 ^ ((L.drop off).take k).length := this
    _ ≤ 256 ^ k := Nat.pow_le_pow_right (by norm_num) (by simp)
/-- The serialized list keeps 4 trailing zero bytes after the 32-bit digest counter (the expand
machine still writes whole words); the witness is its first `wsize = 24828` bytes. -/
theorem witList_readLE_lt (N : HashOutput) (w : WCT9.Witness) : readLE (witList N w) < 2 ^ (8 * 24828) := by
  have hsplit : witList N w = ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)) ++
      zeros 4 := by
    simp only [witList, tailBytes, List.append_assoc]
  have hlen : ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)).length =
      24828 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, leafBuffersBytes_length,
      bytesLE_length, zeros, List.length_replicate]
  have hz : readLE (zeros 4) = 0 := by decide
  have h256 : ∀ n : Nat, (256 : Nat) ^ n = 2 ^ (8 * n) := fun n => by rw [pow_mul]; norm_num
  rw [hsplit, readLE_append, hz, Nat.mul_zero, Nat.add_zero, ← h256, ← hlen]
  exact SigGolfCandidate.T3M.readLE_lt _
theorem wdig_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wdig (witEnc N w) off = readDigest (window (witList N w) off 16) := by
  unfold wdig witEnc readDigest window
  exact extract_readLE_lt (witList N w) 24828 (witList_readLE_lt N w) off 16
theorem wle32_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wle32 (witEnc N w) off = BitVec.ofNat 32 (readLE (window (witList N w) off 4)) := by
  unfold wle32 witEnc window
  exact extract_readLE_lt (witList N w) 24828 (witList_readLE_lt N w) off 4
theorem extractLsb'_extractLsb'_add {n : Nat} (x : BitVec n) (a b c : Nat) (h : b + c ≤ 128) :
    (x.extractLsb' a 128).extractLsb' b c = x.extractLsb' (a + b) c := by
  ext k hk
  simp [BitVec.getElem_extractLsb']
  rw [show a + b + k = a + (b + k) by omega]
  simp; omega
/-- The high word of a witness digest is the 64-bit witness word 8 bytes further. -/
theorem wdig_high (x : WBytes) (off : Nat) : (wdig x off).extractLsb' 64 64 = x.extractLsb' (8 * (off + 8)) 64 := by
  unfold wdig
  rw [extractLsb'_extractLsb'_add _ _ _ _ (by omega), show 8 * off + 64 = 8 * (off + 8) by omega]
theorem wword_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    (witEnc N w).extractLsb' (8 * off) 64 = BitVec.ofNat 64 (readLE (window (witList N w) off 8)) := by
  unfold witEnc window
  exact extract_readLE_lt (witList N w) 24828 (witList_readLE_lt N w) off 8
theorem witList_split (N : HashOutput) (w : WCT9.Witness) :
    witList N w = ((headerBytes N w ++ wctBytes N w.signature) ++ (List.finRange 4).flatMap (layerRegion N w)) ++
      (leafBuffersBytes w.signature ++ tailBytes w) := by simp only [witList, List.append_assoc]
section header
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_header (off n : Nat) (h : off + n ≤ 176) :
    window (witList N w) off n = window (headerBytes N w) off n := by
  rw [witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_left _ _ _ _ (by rw [headerBytes_length]; omega)]
/-- The header as a slot, 16 zero bytes, the L3 counter, 68 zero bytes, the selector, 32 zero bytes, the R9 slot and 16 zero bytes. -/
theorem headerBytes_eq : headerBytes N w =
    (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
      ((zeros 8 ++ bytesLE 8 (1 : BitVec 64)) ++ (bytesLE 4 (w.counters 3) ++ ((zeros 68 ++ (bytesLE 8 w.topHint ++ zeros 32)) ++
        ((if (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
          zeros 16)))) := by
  simp only [headerBytes, List.append_assoc]
theorem win_header_mid (off n : Nat) (h0 : 36 ≤ off) (h : off + n ≤ 104) :
    window (witList N w) off n = zeros n := by
  rw [win_header N w off n (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
    window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]; omega)]
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]; omega)]
  exact window_zeros _ _ _ (by simp [bytesLE_length, zeros]; omega)
theorem wctr3_witEnc : wle32 (witEnc N w) 32 = w.counters 3 := by
  rw [wle32_witEnc, win_header _ _ _ _ (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 32 - 16 - (zeros 8 ++ bytesLE 8 (1 : BitVec 64)).length = 0 by simp [zeros, bytesLE_length],
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wpad3_witEnc : (witEnc N w).extractLsb' (8 * 36) 96 = 0 := by
  have h := extract_readLE_lt (witList N w) 24828 (witList_readLE_lt N w) 36 12
  unfold witEnc
  rw [show (96 : Nat) = 8 * 12 from rfl, h, show ((witList N w).drop 36).take 12 = window (witList N w) 36 12 from rfl,
    win_header_mid _ _ _ _ le_rfl (by omega)]
  rfl
theorem wright3_witEnc : wdig (witEnc N w) 48 = 0 := by
  rw [wdig_witEnc, win_header_mid _ _ _ _ (by omega) (by omega), readDigest_zeros]
/-- C2/C3 (FULL): the L3 row tweak's high word (witness 24) is LE64 1. -/
theorem win_header_hi : window (witList N w) 24 8 = bytesLE 8 (1 : BitVec 64) := by
  rw [win_header _ _ _ _ (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
    window_append_right _ _ _ _ (by simp [zeros]),
    show 24 - 16 - (zeros 8).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
end header
section tail
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_tail (off n : Nat) (h : off + n ≤ 32) :
    window (witList N w) (24800 + off) n = window (tailBytes w) off n := by
  rw [witList_split, window_append_right _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_right _ _ _ _ (by rw [leafBuffersBytes_length]; omega), leafBuffersBytes_length]
  exact congrArg (fun k : Nat => window (tailBytes w) k n)
    (show 24800 + off - (176 + 8080 + 13424) - 3120 = off by omega)
theorem wrho_witEnc : wrho (witEnc N w) = w.signature.rho := by
  unfold wrho rhoOff
  rw [wdig_witEnc, show (24800 : Nat) = 24800 + 0 from rfl, win_tail _ _ _ _ (by omega)]
  unfold tailBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]), window_full _ _ (bytesLE_length _ _),
    Correctness.readDigest_bytesLE]
theorem tail_counter_window : window (tailBytes w) 24 8 = bytesLE 4 w.digestCounter ++ zeros 4 := by
  rw [show tailBytes w = (bytesLE 16 w.signature.rho ++ zeros 8) ++ (bytesLE 4 w.digestCounter ++ zeros 4) by
    simp only [tailBytes, List.append_assoc]]
  rw [window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 24 - (bytesLE 16 w.signature.rho ++ zeros 8).length = 0 by simp [bytesLE_length, zeros]]
  exact window_full _ _ (by simp [bytesLE_length, zeros])
theorem wdc_witEnc : wdc (witEnc N w) = w.digestCounter := by
  unfold wdc dcOff
  rw [wle32_witEnc, show (24824 : Nat) = 24800 + 24 from rfl, win_tail _ _ _ _ (by omega)]
  have h : window (tailBytes w) 24 4 = window (window (tailBytes w) 24 8) 0 4 := by
    unfold window; rw [List.drop_zero, List.take_take, Nat.min_eq_left (by omega)]
  rw [h, tail_counter_window, window_append_left _ _ _ _ (by simp [bytesLE_length]),
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wdcWord_witEnc : (wdcWord (witEnc N w)).toNat = w.digestCounter.toNat := by
  unfold wdcWord witEnc dcOff
  rw [show (64 : Nat) = 8 * 8 from rfl, extract_readLE_lt (witList N w) 24828 (witList_readLE_lt N w) 24824 8,
    show ((witList N w).drop 24824).take 8 = window (witList N w) (24800 + 24) 8 from rfl,
    win_tail _ _ _ _ (by omega), tail_counter_window, readLE_append, bytesLE_length,
    Correctness.readLE_bytesLE]
  have hz : readLE (zeros 4) = 0 := by decide
  rw [hz, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans w.digestCounter.isLt (by decide))
end tail
theorem layerBase_ge (lay : Layer) : 8256 ≤ layerBase lay := by
  fin_cases lay <;> simp [layerBase]
theorem layerEnd_le (lay : Layer) : layerBase lay + (16 * pathSlots lay + 64 * chainCount lay) ≤ 21680 := by
  fin_cases lay <;> decide
theorem layer_prefix (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (((List.finRange 4).take lay.val).map fun l => (layerRegion N w l).length).sum = layerBase lay - 8256 := by
  simp only [layerRegion_length]
  fin_cases lay <;> decide
theorem win_layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (j m : Nat)
    (hjm : j + m ≤ 16 * pathSlots lay + 64 * chainCount lay) :
    window (witList N w) (layerBase lay + j) m = window (layerRegion N w lay) j m := by
  have hb := layerBase_ge lay
  have he := layerEnd_le lay
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := window_flatMap (List.finRange 4) (layerRegion N w) lay.val (by simp) j m
    (by rw [hlen, layerRegion_length]; omega)
  rw [layer_prefix N w lay, hlen] at key
  rw [witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_right _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length]
  rw [show layerBase lay + j - (176 + 8080) = (layerBase lay - 8256) + j by omega, key]
theorem win_chain (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (i : Fin (chainCount lay)) (o : Nat)
    (ho : o + 16 ≤ 64) :
    window (witList N w) (chainBlock lay i.val + o) 16 =
      window (zeros 48 ++ bytesLE 16 ((w.signature.layers lay).values i)) o 16 := by
  have hi := i.isLt
  unfold chainBlock
  rw [show layerBase lay + 16 * pathSlots lay + 64 * (chainCount lay - 1 - i.val) + o =
      layerBase lay + (16 * pathSlots lay + (64 * (chainCount lay - 1 - i.val) + o)) by omega,
    win_layerRegion _ _ _ _ _ (by omega)]
  unfold layerRegion
  split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    rw [window_append_right _ _ _ _ (by rw [topPathBytes_length]; omega), topPathBytes_length,
      Nat.add_sub_cancel_left]
    unfold window
    rw [List.drop_drop, show 64 * height 0 + (64 * (chainCount 0 - 1 - i.val) + o) =
      64 * height 0 + 64 * (chainCount 0 - 1 - i.val) + o by omega]
    exact layerBytes_chain _ _ _ i o ho
  · rw [window_append_right _ _ _ _ (by rw [lowerPathBytes_length]; omega), lowerPathBytes_length,
      Nat.add_sub_cancel_left]
    unfold window
    rw [List.drop_drop, show 64 * height lay + (64 * (chainCount lay - 1 - i.val) + o) =
      64 * height lay + 64 * (chainCount lay - 1 - i.val) + o by omega]
    exact layerBytes_chain _ _ _ i o ho
section t3
variable (N : HashOutput) (w : WCT9.Witness)
theorem wvalue_witEnc (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (witEnc N w) lay i.val = (w.signature.layers lay).values i := by
  unfold wvalue
  rw [wdig_witEnc, win_chain _ _ _ _ _ (by omega), window_append_right _ _ _ _ (by simp [zeros]),
    show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _),
    Correctness.readDigest_bytesLE]
theorem wchainPads_witEnc (lay : Layer) (i : Fin (chainCount lay)) : wchainPads (witEnc N w) lay i.val = (0, 0) := by
  unfold wchainPads
  rw [wdig_witEnc, wdig_witEnc, show chainBlock lay i.val = chainBlock lay i.val + 0 from rfl,
    win_chain _ _ _ _ _ (by omega), Nat.add_zero, win_chain _ _ _ _ _ (by omega),
    window_append_left _ _ _ _ (by simp [zeros]), window_append_left _ _ _ _ (by simp [zeros]),
    window_zeros _ _ _ (by omega), window_zeros _ _ _ (by omega), readDigest_zeros]
theorem wchainHeaderPad_witEnc (lay : Layer) (i : Fin (chainCount lay)) :
    wchainHeaderPad (witEnc N w) lay i.val = 0 := by
  unfold wchainHeaderPad
  rw [wdig_witEnc, win_chain _ _ _ _ _ (by omega), window_append_left _ _ _ _ (by simp [zeros]),
    window_zeros _ _ _ (by omega), readDigest_zeros]
  rfl
end t3
theorem lower_sib_bound (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, lowerSibSlot lay leaf j + 16 ≤ 16 * pathSlots lay := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_pad_bound (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, 16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * pathSlots lay := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_sib_disjoint (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      lowerSibSlot lay leaf j + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ lowerSibSlot lay leaf j := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_pad_disjoint (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD j 0 + 32 + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lower_pad_pad_disjoint (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j' 0 + 32 ∨
        16 * (lowerPlan lay leaf).getD j' 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
/-- C2/C3 (FULL): the high tweak word of a lower fold window (`16 P_j + 24`, levels below the root window) is clear
of every sibling slot. -/
theorem lower_hp_sib (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay - 1, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD j 0 + 32 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 24 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
/-- ... and of the root window's row tweak high word and counter (`16 P_r + 24 .. 16 P_r + 36`); so is its Z pad. -/
theorem lower_hp_root (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j < height lay - 1,
      (16 * (lowerPlan lay leaf).getD j 0 + 32 ≤ 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 24 ∨
        16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 36 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 24) ∧
      (16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 24 ∨
        16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 36 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32) := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
/-- The root window's row tweak high word is clear of every sibling slot. -/
theorem lower_hi_sib (lay : Layer) (hlay : lay.val ≠ 0) :
    ∀ leaf < 2 ^ height lay, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 32 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 24 := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem lowerSlots_ok (lay : Layer) (hlay : lay.val ≠ 0) :
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, lowerSibSlot lay leaf j + 16 ≤ 16 * pathSlots lay) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, 16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * pathSlots lay) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      lowerSibSlot lay leaf j + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ lowerSibSlot lay leaf j) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay,
      16 * (lowerPlan lay leaf).getD j 0 + 32 + 16 ≤ lowerSibSlot lay leaf j' ∨
        lowerSibSlot lay leaf j' + 16 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32) ∧
    (∀ leaf < 2 ^ height lay, ∀ j < height lay, ∀ j' < height lay, j ≠ j' →
      16 * (lowerPlan lay leaf).getD j 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j' 0 + 32 ∨
        16 * (lowerPlan lay leaf).getD j' 0 + 48 ≤ 16 * (lowerPlan lay leaf).getD j 0 + 32) :=
  ⟨lower_sib_bound lay hlay, lower_pad_bound lay hlay, lower_sib_disjoint lay hlay, lower_pad_disjoint lay hlay,
    lower_pad_pad_disjoint lay hlay⟩
theorem window_map_range (f : Nat → UInt8) (n off m : Nat) (h : off + m ≤ n) :
    window ((List.range n).map f) off m = (List.range m).map (fun i => f (off + i)) := by
  unfold window
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
theorem map_range_getD (L : List UInt8) (n : Nat) (h : L.length = n) :
    (List.range n).map (fun i => L.getD i 0) = L := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]
section lowerPath
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay)
  (ls : LayerSignature lay) (ctr : BitVec 32)
include hlay hleaf
theorem lowerPathByte_sib (j : Fin (height lay)) {i : Nat} (hi : i < 16) :
    lowerPathByte lay leaf ls ctr (lowerSibSlot lay leaf j.val + i) = (bytesLE 16 (ls.path j)).getD i 0 := by
  unfold lowerPathByte
  generalize hf : (List.finRange (height lay)).find? _ = r
  rcases r with _ | j'
  · exfalso
    have := List.find?_eq_none.mp hf j (List.mem_finRange j)
    simp only [decide_eq_true_eq, not_and, not_lt] at this
    have := this (by omega)
    omega
  · have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have hjj : j' = j := by
      by_contra hne
      have hd := lower_sib_disjoint lay hlay leaf hleaf j'.val j'.isLt j.val j.isLt (fun e => hne (Fin.ext e))
      omega
    subst hjj
    simp only [Nat.add_sub_cancel_left]
omit hlay hleaf in
theorem lowerPathByte_free {p : Nat} (hp : ∀ j : Fin (height lay), p < lowerSibSlot lay leaf j.val ∨
    lowerSibSlot lay leaf j.val + 16 ≤ p) :
    lowerPathByte lay leaf ls ctr p = if lowerCtrSlot lay leaf ≤ p ∧ p < lowerCtrSlot lay leaf + 4 then
      (bytesLE 4 ctr).getD (p - lowerCtrSlot lay leaf) 0
    else if lowerHiSlot lay leaf ≤ p ∧ p < lowerHiSlot lay leaf + 8 then
      (bytesLE 8 (1 : BitVec 64)).getD (p - lowerHiSlot lay leaf) 0 else 0 := by
  unfold lowerPathByte
  rw [List.find?_eq_none.mpr (fun j _ => by
    have := hp j
    simp only [decide_eq_true_eq, not_and, not_lt]
    omega)]
theorem lowerPath_sib (j : Fin (height lay)) :
    window (lowerPathBytes lay leaf ls ctr) (lowerSibSlot lay leaf j.val) 16 = bytesLE 16 (ls.path j) := by
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (lower_sib_bound lay hlay leaf hleaf j.val j.isLt),
    List.map_congr_left (fun i hi => lowerPathByte_sib hlay hleaf ls ctr j (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem lowerPath_pad {j : Nat} (hj : j + 1 < height lay) :
    window (lowerPathBytes lay leaf ls ctr) (16 * (lowerPlan lay leaf).getD j 0 + 32) 16 = zeros 16 := by
  have hz : ∀ i, i < 16 → lowerPathByte lay leaf ls ctr (16 * (lowerPlan lay leaf).getD j 0 + 32 + i) = 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_pad_disjoint lay hlay leaf hleaf j (by omega) j'.val j'.isLt
      omega)]
    have hd := lower_pad_pad_disjoint lay hlay leaf hleaf j (by omega) (height lay - 1) (by omega) (by omega)
    have hr := (lower_hp_root lay hlay leaf hleaf j (by omega)).2
    unfold lowerCtrSlot lowerHiSlot
    rw [if_neg (by omega), if_neg (by omega)]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by have := lower_pad_bound lay hlay leaf hleaf j (by omega); omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
theorem lowerPath_ctr :
    window (lowerPathBytes lay leaf ls ctr) (lowerCtrSlot lay leaf) 4 = bytesLE 4 ctr := by
  have hb := lower_pad_bound lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
  have hz : ∀ i, i < 4 → lowerPathByte lay leaf ls ctr (lowerCtrSlot lay leaf + i) = (bytesLE 4 ctr).getD i 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_pad_disjoint lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
        j'.val j'.isLt
      unfold lowerCtrSlot; omega), if_pos (by omega), Nat.add_sub_cancel_left]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by unfold lowerCtrSlot; omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem lowerPath_rowPad :
    window (lowerPathBytes lay leaf ls ctr) (lowerCtrSlot lay leaf + 4) 12 = zeros 12 := by
  have hb := lower_pad_bound lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
  have hz : ∀ i, i < 12 → lowerPathByte lay leaf ls ctr (lowerCtrSlot lay leaf + 4 + i) = 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_pad_disjoint lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
        j'.val j'.isLt
      unfold lowerCtrSlot; omega), if_neg (by omega), if_neg (by unfold lowerHiSlot lowerCtrSlot; omega)]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by unfold lowerCtrSlot; omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
/-- C2/C3 (FULL): the root window's row tweak high word holds LE64 1. -/
theorem lowerPath_hi :
    window (lowerPathBytes lay leaf ls ctr) (lowerHiSlot lay leaf) 8 = bytesLE 8 (1 : BitVec 64) := by
  have hb := lower_pad_bound lay hlay leaf hleaf (height lay - 1) (by have := height_pos' lay; omega)
  have hz : ∀ i, i < 8 → lowerPathByte lay leaf ls ctr (lowerHiSlot lay leaf + i) =
      (bytesLE 8 (1 : BitVec 64)).getD i 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_hi_sib lay hlay leaf hleaf j'.val j'.isLt
      unfold lowerHiSlot; omega), if_neg (by unfold lowerHiSlot lowerCtrSlot; omega), if_pos (by omega),
      Nat.add_sub_cancel_left]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by unfold lowerHiSlot; omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
/-- C2 (FULL): the high tweak word of a lower fold window below the root is zero. -/
theorem lowerPath_hp {j : Nat} (hj : j + 1 < height lay) :
    window (lowerPathBytes lay leaf ls ctr) (16 * (lowerPlan lay leaf).getD j 0 + 24) 8 = zeros 8 := by
  have hb := lower_pad_bound lay hlay leaf hleaf j (by omega)
  have hr := (lower_hp_root lay hlay leaf hleaf j (by omega)).1
  have hz : ∀ i, i < 8 → lowerPathByte lay leaf ls ctr (16 * (lowerPlan lay leaf).getD j 0 + 24 + i) = 0 := by
    intro i hi'
    rw [lowerPathByte_free ls ctr (fun j' => by
      have := lower_hp_sib lay hlay leaf hleaf j (by omega) j'.val j'.isLt
      omega), if_neg (by unfold lowerCtrSlot; omega), if_neg (by unfold lowerHiSlot; omega)]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by omega),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
end lowerPath
theorem route_leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ height lay := by
  unfold route; exact Nat.mod_lt _ (by positivity)
theorem win_lowerPath (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (hlay : lay.val ≠ 0) (o m : Nat)
    (h : o + m ≤ 16 * pathSlots lay) :
    window (witList N w) (layerBase lay + o) m =
      window (lowerPathBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
        (w.counters (Fin.ofNat 4 (lay.val - 1)))) o m := by
  rw [win_layerRegion N w lay o m (by omega)]
  unfold layerRegion
  rw [if_neg hlay, window_append_left _ _ _ _ (by rw [lowerPathBytes_length]; exact h)]
/-! ### C4 top path area: plan-placed siblings, honest zero high words and Z pads
Line A (levels 0..5, row `leaf % 64`) lies in bytes `[336, 672)`, line B (levels 6..11, row `leaf / 64 % 64`) in
`[0, 320)`; within a line the sibling slots and the pad areas `[16 P_j + 24, 16 P_j + 48)` are disjoint (kernel
checks over the 64 rows). -/
def topSlotA (r j : Nat) : Nat := (topPlanA.getD r []).getD j 0
def topSlotB (r j : Nat) : Nat := (topPlanB.getD r []).getD j 0
def topSibA (r j : Nat) : Nat := 16 * topSlotA r j + sibOff (r / 2 ^ j % 2)
def topSibB (r j : Nat) : Nat := 16 * topSlotB r j + sibOff (r / 2 ^ j % 2)
theorem topA_range : ∀ r < 64, ∀ j < 6, 336 ≤ 16 * topSlotA r j ∧ 16 * topSlotA r j + 64 ≤ 672 := by decide
theorem topB_range : ∀ r < 64, ∀ j < 6, 16 * topSlotB r j + 64 ≤ 320 := by decide
theorem topA_sib : ∀ r < 64, ∀ j < 6, ∀ j' < 6, j ≠ j' →
    topSibA r j + 16 ≤ topSibA r j' ∨ topSibA r j' + 16 ≤ topSibA r j := by decide
theorem topB_sib : ∀ r < 64, ∀ j < 6, ∀ j' < 6, j ≠ j' →
    topSibB r j + 16 ≤ topSibB r j' ∨ topSibB r j' + 16 ≤ topSibB r j := by decide
theorem topA_pad : ∀ r < 64, ∀ j < 6, ∀ j' < 6,
    16 * topSlotA r j + 48 ≤ topSibA r j' ∨ topSibA r j' + 16 ≤ 16 * topSlotA r j + 24 := by decide
theorem topB_pad : ∀ r < 64, ∀ j < 6, ∀ j' < 6,
    16 * topSlotB r j + 48 ≤ topSibB r j' ∨ topSibB r j' + 16 ≤ 16 * topSlotB r j + 24 := by decide
theorem sibOff_le (b : Nat) : sibOff b ≤ 48 := by unfold sibOff; split <;> omega
theorem topPlanSlot_lo {leaf j : Nat} (hj : j < 6) : topPlanSlot leaf j = topSlotA (leaf % 64) j := by
  unfold topPlanSlot topSlotA; rw [if_pos hj]
theorem topPlanSlot_hi {leaf j : Nat} (hj : 6 ≤ j) : topPlanSlot leaf j = topSlotB (leaf / 64 % 64) (j - 6) := by
  unfold topPlanSlot topSlotB; rw [if_neg (by omega)]
theorem bit_lo (leaf j : Nat) (hj : j < 6) : leaf / 2 ^ j % 2 = leaf % 64 / 2 ^ j % 2 := by
  interval_cases j <;> simp only [Nat.reducePow] <;> omega
theorem bit_hi (leaf j : Nat) (h1 : 6 ≤ j) (h2 : j < 12) : leaf / 2 ^ j % 2 = leaf / 64 % 64 / 2 ^ (j - 6) % 2 := by
  interval_cases j <;> simp only [Nat.reducePow, Nat.reduceSub] <;> omega
theorem topSibSlot_lo {leaf j : Nat} (hj : j < 6) : topSibSlot leaf j = topSibA (leaf % 64) j := by
  unfold topSibSlot topSibA; rw [topPlanSlot_lo hj, bit_lo leaf j hj]
theorem topSibSlot_hi {leaf j : Nat} (h1 : 6 ≤ j) (h2 : j < 12) :
    topSibSlot leaf j = topSibB (leaf / 64 % 64) (j - 6) := by
  unfold topSibSlot topSibB; rw [topPlanSlot_hi h1, bit_hi leaf j h1 h2]
theorem height_top : height (0 : Layer) = 12 := rfl
theorem pathSlots_top : 16 * pathSlots (0 : Layer) = 672 := rfl
/-- Every top window's sibling slot and pad area lie in its line's range. -/
theorem top_ranges (leaf j : Nat) (hj : j < height 0) :
    (j < 6 → 336 ≤ topSibSlot leaf j ∧ topSibSlot leaf j + 16 ≤ 672 ∧
      336 ≤ 16 * topPlanSlot leaf j ∧ 16 * topPlanSlot leaf j + 48 ≤ 672) ∧
    (6 ≤ j → topSibSlot leaf j + 16 ≤ 320 ∧ 16 * topPlanSlot leaf j + 48 ≤ 320) := by
  rw [height_top] at hj
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr' : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  refine ⟨fun h6 => ?_, fun h6 => ?_⟩
  · have := topA_range _ hr j h6
    have := sibOff_le (leaf % 64 / 2 ^ j % 2)
    rw [topSibSlot_lo h6, topPlanSlot_lo h6]
    unfold topSibA
    omega
  · have := topB_range _ hr' (j - 6) (by omega)
    have := sibOff_le (leaf / 64 % 64 / 2 ^ (j - 6) % 2)
    rw [topSibSlot_hi h6 hj, topPlanSlot_hi h6]
    unfold topSibB
    omega
theorem top_sib_bound (leaf j : Nat) (hj : j < height 0) : topSibSlot leaf j + 16 ≤ 672 := by
  have h := top_ranges leaf j hj
  by_cases h6 : j < 6
  · exact (h.1 h6).2.1
  · have := (h.2 (by omega)).1; omega
theorem top_pad_bound (leaf j : Nat) (hj : j < height 0) : 16 * topPlanSlot leaf j + 48 ≤ 672 := by
  have h := top_ranges leaf j hj
  by_cases h6 : j < 6
  · exact (h.1 h6).2.2.2
  · have := (h.2 (by omega)).2; omega
theorem top_sib_disjoint (leaf j j' : Nat) (hj : j < height 0) (hj' : j' < height 0) (hne : j ≠ j') :
    topSibSlot leaf j + 16 ≤ topSibSlot leaf j' ∨ topSibSlot leaf j' + 16 ≤ topSibSlot leaf j := by
  have h := top_ranges leaf j hj
  have h' := top_ranges leaf j' hj'
  rw [height_top] at hj hj'
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr' : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · rw [topSibSlot_lo h6, topSibSlot_lo h6']; exact topA_sib _ hr j h6 j' h6' hne
  · have := (h.1 h6).1; have := (h'.2 (by omega)).1; omega
  · have := (h.2 (by omega)).1; have := (h'.1 h6').1; omega
  · rw [topSibSlot_hi (by omega) hj, topSibSlot_hi (by omega) hj']
    exact topB_sib _ hr' (j - 6) (by omega) (j' - 6) (by omega) (by omega)
theorem top_pad_sib (leaf j j' : Nat) (hj : j < height 0) (hj' : j' < height 0) :
    16 * topPlanSlot leaf j + 48 ≤ topSibSlot leaf j' ∨ topSibSlot leaf j' + 16 ≤ 16 * topPlanSlot leaf j + 24 := by
  have h := top_ranges leaf j hj
  have h' := top_ranges leaf j' hj'
  rw [height_top] at hj hj'
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr' : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · rw [topPlanSlot_lo h6, topSibSlot_lo h6']; exact topA_pad _ hr j h6 j' h6'
  · have := (h.1 h6).2.2.1; have := (h'.2 (by omega)).1; omega
  · have := (h.2 (by omega)).2; have := (h'.1 h6').1; omega
  · rw [topPlanSlot_hi (by omega), topSibSlot_hi (by omega) hj']
    exact topB_pad _ hr' (j - 6) (by omega) (j' - 6) (by omega)
section topPath
variable (leaf : Nat) (ls : LayerSignature 0)
theorem topPathByte_sib (j : Fin (height 0)) {i : Nat} (hi : i < 16) :
    topPathByte leaf ls (topSibSlot leaf j.val + i) = (bytesLE 16 (ls.path j)).getD i 0 := by
  unfold topPathByte
  generalize hf : (List.finRange (height 0)).find? _ = r
  rcases r with _ | j'
  · exfalso
    have := List.find?_eq_none.mp hf j (List.mem_finRange j)
    simp only [decide_eq_true_eq, not_and, not_lt] at this
    have := this (by omega)
    omega
  · have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have hjj : j' = j := by
      by_contra hne
      have hd := top_sib_disjoint leaf j'.val j.val j'.isLt j.isLt (fun e => hne (Fin.ext e))
      omega
    subst hjj
    simp only [Nat.add_sub_cancel_left]
theorem topPathByte_free {p : Nat}
    (hp : ∀ j : Fin (height 0), p < topSibSlot leaf j.val ∨ topSibSlot leaf j.val + 16 ≤ p) :
    topPathByte leaf ls p = 0 := by
  unfold topPathByte
  rw [List.find?_eq_none.mpr (fun j _ => by
    have := hp j
    simp only [decide_eq_true_eq, not_and, not_lt]
    omega)]
theorem topPath_sib (j : Fin (height 0)) :
    window (topPathBytes leaf ls) (topSibSlot leaf j.val) 16 = bytesLE 16 (ls.path j) := by
  unfold topPathBytes
  rw [window_map_range _ _ _ _ (by rw [pathSlots_top]; exact top_sib_bound leaf j.val j.isLt),
    List.map_congr_left (fun i hi => topPathByte_sib leaf ls j (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem topPath_zero {a m : Nat} (hb : a + m ≤ 672)
    (hc : ∀ j : Fin (height 0), a + m ≤ topSibSlot leaf j.val ∨ topSibSlot leaf j.val + 16 ≤ a) :
    window (topPathBytes leaf ls) a m = zeros m := by
  have hz : ∀ i, i < m → topPathByte leaf ls (a + i) = 0 := by
    intro i hi
    exact topPathByte_free leaf ls (fun j => by have := hc j; omega)
  unfold topPathBytes
  rw [window_map_range _ _ _ _ (by rw [pathSlots_top]; exact hb),
    List.map_congr_left (fun i hi => hz i (List.mem_range.mp hi))]
  simp [zeros, List.map_const']
theorem topPath_pad {j : Nat} (hj : j < height 0) :
    window (topPathBytes leaf ls) (16 * topPlanSlot leaf j + 32) 16 = zeros 16 :=
  topPath_zero leaf ls (by have := top_pad_bound leaf j hj; omega)
    (fun j' => by have := top_pad_sib leaf j j'.val hj j'.isLt; omega)
theorem topPath_hp {j : Nat} (hj : j < height 0) :
    window (topPathBytes leaf ls) (16 * topPlanSlot leaf j + 24) 8 = zeros 8 :=
  topPath_zero leaf ls (by have := top_pad_bound leaf j hj; omega)
    (fun j' => by have := top_pad_sib leaf j j'.val hj j'.isLt; omega)
end topPath
theorem win_topPath (N : HashOutput) (w : WCT9.Witness) (o m : Nat) (h : o + m ≤ 672) :
    window (witList N w) (layerBase 0 + o) m =
      window (topPathBytes (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) o m := by
  rw [win_layerRegion N w 0 o m (by rw [pathSlots_top]; omega)]
  unfold layerRegion
  rw [if_pos (show (0 : Layer).val = 0 from rfl),
    window_append_left _ _ _ _ (by rw [topPathBytes_length, pathSlots_top]; exact h)]
section t3b
variable (N : HashOutput) (w : WCT9.Witness)
theorem wpath_witEnc (lay : Layer) (j : Fin (height lay)) :
    wpath (witEnc N w) lay (route (WCT9.digestIndex N) lay).1 j.val = (w.signature.layers lay).path j := by
  by_cases hlay : lay.val = 0
  · have hl : lay = 0 := Fin.ext hlay
    subst hl
    unfold wpath merkleBlock
    rw [if_pos (show (0 : Layer).val = 0 from rfl), Nat.add_assoc,
      show 16 * topPlanSlot (route (WCT9.digestIndex N) 0).1 j.val +
        sibOff ((route (WCT9.digestIndex N) 0).1 / 2 ^ j.val % 2) =
        topSibSlot (route (WCT9.digestIndex N) 0).1 j.val from rfl, wdig_witEnc,
      win_topPath _ _ _ _ (top_sib_bound _ j.val j.isLt), topPath_sib, Correctness.readDigest_bytesLE]
  · have hleaf := route_leaf_lt (WCT9.digestIndex N) lay
    unfold wpath merkleBlock
    rw [if_neg hlay, Nat.add_assoc, show 16 * (lowerPlan lay (route (WCT9.digestIndex N) lay).1).getD j.val 0 +
        sibOff ((route (WCT9.digestIndex N) lay).1 / 2 ^ j.val % 2) =
        lowerSibSlot lay (route (WCT9.digestIndex N) lay).1 j.val from rfl, wdig_witEnc,
      win_lowerPath _ _ _ hlay _ _ (lower_sib_bound lay hlay _ hleaf j.val j.isLt),
      lowerPath_sib hlay hleaf, Correctness.readDigest_bytesLE]
theorem wmerklePad_witEnc (lay : Layer) (j : Fin (height lay)) (hj : j.val + 1 < height lay ∨ lay.val = 0) :
    wmerklePad (witEnc N w) lay (route (WCT9.digestIndex N) lay).1 j.val = 0 := by
  by_cases hlay : lay.val = 0
  · have hl : lay = 0 := Fin.ext hlay
    subst hl
    unfold wmerklePad merkleBlock
    rw [if_pos (show (0 : Layer).val = 0 from rfl), Nat.add_assoc, wdig_witEnc,
      win_topPath _ _ _ _ (by have := top_pad_bound (route (WCT9.digestIndex N) 0).1 j.val j.isLt; omega),
      topPath_pad _ _ j.isLt, readDigest_zeros]
  · have hleaf := route_leaf_lt (WCT9.digestIndex N) lay
    have hj' : j.val + 1 < height lay := hj.resolve_right hlay
    unfold wmerklePad merkleBlock
    rw [if_neg hlay, Nat.add_assoc, wdig_witEnc,
      win_lowerPath _ _ _ hlay _ _ (by have := lower_pad_bound lay hlay _ hleaf j.val j.isLt; omega),
      lowerPath_pad hlay hleaf _ _ hj', readDigest_zeros]
theorem rowBlock_upper (index : Nat) (lay : Layer) (h : lay.val < 3) :
    rowBlock index lay + 32 = layerBase (upLayer lay) + lowerCtrSlot (upLayer lay) (route index (upLayer lay)).1 := by
  have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
  unfold rowBlock merkleBlock lowerCtrSlot
  rw [if_neg (by omega), if_neg hv]
  omega
theorem upLayer_down (lay : Layer) (h : lay.val < 3) : (Fin.ofNat 4 ((upLayer lay).val - 1) : Layer) = lay := by
  apply Fin.ext
  unfold upLayer
  simp [Fin.val_ofNat]
  omega
theorem wbcCtr_witEnc (lay : Layer) : wbcCtr (witEnc N w) (WCT9.digestIndex N) lay = w.counters lay := by
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    exact wctr3_witEnc N w
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
    have hleaf := route_leaf_lt (WCT9.digestIndex N) (upLayer lay)
    have hb := lower_pad_bound (upLayer lay) hv _ hleaf (height (upLayer lay) - 1)
      (by have := height_pos' (upLayer lay); omega)
    unfold wbcCtr bcCounterOff
    rw [rowBlock_upper _ _ hlt, wle32_witEnc,
      win_lowerPath _ _ _ hv _ _ (by unfold lowerCtrSlot; omega), upLayer_down lay hlt,
      lowerPath_ctr hv hleaf, readLE_bytesLE_32]
theorem wbcPad_witEnc (lay : Layer) : wbcPad (witEnc N w) (WCT9.digestIndex N) lay = 0 := by
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    exact wpad3_witEnc N w
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
    have hleaf := route_leaf_lt (WCT9.digestIndex N) (upLayer lay)
    have hb := lower_pad_bound (upLayer lay) hv _ hleaf (height (upLayer lay) - 1)
      (by have := height_pos' (upLayer lay); omega)
    unfold wbcPad witEnc bcCounterOff
    rw [rowBlock_upper _ _ hlt, show (96 : Nat) = 8 * 12 from rfl,
      extract_readLE_lt (witList N w) 24828 (witList_readLE_lt N w) _ 12,
      show ((witList N w).drop (layerBase (upLayer lay) +
          lowerCtrSlot (upLayer lay) (route (WCT9.digestIndex N) (upLayer lay)).1 + 4)).take 12 =
        window (witList N w) (layerBase (upLayer lay) +
          (lowerCtrSlot (upLayer lay) (route (WCT9.digestIndex N) (upLayer lay)).1 + 4)) 12 by
        unfold window; rw [Nat.add_assoc],
      win_lowerPath _ _ _ hv _ _ (by unfold lowerCtrSlot; omega), lowerPath_rowPad hv hleaf]
    rfl
theorem rowBlock_hi (index : Nat) (lay : Layer) (h : lay.val < 3) :
    rowBlock index lay + 16 + 8 = layerBase (upLayer lay) + lowerHiSlot (upLayer lay) (route index (upLayer lay)).1 := by
  have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
  unfold rowBlock merkleBlock lowerHiSlot
  rw [if_neg (by omega), if_neg hv]
  omega
/-- C2/C3 (FULL): the honest encoding row tweak high words are 1. -/
theorem wbcHigh_witEnc (lay : Layer) : wbcHigh (witEnc N w) (WCT9.digestIndex N) lay = 1 := by
  unfold wbcHigh
  rw [wdig_high, wword_witEnc]
  by_cases h3 : lay.val = 3
  · have hl : lay = 3 := Fin.ext h3
    subst hl
    rw [show rowBlock (WCT9.digestIndex N) 3 + 16 + 8 = 24 by simp [rowBlock], win_header_hi]
    decide
  · have hlt : lay.val < 3 := by have := lay.isLt; omega
    have hv : (upLayer lay).val ≠ 0 := by unfold upLayer; simp [Fin.val_ofNat]; omega
    have hleaf := route_leaf_lt (WCT9.digestIndex N) (upLayer lay)
    have hb := lower_pad_bound (upLayer lay) hv _ hleaf (height (upLayer lay) - 1)
      (by have := height_pos' (upLayer lay); omega)
    rw [rowBlock_hi _ _ hlt, win_lowerPath _ _ _ hv _ _ (by unfold lowerHiSlot; omega), lowerPath_hi hv hleaf]
    decide
/-- C2 (FULL) + C4: the honest high tweak words of the fold windows are 0 (lower windows below the root, every top
window). -/
theorem wmerkleHigh_witEnc (lay : Layer) (j : Fin (height lay)) (hj : j.val + 1 < height lay ∨ lay.val = 0) :
    wmerkleHigh (witEnc N w) lay (route (WCT9.digestIndex N) lay).1 j.val = 0 := by
  unfold wmerkleHigh
  by_cases hlay : lay.val = 0
  · have hl : lay = 0 := Fin.ext hlay
    subst hl
    have hb := top_pad_bound (route (WCT9.digestIndex N) 0).1 j.val j.isLt
    rw [wdig_high, wword_witEnc]
    unfold merkleBlock
    rw [if_pos (show (0 : Layer).val = 0 from rfl),
      show layerBase 0 + 16 * topPlanSlot (route (WCT9.digestIndex N) 0).1 j.val + 16 + 8 =
        layerBase 0 + (16 * topPlanSlot (route (WCT9.digestIndex N) 0).1 j.val + 24) by omega,
      win_topPath _ _ _ _ (by omega), topPath_hp _ _ j.isLt]
    decide
  · have hj : j.val + 1 < height lay := hj.resolve_right hlay
    have hleaf := route_leaf_lt (WCT9.digestIndex N) lay
    have hb := lower_pad_bound lay hlay _ hleaf j.val j.isLt
    rw [wdig_high, wword_witEnc]
    unfold merkleBlock
    rw [if_neg hlay, show layerBase lay + 16 * (lowerPlan lay (route (WCT9.digestIndex N) lay).1).getD j.val 0 + 16 + 8 =
        layerBase lay + (16 * (lowerPlan lay (route (WCT9.digestIndex N) lay).1).getD j.val 0 + 24) by omega,
      win_lowerPath _ _ _ hlay _ _ (by omega), lowerPath_hp hlay hleaf _ _ hj]
    decide
end t3b
theorem win_region (N : HashOutput) (w : WCT9.Witness) (k : WCT9.Coord) (o n : Nat) (h : o + n ≤ 896) :
    window (witList N w) (regionBase k.val + o) n =
      window (regionBytes (WCT9.child N k).val (w.signature.openings k) (prevSibL N w.signature k.val)
        (prevSibZ N w.signature k.val)) o n := by
  have hk := k.isLt
  have hrb : regionBase k.val = 176 + 896 * (8 - k.val) := rfl
  rw [witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    show regionBase k.val + o - 176 = 896 * (8 - k.val) + o by omega]
  have hidx : ((List.finRange 9).reverse[8 - k.val]'(by simp; omega)) = k := by
    rw [List.getElem_reverse]; ext; simp; omega
  have key := window_flatMap (List.finRange 9).reverse (regionCell N w.signature) (8 - k.val) (by simp; omega) o n
    (by rw [hidx, regionCell_length]; unfold regionLen; split <;> omega)
  simp only [regionCell_length] at key
  rw [wct_prefix, hidx] at key
  rw [wctBytes_eq, key]
  unfold regionCell
  rw [window_append_left _ _ _ _ (by
    rw [regionBytes_length _ _ _ _ (prevSibL_length _ _ _) (prevSibZ_length _ _ _)]; exact h)]
theorem wdig_region (N : HashOutput) (w : WCT9.Witness) (k : WCT9.Coord) (o : Nat) (h : o + 16 ≤ 896) :
    wdig (witEnc N w) (regionBase k.val + o) =
      readDigest (window (regionBytes (WCT9.child N k).val (w.signature.openings k) (prevSibL N w.signature k.val)
        (prevSibZ N w.signature k.val)) o 16) := by
  rw [wdig_witEnc, win_region N w k o 16 h]
theorem auth_sib_bound : ∀ c < 128, ∀ l < 5, authSibOff c l + 16 ≤ 320 := by decide
theorem auth_pad_bound : ∀ c < 128, ∀ l < 5, authPadOff c l + 16 ≤ 320 ∨ authPadOff c l = 320 := by decide
theorem auth_sib_disjoint : ∀ c < 128, ∀ l < 5, ∀ l' < 5, l ≠ l' →
    authSibOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authSibOff c l := by decide
theorem auth_pad_disjoint : ∀ c < 128, ∀ l < 5, ∀ l' < 5,
    authPadOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authPadOff c l := by decide
theorem find_finRange_eq (l : Fin 5) : (List.finRange 5).find? (fun l' => decide (l' = l)) = some l := by
  revert l; decide
theorem authByte5_sib {c : Nat} (hc : c < 128) (op : WCT9.Opening) (l : Fin 5) {i : Nat} (hi : i < 16) :
    authByte5 c op (authSibOff c l.val + i) = (bytesLE 16 (op.path (Fin.castLE (by decide) l))).getD i 0 := by
  have hP : (fun l' : Fin 5 => decide (authSibOff c l'.val ≤ authSibOff c l.val + i ∧
      authSibOff c l.val + i < authSibOff c l'.val + 16)) = fun l' => decide (l' = l) := by
    funext l'
    by_cases h : l' = l
    · subst h; simp only [decide_true, decide_eq_true_eq]; omega
    · have hd := auth_sib_disjoint c hc l'.val l'.isLt l.val l.isLt (fun e => h (Fin.ext e))
      simp only [h, decide_false, decide_eq_false_iff_not, not_and, not_lt]
      omega
  unfold authByte5
  rw [hP, find_finRange_eq]
  simp only [Nat.add_sub_cancel_left]
theorem authByte5_none {c : Nat} (op : WCT9.Opening) {p : Nat}
    (hp : ∀ l : Fin 5, p < authSibOff c l.val ∨ authSibOff c l.val + 16 ≤ p) : authByte5 c op p = 0 := by
  unfold authByte5
  rw [List.find?_eq_none.mpr (fun l _ => by
    have := hp l
    simp only [decide_eq_true_eq, not_and, not_lt]
    omega)]
theorem merkleBytes_sib {c : Nat} (hc : c < 128) (op : WCT9.Opening) (l : Fin 5) :
    window (merkleBytes c op) (authSibOff c l.val) 16 = bytesLE 16 (op.path (Fin.castLE (by decide) l)) := by
  unfold merkleBytes
  rw [window_map_range _ _ _ _ (auth_sib_bound c hc l.val l.isLt),
    List.map_congr_left (fun i hi => authByte5_sib hc op l (List.mem_range.mp hi))]
  exact map_range_getD _ _ (bytesLE_length _ _)
theorem merkleBytes_pad {c : Nat} (hc : c < 128) (op : WCT9.Opening) {l : Nat} (hl : l < 5) (hb : authPadOff c l + 16 ≤ 320) :
    window (merkleBytes c op) (authPadOff c l) 16 = zeros 16 := by
  unfold merkleBytes
  rw [window_map_range _ _ _ _ hb,
    List.map_congr_left (fun i hi => authByte5_none op (fun l' => by
      have := auth_pad_disjoint c hc l hl l'.val l'.isLt
      have := List.mem_range.mp hi
      omega))]
  simp [zeros, List.map_const']
theorem auth_tw_bound : ∀ c < 128, ∀ l < 4, authBase c l + 16 + 16 ≤ 320 := by decide
theorem auth_tw_disjoint : ∀ c < 128, ∀ l < 4, ∀ l' < 5,
    authBase c l + 16 + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authBase c l + 16 := by decide
theorem merkleBytes_tw {c : Nat} (hc : c < 128) (op : WCT9.Opening) {l : Nat} (hl : l < 4)
    (hb : authBase c l + 16 + 16 ≤ 320) :
    window (merkleBytes c op) (authBase c l + 16) 16 = zeros 16 := by
  unfold merkleBytes
  rw [window_map_range _ _ _ _ hb,
    List.map_congr_left (fun i hi => authByte5_none op (fun l' => by
      have := auth_tw_disjoint c hc l hl l'.val l'.isLt
      have := List.mem_range.mp hi
      omega))]
  simp [zeros, List.map_const']
section region
variable (c : Nat) (op : WCT9.Opening) (padL padZ : List UInt8)
theorem region_merkle (o n : Nat) (h : o + n ≤ 320) :
    window (regionBytes c op padL padZ) o n = window (merkleBytes c op) o n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length]; omega)]
theorem region_chain (o n : Nat) (h0 : 320 ≤ o) (h : o + n ≤ 640) :
    window (regionBytes c op padL padZ) o n = window (chainBytes op) (o - 320) n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length]; omega), merkleBytes_length]
theorem region_prefix (o n : Nat) (h0 : 640 ≤ o) (h : o + n ≤ 688) :
    window (regionBytes c op padL padZ) o n = zeros n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length]
  exact window_zeros _ _ _ (by omega)
theorem region_leaf (hL : padL.length = 16) (o n : Nat) (h0 : 688 ≤ o) (h : o + n ≤ 816) :
    window (regionBytes c op padL padZ) o n = window (leafBytes op padL) (o - 688) n := by
  unfold regionBytes
  rw [window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, zeros]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length, zeros, List.length_replicate]
theorem region_top (hL : padL.length = 16) (o n : Nat) (h0 : 832 ≤ o) :
    window (regionBytes c op padL padZ) o n = window (topBlockBytes c op padZ) (o - 832) n := by
  unfold regionBytes
  rw [window_append_right _ _ _ _ (by simp [merkleBytes_length, chainBytes_length, leafBytes_length', zeros]; omega)]
  simp only [List.length_append, merkleBytes_length, chainBytes_length, leafBytes_length', hL, zeros,
    List.length_replicate]
theorem chainBytes_window (i : Fin 5) (o : Nat) (ho : o + 16 ≤ 64) :
    window (chainBytes op) (64 * (4 - i.val) + o) 16 = window (zeros 48 ++ bytesLE 16 (op.values i.succ)) o 16 := by
  have hi := i.isLt
  unfold chainBytes
  rw [window_flatMap_const _ _ 64 (fun j => by simp [zeros, bytesLE_length]) (4 - i.val) (by simp; omega) o 16 ho]
  have hj : ((List.finRange 5).reverse[4 - i.val]'(by simp; omega)) = i := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hj]
theorem leafBytes_window_zero : window (leafBytes op padL) 0 16 = bytesLE 16 (op.values 0) := by
  unfold leafBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
theorem leafBytes_window_pad (hL : padL.length = 16) : window (leafBytes op padL) 32 16 = padL := by
  unfold leafBytes
  rw [window_append_left _ _ _ _ (by simp [bytesLE_length, zeros, hL]),
    window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 32 - (bytesLE 16 (op.values 0) ++ zeros 16).length = 0 by simp [bytesLE_length, zeros],
    window_full _ _ hL]
theorem leafBytes_window_succ (hL : padL.length = 16) (i : Fin 5) :
    window (leafBytes op padL) (48 + 16 * i.val) 16 = bytesLE 16 (op.values i.succ) := by
  have hi := i.isLt
  unfold leafBytes
  rw [window_append_right _ _ _ _ (by simp [bytesLE_length, zeros, hL]),
    show 48 + 16 * i.val - (bytesLE 16 (op.values 0) ++ zeros 16 ++ padL).length = 16 * i.val + 0 by
      simp [bytesLE_length, zeros, hL],
    window_flatMap_const _ _ 16 (fun j => bytesLE_length _ _) i.val (by simp [hi]) 0 16 le_rfl,
    window_full _ _ (bytesLE_length _ _)]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
theorem topBlock_sib (hZ : padZ.length = 16) :
    window (topBlockBytes c op padZ) (sibOff (c / 2 ^ 5 % 2)) 16 = bytesLE 16 (op.path 5) := by
  unfold topBlockBytes sibOff
  by_cases hb : c / 2 ^ 5 % 2 = 1
  · rw [if_pos hb, if_pos hb, if_neg (show ¬(c / 2 ^ 5 % 2 = 0) by omega),
      window_append_left _ _ _ _ (by simp [bytesLE_length, zeros, hZ]),
      window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
      window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
  · rw [if_neg hb, if_neg hb, if_pos (show c / 2 ^ 5 % 2 = 0 by omega),
      window_append_right _ _ _ _ (by simp [zeros, hZ]),
      show 48 - (zeros 16 ++ zeros 16 ++ padZ).length = 0 by simp [zeros, hZ],
      window_full _ _ (bytesLE_length _ _)]
theorem topBlock_pad (hZ : padZ.length = 16) : window (topBlockBytes c op padZ) 32 16 = padZ := by
  unfold topBlockBytes
  rw [window_append_left _ _ _ _ (by simp only [List.length_append, ite_slot_length, zeros_len, hZ]; omega),
    window_append_right _ _ _ _ (by simp only [List.length_append, ite_slot_length, zeros_len]; omega),
    show 32 - ((if c / 2 ^ 5 % 2 = 1 then bytesLE 16 (op.path 5) else zeros 16) ++ zeros 16).length = 0 by
      simp only [List.length_append, ite_slot_length, zeros_len],
    window_full _ _ hZ]
end region
section fields
variable (N : HashOutput) (w : WCT9.Witness)
theorem wopen_witEnc (k : WCT9.Coord) (t : Fin 6) :
    wopen (witEnc N w) k.val t.val = (w.signature.openings k).values t := by
  unfold wopen wctChainBlock
  rcases t with ⟨_ | i, ht⟩
  · dsimp only
    rw [show regionBase k.val + (640 - 64 * 0) + 48 = regionBase k.val + 688 by omega,
      wdig_region N w k _ (by omega), region_leaf _ _ _ _ (prevSibL_length _ _ _) _ _ le_rfl (by omega),
      Nat.sub_self, leafBytes_window_zero, Correctness.readDigest_bytesLE]
    rfl
  · have hi : i < 5 := by omega
    dsimp only
    rw [show regionBase k.val + (640 - 64 * (i + 1)) + 48 = regionBase k.val + (320 + (64 * (4 - i) + 48)) by
        omega, wdig_region N w k _ (by omega), region_chain _ _ _ _ _ _ (by omega) (by omega),
      show 320 + (64 * (4 - i) + 48) - 320 = 64 * (4 - (⟨i, hi⟩ : Fin 5).val) + 48 by simp,
      chainBytes_window _ _ _ (by omega), window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _),
      Correctness.readDigest_bytesLE]
    rfl
theorem wleaf_witEnc (k : WCT9.Coord) (t : Fin 6) :
    wleaf (witEnc N w) k.val t.val = (w.signature.openings k).values t := by
  rcases t with ⟨_ | i, ht⟩
  · rw [show (⟨0, ht⟩ : Fin 6).val = 0 from rfl, wleaf_zero]
    exact wopen_witEnc N w k ⟨0, ht⟩
  · have hi : i < 5 := by omega
    unfold wleaf wctLeafSlot
    dsimp only
    rw [if_neg (by omega), show regionBase k.val + (720 + 16 * (i + 1)) = regionBase k.val + (688 + (48 + 16 * i)) by
        omega, wdig_region N w k _ (by omega),
      region_leaf _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega) (by omega),
      show 688 + (48 + 16 * i) - 688 = 48 + 16 * (⟨i, hi⟩ : Fin 5).val by simp,
      leafBytes_window_succ _ _ (prevSibL_length _ _ _), Correctness.readDigest_bytesLE]
    rfl
theorem wreveal_witEnc (k : WCT9.Coord) (t : Fin 6) (d : Nat) :
    wreveal (witEnc N w) k.val t.val d = (w.signature.openings k).values t := by
  unfold wreveal
  split
  · exact wleaf_witEnc N w k t
  · exact wopen_witEnc N w k t
theorem wcpads_witEnc (k : WCT9.Coord) (t : Fin 6) : wcpads (witEnc N w) k.val t.val = (0, 0) := by
  unfold wcpads wctChainBlock
  rcases t with ⟨_ | i, ht⟩
  · dsimp only
    rw [show regionBase k.val + (640 - 64 * 0) = regionBase k.val + 640 by omega,
      show regionBase k.val + 640 + 32 = regionBase k.val + 672 by omega,
      wdig_region N w k _ (by omega), wdig_region N w k _ (by omega),
      region_prefix _ _ _ _ _ _ le_rfl (by omega), region_prefix _ _ _ _ _ _ (by omega) (by omega), readDigest_zeros]
  · have hi : i < 5 := by omega
    dsimp only
    rw [show regionBase k.val + (640 - 64 * (i + 1)) = regionBase k.val + (320 + (64 * (4 - i) + 0)) by omega,
      show regionBase k.val + (320 + (64 * (4 - i) + 0)) + 32 = regionBase k.val + (320 + (64 * (4 - i) + 32)) by
        omega,
      wdig_region N w k _ (by omega), wdig_region N w k _ (by omega),
      region_chain _ _ _ _ _ _ (by omega) (by omega), region_chain _ _ _ _ _ _ (by omega) (by omega),
      show 320 + (64 * (4 - i) + 0) - 320 = 64 * (4 - (⟨i, hi⟩ : Fin 5).val) + 0 by simp,
      show 320 + (64 * (4 - i) + 32) - 320 = 64 * (4 - (⟨i, hi⟩ : Fin 5).val) + 32 by simp,
      chainBytes_window _ _ _ (by omega), chainBytes_window _ _ _ (by omega),
      window_append_left _ _ _ _ (by simp [zeros]), window_append_left _ _ _ _ (by simp [zeros]),
      window_zeros _ _ _ (by omega), window_zeros _ _ _ (by omega), readDigest_zeros]
theorem wcHeaderPad_witEnc (k : WCT9.Coord) (t : Fin 6) : wcHeaderPad (witEnc N w) k.val t.val = 0 := by
  unfold wcHeaderPad wctChainBlock
  rcases t with ⟨_ | i, ht⟩
  · dsimp only
    rw [show regionBase k.val + (640 - 64 * 0) + 16 = regionBase k.val + 656 by omega,
      wdig_region N w k _ (by omega), region_prefix _ _ _ _ _ _ (by omega) (by omega), readDigest_zeros]
    rfl
  · have hi : i < 5 := by omega
    dsimp only
    rw [show regionBase k.val + (640 - 64 * (i + 1)) + 16 = regionBase k.val + (320 + (64 * (4 - i) + 16)) by omega,
      wdig_region N w k _ (by omega), region_chain _ _ _ _ _ _ (by omega) (by omega),
      show 320 + (64 * (4 - i) + 16) - 320 = 64 * (4 - (⟨i, hi⟩ : Fin 5).val) + 16 by simp,
      chainBytes_window _ _ _ (by omega), window_append_left _ _ _ _ (by simp [zeros]),
      window_zeros _ _ _ (by omega), readDigest_zeros]
    rfl
theorem prev_coord (k : WCT9.Coord) : (Fin.ofNat 9 (k.val + 1 - 1) : WCT9.Coord) = k :=
  Fin.ext (by rw [Fin.val_ofNat, Nat.add_sub_cancel, Nat.mod_eq_of_lt k.isLt])
theorem prevSibL_succ (sig : WCT9.Signature) (k : WCT9.Coord) :
    prevSibL N sig (k.val + 1) =
      if (WCT9.child N k).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((sig.openings k).path 6) else zeros 16 := by
  unfold prevSibL; rw [if_neg (by omega), prev_coord]
theorem prevSibZ_succ (sig : WCT9.Signature) (k : WCT9.Coord) :
    prevSibZ N sig (k.val + 1) =
      if (WCT9.child N k).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((sig.openings k).path 6) else zeros 16 := by
  unfold prevSibZ; rw [if_neg (by omega), prev_coord]
/-- Nested FTS (r1-1): the level-5 fold pad of coordinate `k` holds coordinate `k - 1`'s right-slot sibling. -/
theorem wmpad_five_witEnc (k : WCT9.Coord) (c : Nat) :
    wmpad (witEnc N w) k.val c 5 = readDigest (prevSibZ N w.signature k.val) := by
  unfold wmpad authPadOff
  rw [authBase_five, wdig_region N w k _ (by omega),
    region_top _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega), Nat.add_sub_cancel_left,
    topBlock_pad _ _ _ (prevSibZ_length _ _ _)]
/-- Nested FTS (r1-1): the leaf pad of coordinate `k` holds coordinate `k - 1`'s left-slot sibling. -/
theorem wleafPad_prev_witEnc (k : WCT9.Coord) :
    wleafPad (witEnc N w) k.val = readDigest (prevSibL N w.signature k.val) := by
  unfold wleafPad wctLeafBlock
  rw [show regionBase k.val + 688 + 32 = regionBase k.val + 720 by omega, wdig_region N w k _ (by omega),
    region_leaf _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega) (by omega), show 720 - 688 = 32 from rfl,
    leafBytes_window_pad _ _ (prevSibL_length _ _ _)]
theorem wmpad_start_witEnc (c : Nat) : wmpad (witEnc N w) 0 c 5 = 0 :=
  (wmpad_five_witEnc N w 0 c).trans (by unfold prevSibZ; rw [if_pos (show (0 : WCT9.Coord).val = 0 from rfl), readDigest_zeros])
theorem wleafPad_witEnc : wleafPad (witEnc N w) 0 = 0 :=
  (wleafPad_prev_witEnc N w 0).trans (by unfold prevSibL; rw [if_pos (show (0 : WCT9.Coord).val = 0 from rfl), readDigest_zeros])
theorem wctStart_witEnc : wctStart (witEnc N w) = (0, 0) := by
  unfold wctStart; rw [wleafPad_witEnc, wmpad_start_witEnc]
/-- Nested FTS (r1-1): the supplied top sibling of coordinate `k` (level 6) sits in coordinate `k + 1`'s region, or in
the header for `k = 8`. -/
theorem wtop_witEnc (k : WCT9.Coord) :
    wdig (witEnc N w) (topSlot k.val (WCT9.child N k).val) = (w.signature.openings k).path 6 := by
  have hk := k.isLt
  by_cases h8 : k.val = 8
  · obtain rfl : k = 8 := Fin.ext h8
    by_cases h0 : (WCT9.child N 8).val / 2 ^ 6 % 2 = 0
    · rw [show topSlot (8 : WCT9.Coord).val (WCT9.child N 8).val = 144 by
          unfold topSlot regionBase; rw [if_pos h0]; rfl,
        wdig_witEnc, win_header _ _ _ _ (by omega), headerBytes_eq,
        if_neg (show ¬((WCT9.child N 8).val / 2 ^ 6 % 2 = 1) by omega), if_pos h0,
        window_append_right _ _ _ _ (by simp [zeros]), window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
        show 144 - (zeros 16).length - (zeros 8 ++ bytesLE 8 (1 : BitVec 64)).length - (bytesLE 4 (w.counters 3)).length - ((zeros 68 ++ (bytesLE 8 w.topHint ++ zeros 32))).length = 0
          by simp [zeros, bytesLE_length],
        window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
    · have h1 : (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 := by omega
      rw [show topSlot (8 : WCT9.Coord).val (WCT9.child N 8).val = 0 by
          unfold topSlot regionBase; rw [if_neg h0]; rfl,
        wdig_witEnc, win_header _ _ _ _ (by omega), headerBytes_eq, if_pos h1,
        window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
        Correctness.readDigest_bytesLE]
  · have hk' : k.val + 1 < 9 := by omega
    by_cases h0 : (WCT9.child N k).val / 2 ^ 6 % 2 = 0
    · rw [show topSlot k.val (WCT9.child N k).val = regionBase (⟨k.val + 1, hk'⟩ : WCT9.Coord).val + 864 by
          unfold topSlot regionBase; rw [if_pos h0]; dsimp only; omega,
        wdig_region N w _ _ (by omega), region_top _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega),
        show 864 - 832 = 32 from rfl, topBlock_pad _ _ _ (prevSibZ_length _ _ _)]
      show readDigest (prevSibZ N w.signature (k.val + 1)) = _
      rw [prevSibZ_succ, if_pos h0, Correctness.readDigest_bytesLE]
    · have h1 : (WCT9.child N k).val / 2 ^ 6 % 2 = 1 := by omega
      rw [show topSlot k.val (WCT9.child N k).val = regionBase (⟨k.val + 1, hk'⟩ : WCT9.Coord).val + 720 by
          unfold topSlot regionBase; rw [if_neg h0]; dsimp only; omega,
        wdig_region N w _ _ (by omega), region_leaf _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega) (by omega),
        show 720 - 688 = 32 from rfl, leafBytes_window_pad _ _ (prevSibL_length _ _ _)]
      show readDigest (prevSibL N w.signature (k.val + 1)) = _
      rw [prevSibL_succ, if_pos h1, Correctness.readDigest_bytesLE]
theorem wsib_witEnc (k : WCT9.Coord) (l : Fin 7) :
    wsib (witEnc N w) k.val (WCT9.child N k).val l.val = (w.signature.openings k).path l := by
  have hc := (WCT9.child N k).isLt
  unfold wsib
  rcases l with ⟨l, hl⟩
  dsimp only
  by_cases h5 : l < 5
  · rw [if_pos (by omega), wdig_region N w k _ (by have := auth_sib_bound _ hc l h5; omega),
      region_merkle _ _ _ _ _ _ (auth_sib_bound _ hc l h5), merkleBytes_sib hc _ ⟨l, h5⟩,
      Correctness.readDigest_bytesLE]
    rfl
  · by_cases h6 : l = 5
    · subst h6
      have hs : sibOff ((WCT9.child N k).val / 2 ^ 5 % 2) ≤ 48 := by unfold sibOff; split <;> omega
      rw [if_pos (by omega), show authSibOff (WCT9.child N k).val 5 = 832 + sibOff ((WCT9.child N k).val / 2 ^ 5 % 2) by
          unfold authSibOff; rw [if_pos (by omega), authBase_five],
        wdig_region N w k _ (by omega), region_top _ _ _ _ (prevSibL_length _ _ _) _ _ (by omega),
        Nat.add_sub_cancel_left, topBlock_sib _ _ _ (prevSibZ_length _ _ _), Correctness.readDigest_bytesLE]
      rfl
    · obtain rfl : l = 6 := by omega
      rw [if_neg (by omega), wtop_witEnc]
      rfl
theorem wmpad_witEnc (k : WCT9.Coord) (l : Nat) (hl : l < 5) : wmpad (witEnc N w) k.val (WCT9.child N k).val l = 0 := by
  have hc := (WCT9.child N k).isLt
  by_cases hp : authPadOff (WCT9.child N k).val l = 320
  · unfold wmpad
    rw [hp]
    have hz := congrArg Prod.fst (wcpads_witEnc N w k (5 : Fin 6))
    simpa [wcpads, wctChainBlock] using hz
  · have hb : authPadOff (WCT9.child N k).val l + 16 ≤ 320 :=
      (auth_pad_bound _ hc l hl).resolve_right hp
    unfold wmpad
    rw [wdig_region N w k _ (by omega),
      region_merkle _ _ _ _ _ _ hb, merkleBytes_pad hc _ hl hb, readDigest_zeros]
theorem wmhpad_witEnc (k : WCT9.Coord) (l : Nat) : wmhpad (witEnc N w) k.val (WCT9.child N k).val l = 0 := by
  have hc := (WCT9.child N k).isLt
  unfold wmhpad
  split
  · rename_i hl
    have hb := auth_tw_bound _ hc l hl
    rw [Nat.add_assoc, wdig_region N w k _ (by omega), region_merkle _ _ _ _ _ _ hb, merkleBytes_tw hc _ hl hb,
      readDigest_zeros]
    rfl
  · rfl
end fields
theorem witDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : witDecP N (witEnc N w) = w := by
  obtain ⟨⟨rho, openings, layers⟩, dc, ctr, hint⟩ := w
  unfold witDecP
  simp only [WCT9.Witness.mk.injEq, WCT9.Signature.mk.injEq]
  refine ⟨⟨wrho_witEnc N _, funext fun k => ?_, funext fun lay => ?_⟩, wdc_witEnc N _,
    (funext fun lay => wbcCtr_witEnc N _ lay),
    SigGolfCandidate.Choice.Witness.topHint_roundtrip N _⟩
  · have hv := fun t => wreveal_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr, hint⟩ k t
      (WCT9.wordDigit (WCT9.rank N k) t)
    have hp := fun l => wsib_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr, hint⟩ k l
    simp only at hv hp
    rcases ho : openings k with ⟨vals, path⟩
    rw [ho] at hv hp
    simp only [WCT9.Opening.mk.injEq]
    exact ⟨funext hv, funext hp⟩
  · exact SigGolfCandidate.T3M.LayerSignature.ext' (funext fun i => wvalue_witEnc N _ lay i)
      (funext fun j => wpath_witEnc N _ lay j)
theorem win_endpointBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (endpointBytes sig lay) (16 * i.val) 16 = bytesLE 16 ((sig.layers lay).values i) := by
  have h := window_flatMap_const (List.finRange (chainCount lay))
    (fun j => bytesLE 16 ((sig.layers lay).values j)) 16 (fun j => bytesLE_length _ _)
    i.val (by simpa using i.isLt) 0 16 (by omega)
  simpa [endpointBytes, window_full _ _ (bytesLE_length _ _)] using h

theorem win_leafBufferBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (leafBufferBytes sig lay)
      (if lay = 0 then 32 + 16 * i.val else if i.val = 0 then 0 else 16 + 16 * i.val) 16 =
      bytesLE 16 ((sig.layers lay).values i) := by
  have hi := i.isLt
  have hc : 0 < chainCount lay := by fin_cases lay <;> decide
  unfold leafBufferBytes
  by_cases ht : lay = 0
  · rw [if_pos ht, if_pos ht]
    rw [window_append_left _ _ _ _ (by simp [zeros, endpointBytes_length]; omega),
      window_append_right _ _ _ _ (by simp [zeros])]
    simpa [zeros] using win_endpointBytes sig lay i
  · rw [if_neg ht, if_neg ht]
    have htlen : ((endpointBytes sig lay).take 16).length = 16 := by
      rw [List.length_take, endpointBytes_length, Nat.min_eq_left (by omega)]
    by_cases hz : i.val = 0
    · rw [if_pos hz]
      rw [window_append_left _ _ _ _ (by simp [htlen, zeros]),
        window_append_left _ _ _ _ (by simp [htlen, zeros]),
        window_append_left _ _ _ _ (by rw [htlen]), window_take _ _ _ _ (by omega)]
      simpa [hz] using win_endpointBytes sig lay i
    · rw [if_neg hz]
      rw [window_append_left _ _ _ _ (by
        simp only [List.length_append, htlen, zeros, List.length_replicate, List.length_drop, endpointBytes_length]
        omega), window_append_right _ _ _ _ (by
        simp only [List.length_append, htlen, zeros, List.length_replicate]
        omega)]
      simp only [List.length_append, htlen, zeros, List.length_replicate]
      unfold window
      rw [List.drop_drop, show 16 + (16 + 16 * i.val - (16 + 16)) = 16 * i.val by omega]
      exact win_endpointBytes sig lay i

theorem win_leafBuffersBytes (sig : WCT9.Signature) (lay : Layer) (i : Fin (chainCount lay)) :
    window (leafBuffersBytes sig) (leafBufferSlot lay i.val - 21680) 16 =
      bytesLE 16 ((sig.layers lay).values i) := by
  have hi := i.isLt
  have hidx : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have hget : (List.finRange 4).reverse[3 - lay.val]'hidx = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes sig l).length)).sum = leafBufferBase lay - 21680 := by
    simp only [leafBufferBytes_length]
    fin_cases lay <;> decide
  let off := if lay = 0 then 32 + 16 * i.val else if i.val = 0 then 0 else 16 + 16 * i.val
  have hb : off + 16 ≤ (leafBufferBytes sig lay).length := by
    rw [leafBufferBytes_length]
    fin_cases lay <;> norm_num [off, leafBufferLen, chainCount] at *
    all_goals (try split_ifs) <;> omega
  have h := window_flatMap (List.finRange 4).reverse (leafBufferBytes sig)
    (3 - lay.val) hidx off 16 (by simpa only [hget] using hb)
  rw [hp, hget] at h
  have hbase : 21680 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hoff : leafBufferSlot lay i.val - 21680 = leafBufferBase lay - 21680 + off := by
    unfold leafBufferSlot
    change leafBufferBase lay + off - 21680 = leafBufferBase lay - 21680 + off
    omega
  rw [hoff]
  exact h.trans (win_leafBufferBytes sig lay i)
theorem win_leafBuffer (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (o n : Nat) (h : o + n ≤ leafBufferLen lay) :
    window (witList N w) (leafBufferBase lay + o) n = window (leafBufferBytes w.signature lay) o n := by
  have hidx : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have hget : (List.finRange 4).reverse[3 - lay.val]'hidx = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes w.signature l).length)).sum = leafBufferBase lay - 21680 := by
    simp only [leafBufferBytes_length]
    fin_cases lay <;> decide
  have hb : o + n ≤ (leafBufferBytes w.signature lay).length := by rw [leafBufferBytes_length]; exact h
  have key := window_flatMap (List.finRange 4).reverse (leafBufferBytes w.signature) (3 - lay.val) hidx o n
    (by simpa only [hget] using hb)
  rw [hp, hget] at key
  have hbase : 21680 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hend : leafBufferBase lay + leafBufferLen lay ≤ 24800 := by fin_cases lay <;> decide
  rw [witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
    omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega),
    show leafBufferBase lay + o - (176 + 8080 + 13424) = leafBufferBase lay - 21680 + o by omega]
  exact key
/-- C3 (FULL): the honest top leaf pad is zero. -/
theorem wtopLeafPad_witEnc (N : HashOutput) (w : WCT9.Witness) : wtopLeafPad (witEnc N w) = 0 := by
  unfold wtopLeafPad
  rw [wdig_witEnc, show leafBufferBase 0 = leafBufferBase 0 + 0 from rfl,
    win_leafBuffer N w 0 0 16 (by decide)]
  unfold leafBufferBytes
  rw [if_pos rfl, window_append_left _ _ _ _ (by simp only [List.length_append, zeros, List.length_replicate]; omega),
    window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega), readDigest_zeros]
/-- C3 (FULL): the honest leaf tweak high words are zero. -/
theorem wleafHigh_witEnc (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : wleafHigh (witEnc N w) lay = 0 := by
  unfold wleafHigh
  rw [wdig_witEnc, win_leafBuffer N w lay 16 16 (by fin_cases lay <;> decide)]
  have hz : window (leafBufferBytes w.signature lay) 16 16 = zeros 16 := by
    unfold leafBufferBytes
    split
    · rw [window_append_left _ _ _ _ (by simp only [List.length_append, zeros, List.length_replicate]; omega),
        window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega)]
    · have hc : 1 ≤ chainCount lay := by fin_cases lay <;> decide
      have htlen : ((endpointBytes w.signature lay).take 16).length = 16 := by
        rw [List.length_take, endpointBytes_length]; omega
      rw [window_append_left _ _ _ _ (by
          simp only [List.length_append, htlen, zeros, List.length_replicate, List.length_drop, endpointBytes_length]
          omega),
        window_append_left _ _ _ _ (by simp only [List.length_append, htlen, zeros, List.length_replicate]; omega),
        window_append_right _ _ _ _ (by rw [htlen]), htlen, window_zeros _ _ _ (by omega)]
  rw [hz, readDigest_zeros]
  decide
theorem wbuffer_witEnc (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (i : Fin (chainCount lay)) :
    wdig (witEnc N w) (leafBufferSlot lay i.val) = (w.signature.layers lay).values i := by
  have hb := leafBufferSlot_bounds lay i.val i.isLt
  rw [wdig_witEnc, witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
    omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega)]
  rw [show 176 + 8080 + 13424 = 21680 by decide,
    win_leafBuffersBytes, Correctness.readDigest_bytesLE]
theorem padDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : padDecP N (witEnc N w) = 0 := by
  unfold padDecP
  show Pads.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = Pads.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  congr 1
  · funext k t; exact wcpads_witEnc N w k t
  · funext k t; exact wcHeaderPad_witEnc N w k t
  · funext k l; split
    · rename_i hl
      rcases hl with hl | ⟨hl5, hk0⟩
      · exact wmpad_witEnc N w k l.val hl
      · rw [hk0, hl5]; exact wmpad_start_witEnc N w _
    · rfl
  · funext k l; exact wmhpad_witEnc N w k l.val
  · funext k; split
    · exact wleafPad_witEnc N w
    · rfl
  · funext lay i; exact wchainPads_witEnc N w lay i
  · funext lay j; split
    · rename_i h; exact wmerklePad_witEnc N w lay j h
    · rfl
  · funext lay i; exact wchainHeaderPad_witEnc N w lay i
  · funext lay; exact wbcPad_witEnc N w lay
  · exact wright3_witEnc N w
  · funext lay i
    rw [wvalue_witEnc, wbuffer_witEnc, BitVec.xor_self]
    rfl
  · funext lay j; split
    · rename_i h; exact wmerkleHigh_witEnc N w lay j h
    · rfl
  · exact wtopLeafPad_witEnc N w
  · funext lay; exact wleafHigh_witEnc N w lay
  · funext lay; rw [wbcHigh_witEnc N w lay]; decide
end ClaudeWCT.W9.T3M
end
section
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (eval_countCalls_bind_congr eval_countCalls_fst eval_map)
set_option linter.unusedSimpArgs false
def honestProgramCore (message : Message) : M Bool := do
  let keys ← WCT9.Rev3.keygen
  let sig ← WCT9.Rev3.sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← WCT9.Rev3.expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => WCT9.Rev3.verify message keys.1 witness
def honestProgramB (message : Message) : M Bool := do
  let keys ← WCT9.Rev3.keygen
  let sig ← WCT9.Rev3.sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let wb ← expandB message keys.1 sig
    match wb with
    | none => pure false
    | some wb => verifyP message keys.1 wb
def ExpandEqExpandN : Prop := ∀ (m : Message) (pk : Digest) (σ : WCT9.Signature),
  WCT9.Rev3.expand m pk σ = Option.map Prod.snd <$> expandN m pk σ
def VerifyPWitEncEval : Prop := ∀ (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness),
  evalWithAnswerFn answers (expandN m pk σ) = some (N, w) →
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w))
def HonestBEval : Prop := ∀ (answers : Correctness.Answers) (m : Message),
  evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m)
theorem expand_eq_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    WCT9.Rev3.expand m pk σ = Option.map Prod.snd <$> expandN m pk σ := rfl
theorem expandEqExpandN_holds : ExpandEqExpandN := expand_eq_expandN
theorem expandN0_eq (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    expandN0 m pk σ = WCT9.expandWithN WCT9.digestAttemptLimit m pk σ := rfl
structure ExpandFacts0 (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) : Prop where
  sig : w.signature = σ
  dc : w.digestCounter.toNat < WCT9.digestAttemptLimit
  digest : evalWithAnswerFn answers (digest σ.rho m w.digestCounter) = N
  adm : WCT9.admissible N = true
  cap : WCT9.capOk N = true
theorem expandN0_facts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN0 m pk σ) = some (N, w)) :
    ExpandFacts0 answers m pk σ N w := by
  simp only [expandN0, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (WCT9.digestSearch σ.rho m 0 WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (WCT9.expandLayersBC σ (WCT9.digestIndex output) 4
          (.pair (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex output) output)).1
            (evalWithAnswerFn answers (WCT9.recoverFts σ (WCT9.digestIndex output) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters, topHint⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            obtain ⟨_, hcounter, houtput, hadm⟩ := WCT9.digestSearch_some_good answers σ.rho m
              WCT9.digestAttemptLimit 0 counter output (by unfold WCT9.digestAttemptLimit; norm_num) hd
            exact ⟨rfl, by simpa using hcounter, houtput, WCT9.admissible_of_producer hadm,
              (WCT9.capOk_iff output).2 ((WCT9.producerAdmissible_iff output).1 hadm).2⟩
/-- An H2 expansion is the old expansion of a completion `fillTop σ c`. -/
theorem expandN_completion (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    ∃ c, c < 2 ^ 16 ∧ w.signature = WCT9.fillTop σ c ∧
      evalWithAnswerFn answers (expandN0 m pk (WCT9.fillTop σ c)) = some (N, w) :=
  WCT9.eval_expandS answers _ m pk σ N w he
structure ExpandFacts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) : Prop where
  rho : w.signature.rho = σ.rho
  fill : ∃ c, c < 2 ^ 16 ∧ w.signature = WCT9.fillTop σ c ∧
    evalWithAnswerFn answers (expandN0 m pk (WCT9.fillTop σ c)) = some (N, w)
  dc : w.digestCounter.toNat < WCT9.digestAttemptLimit
  digest : evalWithAnswerFn answers (digest σ.rho m w.digestCounter) = N
  adm : WCT9.admissible N = true
  cap : WCT9.capOk N = true
theorem expandN_facts (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    ExpandFacts answers m pk σ N w := by
  obtain ⟨c, hc, hsig, h0⟩ := expandN_completion answers m pk σ N w he
  have F := expandN0_facts answers m pk _ N w h0
  exact ⟨by rw [hsig]; rfl, ⟨c, hc, hsig, h0⟩, F.dc, F.digest, F.adm, F.cap⟩
theorem verifyP_witEnc_eval0 (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN0 m pk σ) = some (N, w)) :
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w)) := by
  have F := expandN0_facts answers m pk σ N w he
  have hv : verifyP m pk (witEnc N w) =
      digest w.signature.rho m w.digestCounter >>= verifyTailP pk (witEnc N w) := by
    rw [verifyP_eq_tail]
    unfold digestP
    rw [wdc_witEnc, wrho_witEnc, if_neg (by have := w.digestCounter.isLt; unfold WCT9.digestVerifyWindow; omega), bind_map_left]
  have hw : WCT9.Rev3.verify m pk w =
      digest w.signature.rho m w.digestCounter >>= fun N' => verifyPadsTail pk N' w 0 := by
    rw [← verifyPads_zero]
    unfold verifyPads
    rw [if_neg (by have := F.dc; omega)]
  rw [hv, hw]
  apply eval_countCalls_bind_congr
  rw [F.sig, F.digest, verifyTailP_shaped pk N _ F.adm, witDecP_witEnc, padDecP_witEnc]
theorem verifyP_witEnc_eval (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature)
    (N : HashOutput) (w : WCT9.Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, w)) :
    evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w))) =
      evalWithAnswerFn answers (Cost.countCalls (WCT9.Rev3.verify m pk w)) := by
  obtain ⟨c, -, -, h0⟩ := expandN_completion answers m pk σ N w he
  exact verifyP_witEnc_eval0 answers m pk _ N w h0
theorem verifyPWitEncEval_holds : VerifyPWitEncEval := verifyP_witEnc_eval
theorem expandN_proj (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    expandN m pk (WCT9.proj σ) = expandN m pk σ := by
  unfold expandN WCT9.expandS
  rw [WCT9.proj_proj]
theorem expandB_proj (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    expandB m pk (WCT9.proj σ) = expandB m pk σ := by
  unfold expandB; rw [expandN_proj]
theorem eval_expandB (answers : Correctness.Answers) (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    evalWithAnswerFn answers (expandB m pk σ) =
      (evalWithAnswerFn answers (expandN m pk σ)).map (fun x => witEnc x.1 x.2) := by
  unfold expandB; rw [eval_map]
theorem honestB_eval (answers : Correctness.Answers) (m : Message) :
    evalWithAnswerFn answers (honestProgramB m) = evalWithAnswerFn answers (honestProgramCore m) := by
  unfold honestProgramB honestProgramCore
  simp only [evalWithAnswerFn_bind]
  cases hs : evalWithAnswerFn answers (WCT9.Rev3.sign (evalWithAnswerFn answers WCT9.Rev3.keygen).2 m) with
  | none => rfl
  | some sig =>
      simp only []
      rw [expand_eq_expandN, evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_map, eval_expandB]
      cases hx : evalWithAnswerFn answers (expandN m (evalWithAnswerFn answers WCT9.Rev3.keygen).1 sig) with
      | none => rfl
      | some x =>
          obtain ⟨N, w⟩ := x
          simp only [Option.map_some]
          have := verifyP_witEnc_eval answers m _ sig N w hx
          have h1 := congrArg Prod.fst this
          rwa [eval_countCalls_fst, eval_countCalls_fst] at h1
theorem honestBEval_holds : HonestBEval := honestB_eval
end ClaudeWCT.W9.T3M
end
