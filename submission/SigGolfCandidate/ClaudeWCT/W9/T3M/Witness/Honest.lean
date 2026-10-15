import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Encode
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.TopLayer
import SigGolfCandidate.ClaudeWCT.WCT9.Correctness
import SigGolfCandidate.ClaudeWCT.WCT9.Omit

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
theorem wctChainInputP_zero (index coord child t step : Nat) (value : Digest) :
    wctChainInputP index coord child t step 0 0 0 value = WCT9.chainInput index coord child t step value := by
  simp only [wctChainInputP, WCT9.chainInput, WCT9.ftsChainHeader, bytesLE_zero16]
@[simp] theorem wctChainP_zero (index coord child t start count : Nat) (value : Digest) :
    wctChainP index coord child t start count 0 0 0 value = WCT9.chain index coord child t start count value := by
  simp only [wctChainP, WCT9.chain, wctChainInputP_zero]
@[simp] theorem wctNodeHashP_zero (coord index heap : Nat) (left right : Digest) :
    wctNodeHashP coord index heap left 0 0 right = WCT9.wctNodeHash coord index heap left right := by
  simp only [wctNodeHashP, SigGolfCandidate.T3M.SecurityInputs.nodeInputPH_zero, WCT9.wctNodeHash,
    ← SigGolfCandidate.T3M.SecurityInputs.nodeHashP_eq_shortHash, nodeHashP_zero]
theorem recoverCoordinateP_zero (sig : WCT9.Signature) (index : Nat) (output : HashOutput) (coord : WCT9.Coord)
    (prev : Digest × Digest) :
    recoverCoordinateP sig 0 index output coord prev = WCT9.recoverCoordinate sig index output coord prev := by
  simp only [recoverCoordinateP, WCT9.recoverCoordinate, Pads.zero_wctChain, Pads.zero_wctChainHigh,
    Pads.zero_wctMerkle, Pads.zero_wctMerkleHigh, Pads.zero_wctLeaf, WCT9.leafHashP_zero, wctChainP_zero,
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
    ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay tree leaf msg counter 0 0) =
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
theorem recoverLayerPairP_zero (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hindex : index < 2 ^ 31) :
    recoverLayerPairP sig 0 index lay digits = WCT9.recoverLayerPair sig index lay digits := by
  simp only [recoverLayerPairP, WCT9.recoverLayerPair, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    chainP_zero_route _ _ _ _ _ hindex, Pads.zero_merkle', nodeHashP_zero]
private theorem mapM_congr_guard {α β : Type} {f g : α → M β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
      rw [List.mapM_cons, List.mapM_cons, h x (by simp),
        mapM_congr_guard l (fun y hy => h y (by simp [hy]))]
theorem recoverLayerPairGuardP_zero (sig : WCT9.Signature) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) (hindex : index < 2 ^ 31) :
    recoverLayerPairGuardP sig 0 index lay answer digits =
      WCT9.recoverLayerPairGuard sig index lay answer digits := by
  simp only [recoverLayerPairGuardP, WCT9.recoverLayerPairGuard, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    recoverLayerPairP_zero _ _ _ _ hindex]
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
    exact chainP_zero_route index lay ⟨i, hi'⟩ _ _ hindex
theorem verifyTopP_zero (sig : WCT9.Signature) (index : Nat) (answer : Digest) (hindex : index < 2 ^ 31) :
    verifyTopP sig 0 index answer = WCT9.verifyTop sig index answer := by
  simp only [verifyTopP, WCT9.verifyTop, Pads.zero_chain', Pads.zero_chainHeader, valueP_zero,
    chainP_zero_route _ _ _ _ _ hindex, Pads.zero_merkle', nodeHashP_zero]
theorem verifyLayersBCP_zero (w : WCT9.Witness) (index : Nat) (hindex : index < 2 ^ 31) : ∀ n msg,
    verifyLayersBCP w 0 index n msg = WCT9.verifyLayersBC w index n msg := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
      intro msg
      simp only [verifyLayersBCP, WCT9.verifyLayersBC, Pads.zero_bc, Pads.zero_bcRight,
        encodingHash_layerEncodingInputP_zero, verifyTopP_zero _ _ _ hindex, recoverLayerPairGuardP_zero _ _ _ _ _ hindex, ih]
      rfl
theorem verifyPads_zero (m : Message) (pk : Digest) (w : WCT9.Witness) :
    verifyPads m pk w 0 = WCT9.Rev3.verify m pk w := by
  unfold verifyPads verifyPadsTail WCT9.Rev3.verify WCT9.verifyWith
  simp only [recoverFtsP_zero, verifyLayersBCP_zero _ _ (WCT9.digestIndex_lt _)]
  rfl
theorem layerP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (hlay : lay.val = 0) :
    layerP w (WCT9.digestIndex N) lay digits =
      recoverLayerP (WCT9.toT3Signature (effectiveSignature (witDecP N w).signature (padDecP N w) digits)) (padDecP N w).toT3 (WCT9.digestIndex N) lay
        digits := by
  unfold layerP recoverLayerP
  simp only [WCT9.toT3Signature, effectiveSignature]
  simp only [valueP_dec]
  simp only [Pads.toT3, padDecP, witDecP, hlay, or_true, if_true]
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
  simp only [hm, valueP_dec]
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
theorem layersBC_dec (N : HashOutput) (w : WBytes) : ∀ n msg,
    layersBC w (WCT9.digestIndex N) n msg =
      verifyLayersBCP (witDecP N w) (padDecP N w) (WCT9.digestIndex N) n msg := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
      intro msg
      unfold layersBC verifyLayersBCP
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
theorem top_path_eq : 16 * pathSlots 0 = 64 * height 0 := rfl
theorem layerRegion_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegion N w lay).length = 16 * pathSlots lay + 64 * chainCount lay := by
  unfold layerRegion; split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    rw [layerBytes_length]; rfl
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
    ((List.finRange 4).flatMap (layerRegion N w)).length = 13456 := by
  simp only [List.length_flatMap, layerRegion_length]
  decide
theorem witList_length_eq (N : HashOutput) (w : WCT9.Witness) : (witList N w).length = 24864 := by
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
machine still writes whole words); the witness is its first `wsize = 24860` bytes. -/
theorem witList_readLE_lt (N : HashOutput) (w : WCT9.Witness) : readLE (witList N w) < 2 ^ (8 * 24860) := by
  have hsplit : witList N w = ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)) ++
      zeros 4 := by
    simp only [witList, tailBytes, List.append_assoc]
  have hlen : ((headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)).length =
      24860 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, leafBuffersBytes_length,
      bytesLE_length, zeros, List.length_replicate]
  have hz : readLE (zeros 4) = 0 := by decide
  have h256 : ∀ n : Nat, (256 : Nat) ^ n = 2 ^ (8 * n) := fun n => by rw [pow_mul]; norm_num
  rw [hsplit, readLE_append, hz, Nat.mul_zero, Nat.add_zero, ← h256, ← hlen]
  exact SigGolfCandidate.T3M.readLE_lt _
theorem wdig_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wdig (witEnc N w) off = readDigest (window (witList N w) off 16) := by
  unfold wdig witEnc readDigest window
  exact extract_readLE_lt (witList N w) 24860 (witList_readLE_lt N w) off 16
theorem wle32_witEnc (N : HashOutput) (w : WCT9.Witness) (off : Nat) :
    wle32 (witEnc N w) off = BitVec.ofNat 32 (readLE (window (witList N w) off 4)) := by
  unfold wle32 witEnc window
  exact extract_readLE_lt (witList N w) 24860 (witList_readLE_lt N w) off 4
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
/-- The header as a slot, 16 zero bytes, the L3 counter, 108 zero bytes, the R9 slot and 16 zero bytes. -/
theorem headerBytes_eq : headerBytes N w =
    (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
      (zeros 16 ++ (bytesLE 4 (w.counters 3) ++ (zeros 108 ++
        ((if (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
          zeros 16)))) := by
  simp only [headerBytes, List.append_assoc]
theorem win_header_mid (off n : Nat) (h0 : 36 ≤ off) (h : off + n ≤ 144) :
    window (witList N w) off n = zeros n := by
  rw [win_header N w off n (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_right _ _ _ _ (by simp [zeros]; omega),
    window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]; omega)]
  exact window_zeros _ _ _ (by simp [bytesLE_length, zeros]; omega)
theorem wctr3_witEnc : wle32 (witEnc N w) 32 = w.counters 3 := by
  rw [wle32_witEnc, win_header _ _ _ _ (by omega), headerBytes_eq,
    window_append_right _ _ _ _ (by rw [ite_slot_length]; omega), ite_slot_length,
    window_append_right _ _ _ _ (by simp [zeros]),
    window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]),
    show 32 - 16 - (zeros 16).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wpad3_witEnc : (witEnc N w).extractLsb' (8 * 36) 96 = 0 := by
  have h := extract_readLE_lt (witList N w) 24860 (witList_readLE_lt N w) 36 12
  unfold witEnc
  rw [show (96 : Nat) = 8 * 12 from rfl, h, show ((witList N w).drop 36).take 12 = window (witList N w) 36 12 from rfl,
    win_header_mid _ _ _ _ le_rfl (by omega)]
  rfl
theorem wright3_witEnc : wdig (witEnc N w) 48 = 0 := by
  rw [wdig_witEnc, win_header_mid _ _ _ _ (by omega) (by omega), readDigest_zeros]
end header
section tail
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_tail (off n : Nat) (h : off + n ≤ 32) :
    window (witList N w) (24832 + off) n = window (tailBytes w) off n := by
  rw [witList_split, window_append_right _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_right _ _ _ _ (by rw [leafBuffersBytes_length]; omega), leafBuffersBytes_length]
  exact congrArg (fun k : Nat => window (tailBytes w) k n)
    (show 24832 + off - (176 + 8080 + 13456) - 3120 = off by omega)
theorem wrho_witEnc : wrho (witEnc N w) = w.signature.rho := by
  unfold wrho rhoOff
  rw [wdig_witEnc, show (24832 : Nat) = 24832 + 0 from rfl, win_tail _ _ _ _ (by omega)]
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
  rw [wle32_witEnc, show (24856 : Nat) = 24832 + 24 from rfl, win_tail _ _ _ _ (by omega)]
  have h : window (tailBytes w) 24 4 = window (window (tailBytes w) 24 8) 0 4 := by
    unfold window; rw [List.drop_zero, List.take_take, Nat.min_eq_left (by omega)]
  rw [h, tail_counter_window, window_append_left _ _ _ _ (by simp [bytesLE_length]),
    window_full _ _ (bytesLE_length _ _), readLE_bytesLE_32]
theorem wdcWord_witEnc : (wdcWord (witEnc N w)).toNat = w.digestCounter.toNat := by
  unfold wdcWord witEnc dcOff
  rw [show (64 : Nat) = 8 * 8 from rfl, extract_readLE_lt (witList N w) 24860 (witList_readLE_lt N w) 24856 8,
    show ((witList N w).drop 24856).take 8 = window (witList N w) (24832 + 24) 8 from rfl,
    win_tail _ _ _ _ (by omega), tail_counter_window, readLE_append, bytesLE_length,
    Correctness.readLE_bytesLE]
  have hz : readLE (zeros 4) = 0 := by decide
  rw [hz, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans w.digestCounter.isLt (by decide))
end tail
theorem layerBase_ge (lay : Layer) : 8256 ≤ layerBase lay := by
  fin_cases lay <;> simp [layerBase]
theorem layerEnd_le (lay : Layer) : layerBase lay + (16 * pathSlots lay + 64 * chainCount lay) ≤ 21712 := by
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
    rw [top_path_eq, ← Nat.add_assoc]
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
      (bytesLE 4 ctr).getD (p - lowerCtrSlot lay leaf) 0 else 0 := by
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
    unfold lowerCtrSlot
    rw [if_neg (by omega)]
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
      unfold lowerCtrSlot; omega), if_neg (by omega)]
  unfold lowerPathBytes
  rw [window_map_range _ _ _ _ (by unfold lowerCtrSlot; omega),
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
theorem win_topMerkle (N : HashOutput) (w : WCT9.Witness) (j : Fin (height 0)) (o : Nat) (ho : o + 16 ≤ 64) :
    window (witList N w) (merkleBlock 0 (route (WCT9.digestIndex N) 0).1 j.val + o) 16 =
      window (if (route (WCT9.digestIndex N) 0).1 / 2 ^ j.val % 2 = 1 then
          bytesLE 16 ((w.signature.layers 0).path j) ++ zeros 48
        else zeros 48 ++ bytesLE 16 ((w.signature.layers 0).path j)) o 16 := by
  have hj := j.isLt
  unfold merkleBlock
  rw [if_pos (show (0 : Layer).val = 0 from rfl), Nat.add_assoc, win_layerRegion _ _ _ _ _ (by
      change 64 * (height 0 - 1 - j.val) + o + 16 ≤ 768 + 3456
      have : height (0 : Layer) = 12 := rfl
      omega)]
  unfold layerRegion
  rw [if_pos (show (0 : Layer).val = 0 from rfl)]
  exact layerBytes_merkle _ _ _ j o ho
section t3b
variable (N : HashOutput) (w : WCT9.Witness)
theorem wpath_witEnc (lay : Layer) (j : Fin (height lay)) :
    wpath (witEnc N w) lay (route (WCT9.digestIndex N) lay).1 j.val = (w.signature.layers lay).path j := by
  by_cases hlay : lay.val = 0
  · have hl : lay = 0 := Fin.ext hlay
    subst hl
    unfold wpath
    rw [wdig_witEnc, win_topMerkle _ _ _ _ (by unfold sibOff; split <;> omega)]
    unfold sibOff
    split
    · rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _),
        Correctness.readDigest_bytesLE]
    · rw [window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
        window_full _ _ (bytesLE_length _ _), Correctness.readDigest_bytesLE]
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
    unfold wmerklePad
    rw [wdig_witEnc, win_topMerkle _ _ _ _ (by omega)]
    split
    · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length]),
        readDigest_zeros]
    · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_zeros _ _ _ (by omega),
        readDigest_zeros]
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
      extract_readLE_lt (witList N w) 24860 (witList_readLE_lt N w) _ 12,
      show ((witList N w).drop (layerBase (upLayer lay) +
          lowerCtrSlot (upLayer lay) (route (WCT9.digestIndex N) (upLayer lay)).1 + 4)).take 12 =
        window (witList N w) (layerBase (upLayer lay) +
          (lowerCtrSlot (upLayer lay) (route (WCT9.digestIndex N) (upLayer lay)).1 + 4)) 12 by
        unfold window; rw [Nat.add_assoc],
      win_lowerPath _ _ _ hv _ _ (by unfold lowerCtrSlot; omega), lowerPath_rowPad hv hleaf]
    rfl
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
theorem auth_tw_bound : ∀ c < 128, ∀ l < 4, c / 2 ^ l % 2 = 1 → authBase c l + 16 + 16 ≤ 320 := by decide
theorem auth_tw_disjoint : ∀ c < 128, ∀ l < 4, c / 2 ^ l % 2 = 1 → ∀ l' < 5,
    authBase c l + 16 + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authBase c l + 16 := by decide
theorem merkleBytes_tw {c : Nat} (hc : c < 128) (op : WCT9.Opening) {l : Nat} (hl : l < 4) (hbit : c / 2 ^ l % 2 = 1)
    (hb : authBase c l + 16 + 16 ≤ 320) :
    window (merkleBytes c op) (authBase c l + 16) 16 = zeros 16 := by
  unfold merkleBytes
  rw [window_map_range _ _ _ _ hb,
    List.map_congr_left (fun i hi => authByte5_none op (fun l' => by
      have := auth_tw_disjoint c hc l hl hbit l'.val l'.isLt
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
        window_append_right _ _ _ _ (by simp [zeros]), window_append_right _ _ _ _ (by simp [zeros]),
        window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
        window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
        show 144 - (zeros 16).length - (zeros 16).length - (bytesLE 4 (w.counters 3)).length - (zeros 108).length = 0
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
    have hb := auth_tw_bound _ hc l hl.1 hl.2
    rw [Nat.add_assoc, wdig_region N w k _ (by omega), region_merkle _ _ _ _ _ _ hb, merkleBytes_tw hc _ hl.1 hl.2 hb,
      readDigest_zeros]
    rfl
  · rfl
end fields
theorem witDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : witDecP N (witEnc N w) = w := by
  obtain ⟨⟨rho, openings, layers⟩, dc, ctr⟩ := w
  unfold witDecP
  simp only [WCT9.Witness.mk.injEq, WCT9.Signature.mk.injEq]
  refine ⟨⟨wrho_witEnc N _, funext fun k => ?_, funext fun lay => ?_⟩, wdc_witEnc N _,
    funext fun lay => wbcCtr_witEnc N _ lay⟩
  · have hv := fun t => wreveal_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr⟩ k t
      (WCT9.wordDigit (WCT9.rank N k) t)
    have hp := fun l => wsib_witEnc N ⟨⟨rho, openings, layers⟩, dc, ctr⟩ k l
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
    window (leafBuffersBytes sig) (leafBufferSlot lay i.val - 21712) 16 =
      bytesLE 16 ((sig.layers lay).values i) := by
  have hi := i.isLt
  have hidx : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have hget : (List.finRange 4).reverse[3 - lay.val]'hidx = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes sig l).length)).sum = leafBufferBase lay - 21712 := by
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
  have hbase : 21712 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hoff : leafBufferSlot lay i.val - 21712 = leafBufferBase lay - 21712 + off := by
    unfold leafBufferSlot
    change leafBufferBase lay + off - 21712 = leafBufferBase lay - 21712 + off
    omega
  rw [hoff]
  exact h.trans (win_leafBufferBytes sig lay i)
theorem wbuffer_witEnc (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (i : Fin (chainCount lay)) :
    wdig (witEnc N w) (leafBufferSlot lay i.val) = (w.signature.layers lay).values i := by
  have hb := leafBufferSlot_bounds lay i.val i.isLt
  rw [wdig_witEnc, witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
    omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega)]
  rw [show 176 + 8080 + 13456 = 21712 by decide,
    win_leafBuffersBytes, Correctness.readDigest_bytesLE]
theorem padDecP_witEnc (N : HashOutput) (w : WCT9.Witness) : padDecP N (witEnc N w) = 0 := by
  unfold padDecP
  show Pads.mk _ _ _ _ _ _ _ _ _ _ _ = Pads.mk _ _ _ _ _ _ _ _ _ _ _
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
          obtain ⟨root, counters⟩ := layers
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

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def prefixList (p : List UInt8) (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  p ++ (witList N w).drop 8256

def prefixEnc (p : List UInt8) (N : HashOutput) (w : WCT9.Witness) : WBytes :=
  BitVec.ofNat _ (readLE (prefixList p N w))

theorem prefixList_readLE_lt (p : List UInt8) (hp : p.length=8256)
    (N : HashOutput) (w : WCT9.Witness) : readLE (prefixList p N w)<2^(8*24860) := by
  let pre := (headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
      leafBuffersBytes w.signature) ++ (bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter)
  have hs : witList N w=pre++zeros 4 := by simp only [pre,witList,tailBytes,List.append_assoc]
  have hl : pre.length=24860 := by
    simp only [pre,List.length_append,headerBytes_length,wctBytes_length,layers_length,
      leafBuffersBytes_length,bytesLE_length,zeros,List.length_replicate]
  have hh : prefixList p N w=(p++pre.drop 8256)++zeros 4 := by
    rw [prefixList,hs,List.drop_append_of_le_length (by omega),List.append_assoc]
  have hlen : (p++pre.drop 8256).length=24860 := by simp [hp,hl]
  have hz : readLE (zeros 4)=0 := by decide
  have h256 : ∀ n : Nat,(256:Nat)^n=2^(8*n) := fun n=>by rw [pow_mul];norm_num
  rw [hh,readLE_append,hz,Nat.mul_zero,Nat.add_zero,←h256,←hlen]
  exact SigGolfCandidate.T3M.readLE_lt _

theorem prefix_window (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (off k : Nat) (ho : 8256≤off) :
    window (prefixList p N w) off k=window (witList N w) off k := by
  unfold prefixList
  rw [window_append_right _ _ _ _ (by omega),hp]
  unfold window
  rw [List.drop_drop,Nat.add_sub_of_le ho]

theorem wdig_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : 8256≤off) : wdig (prefixEnc p N w) off=wdig (witEnc N w) off := by
  rw [wdig_witEnc]
  have h := extract_readLE_lt (prefixList p N w) 24860 (prefixList_readLE_lt p hp N w) off 16
  change wdig (BitVec.ofNat _ (readLE (prefixList p N w))) off=_
  rw [wdig,h]
  exact congrArg readDigest (prefix_window p hp N w off 16 ho)

theorem wle32_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : 8256≤off) : wle32 (prefixEnc p N w) off=wle32 (witEnc N w) off := by
  rw [wle32_witEnc]
  have h := extract_readLE_lt (prefixList p N w) 24860 (prefixList_readLE_lt p hp N w) off 4
  change wle32 (BitVec.ofNat _ (readLE (prefixList p N w))) off=_
  rw [wle32,h]
  exact congrArg (fun bs=>BitVec.ofNat 32 (readLE bs)) (prefix_window p hp N w off 4 ho)
#print axioms wdig_prefixEnc
#print axioms wle32_prefixEnc
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layerBase_lower (lay : Layer) : 8256≤layerBase lay := by fin_cases lay <;> decide

theorem wrho_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness) :
    wrho (prefixEnc p N w)=w.signature.rho := by
  unfold wrho
  rw [wdig_prefixEnc p hp N w _ (by decide)]
  exact wrho_witEnc N w

theorem wdc_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness) :
    wdc (prefixEnc p N w)=w.digestCounter := by
  unfold wdc
  rw [wle32_prefixEnc p hp N w _ (by decide)]
  exact wdc_witEnc N w

theorem wvalue_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (prefixEnc p N w) lay i.val=(w.signature.layers lay).values i := by
  unfold wvalue
  rw [wdig_prefixEnc p hp N w _ (by have := layerBase_lower lay;unfold chainBlock;omega)]
  exact wvalue_witEnc N w lay i

theorem wpath_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (i : Fin (height lay)) :
    wpath (prefixEnc p N w) lay (route (WCT9.digestIndex N) lay).1 i.val=(w.signature.layers lay).path i := by
  unfold wpath
  rw [wdig_prefixEnc p hp N w _ (by have := layerBase_lower lay;unfold merkleBlock;omega)]
  exact wpath_witEnc N w lay i

theorem wbcCtr_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (hl : lay≠3) : wbcCtr (prefixEnc p N w) (WCT9.digestIndex N) lay=w.counters lay := by
  unfold wbcCtr
  rw [wle32_prefixEnc p hp N w _ (by
    have hn : lay.val≠3 := fun h=>hl (Fin.ext h)
    have := layerBase_lower (upLayer lay)
    unfold bcCounterOff rowBlock
    rw [if_neg hn]
    unfold merkleBlock
    omega)]
  exact wbcCtr_witEnc N w lay
#print axioms wrho_prefixEnc
#print axioms wdc_prefixEnc
#print axioms wvalue_prefixEnc
#print axioms wpath_prefixEnc
#print axioms wbcCtr_prefixEnc
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wbuffer_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wdig (prefixEnc p N w) (leafBufferSlot lay i.val)=(w.signature.layers lay).values i := by
  rw [wdig_prefixEnc p hp N w _ (by have := leafBufferSlot_bounds lay i.val i.isLt;omega)]
  exact wbuffer_witEnc N w lay i

theorem wbcPad_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (lay : Layer) (hl : lay≠3) : wbcPad (prefixEnc p N w) (WCT9.digestIndex N) lay=0 := by
  have hlow : 8256≤bcCounterOff (WCT9.digestIndex N) lay+4 := by
    have hn : lay.val≠3 := fun h=>hl (Fin.ext h)
    have := layerBase_lower (upLayer lay)
    unfold bcCounterOff rowBlock
    rw [if_neg hn]
    unfold merkleBlock
    omega
  have hh : wbcPad (prefixEnc p N w) (WCT9.digestIndex N) lay=wbcPad (witEnc N w) (WCT9.digestIndex N) lay := by
    unfold wbcPad prefixEnc witEnc
    rw [show (96:Nat)=8*12 by rfl,
      extract_readLE_lt (prefixList p N w) 24860 (prefixList_readLE_lt p hp N w) _ 12,
      extract_readLE_lt (witList N w) 24860 (witList_readLE_lt N w) _ 12]
    exact congrArg (fun bs=>BitVec.ofNat 96 (readLE bs)) (prefix_window p hp N w _ 12 hlow)
  rw [hh,wbcPad_witEnc]

theorem prefix_window_left (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (off k : Nat) (ho : off+k≤8256) :
    window (prefixList p N w) off k=window p off k := by
  exact window_append_left _ _ _ _ (by omega)

theorem wdig_prefixEnc_left (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : off+16≤8256) :
    wdig (prefixEnc p N w) off=readDigest (window p off 16) := by
  unfold wdig prefixEnc
  rw [extract_readLE_lt (prefixList p N w) 24860 (prefixList_readLE_lt p hp N w) off 16]
  exact congrArg readDigest (prefix_window_left p hp N w off 16 ho)

theorem wle32_prefixEnc_left (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : off+4≤8256) :
    wle32 (prefixEnc p N w) off=BitVec.ofNat 32 (readLE (window p off 4)) := by
  unfold wle32 prefixEnc
  rw [show (32:Nat)=8*4 by rfl,
    extract_readLE_lt (prefixList p N w) 24860 (prefixList_readLE_lt p hp N w) off 4]
  exact congrArg (fun bs=>BitVec.ofNat 32 (readLE bs)) (prefix_window_left p hp N w off 4 ho)

/-- The prefix counter bytes are independent of every forest slot. -/
def countedPrefix (counter : BitVec 32) (byte : Nat→UInt8) : List UInt8 :=
  (List.range 8256).map fun offset=>if 32≤offset ∧ offset<36 then
    (bytesLE 4 counter).getD (offset-32) 0 else byte offset

theorem countedPrefix_length (counter : BitVec 32) (byte : Nat→UInt8) :
    (countedPrefix counter byte).length=8256 := by simp [countedPrefix]

theorem countedPrefix_counter (counter : BitVec 32) (byte : Nat→UInt8) :
    window (countedPrefix counter byte) 32 4=bytesLE 4 counter := by
  unfold countedPrefix
  rw [window_map_range _ 8256 32 4 (by decide)]
  calc
    _ = (List.range 4).map (fun i=>(bytesLE 4 counter).getD i 0) := by
      apply List.map_congr_left
      intro i hi
      have hi' : i<4 := List.mem_range.mp hi
      simp [show 32≤32+i ∧ 32+i<36 by omega]
    _ = bytesLE 4 counter := map_range_getD _ 4 (by simp [bytesLE_length])

theorem wctr3_countedPrefix (counter : BitVec 32) (byte : Nat→UInt8) (N : HashOutput) (w : WCT9.Witness) :
    wbcCtr (prefixEnc (countedPrefix counter byte) N w) (WCT9.digestIndex N) 3=counter := by
  change wle32 (prefixEnc _ N w) 32=counter
  rw [wle32_prefixEnc_left _ (countedPrefix_length _ _) _ _ _ (by decide),countedPrefix_counter,
    readLE_bytesLE_32]

#print axioms wbuffer_prefixEnc
#print axioms wbcPad_prefixEnc
#print axioms wctr3_countedPrefix
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

@[simp] theorem wrho_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wrho (witEnc output w) = w.signature.rho :=
  PairedReadout.wrho_prefixEnc _ (forestBytes_length output w) output (mainWitness w)

@[simp] theorem wdc_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wdc (witEnc output w) = w.digestCounter :=
  PairedReadout.wdc_prefixEnc _ (forestBytes_length output w) output (mainWitness w)

theorem wvalue_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wvalue (witEnc output w) lay i.val = (w.signature.layers lay).values i :=
  PairedReadout.wvalue_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay i

theorem wbuffer_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (i : Fin (chainCount lay)) :
    wdig (witEnc output w) (leafBufferSlot lay i.val) = (w.signature.layers lay).values i :=
  PairedReadout.wbuffer_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay i

theorem wvalueFor_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (digits : List Nat) (i : Fin (chainCount lay)) :
    wvalueFor (witEnc output w) lay digits i.val = (w.signature.layers lay).values i := by
  unfold wvalueFor
  split
  · exact wbuffer_witEnc output w lay i
  · exact wvalue_witEnc output w lay i

theorem wpath_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (i : Fin (height lay)) :
    wpath (witEnc output w) lay (route (WCT9.digestIndex output) lay).1 i.val =
      (w.signature.layers lay).path i :=
  PairedReadout.wpath_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay i

@[simp] theorem wbcCtr_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) : wbcCtr (witEnc output w) (WCT9.digestIndex output) lay = w.counters lay := by
  by_cases hl : lay = 3
  · subst lay
    exact PairedReadout.wctr3_countedPrefix (w.counters 3)
      (slotByte (forestSlots output w.signature)) output (mainWitness w)
  · exact PairedReadout.wbcCtr_prefixEnc _ (forestBytes_length output w) output (mainWitness w) lay hl

#print axioms wrho_witEnc
#print axioms wvalueFor_witEnc
#print axioms wbcCtr_witEnc
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
/-- Address and logical field number for one shared coordinate, including both
copies of each chain reveal. Authentication fields are numbered from six. -/
def coreSlots (child count : Nat) : List (Nat × Nat) :=
  ((List.range 6).flatMap fun i=>[(640-64*i+48,i),(if i=0 then 688 else 720+16*i,i)]) ++
  ((List.range count).map fun level=>
    ((if level<5 then SharedPathPacking.block child level else 832)+48*(1-child/2^level%2),6+level))

def CoreLayoutOK (child : Nat) : Bool :=
  let slots:=coreSlots child 6
  slots.all (fun p=>decide (p.1%16=0 ∧ p.1+16≤896 ∧ p.1≠160 ∧ p.1≠720)) &&
  slots.all (fun p=>slots.all (fun q=>decide (p.1=q.1→p.2=q.2)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem coreLayoutOK_all : ∀child : Fin 128,CoreLayoutOK child.val=true := by
  intro child
  fin_cases child <;> decide +kernel

theorem coreSlots_subset (child count : Nat) (hc : count≤6) :
    coreSlots child count ⊆ coreSlots child 6 := by
  intro p hp
  simp only [coreSlots,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range] at hp ⊢
  rcases hp with h | ⟨i,hi,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,by omega,rfl⟩

theorem coreSlots_range (child : Fin 128) (count : Nat) (hc : count≤6)
    (p : Nat × Nat) (hp : p∈coreSlots child.val count) :
    p.1%16=0 ∧ p.1+16≤896 ∧ p.1≠160 ∧ p.1≠720 := by
  have h:=coreLayoutOK_all child
  simp only [CoreLayoutOK,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  exact h.1 p (coreSlots_subset child.val count hc hp)

theorem coreSlots_functional (child : Fin 128) (count : Nat) (hc : count≤6)
    (p q : Nat × Nat) (hp : p∈coreSlots child.val count) (hq : q∈coreSlots child.val count)
    (he : p.1=q.1) : p.2=q.2 := by
  have h:=coreLayoutOK_all child
  simp only [CoreLayoutOK,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  exact h.2 p (coreSlots_subset child.val count hc hp) q (coreSlots_subset child.val count hc hq) he
#print axioms coreSlots_range
#print axioms coreSlots_functional
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def slotRegion (k : Nat) : Nat :=176+896*(8-k)
/-- C1 (X = 128): a pair's handed-off top value lands on the next region's R pad at `+160` (right) or on its leaf
pad at `+720` (left). -/
def handSlot (k : Nat) (right : Bool) : Nat :=
  if k=8 then (if right then 48 else 0)
  else slotRegion (k+1)+(if right then 160 else 720)

inductive SlotAt (children : Fin 9→Fin 128) (counts : Fin 9→Nat) (sides : Fin 9→Bool) :
    Nat→(Fin 9×Nat)→Prop
  | core (k : Fin 9) (p : Nat×Nat) (hp : p∈coreSlots (children k).val (counts k)) :
      SlotAt children counts sides (slotRegion k.val+p.1) (k,p.2)
  | hand (k : Fin 9) : SlotAt children counts sides (handSlot k.val (sides k)) (k,6+counts k)

theorem slotRegion_injective (k l a b : Nat) (hk : k<9) (hl : l<9)
    (ha : a<896) (hb : b<896) (he : slotRegion k+a=slotRegion l+b) : k=l ∧ a=b := by
  unfold slotRegion at he
  omega

theorem core_ne_hand (k l : Fin 9) (off : Nat) (ho : off<896)
    (h160 : off≠160) (h720 : off≠720) (side : Bool) :
    slotRegion k.val+off≠handSlot l.val side := by
  intro he
  by_cases hl:l.val=8
  · simp only [handSlot,hl,if_true] at he
    cases side <;> simp at he <;> unfold slotRegion at he <;> omega
  · simp only [handSlot,if_neg hl] at he
    have hll:l.val+1<9:=by omega
    have hh:=slotRegion_injective k.val (l.val+1) off (if side then 160 else 720)
      k.isLt hll ho (by cases side <;> decide) he
    cases side <;> simp at hh <;> omega

theorem handSlot_same (k l : Fin 9) (left right : Bool)
    (he : handSlot k.val left=handSlot l.val right) : k=l := by
  apply Fin.ext
  by_cases hk:k.val=8 <;> by_cases hl:l.val=8
  · omega
  · simp only [handSlot,hk,if_true,if_neg hl] at he
    cases left <;> cases right <;> simp at he <;> unfold slotRegion at he <;> omega
  · simp only [handSlot,hl,if_true,if_neg hk] at he
    cases left <;> cases right <;> simp at he <;> unfold slotRegion at he <;> omega
  · simp only [handSlot,if_neg hk,if_neg hl] at he
    have hh:=slotRegion_injective (k.val+1) (l.val+1) (if left then 160 else 720)
      (if right then 160 else 720) (by omega) (by omega)
      (by cases left <;> decide) (by cases right <;> decide) he
    omega

theorem SlotAt.functional_of_addr {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) {a b : Nat} {p q : Fin 9×Nat}
    (hp : SlotAt children counts sides a p) (hq : SlotAt children counts sides b q) (heq : a=b) : p=q := by
  cases hp with
  | core k x hx =>
    have xr:=coreSlots_range (children k) (counts k) (hc k) x hx
    cases hq with
    | core l y hy =>
      have yr:=coreSlots_range (children l) (counts l) (hc l) y hy
      have hh:=slotRegion_injective k.val l.val x.1 y.1 k.isLt l.isLt (by omega) (by omega) heq
      have kl:k=l:=Fin.ext hh.1
      subst l
      have hxy:=coreSlots_functional (children k) (counts k) (hc k) x y hx hy hh.2
      exact Prod.ext rfl hxy
    | hand l => exact False.elim (core_ne_hand k l x.1 (by omega) xr.2.2.1 xr.2.2.2 (sides l) heq)
  | hand k =>
    cases hq with
    | core l y hy =>
      have yr:=coreSlots_range (children l) (counts l) (hc l) y hy
      exact False.elim (core_ne_hand l k y.1 (by omega) yr.2.2.1 yr.2.2.2 (sides k) heq.symm)
    | hand l =>
      have kl:k=l:=handSlot_same k l (sides k) (sides l) heq
      subst l
      rfl
theorem SlotAt.functional {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) {a : Nat} {p q : Fin 9×Nat}
    (hp : SlotAt children counts sides a p) (hq : SlotAt children counts sides a q) : p=q :=
  SlotAt.functional_of_addr hc hp hq rfl
#print axioms SlotAt.functional
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem SlotAt.layout {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) {a : Nat} {tag : Fin 9×Nat} (h : SlotAt children counts sides a tag) :
    a%16=0 ∧ a+16≤8256 ∧ (a+16≤32 ∨ 48≤a) := by
  cases h with
  | core k p hp =>
    have hr:=coreSlots_range (children k) (counts k) (hc k) p hp
    have hk:=k.isLt
    unfold slotRegion
    omega
  | hand k =>
    have hk:=k.isLt
    by_cases he:k.val=8
    · cases sides k <;> simp [handSlot,he]
    · cases sides k <;> simp [handSlot,he,slotRegion] <;> omega

def readSlot (slots : List (Nat×Digest)) (offset : Nat) : UInt8 :=
  match slots.find? (fun p=>decide (p.1≤offset ∧ offset<p.1+16)) with
  | some p=>(bytesLE 16 p.2).getD (offset-p.1) 0
  | none=>0

theorem readSlot_at (slots : List (Nat×Digest))
    (ha : ∀p∈slots,p.1%16=0)
    (hf : ∀p∈slots,∀q∈slots,p.1=q.1→p.2=q.2)
    (a : Nat) (d : Digest) (hm : (a,d)∈slots) (i : Nat) (hi : i<16) :
    readSlot slots (a+i)=(bytesLE 16 d).getD i 0 := by
  have halign:=ha (a,d) hm
  unfold readSlot
  generalize he : slots.find? _=found
  cases found with
  | none =>
    have hn:=List.find?_eq_none.mp he (a,d) hm
    simp only [decide_eq_true_eq] at hn
    omega
  | some p =>
    have hp:=List.mem_of_find?_eq_some he
    have hr:=List.find?_some he
    simp only [decide_eq_true_eq] at hr
    have hpmod:=ha p hp
    have hpa:p.1=a:=by omega
    have hpd:=hf p hp (a,d) hm hpa
    simp only [hpa,hpd,Nat.add_sub_cancel_left]

theorem readSlot_free (slots : List (Nat×Digest)) (off : Nat)
    (hf : ∀p∈slots,off<p.1∨p.1+16≤off) : readSlot slots off=0 := by
  unfold readSlot
  rw [List.find?_eq_none.mpr (fun p hp=>by
    have hh:=hf p hp
    simp only [decide_eq_true_eq]
    omega)]

theorem countedPrefix_digest (counter : BitVec 32) (slots : List (Nat×Digest))
    (ha : ∀p∈slots,p.1%16=0)
    (hf : ∀p∈slots,∀q∈slots,p.1=q.1→p.2=q.2)
    (a : Nat) (d : Digest) (hm : (a,d)∈slots) (hb : a+16≤8256)
    (hn : a+16≤32∨36≤a) :
    window (countedPrefix counter (readSlot slots)) a 16=bytesLE 16 d := by
  unfold countedPrefix
  rw [window_map_range _ _ _ _ hb]
  calc
    _ = (List.range 16).map (fun i=>(bytesLE 16 d).getD i 0) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<16:=List.mem_range.mp hi
      rw [if_neg (by omega),readSlot_at slots ha hf a d hm i hi']
    _ = bytesLE 16 d := map_range_getD _ _ (bytesLE_length _ _)

theorem countedPrefix_pad3 (counter : BitVec 32) (slots : List (Nat×Digest))
    (hf : ∀p∈slots,p.1+16≤36∨48≤p.1) :
    window (countedPrefix counter (readSlot slots)) 36 12=zeros 12 := by
  unfold countedPrefix
  rw [window_map_range _ _ _ _ (by decide)]
  calc
    _ = (List.range 12).map (fun _=> (0:UInt8)) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<12:=List.mem_range.mp hi
      rw [if_neg (by omega)]
      exact readSlot_free slots _ (fun p hp=>by have :=hf p hp;omega)
    _ = zeros 12 := by simp [zeros]

theorem wpad3_countedPrefix (counter : BitVec 32) (slots : List (Nat×Digest))
    (hf : ∀p∈slots,p.1+16≤36∨48≤p.1) (N : HashOutput) (w : WCT9.Witness) :
    wbcPad (prefixEnc (countedPrefix counter (readSlot slots)) N w) (WCT9.digestIndex N) 3=0 := by
  change (prefixEnc _ N w).extractLsb' (8*36) 96=0
  unfold prefixEnc
  rw [show (96:Nat)=8*12 by rfl,
    extract_readLE_lt _ 24860 (prefixList_readLE_lt _ (countedPrefix_length _ _) N w) 36 12]
  change BitVec.ofNat 96 (readLE (window _ 36 12))=0
  rw [prefix_window_left _ (countedPrefix_length _ _) _ _ _ _ (by decide),countedPrefix_pad3 counter slots hf]
  rfl
#print axioms readSlot_at
#print axioms countedPrefix_digest
#print axioms wpad3_countedPrefix
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def physicalChildren (output : HashOutput) (k : Fin 9) : Fin 128 :=
  ⟨SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val,
    SharedForest.physicalChild_lt _ _ (SharedForest.rawChildFromOutput output k).isLt⟩
def pathCounts (k : Fin 9) : Nat :=SharedV3.lastLevel k.val+1
def handSides (output : HashOutput) (k : Fin 9) : Bool :=
  decide (SharedV3.direction k.val (physicalChildren output k).val=0)
def fieldValue (sig : SharedForest.Signature) (tag : Fin 9×Nat) : Digest :=
  if h:tag.2<6 then Paired.coordinateValues sig.forest tag.1 ⟨tag.2,h⟩
  else Paired.coordinatePath sig.forest tag.1 (tag.2-6)

theorem pathCounts_le (k : Fin 9) : pathCounts k≤6 := by
  unfold pathCounts SharedV3.lastLevel
  split <;> omega

theorem topOtherOff_handSlot (output : HashOutput) (k : Fin 9) :
    SharedV3.topOtherOff k.val (physicalChildren output k).val=handSlot k.val (handSides output k) := by
  have hk:=k.isLt
  unfold SharedV3.topOtherOff V3.regionOffset handSlot handSides slotRegion SharedV3.handR
  by_cases h:k.val=8 <;> by_cases hd:SharedV3.direction k.val (physicalChildren output k).val=0
  all_goals try simp only [h] at hd
  all_goals simp [h,hd]
  all_goals omega

theorem coordinateSlot_entry (output : HashOutput) (sig : SharedForest.Signature) (k : Fin 9)
    (entry : Nat×Digest) (hm : entry∈Paired.coordinateSlots output sig k) :
    ∃tag,SlotAt (physicalChildren output) pathCounts (handSides output) entry.1 tag ∧ entry.2=fieldValue sig tag := by
  unfold Paired.coordinateSlots at hm
  simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with (⟨i,hi,he⟩ | ⟨level,hl,he⟩) | he
  · rcases he with he | he
    · subst entry
      refine ⟨(k,i.val),?_,?_⟩
      · exact SlotAt.core k (640-64*i.val+48,i.val) (by
          apply List.mem_append_left
          apply List.mem_flatMap.mpr
          exact ⟨i.val,List.mem_range.mpr i.isLt,by simp⟩)
      · simp [fieldValue,i.isLt]
    · subst entry
      refine ⟨(k,i.val),?_,?_⟩
      · exact SlotAt.core k (V3.leafSlot i.val,i.val) (by
          apply List.mem_append_left
          apply List.mem_flatMap.mpr
          exact ⟨i.val,List.mem_range.mpr i.isLt,by simp [V3.leafSlot]⟩)
      · simp [fieldValue,i.isLt]
  · subst entry
    refine ⟨(k,6+level),?_,?_⟩
    · exact SlotAt.core k (SharedV3.sibOff (physicalChildren output k).val level,6+level) (by
        apply List.mem_append_right
        apply List.mem_map.mpr
        exact ⟨level,hl,rfl⟩)
    · simp [fieldValue]
  · subst entry
    refine ⟨(k,6+pathCounts k),?_,?_⟩
    · rw [show SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val=(physicalChildren output k).val from rfl,
        topOtherOff_handSlot]
      exact SlotAt.hand k
    · simp [fieldValue,pathCounts]

theorem forestSlot_entry (output : HashOutput) (sig : SharedForest.Signature)
    (entry : Nat×Digest) (hm : entry∈Paired.forestSlots output sig) :
    ∃tag,SlotAt (physicalChildren output) pathCounts (handSides output) entry.1 tag ∧ entry.2=fieldValue sig tag := by
  rcases List.mem_flatMap.mp hm with ⟨k,hk,he⟩
  exact coordinateSlot_entry output sig k entry he

theorem forestSlot_layout (output : HashOutput) (sig : SharedForest.Signature)
    (entry : Nat×Digest) (hm : entry∈Paired.forestSlots output sig) :
    entry.1%16=0 ∧ entry.1+16≤8256 ∧ (entry.1+16≤32∨48≤entry.1) := by
  obtain ⟨tag,hh,_⟩:=forestSlot_entry output sig entry hm
  exact hh.layout pathCounts_le

theorem forestSlot_functional (output : HashOutput) (sig : SharedForest.Signature)
    (p q : Nat×Digest) (hp : p∈Paired.forestSlots output sig) (hq : q∈Paired.forestSlots output sig)
    (he : p.1=q.1) : p.2=q.2 := by
  obtain ⟨pt,ph,pv⟩:=forestSlot_entry output sig p hp
  obtain ⟨qt,qh,qv⟩:=forestSlot_entry output sig q hq
  rw [pv,qv,ph.functional_of_addr pathCounts_le qh he]

theorem wdig_paired_slot (output : HashOutput) (witness : SharedForest.Witness)
    (a : Nat) (d : Digest) (hm : (a,d)∈Paired.forestSlots output witness.signature) :
    wdig (Paired.witEnc output witness) a=d := by
  have hr:=forestSlot_layout output witness.signature (a,d) hm
  change wdig (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)) a=d
  rw [wdig_prefixEnc_left _ (countedPrefix_length _ _) _ _ _ hr.2.1,
    countedPrefix_digest _ _ (fun p hp=>(forestSlot_layout _ _ p hp).1)
      (fun p hp q hq he=>forestSlot_functional output witness.signature p q hp hq he) a d hm hr.2.1 (by omega),Correctness.readDigest_bytesLE]

theorem wpad3_paired (output : HashOutput) (witness : SharedForest.Witness) :
    wbcPad (Paired.witEnc output witness) (WCT9.digestIndex output) 3=0 := by
  exact wpad3_countedPrefix (witness.counters 3) (Paired.forestSlots output witness.signature)
    (fun p hp=>by have hh:=forestSlot_layout output witness.signature p hp;omega) output (Paired.mainWitness witness)
#print axioms forestSlot_entry
#print axioms wdig_paired_slot
#print axioms wpad3_paired
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wchainValue_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEnc output witness) (V3.chainOffset k.val i.val+48)=coordinateValues witness.signature.forest k i := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨i,List.mem_finRange i,by simp⟩

theorem wleafValue_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEnc output witness) (V3.regionOffset k.val+V3.leafSlot i.val)=coordinateValues witness.signature.forest k i := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨i,List.mem_finRange i,by simp⟩

theorem wsibling_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (level : Nat) (hl : level<SharedV3.lastLevel k.val+1) :
    SharedV3.sibling (witEnc output witness) k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) level =
      coordinatePath witness.signature.forest k level := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨level,List.mem_range.mpr hl,rfl⟩

theorem wtopOther_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) :
    SharedV3.topOther (witEnc output witness) k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) =
      coordinatePath witness.signature.forest k (SharedV3.lastLevel k.val+1) := by
  apply PairedReadout.wdig_paired_slot
  apply List.mem_flatMap.mpr
  refine ⟨k,List.mem_finRange k,?_⟩
  unfold coordinateSlots
  apply List.mem_append_right
  simp

theorem wbcPad_witEnc (output : HashOutput) (witness : SharedForest.Witness) (lay : Layer) :
    wbcPad (witEnc output witness) (WCT9.digestIndex output) lay=0 := by
  by_cases h:lay=3
  · subst lay;exact PairedReadout.wpad3_paired output witness
  · exact PairedReadout.wbcPad_prefixEnc (forestBytes output witness) (forestBytes_length _ _) output (mainWitness witness) lay h
#print axioms wchainValue_witEnc
#print axioms wleafValue_witEnc
#print axioms wsibling_witEnc
#print axioms wtopOther_witEnc
#print axioms wbcPad_witEnc
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expandN_digest (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    evalWithAnswerFn answers (digest (wrho (witEnc output w)) message
      (wdc (witEnc output w))) = output := by
  obtain ⟨_,counter,_,c,hs,_,_,hw,hc,_⟩ := expandN_selections answers message pk sig output w he
  have hd := (sharedDigestSearch_some answers sig.rho message WCT9.digestAttemptLimit 0
    counter output (by decide) hs).2.2.2
  rw [wrho_witEnc,wdc_witEnc,hw,hc,nonce_retained]
  exact hd

theorem expandB_some (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (wb : WBytes)
    (he : evalWithAnswerFn answers (expandB message pk sig) = some wb) :
    ∃ output w, evalWithAnswerFn answers (expandN message pk sig) = some (output,w) ∧
      wb = witEnc output w := by
  unfold expandB at he
  rw [evalWithAnswerFn_map] at he
  cases hn : evalWithAnswerFn answers (expandN message pk sig) with
  | none => simp only [hn,Option.map_none,reduceCtorEq] at he
  | some found =>
      obtain ⟨output,w⟩ := found
      simp only [hn,Option.map_some,Option.some.injEq] at he
      exact ⟨output,w,rfl,he.symm⟩

theorem expandN_nonce (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    wrho (witEnc output w) = sig.rho := by
  obtain ⟨_,_,_,c,_,_,_,hw,_,_⟩ := expandN_selections answers message pk sig output w he
  rw [wrho_witEnc,hw,nonce_retained]
#print axioms expandN_digest
#print axioms expandB_some
#print axioms expandN_nonce
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem countedPrefix_freeWord (counter : BitVec 32) (slots : List (Nat×Digest))
    (off : Nat) (hb : off+8≤8256) (hn : off+8≤32 ∨ 36≤off)
    (hf : ∀p∈slots,off+8≤p.1 ∨ p.1+16≤off) :
    window (countedPrefix counter (readSlot slots)) off 8=zeros 8 := by
  unfold countedPrefix
  rw [window_map_range _ _ _ _ hb]
  calc
    _=(List.range 8).map (fun _=>(0:UInt8)) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<8:=List.mem_range.mp hi
      rw [if_neg (by omega)]
      exact readSlot_free slots _ (fun p hp=>by have :=hf p hp;omega)
    _=zeros 8 := by simp [zeros]

theorem word_prefixEnc_free (counter : BitVec 32) (slots : List (Nat×Digest))
    (N : HashOutput) (w : WCT9.Witness) (off : Nat)
    (hb : off+8≤8256) (hn : off+8≤32 ∨ 36≤off)
    (hf : ∀p∈slots,off+8≤p.1 ∨ p.1+16≤off) :
    (prefixEnc (countedPrefix counter (readSlot slots)) N w).extractLsb' (8*off) 64=0 := by
  unfold prefixEnc
  rw [show (64:Nat)=8*8 by rfl,
    extract_readLE_lt _ 24860 (prefixList_readLE_lt _ (countedPrefix_length _ _) N w) off 8]
  change BitVec.ofNat 64 (readLE (window _ off 8))=0
  rw [prefix_window_left _ (countedPrefix_length _ _) _ _ _ _ hb,
    countedPrefix_freeWord counter slots off hb hn hf]
  rfl
#print axioms word_prefixEnc_free
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem countedPrefix_free (counter : BitVec 32) (slots : List (Nat×Digest))
    (off n : Nat) (hb:off+n≤8256) (hn:off+n≤32 ∨ 36≤off ∨ counter=0)
    (hf:∀p∈slots,off+n≤p.1 ∨ p.1+16≤off) :
    window (countedPrefix counter (readSlot slots)) off n=zeros n := by
  unfold countedPrefix
  rw[window_map_range _ _ _ _ hb]
  calc
    _=(List.range n).map (fun _=>(0:UInt8)) := by
      apply List.map_congr_left
      intro i hi
      have hi':i<n:=List.mem_range.mp hi
      split_ifs with h
      · have hc:counter=0:=by rcases hn with hn|hn|hn <;> omega
        rw[hc]
        have he:bytesLE 4 (0:BitVec 32)=List.replicate 4 (0:UInt8):=by decide
        rw[he]
        have hx:off+i-32=0∨off+i-32=1∨off+i-32=2∨off+i-32=3:=by omega
        rcases hx with hx|hx|hx|hx <;> rw[hx] <;> rfl
      · exact readSlot_free slots _ (fun p hp=>by have:=hf p hp;omega)
    _=zeros n:=by simp[zeros]

theorem extract_prefixEnc_free (counter : BitVec 32) (slots : List (Nat×Digest))
    (N : HashOutput) (w : WCT9.Witness) (off n : Nat)
    (hb:off+n≤8256) (hn:off+n≤32 ∨ 36≤off ∨ counter=0)
    (hf:∀p∈slots,off+n≤p.1 ∨ p.1+16≤off) :
    (prefixEnc (countedPrefix counter (readSlot slots)) N w).extractLsb' (8*off) (8*n)=0 := by
  unfold prefixEnc
  rw[extract_readLE_lt _ 24860 (prefixList_readLE_lt _ (countedPrefix_length _ _) N w) off n]
  change BitVec.ofNat (8*n) (readLE (window _ off n))=0
  rw[prefix_window_left _ (countedPrefix_length _ _) _ _ _ _ hb,
    countedPrefix_free counter slots off n hb hn hf]
  simp only[zeros,readLE_replicate_zero]
  rfl
#print axioms countedPrefix_free
#print axioms extract_prefixEnc_free
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem SlotAt.free_local {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc : ∀k,counts k≤6) (k : Fin 9) (off len : Nat) (hb:off+len≤896)
    (hf:∀p∈coreSlots (children k).val (counts k),off+len≤p.1 ∨ p.1+16≤off)
    (h160:off+len≤160 ∨ 176≤off) (h720:off+len≤720 ∨ 736≤off)
    {a : Nat} {tag : Fin 9×Nat} (h:SlotAt children counts sides a tag) :
    slotRegion k.val+off+len≤a ∨ a+16≤ slotRegion k.val+off := by
  cases h with
  | core l p hp =>
    have hr:=coreSlots_range (children l) (counts l) (hc l) p hp
    by_cases he:k=l
    · subst l;have hh:=hf p hp;omega
    · have hk:=k.isLt;have hl:=l.isLt
      have hn:k.val≠l.val:=by intro hv;exact he (Fin.ext hv)
      unfold slotRegion
      omega
  | hand l =>
    have hk:=k.isLt;have hl:=l.isLt
    by_cases he:l.val=8
    · cases sides l <;> simp only[handSlot,he,↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega
    · by_cases heq:k.val=l.val+1
      · simp only [handSlot,if_neg he]
        rw[←heq]
        cases sides l <;> simp only[↓reduceIte,Bool.false_eq_true] <;> omega
      · unfold handSlot
        rw[if_neg he]
        cases sides l <;> simp only[↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega
#print axioms SlotAt.free_local
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.Research
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Witness fields whose honest value is zero: chain pads, node pads below the R pad and (C1) the high header
word of every packed level `0..3`. -/
def zeroFields (child : Nat) : List (Nat×Nat) :=
  ((List.range 6).flatMap fun i=>[(640-64*i,16),(640-64*i+24,8),(640-64*i+32,16)]) ++
  ((List.range 6).filterMap fun l=>if l=4 then none else
    some ((if l<5 then SharedPathPacking.block child l else 832)+32,16)) ++
  ((List.range 4).map fun l=>(SharedPathPacking.block child l+24,8))

def ZeroLayoutOK (child : Nat) : Bool := (zeroFields child).all fun q=>
  decide (q.1+q.2≤896 ∧ (q.1+q.2≤160∨176≤q.1) ∧ (q.1+q.2≤720∨736≤q.1)) &&
    (coreSlots child 6).all (fun p=>decide (q.1+q.2≤p.1∨p.1+16≤q.1))

theorem zeroLayoutOK_all : ∀child : Fin 128,ZeroLayoutOK child.val=true := by
  intro child
  fin_cases child <;> decide +kernel

theorem zeroFields_free (child : Fin 128) (q : Nat×Nat) (hq:q∈zeroFields child.val) :
    q.1+q.2≤896 ∧ (q.1+q.2≤160∨176≤q.1) ∧ (q.1+q.2≤720∨736≤q.1) ∧
    (∀p∈coreSlots child.val 6,q.1+q.2≤p.1∨p.1+16≤q.1) := by
  have hh:=zeroLayoutOK_all child
  simp only[ZeroLayoutOK,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨(hh q hq).1.1,(hh q hq).1.2.1,(hh q hq).1.2.2,(hh q hq).2⟩

theorem SlotAt.zero_fields {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc:∀k,counts k≤6) (k:Fin 9) (q:Nat×Nat) (hq:q∈zeroFields (children k).val)
    {a:Nat} {tag:Fin 9×Nat} (h:SlotAt children counts sides a tag) :
    slotRegion k.val+q.1+q.2≤a ∨ a+16≤ slotRegion k.val+q.1 := by
  have hh:=zeroFields_free (children k) q hq
  exact h.free_local hc k q.1 q.2 hh.1
    (fun p hp=>hh.2.2.2 p (coreSlots_subset _ _ (hc k) hp)) hh.2.1 hh.2.2.1
#print axioms zeroLayoutOK_all
#print axioms SlotAt.zero_fields
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem extract_witEnc_zero_field (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (q : Nat×Nat) (hq:q∈zeroFields (physicalChildren output k).val) :
    (Paired.witEnc output witness).extractLsb' (8*(V3.regionOffset k.val+q.1)) (8*q.2)=0 := by
  have hf:=zeroFields_free (physicalChildren output k) q hq
  change (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)).extractLsb' _ _=0
  apply extract_prefixEnc_free
  · have hk:=k.isLt;unfold V3.regionOffset;omega
  · right;left;unfold V3.regionOffset;omega
  · intro p hp
    obtain ⟨tag,hs,_⟩:=forestSlot_entry output witness.signature p hp
    exact hs.zero_fields pathCounts_le k q hq

theorem chain_zero_fields (child : Nat) (i : Fin 6) :
    (640-64*i.val,16)∈zeroFields child ∧
    (640-64*i.val+24,8)∈zeroFields child ∧
    (640-64*i.val+32,16)∈zeroFields child := by
  have hs:∀q∈[(640-64*i.val,16),(640-64*i.val+24,8),(640-64*i.val+32,16)],q∈zeroFields child:=by
    intro q hq
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨i.val,List.mem_range.mpr i.isLt,hq⟩
  exact ⟨hs _ (by simp),hs _ (by simp),hs _ (by simp)⟩

theorem chainPadA_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) : V3.chainPadA (Paired.witEnc output witness) k.val i.val=0 := by
  exact extract_witEnc_zero_field output witness k _ (chain_zero_fields _ i).1

theorem chainPadB_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) : V3.chainPadB (Paired.witEnc output witness) k.val i.val=0 := by
  simpa only[V3.chainPadB,V3.chainOffset,Nat.add_assoc] using
    extract_witEnc_zero_field output witness k _ (chain_zero_fields _ i).2.1

theorem chainPadC_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) : V3.chainPadC (Paired.witEnc output witness) k.val i.val=0 := by
  simpa only[V3.chainPadC,V3.chainOffset,W9Machine.wdig,ClaudeWCT.W9.T3M.wdig,Nat.add_assoc] using
    extract_witEnc_zero_field output witness k _ (chain_zero_fields _ i).2.2

#print axioms extract_witEnc_zero_field
#print axioms chainPadA_witEnc
#print axioms chainPadB_witEnc
#print axioms chainPadC_witEnc
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem node_zero_fields (child l : Nat) (hl:l<6) (hne:l≠4) :
    ((if l<5 then SharedPathPacking.block child l else 832)+32,16)∈zeroFields child := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_filterMap.mpr ⟨l,List.mem_range.mpr hl,by simp[hne]⟩

theorem header_zero_fields (child l : Nat) (hl:l<4) :
    (SharedPathPacking.block child l+24,8)∈zeroFields child := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨l,List.mem_range.mpr hl,rfl⟩

theorem nodePad_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (l : Nat) (hl:l≤SharedV3.lastLevel k.val) (hne:l≠4) :
    SharedV3.nodePad (Paired.witEnc output witness) k.val (physicalChildren output k).val l=0 := by
  have h6:l<6:=by unfold SharedV3.lastLevel at hl;split at hl <;> omega
  simpa only[SharedV3.nodePad,SharedV3.blkOff,W9Machine.wdig,ClaudeWCT.W9.T3M.wdig,Nat.add_assoc] using
    extract_witEnc_zero_field output witness k _ (node_zero_fields _ l h6 hne)

theorem nodeHPad_witEnc (output : HashOutput) (witness : SharedForest.Witness)
    (k : Fin 9) (l : Nat) :
    SharedV3.nodeHPad (Paired.witEnc output witness) k.val (physicalChildren output k).val l=0 := by
  unfold SharedV3.nodeHPad
  split_ifs with hh
  · rw[SharedV3.nodeTw,W9Machine.wdig_hi]
    have hz:=extract_witEnc_zero_field output witness k _ (header_zero_fields _ l hh)
    simpa only[SharedV3.blkOff,if_pos (show l<5 by omega),Nat.add_assoc] using hz
  · rfl

theorem SlotAt.initial_free {children : Fin 9→Fin 128} {counts : Fin 9→Nat} {sides : Fin 9→Bool}
    (hc:∀k,counts k≤6) (off:Nat) (ho:off=160∨off=720)
    {a:Nat} {tag:Fin 9×Nat} (h:SlotAt children counts sides a tag) :
    slotRegion 0+off+16≤a ∨ a+16≤ slotRegion 0+off := by
  cases h with
  | core k p hp =>
    have hr:=coreSlots_range (children k) (counts k) (hc k) p hp
    have hk:=k.isLt
    by_cases hz:k.val=0
    · unfold slotRegion
      rw[hz]
      rcases ho with ho|ho <;> omega
    · unfold slotRegion
      rcases ho with ho|ho <;> omega
  | hand k =>
    have hk:=k.isLt
    by_cases hz:k.val=8
    · cases sides k <;> simp only[handSlot,hz,↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega
    · cases sides k <;> simp only[handSlot,if_neg hz,↓reduceIte,Bool.false_eq_true] <;> unfold slotRegion <;> omega

theorem initial_word_zero (output : HashOutput) (witness : SharedForest.Witness)
    (off:Nat) (ho:off=160∨off=720) :
    W9Machine.wdig (Paired.witEnc output witness) (V3.regionOffset 0+off)=0 := by
  change (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)).extractLsb' _ (8*16)=0
  apply extract_prefixEnc_free
  · rcases ho with ho|ho <;> rw[ho] <;> decide
  · right;left;unfold V3.regionOffset;omega
  · intro p hp
    obtain ⟨tag,hs,_⟩:=forestSlot_entry output witness.signature p hp
    exact hs.initial_free pathCounts_le off ho

theorem initialPair_witEnc (output : HashOutput) (witness : SharedForest.Witness) :
    SharedV3.initialPair (Paired.witEnc output witness)=(0,0) := by
  exact Prod.ext (initial_word_zero output witness 720 (by simp))
    (initial_word_zero output witness 160 (by simp))
#print axioms nodePad_witEnc
#print axioms nodeHPad_witEnc
#print axioms initialPair_witEnc
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.PairedReadout
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem original_prefix_of_slots (output : HashOutput) (witness : SharedForest.Witness)
    (s t : MachineState) (W : Nat→Prop)
    (hslots : ∀p∈Paired.forestSlots output witness.signature,∀half,half<2→W (1216+p.1+8*half))
    (hread : ∀A,W A→W9Machine.OrigW (Paired.witEnc output witness) t A)
    (hframe : ∀A,A<2^64→¬W A→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))
    (hzero : ∀ (off : Nat), off + 8 ≤ 8256 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (1216+off))=0)
    (off:Nat) (hb:off+8≤8256) (ha:off%8=0) (hc:off≠32∨witness.counters 3=0) :
    W9Machine.OrigW (Paired.witEnc output witness) t (1216+off) := by
  by_cases hw:W (1216+off)
  · exact hread _ hw
  have hf:∀p∈Paired.forestSlots output witness.signature,off+8≤p.1∨p.1+16≤off:=by
    intro p hp
    have hal: p.1%16=0:=(forestSlot_layout output witness.signature p hp).1
    by_contra hn
    have he:off=p.1∨off=p.1+8:=by omega
    rcases he with he|he
    · exact hw (by simpa[he] using hslots p hp 0 (by decide))
    · exact hw (by simpa[he,Nat.add_assoc] using hslots p hp 1 (by decide))
  have hz:(Paired.witEnc output witness).extractLsb' (8*off) 64=0:=by
    change (prefixEnc (countedPrefix (witness.counters 3) (readSlot (Paired.forestSlots output witness.signature))) output (Paired.mainWitness witness)).extractLsb' _ (8*8)=0
    apply extract_prefixEnc_free _ _ _ _ _ _ hb _ hf
    rcases hc with hc|hc
    · omega
    · exact Or.inr (Or.inr hc)
  unfold W9Machine.OrigW
  rw[hframe _ (by omega) hw,hzero off hb ha,show 1216+off-0x4c0=off by omega,hz]
#print axioms original_prefix_of_slots
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem counterWord_witEnc (output : HashOutput) (witness : SharedForest.Witness) :
    (witEnc output witness).extractLsb' (8*32) 64=(witness.counters 3).setWidth 64 := by
  have hlo:=wbcCtr_witEnc output witness 3
  have hhi:=PairedReadout.wpad3_paired output witness
  change (witEnc output witness).extractLsb' 256 32=witness.counters 3 at hlo
  change (witEnc output witness).extractLsb' 288 96=0 at hhi
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hj,decide_true,Bool.true_and]
  by_cases h:j<32
  · have hh:=congrArg (fun x:BitVec 32=>x.getLsbD j) hlo
    simpa only [BitVec.getLsbD_extractLsb',h,decide_true,Bool.true_and] using hh
  · have hh:=congrArg (fun x:BitVec 96=>x.getLsbD (j-32)) hhi
    simp only [BitVec.getLsbD_extractLsb',show j-32<96 by omega,decide_true,
      Bool.true_and,BitVec.getLsbD_zero] at hh
    rw[BitVec.getLsbD_of_ge (witness.counters 3) j (by omega)]
    have hh0 : (0:BitVec 96).getLsbD (j-32)=false:=by simp
    rw[hh0] at hh
    simpa only [show 288+(j-32)=8*32+j by omega] using hh
#print axioms counterWord_witEnc
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open SigGolfCandidate.T3 SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem word_prefixEnc (p : List UInt8) (hp : p.length=8256) (N : HashOutput) (w : WCT9.Witness)
    (off : Nat) (ho : 8256≤off) :
    (prefixEnc p N w).extractLsb' (8*off) 64=(ClaudeWCT.W9.T3M.witEnc N w).extractLsb' (8*off) 64 := by
  have h:=congrArg (fun d:Digest=>d.extractLsb' 0 64) (wdig_prefixEnc p hp N w off ho)
  change (W9Machine.wdig (prefixEnc p N w) off).extractLsb' 0 64=
    (W9Machine.wdig (ClaudeWCT.W9.T3M.witEnc N w) off).extractLsb' 0 64 at h
  rw[W9Machine.wdig_lo,W9Machine.wdig_lo] at h
  exact h
#print axioms word_prefixEnc
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research

theorem word_witEnc_tail (output : HashOutput) (witness : SharedForest.Witness)
    (off : Nat) (ho : 8256≤off) :
    (witEnc output witness).extractLsb' (8*off) 64=
      (ClaudeWCT.W9.T3M.witEnc output (mainWitness witness)).extractLsb' (8*off) 64 :=
  PairedReadout.word_prefixEnc _ (PairedReadout.countedPrefix_length _ _) _ _ off ho
#print axioms word_witEnc_tail
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.PairedReadout
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research

theorem original_prefix_restore (output : HashOutput) (witness : SharedForest.Witness)
    (s t : MachineState)
    (hs : ∀ (off:Nat), off+8≤8256 → off%8=0 → off≠32 → W9Machine.OrigW (Paired.witEnc output witness) s (1216+off))
    (hf : Frame s t (fun A=>A=1248))
    (hc : t.getMem 1248=(witness.counters 3).setWidth 64)
    (off : Nat) (hb : off+8≤8256) (ha : off%8=0) :
    W9Machine.OrigW (Paired.witEnc output witness) t (1216+off) := by
  unfold W9Machine.OrigW
  rw[show 1216+off-0x4c0=off by omega]
  by_cases he:off=32
  · subst off
    rw[Paired.counterWord_witEnc]
    exact hc
  · rw[hf.get (by omega) (by omega)]
    have h:=hs off hb ha he
    simpa only [W9Machine.OrigW,show 1216+off-0x4c0=off by omega] using h
#print axioms original_prefix_restore
end ClaudeWCT.W9.T3M.PairedReadout

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (nodeHashP_zero)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Layer execution reads its chain and Merkle data only from the retained tail. -/
theorem layer_tail_fields (a b : WBytes)
    (h : ∀ off,8256≤off→wdig a off=wdig b off) (lay : Layer) :
    (∀ i,wchainPads a lay i=wchainPads b lay i) ∧
    (∀ i,wchainHeaderPad a lay i=wchainHeaderPad b lay i) ∧
    (∀ digits i,wvalueFor a lay digits i=wvalueFor b lay digits i) ∧
    (∀ leaf j,wpath a lay leaf j=wpath b lay leaf j) ∧
    (∀ leaf j,wmerklePad a lay leaf j=wmerklePad b lay leaf j) := by
  have hb : 8256≤layerBase lay := by fin_cases lay <;> decide
  have hl : 8256≤leafBufferBase lay := by fin_cases lay <;> decide
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i;unfold wchainPads;congr 1 <;> apply h <;> unfold chainBlock <;> omega
  · intro i;unfold wchainHeaderPad;rw[h _ (by unfold chainBlock;omega)]
  · intro digits i;unfold wvalueFor;split
    · apply h;unfold leafBufferSlot;omega
    · unfold wvalue;apply h;unfold chainBlock;omega
  · intro leaf j;unfold wpath;apply h;unfold merkleBlock;omega
  · intro leaf j;unfold wmerklePad;apply h;unfold merkleBlock;omega

theorem layerPairP_tail (a b : WBytes)
    (h : ∀ off,8256≤off→wdig a off=wdig b off) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerPairP a index lay digits=layerPairP b index lay digits := by
  obtain ⟨hcp,hh,hv,hp,hm⟩ := layer_tail_fields a b h lay
  simp only [layerPairP,hcp,hh,hv,hp,hm]

theorem layerGuardedPairP_tail (a b : WBytes)
    (h : ∀ off,8256≤off→wdig a off=wdig b off) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) :
    layerGuardedPairP a index lay answer digits=layerGuardedPairP b index lay answer digits := by
  obtain ⟨hcp,hh,hv,hp,hm⟩ := layer_tail_fields a b h lay
  have hc : layerChainP a index lay digits=layerChainP b index lay digits := by
    funext i;simp only [layerChainP,hcp,hh,hv]
  simp only [layerGuardedPairP,hc,layerPairP_tail a b h]

theorem topLayerP_tail (a b : WBytes)
    (h : ∀ off,8256≤off→wdig a off=wdig b off) (index : Nat) (answer : Digest) :
    topLayerP a index answer=topLayerP b index answer := by
  obtain ⟨hcp,hh,hv,hp,hm⟩ := layer_tail_fields a b h 0
  have hc : topChainP a (route index 0).2 (route index 0).1 (dataDigits 0 answer)=
      topChainP b (route index 0).2 (route index 0).1 (dataDigits 0 answer) := by
    funext i digit;simp only [topChainP,hcp,hh,hv]
  have hf : topFinishP a (route index 0).2 (route index 0).1=
      topFinishP b (route index 0).2 (route index 0).1 := by
    funext ends;simp only [topFinishP,hp,hm]
  simp only [topLayerP,hc,hf]

theorem layersCanonicalBC_tail (a b : WBytes) (index : Nat)
    (h : ∀ off,8256≤off→wdig a off=wdig b off)
    (hc : ∀ lay,wbcCtr a index lay=wbcCtr b index lay)
    (hp : ∀ lay,wbcPad a index lay=wbcPad b index lay) :
    ∀n left right,layersCanonicalBC a index n (.pair left right)=
      layersCanonicalBC b index n (.pair left right) := by
  intro n
  induction n with
  | zero=>intro left right;rfl
  | succ n ih=>
    intro left right
    simp only [layersCanonicalBC,hc,hp,layerEncodingInputP,topLayerP_tail a b h,
      layerGuardedPairP_tail a b h,ih]

/-- Canonical decoding is the only changed branch in the retained WOTS program. -/
theorem layersCanonicalBC_legacy_witEnc (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) : ∀n left right,
    layersCanonicalBC (ClaudeWCT.W9.T3M.witEnc output (mainWitness w))
      (WCT9.digestIndex output) n (.pair left right) =
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) n (.pair left right) := by
  intro n
  induction n with
  | zero=>intro left right;rfl
  | succ n ih=>
    intro left right
    simp only [layersCanonicalBC,SigGolfCandidate.Research.SharedForest.verifyLayers,
      ClaudeWCT.W9.T3M.wbcCtr_witEnc,ClaudeWCT.W9.T3M.wbcPad_witEnc,
      topLayerP_dec output,layerGuardedPairP_dec output,
      witDecP_witEnc,padDecP_witEnc,verifyTopP_zero _ _ _ (WCT9.digestIndex_lt output),
      recoverLayerPairGuardP_zero _ _ _ _ _ (WCT9.digestIndex_lt output),
      ih,layerEncodingInputP,WCT9.layerEncodingInput]
    rfl

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layersCanonicalBC_witEnc (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (n : Nat) (left right : Digest) :
    layersCanonicalBC (witEnc output w) (WCT9.digestIndex output) n (.pair left right)=
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) n (.pair left right) := by
  have ht : ∀ off,8256≤off→wdig (witEnc output w) off=
      wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) off := by
    intro off ho
    exact PairedReadout.wdig_prefixEnc (forestBytes output w) (forestBytes_length output w)
      output (mainWitness w) off ho
  have hc : ∀ lay,wbcCtr (witEnc output w) (WCT9.digestIndex output) lay=
      wbcCtr (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (WCT9.digestIndex output) lay := by
    intro lay
    rw [ClaudeWCT.W9.T3M.Paired.wbcCtr_witEnc,ClaudeWCT.W9.T3M.wbcCtr_witEnc]
    rfl
  have hp : ∀ lay,wbcPad (witEnc output w) (WCT9.digestIndex output) lay=
      wbcPad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (WCT9.digestIndex output) lay := by
    intro lay
    rw [ClaudeWCT.W9.T3M.Paired.wbcPad_witEnc,ClaudeWCT.W9.T3M.wbcPad_witEnc]
  exact (layersCanonicalBC_tail _ _ _ ht hc hp n left right).trans
    (layersCanonicalBC_legacy_witEnc output w n left right)

theorem expandN_fillTopSignature (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    expandN message pk (fillTopSignature sig c)=expandN message pk sig := by
  simp only [expandN,hints_retained,fillTopSignature_fillTopSignature]

theorem expandB_fillTopSignature (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    expandB message pk (fillTopSignature sig c)=expandB message pk sig := by
  rw [expandB,expandB,expandN_fillTopSignature]
end ClaudeWCT.W9.T3M.Paired
