import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsReference
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsMask
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_CanonGraphHonest
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsTopLevelsSat

namespace ClaudeWCT.W9.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
/-- Top-nonce layer (r3-lean-nonsec): a rejected keygen trial (nonce below the selected one) of a top node, with honest
children. -/
def TopTrial (T : Answers) (x : HashInput) : Prop :=
  ∃ level c k, level < 11 ∧ c < 2 ^ (11 - level) ∧ k < WCT9.honestNonce T 0 0 level c ∧
    x = pad64 (WCT9.merkleNodeInputN 0 0 (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ (∃ p : Extract.Pos, p.Bounded ∧ x = Extract.honestInput T p) ∨ TopTrial T x
  | _ => True
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    HonestQuery T (.inl (.inr (Extract.honestInput T p))) := Or.inr (Or.inl ⟨p, hp, rfl⟩)
theorem sat_privateHash (T : Answers) (c : Coordinate) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateHash c) :=
  QueriesSat.query (honestQuery_private T c)
theorem sat_privatePair (T : Answers) (tag lay tree position index : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privatePair tag lay tree position index) := by
  unfold SigGolfCandidate.T3.privatePair
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem sat_mask (T : Answers) (level index : Nat) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.mask level index) := by
  unfold SigGolfCandidate.T3.mask SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_privateMac (T : Answers) (region : Region) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateMac region) := by
  unfold SigGolfCandidate.T3.privateMac SigGolfCandidate.T3.privateMacKey
  exact QueriesSat.bind (QueriesSat.bind (sat_privateHash T _) (QueriesSat.bind
    (sat_privateHash T _) (QueriesSat.pure' _))) (QueriesSat.pure' _)
theorem sat_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.maskedLevel nodes level) := by
  unfold SigGolfCandidate.T3.maskedLevel SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun _ _ =>
    QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)) (QueriesSat.pure' _)
theorem sat_privateNonce (T : Answers) (message : Message) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateNonce message) := by
  unfold SigGolfCandidate.T3.privateNonce
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem posOf_eq_none {x : HashInput}
    (h : ∀ p : Extract.Pos, p.Bounded → x.length = p.len →
      Extract.hdrKey x ≠ bytesLE 16 p.hdr) : Extract.posOf x = none :=
  Extract.posOf_eq_none h
/-- A 64-byte input whose header is an encoding row tweak with any high word (D6: the high word is a witness pad)
decodes to no position: every 64-byte position differs from the row tweak in the low word. -/
theorem posOf_row_none {x : HashInput} {lay : Layer} {tree leaf : Nat} {hi : BitVec 64} (hlen : x.length = 64)
    (hx' : Extract.hdrBlock x = bytesLE 16 (WCT9.rowTweakW lay tree leaf hi)) :
    Extract.posOf x = none := by
  have hlow : (rowTweak lay tree leaf).extractLsb' 0 64 = hyperWord lay.val (tree * 2 ^ height lay + leaf) := by
    unfold rowTweak; exact BitVec.extractLsb'_append_eq_right
  have hx : Extract.hdrBlock x = bytesLE 16 (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64) := by
    rw [hlow]; exact hx'
  apply posOf_eq_none
  intro p hb hl he
  have hm : (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64).toNat % 256 < 128 := by
    have h1 := append64_marker hi ((rowTweak lay tree leaf).extractLsb' 0 64)
    have h2 := rowTweak_marker lay tree leaf
    unfold tweakMarker at h1 h2
    rw [h1, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    have : (rowTweak lay tree leaf).toNat % 2 ^ 64 % 256 = (rowTweak lay tree leaf).toNat % 256 :=
      Nat.mod_mod_of_dvd _ (by norm_num)
    omega
  -- C4: the row tweak's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock x) := by
    rw [hx, Extract.topLow_bytesLE_iff, append64_lowNat, hlow, hyperWord_toNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT, hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _ hm] at he
  have hlo := congrArg (BitVec.extractLsb' 0 64) (bytesLE_injective he)
  rw [BitVec.extractLsb'_append_eq_right] at hlo
  exact Extract.rowTweak_low_ne_hdr lay tree leaf hb (by rw [← hl, hlen]) hlo
theorem posOf_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.posOf (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) = none :=
  posOf_row_none (lay := lay) (tree := tree) (leaf := leaf) (hi := 1)
    (by rw [← BC.pad64_layerEncodingInputP_zero]; exact BC.layerEncodingRow_length _ _ _ _ _ _ _ _)
    ((BC.hdrBlock_layerEncodingInput lay tree leaf msg counter).trans (by rw [WCT9.rowTweakW_one]))
theorem posOf_layerEncodingP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Extract.posOf (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) = none :=
  posOf_row_none (BC.layerEncodingRow_length lay tree leaf msg counter pad padR hi)
    (BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad padR hi)
theorem posOf_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Extract.posOf (pad64 (digestInput rho message counter)) = none := by
  unfold digestInput
  apply posOf_eq_none
  intro p hb hl he
  have hlen : (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message)).length = 64 := by
    rw [Cost.pad64_length]; simp only [List.length_append, bytesLE_length]
  -- C4: the digest header's low word is 0, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock
      (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message))) := by
    rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
      Extract.hdrBlock_prefix, Extract.topLow_bytesLE_iff, digestHeader_lowNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT,
    Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix,
    SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _
      (by rw [digestHeader_firstByte]; decide)] at he
  have hh := bytesLE_injective he
  cases p with
  | chain lay tree leaf i step => exact (chainHeader_ne_digestHeader _ _ _ _ _ counter).symm hh
  | wctChain index coord child c step =>
      have hn := congrArg (fun x : Digest => x.toNat % 256) hh
      simp only [Extract.Pos.hdr, WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_firstByte,
        digestHeader_firstByte] at hn
      omega
  | wctNode index coord level nd =>
      simp only [Extract.Pos.hdr, WCT9.wctNodeHeader] at hh
      exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
  | leaf lay tree lf => exact digestHeader_ne_leafTweak _ _ _ _ hh
  | node lay tree level nd =>
      simp only [Extract.Pos.hdr] at hh
      by_cases h0 : lay = 0
      · subst h0
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top] at hh
        exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
      · -- C2: a lower node word has marker `128 + heap`, the digest header marker 0.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay ≤ 7 := by revert h0; fin_cases lay <;> decide
        have hhp := Extract.node_heap_lt128 hnd h7
        rw [Extract.merkleTweak_layer_lower h0] at hh
        have hn := congrArg (fun x : Digest => x.toNat % 256) hh
        simp only [digestHeader_firstByte, WCT9.lowerTweak_firstByte hhp] at hn
        omega
  | wctLeaf index coord child => exact (WCT9.ftsLeafHeader_ne_digestHeader _ _ _ _).symm hh
  | forest index => simp only [Extract.Pos.hdr] at hh; exact digestHeader_ne_header _ _ _ _ _ _ hh
theorem sat_layerCounterSearch (T : Answers) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.layerCounterSearch]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_layerEncoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _
theorem sat_digestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) :=
  ClaudeWCT.WCT9.Wots.Structural.sat_digestSearch_of T _ rho message fun _ => Or.inl (posOf_digest _ _ _)
private theorem canonicalHeader_low (hdr : Digest) :
    (Extract.canonicalHeader (bytesLE 16 hdr)).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words]
  unfold SigGolfCandidate.T3M.Extract.canonicalHeader
  split_ifs <;> simp [List.take_append, bytesLE_length]
private theorem low_ne_of_firstByte (x y : BitVec 128)
    (hc : 128 ≤ x.toNat % 256) (hr : y.toNat % 256 < 128) :
    x.extractLsb' 0 64 ≠ y.extractLsb' 0 64 := by
  intro he
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] at hv
  omega
theorem posOf_chain_offgraph (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (hoff : chainHeaderSpill tree leaf i step ≠ 0) :
    Extract.posOf (pad64 (WCT9.chainInputW lay tree leaf i step value)) = none := by
  apply posOf_eq_none
  intro p hb _ he
  have hlen : (pad64 (WCT9.chainInputW lay tree leaf i step value)).length = 64 := by
    rw [WCT9.chainInputW_padded]; simp [WCT9.chainInputW_length]
  -- C4: a chain header's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock (pad64 (WCT9.chainInputW lay tree leaf i step value))) := by
    rw [WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header, Extract.topLow_bytesLE_iff, Extract.tweakLow_eq_low,
      chainHeader_low, chainHeaderFlaggedLow_toNat]
    have := chainHeaderLow_band lay tree leaf i step
    split_ifs <;> omega
  rw [Extract.hdrKey_of_len64 hlen hT, WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header] at he
  have hn := congrArg (List.take 8) he
  rw [canonicalHeader_low] at hn
  have hp : (bytesLE 16 p.hdr).take 8 = bytesLE 8 (p.hdr.extractLsb' 0 64) := by
    rw [← Extract.Pos.canonicalHeader_eq hb]
    exact canonicalHeader_low _
  rw [hp] at hn
  have hlo := bytesLE_injective hn
  have hbit := chainHeader_offgraph_bit lay tree leaf i step
  rw [if_neg hoff] at hbit
  cases p with
  | chain lay' tree' leaf' i' step' =>
      exact chainHeader_offgraph_low_ne hoff hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega) hlo
  | wctChain index coord child c step' =>
      exact WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _ hlo.symm
  | wctNode index coord level nd =>
      exact WCT9.wctNodeHeader_low_ne_chainHeader hb.2.1 _ _ _ _ _ _ _ hlo.symm
  | node lay' tree' level nd =>
      by_cases h0 : lay' = 0
      · -- C4: a top label's low word is below 4096, a chain header's carries type byte 193.
        subst h0
        have hv := congrArg BitVec.toNat hlo
        simp only [Extract.Pos.hdr] at hv
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top_low, topNodeWord_toNat64, chainHeader_low,
          chainHeaderFlaggedLow_toNat] at hv
        have := chainHeaderLow_band lay tree leaf i step
        have := topNodeWord_lt (2 ^ (height (0 : Layer) - level - 1) + nd)
        split_ifs at hv <;> omega
      · -- C2: a lower node word has bit 55 clear (layer byte `lay' - 1 ≤ 2`), an off-graph chain header has it set.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay' ≤ 7 := by revert h0; fin_cases lay' <;> decide
        have hh := Extract.node_heap_lt128 hnd h7
        rw [hlo] at hbit
        simp only [Extract.Pos.hdr] at hbit
        rw [Extract.merkleTweak_layer_lower h0, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
          WCT9.lowerTweak_toNat hh] at hbit
        have h1 := Nat.mod_lt tree' (show 0 < 2 ^ 32 by decide)
        have h2 : (lay'.val - 1) % 256 ≤ 2 := by have := lay'.isLt; omega
        omega
  | _ =>
      exact low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
        (Extract.Pos.hdr_marker_lt hb (by simp only [Extract.Pos.cls]; (try split) <;> omega)
          (by simp only [Extract.Pos.cls]; (try split) <;> omega)) hlo
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7)
    (hG : WCT9.isG lay i = false := by simp) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.chain lay tree leaf i start count
      (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chain_zero]; exact QueriesSat.pure' _
  | succ count ih =>
      rw [Correctness.chain_add lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      rw [eval_honestChain]
      intro q hq
      rw [queried_chain_one, List.mem_singleton] at hq
      rw [hq]
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        have he : Extract.honestInput T (.chain lay tree leaf i (start + count)) =
            pad64 (chainInput lay tree leaf i (start + count)
              (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count))) := by
          simp only [Extract.honestInput]
          rw [WCT9.chainInputW_F hG]
          exact congrArg (fun v => pad64 (chainInput lay tree leaf i (start + count) v))
            (honestChainValueW_eq hG (Or.inr (Or.inr (by omega))))
        rw [← he]
        exact honestQuery_honest T (.chain lay tree leaf i (start + count)) hg
      · refine Or.inl ?_
        rw [← WCT9.chainInputW_F hG]
        exact posOf_chain_offgraph lay tree leaf i (start + count) _ hoff
theorem sat_halfHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (high : Bool) (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (WCT9.halfHash high input) := by
  intro q hq
  have he : SourceReplay.queried T (WCT9.halfHash high input) = [.inl (.inr (pad64 input))] := by
    cases high <;> rfl
  rw [he, List.mem_singleton] at hq
  rw [hq]
  exact h
/-- `sat_chain` for the chains of the current scheme (`chainW`; the chain-0 high half changes only the value after
step 6, which no query reads). -/
theorem sat_chainW (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7) :
    QueriesSat T (HonestQuery T) (WCT9.chainW lay tree leaf i start count
      (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chainW_zero']; exact QueriesSat.pure' _
  | succ count ih =>
      rw [chainW_add' lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      have heval : evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count
          (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) =
          honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count) := by
        unfold honestChainValueW
        rw [eval_chainW_add' T lay tree leaf i 0 start count, Nat.zero_add]
      rw [heval, chainW_one']
      apply sat_halfHash
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        refine Or.inr (Or.inl ⟨.chain lay tree leaf i (start + count), hg, ?_⟩)
        rfl
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)
/-! ### Top leaves (campaign T8D: family seeds through `topCoefs`, `buildLeafTop`, `buildTopTree`) -/
theorem sat_topPairsFrom (T : Answers) (first start : Nat) (init : List Digest) :
    QueriesSat T (HonestQuery T) (topPairsFrom first start init) := by
  unfold topPairsFrom
  refine QueriesSat.foldlM_range' _ _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
  unfold topSeedPair
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_topCoefs (T : Answers) (leaf : Nat) : QueriesSat T (HonestQuery T) (topCoefs leaf) := by
  unfold topCoefs
  exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
theorem sat_topFamilyCoefs (T : Answers) (leaf : Nat) (cc : List Digest × Digest) :
    QueriesSat T (HonestQuery T) (topFamilyCoefs leaf cc) := by
  unfold topFamilyCoefs
  split
  · unfold topCoefsK
    exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
  · exact QueriesSat.pure' _
theorem sat_buildLeafTopC (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTopC leaf (Correctness.topCoefList T leaf) digits signatureOnly) := by
  rw [Correctness.buildLeafTopC_eq]
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun i hi rows _ => ⟨?_, trivial⟩)) ?_
  · unfold Correctness.topLeafStep
    have hseed : topSeed (Correctness.topCoefList T leaf) leaf i = WCT9.wotsSeed T 0 0 leaf i := by
      rw [WCT9.wotsSeed_top, Correctness.leafSeed_top]; rfl
    rw [hseed]
    have hd := hvalid i hi
    have hw := Mask.width_le (0 : Layer) i
    have hc := Mask.chainCount_le (0 : Layer)
    -- witness stack: the top chain is `chainW 0 0` (G for even i ≤ 52), via the G-aware `sat_chainW`
    simp only [← WCT9.chainW_top_eq]
    have h0 : WCT9.wotsSeed T 0 0 leaf i =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0 := by
      simp [honestChainValueW, WCT9.chainW]
    rw [h0]
    refine QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i 0 _ (by decide) hleaf (by omega) (by omega)) ?_
    have heval : evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 (digits.getD i 0)
        (honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0)) =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) (digits.getD i 0) := by
      have hz : ∀ v, evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 0 v) = v := by
        intro v; simp [WCT9.chainW, evalWithAnswerFn_pure]
      unfold honestChainValueW
      rw [hz]
    rw [heval]
    split
    · exact QueriesSat.pure' _
    · exact QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i _ _ (by decide) hleaf (by omega) (by omega))
        (QueriesSat.pure' _)
  · cases signatureOnly
    · have hr := Correctness.eval_topLeafRows T leaf digits hvalid false
      simp only [Correctness.LeafRows, Bool.false_eq_true, ite_false, min_self] at hr
      have he := Correctness.list_eq_range_map _ (leafEnd T 0 0 leaf) _ hr.1
        (fun i hi => hr.2.2.1 i (by rw [hr.1]; exact hi))
      simp only [Bool.false_eq_true, ite_false]
      refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [he, ← WCT9.wotsEnd_top]
      unfold leafHash
      exact sat_projHash _ _ (honestQuery_honest T (.leaf (0 : Layer) 0 leaf) hb)
    · simp only [ite_true]
      exact QueriesSat.pure' _
theorem sat_buildLeafTop (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTop leaf digits signatureOnly) := by
  rw [Correctness.buildLeafTop_eq]
  refine QueriesSat.bind (sat_topCoefs T leaf) ?_
  rw [Correctness.eval_topCoefs]
  have h := sat_buildLeafTopC T leaf digits hvalid signatureOnly hleaf hb
  rw [Correctness.buildLeafTopC_eq] at h
  exact h
theorem honestNonce_top_eq (T : Answers) (level c : Nat) (hl : level < 11) :
    WCT9.honestNonce T 0 0 level c = (evalWithAnswerFn T (topNodeAt (level + 1) (2 ^ (11 - level) + c)
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))).1 := by
  unfold WCT9.honestNonce
  rw [if_pos ⟨rfl, hl⟩, show height (0 : Layer) - level - 1 = 11 - level by simp [height]; omega]
theorem honestQuery_topTrial (T : Answers) (level c k : Nat) (hl : level < 11) (hc : c < 2 ^ (11 - level))
    (hk : k ≤ WCT9.honestNonce T 0 0 level c) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))))) := by
  rw [← WCT9.merkleNodeInputN_top 0]
  rcases Nat.lt_or_ge k (WCT9.honestNonce T 0 0 level c) with hlt | hge
  · exact Or.inr (Or.inr ⟨level, c, k, hl, hc, hlt, rfl⟩)
  · have heq : k = WCT9.honestNonce T 0 0 level c := le_antisymm hk hge
    subst heq
    have hh : height (0 : Layer) - level - 1 = 11 - level := by simp [height]; omega
    refine Or.inr (Or.inl ⟨.node 0 0 level c, ⟨by norm_num, by simp [height]; omega, Or.inl rfl, fun _ => rfl,
      by rw [hh]; exact hc⟩, ?_⟩)
    show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - level - 1) + c)
      (WCT9.honestNonce T 0 0 level c) _ _)
    rw [hh]
    rfl
theorem honestQuery_topRoot (T : Answers) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput 1 0
      (treeValue (WCT9.wotsTree T 0 0) 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 1))))) := by
  refine Or.inr (Or.inl ⟨.node 0 0 11 0, ⟨by norm_num, by simp [height], Or.inl rfl, fun _ => rfl, by simp [height]⟩, ?_⟩)
  show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - 11 - 1) + 0)
    (WCT9.honestNonce T 0 0 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0)) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0 + 1)))
  rw [WCT9.honestNonce_root]
  exact (congrArg pad64 (WCT9.merkleNodeInputN_top 0 1 0 _ _)).symm
theorem sat_buildTopTree (T : Answers) : QueriesSat T (HonestQuery T) buildTopTree := by
  unfold buildTopTree
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (Correctness.TopTreeState T) _ (Correctness.topTreeState_zero T)
    (fun leaf hleaf st hst => ⟨?_, Correctness.eval_topTreeStep T leaf st hst⟩)) ?_
  · have hl' : leaf < 2 ^ 32 := by
      have : 2 ^ height (0 : Layer) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le 0)
      omega
    unfold topTreeStep
    refine QueriesSat.bind (sat_topFamilyCoefs T leaf st.2) ?_
    rw [(Correctness.topTreeStep_coefs T leaf st hst).1]
    exact QueriesSat.bind (sat_buildLeafTopC T leaf [] (Cost.validDigits_nil 0) false hl'
      (Extract.leaf_bounded_of_treeBits (by decide) hleaf)) (QueriesSat.pure' _)
  · rw [(Correctness.eval_topTreeLoop T (2 ^ height 0)).1]
    have hroots : (List.range (2 ^ height 0)).map (Correctness.leafRoot T 0 0) =
        (List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0) := by rw [WCT9.wotsRoot_top]
    have hW : evalWithAnswerFn T (buildTopLevels ((List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0))) =
        WCT9.wotsTree T 0 0 := by unfold WCT9.wotsTree; rw [if_pos rfl]
    rw [hroots]
    apply SigGolfCandidate.T3.Security.Wots.Structural.sat_buildTopLevels T (HonestQuery T) _ (by simp [height])
    · rw [hW]; exact honestQuery_topRoot T
    · intro level c k hl hc hk
      rw [hW] at hk ⊢
      exact honestQuery_topTrial T level c k hl hc (le_of_le_of_eq hk (honestNonce_top_eq T level c hl).symm)
theorem sat_packedSecret (T : Answers) (lay : Layer) (tree q : Nat) (carry : Digest) :
    QueriesSat T (HonestQuery T) (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry) := by
  unfold WCT9.packedSecret
  split
  · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_lowerCoefs (T : Answers) (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    QueriesSat T (HonestQuery T) (WCT9.lowerCoefs lay tree leaf carry) := by
  unfold WCT9.lowerCoefs WCT9.lowerFamCoefs
  split
  · refine QueriesSat.bind (QueriesSat.bind ?_ (QueriesSat.pure' _)) (QueriesSat.pure' _)
    refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_leafRowsF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (WCT9.leafRowsF lay tree leaf digits (WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))) := by
  unfold WCT9.leafRowsF
  refine QueriesSat.foldlM_range _ _ (WCT9.LeafRowsF T lay tree leaf digits) _
    (by simp [WCT9.LeafRowsF])
    (fun i hi rows hrows => ⟨?_, WCT9.leafStepF_inv T hlay tree leaf digits hvalid i hi rows hrows⟩)
  unfold WCT9.leafStepF
  rw [WCT9.lowerFamilySeed_eq T hlay]
  have hd := hvalid i hi
  have hw := Mask.width_le lay i
  have hc := Mask.chainCount_le lay
  rw [← honestChainValueW_zero T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i)]
  refine QueriesSat.bind (sat_chainW T lay tree leaf i 0 (digits.getD i 0) htree hleaf (by omega) (by omega)) ?_
  rw [honestChainValueW_zero, show evalWithAnswerFn T (WCT9.chainW lay tree leaf i 0 (digits.getD i 0)
      (WCT9.wotsSeed T lay tree leaf i)) =
      honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (digits.getD i 0) from rfl]
  exact QueriesSat.bind (sat_chainW T lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
    htree hleaf (by omega) (by omega)) (QueriesSat.pure' _)
theorem sat_buildLeafPF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (carry : List Digest)
    (hcarry : leaf % WCT9.famGrp lay ≠ 0 → carry = WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (WCT9.buildLeafPF lay tree leaf digits carry) := by
  rw [WCT9.buildLeafPF_factor]
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [WCT9.eval_lowerCoefs T hlay tree leaf carry hcarry]
  dsimp only
  refine QueriesSat.bind (sat_leafRowsF T hlay tree leaf digits hvalid htree hleaf) ?_
  rw [WCT9.eval_leafRowsF T hlay tree leaf digits hvalid]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  exact sat_halfHash _ _ (honestQuery_honest T (.leaf lay tree leaf) hb)
theorem sat_treeRowsP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.treeRowsP lay tree selected digits) := by
  unfold WCT9.treeRowsP
  refine QueriesSat.foldlM_range _ _ (fun done rows => rows.2.2 = WCT9.treeCarry T lay tree done) _
    (by simp [WCT9.treeCarry]) (fun leaf hleaf rows hrows => ?_)
  have hd : Cost.ValidDigits lay (if leaf = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  have hl' : leaf < 2 ^ 32 := by
    have : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  have hcarry := WCT9.carryOk_treeCarry T lay tree leaf
  rw [← hrows] at hcarry
  refine ⟨QueriesSat.bind (sat_buildLeafPF T hlay tree leaf _ hd _ hcarry htree hl'
    (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_, ?_⟩
  · generalize evalWithAnswerFn T (WCT9.buildLeafPF lay tree leaf (if leaf = selected then digits else []) rows.2.2) = x
    obtain ⟨⟨root, values⟩, c⟩ := x
    exact QueriesSat.pure' _
  · simp only [evalWithAnswerFn_bind, WCT9.buildLeafPF_result T hlay tree leaf _ hd _ hcarry, evalWithAnswerFn_pure]
    show WCT9.leafCarryOut T lay tree leaf = WCT9.treeCarry T lay tree (leaf + 1)
    unfold WCT9.treeCarry
    rw [if_neg (show leaf + 1 ≠ 0 by omega), Nat.add_sub_cancel]
/-! ### C2 (FULL): the lower trees fold with `lowerLevel` (`lowerNodeHash`, the half of each heap) -/
def merkleQuery (lay tree heap : Nat) (left right : Digest) : SigGolfCandidate.T3.Spec.Domain :=
  .inl (.inr (pad64 (WCT9.merkleNodeInput lay tree heap left right)))
theorem sat_lowerNodeHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree heap : Nat)
    (left right : Digest) (h : Q (merkleQuery lay tree heap left right)) :
    QueriesSat T Q (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  exact sat_halfHash _ _ h
theorem sat_lowerLevel {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h level : Nat)
    (nodes : List Digest)
    (hq : ∀ i, i < nodes.length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))) :
    QueriesSat T Q (WCT9.lowerLevel lay tree h level nodes) := by
  unfold WCT9.lowerLevel
  exact QueriesSat.mapM _ _ (fun i hi => sat_lowerNodeHash _ _ _ _ _ (hq i (List.mem_range.mp hi)))
def lowerStep (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← WCT9.lowerLevel lay tree h level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])
def lowerFold (lay tree h : Nat) (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM (lowerStep lay tree h) [leaves]
theorem eval_lowerStep (T : Answers) (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (lowerStep lay tree h levels level) =
      levels ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h level (levels.getD (level - 1) []))] := by
  simp only [lowerStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem eval_lowerSteps_append (T : Answers) (lay tree h : Nat) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM (lowerStep lay tree h) state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_lowerStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩
theorem lowerFold_succ (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    lowerFold lay tree h leaves (n + 1) =
      (lowerFold lay tree h leaves n >>= fun state => lowerStep lay tree h state (1 + n)) := by
  unfold lowerFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem lowerFold_length (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (lowerFold lay tree h leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lowerFold_succ, evalWithAnswerFn_bind, eval_lowerStep, List.length_append, ih]
      simp
theorem lowerFold_prefix (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (lowerFold lay tree h leaves m) =
      evalWithAnswerFn T (lowerFold lay tree h leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold lowerFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_lowerSteps_append T lay tree h _ _
theorem sat_lowerFold {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h : Nat)
    (leaves : List Digest) (n : Nat) (hn : n ≤ h)
    (hq : ∀ level, level < n → ∀ node,
      node < ((evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD level []).length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node))
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node + 1)))) :
    QueriesSat T Q (lowerFold lay tree h leaves n) := by
  unfold lowerFold
  refine QueriesSat.foldlM_range' 1 n _
    (fun i state => state = evalWithAnswerFn T (lowerFold lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold lowerStep
    refine QueriesSat.bind (sat_lowerLevel _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := lowerFold_length T lay tree h leaves i
    obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves i n (by omega)
    have hget : (evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD i [] =
        (evalWithAnswerFn T (lowerFold lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i (by omega) node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [lowerFold_succ, evalWithAnswerFn_bind]
theorem honestQuery_lowerNode (T : Answers) (lay : Layer) (tree : Nat) (ht : tree < 2 ^ Extract.treeBits lay)
    (level node : Nat) (hlevel : level < height lay) (hroot : lay = 0 ∨ level + 1 < height lay) (hlay : lay ≠ 0)
    (hnode : node < ((WCT9.wotsTree T lay tree).getD level []).length / 2) :
    HonestQuery T (merkleQuery lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (WCT9.wotsTree T lay tree) level (2 * node)) (treeValue (WCT9.wotsTree T lay tree) level (2 * node + 1))) := by
  have hshape := (WCT9.wotsTree_correct T hlay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine Or.inr (Or.inl ⟨.node lay tree level node, ⟨by
    have h31 := lt_of_le_of_lt (Nat.le_add_right _ _) (Extract.routed_lt_of_treeBits ht (Nat.one_le_two_pow))
    have hle : tree ≤ tree * 2 ^ height lay := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
    omega, hlevel, hroot, Extract.tree_zero_of_treeBits ht, by rw [hw, hpow] at hnode; omega⟩, ?_⟩)
  show pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - (level + 1)) + node) _ _) =
    pad64 (WCT9.merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + node) (WCT9.honestNonce T lay tree level node) _ _)
  rw [WCT9.honestInputN_lower T hlay, Nat.sub_sub]
theorem buildLevelsBelow_eq_fold (tag lay tree h : Nat) (leaves : List Digest) :
    WCT9.buildLevelsBelow tag lay tree h leaves = lowerFold lay tree h leaves (h - 1) := rfl
theorem lowerLevels_eq_fold (lay tree h : Nat) (leaves : List Digest) :
    WCT9.lowerLevels lay tree h leaves = lowerFold lay tree h leaves h := rfl
theorem below_getD (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (level : Nat) (hl : level + 1 < h) :
    (evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)).getD level [] =
      (evalWithAnswerFn T (WCT9.lowerLevels lay tree h leaves)).getD level [] := by
  rw [buildLevelsBelow_eq_fold, lowerLevels_eq_fold]
  obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves (h - 1) h (by omega)
  have hlen := lowerFold_length T lay tree h leaves (h - 1)
  rw [hext, List.getD_append _ _ _ _ (by omega)]
theorem sat_buildTreeP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.buildTreeP lay tree selected digits) := by
  rw [WCT9.buildTreeP_factor]
  refine QueriesSat.bind (sat_treeRowsP T hlay tree selected digits hvalid htree ht) ?_
  obtain ⟨hlen, hroot, -, -⟩ := WCT9.eval_treeRowsP T hlay tree selected digits hvalid
  have hroots := Correctness.list_eq_range_map _ _ _ hlen hroot
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [hroots, buildLevelsBelow_eq_fold]
  refine sat_lowerFold _ _ _ _ _ (by omega) ?_
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay) ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))
    level (by omega)
  rw [← buildLevelsBelow_eq_fold 3, hg] at hnode
  rw [← buildLevelsBelow_eq_fold 3]
  have hwt : WCT9.wotsTree T lay tree = evalWithAnswerFn T (WCT9.lowerLevels lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))) := by
    unfold WCT9.wotsTree; rw [if_neg hlay]
  have := honestQuery_lowerNode T lay tree ht level node (by omega) (Or.inr (by omega)) hlay (by rw [hwt]; exact hnode)
  rw [hwt] at this
  simp only [treeValue, hg]
  exact this
theorem honestQuery_of_fts (T : Answers) {index : Nat} (hindex : index < 2 ^ 31) {q : SigGolfCandidate.T3.Spec.Domain}
    (h : ClaudeWCT.WCT9.Wots.FtsHonestQuery T index q) : HonestQuery T q := by
  rcases q with (coin | x) | (tweak | other)
  · exact h.elim
  · obtain ⟨pos, hb, hx⟩ := Extract.ftsHonestQuery_pos hindex h
    exact Or.inr (Or.inl ⟨pos, hb, hx⟩)
  · trivial
  · trivial
theorem sat_signForest (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.signForest index output) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_signForest T index output).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_keygenPayload (T : Answers) : QueriesSat T (HonestQuery T) keygenPayload := by
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine QueriesSat.bind (sat_buildTopTree T) ?_
  generalize evalWithAnswerFn T buildTopTree = levels
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun level _ => sat_maskedLevel T _ _) (QueriesSat.pure' _)
theorem sat_keygen (T : Answers) : QueriesSat T (HonestQuery T) keygen := by
  unfold keygen
  refine QueriesSat.bind (sat_keygenPayload T) ?_
  generalize evalWithAnswerFn T keygenPayload = x
  obtain ⟨publicKey, region⟩ := x
  exact QueriesSat.bind (sat_privateMac T _) (QueriesSat.pure' _)
theorem sat_topPath (T : Answers) (cache : Cache) (leaf : Nat) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (topPath cache leaf) := by
  unfold topPath
  exact QueriesSat.mapM _ _ fun level _ => QueriesSat.bind (sat_mask T _ _) (QueriesSat.pure' _)
theorem sat_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (signTop cache leaf digits) := by
  unfold signTop
  refine QueriesSat.bind (sat_buildLeafTop T leaf digits hvalid true (by omega)
    (Extract.leaf_bounded_of_treeBits (by decide) (by simpa [height] using hleaf))) ?_
  generalize evalWithAnswerFn T (buildLeafTop leaf digits true) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.bind (sat_topPath T cache leaf hleaf) (QueriesSat.pure' _)
theorem sat_signLayers (T : Answers) (cache : Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, QueriesSat T (HonestQuery T) (WCT9.signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _; exact QueriesSat.pure' _
  | succ n ih =>
      intro hn msg
      simp only [WCT9.signLayersBC]
      refine QueriesSat.bind (sat_layerCounterSearch T _ _ _ _ _ _) ?_
      generalize hs : evalWithAnswerFn T (WCT9.layerCounterSearch _ _ _ _ _ _) = r
      cases r with
      | none =>
          dsimp only
          split_ifs with hn0
          · subst hn0
            refine QueriesSat.bind (sat_signTop T cache _ _ (Mask.dummyDigits_spec 0).2 ?_) (QueriesSat.pure' _)
            have := route_leaf_bound index (Fin.ofNat 4 0)
            exact this
          · exact QueriesSat.pure' _
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (WCT9.layerCounterSearch_some T _ _ _ msg _ 0 counter digits
            (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          dsimp only
          split_ifs with hn0
          · subst hn0
            refine QueriesSat.bind (sat_signTop T cache _ digits hvalid ?_) (QueriesSat.pure' _)
            have := route_leaf_bound index (Fin.ofNat 4 0)
            exact this
          · have hl0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
              rw [h] at hv
              exact hn0 hv.symm
            refine QueriesSat.bind (sat_buildTreeP T hl0 _ _ digits hvalid (Mask.route_tree_lt index hindex _)
              (Extract.route_tree_treeBits index hindex _)) ?_
            refine QueriesSat.bind (ih (by omega) _) ?_
            generalize evalWithAnswerFn T (WCT9.signLayersBC cache index n _) = r
            rcases r with _ | r <;> exact QueriesSat.pure' _
theorem sat_signPayload (T : Answers) (cache : Cache) (message : Message) :
    QueriesSat T (HonestQuery T) (signPayload cache message) := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine QueriesSat.bind (sat_privateNonce T message) ?_
  refine QueriesSat.bind (sat_digestSearch T _ _ _ _) ?_
  generalize evalWithAnswerFn T (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn T (privateNonce message)) message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · exact QueriesSat.pure' _
  · dsimp only
    have hindex : WCT9.digestIndex output < 2 ^ 31 := Nat.mod_lt _ (by decide)
    refine QueriesSat.bind (sat_signForest T _ hindex _) ?_
    refine QueriesSat.bind (sat_signLayers T cache _ hindex 4 le_rfl _) ?_
    generalize evalWithAnswerFn T (WCT9.signLayersBC cache (WCT9.digestIndex output) 4 _) = pieces
    rcases pieces with _ | pieces <;> exact QueriesSat.pure' _
theorem sat_authenticatedSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    QueriesSat T (HonestQuery T) (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine QueriesSat.bind (sat_privateMac T _) ?_
  split
  · exact sat_signPayload T _ _
  · exact QueriesSat.pure' _
end ClaudeWCT.W9.T3.Security.Wots.Structural

-- Stage 2 (C2/C3, #866): this paired copy of `Structural` is #866's `Structural` section with Ghost's paired
-- `HonestQuery` (paired honest inputs/bounds) and without the unpaired signer lemmas.
namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
/-- Top-nonce layer (r3-lean-nonsec): a rejected keygen trial (nonce below the selected one) of a top node, with honest
children. -/
def TopTrial (T : Answers) (x : HashInput) : Prop :=
  ∃ level c k, level < 11 ∧ c < 2 ^ (11 - level) ∧ k < WCT9.honestNonce T 0 0 level c ∧
    x = pad64 (WCT9.merkleNodeInputN 0 0 (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ (∃ p : Extract.Pos, Extract.Paired.Bounded p ∧ x = Extract.Paired.honestInput T p) ∨
      TopTrial T x
  | _ => True
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : Extract.Paired.Bounded p) :
    HonestQuery T (.inl (.inr (Extract.Paired.honestInput T p))) := Or.inr (Or.inl ⟨p, hp, rfl⟩)
theorem sat_privateHash (T : Answers) (c : Coordinate) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateHash c) :=
  QueriesSat.query (honestQuery_private T c)
theorem sat_privatePair (T : Answers) (tag lay tree position index : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privatePair tag lay tree position index) := by
  unfold SigGolfCandidate.T3.privatePair
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem sat_mask (T : Answers) (level index : Nat) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.mask level index) := by
  unfold SigGolfCandidate.T3.mask SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_privateMac (T : Answers) (region : Region) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateMac region) := by
  unfold SigGolfCandidate.T3.privateMac SigGolfCandidate.T3.privateMacKey
  exact QueriesSat.bind (QueriesSat.bind (sat_privateHash T _) (QueriesSat.bind
    (sat_privateHash T _) (QueriesSat.pure' _))) (QueriesSat.pure' _)
theorem sat_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.maskedLevel nodes level) := by
  unfold SigGolfCandidate.T3.maskedLevel SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun _ _ =>
    QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)) (QueriesSat.pure' _)
theorem sat_privateNonce (T : Answers) (message : Message) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateNonce message) := by
  unfold SigGolfCandidate.T3.privateNonce
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem posOf_eq_none {x : HashInput}
    (h : ∀ p : Extract.Pos, p.Bounded → x.length = p.len →
      Extract.hdrKey x ≠ bytesLE 16 p.hdr) : Extract.posOf x = none :=
  Extract.posOf_eq_none h
/-- A 64-byte input whose header is an encoding row tweak with any high word (D6: the high word is a witness pad)
decodes to no position: every 64-byte position differs from the row tweak in the low word. -/
theorem posOf_row_none {x : HashInput} {lay : Layer} {tree leaf : Nat} {hi : BitVec 64} (hlen : x.length = 64)
    (hx' : Extract.hdrBlock x = bytesLE 16 (WCT9.rowTweakW lay tree leaf hi)) :
    Extract.posOf x = none := by
  have hlow : (rowTweak lay tree leaf).extractLsb' 0 64 = hyperWord lay.val (tree * 2 ^ height lay + leaf) := by
    unfold rowTweak; exact BitVec.extractLsb'_append_eq_right
  have hx : Extract.hdrBlock x = bytesLE 16 (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64) := by
    rw [hlow]; exact hx'
  apply posOf_eq_none
  intro p hb hl he
  have hm : (hi ++ (rowTweak lay tree leaf).extractLsb' 0 64).toNat % 256 < 128 := by
    have h1 := append64_marker hi ((rowTweak lay tree leaf).extractLsb' 0 64)
    have h2 := rowTweak_marker lay tree leaf
    unfold tweakMarker at h1 h2
    rw [h1, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    have : (rowTweak lay tree leaf).toNat % 2 ^ 64 % 256 = (rowTweak lay tree leaf).toNat % 256 :=
      Nat.mod_mod_of_dvd _ (by norm_num)
    omega
  -- C4: the row tweak's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock x) := by
    rw [hx, Extract.topLow_bytesLE_iff, append64_lowNat, hlow, hyperWord_toNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT, hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _ hm] at he
  have hlo := congrArg (BitVec.extractLsb' 0 64) (bytesLE_injective he)
  rw [BitVec.extractLsb'_append_eq_right] at hlo
  exact Extract.rowTweak_low_ne_hdr lay tree leaf hb (by rw [← hl, hlen]) hlo
theorem posOf_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.posOf (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) = none :=
  posOf_row_none (lay := lay) (tree := tree) (leaf := leaf) (hi := 1)
    (by rw [← BC.pad64_layerEncodingInputP_zero]; exact BC.layerEncodingRow_length _ _ _ _ _ _ _ _)
    ((BC.hdrBlock_layerEncodingInput lay tree leaf msg counter).trans (by rw [WCT9.rowTweakW_one]))
theorem posOf_layerEncodingP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Extract.posOf (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) = none :=
  posOf_row_none (BC.layerEncodingRow_length lay tree leaf msg counter pad padR hi)
    (BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad padR hi)
theorem posOf_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Extract.posOf (pad64 (digestInput rho message counter)) = none := by
  unfold digestInput
  apply posOf_eq_none
  intro p hb hl he
  have hlen : (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message)).length = 64 := by
    rw [Cost.pad64_length]; simp only [List.length_append, bytesLE_length]
  -- C4: the digest header's low word is 0, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock
      (pad64 (bytesLE 16 rho ++ bytesLE 16 (digestHeader counter) ++ bytesLE 32 message))) := by
    rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
      Extract.hdrBlock_prefix, Extract.topLow_bytesLE_iff, digestHeader_lowNat]; omega
  rw [Extract.hdrKey_of_len64 hlen hT,
    Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix,
    SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _
      (by rw [digestHeader_firstByte]; decide)] at he
  have hh := bytesLE_injective he
  cases p with
  | chain lay tree leaf i step => exact (chainHeader_ne_digestHeader _ _ _ _ _ counter).symm hh
  | wctChain index coord child c step =>
      have hn := congrArg (fun x : Digest => x.toNat % 256) hh
      simp only [Extract.Pos.hdr, WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_firstByte,
        digestHeader_firstByte] at hn
      omega
  | wctNode index coord level nd =>
      simp only [Extract.Pos.hdr, WCT9.wctNodeHeader] at hh
      exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
  | leaf lay tree lf => exact digestHeader_ne_leafTweak _ _ _ _ hh
  | node lay tree level nd =>
      simp only [Extract.Pos.hdr] at hh
      by_cases h0 : lay = 0
      · subst h0
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top] at hh
        exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
      · -- C2: a lower node word has marker `128 + heap`, the digest header marker 0.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay ≤ 7 := by revert h0; fin_cases lay <;> decide
        have hhp := Extract.node_heap_lt128 hnd h7
        rw [Extract.merkleTweak_layer_lower h0] at hh
        have hn := congrArg (fun x : Digest => x.toNat % 256) hh
        simp only [digestHeader_firstByte, WCT9.lowerTweak_firstByte hhp] at hn
        omega
  | wctLeaf index coord child => exact (WCT9.ftsLeafHeader_ne_digestHeader _ _ _ _).symm hh
  | forest index => simp only [Extract.Pos.hdr] at hh; exact digestHeader_ne_header _ _ _ _ _ _ hh
theorem sat_layerCounterSearch (T : Answers) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.layerCounterSearch]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_layerEncoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _
theorem sat_digestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) :=
  ClaudeWCT.WCT9.Wots.Structural.sat_digestSearch_of T _ rho message fun _ => Or.inl (posOf_digest _ _ _)
private theorem canonicalHeader_low (hdr : Digest) :
    (Extract.canonicalHeader (bytesLE 16 hdr)).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, SigGolfCandidate.T3M.Extract.bytesLE_header_words]
  unfold SigGolfCandidate.T3M.Extract.canonicalHeader
  split_ifs <;> simp [List.take_append, bytesLE_length]
private theorem low_ne_of_firstByte (x y : BitVec 128)
    (hc : 128 ≤ x.toNat % 256) (hr : y.toNat % 256 < 128) :
    x.extractLsb' 0 64 ≠ y.extractLsb' 0 64 := by
  intro he
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] at hv
  omega
theorem posOf_chain_offgraph (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (hoff : chainHeaderSpill tree leaf i step ≠ 0) :
    Extract.posOf (pad64 (WCT9.chainInputW lay tree leaf i step value)) = none := by
  apply posOf_eq_none
  intro p hb _ he
  have hlen : (pad64 (WCT9.chainInputW lay tree leaf i step value)).length = 64 := by
    rw [WCT9.chainInputW_padded]; simp [WCT9.chainInputW_length]
  -- C4: a chain header's low word carries type byte 193, so it is no top label.
  have hT : ¬ Extract.TopLow (Extract.hdrBlock (pad64 (WCT9.chainInputW lay tree leaf i step value))) := by
    rw [WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header, Extract.topLow_bytesLE_iff, Extract.tweakLow_eq_low,
      chainHeader_low, chainHeaderFlaggedLow_toNat]
    have := chainHeaderLow_band lay tree leaf i step
    split_ifs <;> omega
  rw [Extract.hdrKey_of_len64 hlen hT, WCT9.chainInputW_padded, Extract.hdrBlock, WCT9.chainInputW_header] at he
  have hn := congrArg (List.take 8) he
  rw [canonicalHeader_low] at hn
  have hp : (bytesLE 16 p.hdr).take 8 = bytesLE 8 (p.hdr.extractLsb' 0 64) := by
    rw [← Extract.Pos.canonicalHeader_eq hb]
    exact canonicalHeader_low _
  rw [hp] at hn
  have hlo := bytesLE_injective hn
  have hbit := chainHeader_offgraph_bit lay tree leaf i step
  rw [if_neg hoff] at hbit
  cases p with
  | chain lay' tree' leaf' i' step' =>
      exact chainHeader_offgraph_low_ne hoff hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2; omega) hlo
  | wctChain index coord child c step' =>
      exact WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _ hlo.symm
  | wctNode index coord level nd =>
      exact WCT9.wctNodeHeader_low_ne_chainHeader hb.2.1 _ _ _ _ _ _ _ hlo.symm
  | node lay' tree' level nd =>
      by_cases h0 : lay' = 0
      · -- C4: a top label's low word is below 4096, a chain header's carries type byte 193.
        subst h0
        have hv := congrArg BitVec.toNat hlo
        simp only [Extract.Pos.hdr] at hv
        rw [show ((0 : Layer).val) = 0 from rfl, WCT9.merkleTweak_top_low, topNodeWord_toNat64, chainHeader_low,
          chainHeaderFlaggedLow_toNat] at hv
        have := chainHeaderLow_band lay tree leaf i step
        have := topNodeWord_lt (2 ^ (height (0 : Layer) - level - 1) + nd)
        split_ifs at hv <;> omega
      · -- C2: a lower node word has bit 55 clear (layer byte `lay' - 1 ≤ 2`), an off-graph chain header has it set.
        obtain ⟨-, -, -, -, hnd⟩ := hb
        have h7 : height lay' ≤ 7 := by revert h0; fin_cases lay' <;> decide
        have hh := Extract.node_heap_lt128 hnd h7
        rw [hlo] at hbit
        simp only [Extract.Pos.hdr] at hbit
        rw [Extract.merkleTweak_layer_lower h0, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
          WCT9.lowerTweak_toNat hh] at hbit
        have h1 := Nat.mod_lt tree' (show 0 < 2 ^ 32 by decide)
        have h2 : (lay'.val - 1) % 256 ≤ 2 := by have := lay'.isLt; omega
        omega
  | _ =>
      exact low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
        (Extract.Pos.hdr_marker_lt hb (by simp only [Extract.Pos.cls]; (try split) <;> omega)
          (by simp only [Extract.Pos.cls]; (try split) <;> omega)) hlo
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7)
    (hG : WCT9.isG lay i = false := by simp) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.chain lay tree leaf i start count
      (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chain_zero]; exact QueriesSat.pure' _
  | succ count ih =>
      rw [Correctness.chain_add lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      rw [eval_honestChain]
      intro q hq
      rw [queried_chain_one, List.mem_singleton] at hq
      rw [hq]
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        have he : Extract.honestInput T (.chain lay tree leaf i (start + count)) =
            pad64 (chainInput lay tree leaf i (start + count)
              (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count))) := by
          simp only [Extract.honestInput]
          rw [WCT9.chainInputW_F hG]
          exact congrArg (fun v => pad64 (chainInput lay tree leaf i (start + count) v))
            (honestChainValueW_eq hG (Or.inr (Or.inr (by omega))))
        rw [← he]
        exact honestQuery_honest T (.chain lay tree leaf i (start + count)) hg
      · refine Or.inl ?_
        rw [← WCT9.chainInputW_F hG]
        exact posOf_chain_offgraph lay tree leaf i (start + count) _ hoff
theorem sat_halfHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (high : Bool) (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (WCT9.halfHash high input) := by
  intro q hq
  have he : SourceReplay.queried T (WCT9.halfHash high input) = [.inl (.inr (pad64 input))] := by
    cases high <;> rfl
  rw [he, List.mem_singleton] at hq
  rw [hq]
  exact h
/-- `sat_chain` for the chains of the current scheme (`chainW`; the chain-0 high half changes only the value after
step 6, which no query reads). -/
theorem sat_chainW (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7) :
    QueriesSat T (HonestQuery T) (WCT9.chainW lay tree leaf i start count
      (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chainW_zero']; exact QueriesSat.pure' _
  | succ count ih =>
      rw [chainW_add' lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      have heval : evalWithAnswerFn T (WCT9.chainW lay tree leaf i start count
          (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) start)) =
          honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count) := by
        unfold honestChainValueW
        rw [eval_chainW_add' T lay tree leaf i 0 start count, Nat.zero_add]
      rw [heval, chainW_one']
      apply sat_halfHash
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 7 := by
          unfold chainHeaderSpill at hoff
          omega
        refine Or.inr (Or.inl ⟨.chain lay tree leaf i (start + count), hg, ?_⟩)
        rfl
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)
/-! ### Top leaves (campaign T8D: family seeds through `topCoefs`, `buildLeafTop`, `buildTopTree`) -/
theorem sat_topPairsFrom (T : Answers) (first start : Nat) (init : List Digest) :
    QueriesSat T (HonestQuery T) (topPairsFrom first start init) := by
  unfold topPairsFrom
  refine QueriesSat.foldlM_range' _ _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
  unfold topSeedPair
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_topCoefs (T : Answers) (leaf : Nat) : QueriesSat T (HonestQuery T) (topCoefs leaf) := by
  unfold topCoefs
  exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
theorem sat_topFamilyCoefs (T : Answers) (leaf : Nat) (cc : List Digest × Digest) :
    QueriesSat T (HonestQuery T) (topFamilyCoefs leaf cc) := by
  unfold topFamilyCoefs
  split
  · unfold topCoefsK
    exact QueriesSat.bind (sat_topPairsFrom T _ _ _) (QueriesSat.pure' _)
  · exact QueriesSat.pure' _
theorem sat_buildLeafTopC (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTopC leaf (Correctness.topCoefList T leaf) digits signatureOnly) := by
  rw [Correctness.buildLeafTopC_eq]
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun i hi rows _ => ⟨?_, trivial⟩)) ?_
  · unfold Correctness.topLeafStep
    have hseed : topSeed (Correctness.topCoefList T leaf) leaf i = WCT9.wotsSeed T 0 0 leaf i := by
      rw [WCT9.wotsSeed_top, Correctness.leafSeed_top]; rfl
    rw [hseed]
    have hd := hvalid i hi
    have hw := Mask.width_le (0 : Layer) i
    have hc := Mask.chainCount_le (0 : Layer)
    -- witness stack: the top chain is `chainW 0 0` (G for even i ≤ 52), via the G-aware `sat_chainW`
    simp only [← WCT9.chainW_top_eq]
    have h0 : WCT9.wotsSeed T 0 0 leaf i =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0 := by
      simp [honestChainValueW, WCT9.chainW]
    rw [h0]
    refine QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i 0 _ (by decide) hleaf (by omega) (by omega)) ?_
    have heval : evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 (digits.getD i 0)
        (honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) 0)) =
        honestChainValueW T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i) (digits.getD i 0) := by
      have hz : ∀ v, evalWithAnswerFn T (WCT9.chainW (0 : Layer) 0 leaf i 0 0 v) = v := by
        intro v; simp [WCT9.chainW, evalWithAnswerFn_pure]
      unfold honestChainValueW
      rw [hz]
    rw [heval]
    split
    · exact QueriesSat.pure' _
    · exact QueriesSat.bind (sat_chainW T (0 : Layer) 0 leaf i _ _ (by decide) hleaf (by omega) (by omega))
        (QueriesSat.pure' _)
  · cases signatureOnly
    · have hr := Correctness.eval_topLeafRows T leaf digits hvalid false
      simp only [Correctness.LeafRows, Bool.false_eq_true, ite_false, min_self] at hr
      have he := Correctness.list_eq_range_map _ (leafEnd T 0 0 leaf) _ hr.1
        (fun i hi => hr.2.2.1 i (by rw [hr.1]; exact hi))
      simp only [Bool.false_eq_true, ite_false]
      refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [he, ← WCT9.wotsEnd_top]
      unfold leafHash
      exact sat_projHash _ _ (honestQuery_honest T (.leaf (0 : Layer) 0 leaf) hb)
    · simp only [ite_true]
      exact QueriesSat.pure' _
theorem sat_buildLeafTop (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTop leaf digits signatureOnly) := by
  rw [Correctness.buildLeafTop_eq]
  refine QueriesSat.bind (sat_topCoefs T leaf) ?_
  rw [Correctness.eval_topCoefs]
  have h := sat_buildLeafTopC T leaf digits hvalid signatureOnly hleaf hb
  rw [Correctness.buildLeafTopC_eq] at h
  exact h
theorem honestNonce_top_eq (T : Answers) (level c : Nat) (hl : level < 11) :
    WCT9.honestNonce T 0 0 level c = (evalWithAnswerFn T (topNodeAt (level + 1) (2 ^ (11 - level) + c)
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))).1 := by
  unfold WCT9.honestNonce
  rw [if_pos ⟨rfl, hl⟩, show height (0 : Layer) - level - 1 = 11 - level by simp [height]; omega]
theorem honestQuery_topTrial (T : Answers) (level c k : Nat) (hl : level < 11) (hc : c < 2 ^ (11 - level))
    (hk : k ≤ WCT9.honestNonce T 0 0 level c) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput (2 ^ (11 - level) + c) k
      (treeValue (WCT9.wotsTree T 0 0) level (2 * c)) (treeValue (WCT9.wotsTree T 0 0) level (2 * c + 1)))))) := by
  rw [← WCT9.merkleNodeInputN_top 0]
  rcases Nat.lt_or_ge k (WCT9.honestNonce T 0 0 level c) with hlt | hge
  · exact Or.inr (Or.inr ⟨level, c, k, hl, hc, hlt, rfl⟩)
  · have heq : k = WCT9.honestNonce T 0 0 level c := le_antisymm hk hge
    subst heq
    have hh : height (0 : Layer) - level - 1 = 11 - level := by simp [height]; omega
    refine Or.inr (Or.inl ⟨.node 0 0 level c, ⟨by norm_num, by simp [height]; omega, Or.inl rfl, fun _ => rfl,
      by rw [hh]; exact hc⟩, ?_⟩)
    show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - level - 1) + c)
      (WCT9.honestNonce T 0 0 level c) _ _)
    rw [hh]
    rfl
theorem honestQuery_topRoot (T : Answers) :
    HonestQuery T (.inl (.inr (pad64 (topNodeInput 1 0
      (treeValue (WCT9.wotsTree T 0 0) 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 1))))) := by
  refine Or.inr (Or.inl ⟨.node 0 0 11 0, ⟨by norm_num, by simp [height], Or.inl rfl, fun _ => rfl, by simp [height]⟩, ?_⟩)
  show _ = pad64 (WCT9.merkleNodeInputN (0 : Layer).val 0 (2 ^ (height 0 - 11 - 1) + 0)
    (WCT9.honestNonce T 0 0 11 0) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0)) (treeValue (WCT9.wotsTree T 0 0) 11 (2 * 0 + 1)))
  rw [WCT9.honestNonce_root]
  exact (congrArg pad64 (WCT9.merkleNodeInputN_top 0 1 0 _ _)).symm
theorem sat_buildTopTree (T : Answers) : QueriesSat T (HonestQuery T) buildTopTree := by
  unfold buildTopTree
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (Correctness.TopTreeState T) _ (Correctness.topTreeState_zero T)
    (fun leaf hleaf st hst => ⟨?_, Correctness.eval_topTreeStep T leaf st hst⟩)) ?_
  · have hl' : leaf < 2 ^ 32 := by
      have : 2 ^ height (0 : Layer) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le 0)
      omega
    unfold topTreeStep
    refine QueriesSat.bind (sat_topFamilyCoefs T leaf st.2) ?_
    rw [(Correctness.topTreeStep_coefs T leaf st hst).1]
    exact QueriesSat.bind (sat_buildLeafTopC T leaf [] (Cost.validDigits_nil 0) false hl'
      (Extract.leaf_bounded_of_treeBits (by decide) hleaf)) (QueriesSat.pure' _)
  · rw [(Correctness.eval_topTreeLoop T (2 ^ height 0)).1]
    have hroots : (List.range (2 ^ height 0)).map (Correctness.leafRoot T 0 0) =
        (List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0) := by rw [WCT9.wotsRoot_top]
    have hW : evalWithAnswerFn T (buildTopLevels ((List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0))) =
        WCT9.wotsTree T 0 0 := by unfold WCT9.wotsTree; rw [if_pos rfl]
    rw [hroots]
    apply SigGolfCandidate.T3.Security.Wots.Structural.sat_buildTopLevels T (HonestQuery T) _ (by simp [height])
    · rw [hW]; exact honestQuery_topRoot T
    · intro level c k hl hc hk
      rw [hW] at hk ⊢
      exact honestQuery_topTrial T level c k hl hc (le_of_le_of_eq hk (honestNonce_top_eq T level c hl).symm)
theorem sat_packedSecret (T : Answers) (lay : Layer) (tree q : Nat) (carry : Digest) :
    QueriesSat T (HonestQuery T) (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry) := by
  unfold WCT9.packedSecret
  split
  · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_lowerCoefs (T : Answers) (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    QueriesSat T (HonestQuery T) (WCT9.lowerCoefs lay tree leaf carry) := by
  unfold WCT9.lowerCoefs WCT9.lowerFamCoefs
  split
  · refine QueriesSat.bind (QueriesSat.bind ?_ (QueriesSat.pure' _)) (QueriesSat.pure' _)
    refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_leafRowsF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (WCT9.leafRowsF lay tree leaf digits (WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))) := by
  unfold WCT9.leafRowsF
  refine QueriesSat.foldlM_range _ _ (WCT9.LeafRowsF T lay tree leaf digits) _
    (by simp [WCT9.LeafRowsF])
    (fun i hi rows hrows => ⟨?_, WCT9.leafStepF_inv T hlay tree leaf digits hvalid i hi rows hrows⟩)
  unfold WCT9.leafStepF
  rw [WCT9.lowerFamilySeed_eq T hlay]
  have hd := hvalid i hi
  have hw := Mask.width_le lay i
  have hc := Mask.chainCount_le lay
  rw [← honestChainValueW_zero T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i)]
  refine QueriesSat.bind (sat_chainW T lay tree leaf i 0 (digits.getD i 0) htree hleaf (by omega) (by omega)) ?_
  rw [honestChainValueW_zero, show evalWithAnswerFn T (WCT9.chainW lay tree leaf i 0 (digits.getD i 0)
      (WCT9.wotsSeed T lay tree leaf i)) =
      honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (digits.getD i 0) from rfl]
  exact QueriesSat.bind (sat_chainW T lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
    htree hleaf (by omega) (by omega)) (QueriesSat.pure' _)
theorem sat_buildLeafPF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (carry : List Digest)
    (hcarry : leaf % WCT9.famGrp lay ≠ 0 → carry = WCT9.famCoefL T lay tree (WCT9.famOf lay leaf))
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (WCT9.buildLeafPF lay tree leaf digits carry) := by
  rw [WCT9.buildLeafPF_factor]
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [WCT9.eval_lowerCoefs T hlay tree leaf carry hcarry]
  dsimp only
  refine QueriesSat.bind (sat_leafRowsF T hlay tree leaf digits hvalid htree hleaf) ?_
  rw [WCT9.eval_leafRowsF T hlay tree leaf digits hvalid]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  exact sat_halfHash _ _ (honestQuery_honest T (.leaf lay tree leaf) hb)
theorem sat_treeRowsP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.treeRowsP lay tree selected digits) := by
  unfold WCT9.treeRowsP
  refine QueriesSat.foldlM_range _ _ (fun done rows => rows.2.2 = WCT9.treeCarry T lay tree done) _
    (by simp [WCT9.treeCarry]) (fun leaf hleaf rows hrows => ?_)
  have hd : Cost.ValidDigits lay (if leaf = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  have hl' : leaf < 2 ^ 32 := by
    have : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  have hcarry := WCT9.carryOk_treeCarry T lay tree leaf
  rw [← hrows] at hcarry
  refine ⟨QueriesSat.bind (sat_buildLeafPF T hlay tree leaf _ hd _ hcarry htree hl'
    (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_, ?_⟩
  · generalize evalWithAnswerFn T (WCT9.buildLeafPF lay tree leaf (if leaf = selected then digits else []) rows.2.2) = x
    obtain ⟨⟨root, values⟩, c⟩ := x
    exact QueriesSat.pure' _
  · simp only [evalWithAnswerFn_bind, WCT9.buildLeafPF_result T hlay tree leaf _ hd _ hcarry, evalWithAnswerFn_pure]
    show WCT9.leafCarryOut T lay tree leaf = WCT9.treeCarry T lay tree (leaf + 1)
    unfold WCT9.treeCarry
    rw [if_neg (show leaf + 1 ≠ 0 by omega), Nat.add_sub_cancel]
/-! ### C2 (FULL): the lower trees fold with `lowerLevel` (`lowerNodeHash`, the half of each heap) -/
def merkleQuery (lay tree heap : Nat) (left right : Digest) : SigGolfCandidate.T3.Spec.Domain :=
  .inl (.inr (pad64 (WCT9.merkleNodeInput lay tree heap left right)))
theorem sat_lowerNodeHash {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree heap : Nat)
    (left right : Digest) (h : Q (merkleQuery lay tree heap left right)) :
    QueriesSat T Q (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  exact sat_halfHash _ _ h
theorem sat_lowerLevel {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h level : Nat)
    (nodes : List Digest)
    (hq : ∀ i, i < nodes.length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))) :
    QueriesSat T Q (WCT9.lowerLevel lay tree h level nodes) := by
  unfold WCT9.lowerLevel
  exact QueriesSat.mapM _ _ (fun i hi => sat_lowerNodeHash _ _ _ _ _ (hq i (List.mem_range.mp hi)))
def lowerStep (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← WCT9.lowerLevel lay tree h level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])
def lowerFold (lay tree h : Nat) (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM (lowerStep lay tree h) [leaves]
theorem eval_lowerStep (T : Answers) (lay tree h : Nat) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (lowerStep lay tree h levels level) =
      levels ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h level (levels.getD (level - 1) []))] := by
  simp only [lowerStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
theorem eval_lowerSteps_append (T : Answers) (lay tree h : Nat) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM (lowerStep lay tree h) state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_lowerStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (WCT9.lowerLevel lay tree h x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩
theorem lowerFold_succ (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    lowerFold lay tree h leaves (n + 1) =
      (lowerFold lay tree h leaves n >>= fun state => lowerStep lay tree h state (1 + n)) := by
  unfold lowerFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem lowerFold_length (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (lowerFold lay tree h leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lowerFold_succ, evalWithAnswerFn_bind, eval_lowerStep, List.length_append, ih]
      simp
theorem lowerFold_prefix (T : Answers) (lay tree h : Nat) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (lowerFold lay tree h leaves m) =
      evalWithAnswerFn T (lowerFold lay tree h leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold lowerFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_lowerSteps_append T lay tree h _ _
theorem sat_lowerFold {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (lay tree h : Nat)
    (leaves : List Digest) (n : Nat) (hn : n ≤ h)
    (hq : ∀ level, level < n → ∀ node,
      node < ((evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD level []).length / 2 →
      Q (merkleQuery lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node))
        (treeValue (evalWithAnswerFn T (lowerFold lay tree h leaves n)) level (2 * node + 1)))) :
    QueriesSat T Q (lowerFold lay tree h leaves n) := by
  unfold lowerFold
  refine QueriesSat.foldlM_range' 1 n _
    (fun i state => state = evalWithAnswerFn T (lowerFold lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold lowerStep
    refine QueriesSat.bind (sat_lowerLevel _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := lowerFold_length T lay tree h leaves i
    obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves i n (by omega)
    have hget : (evalWithAnswerFn T (lowerFold lay tree h leaves n)).getD i [] =
        (evalWithAnswerFn T (lowerFold lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i (by omega) node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [lowerFold_succ, evalWithAnswerFn_bind]
theorem honestQuery_lowerNode (T : Answers) (lay : Layer) (tree : Nat) (ht : tree < 2 ^ Extract.treeBits lay)
    (level node : Nat) (hlevel : level < height lay) (hroot : lay = 0 ∨ level + 1 < height lay) (hlay : lay ≠ 0)
    (hnode : node < ((WCT9.wotsTree T lay tree).getD level []).length / 2) :
    HonestQuery T (merkleQuery lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (WCT9.wotsTree T lay tree) level (2 * node)) (treeValue (WCT9.wotsTree T lay tree) level (2 * node + 1))) := by
  have hshape := (WCT9.wotsTree_correct T hlay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine Or.inr (Or.inl ⟨.node lay tree level node, ⟨by
    have h31 := lt_of_le_of_lt (Nat.le_add_right _ _) (Extract.routed_lt_of_treeBits ht (Nat.one_le_two_pow))
    have hle : tree ≤ tree * 2 ^ height lay := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
    omega, hlevel, hroot, Extract.tree_zero_of_treeBits ht, by rw [hw, hpow] at hnode; omega⟩, ?_⟩)
  show pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - (level + 1)) + node) _ _) =
    pad64 (WCT9.merkleNodeInputN lay.val tree (2 ^ (height lay - level - 1) + node) (WCT9.honestNonce T lay tree level node) _ _)
  rw [WCT9.honestInputN_lower T hlay, Nat.sub_sub]
theorem buildLevelsBelow_eq_fold (tag lay tree h : Nat) (leaves : List Digest) :
    WCT9.buildLevelsBelow tag lay tree h leaves = lowerFold lay tree h leaves (h - 1) := rfl
theorem lowerLevels_eq_fold (lay tree h : Nat) (leaves : List Digest) :
    WCT9.lowerLevels lay tree h leaves = lowerFold lay tree h leaves h := rfl
theorem below_getD (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (level : Nat) (hl : level + 1 < h) :
    (evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)).getD level [] =
      (evalWithAnswerFn T (WCT9.lowerLevels lay tree h leaves)).getD level [] := by
  rw [buildLevelsBelow_eq_fold, lowerLevels_eq_fold]
  obtain ⟨extra, hext⟩ := lowerFold_prefix T lay tree h leaves (h - 1) h (by omega)
  have hlen := lowerFold_length T lay tree h leaves (h - 1)
  rw [hext, List.getD_append _ _ _ _ (by omega)]
theorem sat_buildTreeP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.buildTreeP lay tree selected digits) := by
  rw [WCT9.buildTreeP_factor]
  refine QueriesSat.bind (sat_treeRowsP T hlay tree selected digits hvalid htree ht) ?_
  obtain ⟨hlen, hroot, -, -⟩ := WCT9.eval_treeRowsP T hlay tree selected digits hvalid
  have hroots := Correctness.list_eq_range_map _ _ _ hlen hroot
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [hroots, buildLevelsBelow_eq_fold]
  refine sat_lowerFold _ _ _ _ _ (by omega) ?_
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay) ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))
    level (by omega)
  rw [← buildLevelsBelow_eq_fold 3, hg] at hnode
  rw [← buildLevelsBelow_eq_fold 3]
  have hwt : WCT9.wotsTree T lay tree = evalWithAnswerFn T (WCT9.lowerLevels lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))) := by
    unfold WCT9.wotsTree; rw [if_neg hlay]
  have := honestQuery_lowerNode T lay tree ht level node (by omega) (Or.inr (by omega)) hlay (by rw [hwt]; exact hnode)
  rw [hwt] at this
  simp only [treeValue, hg]
  exact this
theorem sat_keygenPayload (T : Answers) : QueriesSat T (HonestQuery T) keygenPayload := by
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine QueriesSat.bind (sat_buildTopTree T) ?_
  generalize evalWithAnswerFn T buildTopTree = levels
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun level _ => sat_maskedLevel T _ _) (QueriesSat.pure' _)
theorem sat_keygen (T : Answers) : QueriesSat T (HonestQuery T) keygen := by
  unfold keygen
  refine QueriesSat.bind (sat_keygenPayload T) ?_
  generalize evalWithAnswerFn T keygenPayload = x
  obtain ⟨publicKey, region⟩ := x
  exact QueriesSat.bind (sat_privateMac T _) (QueriesSat.pure' _)
theorem sat_topPath (T : Answers) (cache : Cache) (leaf : Nat) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (topPath cache leaf) := by
  unfold topPath
  exact QueriesSat.mapM _ _ fun level _ => QueriesSat.bind (sat_mask T _ _) (QueriesSat.pure' _)
theorem sat_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (signTop cache leaf digits) := by
  unfold signTop
  refine QueriesSat.bind (sat_buildLeafTop T leaf digits hvalid true (by omega)
    (Extract.leaf_bounded_of_treeBits (by decide) (by simpa [height] using hleaf))) ?_
  generalize evalWithAnswerFn T (buildLeafTop leaf digits true) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.bind (sat_topPath T cache leaf hleaf) (QueriesSat.pure' _)
#print axioms sat_buildTreeP
#print axioms sat_keygen
#print axioms sat_signTop
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Stage 2 (C3, #866): the retained-prefix chain queries what `WCT9.chainW` queries. -/
theorem queried_chainPrefixes (T : Answers) (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    queried T (chainPrefixes lay tree leaf i start count value) =
      queried T (WCT9.chainW lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
      rw [lower_chainW_succ_first]
      simp only [chainPrefixes,queried_bind,queried_pure,List.append_nil,ih]

theorem sat_chainPrefixes (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2^40) (hleaf : leaf < 2^32) (hi : i < 2^24) (hcount : start+count≤7) :
    QueriesSat T (HonestQuery T) (chainPrefixes lay tree leaf i start count
      (honestChainValueW T lay tree leaf i (wotsSeed T lay tree leaf i) start)) := by
  intro q hq
  change q ∈ queried T (chainPrefixes lay tree leaf i start count
    (honestChainValueW T lay tree leaf i (wotsSeed T lay tree leaf i) start)) at hq
  rw [queried_chainPrefixes] at hq
  exact sat_chainW T lay tree leaf i start count htree hleaf hi hcount q hq

theorem sat_buildLeafPrefixes (T : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : List Digest)
    (hcarry : leaf % famGrp lay ≠ 0 → carry = famCoefL T lay tree (famOf lay leaf))
    (htree : tree < 2^40) (hleaf : leaf < 2^32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [eval_lowerCoefs T hlay tree leaf carry hcarry]
  dsimp only
  refine QueriesSat.bind (QueriesSat.mapM _ _ (fun i hi => ?_)) ?_
  · rw [lowerFamilySeed_eq T hlay, ← honestChainValueW_zero T lay tree leaf i (wotsSeed T lay tree leaf i)]
    exact sat_chainPrefixes T lay tree leaf i 0 (maxDigit lay i) htree hleaf
      (by have := Mask.chainCount_le lay; have := List.mem_range.mp hi; omega)
      (by have := Mask.width_le lay i; omega)
  · rw [Correctness.eval_mapM]
    simp only [lowerFamilySeed_eq T hlay]
    change QueriesSat T (HonestQuery T) (do
      let root ← lowerLeafHash lay tree leaf
        ((List.range (chainCount lay)).map fun i =>
          ((prefixRows T lay tree leaf).getD i []).getD (maxDigit lay i) 0)
      pure ((root,prefixRows T lay tree leaf),leafCarryOut T lay tree leaf))
    have he : (List.range (chainCount lay)).map (fun i =>
        ((prefixRows T lay tree leaf).getD i []).getD (maxDigit lay i) 0) =
        (List.range (chainCount lay)).map (wotsEnd T lay tree leaf) := by
      apply List.map_congr_left
      intro i hi
      exact prefixRows_getD T lay tree leaf i _ (List.mem_range.mp hi) (by omega)
    rw [he]
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    rw [WCT9.lowerLeafHash_eq]
    unfold WCT9.lowerHash
    exact sat_halfHash _ _ (honestQuery_honest T (.leaf lay tree leaf) hb)
#print axioms queried_chainPrefixes
#print axioms sat_chainPrefixes
#print axioms sat_buildLeafPrefixes
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sat_canonical_search (T : Answers) (lay : Layer) (floor tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, QueriesSat T (HonestQuery T)
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [CanonicalPolicy.layerCounterSearchAt]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_layerEncoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _

theorem sat_sharedDigestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (sharedDigestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [sharedDigestSearch]
      refine QueriesSat.bind (sat_publicHash _ (Or.inl (posOf_digest rho message (BitVec.ofNat 32 counter)))) ?_
      split
      · exact QueriesSat.pure' _
      · exact ih _

theorem sat_searchPreparedLayers (T : Answers) (cache : SigGolfCandidate.T3.Cache)
    (index : Nat) (prepared : PreparedRoots) (forest : PairRoot) :
    QueriesSat T (HonestQuery T) (searchPreparedLayers cache index prepared forest) := by
  unfold searchPreparedLayers
  refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
  cases hs : evalWithAnswerFn T (CanonicalPolicy.layerCounterSearchAt 0
      (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2
      (route index 0).1 (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2)
      0 (searchLimit 0)) with
  | none => exact QueriesSat.pure' _
  | some found =>
      obtain ⟨counter,digits,low⟩ := found
      have hd := (canonical_search_valid_credit T 0 _ _ _ _ _ _ counter digits low
        (ClaudeWCT.W9.T3.Security.Wots.searchLimit_fits _) hs).1
      dsimp only
      split
      · exact QueriesSat.pure' _
      · refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
        split
        · split
          · exact QueriesSat.pure' _
          · refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
            split
            · split
              · exact QueriesSat.pure' _
              · refine QueriesSat.bind (sat_canonical_search T _ _ _ _ _ _ _) ?_
                split
                · exact QueriesSat.bind (sat_signTop T cache _ digits hd (route_leaf_bound index 0))
                    (QueriesSat.pure' _)
                · exact QueriesSat.pure' _
            · exact QueriesSat.pure' _
        · exact QueriesSat.pure' _
#print axioms sat_canonical_search
#print axioms sat_sharedDigestSearch
#print axioms sat_searchPreparedLayers
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sat_prefixTreeRows (T : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (htree : tree < 2^40) (ht : tree < 2^Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (prefixTreeRows lay tree selected) := by
  unfold prefixTreeRows
  refine QueriesSat.foldlM_range _ _ (fun done rows => rows.2.2 = treeCarry T lay tree done) _
    (by simp [treeCarry]) (fun leaf hleaf rows hrows => ?_)
  have hl : leaf < 2^32 := by
    have : 2^height lay ≤ 2^12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  have hc := carryOk_treeCarry T lay tree leaf
  rw [←hrows] at hc
  refine ⟨?_,?_⟩
  · by_cases hs : leaf = selected
    · simp only [if_pos hs]
      refine QueriesSat.bind (sat_buildLeafPrefixes T hlay tree leaf rows.2.2 hc htree hl
        (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_
      generalize evalWithAnswerFn T (buildLeafPrefixes lay tree leaf rows.2.2) = value
      rcases value with ⟨⟨root,prefixes⟩,carry⟩
      exact QueriesSat.pure' _
    · simp only [if_neg hs]
      refine QueriesSat.bind (sat_buildLeafPF T hlay tree leaf [] (Cost.validDigits_nil lay)
        rows.2.2 hc htree hl (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_
      generalize evalWithAnswerFn T (buildLeafPF lay tree leaf [] rows.2.2) = value
      rcases value with ⟨⟨root,values⟩,carry⟩
      exact QueriesSat.bind (QueriesSat.pure' _) (QueriesSat.pure' _)
  · by_cases hs : leaf = selected
    · simp only [if_pos hs,evalWithAnswerFn_bind,buildLeafPrefixes_result T hlay tree leaf _ hc,
        evalWithAnswerFn_pure]
      unfold treeCarry
      rw [if_neg (show leaf+1≠0 by omega),Nat.add_sub_cancel]
    · simp only [if_neg hs,evalWithAnswerFn_bind,
        buildLeafPF_result T hlay tree leaf [] (Cost.validDigits_nil lay) _ hc,evalWithAnswerFn_pure]
      unfold treeCarry
      rw [if_neg (show leaf+1≠0 by omega),Nat.add_sub_cancel]

theorem sat_buildTreePrefixes (T : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (htree : tree < 2^40) (ht : tree < 2^Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (buildTreePrefixes lay tree selected) := by
  rw [buildTreePrefixes_factor]
  refine QueriesSat.bind (sat_prefixTreeRows T hlay tree selected htree ht) ?_
  have hr := eval_prefixTreeRows T hlay tree selected
  have hroots := Correctness.list_eq_range_map _ _ _ hr.1 hr.2.1
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  -- C2 (#866): the lower levels are `lowerLevel` folds (as in `sat_buildTreeP`).
  rw [hroots, buildLevelsBelow_eq_fold]
  refine sat_lowerFold _ _ _ _ _ (by omega) ?_
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay) ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))
    level (by omega)
  rw [← buildLevelsBelow_eq_fold 3, hg] at hnode
  rw [← buildLevelsBelow_eq_fold 3]
  have hwt : WCT9.wotsTree T lay tree = evalWithAnswerFn T (WCT9.lowerLevels lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))) := by
    unfold WCT9.wotsTree; rw [if_neg hlay]
  have := honestQuery_lowerNode T lay tree ht level node (by omega) (Or.inr (by omega)) hlay (by rw [hwt]; exact hnode)
  rw [hwt] at this
  simp only [treeValue, hg]
  exact this

theorem sat_prepareRoots (T : Answers) (index : Nat) (hi : index<2^31) :
    QueriesSat T (HonestQuery T) (prepareRoots index) := by
  unfold prepareRoots
  refine QueriesSat.bind (sat_buildTreePrefixes T (by decide : (1 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 1) (Extract.route_tree_treeBits index hi 1)) ?_
  refine QueriesSat.bind (sat_buildTreePrefixes T (by decide : (2 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 2) (Extract.route_tree_treeBits index hi 2)) ?_
  exact QueriesSat.bind (sat_buildTreePrefixes T (by decide : (3 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 3) (Extract.route_tree_treeBits index hi 3)) (QueriesSat.pure' _)
#print axioms sat_prefixTreeRows
#print axioms sat_buildTreePrefixes
#print axioms sat_prepareRoots
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

theorem sat_ftsCoefs (coord : Coord) :
    QueriesSat T (HonestQuery T) (ftsCoefs index coord.val) := by
  unfold ftsCoefs
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun j hj acc _ => ⟨?_, trivial⟩)
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)

#check sat_ftsCoefs

include hidx in
theorem sat_fts_chain (coord : Coord) (child : Child) (t : Fin 6) (start count : Nat)
    (hcount : start+count ≤ 4) :
    QueriesSat T (HonestQuery T)
      (ClaudeWCT.WCT9.chain index coord.val child.val t.val start count
        (ftsChainValue T index coord child t start)) := by
  induction count with
  | zero => rw [chain_zero']; exact QueriesSat.pure' _
  | succ count ih =>
      rw [chain_add index coord.val child.val t.val start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      rw [eval_ftsChain]
      intro q hq
      rw [ClaudeWCT.WCT9.Wots.queried_chain_one, List.mem_singleton] at hq
      subst hq
      refine Or.inr (Or.inl ⟨.wctChain index coord.val child.val t.val (start+count),
        ⟨hidx,coord.isLt,child.isLt,t.isLt,by omega⟩,?_⟩)
      exact (Extract.honestInput_ofFts T index (.chain coord child t (start+count)) (by change start+count<4;omega)).symm

#check sat_fts_chain

include hidx in
theorem sat_fts_childStep (coord : Coord) (child : Child) (word : Rank)
    (t : Fin 6) (rows : List Digest × List Digest) :
    QueriesSat T (HonestQuery T)
      (childStep index coord.val child.val word (List.ofFn (ftsCoef T index coord.val)) rows t) := by
  unfold childStep
  have hd:=wordDigit_le_four word t
  have hz : ftsFamilySeed (List.ofFn (ftsCoef T index coord.val)) child.val t.val=
      ftsChainValue T index coord child t 0 := rfl
  simp only []
  rw [hz]
  refine QueriesSat.bind (sat_fts_chain T index hidx coord child t 0 _ (by omega)) ?_
  rw [eval_ftsChain,Nat.zero_add]
  exact QueriesSat.bind (sat_fts_chain T index hidx coord child _ _ _ (by omega)) (QueriesSat.pure' _)

#check sat_fts_childStep

include hidx in
theorem sat_fts_childRows (coord : Coord) (child : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (childRows index coord.val child.val word (List.ofFn (ftsCoef T index coord.val))) := by
  unfold childRows
  refine QueriesSat.foldlM_list _ _ (fun _ _ => True) _ trivial (fun i hi rows _ => ⟨?_,trivial⟩)
  have hi6:i<6 := by simpa using hi
  simp only [List.getElem_finRange,Fin.cast_mk]
  exact sat_fts_childStep T index hidx coord child word ⟨i,hi6⟩ rows

#check sat_fts_childRows

include hidx in
theorem sat_fts_buildChild (coord : Coord) (child : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (buildChildH (128 + Extract.Paired.physical coord.val child.val) index coord.val child.val word
        (List.ofFn (ftsCoef T index coord.val))
        (Extract.Paired.pads T index coord.val (Extract.Paired.physical coord.val child.val/64)).1) := by
  rw [buildChildH_factor]
  refine QueriesSat.bind (sat_fts_childRows T index hidx coord child word) ?_
  rw [eval_childRows_ends T index coord.val child.val word]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [ClaudeWCT.W9.T3M.WctExtract.leafHashH_eq_ftsHash]
  refine ClaudeWCT.WCT9.Wots.Structural.sat_ftsHash T _ _ ?_
  refine Or.inr (Or.inl ⟨.wctLeaf index coord.val child.val,⟨hidx,coord.isLt,child.isLt⟩,?_⟩)
  have he : List.ofFn (fun t : Fin 6 => chainEnd T index coord.val child.val t) =
      Extract.wctEnds T index coord.val child.val := by
    unfold Extract.wctEnds
    apply congrArg List.ofFn
    funext t
    rfl
  change pad64 (Extract.wctLeafInputP _ _ _ _ _) = pad64 (Extract.wctLeafInputP _ _ _ _ _)
  rw [he]

 #check sat_fts_buildChild

theorem physical_raw (first : Bool) (j : Nat) (hj:j<128) :
    SharedForest.physicalChild first (SharedForest.rawChild first j)=j := by
  cases first <;> simp only [SharedForest.physicalChild,SharedForest.rawChild,Bool.false_eq_true,↓reduceIte] <;> omega

 #check physical_raw

include hidx in
theorem sat_sharedRows (coord : Coord) (selected : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (SharedForest.sharedRows (Extract.Paired.first coord.val) index coord.val selected word
        (List.ofFn (ftsCoef T index coord.val)) (Extract.Paired.pads T index coord.val)) := by
  unfold SharedForest.sharedRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j hj rows _ => ⟨?_,trivial⟩)
  have hr:=SharedForest.rawChild_lt (Extract.Paired.first coord.val) j hj
  have hc:=sat_fts_buildChild T index hidx coord ⟨_,hr⟩ word
  simp only [Extract.Paired.physical,physical_raw _ j hj] at hc
  exact QueriesSat.bind hc (QueriesSat.pure' _)

#print axioms sat_sharedRows
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

 include hidx in
theorem honest_sharedNode_input (coord : Coord) (heap : Nat)
    (hcut:SharedForest.heapCut (Extract.Paired.first coord.val) ≤ heap) (hh:heap<128) :
    HonestQuery T (.inl (.inr (pad64 (wctTopInput coord.val index heap
      ((Extract.Paired.nodes T index coord.val).getD (2*heap) 0)
      (if 4≤heap ∧ heap<8 then (Extract.Paired.pads T index coord.val (heap/2-2)).2 else 0)
      ((Extract.Paired.nodes T index coord.val).getD (2*heap+1) 0))))) := by
  have h2:2≤heap := (SharedForest.heapCut_bounds _).1.trans hcut
  obtain ⟨hL,hN,hH⟩:=Extract.heap_decomp h2 hh
  have hused : Extract.Paired.first coord.val=true → Extract.heapLevel heap<5 := by
    intro hf
    have h4:4≤heap := by simpa only [SharedForest.heapCut,hf,if_true] using hcut
    have hlog:2≤Nat.log 2 heap := Nat.le_log_of_pow_le (by decide) h4
    unfold Extract.heapLevel;omega
  refine Or.inr (Or.inl ⟨.wctNode index coord.val (Extract.heapLevel heap) (Extract.heapNode heap),
    ⟨⟨hidx,coord.isLt,hL,hN⟩,hused⟩,?_⟩)
  have hsub:7-Extract.heapLevel heap-1=6-Extract.heapLevel heap := by omega
  rw [hsub] at hH hN
  have he : Extract.heapLevel heap=4 ↔ 4≤heap ∧ heap<8 := by
    have hlo:2^(6-Extract.heapLevel heap)≤heap := by omega
    have hhi:heap<2*2^(6-Extract.heapLevel heap) := by omega
    generalize Extract.heapLevel heap=L at hL hlo hhi ⊢
    interval_cases L <;> norm_num at hlo hhi ⊢ <;> omega
  simp only [Extract.Paired.honestInput,hH,he]

 include hidx in
theorem sat_sharedNode (coord : Coord) (heap : Nat)
    (hcut:SharedForest.heapCut (Extract.Paired.first coord.val) ≤ heap) (hh:heap<128) :
    QueriesSat T (HonestQuery T)
      (SharedForest.sharedNode (Extract.Paired.first coord.val) coord.val index heap
        (Extract.Paired.pads T index coord.val)
        ((Extract.Paired.nodes T index coord.val).getD (2*heap) 0)
        ((Extract.Paired.nodes T index coord.val).getD (2*heap+1) 0)) := by
  have hq:=honest_sharedNode_input T index hidx coord heap hcut hh
  unfold SharedForest.sharedNode
  split_ifs with h4 h8 hf
  · unfold SharedForest.sharedOuterHash
    rw [if_neg (by omega : ¬(4≤heap ∧ heap<8))] at hq
    split_ifs
    · exact SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash _ hq
    · exact ClaudeWCT.WCT9.Wots.Structural.sat_highHash T _ hq
  · rw [if_pos (show 4≤heap ∧ heap<8 by omega)] at hq
    exact ClaudeWCT.WCT9.Wots.Structural.sat_highHash T _ hq
  · rw [if_pos (show 4≤heap ∧ heap<8 by omega)] at hq
    exact SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash _ hq
  · rw [if_neg (by omega : ¬(4≤heap ∧ heap<8)),wctTopInput_zero] at hq
    rw [nodeHashH_eq]
    exact ClaudeWCT.WCT9.Wots.Structural.sat_ftsHash T _ _ hq

#print axioms sat_sharedNode
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

 theorem sharedNodes_actual (coord : Coord) :
    SharedForest.sharedNodes T (Extract.Paired.first coord.val) index coord.val
      (Extract.Paired.pads T index coord.val)=Extract.Paired.nodes T index coord.val := by
  fin_cases coord <;> simp only [Extract.Paired.nodes, Extract.Paired.first, SharedForest.firstNodes, SharedForest.secondNodes]
  all_goals norm_num
  all_goals first | rfl | (congr 1;funext b;simp only [Extract.Paired.pads,Extract.Paired.first,SharedForest.firstNodes];rfl)

theorem sharedHeap_arithmetic (cut done : Nat) (hcut : 2 ≤ cut) (hd : done < 128-cut) :
    cut ≤ 127-done ∧ 127-done < 128 ∧ 128-(128-cut) ≤ 127-done := by omega

theorem sharedHeap_other_arithmetic (done j : Nat) (hd : done < 128)
    (hj : 128-(done+1) ≤ j) (hne : j ≠ 127-done) : 128-done ≤ j := by omega

/-- Arithmetic side conditions of one `sat_sharedHeap` step, kept out of the step's large context so `omega`
never compares the heap-array atoms there. -/
theorem sharedHeap_child_arithmetic (cut done : Nat) (hcut : 2 ≤ cut) (hd : done < 128-cut) :
    128-done ≤ 2*(127-done) ∧ 128-done ≤ 2*(127-done)+1 ∧ 127-done < 256 := by omega

 include hidx in
set_option maxHeartbeats 800000 in
theorem sat_sharedHeap (coord : Coord) :
    QueriesSat T (HonestQuery T)
      (SharedForest.sharedHeap (Extract.Paired.first coord.val) index coord.val
        (Extract.Paired.pads T index coord.val)
        (SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
          (Extract.Paired.pads T index coord.val))) := by
  have hg:=SharedForest.sharedNodes_graph T (Extract.Paired.first coord.val) index coord.val
    (Extract.Paired.pads T index coord.val)
  rw [sharedNodes_actual T index coord] at hg
  obtain ⟨hsize,hleaf,hnode⟩:=hg
  have hcut:=SharedForest.heapCut_bounds (Extract.Paired.first coord.val)
  unfold SharedForest.sharedHeap
  rw [show (if Extract.Paired.first coord.val = true then 124 else 126) =
      128-SharedForest.heapCut (Extract.Paired.first coord.val) by
    cases hf : Extract.Paired.first coord.val <;> rfl]
  change QueriesSat T (HonestQuery T) ((List.range' (SharedForest.heapCut (Extract.Paired.first coord.val))
    (128-SharedForest.heapCut (Extract.Paired.first coord.val))).reverse.foldlM _ _)
  refine QueriesSat.foldlM_list _ _ (ClaudeWCT.WCT9.Wots.Structural.HeapAgree (Extract.Paired.nodes T index coord.val)) _ ?_ ?_
  · refine ⟨by simp [SharedForest.sharedLeaves],?_⟩
    intro j hj
    by_cases hj':j<256
    · simp only [Array.getD_eq_getD_getElem?,List.getElem?_toArray,←List.getD_eq_getElem?_getD]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate];omega),
        List.length_replicate,←hleaf j hj hj']
      simp only [Array.getD_eq_getD_getElem?]
    · have h1 : ((List.replicate 128 (0:Digest)++
          SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
            (Extract.Paired.pads T index coord.val)).toArray).getD j 0=0 := by
        simp only [Array.getD_eq_getD_getElem?,List.getElem?_toArray]
        rw [List.getElem?_eq_none (by simp [SharedForest.sharedLeaves];omega)]
        rfl
      have h2:(Extract.Paired.nodes T index coord.val).getD j 0=0 := by
        simp only [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [h1,h2]
  · intro done hdone nodes ⟨hsz,hagree⟩
    have hd:done<128-SharedForest.heapCut (Extract.Paired.first coord.val) := by
      simpa only [List.length_reverse,List.length_range'] using hdone
    rw [SharedForest.shared_heap_order _ done hd]
    obtain ⟨ha,hb,hc⟩ := sharedHeap_arithmetic _ _ hcut.1 hd
    obtain ⟨hl2,hr2,hs⟩ := sharedHeap_child_arithmetic _ _ hcut.1 hd
    have hl:nodes.getD (2*(127-done)) 0=(Extract.Paired.nodes T index coord.val).getD (2*(127-done)) 0 :=
      hagree (2*(127-done)) hl2
    have hr:nodes.getD (2*(127-done)+1) 0=(Extract.Paired.nodes T index coord.val).getD (2*(127-done)+1) 0 :=
      hagree (2*(127-done)+1) hr2
    refine ⟨?_,?_⟩
    · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [hl,hr]
      exact sat_sharedNode T index hidx coord (127-done) ha hb
    · simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
      refine ⟨by rw [Array.size_set!,hsz],?_⟩
      intro j hj
      by_cases he:j=127-done
      · subst he
        rw [getD_set_self nodes (127-done) _ (by rw [hsz]; exact hs),hl,hr]
        exact (hnode (127-done) ha hb hc).symm
      · rw [getD_set_other nodes _ _ _ (Ne.symm he)]
        exact hagree j (sharedHeap_other_arithmetic done j (lt_of_lt_of_le hd (Nat.sub_le _ _)) hj he)

 theorem sharedRows_roots (coord : Coord) (selected : Child) (word : Rank) :
    (evalWithAnswerFn T (SharedForest.sharedRows (Extract.Paired.first coord.val) index coord.val
      selected word (List.ofFn (ftsCoef T index coord.val)) (Extract.Paired.pads T index coord.val))).1=
      SharedForest.sharedLeaves T (Extract.Paired.first coord.val) index coord.val
        (Extract.Paired.pads T index coord.val) := by
  obtain ⟨hlen,hroot,-⟩:=SharedForest.eval_sharedRows T (Extract.Paired.first coord.val) index coord.val
    selected word (Extract.Paired.pads T index coord.val)
  apply List.ext_getElem (by simpa only [SharedForest.sharedLeaves,List.length_ofFn] using hlen)
  intro j hj hk
  simpa only [SharedForest.sharedLeaves,List.getD_eq_getElem _ _ hj,List.getElem_ofFn] using hroot j (by omega)

 include hidx in
theorem sat_sharedCoordinate (coord : Coord) (selected : Child) (word : Rank) :
    QueriesSat T (HonestQuery T)
      (SharedForest.buildSharedCoordinate (Extract.Paired.first coord.val) index coord.val selected word
        (Extract.Paired.pads T index coord.val)) := by
  unfold SharedForest.buildSharedCoordinate
  refine QueriesSat.bind (sat_ftsCoefs T index coord) ?_
  rw [eval_ftsCoefs]
  change QueriesSat T (HonestQuery T) (SharedForest.sharedRows _ _ _ _ _ _ _ >>= _)
  refine QueriesSat.bind (sat_sharedRows T index hidx coord selected word) ?_
  rw [sharedRows_roots]
  exact QueriesSat.bind (sat_sharedHeap T index hidx coord) (QueriesSat.pure' _)

#print axioms sat_sharedCoordinate
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SharedForest.sharedNodes SharedForest.firstNodes SharedForest.secondNodes
attribute [local irreducible] Extract.Paired.pads Extract.Paired.pairPrev Extract.Paired.nodes
variable (T : Answers) (index : Nat) (hidx : index < 2^31)

 include hidx in
theorem sat_buildPair (pair : Fin 4) (s : SharedForest.Selection) (aWord bWord : Rank) :
    QueriesSat T (HonestQuery T) (SharedForest.buildPair index pair.val s aWord bWord
      (Extract.Paired.pairPrev T index pair.val)) := by
  have ha:=sat_sharedCoordinate T index hidx ⟨2*pair.val,by have:=pair.isLt;omega⟩
    (SharedForest.firstChild s) aWord
  have hA:SharedForest.buildSharedCoordinate true index (2*pair.val) (SharedForest.firstChild s) aWord
      (fun _=>Extract.Paired.pairPrev T index pair.val)=
    SharedForest.buildSharedCoordinate (Extract.Paired.first (2*pair.val)) index (2*pair.val)
      (SharedForest.firstChild s) aWord (Extract.Paired.pads T index (2*pair.val)) := by
    have hf : Extract.Paired.first (2*pair.val) = true := by
      simp only [Extract.Paired.first, decide_eq_true_eq]
      have := pair.isLt
      omega
    rw [hf]
    congr 1
    funext branch
    simp only [Extract.Paired.pads, if_neg (show 2*pair.val ≠ 8 by have := pair.isLt;omega),hf,if_true,
      Nat.mul_div_cancel_left pair.val (by decide : 0<2)]
  rw [←hA] at ha
  unfold SharedForest.buildPair
  refine QueriesSat.bind ha ?_
  rw [SharedForest.buildSharedCoordinate_result]
  have hb:=sat_sharedCoordinate T index hidx ⟨2*pair.val+1,by have:=pair.isLt;omega⟩
    (SharedForest.secondChild s) bWord
  have hB:SharedForest.buildSharedCoordinate false index (2*pair.val+1) (SharedForest.secondChild s) bWord
      (SharedForest.nodesPair (SharedForest.sharedNodes T true index (2*pair.val)
        (fun _=>Extract.Paired.pairPrev T index pair.val)))=
    SharedForest.buildSharedCoordinate (Extract.Paired.first (2*pair.val+1)) index (2*pair.val+1)
      (SharedForest.secondChild s) bWord (Extract.Paired.pads T index (2*pair.val+1)) := by
    have hf : Extract.Paired.first (2*pair.val+1) = false := by
      simp only [Extract.Paired.first, decide_eq_false_iff_not]
      omega
    rw [hf]
    congr 1
    funext branch
    simp only [Extract.Paired.pads, if_neg (show 2*pair.val+1 ≠ 8 by omega),hf,Bool.false_eq_true,if_false]
    rw [show (2*pair.val+1)/2 = pair.val by omega]
    unfold SharedForest.firstNodes
    rfl
  rw [←hB] at hb
  exact QueriesSat.bind hb (QueriesSat.pure' _)

 include hidx in
theorem sat_buildSingleton (s : Child) (word : Rank) :
    QueriesSat T (HonestQuery T) (SharedForest.buildSingleton index s word (Extract.Paired.pairPrev T index 4)) := by
  unfold SharedForest.buildSingleton
  have hs := sat_sharedCoordinate T index hidx 8 s word
  have hf : Extract.Paired.first 8 = false := by decide
  have hp : Extract.Paired.pads T index 8 = (fun _ => Extract.Paired.pairPrev T index 4) := by
    funext branch
    unfold Extract.Paired.pads
    rw [if_pos rfl]
  change QueriesSat T (HonestQuery T)
    (SharedForest.buildSharedCoordinate (Extract.Paired.first 8) index 8 s word (Extract.Paired.pads T index 8)) at hs
  rw [hf,hp] at hs
  exact QueriesSat.bind hs (QueriesSat.pure' _)

 include hidx in
theorem sat_buildForest (selected : SharedForest.ForestSelection) (words : SharedForest.ForestWords) :
    QueriesSat T (HonestQuery T) (SharedForest.buildForest index selected words) := by
  have hfour:List.finRange 4=[0,1,2,3] := by decide
  have h0 : Extract.Paired.pairPrev T index 0 = ftsStart := by unfold Extract.Paired.pairPrev;rfl
  have hstep : ∀ n, Extract.Paired.pairPrev T index (n+1) =
      SharedForest.expectedPairRoot T index n (Extract.Paired.pairPrev T index n) := by
    intro n
    conv_lhs => unfold Extract.Paired.pairPrev
  unfold SharedForest.buildForest
  rw [hfour]
  simp only [List.foldlM_cons,List.foldlM_nil,bind_assoc,pure_bind]
  have h := sat_buildPair T index hidx 0 (selected.pairs 0) (words.first 0) (words.second 0)
  change QueriesSat T (HonestQuery T)
    (SharedForest.buildPair index 0 (selected.pairs 0) (words.first 0) (words.second 0)
      (Extract.Paired.pairPrev T index 0)) at h
  rw [h0] at h
  refine QueriesSat.bind h ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←h0,←hstep 0]
  refine QueriesSat.bind (sat_buildPair T index hidx 1 _ _ _) ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←hstep 1]
  refine QueriesSat.bind (sat_buildPair T index hidx 2 _ _ _) ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←hstep 2]
  refine QueriesSat.bind (sat_buildPair T index hidx 3 _ _ _) ?_
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure,SharedForest.buildPair_result]
  try simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  rw [←hstep 3]
  exact QueriesSat.bind (sat_buildSingleton T index hidx selected.singleton words.singleton) (QueriesSat.pure' _)

#print axioms sat_buildForest
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural

namespace ClaudeWCT.W9.T3.Security.Wots.PairedStructural
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sat_signFromOutput (T : Answers) (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine QueriesSat.bind (sat_buildForest T (digestIndex output) (digestIndex_lt output)
    (forestSelectionFromOutput output) (forestWordsFromOutput output)) ?_
  refine QueriesSat.bind (sat_prepareRoots T (digestIndex output) (digestIndex_lt output)) ?_
  refine QueriesSat.bind (sat_searchPreparedLayers T cache _ _ _) ?_
  generalize evalWithAnswerFn T (searchPreparedLayers cache _ _ _) = found
  rcases found with _ | result <;> exact QueriesSat.pure' _

theorem sat_signPayload (T : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine QueriesSat.bind (sat_privateNonce T message) ?_
  refine QueriesSat.bind (sat_sharedDigestSearch T _ _ _ _) ?_
  generalize evalWithAnswerFn T (sharedDigestSearch (evalWithAnswerFn T (privateNonce message))
    message 0 digestAttemptLimit) = found
  rcases found with _ | ⟨counter,output⟩
  · exact QueriesSat.pure' _
  · refine QueriesSat.bind (sat_signFromOutput T cache _ counter output) ?_
    generalize evalWithAnswerFn T (signFromOutput cache _ counter output) = result
    rcases result with _ | w <;> exact QueriesSat.pure' _

theorem sat_authenticatedSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    QueriesSat T (HonestQuery T) (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine QueriesSat.bind (sat_privateMac T _) ?_
  split
  · exact sat_signPayload T _ _
  · exact QueriesSat.pure' _

#print axioms sat_signFromOutput
#print axioms sat_signPayload
#print axioms sat_authenticatedSign
end ClaudeWCT.W9.T3.Security.Wots.PairedStructural
