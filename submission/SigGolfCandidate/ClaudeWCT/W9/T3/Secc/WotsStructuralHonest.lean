import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest

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
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ ∃ p : Extract.Pos, p.Bounded ∧ x = Extract.honestInput T p
  | _ => True
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    HonestQuery T (.inl (.inr (Extract.honestInput T p))) := Or.inr ⟨p, hp, rfl⟩
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
  rw [Extract.hdrKey_of_len64 hlen, hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _ hm] at he
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
  rw [Extract.hdrKey_of_len64 hlen,
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
    Extract.posOf (pad64 (chainInput lay tree leaf i step value)) = none := by
  apply posOf_eq_none
  intro p hb _ he
  have hlen : (pad64 (chainInput lay tree leaf i step value)).length = 64 := by
    rw [chainInput_padded]; simp [chainInput, zero16, bytesLE_length]
  rw [Extract.hdrKey_of_len64 hlen, chainInput_padded, Extract.hdrBlock, chainInput_header] at he
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
      · exact low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
          (Extract.Pos.hdr_marker_lt hb (by simp [Extract.Pos.cls, h0])) hlo
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
        (Extract.Pos.hdr_marker_lt hb (by simp only [Extract.Pos.cls]; (try split) <;> omega)) hlo
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 7) :
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
        exact honestQuery_honest T (.chain lay tree leaf i (start + count)) hg
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)
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
        refine Or.inr ⟨.chain lay tree leaf i (start + count), hg, ?_⟩
        show pad64 (chainInput lay tree leaf i (start + count)
            (honestChainValueW T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count))) =
          pad64 (chainInput lay tree leaf i (start + count)
            (honestChainValue T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i) (start + count)))
        rw [honestChainValueW_eq (Or.inr (Or.inr (by omega)))]
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)
/-! ### Top leaves (campaign T8D: family seeds through `topCoefs`, `buildLeafTop`, `buildTopTree`) -/
theorem sat_topCoefs (T : Answers) (leaf : Nat) : QueriesSat T (HonestQuery T) (topCoefs leaf) := by
  unfold topCoefs
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j _ acc _ => ⟨?_, trivial⟩)
  unfold topSeedPair
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_buildLeafTop (T : Answers) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (signatureOnly : Bool) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf 0 0 leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafTop leaf digits signatureOnly) := by
  rw [Correctness.buildLeafTop_eq]
  refine QueriesSat.bind (sat_topCoefs T leaf) ?_
  rw [Correctness.eval_topCoefs]
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun i hi rows _ => ⟨?_, trivial⟩)) ?_
  · unfold Correctness.topLeafStep
    have hseed : topSeed (Correctness.topCoefList T leaf) i = WCT9.wotsSeed T 0 0 leaf i := by
      rw [WCT9.wotsSeed_top, Correctness.leafSeed_top]; rfl
    rw [hseed]
    have hd := hvalid i hi
    have hw := Mask.width_le (0 : Layer) i
    have hc := Mask.chainCount_le (0 : Layer)
    rw [← honestChainValue_zero T (0 : Layer) 0 leaf i (WCT9.wotsSeed T 0 0 leaf i)]
    refine QueriesSat.bind (sat_chain T (0 : Layer) 0 leaf _ 0 _ (by decide) hleaf (by omega) (by omega)) ?_
    rw [eval_honestChain, Nat.zero_add]
    split
    · exact QueriesSat.pure' _
    · exact QueriesSat.bind (sat_chain T (0 : Layer) 0 leaf _ _ _ (by decide) hleaf (by omega) (by omega))
        (QueriesSat.pure' _)
  · cases signatureOnly
    · have hr := Correctness.eval_topLeafRows T leaf digits hvalid false
      simp only [Correctness.LeafRows, Bool.false_eq_true, ite_false, min_self] at hr
      have he := Correctness.list_eq_range_map _ (leafEnd T 0 0 leaf) _ hr.1
        (fun i hi => hr.2.2.1 i (by rw [hr.1]; exact hi))
      simp only [Bool.false_eq_true, ite_false]
      refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [he, ← WCT9.wotsEnd_top, Extract.leafHash_eq_shortHash]
      exact sat_shortHash _ (honestQuery_honest T (.leaf (0 : Layer) 0 leaf) hb)
    · simp only [ite_true]
      exact QueriesSat.pure' _
theorem honestQuery_treeNode (T : Answers) (lay : Layer) (tree : Nat) (ht : tree < 2 ^ Extract.treeBits lay)
    (level node : Nat) (hlevel : level < height lay) (hlay0 : lay = 0)
    (hnode : node < ((WCT9.wotsTree T lay tree).getD level []).length / 2) :
    HonestQuery T (nodeQuery 3 lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (WCT9.wotsTree T lay tree) level (2 * node)) (treeValue (WCT9.wotsTree T lay tree) level (2 * node + 1))) := by
  have hshape := (WCT9.wotsTree_correct T lay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h31 := lt_of_le_of_lt (Nat.le_add_right _ _) (Extract.routed_lt_of_treeBits ht (Nat.one_le_two_pow))
  have hle : tree ≤ tree * 2 ^ height lay := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
  have hroot : lay = 0 ∨ level + 1 < height lay := Or.inl hlay0
  have h0 : lay.val = 0 := by rw [hlay0]; rfl
  refine Or.inr ⟨.node lay tree level node, ⟨by omega, hlevel, hroot, Extract.tree_zero_of_treeBits ht,
    by rw [hw, hpow] at hnode; omega⟩, ?_⟩
  show pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - (level + 1)) + node) _ 0 _) =
    pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - level - 1) + node) _ _)
  rw [h0, Extract.merkleNodeInput_top, Nat.sub_sub]
theorem eval_topRoots (T : Answers) :
    evalWithAnswerFn T ((List.range (2 ^ height 0)).foldlM (fun (roots : List Digest) leaf => do
      let (root, _) ← buildLeafTop leaf []
      pure (roots ++ [root])) []) = (List.range (2 ^ height 0)).map (WCT9.wotsRoot T 0 0) := by
  rw [WCT9.wotsRoot_top]
  exact Correctness.eval_foldlM_range_inv T (2 ^ height 0)
    (fun (roots : List Digest) leaf => do
      let (root, _) ← buildLeafTop leaf []
      pure (roots ++ [root]))
    (fun done roots => roots = (List.range done).map (Correctness.leafRoot T 0 0)) [] rfl
    (fun leaf _ roots hroots => by
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      rw [Correctness.eval_buildLeafTop_root T leaf [] (Cost.validDigits_nil 0), hroots, List.range_succ,
        List.map_append, List.map_singleton])
theorem sat_buildTopTree (T : Answers) : QueriesSat T (HonestQuery T) buildTopTree := by
  unfold buildTopTree
  refine QueriesSat.bind (QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial
    (fun leaf hleaf roots _ => ⟨?_, trivial⟩)) ?_
  · have hl' : leaf < 2 ^ 32 := by
      have : 2 ^ height (0 : Layer) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le 0)
      omega
    refine QueriesSat.bind (sat_buildLeafTop T leaf [] (Cost.validDigits_nil 0) false hl'
      (Extract.leaf_bounded_of_treeBits (by decide) hleaf)) ?_
    generalize evalWithAnswerFn T (buildLeafTop leaf [] false) = x
    obtain ⟨root, values⟩ := x
    exact QueriesSat.pure' _
  · rw [eval_topRoots]
    apply sat_buildLevels
    intro level hlevel node hnode
    exact honestQuery_treeNode T 0 0 (by decide) level node hlevel rfl hnode
theorem sat_packedSecret (T : Answers) (lay : Layer) (tree q : Nat) (carry : Digest) :
    QueriesSat T (HonestQuery T) (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) q carry) := by
  unfold WCT9.packedSecret
  split
  · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    unfold WCT9.lowerSeedPair
    exact sat_privatePair T _ _ _ _ _
  · exact QueriesSat.pure' _
theorem sat_lowerCoefs (T : Answers) (lay : Layer) (tree leaf : Nat) (carry : Digest) :
    QueriesSat T (HonestQuery T) (WCT9.lowerCoefs lay tree leaf carry) := by
  unfold WCT9.lowerCoefs
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun j _ rows _ => ⟨?_, trivial⟩)
  refine QueriesSat.bind (sat_packedSecret T lay tree _ _) ?_
  generalize evalWithAnswerFn T (WCT9.packedSecret (WCT9.lowerSeedPair lay tree) (WCT9.lowerCoefOrdinal leaf j)
    rows.2) = sc
  rcases sc with ⟨coef, c⟩
  exact QueriesSat.pure' _
theorem sat_leafRowsF (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (WCT9.leafRowsF lay tree leaf digits (List.ofFn (WCT9.lowerCoef T lay tree leaf))) := by
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
    (hvalid : Cost.ValidDigits lay digits) (carry : Digest)
    (hcarry : WCT9.CarryOk T (WCT9.lowerSeedPair lay tree) (WCT9.lowerCoefOrdinal leaf 0) carry)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (WCT9.buildLeafPF lay tree leaf digits carry) := by
  rw [WCT9.buildLeafPF_factor]
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [WCT9.eval_lowerCoefs T lay tree leaf carry hcarry]
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
    (level node : Nat) (hlevel : level < height lay) (hroot : lay = 0 ∨ level + 1 < height lay)
    (hnode : node < ((WCT9.wotsTree T lay tree).getD level []).length / 2) :
    HonestQuery T (merkleQuery lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (WCT9.wotsTree T lay tree) level (2 * node)) (treeValue (WCT9.wotsTree T lay tree) level (2 * node + 1))) := by
  have hshape := (WCT9.wotsTree_correct T lay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine Or.inr ⟨.node lay tree level node, ⟨by
    have h31 := lt_of_le_of_lt (Nat.le_add_right _ _) (Extract.routed_lt_of_treeBits ht (Nat.one_le_two_pow))
    have hle : tree ≤ tree * 2 ^ height lay := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
    omega, hlevel, hroot, Extract.tree_zero_of_treeBits ht, by rw [hw, hpow] at hnode; omega⟩, ?_⟩
  show pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - (level + 1)) + node) _ _) =
    pad64 (WCT9.merkleNodeInput lay.val tree (2 ^ (height lay - level - 1) + node) _ _)
  rw [Nat.sub_sub]
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
  have := honestQuery_lowerNode T lay tree ht level node (by omega) (Or.inr (by omega)) hnode
  simp only [treeValue, hg]
  exact this
theorem honestQuery_of_fts (T : Answers) {index : Nat} (hindex : index < 2 ^ 31) {q : SigGolfCandidate.T3.Spec.Domain}
    (h : ClaudeWCT.WCT9.Wots.FtsHonestQuery T index q) : HonestQuery T q := by
  rcases q with (coin | x) | (tweak | other)
  · exact h.elim
  · obtain ⟨pos, hb, hx⟩ := Extract.ftsHonestQuery_pos hindex h
    exact Or.inr ⟨pos, hb, hx⟩
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
      cases hs : evalWithAnswerFn T (WCT9.layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 (WCT9.searchLimit (Fin.ofNat 4 n))) with
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
          have hd := (WCT9.layerCounterSearch_some T _ _ _ msg (WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
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
