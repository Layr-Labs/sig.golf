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
    (h : ∀ p : Extract.Pos, p.Bounded →
      Extract.canonicalHeader (Extract.hdrBlock x) ≠ bytesLE 16 p.hdr) : Extract.posOf x = none := by
  unfold Extract.posOf
  rw [dif_neg]
  rintro ⟨p, hb, he⟩
  exact h p hb he
theorem nodeTweak_ne_header_tag (lay tree heap : Nat) {t : Nat} (h2 : t % 256 ≠ 2) (h3 : t % 256 ≠ 3)
    (h6 : t % 256 ≠ 6) (l tr pos ix : Nat) : nodeTweak 3 lay tree heap ≠ header t l tr pos ix := by
  rcases Nat.lt_or_ge lay 13 with h13 | h13
  · rcases Nat.lt_or_ge lay 4 with h4 | h4
    · by_cases h0 : lay = 0
      · subst h0; exact nodeTweak_top_ne_header _ _ _ _ _ _ _
      · exact nodeTweak_lower_ne_header h0 h4 _ _ h2 _ _ _ _
    · exact nodeTweak_fts_ne_header h4 h13 _ _ h6 _ _ _ _
  · rw [nodeTweak_other (by omega)]
    exact Mask.header_ne_of_tag (by omega)
theorem header_ne_hdr {t : Nat} (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 5 ∧ t % 256 ≠ 6 ∧
    t % 256 ≠ 11 ∧ t % 256 ≠ 15) (l tr pos ix : Nat) (p : Extract.Pos) : header t l tr pos ix ≠ p.hdr := by
  obtain ⟨h1, h2, h3, h5, h6, h11, h15⟩ := ht
  cases p with
  | chain lay tree leaf i step => exact (chainHeader_ne_header lay tree leaf i step t l tr pos ix).symm
  | wctChain index coord child c step =>
      exact (WCT9.ftsChainHeaderP_ne_header _ _ _ _ _ _ t l tr pos ix).symm
  | leaf lay tree lf => exact (leafTweak_ne_header _ _ _ h2 _ _ _ _).symm
  | node lay tree level nd => exact (nodeTweak_ne_header_tag _ _ _ h2 h3 h6 _ _ _ _).symm
  | wctNode index coord level nd =>
      simp only [Extract.Pos.hdr, WCT9.wctNodeHeader]; exact (nodeTweak_ne_header_tag _ _ _ h2 h3 h6 _ _ _ _).symm
  | wctLeaf index coord child =>
      simp only [Extract.Pos.hdr]; exact (WCT9.ftsLeafHeader_ne_header _ _ _ _ _ _ _ _ (by omega)).symm
  | forest index => simp only [Extract.Pos.hdr]; exact Mask.header_ne_of_tag (by omega)
theorem posOf_row_none {x : HashInput} {lay : Layer} {tree leaf : Nat}
    (hx : Extract.hdrBlock x = bytesLE 16 (rowTweak lay tree leaf)) : Extract.posOf x = none := by
  apply posOf_eq_none
  intro p hb he
  rw [hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _
    (by have := rowTweak_marker lay tree leaf; unfold tweakMarker at this; omega)] at he
  exact Extract.rowTweak_ne_hdr lay tree leaf hb (bytesLE_injective he)
theorem posOf_prefixed_none {t : Nat} (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 5 ∧
    t % 256 ≠ 6 ∧ t % 256 ≠ 11 ∧ t % 256 ≠ 15) (x : Digest) (rest : HashInput) (l tr pos ix : Nat) :
    Extract.posOf (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr pos ix) ++ rest)) = none := by
  apply posOf_eq_none
  intro p _ he
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix,
    SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _ (by rw [header_firstByte]; decide)] at he
  exact header_ne_hdr ht l tr pos ix p (bytesLE_injective he)
theorem posOf_encoding (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : BitVec 32) :
    Extract.posOf (pad64 (encodingInput lay tree leaf message counter)) = none := by
  apply posOf_row_none (lay := lay) (tree := tree) (leaf := leaf)
  rw [Extract.hdrBlock_pad64 _ (by simp [encodingInput, bytesLE_length])]
  exact Extract.hdrBlock_prefix _ _ _
theorem posOf_hdr_none {x : HashInput} {t : Nat} (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 5 ∧
    t % 256 ≠ 6 ∧ t % 256 ≠ 11 ∧ t % 256 ≠ 15) {l tr pos ix : Nat}
    (hx : Extract.hdrBlock x = bytesLE 16 (header t l tr pos ix)) : Extract.posOf x = none := by
  apply posOf_eq_none
  intro p _ he
  rw [hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _ (by rw [header_firstByte]; decide)] at he
  exact header_ne_hdr ht l tr pos ix p (bytesLE_injective he)
theorem posOf_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.posOf (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) = none :=
  posOf_row_none (BC.hdrBlock_layerEncodingInput lay tree leaf msg counter)
theorem posOf_layerEncodingP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) :
    Extract.posOf (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR)) = none :=
  posOf_row_none (BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad padR)
theorem posOf_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Extract.posOf (pad64 (digestInput rho message counter)) = none := by
  unfold digestInput
  apply posOf_eq_none
  intro p _ he
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
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
  | node lay tree level nd => exact digestHeader_ne_nodeTweak _ _ _ _ _ hh
  | wctLeaf index coord child => exact (WCT9.ftsLeafHeader_ne_digestHeader _ _ _ _).symm hh
  | forest index => simp only [Extract.Pos.hdr] at hh; exact digestHeader_ne_header _ _ _ _ _ _ hh
theorem sat_counterSearch (T : Answers) (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (counterSearch lay tree leaf message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [SigGolfCandidate.T3.counterSearch]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_encoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _
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
theorem sat_digest (T : Answers) (rho : Digest) (message : Message) (counter : BitVec 32) :
    QueriesSat T (HonestQuery T) (digest rho message counter) :=
  sat_publicHash _ (Or.inl (posOf_digest _ _ _))
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
private theorem chain_low_ne_header (lay : Layer) (tree leaf i step tag roleLay roleTree pos ix : Nat) :
    (chainHeader lay tree leaf i step).extractLsb' 0 64 ≠
      (header tag roleLay roleTree pos ix).extractLsb' 0 64 :=
  low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
    (by rw [header_firstByte]; decide)
theorem posOf_chain_offgraph (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (hoff : chainHeaderSpill tree leaf i step ≠ 0) :
    Extract.posOf (pad64 (chainInput lay tree leaf i step value)) = none := by
  apply posOf_eq_none
  intro p hb he
  rw [chainInput_padded, Extract.hdrBlock, chainInput_header] at he
  have hn := congrArg (List.take 8) he
  rw [canonicalHeader_low] at hn
  have hp : (bytesLE 16 p.hdr).take 8 = bytesLE 8 (p.hdr.extractLsb' 0 64) := by
    rw [← Extract.Pos.canonicalHeader_eq hb]
    exact canonicalHeader_low _
  rw [hp] at hn
  have hlo := bytesLE_injective hn
  cases p with
  | chain lay' tree' leaf' i' step' =>
      exact chainHeader_offgraph_low_ne hoff hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hlo
  | wctChain index coord child c step' =>
      exact WCT9.ftsChainHeaderP_low_ne_chainHeader _ _ _ _ _ _ _ _ _ _ _ hlo.symm
  | _ =>
      exact low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
        (Extract.Pos.hdr_marker_lt hb (by simp only [Extract.Pos.cls]; (try split) <;> omega)) hlo
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 256) :
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
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 8 := by
          unfold chainHeaderSpill at hoff
          omega
        exact honestQuery_honest T (.chain lay tree leaf i (start + count)) hg
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)
theorem sat_leafHalf (T : Answers) (lay : Layer) (hl : lay = 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (signatureOnly : Bool) (pair : Nat) (rows : List Digest × List Digest)
    (half : Nat) (hh : half < 2) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (Correctness.leafHalf lay tree leaf digits signatureOnly pair
      (evalWithAnswerFn T (privatePair 0 lay.val tree pair leaf)) rows half) := by
  subst hl
  unfold Correctness.leafHalf
  by_cases hi : chainCount (0 : Layer) ≤ 2 * pair + half
  · simp only [hi, ite_true]
    exact QueriesSat.pure' _
  · simp only [hi, ite_false]
    rw [← Correctness.leafSeed_pair T 0 tree leaf pair half hh, ← WCT9.wotsSeed_top]
    have hd := hvalid (2 * pair + half) (by omega)
    have hw := Mask.width_le (0 : Layer) (2 * pair + half)
    have hc := Mask.chainCount_le (0 : Layer)
    refine QueriesSat.bind ?_ ?_
    · rw [← honestChainValue_zero T (0 : Layer) tree leaf (2 * pair + half) (WCT9.wotsSeed T (0 : Layer) tree leaf (2 * pair + half))]
      exact sat_chain T (0 : Layer) tree leaf _ 0 _ htree hleaf (by omega) (by omega)
    · change QueriesSat T (HonestQuery T) (if signatureOnly = true then _ else
        (SigGolfCandidate.T3.chain (0 : Layer) tree leaf (2 * pair + half) (digits.getD (2 * pair + half) 0)
          (maxDigit (0 : Layer) (2 * pair + half) - digits.getD (2 * pair + half) 0)
          (honestChainValue T (0 : Layer) tree leaf (2 * pair + half) (WCT9.wotsSeed T (0 : Layer) tree leaf (2 * pair + half))
            (digits.getD (2 * pair + half) 0)) >>= _))
      split
      · exact QueriesSat.pure' _
      · exact QueriesSat.bind (sat_chain T (0 : Layer) tree leaf _ _ _ htree hleaf (by omega) (by omega))
          (QueriesSat.pure' _)
theorem sat_leafRows (T : Answers) (lay : Layer) (hl : lay = 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (signatureOnly : Bool) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (Correctness.leafRows lay tree leaf digits signatureOnly) := by
  unfold Correctness.leafRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun pair _ rows _ => ⟨?_, trivial⟩)
  refine QueriesSat.bind (sat_privatePair T _ _ _ _ _) ?_
  exact QueriesSat.foldlM_range 2 _ (fun _ _ => True) rows trivial (fun half hh rows' _ =>
    ⟨sat_leafHalf T lay hl tree leaf digits hvalid signatureOnly pair rows' half hh htree hleaf, trivial⟩)
theorem sat_buildLeaf (T : Answers) (lay : Layer) (hl : lay = 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (signatureOnly : Bool) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32)
    (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.buildLeaf lay tree leaf digits signatureOnly) := by
  rw [Correctness.buildLeaf_eq]
  refine QueriesSat.bind (sat_leafRows T lay hl tree leaf digits hvalid signatureOnly htree hleaf) ?_
  subst hl
  cases signatureOnly
  · have hr := Correctness.eval_leafRows_correct T (0 : Layer) tree leaf digits hvalid false
    have hn : chainCount (0 : Layer) ≤ 2 * ((chainCount (0 : Layer) + 1) / 2) := by omega
    simp only [Correctness.LeafRows, Bool.false_eq_true, ite_false, min_eq_right hn] at hr
    have he := Correctness.list_eq_range_map _ (leafEnd T 0 tree leaf) _ hr.1
      (fun i hi => hr.2.2.1 i (by rw [hr.1]; exact hi))
    simp only [Bool.false_eq_true, ite_false]
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    rw [he, ← WCT9.wotsEnd_top, Extract.leafHash_eq_shortHash]
    exact sat_shortHash _ (honestQuery_honest T (.leaf (0 : Layer) tree leaf) hb)
  · simp only [ite_true]
    exact QueriesSat.pure' _
theorem sat_treeRows (T : Answers) (lay : Layer) (hl : lay = 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (Correctness.treeRows lay tree selected digits) := by
  unfold Correctness.treeRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun leaf hleaf rows _ => ⟨?_, trivial⟩)
  have hd : Cost.ValidDigits lay (if leaf = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  have hl' : leaf < 2 ^ 32 := by
    have : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  refine QueriesSat.bind (sat_buildLeaf T lay hl tree leaf _ hd false htree hl'
    (Extract.leaf_bounded_of_treeBits ht hleaf)) ?_
  generalize evalWithAnswerFn T (SigGolfCandidate.T3.buildLeaf lay tree leaf (if leaf = selected then digits else []) false) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.pure' _
theorem honestQuery_treeNode (T : Answers) (lay : Layer) (tree : Nat) (ht : tree < 2 ^ Extract.treeBits lay)
    (level node : Nat) (hlevel : level < height lay) (hroot : lay = 0 ∨ level + 1 < height lay)
    (hnode : node < ((WCT9.wotsTree T lay tree).getD level []).length / 2) :
    HonestQuery T (nodeQuery 3 lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (WCT9.wotsTree T lay tree) level (2 * node)) (treeValue (WCT9.wotsTree T lay tree) level (2 * node + 1))) := by
  have hshape := (WCT9.wotsTree_correct T lay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h31 := lt_of_le_of_lt (Nat.le_add_right _ _) (Extract.routed_lt_of_treeBits ht (Nat.one_le_two_pow))
  have hle : tree ≤ tree * 2 ^ height lay := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
  refine Or.inr ⟨.node lay tree level node, ⟨by omega, hlevel, hroot, Extract.tree_zero_of_treeBits ht,
    by rw [hw, hpow] at hnode; omega⟩, ?_⟩
  show pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - (level + 1)) + node) _ 0 _) =
    pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - level - 1) + node) _ 0 _)
  rw [Nat.sub_sub]
theorem sat_buildTree (T : Answers) (lay : Layer) (hl : lay = 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.buildTree lay tree selected digits) := by
  rw [Correctness.buildTree_eq]
  refine QueriesSat.bind (sat_treeRows T lay hl tree selected digits hvalid htree ht) ?_
  rw [Correctness.eval_treeRows T lay tree selected digits hvalid]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  apply sat_buildLevels
  intro level hlevel node hnode
  subst hl
  have h := honestQuery_treeNode T 0 tree ht level node hlevel (Or.inl rfl)
  rw [WCT9.wotsTree_top] at h
  exact h hnode
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
  rw [← honestChainValue_zero T lay tree leaf i (WCT9.wotsSeed T lay tree leaf i)]
  refine QueriesSat.bind (sat_chain T lay tree leaf _ 0 _ htree hleaf (by omega) (by omega)) ?_
  rw [eval_honestChain, Nat.zero_add]
  exact QueriesSat.bind (sat_chain T lay tree leaf _ _ _ htree hleaf (by omega) (by omega)) (QueriesSat.pure' _)
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
  rw [Extract.leafHash_eq_shortHash]
  exact sat_shortHash _ (honestQuery_honest T (.leaf lay tree leaf) hb)
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
theorem sat_buildLevelsBelow {T : Answers} {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (tag lay tree h : Nat)
    (leaves : List Digest)
    (hq : ∀ level, level + 1 < h → ∀ node,
      node < ((evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)).getD level []).length / 2 →
      Q (nodeQuery tag lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)) level (2 * node))
        (treeValue (evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)) level (2 * node + 1)))) :
    QueriesSat T Q (WCT9.buildLevelsBelow tag lay tree h leaves) := by
  have he : WCT9.buildLevelsBelow tag lay tree h leaves = levelsFold tag lay tree h leaves (h - 1) := rfl
  rw [he] at hq ⊢
  unfold levelsFold
  refine QueriesSat.foldlM_range' 1 (h - 1) _
    (fun i state => state = evalWithAnswerFn T (levelsFold tag lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold levelsStep
    refine QueriesSat.bind (sat_buildLevel _ _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := levelsFold_length T tag lay tree h leaves i
    obtain ⟨extra, hext⟩ := levelsFold_prefix T tag lay tree h leaves i (h - 1) (by omega)
    have hget : (evalWithAnswerFn T (levelsFold tag lay tree h leaves (h - 1))).getD i [] =
        (evalWithAnswerFn T (levelsFold tag lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i (by omega) node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [levelsFold_succ, evalWithAnswerFn_bind]
theorem below_getD (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (level : Nat) (hl : level + 1 < h) :
    (evalWithAnswerFn T (WCT9.buildLevelsBelow tag lay tree h leaves)).getD level [] =
      (evalWithAnswerFn T (SigGolfCandidate.T3.buildLevels tag lay tree h leaves)).getD level [] := by
  have he : WCT9.buildLevelsBelow tag lay tree h leaves = levelsFold tag lay tree h leaves (h - 1) := rfl
  rw [he, buildLevels_eq_fold]
  obtain ⟨extra, hext⟩ := levelsFold_prefix T tag lay tree h leaves (h - 1) h (by omega)
  have hlen := levelsFold_length T tag lay tree h leaves (h - 1)
  rw [hext, List.getD_append _ _ _ _ (by omega)]
theorem sat_buildTreeP (T : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) (ht : tree < 2 ^ Extract.treeBits lay) :
    QueriesSat T (HonestQuery T) (WCT9.buildTreeP lay tree selected digits) := by
  rw [WCT9.buildTreeP_factor]
  refine QueriesSat.bind (sat_treeRowsP T hlay tree selected digits hvalid htree ht) ?_
  obtain ⟨hlen, hroot, -, -⟩ := WCT9.eval_treeRowsP T hlay tree selected digits hvalid
  have hroots := Correctness.list_eq_range_map _ _ _ hlen hroot
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [hroots]
  apply sat_buildLevelsBelow
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay) ((List.range (2 ^ height lay)).map (WCT9.wotsRoot T lay tree))
    level hlevel
  rw [hg] at hnode
  have := honestQuery_treeNode T lay tree ht level node (by omega) (Or.inr hlevel) hnode
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
theorem sat_buildChildF (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (coord : ClaudeWCT.WCT9.Coord)
    (child : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.buildChildF index coord.val child.val word
      (List.ofFn (WCT9.ftsCoef T index coord.val))) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_buildChildF T index coord child word).mono fun _ hq =>
    honestQuery_of_fts T hindex hq
theorem sat_buildCoordinateF (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (coord : ClaudeWCT.WCT9.Coord)
    (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.buildCoordinateF index coord selected word) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_buildCoordinateF T index coord selected word).mono fun _ hq =>
    honestQuery_of_fts T hindex hq
theorem sat_forestRows (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.forestRows index output) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_forestRows T index output).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_forestPk (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) :
    QueriesSat T (HonestQuery T)
      (ClaudeWCT.WCT9.forestPk index (List.ofFn (ClaudeWCT.WCT9.coordinatePair T index))) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_forestPk T index).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_signForest (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.signForest index output) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_signForest T index output).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_keygenPayload (T : Answers) : QueriesSat T (HonestQuery T) keygenPayload := by
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine QueriesSat.bind (sat_buildTree T 0 rfl 0 0 [] (Cost.validDigits_nil 0) (by decide) (by decide)) ?_
  generalize evalWithAnswerFn T (SigGolfCandidate.T3.buildTree 0 0 0 []) = x
  obtain ⟨levels, values⟩ := x
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
  refine QueriesSat.bind (sat_buildLeaf T 0 rfl 0 leaf digits hvalid true (by decide) (by omega)
    (Extract.leaf_bounded_of_treeBits (by decide) (by simpa [height] using hleaf))) ?_
  generalize evalWithAnswerFn T (SigGolfCandidate.T3.buildLeaf 0 0 leaf digits true) = x
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
