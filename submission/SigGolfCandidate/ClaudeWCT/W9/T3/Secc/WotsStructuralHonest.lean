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
theorem posOf_row_none {x : HashInput} {lay : Layer} {tree leaf : Nat}
    (hx : Extract.hdrBlock x = bytesLE 16 (rowTweak lay tree leaf)) : Extract.posOf x = none := by
  apply posOf_eq_none
  intro p hb he
  rw [hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _
    (by have := rowTweak_marker lay tree leaf; unfold tweakMarker at this; omega)] at he
  exact Extract.rowTweak_ne_hdr lay tree leaf hb (bytesLE_injective he)
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
  | wctNode index coord level nd =>
      exact WCT9.wctNodeHeader_low_ne_chainHeader hb.2.1 _ _ _ _ _ _ _ hlo.symm
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
    exact honestQuery_treeNode T 0 0 (by decide) level node hlevel (Or.inl rfl) hnode
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
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ ∃ p : Extract.Pos, Extract.Paired.Bounded p ∧ x = Extract.Paired.honestInput T p
  | _ => True
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : Extract.Paired.Bounded p) :
    HonestQuery T (.inl (.inr (Extract.Paired.honestInput T p))) := Or.inr ⟨p, hp, rfl⟩
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
theorem posOf_row_none {x : HashInput} {lay : Layer} {tree leaf : Nat}
    (hx : Extract.hdrBlock x = bytesLE 16 (rowTweak lay tree leaf)) : Extract.posOf x = none := by
  apply posOf_eq_none
  intro p hb he
  rw [hx, SigGolfCandidate.T3M.Extract.canonicalHeader_marker_ne _
    (by have := rowTweak_marker lay tree leaf; unfold tweakMarker at this; omega)] at he
  exact Extract.rowTweak_ne_hdr lay tree leaf hb (bytesLE_injective he)
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
  | wctNode index coord level nd =>
      exact WCT9.wctNodeHeader_low_ne_chainHeader hb.2.1 _ _ _ _ _ _ _ hlo.symm
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
    exact honestQuery_treeNode T 0 0 (by decide) level node hlevel (Or.inl rfl) hnode
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

theorem queried_chainPrefixes (T : Answers) (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    queried T (chainPrefixes lay tree leaf i start count value) =
      queried T (SigGolfCandidate.T3.chain lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
      rw [lower_chain_succ_first]
      simp only [chainPrefixes,queried_bind,queried_pure,List.append_nil,ih]

theorem sat_chainPrefixes (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2^40) (hleaf : leaf < 2^32) (hi : i < 2^24) (hcount : start+count≤256) :
    QueriesSat T (HonestQuery T) (chainPrefixes lay tree leaf i start count
      (honestChainValue T lay tree leaf i (wotsSeed T lay tree leaf i) start)) := by
  intro q hq
  change q ∈ queried T (chainPrefixes lay tree leaf i start count
    (honestChainValue T lay tree leaf i (wotsSeed T lay tree leaf i) start)) at hq
  rw [queried_chainPrefixes] at hq
  exact sat_chain T lay tree leaf i start count htree hleaf hi hcount q hq

theorem sat_buildLeafPrefixes (T : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : Digest)
    (hcarry : CarryOk T (lowerSeedPair lay tree) (lowerCoefOrdinal leaf 0) carry)
    (htree : tree < 2^40) (hleaf : leaf < 2^32) (hb : (Extract.Pos.leaf lay tree leaf).Bounded) :
    QueriesSat T (HonestQuery T) (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine QueriesSat.bind (sat_lowerCoefs T lay tree leaf carry) ?_
  rw [eval_lowerCoefs T lay tree leaf carry hcarry]
  dsimp only
  refine QueriesSat.bind (QueriesSat.mapM _ _ (fun i hi => ?_)) ?_
  · rw [lowerFamilySeed_eq T hlay, ← honestChainValue_zero T lay tree leaf i (wotsSeed T lay tree leaf i)]
    exact sat_chainPrefixes T lay tree leaf i 0 (maxDigit lay i) htree hleaf
      (by have := Mask.chainCount_le lay; have := List.mem_range.mp hi; omega)
      (by have := Mask.width_le lay i; omega)
  · rw [Correctness.eval_mapM]
    simp only [lowerFamilySeed_eq T hlay]
    change QueriesSat T (HonestQuery T) (do
      let root ← SigGolfCandidate.T3.leafHash lay tree leaf
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
    rw [Extract.leafHash_eq_shortHash]
    exact sat_shortHash _ (honestQuery_honest T (.leaf lay tree leaf) hb)
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
      obtain ⟨counter,digits⟩ := found
      have hd := (canonical_search_valid_credit T 0 _ _ _ _ _ _ counter digits
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
  rw [hroots]
  apply sat_buildLevelsBelow
  intro level hlevel node hnode
  have hg := below_getD T 3 lay.val tree (height lay)
    ((List.range (2^height lay)).map (wotsRoot T lay tree)) level hlevel
  rw [hg] at hnode
  have hq := honestQuery_treeNode T lay tree ht level node (by omega) (Or.inr hlevel) hnode
  simpa only [treeValue,hg,wotsTree] using hq

theorem sat_prepareRoots (T : Answers) (index : Nat) (hi : index<2^31) :
    QueriesSat T (HonestQuery T) (prepareRoots index) := by
  unfold prepareRoots
  refine QueriesSat.bind (sat_buildTreePrefixes T (by decide : (1 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 1) (Extract.route_tree_treeBits index hi 1)) ?_
  refine QueriesSat.bind (sat_buildTreePrefixes T (by decide : (2 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 2) (Extract.route_tree_treeBits index hi 2)) ?_
  exact QueriesSat.bind (sat_buildTreePrefixes T (by decide : (3 : Layer)≠0) _ _
    (Mask.route_tree_lt index hi 3) (Extract.route_tree_treeBits index hi 3)) (QueriesSat.pure' _)
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
      refine Or.inr ⟨.wctChain index coord.val child.val t.val (start+count),
        ⟨hidx,coord.isLt,child.isLt,t.isLt,by omega⟩,?_⟩
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
      (buildChildF index coord.val child.val word (List.ofFn (ftsCoef T index coord.val))
        (Extract.Paired.pads T index coord.val (Extract.Paired.physical coord.val child.val/64)).1) := by
  rw [buildChildF_factor]
  refine QueriesSat.bind (sat_fts_childRows T index hidx coord child word) ?_
  rw [eval_childRows_ends T index coord.val child.val word]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  rw [ClaudeWCT.W9.T3M.WctExtract.leafHashP_eq_shortHash]
  apply SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash
  refine Or.inr ⟨.wctLeaf index coord.val child.val,⟨hidx,coord.isLt,child.isLt⟩,?_⟩
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
  refine Or.inr ⟨.wctNode index coord.val (Extract.heapLevel heap) (Extract.heapNode heap),
    ⟨⟨hidx,coord.isLt,hL,hN⟩,hused⟩,?_⟩
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
    rw [nodeHash_eq]
    exact SigGolfCandidate.T3.Security.Wots.Structural.sat_shortHash _ hq

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

 include hidx in
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
    have hl:nodes.getD (2*(127-done)) 0=(Extract.Paired.nodes T index coord.val).getD (2*(127-done)) 0 := hagree _ (by omega)
    have hr:nodes.getD (2*(127-done)+1) 0=(Extract.Paired.nodes T index coord.val).getD (2*(127-done)+1) 0 := hagree _ (by omega)
    refine ⟨?_,?_⟩
    · refine QueriesSat.bind ?_ (QueriesSat.pure' _)
      rw [hl,hr]
      exact sat_sharedNode T index hidx coord (127-done) (by omega) (by omega)
    · simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
      refine ⟨by rw [Array.size_set!,hsz],?_⟩
      intro j hj
      by_cases he:j=127-done
      · subst he
        rw [getD_set_self nodes _ _ (by omega),hl,hr]
        obtain ⟨ha,hb,hc⟩ := sharedHeap_arithmetic _ _ hcut.1 hd
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

end ClaudeWCT.W9.T3.Security.Wots.PairedStructural
