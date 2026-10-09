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
