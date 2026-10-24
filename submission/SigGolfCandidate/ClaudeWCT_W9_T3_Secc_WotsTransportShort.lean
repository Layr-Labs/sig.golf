import SigGolfCandidate.ClaudeWCT_W9_New_Positions_FtsBridge
import SigGolfCandidate.ClaudeWCT_W9_New_BC_Respects

namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
/-! C2/C3 (FULL): the half-keeping hashes of the current scheme. -/
theorem halfHash_respects (high : Bool) (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    ShortRespects (WCT9.halfHash high input) := by
  intro A T hAT
  rw [eval_halfHash', eval_halfHash', hAT.public _ h]
theorem chainW_respects (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ShortRespects (WCT9.chainW lay tree leaf i start count value) := by
  unfold WCT9.chainW
  exact ShortRespects.foldlM _ _ (fun step _ v => halfHash_respects _ _
    (short_of_le _ (by rw [WCT9.chainInputW_length]; omega))) value
theorem lowerLeafHash_respects (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length ≤ 200) :
    ShortRespects (WCT9.lowerLeafHash lay tree leaf ends) := by
  rw [WCT9.lowerLeafHash_eq]
  unfold WCT9.lowerHash
  apply halfHash_respects
  apply short_of_le
  rw [leafInput_length]
  split_ifs <;> omega
theorem lowerNodeHash_respects (lay tree heap : Nat) (left right : Digest) :
    ShortRespects (WCT9.lowerNodeHash lay tree heap left right) := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  apply halfHash_respects
  apply short_of_le
  simp [WCT9.merkleNodeInput, zero16, bytesLE_length]
theorem lowerLevels_respects (lay tree h : Nat) (leaves : List Digest) :
    ShortRespects (WCT9.lowerLevels lay tree h leaves) := by
  unfold WCT9.lowerLevels
  exact ShortRespects.foldlM _ _ (fun level _ levels =>
    ShortRespects.bind (ShortRespects.mapM _ _ fun i _ => lowerNodeHash_respects _ _ _ _ _) fun _ =>
      ShortRespects.pure' _) _
/-! Top-nonce layer (r3-lean-nonsec): the img-v6 top tree (nonce-searched node levels) respects short agreement. -/
theorem topNodeHashN_respects (heap n : Nat) (left right : Digest) : ShortRespects (topNodeHashN heap n left right) := by
  unfold topNodeHashN
  exact ShortRespects.projHash _ _ (short_of_le _ (by simp [topNodeInput, nonceBytes, bytesLE_length]))
theorem topNonceSearch_respects (h heap : Nat) (left right : Digest) :
    ∀ fuel n, ShortRespects (topNonceSearch h heap left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact ShortRespects.bind (topNodeHashN_respects _ _ _ _) fun _ => ShortRespects.pure' _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine ShortRespects.bind (topNodeHashN_respects _ _ _ _) fun _ => ?_
      split
      · exact ShortRespects.pure' _
      · exact topNonceSearch_respects h heap left right fuel (n + 1)
theorem buildTopLevels_respects (leaves : List Digest) : ShortRespects (buildTopLevels leaves) := by
  unfold buildTopLevels
  refine ShortRespects.foldlM _ _ (fun level _ levels => ShortRespects.bind ?_ fun _ => ShortRespects.pure' _) _
  unfold buildTopLevel
  refine ShortRespects.mapM _ _ fun i _ => ?_
  split
  · rw [← WCT9.lowerNodeHash_top]
    exact lowerNodeHash_respects _ _ _ _ _
  · unfold topNodeAt
    exact ShortRespects.map _ (topNonceSearch_respects _ _ _ _ _ _)
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem honestChainValueW_short (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    honestChainValueW A lay tree leaf i seed step = honestChainValueW T lay tree leaf i seed step :=
  chainW_respects lay tree leaf i 0 step seed A T hAT
theorem honestTop_short (index : Nat) : Extract.honestTop A index = Extract.honestTop T index := by
  rw [Extract.honestTop_eq_wct9, Extract.honestTop_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestTop_congr (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq))
theorem wotsSeed_short (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsSeed A lay tree leaf i = WCT9.wotsSeed T lay tree leaf i := by
  rw [WCT9.wotsSeed_fam, WCT9.wotsSeed_fam]
  congr 2
  funext j
  unfold WCT9.famCoef WCT9.famCoefN WCT9.lowerSeedPair
  rw [ShortRespects.privatePair 0 lay.val tree _ 0 A T hAT]
theorem wotsEnd_short (lay : Layer) (tree leaf i : Nat) :
    WCT9.wotsEnd A lay tree leaf i = WCT9.wotsEnd T lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_short hAT]
  exact chainW_respects _ _ _ _ _ _ _ A T hAT
theorem wotsRoot_short (lay : Layer) (tree leaf : Nat) :
    WCT9.wotsRoot A lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i _ => wotsEnd_short hAT lay tree leaf i)]
  apply lowerLeafHash_respects
  · simp only [List.length_map, List.length_range]
    have := chainCount_le lay
    omega
  · exact hAT
theorem wotsTree_short (lay : Layer) (tree : Nat) :
    WCT9.wotsTree A lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf _ => wotsRoot_short hAT lay tree leaf)]
  split_ifs
  · exact buildTopLevels_respects _ A T hAT
  · exact lowerLevels_respects _ _ _ _ A T hAT
theorem honestNonce_short (lay : Layer) (tree level c : Nat) :
    WCT9.honestNonce A lay tree level c = WCT9.honestNonce T lay tree level c := by
  unfold WCT9.honestNonce
  split_ifs
  · rw [wotsTree_short hAT]
    unfold topNodeAt
    exact congrArg Prod.fst (topNonceSearch_respects _ _ _ _ _ _ A T hAT)
  · rfl
theorem ftsLevels_short (index coord : Nat) (hc : coord < 9) :
    Extract.ftsLevels A index coord = Extract.ftsLevels T index coord := by
  unfold Extract.ftsLevels
  have h1 := Extract.ftsNodes_eq A index ⟨coord, hc⟩
  have h2 := Extract.ftsNodes_eq T index ⟨coord, hc⟩
  have h3 := ClaudeWCT.WCT9.Wots.coordNodes_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) ⟨coord, hc⟩
  rw [show Extract.ftsNodes A index coord = Extract.ftsNodes T index coord from h1.trans (h3.trans h2.symm)]
theorem ftsPairsHonest_short (index : Nat) : Extract.ftsPairsHonest A index = Extract.ftsPairsHonest T index := by
  rw [Extract.ftsPairsHonest_eq, Extract.ftsPairsHonest_eq]
  exact congrArg List.ofFn (funext fun coord => ClaudeWCT.WCT9.Wots.coordinatePair_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) coord)
theorem wctValue_short (index coord child chain step : Nat) (hc : coord < 9) (hch : child < 128) (ht : chain < 6)
    (hs : step ≤ 4) :
    Extract.wctValue A index coord child chain step = Extract.wctValue T index coord child chain step :=
  ClaudeWCT.WCT9.Wots.ftsChainValue_congr (index := index) (T := A) (T' := T)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) ⟨coord, hc⟩ ⟨child, hch⟩ ⟨chain, ht⟩ step hs
theorem ftsPrev_short (index coord : Nat) (hc : coord ≤ 9) :
    Extract.ftsPrev A index coord = Extract.ftsPrev T index coord :=
  ClaudeWCT.WCT9.Wots.ftsPrev_congr (index := index)
    (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq)) coord hc
theorem wctEnds_short (index coord child : Nat) (hc : coord < 9) (hch : child < 128) :
    Extract.wctEnds A index coord child = Extract.wctEnds T index coord child := by
  unfold Extract.wctEnds
  exact congrArg List.ofFn (funext fun t => wctValue_short hAT index coord child t.val 4 hc hch t.isLt le_rfl)
theorem leafMsg_short (L : LeafAddr) : leafMsg A L = leafMsg T L := by
  unfold leafMsg
  split_ifs
  · unfold Extract.honestPair
    rw [wotsTree_short hAT]
  · rw [honestTop_short hAT]
theorem referenceSearch_short (L : LeafAddr) : referenceSearch A L = referenceSearch T L := by
  unfold referenceSearch
  rw [leafMsg_short hAT]
  exact layerCounterSearch_respects _ _ _ _ _ _ A T hAT
theorem referenceDigits_short (L : LeafAddr) : referenceDigits A L = referenceDigits T L := by
  unfold referenceDigits
  rw [referenceSearch_short hAT]
theorem depth_short (a : ChainAddr) : depth A a = depth T a := by
  unfold depth
  rw [referenceDigits_short hAT]
theorem frontierValue_short (a : ChainAddr) : frontierValue A a = frontierValue T a := by
  unfold frontierValue
  rw [depth_short hAT, wotsSeed_short hAT]
  exact honestChainValueW_short hAT _ _ _ _ _ _
theorem referenceInput_short (L : LeafAddr) : referenceInput A L = referenceInput T L := by
  unfold referenceInput
  rw [referenceSearch_short hAT, leafMsg_short hAT]
theorem honestInput_short (position : Extract.Pos) (hb : position.Bounded) :
    Extract.honestInput A position = Extract.honestInput T position := by
  cases position with
  | chain lay tree leaf i step =>
      simp only [Extract.honestInput]
      rw [wotsSeed_short hAT]
      exact congrArg (fun v => pad64 (WCT9.chainInputW lay tree leaf i step v)) (honestChainValueW_short hAT _ _ _ _ _ _)
  | leaf lay tree leaf =>
      simp only [Extract.honestInput]
      rw [List.map_congr_left (fun i _ => wotsEnd_short hAT lay tree leaf i)]
  | node lay tree level node =>
      simp only [Extract.honestInput]
      rw [wotsTree_short hAT, honestNonce_short hAT]
  | forest index =>
      simp only [Extract.honestInput]
      rw [ftsPairsHonest_short hAT]
  | wctChain index coord child t step =>
      obtain ⟨-, hc, hch, ht, hs⟩ := hb
      simp only [Extract.honestInput]
      rw [wctValue_short hAT index coord child t step hc hch ht (by omega)]
  | wctLeaf index coord child =>
      obtain ⟨-, hc, hch⟩ := hb
      simp only [Extract.honestInput]
      rw [wctEnds_short hAT index coord child hc hch, ftsPrev_short hAT index coord (by omega)]
  | wctNode index coord level nd =>
      obtain ⟨-, hc, -, -⟩ := hb
      simp only [Extract.honestInput]
      rw [ftsLevels_short hAT index coord hc, ftsPrev_short hAT index coord (by omega)]
end objects
theorem honestInput_length (answers : Answers) (position : Extract.Pos) :
    (Extract.honestInput answers position).length ≤ SeccLaw.maxInputLength := by
  cases position with
  | chain lay tree leaf i step =>
      apply short_of_le
      rw [WCT9.chainInputW_length]; omega
  | leaf lay tree leaf =>
      apply short_of_le
      simp only [Extract.leafInput, SigGolfCandidate.T3.leafInput_length, List.length_map, List.length_range]
      have := chainCount_le lay
      split_ifs <;> omega
  | node lay tree level node =>
      apply short_of_le
      simp [Extract.honestInput, WCT9.pad64_merkleNodeInputN, WCT9.merkleNodeInputN_length]
  | forest index =>
      apply short_of_le
      rw [Extract.forestInput, ClaudeWCT.WCT9.forestInput_length _ _ (Extract.ftsPairsHonest_length _ _)]
      omega
  | wctChain index coord child t step =>
      apply short_of_le
      simp only [ClaudeWCT.WCT9.ftsChainInputW_padded, ClaudeWCT.WCT9.ftsChainInputW_length]
      omega
  | wctLeaf index coord child =>
      apply short_of_le
      simp only [Extract.wctLeafInputP, Extract.listInput_length', List.length_cons, List.length_drop,
        Extract.wctEnds, List.length_ofFn]
      omega
  | wctNode index coord level node =>
      apply short_of_le
      simp [nodeInputP]
end ClaudeWCT.W9.T3.Security.Wots.Ref
