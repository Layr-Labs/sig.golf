import SigGolfCandidate.ClaudeWCT.W9.New.Positions.FtsBridge
import SigGolfCandidate.ClaudeWCT.W9.New.BC.Respects

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
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem honestForest_short (index : Nat) : Extract.honestForest A index = Extract.honestForest T index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestForest_congr (fun _ hq => hAT _ (ClaudeWCT.WCT9.Wots.ftsQuery_short hq))
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
  exact chainValue_short hAT _ _ _ _ _ _ _
theorem wotsRoot_short (lay : Layer) (tree leaf : Nat) :
    WCT9.wotsRoot A lay tree leaf = WCT9.wotsRoot T lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i _ => wotsEnd_short hAT lay tree leaf i)]
  apply leafHash_respects
  · simp only [List.length_map, List.length_range]
    have := chainCount_le lay
    omega
  · exact hAT
theorem wotsTree_short (lay : Layer) (tree : Nat) :
    WCT9.wotsTree A lay tree = WCT9.wotsTree T lay tree := by
  unfold WCT9.wotsTree
  rw [List.map_congr_left (fun leaf _ => wotsRoot_short hAT lay tree leaf)]
  exact buildLevels_respects _ _ _ _ _ A T hAT
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
theorem wctEnds_short (index coord child : Nat) (hc : coord < 9) (hch : child < 128) :
    Extract.wctEnds A index coord child = Extract.wctEnds T index coord child := by
  unfold Extract.wctEnds
  exact congrArg List.ofFn (funext fun t => wctValue_short hAT index coord child t.val 4 hc hch t.isLt le_rfl)
theorem leafMsg_short (L : LeafAddr) : leafMsg A L = leafMsg T L := by
  unfold leafMsg
  split_ifs
  · unfold Extract.honestPair
    rw [wotsTree_short hAT]
  · rw [honestForest_short hAT]
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
  exact honestChainValue_short hAT _ _ _ _ _ _
theorem referenceInput_short (L : LeafAddr) : referenceInput A L = referenceInput T L := by
  unfold referenceInput
  rw [referenceSearch_short hAT, leafMsg_short hAT]
theorem honestInput_short (position : Extract.Pos) (hb : position.Bounded) :
    Extract.honestInput A position = Extract.honestInput T position := by
  cases position with
  | chain lay tree leaf i step =>
      simp only [Extract.honestInput]
      rw [wotsSeed_short hAT, honestChainValue_short hAT]
  | leaf lay tree leaf =>
      simp only [Extract.honestInput]
      rw [List.map_congr_left (fun i _ => wotsEnd_short hAT lay tree leaf i)]
  | node lay tree level node =>
      simp only [Extract.honestInput]
      rw [wotsTree_short hAT]
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
      rw [wctEnds_short hAT index coord child hc hch]
  | wctNode index coord level nd =>
      obtain ⟨-, hc, -, -⟩ := hb
      simp only [Extract.honestInput]
      rw [ftsLevels_short hAT index coord hc]
end objects
theorem honestInput_length (answers : Answers) (position : Extract.Pos) :
    (Extract.honestInput answers position).length ≤ SeccLaw.maxInputLength := by
  cases position with
  | chain lay tree leaf i step =>
      apply short_of_le
      rw [chainInput_length]; omega
  | leaf lay tree leaf =>
      apply short_of_le
      simp only [Extract.leafInput, SigGolfCandidate.T3.leafInput_length, List.length_map, List.length_range]
      have := chainCount_le lay
      split_ifs <;> omega
  | node lay tree level node =>
      apply short_of_le
      simp [nodeInputP]
  | forest index =>
      apply short_of_le
      rw [Extract.forestInput, ClaudeWCT.WCT9.forestInput_length _ _ (Extract.ftsPairsHonest_length _ _)]
      omega
  | wctChain index coord child t step =>
      apply short_of_le
      simp only [ClaudeWCT.WCT9.chainInput, zero16, List.length_append, List.length_replicate, bytesLE_length]
      omega
  | wctLeaf index coord child =>
      apply short_of_le
      simp only [Extract.wctLeafInput, Extract.listInput_length', List.length_cons, List.length_drop,
        Extract.wctEnds, List.length_ofFn]
      omega
  | wctNode index coord level node =>
      apply short_of_le
      simp [nodeInputP]
end ClaudeWCT.W9.T3.Security.Wots.Ref
