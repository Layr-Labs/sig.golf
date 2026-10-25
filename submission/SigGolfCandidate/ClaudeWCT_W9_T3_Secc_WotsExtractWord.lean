import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsExtractChain
import SigGolfCandidate.ClaudeWCT_W9_New_G3b_Shared

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf route_split route_tree_succ route_forest)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem referenceInput_ne (answers : Answers) (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfit : Extract.msgFits L.lay msg)
    {digits : List Nat} (hd : decode L.lay (WCT9.encodingAnswer L.lay (answers (.inl (.inr (encRow L msg ctr pad))))) = some digits)
    (hne : msg ≠ leafMsg answers L ∨ digits ≠ referenceDigits answers L) :
    referenceInput answers L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers L with
  | none => rw [hs] at h; simp at h
  | some s =>
      obtain ⟨c, w'⟩ := s
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hm, hc, -⟩ := BC.layerEncodingRow_injective_leaf (msgFits_leafMsg answers L) hfit h
      rw [← h] at hd
      subst hm hc
      have hdec := referenceSearch_decode answers L hs
      have hw : referenceDigits answers L = w' := by unfold referenceDigits; rw [hs]; rfl
      have hdw : digits = w' := Option.some.inj (hd.symm.trans hdec)
      rcases hne with hne | hne
      · exact hne rfl
      · exact hne (hdw.trans hw.symm)
/-- The verifier's encoding row as an `encRow` (the row pad's high component is the XOR mask `hi ^^^ 1`). -/
theorem encRow_wit (L : LeafAddr) (msg : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96) (padR : Digest)
    (hi : BitVec 64) :
    encRow L msg counter (pad, padR, hi ^^^ 1) =
      pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter pad padR hi) := by
  show pad64 (layerEncodingInputP L.lay L.tree L.leaf msg counter pad padR ((hi ^^^ 1) ^^^ 1)) = _
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
theorem xor_one_inj {a b : BitVec 64} (h : a ^^^ 1 = b ^^^ 1) : a = b := by
  have := congrArg (· ^^^ (1 : BitVec 64)) h
  simpa [BitVec.xor_assoc] using this
/-- A row whose 12-byte pad is nonzero or whose high-word mask is nonzero (C2/C3 FULL: row high word `≠ 1`) is not
the reference row. -/
theorem referenceInput_ne_pad (answers : Answers) (L : LeafAddr) (msg : WCT9.LayerMsg) (ctr : BitVec 32) (pad : RowPad)
    (hfit : Extract.msgFits L.lay msg) (hpad : pad.1 ≠ 0 ∨ pad.2.2 ≠ 0) :
    referenceInput answers L ≠ some (encRow L msg ctr pad) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers L with
  | none => rw [hs] at h; simp at h
  | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨-, -, hp, -⟩ := BC.layerEncodingRow_injective_leaf (msgFits_leafMsg answers L) hfit h
      have hh := BC.layerEncodingRow_hi_eq h
      rcases hpad with hpad | hpad
      · exact hpad hp.symm
      · exact hpad (xor_one_inj hh).symm
theorem leafMsg_route (answers : Answers) (index : Nat) (lay : Layer) (hindex : index < 2 ^ 31) :
    leafMsg answers (routeLeaf index lay) = Extract.honestMsg answers index lay := by
  unfold leafMsg Extract.honestMsg
  simp only [routeLeaf]
  by_cases h : lay.val < 3
  · rw [dif_pos h, dif_pos h, route_tree_succ index lay h]
  · rw [dif_neg h, dif_neg h, route_forest index lay h, Nat.mod_eq_of_lt hindex]
end ClaudeWCT.W9.T3.Security.WotsExtract
