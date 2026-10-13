import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Leaf
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Defs

namespace ClaudeWCT.W9.T3M.BC
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
theorem layerEncodingInputP_forest (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    layerEncodingInputP lay tree leaf (.forest root) counter pad padR hi =
      WCT9.pairEncodingInputH lay tree leaf root padR counter pad hi := rfl
theorem layerEncodingInputP_pair (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    layerEncodingInputP lay tree leaf (.pair l r) counter pad padR hi =
      WCT9.pairEncodingInputH lay tree leaf l r counter pad hi :=
  rfl
def rowLeft : WCT9.LayerMsg → Digest
  | .forest root => root
  | .pair l _ => l
def rowRight (padR : Digest) : WCT9.LayerMsg → Digest
  | .forest _ => padR
  | .pair _ r => r
theorem layerEncodingInputP_eq (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    layerEncodingInputP lay tree leaf msg counter pad padR hi =
      WCT9.pairEncodingInputH lay tree leaf (rowLeft msg) (rowRight padR msg) counter pad hi := by
  cases msg <;> rfl
theorem layerEncodingInputP_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    (layerEncodingInputP lay tree leaf msg counter pad padR hi).length = 64 := by
  rw [layerEncodingInputP_eq]; exact WCT9.pairEncodingInputH_length _ _ _ _ _ _ _ _
theorem pad64_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    pad64 (WCT9.pairEncodingInputP lay tree leaf l r counter pad) = WCT9.pairEncodingInputP lay tree leaf l r counter pad := by
  simp [pad64, WCT9.pairEncodingInputP, bytesLE_length]
theorem pad64_pairEncodingInputH (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (hi : BitVec 64) :
    pad64 (WCT9.pairEncodingInputH lay tree leaf l r counter pad hi) =
      WCT9.pairEncodingInputH lay tree leaf l r counter pad hi := by
  simp [pad64, WCT9.pairEncodingInputH, bytesLE_length]
theorem pad64_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi) =
      layerEncodingInputP lay tree leaf msg counter pad padR hi := by
  rw [layerEncodingInputP_eq, pad64_pairEncodingInputH]
theorem layerEncodingRow_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)).length = 64 := by
  rw [pad64_layerEncodingInputP, layerEncodingInputP_length]
/-- The honest encoding (zero pads, row tweak high word 1). -/
theorem pad64_layerEncodingInputP_zero (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    pad64 (layerEncodingInputP lay tree leaf msg counter 0 0 1) =
      pad64 (WCT9.layerEncodingInput lay tree leaf msg counter) := by
  cases msg with
  | forest root =>
      rw [layerEncodingInputP_forest, WCT9.pairEncodingInputH_one, pad64_pairEncodingInputP]
      exact (pad64_encodingInput lay tree leaf root counter).symm
  | pair l r => rfl
theorem layerEncodingInputP_split (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    ∃ first rest : HashInput, first.length = 16 ∧
      layerEncodingInputP lay tree leaf msg counter pad padR hi =
        first ++ bytesLE 16 (WCT9.rowTweakW lay tree leaf hi) ++ (bytesLE 4 counter ++ rest) := by
  refine ⟨bytesLE 16 (rowLeft msg), bytesLE 12 pad ++ bytesLE 16 (rowRight padR msg), bytesLE_length _ _, ?_⟩
  rw [layerEncodingInputP_eq, WCT9.pairEncodingInputH_eq]
  simp only [List.append_assoc]
/-- C2/C3 (FULL): the header block of an encoding carries the row tweak with the witness high word `hi`. -/
theorem hdrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Extract.hdrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) =
      bytesLE 16 (WCT9.rowTweakW lay tree leaf hi) := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter pad padR hi
  rw [pad64_layerEncodingInputP, he]
  unfold Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' hf, List.take_left' (bytesLE_length _ _)]
theorem hdrBlock_layerEncodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.hdrBlock (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) =
      bytesLE 16 (rowTweak lay tree leaf) := by
  rw [← pad64_layerEncodingInputP_zero]
  exact hdrBlock_layerEncodingInputP lay tree leaf msg counter 0 0 1
def ctrBlock (input : HashInput) : HashInput := (input.drop 32).take 4
theorem ctrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    ctrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter pad padR hi)) = bytesLE 4 counter := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter pad padR hi
  rw [pad64_layerEncodingInputP, he]
  unfold ctrBlock
  have h32 : (first ++ bytesLE 16 (WCT9.rowTweakW lay tree leaf hi)).length = 32 := by
    simp [hf, bytesLE_length]
  rw [List.drop_left' h32, List.take_left' (bytesLE_length _ _)]
theorem layerEncodingRow_coords {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay' tree' leaf' msg' c' pad' padR' hi')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ c = c' := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  obtain ⟨e1, e2, e3, -, -, e4, -⟩ := WCT9.pairEncodingInputH_injective hl hr hl' hr' h
  exact ⟨e1, e2, e3, e4⟩
theorem layerEncodingRow_injective {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay' msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay' tree' leaf' msg' c' pad' padR' hi')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ msg = msg' ∧ c = c' ∧ pad = pad' ∧
      (∀ root, msg = .forest root → padR = padR') ∧ hi = hi' := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  obtain ⟨rfl, rfl, rfl, hL, hR, rfl, rfl, rfl⟩ := WCT9.pairEncodingInputH_injective hl hr hl' hr' h
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, rfl⟩
  · cases msg with
    | forest root => exact hf.elim
    | pair l r =>
        cases msg' with
        | forest root' => exact hf'.elim
        | pair l' r' => simp only [rowLeft, rowRight] at hL hR; rw [hL, hR]
  · rintro root rfl
    exact hf.elim
theorem layerEncodingRow_injective_leaf {lay : Layer} {tree leaf : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay tree leaf msg' c' pad' padR' hi')) :
    msg = msg' ∧ c = c' ∧ pad = pad' ∧ (∀ root, msg = .forest root → padR = padR') := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  unfold WCT9.pairEncodingInputH at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, -⟩ := List.append_inj h (by simp only [bytesLE_length])
  have hL := bytesLE_injective hL
  have hR := bytesLE_injective hr
  refine ⟨?_, bytesLE_injective hc, bytesLE_injective hp, ?_⟩
  · cases msg with
    | forest root => exact hf.elim
    | pair l r =>
        cases msg' with
        | forest root' => exact hf'.elim
        | pair l' r' => simp only [rowLeft, rowRight] at hL hR; rw [hL, hR]
  · rintro root rfl
    exact hf.elim
/-- The row tweak's high word of two equal encoding rows agrees (C2/C3 FULL: the high word is a witness pad). -/
theorem layerEncodingRow_hi_eq {lay : Layer} {tree leaf : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {padR padR' : Digest} {hi hi' : BitVec 64}
    (h : pad64 (layerEncodingInputP lay tree leaf msg c pad padR hi) =
      pad64 (layerEncodingInputP lay tree leaf msg' c' pad' padR' hi')) : hi = hi' := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  unfold WCT9.pairEncodingInputH at h
  obtain ⟨h, -⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, -⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, -⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨-, ht⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact (append64_inj (bytesLE_injective ht)).1
/-- Honest layer frame with a zero 12-byte row pad and the honest row high word 1 (C2/C3 FULL). (Nested FTS r1-1:
the L3 row is a pair row, so the old `wbcRight` slot is no longer read and carries no condition.) -/
def GoodZ (answers : SigGolfCandidate.T3.Correctness.Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  Extract.Good answers w index lay ∧ wbcPad w index lay = 0 ∧ wbcHigh w index lay = 1
theorem GoodZ.good {answers : SigGolfCandidate.T3.Correctness.Answers} {w : WBytes} {index : Nat} {lay : Layer}
    (h : GoodZ answers w index lay) : Extract.Good answers w index lay := h.1
end ClaudeWCT.W9.T3M.BC
