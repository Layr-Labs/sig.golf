import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Leaf
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Defs

namespace ClaudeWCT.W9.T3M.BC
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
/-- Campaign S1 encoding row tweak: one word `t3` with the witness high word `hp`. -/
def rowTweakH (lay : Layer) (tree leaf : Nat) (hp : BitVec 64) : BitVec 128 :=
  hp ++ hyperWord lay.val (tree * 2 ^ height lay + leaf)
theorem rowTweakH_zero (lay : Layer) (tree leaf : Nat) : rowTweakH lay tree leaf 0 = rowTweak lay tree leaf := rfl
theorem rowTweakH_injective {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {hp hp' : BitVec 64}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (h : rowTweakH lay tree leaf hp = rowTweakH lay' tree' leaf' hp') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ hp = hp' := by
  obtain ⟨hh, hw⟩ := append64_inj h
  obtain ⟨e1, e2, e3⟩ := rowTweak_injective hl hr hl' hr' (by rw [rowTweak, rowTweak, hw])
  exact ⟨e1, e2, e3, hh⟩
theorem pairEncodingInputPH_eq (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32) (hp : BitVec 64)
    (pad : BitVec 96) :
    WCT9.pairEncodingInputPH lay tree leaf l r counter hp pad =
      bytesLE 16 l ++ bytesLE 16 (rowTweakH lay tree leaf hp) ++ bytesLE 4 counter ++ bytesLE 12 pad ++
        bytesLE 16 r := rfl
theorem layerEncodingInputP_forest (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    layerEncodingInputP lay tree leaf (.forest root) counter hp pad padR =
      WCT9.pairEncodingInputPH lay tree leaf root padR counter hp pad := rfl
theorem layerEncodingInputP_pair (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    layerEncodingInputP lay tree leaf (.pair l r) counter hp pad padR =
      WCT9.pairEncodingInputPH lay tree leaf l r counter hp pad :=
  rfl
def rowLeft : WCT9.LayerMsg → Digest
  | .forest root => root
  | .pair l _ => l
def rowRight (padR : Digest) : WCT9.LayerMsg → Digest
  | .forest _ => padR
  | .pair _ r => r
theorem layerEncodingInputP_eq (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    layerEncodingInputP lay tree leaf msg counter hp pad padR =
      WCT9.pairEncodingInputPH lay tree leaf (rowLeft msg) (rowRight padR msg) counter hp pad := by
  cases msg <;> rfl
theorem pairEncodingInputPH_length (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) : (WCT9.pairEncodingInputPH lay tree leaf l r counter hp pad).length = 64 := by
  simp only [WCT9.pairEncodingInputPH, List.length_append, bytesLE_length]
theorem layerEncodingInputP_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    (layerEncodingInputP lay tree leaf msg counter hp pad padR).length = 64 := by
  rw [layerEncodingInputP_eq]; exact pairEncodingInputPH_length _ _ _ _ _ _ _ _
theorem pad64_pairEncodingInputPH (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) :
    pad64 (WCT9.pairEncodingInputPH lay tree leaf l r counter hp pad) =
      WCT9.pairEncodingInputPH lay tree leaf l r counter hp pad := by
  simp [pad64, WCT9.pairEncodingInputPH, bytesLE_length]
theorem pad64_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (l r : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    pad64 (WCT9.pairEncodingInputP lay tree leaf l r counter pad) = WCT9.pairEncodingInputP lay tree leaf l r counter pad := by
  simp [pad64, WCT9.pairEncodingInputP, bytesLE_length]
theorem pad64_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    pad64 (layerEncodingInputP lay tree leaf msg counter hp pad padR) =
      layerEncodingInputP lay tree leaf msg counter hp pad padR := by
  rw [layerEncodingInputP_eq, pad64_pairEncodingInputPH]
theorem layerEncodingRow_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    (pad64 (layerEncodingInputP lay tree leaf msg counter hp pad padR)).length = 64 := by
  rw [pad64_layerEncodingInputP, layerEncodingInputP_length]
theorem pad64_layerEncodingInputP_zero (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    pad64 (layerEncodingInputP lay tree leaf msg counter 0 0 0) =
      pad64 (WCT9.layerEncodingInput lay tree leaf msg counter) := by
  cases msg with
  | forest root =>
      rw [layerEncodingInputP_forest, WCT9.pairEncodingInputPH_zero, pad64_pairEncodingInputP]
      exact (pad64_encodingInput lay tree leaf root counter).symm
  | pair l r => rfl
theorem layerEncodingInputP_split (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    ∃ first rest : HashInput, first.length = 16 ∧
      layerEncodingInputP lay tree leaf msg counter hp pad padR =
        first ++ bytesLE 16 (rowTweakH lay tree leaf hp) ++ (bytesLE 4 counter ++ rest) := by
  refine ⟨bytesLE 16 (rowLeft msg), bytesLE 12 pad ++ bytesLE 16 (rowRight padR msg), bytesLE_length _ _, ?_⟩
  rw [layerEncodingInputP_eq]
  simp only [WCT9.pairEncodingInputPH, rowTweakH, List.append_assoc]
theorem hdrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    Extract.hdrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter hp pad padR)) =
      bytesLE 16 (rowTweakH lay tree leaf hp) := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter hp pad padR
  rw [pad64_layerEncodingInputP, he]
  unfold Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' hf, List.take_left' (bytesLE_length _ _)]
theorem hdrBlock_layerEncodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    Extract.hdrBlock (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)) =
      bytesLE 16 (rowTweak lay tree leaf) := by
  rw [← pad64_layerEncodingInputP_zero]
  exact hdrBlock_layerEncodingInputP lay tree leaf msg counter 0 0 0
def ctrBlock (input : HashInput) : HashInput := (input.drop 32).take 4
theorem ctrBlock_layerEncodingInputP (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32)
    (hp : BitVec 64) (pad : BitVec 96) (padR : Digest) :
    ctrBlock (pad64 (layerEncodingInputP lay tree leaf msg counter hp pad padR)) = bytesLE 4 counter := by
  obtain ⟨first, rest, hf, he⟩ := layerEncodingInputP_split lay tree leaf msg counter hp pad padR
  rw [pad64_layerEncodingInputP, he]
  unfold ctrBlock
  have h32 : (first ++ bytesLE 16 (rowTweakH lay tree leaf hp)).length = 32 := by
    simp [hf, bytesLE_length]
  rw [List.drop_left' h32, List.take_left' (bytesLE_length _ _)]
theorem pairEncodingInputPH_injective {up up' : Layer} {tree leaf tree' leaf' : Nat} {l r l' r' : Digest}
    {c c' : BitVec 32} {hp hp' : BitVec 64} {pad pad' : BitVec 96}
    (hl : leaf < 2 ^ height up) (hr : tree * 2 ^ height up + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height up') (hr' : tree' * 2 ^ height up' + leaf' < 2 ^ 32)
    (h : WCT9.pairEncodingInputPH up tree leaf l r c hp pad = WCT9.pairEncodingInputPH up' tree' leaf' l' r' c' hp' pad') :
    up = up' ∧ tree = tree' ∧ leaf = leaf' ∧ l = l' ∧ r = r' ∧ c = c' ∧ pad = pad' ∧ hp = hp' := by
  rw [pairEncodingInputPH_eq, pairEncodingInputPH_eq] at h
  obtain ⟨h, hR⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  obtain ⟨e1, e2, e3, e4⟩ := rowTweakH_injective hl hr hl' hr' (bytesLE_injective hh)
  exact ⟨e1, e2, e3, bytesLE_injective hL, bytesLE_injective hR, bytesLE_injective hc, bytesLE_injective hp, e4⟩
theorem layerEncodingRow_coords {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {hp hp' : BitVec 64} {pad pad' : BitVec 96} {padR padR' : Digest}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (h : pad64 (layerEncodingInputP lay tree leaf msg c hp pad padR) =
      pad64 (layerEncodingInputP lay' tree' leaf' msg' c' hp' pad' padR')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ c = c' := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  obtain ⟨e1, e2, e3, -, -, e4, -⟩ := pairEncodingInputPH_injective hl hr hl' hr' h
  exact ⟨e1, e2, e3, e4⟩
theorem layerEncodingRow_injective {lay lay' : Layer} {tree leaf tree' leaf' : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {hp hp' : BitVec 64} {pad pad' : BitVec 96} {padR padR' : Digest}
    (hl : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height lay') (hr' : tree' * 2 ^ height lay' + leaf' < 2 ^ 32)
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay' msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c hp pad padR) =
      pad64 (layerEncodingInputP lay' tree' leaf' msg' c' hp' pad' padR')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ msg = msg' ∧ c = c' ∧ pad = pad' ∧ hp = hp' ∧
      (∀ root, msg = .forest root → padR = padR') := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq] at h
  obtain ⟨rfl, rfl, rfl, hL, hR, rfl, rfl, rfl⟩ := pairEncodingInputPH_injective hl hr hl' hr' h
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · cases msg with
    | forest root => exact hf.elim
    | pair l r =>
        cases msg' with
        | forest root' => exact hf'.elim
        | pair l' r' => simp only [rowLeft, rowRight] at hL hR; rw [hL, hR]
  · rintro root rfl
    exact hf.elim
theorem layerEncodingRow_injective_leaf {lay : Layer} {tree leaf : Nat} {msg msg' : WCT9.LayerMsg}
    {c c' : BitVec 32} {hp hp' : BitVec 64} {pad pad' : BitVec 96} {padR padR' : Digest}
    (hf : Extract.msgFits lay msg) (hf' : Extract.msgFits lay msg')
    (h : pad64 (layerEncodingInputP lay tree leaf msg c hp pad padR) =
      pad64 (layerEncodingInputP lay tree leaf msg' c' hp' pad' padR')) :
    msg = msg' ∧ c = c' ∧ pad = pad' ∧ hp = hp' ∧ (∀ root, msg = .forest root → padR = padR') := by
  rw [pad64_layerEncodingInputP, pad64_layerEncodingInputP, layerEncodingInputP_eq, layerEncodingInputP_eq,
    pairEncodingInputPH_eq, pairEncodingInputPH_eq] at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, hH⟩ := List.append_inj h (by simp only [bytesLE_length])
  have hL := bytesLE_injective hL
  have hR := bytesLE_injective hr
  have hH := (append64_inj (bytesLE_injective hH)).1
  refine ⟨?_, bytesLE_injective hc, bytesLE_injective hp, hH, ?_⟩
  · cases msg with
    | forest root => exact hf.elim
    | pair l r =>
        cases msg' with
        | forest root' => exact hf'.elim
        | pair l' r' => simp only [rowLeft, rowRight] at hL hR; rw [hL, hR]
  · rintro root rfl
    exact hf.elim
/-- Honest layer frame with a zero 12-byte row pad. (Nested FTS r1-1: the L3 row is a pair row, so the old
`wbcRight` slot is no longer read and carries no condition.) -/
def GoodZ (answers : SigGolfCandidate.T3.Correctness.Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  Extract.Good answers w index lay ∧ wbcPad w index lay = 0 ∧ wbcHigh w index lay = 0
theorem GoodZ.good {answers : SigGolfCandidate.T3.Correctness.Answers} {w : WBytes} {index : Nat} {lay : Layer}
    (h : GoodZ answers w index lay) : Extract.Good answers w index lay := h.1
end ClaudeWCT.W9.T3M.BC
