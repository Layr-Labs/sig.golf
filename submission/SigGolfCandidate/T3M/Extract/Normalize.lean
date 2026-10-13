import SigGolfCandidate.T3M.Bytes

namespace SigGolfCandidate.T3M.Extract
open SigGolfCandidate.T3
def canonicalHeader (hdr : HashInput) : HashInput :=
  if 128 ≤ (hdr.getD 0 0).toNat then hdr.take 8 ++ List.replicate 8 0 else hdr
@[simp] theorem canonicalHeader_unmarked (hdr : HashInput) (h : ¬128 ≤ (hdr.getD 0 0).toNat) :
    canonicalHeader hdr = hdr := by
  unfold canonicalHeader
  rw [if_neg h]
theorem canonicalHeader_marked (low pad : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = low ++ List.replicate 8 0 := by
  have hm : 128 ≤ ((low ++ pad).getD 0 0).toNat := by
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hmark
  unfold canonicalHeader
  rw [if_pos hm]
  simp [List.take_append, hlen]
theorem canonicalHeader_pad_irrelevant (low pad pad' : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = canonicalHeader (low ++ pad') := by
  rw [canonicalHeader_marked low pad hlen hmark, canonicalHeader_marked low pad' hlen hmark]
theorem canonicalHeader_zero_pad (low : HashInput) (hlen : low.length = 8) :
    canonicalHeader (low ++ List.replicate 8 0) = low ++ List.replicate 8 0 := by
  by_cases hm : 128 ≤ (low.getD 0 0).toNat
  · exact canonicalHeader_marked low _ hlen hm
  · apply canonicalHeader_unmarked
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hm
end SigGolfCandidate.T3M.Extract
namespace SigGolfCandidate.T3M.Extract
open SigGolfCandidate.T3
/-! ### Campaign S1 normalisation (length-aware)
A one-word label (top/lower folds, encodings, lower leaves, chains, FTS folds of levels 0..3) carries the position in
its low word `W` (bytes 16..24); the high word (bytes 24..32) is a witness pad. `padLabel len W` recognises these
words: top fold words `1 ≤ W < 2 ^ 16` (64-byte inputs only: the 320-byte forest header has `W = 3841`), marked words
(byte0 `≥ 128`), and the 0xc1-typed lower words (byte7 `= 193`). The digest word `W = 0`, the FTS two-word labels
(levels 4/5, byte1 6, `W ≥ 2 ^ 16`), the FTS leaf header and the forest header keep their high word. -/
def padLabel (len w : Nat) : Prop := (len = 64 ∧ 1 ≤ w ∧ w < 2 ^ 16) ∨ 128 ≤ w % 256 ∨ w / 2 ^ 56 % 256 = 193
instance (len w : Nat) : Decidable (padLabel len w) := by unfold padLabel; infer_instance
/-- Header block normalisation for an input of length `len`: erase the high word of a one-word label. -/
def canonicalHeaderL (len : Nat) (hdr : HashInput) : HashInput :=
  if padLabel len (readLE (hdr.take 8)) then hdr.take 8 ++ List.replicate 8 0 else hdr
theorem canonicalHeaderL_pad (len : Nat) (low pad : HashInput) (hlen : low.length = 8)
    (hp : padLabel len (readLE low)) :
    canonicalHeaderL len (low ++ pad) = low ++ List.replicate 8 0 := by
  unfold canonicalHeaderL
  rw [List.take_left' hlen, if_pos hp]
theorem canonicalHeaderL_keep (len : Nat) (low pad : HashInput) (hlen : low.length = 8)
    (hp : ¬padLabel len (readLE low)) :
    canonicalHeaderL len (low ++ pad) = low ++ pad := by
  unfold canonicalHeaderL
  rw [List.take_left' hlen, if_neg hp]
theorem canonicalHeaderL_zero_pad (len : Nat) (low : HashInput) (hlen : low.length = 8) :
    canonicalHeaderL len (low ++ List.replicate 8 0) = low ++ List.replicate 8 0 := by
  by_cases hp : padLabel len (readLE low)
  · exact canonicalHeaderL_pad len low _ hlen hp
  · exact canonicalHeaderL_keep len low _ hlen hp
end SigGolfCandidate.T3M.Extract
