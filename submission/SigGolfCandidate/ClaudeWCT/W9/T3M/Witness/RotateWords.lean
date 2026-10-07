import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Rotate
import SigGolfCandidate.T3M.Bytes

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3 SigGolfCandidate.T3M
open SphincsSecurity (bytesLE bytesLE_length)

theorem legacyCounter_words (c : BitVec 32) :
    wordsOf (bytesLE 4 c ++ zeros 12) = [BitVec.ofNat 64 c.toNat, 0] := by
  have hc : readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
    simp
  rw [show zeros 12 = List.replicate 4 0 ++ List.replicate (8 * 1) 0 by
      simp [zeros, List.replicate_add],
    ← List.append_assoc, wordsOf_append8 _ _ (by simp [bytesLE_length]), hc, wordsOf_replicate_zero]
  rfl

theorem tailCounter_words (c : BitVec 32) :
    wordsOf (zeros 12 ++ bytesLE 4 c) = [0, BitVec.ofNat 64 (256 ^ 4 * c.toNat)] := by
  have hc : readLE (zeros 4 ++ bytesLE 4 c) = 256 ^ 4 * c.toNat := by
    rw [readLE_append, readLE_bytesLE]
    simp [zeros, readLE_cons, readLE_nil]
  rw [show zeros 12 = zeros 8 ++ zeros 4 by simp [zeros, List.replicate_add],
    List.append_assoc, wordsOf_append8 _ _ (by simp [zeros]),
    show zeros 4 ++ bytesLE 4 c = (zeros 4 ++ bytesLE 4 c) ++ [] by simp,
    wordsOf_append8 _ _ (by simp [zeros, bytesLE_length]), hc]
  simp [zeros, wordsOf_nil, readLE_cons, readLE_nil]

theorem legacyDigest_words (w : WCT9.Witness) :
    wordsOf (legacyDigestBytes w) =
      [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64,
        BitVec.ofNat 64 w.digestCounter.toNat, 0] := by
  unfold legacyDigestBytes
  rw [List.append_assoc, wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_bytesLE16, legacyCounter_words]
  rfl

theorem tailDigest_words (w : WCT9.Witness) :
    wordsOf (digestBytes w) =
      [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64,
        0, BitVec.ofNat 64 (256 ^ 4 * w.digestCounter.toNat)] := by
  unfold digestBytes
  rw [List.append_assoc, wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_bytesLE16, tailCounter_words]
  rfl

theorem legacyWit_words (N : HashOutput) (w : WCT9.Witness) :
    wordsOf (legacyWitList N w) =
      [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64,
        BitVec.ofNat 64 w.digestCounter.toNat, 0] ++ wordsOf (witBody N w) := by
  rw [legacyWitList_eq, wordsOf_append _ _ (by simp [legacyDigestBytes_length]), legacyDigest_words]

theorem tailWit_words (N : HashOutput) (w : WCT9.Witness) :
    wordsOf (witList N w) = wordsOf (witBody N w) ++
      [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64,
        0, BitVec.ofNat 64 (256 ^ 4 * w.digestCounter.toNat)] := by
  rw [witList, wordsOf_append _ _ (by simp [witBody_length_eq]), tailDigest_words]

theorem moved_body_word (N : HashOutput) (w : WCT9.Witness) (i : Nat) (hi : i < 2725) :
    (wordsOf (witList N w)).getD i 0 = (wordsOf (legacyWitList N w)).getD (i + 4) 0 := by
  have hl : (wordsOf (witBody N w)).length = 2725 :=
    length_wordsOf 2725 _ (by rw [witBody_length_eq])
  rw [tailWit_words, legacyWit_words, List.getD_append _ _ _ _ (by omega),
    List.getD_append_right _ _ _ _ (by simp)]
  simp

#print axioms moved_body_word
#print axioms tailWit_words
end ClaudeWCT.W9.T3M
