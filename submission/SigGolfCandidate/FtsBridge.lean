import SigGolfCandidate.FtsCode
set_option linter.all false

/-! # FTS carrier grind: the machine-level search `FtsGrind.search` and the scheme's `ftsNonceSearch`

`ftsNonceSearch` (Merge011) hashes `ftsNodeInputN` with `shortHash` (the low half) and tests `ftsZeroOk`;
`FtsGrind.search b` hashes `trialInput pre n right` with `publicHash` and tests `zeroOk b` on the low half. They are
the same program up to keeping the low half of the answer. -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.T3 (Digest HashOutput M publicHash shortHash nonceBytes)
open SphincsSecurity (bytesLE)
open ClaudeWCT.WCT9 (ftsZeroBits ftsZeroOk ftsNodeInputN ftsNodeHashN ftsNonceSearch wctNodeHeader)

/-- The 32-byte trial prefix of an FTS node: left value and header. -/
def ftsPre (coord index heap : Nat) (left : Digest) : List UInt8 :=
  bytesLE 16 left ++ bytesLE 16 (wctNodeHeader coord index heap)

theorem trialInput_fts (coord index heap n : Nat) (left right : Digest) :
    trialInput (ftsPre coord index heap left) n (bytesLE 16 right) = ftsNodeInputN coord index heap n left right := by
  simp [trialInput, ftsPre, ftsNodeInputN, List.append_assoc]

theorem zeroOk_fts (coord heap : Nat) (a : HashOutput) :
    zeroOk (ftsZeroBits coord heap) a = ftsZeroOk coord heap (a.extractLsb' 0 128) := by
  unfold zeroOk ftsZeroOk
  have h := (a.extractLsb' 0 128).isLt
  by_cases hz : (a.extractLsb' 0 128).toNat < 2 ^ (128 - ftsZeroBits coord heap)
  · rw [decide_eq_true hz]
    symm; rw [beq_iff_eq, Nat.div_eq_zero_iff]; right; exact hz
  · rw [decide_eq_false hz]
    symm; rw [beq_eq_false_iff_ne, ne_eq, Nat.div_eq_zero_iff]
    rintro (h0 | h0)
    · exact absurd h0 (by positivity)
    · exact hz h0

/-- The scheme's FTS nonce search is the machine-level search with the answer's low half kept. -/
theorem ftsNonceSearch_eq (coord index heap : Nat) (left right : Digest) :
    ∀ fuel n, ftsNonceSearch coord index heap left right fuel n =
      (fun r => (r.1, r.2.extractLsb' 0 128)) <$>
        search (ftsZeroBits coord heap) (ftsPre coord index heap left) (bytesLE 16 right) fuel n
  | 0, n => by
      simp only [ftsNonceSearch, search, ftsNodeHashN, shortHash, trialInput_fts, map_bind, bind_assoc, pure_bind]
      rfl
  | fuel + 1, n => by
      simp only [ftsNonceSearch, search, ftsNodeHashN, shortHash, trialInput_fts, map_bind, bind_assoc, pure_bind]
      congr 1
      funext a
      rw [zeroOk_fts]
      split
      · simp
      · exact ftsNonceSearch_eq coord index heap left right fuel (n + 1)

end SigGolfCandidate.FtsGrind
