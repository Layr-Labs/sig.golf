import SigGolfCandidate.FtsCode
set_option debug.skipKernelTC true
set_option linter.all false

/-! # FTS carrier grind: the machine-level search `FtsGrind.search` and the scheme's `ftsNonceSearch`

`ftsNonceSearch` (Merge011) hashes `ftsNodeInputN` with `ftsHash heap` (the `ftsHighHeap` half) and tests
`ftsZeroOk`; `FtsGrind.searchH hi b` hashes `trialInput pre n right` with `publicHash` and tests `zeroOkH hi b` on the
half `hi`. They are the same program up to keeping that half of the answer (`ftsNonceSearch_eqH`); on the low-half
heaps it is E8's `search` (`ftsNonceSearch_eq`). -/

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

theorem zeroOkH_fts (hi : Bool) (coord heap : Nat) (a : HashOutput) :
    zeroOkH hi (ftsZeroBits coord heap) a = ftsZeroOk coord heap (halfOf hi a) := by
  unfold zeroOkH ftsZeroOk
  have h := (halfOf hi a).isLt
  by_cases hz : (halfOf hi a).toNat < 2 ^ (128 - ftsZeroBits coord heap)
  · rw [decide_eq_true hz]
    symm; rw [beq_iff_eq, Nat.div_eq_zero_iff]; right; exact hz
  · rw [decide_eq_false hz]
    symm; rw [beq_eq_false_iff_ne, ne_eq, Nat.div_eq_zero_iff]
    rintro (h0 | h0)
    · exact absurd h0 (by positivity)
    · exact hz h0

theorem ftsNodeHashN_half (coord index heap n : Nat) (left right : Digest) :
    ftsNodeHashN coord index heap n left right =
      (fun a => halfOf (ClaudeWCT.WCT9.ftsHighHeap heap) a) <$> publicHash (ftsNodeInputN coord index heap n left right) := by
  unfold ftsNodeHashN ClaudeWCT.WCT9.ftsHash halfOf
  cases ClaudeWCT.WCT9.ftsHighHeap heap <;> rfl

/-- Y5 #1: the scheme's FTS nonce search is the machine-level search on the heap's half (`ftsHighHeap`). -/
theorem ftsNonceSearch_eqH (coord index heap : Nat) (left right : Digest) :
    ∀ fuel n, ftsNonceSearch coord index heap left right fuel n =
      (fun r => (r.1, halfOf (ClaudeWCT.WCT9.ftsHighHeap heap) r.2)) <$>
        searchH (ClaudeWCT.WCT9.ftsHighHeap heap) (ftsZeroBits coord heap) (ftsPre coord index heap left)
          (bytesLE 16 right) fuel n
  | 0, n => by
      simp only [ftsNonceSearch, searchH, ftsNodeHashN_half, trialInput_fts, map_bind, bind_assoc, pure_bind,
        bind_map_left]
      rfl
  | fuel + 1, n => by
      simp only [ftsNonceSearch, searchH, ftsNodeHashN_half, trialInput_fts, map_bind, bind_assoc, pure_bind,
        bind_map_left]
      congr 1
      funext a
      rw [zeroOkH_fts]
      split
      · simp
      · exact ftsNonceSearch_eqH coord index heap left right fuel (n + 1)

/-- The scheme's FTS nonce search on a low-half heap (heaps `8..15`, odd heaps `17..31`) is the machine-level search
with the answer's low half kept. -/
theorem ftsNonceSearch_eq {coord index heap : Nat} (hlo : ClaudeWCT.WCT9.ftsHighHeap heap = false)
    (left right : Digest) (fuel n : Nat) :
    ftsNonceSearch coord index heap left right fuel n =
      (fun r => (r.1, r.2.extractLsb' 0 128)) <$>
        search (ftsZeroBits coord heap) (ftsPre coord index heap left) (bytesLE 16 right) fuel n := by
  rw [ftsNonceSearch_eqH, hlo, searchH_false]
  rfl

end SigGolfCandidate.FtsGrind
