import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Encode
import SigGolfCandidate.Choice.Search

namespace SigGolfCandidate.Choice.Witness
open SigGolfCandidate.T3
open SigGolfCandidate.T3M (zeros window window_append_left window_append_right window_full
  readLE_drop readLE_take)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A byte window below the truncation boundary survives serialization even
when the source list contains additional trailing bytes. -/
theorem extract_readLE_window (L : List UInt8) (n off k : Nat) (h : off + k ≤ n) :
    (BitVec.ofNat (8 * n) (readLE L)).extractLsb' (8 * off) (8 * k) =
      BitVec.ofNat (8 * k) (readLE (window L off k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ (8 * n) = 2 ^ (8 * (n - off)) * 2 ^ (8 * off) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp, Nat.mod_mul_left_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * k ≤ 8 * (n - off)))]
  have hb : ∀ j : Nat, 2 ^ (8 * j) = 256 ^ j := fun j => by rw [pow_mul]; norm_num
  rw [hb off, hb k, readLE_drop, readLE_take]
  unfold window
  rw [← readLE_take, Nat.mod_mod]

theorem header_length (N : HashOutput) (w : ClaudeWCT.WCT9.Witness) :
    (headerBytes N w).length = 176 := by
  have hi (p : Prop) [Decidable p] (d : Digest) :
      (if p then bytesLE 16 d else zeros 16).length = 16 := by
    split <;> simp [zeros, bytesLE_length]
  simp only [headerBytes, List.length_append, hi, bytesLE_length]
  rfl

theorem hint_window (N : HashOutput) (w : ClaudeWCT.WCT9.Witness) :
    window (witList N w) 104 8 = bytesLE 8 w.topHint := by
  let prefixBytes :=
    (if (ClaudeWCT.WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then
      bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
      zeros 8 ++ bytesLE 8 1 ++ bytesLE 4 (w.counters 3) ++ zeros 68
  have hp : prefixBytes.length = 104 := by
    dsimp only [prefixBytes]
    split <;> simp [zeros, bytesLE_length]
  have hw : ∃ rest, witList N w = prefixBytes ++ (bytesLE 8 w.topHint ++ rest) := by
    refine ⟨zeros 32 ++
      (if (ClaudeWCT.WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then
        bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
      zeros 16 ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
        leafBuffersBytes w.signature ++ tailBytes w, ?_⟩
    simp only [witList, headerBytes, prefixBytes, List.append_assoc]
  obtain ⟨rest, hw⟩ := hw
  rw [hw, window_append_right _ _ _ _ hp.le, hp, Nat.sub_self,
    window_append_left _ _ _ _ (by simp only [bytesLE_length]; omega),
    window_full _ _ (bytesLE_length _ _)]

/-- Exact round trip at relative offset 104 (absolute address 1320). -/
theorem topHint_roundtrip (N : HashOutput) (w : ClaudeWCT.WCT9.Witness) :
    wtopHint (witEnc N w) = w.topHint := by
  change (BitVec.ofNat (8 * wsize) (readLE (witList N w))).extractLsb' (8 * 104) (8 * 8) = _
  rw [extract_readLE_window _ _ _ _ (by decide), hint_window,
    SigGolfCandidate.T3.Correctness.readLE_bytesLE]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem decoded_hint (N : HashOutput) (w : ClaudeWCT.WCT9.Witness) :
    (witDecP N (witEnc N w)).topHint = w.topHint := topHint_roundtrip N w

end SigGolfCandidate.Choice.Witness

#print axioms SigGolfCandidate.Choice.Witness.topHint_roundtrip
#print axioms SigGolfCandidate.Choice.Witness.decoded_hint
