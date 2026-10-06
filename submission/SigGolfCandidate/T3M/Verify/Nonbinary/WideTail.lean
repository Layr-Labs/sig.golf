import SigGolfCandidate.T3M.Verify.Nonbinary.PairAlgebra

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
theorem compressedSum_ne_254 (f : Nat → Nat) : compressedSum f ≠ 254 := by
  intro he
  have hgood : ∀ i, i < 17 → f i < 125 := by
    intro i hi
    by_contra hn
    have hb := compressedSum_bad f i hi (by omega)
    omega
  have hf := compressedSum_good f hgood
  have H : ∀ l : List Nat, (∀ i ∈ l, f i < 125) →
      (l.map fun i => rankLookup (f i)).sum ≤ 12 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro hh
      have hd := rankWeight_le (f i)
      have ht := ih (fun j hj => hh j (by simp [hj]))
      have hi := hh i (by simp)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [rankLookup, if_pos hi]
      omega
  have hb : fullSum f ≤ 204 := by
    have h := H (List.range 17) (fun i hi => hgood i (List.mem_range.mp hi))
    simpa [fullSum] using h
  omega
def wideTailTarget (r : Nat) : Nat :=
  if r < 64 then 128 - (r % 4 + (r / 4) % 4 + r / 16) else 254
theorem wideTailTarget_le (r : Nat) : wideTailTarget r ≤ 254 := by
  unfold wideTailTarget; split_ifs <;> omega
end SigGolfCandidate.T3M.Verify.Nonbinary
