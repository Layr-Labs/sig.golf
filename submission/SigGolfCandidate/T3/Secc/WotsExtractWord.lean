import SigGolfCandidate.T3.Secc.WotsExtractChain

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def dummyDigest0 : Digest := BitVec.ofNat 128 194407444155172597201995464558563070242
def dummyDigestLow : Digest := BitVec.ofNat 128 267364716866451649869350547003163471286
def dummyDigest (lay : Layer) : Digest := if lay.val = 0 then dummyDigest0 else dummyDigestLow
theorem dummyDigest_decode (lay : Layer) : decode lay (dummyDigest lay) = some (dummyDigits lay) := by
  fin_cases lay
  · show decode 0 dummyDigest0 = some (dummyDigits 0)
    decide +kernel
  · show decode 1 dummyDigestLow = some (dummyDigits 1)
    decide +kernel
  · show decode 2 dummyDigestLow = some (dummyDigits 2)
    decide +kernel
  · show decode 3 dummyDigestLow = some (dummyDigits 3)
    decide +kernel
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.WotsExtract
theorem dummyDigits_valid (lay : Layer) : ∃ value : Digest, decode lay value = some (dummyDigits lay) :=
  ⟨dummyDigest lay, dummyDigest_decode lay⟩
theorem word_cases {lay : Layer} {refDigest candDigest : Digest} {refDigits candDigits : List Nat}
    (hr : decode lay refDigest = some refDigits) (hc : decode lay candDigest = some candDigits) :
    candDigits = refDigits ∨
      (∃ i, MixedCode.UnitNeighborAt (decodedWord hr) (decodedWord hc) i) ∨
      (∃ i, (decodedWord hc i).val + 2 ≤ (decodedWord hr i).val) ∨
      (∃ i j, i ≠ j ∧ (decodedWord hc i).val < (decodedWord hr i).val ∧
        (decodedWord hc j).val < (decodedWord hr j).val) := by
  by_cases he : candDigits = refDigits
  · exact Or.inl he
  right
  have hne : decodedWord hc ≠ decodedWord hr := by
    intro hw
    apply he
    rw [← decodedWord_list hc, ← decodedWord_list hr, hw]
  rcases MixedCode.backwardWork_trichotomy (decodedWord_valid hr) (decodedWord_valid hc) with h | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · exact Or.inr (MixedCode.two_backward_steps h)
end SigGolfCandidate.T3.Security.Wots
namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def routeLeaf (index : Nat) (lay : Layer) : LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩
theorem route_split (index b h : Nat) : index / 2 ^ (b + h) * 2 ^ h + index / 2 ^ b % 2 ^ h = index / 2 ^ b := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' (index / 2 ^ b) (2 ^ h)
theorem route_tree_succ (index : Nat) (lay : Layer) (h : lay.val < 3) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = (route index ⟨lay.val + 1, by omega⟩).2 := by
  fin_cases lay
  · show index / 2 ^ (19 + 12) * 2 ^ 12 + index / 2 ^ 19 % 2 ^ 12 = index / 2 ^ 19
    exact route_split index 19 12
  · show index / 2 ^ (12 + 7) * 2 ^ 7 + index / 2 ^ 12 % 2 ^ 7 = index / 2 ^ 12
    exact route_split index 12 7
  · show index / 2 ^ (6 + 6) * 2 ^ 6 + index / 2 ^ 6 % 2 ^ 6 = index / 2 ^ 6
    exact route_split index 6 6
  · exact absurd h (by decide)
theorem route_forest (index : Nat) (lay : Layer) (h : ¬lay.val < 3) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = index := by
  fin_cases lay
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · show index / 2 ^ (0 + 6) * 2 ^ 6 + index / 2 ^ 0 % 2 ^ 6 = index
    have := route_split index 0 6
    simpa using this
theorem routeLeaf_source (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) :
    (routeLeaf index lay).tree < 2 ^ 31 ∧ (routeLeaf index lay).leaf < 2 ^ height (routeLeaf index lay).lay :=
  ⟨lt_of_le_of_lt (Nat.div_le_self _ _) hidx, route_leaf_bound index lay⟩
end SigGolfCandidate.T3.Security.WotsExtract
