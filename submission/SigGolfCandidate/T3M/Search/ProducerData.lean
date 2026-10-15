import SigGolfCandidate.T3M.Images.Sizes
import SigGolfCandidate.T3M.Search.TopTables

namespace SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Images
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
private theorem sign_table_check : (List.range 628).all (fun i => decide (signLegacyData.getD i 0 = tableByte i)) = true := by
  decide +kernel
private theorem expand_table_check : (List.range 628).all (fun i => decide (expandLegacyData.getD i 0 = tableByte i)) = true := by
  decide +kernel
theorem signLegacyData_table (i : Nat) (hi : i < 628) : signLegacyData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp sign_table_check) i (List.mem_range.mpr hi)
theorem expandLegacyData_table (i : Nat) (hi : i < 628) : expandLegacyData.getD i 0 = tableByte i := by
  simpa using (List.all_eq_true.mp expand_table_check) i (List.mem_range.mpr hi)
private theorem sign_cf_check : (List.range 20).all (fun j => decide (signLegacyData.getD (628 + j) 0 = cfByte 1 (628 + j))) = true := by
  decide +kernel
private theorem expand_cf_check : (List.range 20).all (fun j => decide (expandLegacyData.getD (628 + j) 0 = cfByte 0 (628 + j))) = true := by
  decide +kernel
theorem signLegacyData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) : signLegacyData.getD i 0 = cfByte 1 i := by
  have h := (List.all_eq_true.mp sign_cf_check) (i - 628) (List.mem_range.mpr (by omega))
  simpa [show 628 + (i - 628) = i by omega] using h
theorem expandLegacyData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) : expandLegacyData.getD i 0 = cfByte 0 i := by
  have h := (List.all_eq_true.mp expand_cf_check) (i - 628) (List.mem_range.mpr (by omega))
  simpa [show 628 + (i - 628) = i by omega] using h
theorem signLegacyData_length : signLegacyData.length = 4096 := by decide +kernel
theorem expandLegacyData_length : expandLegacyData.length = 4096 := by decide +kernel
theorem getD_prefixed (pre tail : List (BitVec 8)) (n i : Nat)
    (hp : pre.length = n) :
    (pre ++ tail).getD (n + i) 0 = tail.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
  rfl
theorem signData_length : signData.length = 86016 := Images.signData_length
theorem signData_table (i : Nat) (hi : i < 628) :
    signData.getD (81920 + i) 0 = tableByte i := by
  rw [signData, getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_table i hi
theorem signData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) :
    signData.getD (81920 + i) 0 = cfByte 1 i := by
  rw [signData, getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_cf i hi hj
theorem expandData_length : expandData.length = 27648 := Images.expandData_length
theorem expandData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) :
    expandData.getD (23552 + i) 0 = cfByte 0 i := by
  rw [expandData, getD_prefixed _ _ _ _ expandPrefixData_length]; exact expandLegacyData_cf i hi hj
theorem expandData_table (i : Nat) (hi : i < 628) :
    expandData.getD (23552 + i) 0 = tableByte i := by
  rw [expandData, getD_prefixed _ _ _ _ expandPrefixData_length]; exact expandLegacyData_table i hi
end SigGolfCandidate.T3M.Search
