import SigGolfCandidate.T3M_Search_RewardBlocks
import SigGolfCandidate.T3M_Images_Sizes
import SigGolfCandidate.T3M_Search_TopTables
import SigGolfCandidate.T3M_Search_ZeroCap
set_option Elab.async false

namespace SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Images
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Check a byte slice once, then recover its indexed specification without repeated list traversal. -/
private theorem getD_slice_of_eq (xs : List (BitVec 8)) (start count : Nat)
    (f : Nat → BitVec 8)
    (h : (xs.drop start).take count = List.ofFn (fun i : Fin count => f (start + i.val)))
    (i : Nat) (hi : i < count) : xs.getD (start + i) 0 = f (start + i) := by
  have he := congrArg (fun ys : List (BitVec 8) => ys[i]?) h
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_ofFn, dif_pos hi] at he
  rw [List.getD_eq_getElem?_getD, he]
  rfl

-- Keep the zero offset explicit so elaboration matches the slice lemma without normalizing the table.
private theorem sign_table_check : (signLegacyData.drop 0).take 628 =
    List.ofFn (fun i : Fin 628 => tableByte (0 + i.val)) := by
  decide +kernel
private theorem expand_table_check : (expandLegacyData.drop 0).take 628 =
    List.ofFn (fun i : Fin 628 => tableByte (0 + i.val)) := by
  decide +kernel
theorem signLegacyData_table (i : Nat) (hi : i < 628) : signLegacyData.getD i 0 = tableByte i := by
  simpa only [Nat.zero_add] using getD_slice_of_eq signLegacyData 0 628 tableByte sign_table_check i hi
theorem expandLegacyData_table (i : Nat) (hi : i < 628) : expandLegacyData.getD i 0 = tableByte i := by
  simpa only [Nat.zero_add] using getD_slice_of_eq expandLegacyData 0 628 tableByte expand_table_check i hi
private theorem sign_cf_check : (signLegacyData.drop 628).take 20 =
    List.ofFn (fun j : Fin 20 => cfByte 1 (628 + j.val)) := by
  decide +kernel
private theorem expand_cf_check : (expandLegacyData.drop 628).take 20 =
    List.ofFn (fun j : Fin 20 => cfByte 0 (628 + j.val)) := by
  decide +kernel
theorem signLegacyData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) : signLegacyData.getD i 0 = cfByte 1 i := by
  have h := getD_slice_of_eq signLegacyData 628 20 (cfByte 1) sign_cf_check (i-628) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem expandLegacyData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) : expandLegacyData.getD i 0 = cfByte 0 i := by
  have h := getD_slice_of_eq expandLegacyData 628 20 (cfByte 0) expand_cf_check (i-628) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem signLegacyData_length : signLegacyData.length = 4096 := by decide +kernel
theorem expandLegacyData_length : expandLegacyData.length = 4096 := by decide +kernel
theorem getD_prefixed (pre tail : List (BitVec 8)) (n i : Nat)
    (hp : pre.length = n) :
    (pre ++ tail).getD (n + i) 0 = tail.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
  rfl
theorem signData_length : signData.length = 86144 := Images.signData_length
theorem signZtData_length : signZtData.length = 128 := by decide +kernel
theorem signData_table (i : Nat) (hi : i < 628) :
    signData.getD (82048 + i) 0 = tableByte i := by
  rw [signData, show 82048 + i = 128 + (81920 + i) by omega, getD_prefixed _ _ _ _ signZtData_length,
    getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_table i hi
theorem signData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) :
    signData.getD (82048 + i) 0 = cfByte 1 i := by
  rw [signData, show 82048 + i = 128 + (81920 + i) by omega, getD_prefixed _ _ _ _ signZtData_length,
    getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_cf i hi hj
private theorem zt_check : ∀ r : Fin 128, signZtData.getD r.val 0 = ZeroCap.ztByte r.val := by decide +kernel
/-- The zero-count table at the start of the sign data. -/
theorem signData_zt (r : Nat) (hr : r < 128) : signData.getD r 0 = ZeroCap.ztByte r := by
  rw [signData, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [signZtData_length]; exact hr),
    ← List.getD_eq_getElem?_getD]
  exact zt_check ⟨r, hr⟩
theorem expandData_length : expandData.length = 29936 := Images.expandData_length
theorem expandZtData_length : expandZtData.length = 128 := by decide +kernel
theorem expandData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) :
    expandData.getD (25840 + i) 0 = cfByte 0 i := by
  rw [expandData, List.append_assoc, show 25840 + i = 128 + (2160 + (23552 + i)) from by omega,
    getD_prefixed _ _ _ _ expandZtData_length, getD_prefixed _ _ _ _ expandSharedData_length, getD_prefixed _ _ _ _ expandPrefixData_length]
  exact expandLegacyData_cf i hi hj
theorem expandData_table (i : Nat) (hi : i < 628) :
    expandData.getD (25840 + i) 0 = tableByte i := by
  rw [expandData, List.append_assoc, show 25840 + i = 128 + (2160 + (23552 + i)) from by omega,
    getD_prefixed _ _ _ _ expandZtData_length, getD_prefixed _ _ _ _ expandSharedData_length, getD_prefixed _ _ _ _ expandPrefixData_length]
  exact expandLegacyData_table i hi

private theorem sign_reward_check :
    (signLegacyData.drop 1024).take 1920 =
      List.ofFn (fun j : Fin 1920 => Reward.rewardTableByte (1024 + j.val)) := by
  decide +kernel
private theorem expand_reward_check :
    (expandLegacyData.drop 1024).take 1920 =
      List.ofFn (fun j : Fin 1920 => Reward.rewardTableByte (1024 + j.val)) := by
  decide +kernel
theorem signLegacyData_reward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2944) :
    signLegacyData.getD i 0 = Reward.rewardTableByte i := by
  have h := getD_slice_of_eq signLegacyData 1024 1920 Reward.rewardTableByte sign_reward_check
    (i-1024) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem expandLegacyData_reward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2944) :
    expandLegacyData.getD i 0 = Reward.rewardTableByte i := by
  have h := getD_slice_of_eq expandLegacyData 1024 1920 Reward.rewardTableByte expand_reward_check
    (i-1024) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem signData_reward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2944) :
    signData.getD (82048+i) 0 = Reward.rewardTableByte i := by
  rw [signData, show 82048 + i = 128 + (81920 + i) by omega, getD_prefixed _ _ _ _ signZtData_length,
    getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_reward i hi hj
theorem expandData_reward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2944) :
    expandData.getD (25840 + i) 0 = Reward.rewardTableByte i := by
  rw [expandData, List.append_assoc, show 25840 + i = 128 + (2160 + (23552 + i)) from by omega,
    getD_prefixed _ _ _ _ expandZtData_length, getD_prefixed _ _ _ _ expandSharedData_length, getD_prefixed _ _ _ _ expandPrefixData_length]
  exact expandLegacyData_reward i hi hj

end SigGolfCandidate.T3M.Search
