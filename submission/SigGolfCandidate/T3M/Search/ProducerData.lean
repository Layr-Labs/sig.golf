import SigGolfCandidate.T3M.Search.RewardBlocks
import SigGolfCandidate.T3M.Images.Sizes
import SigGolfCandidate.T3M.Search.TopTables

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

/-- R6 expand image (EXP): TOP_DATA + 0..1023 holds the first 1024 bytes of the packed R6 table block. -/
private theorem expand_r6a_check : (expandLegacyData.drop 0).take 1024 =
    List.ofFn (fun i : Fin 1024 => r6TableByte (0 + i.val)) := by
  decide +kernel
theorem expandLegacyData_r6tableA (i : Nat) (hi : i < 1024) : expandLegacyData.getD i 0 = r6TableByte i := by
  simpa only [Nat.zero_add] using getD_slice_of_eq expandLegacyData 0 1024 r6TableByte expand_r6a_check i hi
private theorem sign_cf_check : (signLegacyData.drop 628).take 20 =
    List.ofFn (fun j : Fin 20 => cfByteR6 1 (628 + j.val)) := by
  decide +kernel
theorem signLegacyData_cfR6 (i : Nat) (hi : 628 ≤ i) (hj : i < 648) : signLegacyData.getD i 0 = cfByteR6 1 i := by
  have h := getD_slice_of_eq signLegacyData 628 20 (cfByteR6 1) sign_cf_check (i-628) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem signLegacyData_length : signLegacyData.length = 4096 := by decide +kernel
theorem expandLegacyData_length : expandLegacyData.length = 4096 := by decide +kernel
theorem getD_prefixed (pre tail : List (BitVec 8)) (n i : Nat)
    (hp : pre.length = n) :
    (pre ++ tail).getD (n + i) 0 = tail.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
  rfl
theorem signData_length : signData.length = 86016 := Images.signData_length
theorem expandData_length : expandData.length = 29808 := Images.expandData_length

/-- R6 sign image: only the lower reward tables (TOP_DATA + 1024..2047) stay; 2048..3743 is the R6 block. -/
private theorem sign_reward_check :
    (signLegacyData.drop 1024).take 1024 =
      List.ofFn (fun j : Fin 1024 => Reward.rewardTableByte (1024 + j.val)) := by
  decide +kernel
private theorem sign_r6table_check :
    (signLegacyData.drop 2048).take 1696 =
      List.ofFn (fun j : Fin 1696 => (fun i => r6TableByte (i - 2048)) (2048 + j.val)) := by
  decide +kernel
/-- R6 expand image (EXP): lower reward tables at 1024..2047, R6 block bytes 1024..1695 at 2048..2719, main's
tail table at 2720..2943. -/
private theorem expand_lower_check :
    (expandLegacyData.drop 1024).take 1024 =
      List.ofFn (fun j : Fin 1024 => Reward.rewardTableByte (1024 + j.val)) := by
  decide +kernel
private theorem expand_r6b_check :
    (expandLegacyData.drop 2048).take 672 =
      List.ofFn (fun j : Fin 672 => (fun i => r6TableByte (i - 1024)) (2048 + j.val)) := by
  decide +kernel
theorem signLegacyData_lowerReward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2048) :
    signLegacyData.getD i 0 = Reward.rewardTableByte i := by
  have h := getD_slice_of_eq signLegacyData 1024 1024 Reward.rewardTableByte sign_reward_check
    (i-1024) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem signLegacyData_r6table (i : Nat) (hi : i < 1696) :
    signLegacyData.getD (2048 + i) 0 = r6TableByte i := by
  have h := getD_slice_of_eq signLegacyData 2048 1696 (fun i => r6TableByte (i - 2048)) sign_r6table_check i hi
  simpa only [Nat.add_sub_cancel_left] using h
theorem expandLegacyData_lowerReward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2048) :
    expandLegacyData.getD i 0 = Reward.rewardTableByte i := by
  have h := getD_slice_of_eq expandLegacyData 1024 1024 Reward.rewardTableByte expand_lower_check
    (i-1024) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem expandLegacyData_r6tableB (i : Nat) (hi : 1024 ≤ i) (hj : i < 1696) :
    expandLegacyData.getD (1024 + i) 0 = r6TableByte i := by
  have h := getD_slice_of_eq expandLegacyData 2048 672 (fun i => r6TableByte (i - 1024)) expand_r6b_check
    (i-1024) (by omega)
  rw [show 2048 + (i - 1024) = 1024 + i by omega] at h
  simpa only [Nat.add_sub_cancel_left] using h

theorem signData_cfR6 (i : Nat) (hi : 628 ≤ i) (hj : i < 648) :
    signData.getD (81920 + i) 0 = cfByteR6 1 i := by
  rw [signData, getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_cfR6 i hi hj
theorem signData_lowerReward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2048) :
    signData.getD (81920+i) 0 = Reward.rewardTableByte i := by
  rw [signData, getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_lowerReward i hi hj
/-- R6 sign image: the choice flag byte (TOP_DATA + 631) of the initial data is 1 (`CfFlagOK 1` at `sinit`). -/
theorem signData_flag : signData.getD (81920 + 631) 0 = BitVec.ofNat 8 1 := by
  rw [signData_cfR6 631 (by omega) (by omega)]; unfold cfByteR6; rw [if_pos rfl]
theorem signData_r6table (i : Nat) (hi : i < 1696) :
    signData.getD (81920 + 2048 + i) 0 = r6TableByte i := by
  rw [signData, Nat.add_assoc, getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_r6table i hi

end SigGolfCandidate.T3M.Search
