import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Final
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.WitV5

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer height chainCount LayerSignature route readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap window_flatMap_const
  window_full window_zeros window_take zeros wordsOf layerBytes layerBytes_length layerBytes_merkle layerBytes_chain)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (witList headerBytes wctBytes regionBytes layerRegion tailBytes lowerPathBytes headerBytes_length
  regionBytes_length witList_length_eq win_header win_region win_layerRegion win_tail regionLen regionTake_length
  wct_prefix wctBytes_length layers_length tailBytes_length)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 layerRegionV6 layerBytesBCV6 bcTopBlockV6 wctBytesV6_length
  witListV6_length layerRegionV6_length layersV6_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
theorem window_window' (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
section
variable (N : HashOutput) (w : WCT9.Witness)
theorem v6_head (o : Nat) (h : o + 8 ≤ 64) : window (witListV6 N w) o 8 = window (headerBytes w) o 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_left _ _ _ _ (by rw [headerBytes_length]; omega)]
theorem v6_region (k : Nat) (hk : k < 9) (j : Nat) (hj : j + 8 ≤ 832) :
    window (witListV6 N w) (64 + 896 * k + j) 8 =
      window (regionBytes (WCT9.child N ⟨k, hk⟩).val (w.signature.openings ⟨k, hk⟩)) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right (headerBytes w) _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    window_append_left _ _ _ _ (by rw [wctBytesV6_length]; omega),
    show 64 + 896 * k + j - 64 = 896 * k + j by omega]
  unfold wctBytesV6
  rw [window_flatMap_const _ _ 896 (fun k => ClaudeWCT.W9.Machine.Expand.regionBytesV6_length _ _) k (by simp; omega)
    j 8 (by omega)]
  simp only [List.getElem_finRange, Fin.cast_mk, ClaudeWCT.W9.Machine.Expand.regionBytesV6]
  rw [window_append_left _ _ _ _ (by rw [regionBytes_length]; omega)]
def layOffV6 (lay : Layer) : Nat := (![0, 4224, 7424, 10560] : Layer → Nat) lay
theorem v6_layer (lay : Layer) (j : Nat) (hj : j + 8 ≤ 64 * (height lay + chainCount lay)) :
    window (witListV6 N w) (8136 + layOffV6 lay + j) 8 = window (layerRegionV6 N w lay) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right (headerBytes w) _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    window_append_right (wctBytesV6 N w.signature) _ _ _ (by rw [wctBytesV6_length]; omega), wctBytesV6_length,
    window_append_right (zeros 8) _ _ _ (by simp [zeros]; omega), show (zeros 8).length = 8 by simp [zeros]]
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := window_flatMap (List.finRange 4) (layerRegionV6 N w) lay.val (by simp) j 8
    (by rw [hlen, layerRegionV6_length]; omega)
  have hpre : (((List.finRange 4).take lay.val).map fun l => (layerRegionV6 N w l).length).sum = layOffV6 lay := by
    simp only [layerRegionV6_length]
    fin_cases lay <;> decide
  rw [hpre, hlen] at key
  rw [show 8136 + layOffV6 lay + j - 64 - 8064 - 8 = layOffV6 lay + j by omega, key]
theorem win_region0 (o : Nat) (h : o + 8 ≤ 832) :
    window (witList N w) (64 + 816 * 8 + o) 8 =
      window (regionBytes (WCT9.child N 0).val (w.signature.openings 0)) o 8 := by
  rw [ClaudeWCT.W9.T3M.witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    show 64 + 816 * 8 + o - 64 = 816 * (8 - (0 : WCT9.Coord).val) + o by simp; omega]
  have hidx : ((List.finRange 9).reverse[8 - (0 : WCT9.Coord).val]'(by simp)) = 0 := by decide
  have key := window_flatMap (List.finRange 9).reverse (fun k => (regionBytes (WCT9.child N k).val
      (w.signature.openings k)).take (if k.val = 0 then 832 else 816)) (8 - (0 : WCT9.Coord).val) (by simp) o 8
    (by rw [hidx, regionTake_length]; unfold regionLen; simp; omega)
  rw [show (((List.finRange 9).reverse.take (8 - (0 : WCT9.Coord).val)).map fun b => ((regionBytes (WCT9.child N b).val
      (w.signature.openings b)).take (if b.val = 0 then 832 else 816)).length) =
      (((List.finRange 9).reverse.take (8 - (0 : WCT9.Coord).val)).map regionLen) from
      List.map_congr_left (fun b _ => regionTake_length b _ _), wct_prefix, hidx] at key
  unfold wctBytes
  rw [key, window_take _ _ _ _ (by simp; omega)]
end
section lower
variable {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32)
def canon (j : Fin (height lay)) (d : Nat) : List UInt8 :=
  if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) then window (bytesLE 16 (ls.path j)) 0 8
  else if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 then window (bytesLE 16 (ls.path j)) 8 8
  else if d = 32 ∧ j.val = height lay - 1 then bytesLE 4 ctr ++ zeros 4
  else zeros 8
theorem sibOff_vals (b : Nat) : SigGolfCandidate.T3M.sibOff b = 0 ∨ SigGolfCandidate.T3M.sibOff b = 48 := by
  unfold SigGolfCandidate.T3M.sibOff; split <;> simp
theorem win8_of_16 (L : List UInt8) (x a : Nat) (ha : a + 8 ≤ 16) :
    window L (x + a) 8 = window (window L x 16) a 8 := (window_window' L x 16 a 8 ha).symm
theorem block_win (P : List UInt8) (hP : P.length = 16) (b : Bool) (d : Nat) (hd : d % 8 = 0) (hd' : d + 8 ≤ 64) :
    window (if b then P ++ zeros 48 else zeros 48 ++ P) d 8 =
      if d = (if b then 0 else 48) then window P 0 8 else if d = (if b then 0 else 48) + 8 then window P 8 8
      else zeros 8 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    by_cases h48 : 48 ≤ d
    · rw [window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 48).length = 48 by simp [zeros]]
      rcases (show d = 48 ∨ d = 56 by omega) with rfl | rfl
      · simp
      · simp
    · rw [window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega),
        if_neg (by omega), if_neg (by omega)]
  · simp only [if_true]
    by_cases h16 : d < 16
    · rw [window_append_left _ _ _ _ (by rw [hP]; omega)]
      rcases (show d = 0 ∨ d = 8 by omega) with rfl | rfl
      · simp
      · simp
    · rw [window_append_right _ _ _ _ (by rw [hP]; omega), hP, window_zeros _ _ _ (by omega),
        if_neg (by omega), if_neg (by omega)]
end lower
section lowerAB
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
theorem window_drop (L : List UInt8) (k x n : Nat) : window (L.drop k) x n = window L (k + x) n := by
  unfold window; rw [List.drop_drop]
theorem bytesLE16_len (x : SigGolfCandidate.T3.Digest) : (bytesLE 16 x).length = 16 := bytesLE_length _ _
include hlay in
theorem v6_block (j : Fin (height lay)) (d : Nat) (hd : d % 8 = 0) (hd' : d + 8 ≤ 64)
    (hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) ∨
      d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 ∨ d = 32 ∨ d = 40) :
    window (layerBytesBCV6 lay leaf ls ctr) (64 * (height lay - 1 - j.val) + d) 8 = canon leaf ls ctr j d := by
  have hj := j.isLt
  have hs := sibOff_vals (leaf / 2 ^ j.val % 2)
  unfold layerBytesBCV6
  by_cases htop : j.val = height lay - 1
  · rw [show 64 * (height lay - 1 - j.val) + d = d by rw [htop]; simp,
      window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega)]
    have hT : WCT9.topLevel lay = j := Fin.ext (by unfold WCT9.topLevel; simp [htop])
    unfold bcTopBlockV6 canon
    rw [hT, ← htop]
    unfold SigGolfCandidate.T3M.sibOff at hdv ⊢
    split
    · rename_i hb
      simp only [hb, if_true] at hdv ⊢
      rcases hdv with rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length])]
      · simp only [show (0 : Nat) + 8 = 8 from rfl, show (8 : Nat) ≠ 0 by decide, if_true, if_false]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length])]
      · simp only [show (32 : Nat) ≠ 0 by decide, show (32 : Nat) ≠ 0 + 8 by decide, if_false, true_and, if_true]
        rw [show bytesLE 16 (ls.path j) ++ zeros 16 ++ bytesLE 4 ctr ++ zeros 28 =
          (bytesLE 16 (ls.path j) ++ zeros 16) ++ (bytesLE 4 ctr ++ zeros 28) by simp [List.append_assoc],
          window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 32 - (bytesLE 16 (ls.path j) ++ zeros 16).length = 0 by simp [zeros, bytesLE_length]]
        unfold window
        simp only [List.drop_zero, List.append_assoc]
        rw [show 8 = (bytesLE 4 ctr).length + 4 by rw [bytesLE_length], List.take_append]
        simp [zeros]
      · simp only [show (40 : Nat) ≠ 0 by decide, show (40 : Nat) ≠ 0 + 8 by decide, if_false,
          show (40 : Nat) ≠ 32 by decide, false_and]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 40 - (bytesLE 16 (ls.path j) ++ zeros 16 ++ bytesLE 4 ctr).length = 4 by simp [zeros, bytesLE_length],
          window_zeros _ _ _ (by omega)]
    · rename_i hb
      simp only [hb, if_false] at hdv ⊢
      rcases hdv with rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 48 - (zeros 32 ++ bytesLE 4 ctr ++ zeros 12).length = 0 by simp [zeros, bytesLE_length]]
      · simp only [show (48 : Nat) + 8 ≠ 48 by decide, if_true, if_false]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 48 + 8 - (zeros 32 ++ bytesLE 4 ctr ++ zeros 12).length = 8 by simp [zeros, bytesLE_length]]
      · simp only [show (32 : Nat) ≠ 48 by decide, show (32 : Nat) ≠ 48 + 8 by decide, if_false, true_and, if_true]
        rw [show zeros 32 ++ bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path j) =
          zeros 32 ++ (bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path j)) by simp [List.append_assoc],
          window_append_right _ _ _ _ (by simp [zeros]), show 32 - (zeros 32).length = 0 by simp [zeros]]
        unfold window
        simp only [List.drop_zero, List.append_assoc]
        rw [show 8 = (bytesLE 4 ctr).length + 4 by rw [bytesLE_length], List.take_append]
        simp [zeros]
      · simp only [show (40 : Nat) ≠ 48 by decide, show (40 : Nat) ≠ 48 + 8 by decide, if_false,
          show (40 : Nat) ≠ 32 by decide, false_and]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 40 - (zeros 32 ++ bytesLE 4 ctr).length = 4 by simp [zeros, bytesLE_length],
          window_zeros _ _ _ (by omega)]
  · have hjl : j.val + 1 < height lay := by omega
    rw [window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega),
      ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length, window_drop,
      show 64 + (64 * (height lay - 1 - j.val) + d - 64) = 64 * (height lay - 1 - j.val) + (d - d % 16) + d % 16 by
        omega,
      win8_of_16 _ _ _ (by omega), layerBytes_merkle lay leaf ls j (d - d % 16) (by omega),
      window_window' _ _ _ _ _ (by omega), show d - d % 16 + d % 16 = d by omega]
    have hbk := block_win (bytesLE 16 (ls.path j)) (bytesLE_length _ _) (decide (leaf / 2 ^ j.val % 2 = 1)) d hd hd'
    simp only [decide_eq_true_eq] at hbk
    rw [hbk]
    unfold canon SigGolfCandidate.T3M.sibOff
    by_cases hb : leaf / 2 ^ j.val % 2 = 1
    · simp only [hb, if_true]
      rw [if_neg (show ¬ (d = 32 ∧ j.val = height lay - 1) by omega)]
    · simp only [hb, if_false]
      rw [if_neg (show ¬ (d = 32 ∧ j.val = height lay - 1) by omega)]
end lowerAB
section lowerBC
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
theorem window_split (L : List UInt8) (o a b : Nat) :
    window L o (a + b) = window L o a ++ window L (o + a) b := by
  unfold window
  rw [List.take_add, List.drop_drop]
include hlay hleaf
theorem v7_block (j : Fin (height lay)) (d : Nat) (hd' : d + 8 ≤ 64)
    (hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) ∨
      d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 ∨ d = 32 ∨ d = 40) :
    window (lowerPathBytes lay leaf ls ctr) (16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + d) 8 =
      canon leaf ls ctr j d := by
  have hj := j.isLt
  have hs := sibOff_vals (leaf / 2 ^ j.val % 2)
  have hsib := ClaudeWCT.W9.T3M.lowerPath_sib hlay hleaf ls ctr j
  unfold ClaudeWCT.W9.T3M.lowerSibSlot at hsib
  unfold canon
  rcases hdv with h | h | h | h
  · subst h
    rw [if_pos rfl, show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) = 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 0 from rfl, win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_pos rfl, show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 +
      (SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8) = 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 by omega, win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases htop : j.val = height lay - 1
    · rw [if_pos ⟨rfl, htop⟩]
      have hc := ClaudeWCT.W9.T3M.lowerPath_ctr hlay hleaf ls ctr
      have hr := ClaudeWCT.W9.T3M.lowerPath_rowPad hlay hleaf ls ctr
      unfold ClaudeWCT.W9.T3M.lowerCtrSlot at hc hr
      rw [← htop] at hc hr
      rw [show (8 : Nat) = 4 + 4 from rfl, window_split, hc,
        show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 4 =
          16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 0 from rfl,
        ← window_window' _ _ 12 0 4 (by omega), hr, window_zeros _ _ _ (by omega)]
    · rw [if_neg (by omega)]
      have hp := ClaudeWCT.W9.T3M.lowerPath_pad hlay hleaf ls ctr (j := j.val) (by omega)
      rw [show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 =
        16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 0 from rfl, win8_of_16 _ _ _ (by omega), hp,
        window_zeros _ _ _ (by omega)]
  · subst h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    by_cases htop : j.val = height lay - 1
    · have hr := ClaudeWCT.W9.T3M.lowerPath_rowPad hlay hleaf ls ctr
      unfold ClaudeWCT.W9.T3M.lowerCtrSlot at hr
      rw [← htop] at hr
      rw [show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 40 =
          16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 4 by omega,
        ← window_window' _ _ 12 4 8 (by omega), hr, window_zeros _ _ _ (by omega)]
    · have hp := ClaudeWCT.W9.T3M.lowerPath_pad hlay hleaf ls ctr (j := j.val) (by omega)
      rw [show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 40 =
        16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 8 by omega, win8_of_16 _ _ _ (by omega), hp,
        window_zeros _ _ _ (by omega)]
end lowerBC
section lowerC
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
include hlay hleaf
theorem v7_free (p : Nat) (hp8 : p % 8 = 0) (hp' : p + 8 ≤ 16 * ClaudeWCT.W9.T3M.pathSlots lay)
    (hnot : ∀ j : Fin (height lay), p ≠ ClaudeWCT.W9.T3M.lowerSibSlot lay leaf j.val ∧
      p ≠ ClaudeWCT.W9.T3M.lowerSibSlot lay leaf j.val + 8 ∧
      p ≠ 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 ∧
      p ≠ 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 40) :
    window (lowerPathBytes lay leaf ls ctr) p 8 = zeros 8 := by
  have hsl : ∀ j : Fin (height lay), ClaudeWCT.W9.T3M.lowerSibSlot lay leaf j.val % 16 = 0 := fun j => by
    unfold ClaudeWCT.W9.T3M.lowerSibSlot
    rcases sibOff_vals (leaf / 2 ^ j.val % 2) with h | h <;> rw [h] <;> omega
  have hh : 1 ≤ height lay := ClaudeWCT.W9.T3M.height_pos' lay
  unfold lowerPathBytes
  rw [ClaudeWCT.W9.T3M.window_map_range _ _ _ _ hp']
  have hz : ∀ i ∈ List.range 8, ClaudeWCT.W9.T3M.lowerPathByte lay leaf ls ctr (p + i) = (fun _ => (0 : UInt8)) i := by
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [ClaudeWCT.W9.T3M.lowerPathByte_free ls ctr (fun j => by
      have := hnot j; have := hsl j; omega)]
    have hc := hnot ⟨height lay - 1, by omega⟩
    simp only at hc
    unfold ClaudeWCT.W9.T3M.lowerCtrSlot
    rw [if_neg (by omega)]
  rw [List.map_congr_left hz]
  simp [zeros, List.map_const']
end lowerC
theorem wordsOf_getD' (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [SigGolfCandidate.T3M.wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := SigGolfCandidate.T3M.readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
section ident
variable (N : HashOutput) (w : WCT9.Witness)
def v6M (B : Nat) : Word := (wordsOf (witListV6 N w)).getD ((B - WIT) / 8) 0
theorem v6M_eq (x : Nat) (hx : x % 8 = 0) (hx' : x + 8 ≤ 21832) :
    v6M N w (WIT + x) = BitVec.ofNat 64 (readLE (window (witListV6 N w) x 8)) := by
  unfold v6M
  rw [show (WIT + x - WIT) / 8 = x / 8 by omega, wordsOf_getD' _ 2729 (by rw [witListV6_length]) _ (by omega),
    show 8 * (x / 8) = x by omega]
theorem lroute_eq (lay : Layer) (hl : lay.val ≠ 0) (idx : Nat) :
    lroute lay.val idx = (route idx lay).1 := by
  unfold lroute route
  fin_cases lay <;> simp_all [height]
theorem plan_eq (lay : Layer) (r j : Nat) : plan lay.val r j = (ClaudeWCT.W9.T3M.lowerPlan lay r).getD j 0 := by
  unfold plan; congr 2; ext; simp [Nat.mod_eq_of_lt lay.isLt]
theorem lvSrc_eq (lay : Layer) (hl : lay.val ≠ 0) (j : Nat) (hj : j < height lay) :
    lvSrc lay.val j - SNAP2 = 8136 + layOffV6 lay + 64 * (height lay - 1 - j) := by
  unfold lvSrc SNAP2 layOffV6
  fin_cases lay <;> simp_all [height] <;> omega
theorem lvH_eq (lay : Layer) (hl : lay.val ≠ 0) : lvH lay.val = height lay := by
  unfold lvH; fin_cases lay <;> simp_all [height]
theorem lvDst_eq (lay : Layer) (hl : lay.val ≠ 0) : lvDst lay.val - WIT = ClaudeWCT.W9.T3M.layerBase lay ∧
    pathTop lay.val = 16 * ClaudeWCT.W9.T3M.pathSlots lay ∧
    chDst lay.val - WIT = ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay ∧
    chSrc lay.val - SNAP2 = 8136 + layOffV6 lay + 64 * height lay := by
  unfold chDst chSrc pathTop
  unfold lvDst WIT SNAP2 layOffV6 ClaudeWCT.W9.T3M.layerBase ClaudeWCT.W9.T3M.pathSlots
  fin_cases lay <;> simp_all [height]
end ident
theorem wu_small (X : Nat) (hX : X < 2 ^ 32) : LoadKind.wu.fromWord (BitVec.ofNat 64 X) 0 = BitVec.ofNat 64 X := by
  apply BitVec.eq_of_toNat_eq
  simp only [LoadKind.fromWord, extractWord32, Nat.zero_div, Nat.zero_mul, BitVec.ushiftRight_zero,
    BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : X < 2 ^ 64), Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt (by omega : X < 2 ^ 64)]
section ident2
variable (N : HashOutput) (w : WCT9.Witness)
theorem layerRegion_top : layerRegion N w 0 = layerRegionV6 N w 0 := by
  unfold layerRegion layerRegionV6; simp
theorem zone_low (L : Layer) (hL : L.val ≠ 0) (o : Nat) (h1 : ClaudeWCT.W9.T3M.layerBase L ≤ o)
    (h2 : o + 8 ≤ ClaudeWCT.W9.T3M.layerBase L + (16 * ClaudeWCT.W9.T3M.pathSlots L + 64 * chainCount L))
    (h8 : o % 8 = 0) :
    BitVec.ofNat 64 (readLE (window (witList N w) o 8)) =
      if o - ClaudeWCT.W9.T3M.layerBase L < 16 * ClaudeWCT.W9.T3M.pathSlots L then
        pathOut (v6M N w) L.val (lroute L.val (WCT9.digestIndex N)) (o - ClaudeWCT.W9.T3M.layerBase L)
      else v6M N w (8136 + layOffV6 L + 64 * height L + (o - ClaudeWCT.W9.T3M.layerBase L -
        16 * ClaudeWCT.W9.T3M.pathSlots L) + WIT) := by
  have hW : WIT = 0x800 := rfl
  set leaf := (route (WCT9.digestIndex N) L).1 with hleafdef
  have hleaf : leaf < 2 ^ height L := ClaudeWCT.W9.T3M.route_leaf_lt _ _
  have hps : 16 * ClaudeWCT.W9.T3M.pathSlots L ≤ 16 * 23 ∧ ClaudeWCT.W9.T3M.layerBase L % 16 = 0 ∧
      ClaudeWCT.W9.T3M.pathSlots L ≥ 19 := by
    fin_cases L <;> simp_all [ClaudeWCT.W9.T3M.pathSlots, ClaudeWCT.W9.T3M.layerBase]
  have hlo : 8136 + layOffV6 L + 64 * (height L + chainCount L) ≤ 21832 ∧ layOffV6 L % 64 = 0 := by
    fin_cases L <;> decide
  have hh1 := ClaudeWCT.W9.T3M.height_pos' L
  rw [show o = ClaudeWCT.W9.T3M.layerBase L + (o - ClaudeWCT.W9.T3M.layerBase L) by omega,
    win_layerRegion N w L _ 8 (by omega), Nat.add_sub_cancel_left]
  unfold layerRegion
  rw [if_neg hL]
  by_cases hp : o - ClaudeWCT.W9.T3M.layerBase L < 16 * ClaudeWCT.W9.T3M.pathSlots L
  · rw [if_pos hp, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.T3M.lowerPathBytes_length]; omega)]
    unfold pathOut
    rw [lroute_eq L hL, ← hleafdef]
    cases h : (List.range (lvH L.val)).find? (fun j => decide (lvHit L.val leaf j (o - ClaudeWCT.W9.T3M.layerBase L)))
      with
    | none =>
      simp only
      rw [v7_free hL hleaf _ _ _ (by omega) (by omega) (fun j => by
        have := List.find?_eq_none.mp h j.val (List.mem_range.mpr (by rw [lvH_eq L hL]; exact j.isLt))
        have h' : ¬ lvHit L.val leaf j.val (o - ClaudeWCT.W9.T3M.layerBase L) := fun hh => this (decide_eq_true hh)
        unfold lvHit sibS padS at h'
        rw [plan_eq] at h'
        unfold ClaudeWCT.W9.T3M.lowerSibSlot
        rw [sibOff_eq _ (Nat.mod_lt _ (by norm_num))]
        omega)]
      simp [zeros]; rfl
    | some j =>
      simp only
      obtain ⟨hj, hp'⟩ := lvs_find_some h
      rw [lvH_eq L hL] at hj
      have hh : lvHit L.val leaf j (o - ClaudeWCT.W9.T3M.layerBase L) := of_decide_eq_true hp'
      unfold lvHit sibS padS at hh
      rw [plan_eq] at hh
      set pj := (ClaudeWCT.W9.T3M.lowerPlan L leaf).getD j 0 with hpj
      have hb : leaf / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hsb := sibOff_eq (leaf / 2 ^ j % 2) hb
      have hpbnd := ClaudeWCT.W9.T3M.lower_pad_bound L hL leaf hleaf j hj
      have hsbnd := ClaudeWCT.W9.T3M.lower_sib_bound L hL leaf hleaf j hj
      unfold ClaudeWCT.W9.T3M.lowerSibSlot at hsbnd
      rw [sibOff_eq _ hb, ← hpj] at hsbnd
      rw [← hpj] at hpbnd
      set d := o - ClaudeWCT.W9.T3M.layerBase L - 16 * pj with hd
      have hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, hj⟩ : Fin (height L)).val % 2) ∨
          d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, hj⟩ : Fin (height L)).val % 2) + 8 ∨ d = 32 ∨ d = 40 := by
        simp only; rw [hsb]; omega
      have e7 := v7_block hL hleaf (w.signature.layers L) (w.counters (Fin.ofNat 4 (L.val - 1))) ⟨j, hj⟩ d
        (by omega) hdv
      have e6 := v6_block hL (leaf := leaf) (w.signature.layers L) (w.counters (Fin.ofNat 4 (L.val - 1))) ⟨j, hj⟩ d
        (by omega) (by omega) hdv
      simp only at e7 e6
      rw [plan_eq, ← hpj, show o - ClaudeWCT.W9.T3M.layerBase L = 16 * pj + d by omega, e7,
        show 16 * pj + d - 16 * pj = d by omega,
        show lvSrc L.val j - SNAP2 + WIT + d = WIT + (8136 + layOffV6 L + (64 * (height L - 1 - j) + d)) by
          rw [lvSrc_eq L hL j hj]; omega,
        v6M_eq N w _ (by omega) (by omega)]
      rw [show 8136 + layOffV6 L + (64 * (height L - 1 - j) + d) = 8136 + layOffV6 L + (64 * (height L - 1 - j) + d)
        from rfl, v6_layer N w L _ (by omega)]
      unfold layerRegionV6
      rw [if_neg hL, e6]
  · rw [if_neg hp, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.T3M.lowerPathBytes_length]; omega),
      ClaudeWCT.W9.T3M.lowerPathBytes_length, window_drop,
      show 8136 + layOffV6 L + 64 * height L + (o - ClaudeWCT.W9.T3M.layerBase L - 16 * ClaudeWCT.W9.T3M.pathSlots L) +
        WIT = WIT + (8136 + layOffV6 L + (64 * height L + (o - ClaudeWCT.W9.T3M.layerBase L -
          16 * ClaudeWCT.W9.T3M.pathSlots L))) by omega,
      v6M_eq N w _ (by omega) (by omega), v6_layer N w L _ (by omega)]
    unfold layerRegionV6 layerBytesBCV6
    rw [if_neg hL, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega),
      ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length, window_drop,
      show 64 + (64 * height L + (o - ClaudeWCT.W9.T3M.layerBase L - 16 * ClaudeWCT.W9.T3M.pathSlots L) - 64) =
        64 * height L + (o - ClaudeWCT.W9.T3M.layerBase L - 16 * ClaudeWCT.W9.T3M.pathSlots L) by omega]
end ident2
theorem compact2_words (N : HashOutput) (w : WCT9.Witness) (i : Nat) (hi : i < 2614) :
    (wordsOf (witList N w)).getD i 0 = out2 (v6M N w) (WCT9.digestIndex N) (8 * i) := by
  rw [wordsOf_getD' _ 2614 (by rw [witList_length_eq]) i hi]
  unfold out2
  by_cases h64 : 8 * i < 64
  · rw [if_pos h64, v6M_eq N w _ (by omega) (by omega), win_header N w _ _ (by omega), v6_head N w _ (by omega)]
  rw [if_neg h64]
  by_cases h8k : 8 * i < 7424
  · rw [if_pos h8k]
    by_cases hq : (8 * i - 64) / 816 < 8
    · have hm : min ((8 * i - 64) / 816) 8 = (8 * i - 64) / 816 := Nat.min_eq_left (by omega)
      rw [hm]
      have hw7 := win_region N w ⟨8 - (8 * i - 64) / 816, by omega⟩ ((8 * i - 64) % 816) 8 (by omega)
      have hw6 := v6_region N w (8 - (8 * i - 64) / 816) (by omega) ((8 * i - 64) % 816) (by omega)
      rw [show ClaudeWCT.W9.T3M.regionBase (8 - (8 * i - 64) / 816) + (8 * i - 64) % 816 = 8 * i by
        unfold ClaudeWCT.W9.T3M.regionBase; omega] at hw7
      rw [hw7, show WIT + 64 + 896 * (8 - (8 * i - 64) / 816) + (8 * i - 64 - 816 * ((8 * i - 64) / 816)) =
        WIT + (64 + 896 * (8 - (8 * i - 64) / 816) + (8 * i - 64) % 816) by omega,
        v6M_eq N w _ (by omega) (by omega), hw6]
    · have hm : min ((8 * i - 64) / 816) 8 = 8 := Nat.min_eq_right (by omega)
      rw [hm]
      have hw7 := win_region0 N w (8 * i - 64 - 816 * 8) (by omega)
      have hw6 := v6_region N w 0 (by omega) (8 * i - 64 - 816 * 8) (by omega)
      rw [show 64 + 816 * 8 + (8 * i - 64 - 816 * 8) = 8 * i by omega] at hw7
      rw [hw7, show WIT + 64 + 896 * (8 - 8) + (8 * i - 64 - 816 * 8) = WIT + (64 + 896 * 0 + (8 * i - 64 - 816 * 8))
        by omega, v6M_eq N w _ (by omega) (by omega), hw6]
      rfl
  rw [if_neg h8k]
  by_cases htop : 8 * i < 11648
  · rw [if_pos htop]
    have hw7 := win_layerRegion N w 0 (8 * i - 7424) 8 (by simp [ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
    have hw6 := v6_layer N w 0 (8 * i - 7424) (by simp [height, chainCount]; omega)
    rw [show ClaudeWCT.W9.T3M.layerBase 0 + (8 * i - 7424) = 8 * i by simp [ClaudeWCT.W9.T3M.layerBase]; omega]
      at hw7
    rw [hw7, layerRegion_top, show WIT + 8 * i + 712 = WIT + (8136 + layOffV6 0 + (8 * i - 7424)) by
      simp [layOffV6]; omega, v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6]; omega), hw6]
  rw [if_neg htop]
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  by_cases hlow : 8 * i < 20880
  · rw [if_pos hlow]
    have hW : WIT = 0x800 := rfl
    have key : ∀ L : Layer, L.val ≠ 0 → zoneLay (8 * i) = L.val → ClaudeWCT.W9.T3M.layerBase L ≤ 8 * i →
        8 * i + 8 ≤ ClaudeWCT.W9.T3M.layerBase L + (16 * ClaudeWCT.W9.T3M.pathSlots L + 64 * chainCount L) →
        BitVec.ofNat 64 (readLE (window (witList N w) (8 * i) 8)) =
          (if 8 * i - (lvDst (zoneLay (8 * i)) - WIT) < pathTop (zoneLay (8 * i)) then
            pathOut (v6M N w) (zoneLay (8 * i)) (lroute (zoneLay (8 * i)) (WCT9.digestIndex N))
              (8 * i - (lvDst (zoneLay (8 * i)) - WIT))
          else v6M N w (chSrc (zoneLay (8 * i)) - SNAP2 + WIT + (8 * i - (chDst (zoneLay (8 * i)) - WIT)))) := by
      intro L hL hz h1 h2
      obtain ⟨e1, e2, e3, e4⟩ := lvDst_eq L hL
      rw [hz, e1, e2, e3, e4, zone_low N w L hL (8 * i) h1 h2 (by omega)]
      by_cases hc : 8 * i - ClaudeWCT.W9.T3M.layerBase L < 16 * ClaudeWCT.W9.T3M.pathSlots L
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, show 8136 + layOffV6 L + 64 * height L + (8 * i - ClaudeWCT.W9.T3M.layerBase L -
          16 * ClaudeWCT.W9.T3M.pathSlots L) + WIT = 8136 + layOffV6 L + 64 * height L + WIT +
          (8 * i - (ClaudeWCT.W9.T3M.layerBase L + 16 * ClaudeWCT.W9.T3M.pathSlots L)) by omega]
    by_cases hz1 : 8 * i < 14768
    · exact key 1 (by decide) (by unfold zoneLay; rw [if_pos hz1]; rfl) (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
        (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
    · by_cases hz2 : 8 * i < 17824
      · exact key 2 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_pos hz2]; rfl)
          (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
          (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
      · exact key 3 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_neg hz2]; rfl)
          (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
          (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
  · rw [if_neg hlow]
    have hrho : ∀ t, t + 8 ≤ 16 → window (witList N w) (20880 + t) 8 = window (witListV6 N w) t 8 := fun t ht => by
      rw [win_tail N w _ _ (by omega), v6_head N w _ (by omega)]
      unfold tailBytes headerBytes
      simp only [List.append_assoc]
      rw [window_append_left _ _ _ _ (by simp [bytesLE_length]; omega),
        window_append_left _ _ _ _ (by simp [bytesLE_length]; omega)]
    rcases (show 8 * i = 20880 ∨ 8 * i = 20888 ∨ 8 * i = 20896 ∨ 8 * i = 20904 by omega) with h | h | h | h
    · rw [if_pos h, h, show (20880 : Nat) = 20880 + 0 from rfl, hrho 0 (by omega),
        show WIT = WIT + 0 from rfl, v6M_eq N w 0 (by omega) (by omega)]
    · rw [if_neg (by omega), if_pos h, h, hrho 8 (by omega), v6M_eq N w 8 (by omega) (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, h, show (20896 : Nat) = 20880 + 16 from rfl,
        win_tail N w _ _ (by omega)]
      unfold tailBytes
      simp only [List.append_assoc]
      rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
        show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
        window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega)]
      rfl
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), h, show (20904 : Nat) = 20880 + 24 from rfl,
        win_tail N w _ _ (by omega), ClaudeWCT.W9.T3M.tail_counter_window, v6M_eq N w 16 (by omega) (by omega),
        v6_head N w _ (by omega)]
      have hh : window (headerBytes w) 16 8 = bytesLE 4 w.digestCounter ++ zeros 4 := by
        unfold headerBytes
        rw [show bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++
          zeros 28 = bytesLE 16 w.signature.rho ++ (bytesLE 4 w.digestCounter ++ zeros 4 ++ (zeros 8 ++
            bytesLE 4 (w.counters 3) ++ zeros 28)) by simp [zeros, List.append_assoc, List.replicate_add]]
        rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
          show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
          window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]), window_full _ _ (by simp [bytesLE_length, zeros])]
      rw [hh, wu_small _ (by
        rw [SigGolfCandidate.T3M.readLE_append, bytesLE_length]
        rw [SigGolfCandidate.T3M.readLE_bytesLE]
        have := w.digestCounter.isLt
        have hz : readLE (zeros 4) = 0 := by decide
        rw [hz]; omega)]
end ClaudeWCT.W9.Machine.Expand.Compact2
