import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Final
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.WitV5

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer height chainCount LayerSignature route readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap window_flatMap_const
  window_full window_zeros window_take zeros wordsOf layerBytes layerBytes_length layerBytes_merkle layerBytes_chain)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M ( headerBytes wctBytes regionBytes layerRegion tailBytes lowerPathBytes headerBytes_length
  regionBytes_length      regionLen regionTake_length
  wct_prefix wctBytes_length layers_length tailBytes_length)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 layerRegionV6 layerBytesBCV6 bcTopBlockV6 wctBytesV6_length
  witListV6_length layerRegionV6_length layersV6_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
open ClaudeWCT.W9.T3M (pathSlots layerBase layerBase_ge layerEnd_le layerRegion_length layer_prefix regionBase)
/-- Serialized output of the in-place compactor, before the endpoint-buffer pass. -/
def preBufferWitList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++ tailBytes w
theorem preBufferWitList_length (N : HashOutput) (w : WCT9.Witness) : (preBufferWitList N w).length = 20912 := by
  unfold preBufferWitList
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, tailBytes_length]

theorem preBufferWitList_split (N : HashOutput) (w : WCT9.Witness) :
    preBufferWitList N w = ((headerBytes w ++ wctBytes N w.signature) ++ (List.finRange 4).flatMap (layerRegion N w)) ++
      tailBytes w := rfl

theorem preBufferWinHeader (N : HashOutput) (w : WCT9.Witness) (off n : Nat) (h : off + n ≤ 64) :
    window (preBufferWitList N w) off n = window (headerBytes w) off n := by
  rw [preBufferWitList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_left _ _ _ _ (by rw [headerBytes_length]; omega)]

theorem preBufferWinTail (N : HashOutput) (w : WCT9.Witness) (off n : Nat) (h : off + n ≤ 32) :
    window (preBufferWitList N w) (20880 + off) n = window (tailBytes w) off n := by
  rw [preBufferWitList_split, window_append_right _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, Nat.add_sub_cancel_left]

theorem preBufferWinLayer (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (j m : Nat)
    (hjm : j + m ≤ 16 * pathSlots lay + 64 * chainCount lay) :
    window (preBufferWitList N w) (layerBase lay + j) m = window (layerRegion N w lay) j m := by
  have hb := layerBase_ge lay
  have he := layerEnd_le lay
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := window_flatMap (List.finRange 4) (layerRegion N w) lay.val (by simp) j m
    (by rw [hlen, layerRegion_length]; omega)
  rw [layer_prefix N w lay, hlen] at key
  rw [preBufferWitList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_right _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length]
  rw [show layerBase lay + j - (64 + 7360) = (layerBase lay - 7424) + j by omega, key]

theorem preBufferWinRegion (N : HashOutput) (w : WCT9.Witness) (k : WCT9.Coord) (o n : Nat) (h : o + n ≤ 816) :
    window (preBufferWitList N w) (regionBase k.val + o) n =
      window (regionBytes (WCT9.child N k).val (w.signature.openings k)) o n := by
  have hk := k.isLt
  have hrb : regionBase k.val = 64 + 816 * (8 - k.val) := rfl
  rw [preBufferWitList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    show regionBase k.val + o - 64 = 816 * (8 - k.val) + o by omega]
  have hidx : ((List.finRange 9).reverse[8 - k.val]'(by simp; omega)) = k := by
    rw [List.getElem_reverse]; ext; simp; omega
  have key := window_flatMap (List.finRange 9).reverse (fun k => (regionBytes (WCT9.child N k).val
      (w.signature.openings k)).take (if k.val = 0 then 832 else 816)) (8 - k.val) (by simp; omega) o n
    (by rw [hidx, regionTake_length]; unfold regionLen; split <;> omega)
  rw [show (((List.finRange 9).reverse.take (8 - k.val)).map fun b => ((regionBytes (WCT9.child N b).val
      (w.signature.openings b)).take (if b.val = 0 then 832 else 816)).length) =
      (((List.finRange 9).reverse.take (8 - k.val)).map regionLen) from
      List.map_congr_left (fun b _ => regionTake_length b _ _), wct_prefix, hidx] at key
  unfold wctBytes
  rw [key, window_take _ _ _ _ (by split <;> omega)]
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
    window (preBufferWitList N w) (64 + 816 * 8 + o) 8 =
      window (regionBytes (WCT9.child N 0).val (w.signature.openings 0)) o 8 := by
  rw [preBufferWitList_split, window_append_left _ _ _ _ (by
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
    BitVec.ofNat 64 (readLE (window (preBufferWitList N w) o 8)) =
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
    preBufferWinLayer N w L _ 8 (by omega), Nat.add_sub_cancel_left]
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
    (wordsOf (preBufferWitList N w)).getD i 0 = out2 (v6M N w) (WCT9.digestIndex N) (8 * i) := by
  rw [wordsOf_getD' _ 2614 (by rw [preBufferWitList_length]) i hi]
  unfold out2
  by_cases h64 : 8 * i < 64
  · rw [if_pos h64, v6M_eq N w _ (by omega) (by omega), preBufferWinHeader N w _ _ (by omega), v6_head N w _ (by omega)]
  rw [if_neg h64]
  by_cases h8k : 8 * i < 7424
  · rw [if_pos h8k]
    by_cases hq : (8 * i - 64) / 816 < 8
    · have hm : min ((8 * i - 64) / 816) 8 = (8 * i - 64) / 816 := Nat.min_eq_left (by omega)
      rw [hm]
      have hw7 := preBufferWinRegion N w ⟨8 - (8 * i - 64) / 816, by omega⟩ ((8 * i - 64) % 816) 8 (by omega)
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
    have hw7 := preBufferWinLayer N w 0 (8 * i - 7424) 8 (by simp [ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
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
        BitVec.ofNat 64 (readLE (window (preBufferWitList N w) (8 * i) 8)) =
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
    have hrho : ∀ t, t + 8 ≤ 16 → window (preBufferWitList N w) (20880 + t) 8 = window (witListV6 N w) t 8 := fun t ht => by
      rw [preBufferWinTail N w _ _ (by omega), v6_head N w _ (by omega)]
      unfold tailBytes headerBytes
      simp only [List.append_assoc]
      rw [window_append_left _ _ _ _ (by simp [bytesLE_length]; omega),
        window_append_left _ _ _ _ (by simp [bytesLE_length]; omega)]
    rcases (show 8 * i = 20880 ∨ 8 * i = 20888 ∨ 8 * i = 20896 ∨ 8 * i = 20904 by omega) with h | h | h | h
    · rw [if_pos h, h, show (20880 : Nat) = 20880 + 0 from rfl, hrho 0 (by omega),
        show WIT = WIT + 0 from rfl, v6M_eq N w 0 (by omega) (by omega)]
    · rw [if_neg (by omega), if_pos h, h, hrho 8 (by omega), v6M_eq N w 8 (by omega) (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, h, show (20896 : Nat) = 20880 + 16 from rfl,
        preBufferWinTail N w _ _ (by omega)]
      unfold tailBytes
      simp only [List.append_assoc]
      rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
        show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
        window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega)]
      rfl
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), h, show (20904 : Nat) = 20880 + 24 from rfl,
        preBufferWinTail N w _ _ (by omega), ClaudeWCT.W9.T3M.tail_counter_window, v6M_eq N w 16 (by omega) (by omega),
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

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer chainCount readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (headerBytes wctBytes layerRegion tailBytes headerBytes_length wctBytes_length layers_length
  leafBuffersBytes leafBuffersBytes_length leafBufferBytes leafBufferBytes_length leafBufferLen
  leafBufferBase leafBufferSlot endpointBytes endpointBytes_length chainBlock pathSlots layerBase)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem preBufferPrefix (N : HashOutput) (w : WCT9.Witness) (off n : Nat) (h : off + n ≤ 20880) :
    window (preBufferWitList N w) off n = window (ClaudeWCT.W9.T3M.witList N w) off n := by
  have hp : (headerBytes w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w)).length = 20880 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [preBufferWitList_split, ClaudeWCT.W9.T3M.witList_split]
  exact (window_append_left _ _ off n (by rw [hp]; exact h)).trans
    (window_append_left _ _ off n (by rw [hp]; exact h)).symm

theorem preBufferEndpointWindow (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (i : Fin (chainCount lay)) (k : Nat) (hk : k + 8 ≤ 16) :
    window (preBufferWitList N w) (chainBlock lay i.val + 48 + k) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values i)) k 8 := by
  have hi := i.isLt
  have he := ClaudeWCT.W9.T3M.layerEnd_le lay
  have hb : chainBlock lay i.val + 48 + k + 8 ≤ 20880 := by unfold chainBlock; omega
  rw [preBufferPrefix N w _ _ hb]
  rw [show chainBlock lay i.val + 48 + k = (chainBlock lay i.val + 48) + k from rfl,
    ← window_window' _ _ 16 _ 8 hk, ClaudeWCT.W9.T3M.win_chain N w lay i 48 (by omega),
    window_append_right _ _ _ _ (by simp [zeros]),
    show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]

theorem finalBufferWindow (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (off n : Nat) (h : off + n ≤ leafBufferLen lay) :
    window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase lay + off) n =
      window (leafBufferBytes w.signature lay) off n := by
  have hbase : 20880 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hbound : leafBufferBase lay + leafBufferLen lay ≤ 24000 := by fin_cases lay <;> decide
  rw [ClaudeWCT.W9.T3M.witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega)]
  have hi : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have he : (List.finRange 4).reverse[3 - lay.val]'hi = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes w.signature l).length)).sum = leafBufferBase lay - 20880 := by
    simp only [leafBufferBytes_length]; fin_cases lay <;> decide
  have hw := SigGolfCandidate.T3M.window_flatMap (List.finRange 4).reverse (leafBufferBytes w.signature)
    (3 - lay.val) hi off n (by rw [he, leafBufferBytes_length]; exact h)
  rw [hp, he] at hw
  simpa only [leafBuffersBytes, show leafBufferBase lay + off - (64 + 7360 + 13456) = leafBufferBase lay - 20880 + off by omega]
    using hw

theorem endpointBytesWord (sig : WCT9.Signature) (lay : Layer) (off : Nat)
    (hb : off + 8 ≤ 16 * chainCount lay) (ha : off % 8 = 0) :
    window (endpointBytes sig lay) off 8 =
      window (bytesLE 16 ((sig.layers lay).values ⟨off / 16, by omega⟩)) (off % 16) 8 := by
  have hk : off % 16 + 8 ≤ 16 := by omega
  conv_lhs => rw [show off = 16 * (off / 16) + off % 16 by omega]
  rw [← window_window' _ _ 16 _ 8 hk]
  rw [ClaudeWCT.W9.T3M.win_endpointBytes sig lay ⟨off / 16, by omega⟩]

end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer chainCount readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros window_take zeros wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (leafBufferBytes leafBufferBytes_length leafBufferLen endpointBytes endpointBytes_length)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem topBufferWindow (sig : WCT9.Signature) (off : Nat) (hb : off + 8 ≤ 912) (ha : off % 8 = 0) :
    window (leafBufferBytes sig 0) off 8 =
      if off < 32 then zeros 8 else if off < 896 then window (endpointBytes sig 0) (off - 32) 8 else zeros 8 := by
  simp only [leafBufferBytes, if_true]
  have hl : (endpointBytes sig 0).length = 864 := by rw [endpointBytes_length]; rfl
  by_cases h32 : off < 32
  · rw [if_pos h32, window_append_left _ _ _ _ (by simp [zeros,hl]; omega),
      window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega)]
  · rw [if_neg h32]
    by_cases h896 : off < 896
    · rw [if_pos h896, window_append_left _ _ _ _ (by simp [zeros,hl]; omega),
        window_append_right _ _ _ _ (by simp [zeros]; omega)]
      simp only [zeros, List.length_replicate]
    · rw [if_neg h896, window_append_right _ _ _ _ (by simp [zeros,hl]; omega)]
      simp only [List.length_append, zeros, List.length_replicate,hl]
      exact window_zeros _ _ _ (by omega)

theorem lowerBufferWindow (sig : WCT9.Signature) (lay : Layer) (hL : lay ≠ 0)
    (off : Nat) (hb : off + 8 ≤ 736) (ha : off % 8 = 0) :
    window (leafBufferBytes sig lay) off 8 =
      if off < 16 then window (endpointBytes sig lay) off 8 else if off < 32 then zeros 8
      else if off < 704 then window (endpointBytes sig lay) (off - 16) 8 else zeros 8 := by
  have hl : (endpointBytes sig lay).length = 688 := by
    rw [endpointBytes_length]; fin_cases lay
    · exact absurd rfl hL
    all_goals rfl
  have ht : ((endpointBytes sig lay).take 16).length = 16 := by simp [hl]
  have hd : ((endpointBytes sig lay).drop 16).length = 672 := by simp [hl]
  simp only [leafBufferBytes, if_neg hL]
  by_cases h16 : off < 16
  · rw [if_pos h16,
      window_append_left _ _ _ _ (by simp [List.length_append, ht,hd,zeros]; omega),
      window_append_left _ _ _ _ (by simp [List.length_append,ht,zeros]; omega),
      window_append_left _ _ _ _ (by rw [ht]; omega), window_take _ _ _ _ (by omega)]
  · rw [if_neg h16]
    by_cases h32 : off < 32
    · rw [if_pos h32,
        window_append_left _ _ _ _ (by simp [List.length_append,ht,hd,zeros]; omega),
        window_append_left _ _ _ _ (by simp [List.length_append,ht,zeros]; omega),
        window_append_right _ _ _ _ (by rw [ht]; omega), ht, window_zeros _ _ _ (by omega)]
    · rw [if_neg h32]
      by_cases h704 : off < 704
      · rw [if_pos h704,
          window_append_left _ _ _ _ (by simp [List.length_append,ht,hd,zeros]; omega),
          window_append_right _ _ _ _ (by simp [List.length_append,ht,zeros]; omega)]
        simp only [List.length_append,ht,zeros,List.length_replicate]
        unfold window
        rw [List.drop_drop, show 16 + (off - (16 + 16)) = off - 16 by omega]
      · rw [if_neg h704, window_append_right _ _ _ _ (by simp [List.length_append,ht,hd,zeros]; omega)]
        simp only [List.length_append,ht,hd,zeros,List.length_replicate]
        exact window_zeros _ _ _ (by omega)

end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer chainCount readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (leafBufferSlot leafBufferBase leafBufferLen leafBufferBytes chainBlock pathSlots layerBase)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def preBufferMem (N : HashOutput) (w : WCT9.Witness) (A : Nat) : Word :=
  BitVec.ofNat 64 (readLE (window (preBufferWitList N w) (A - 2048) 8))
def serializedMem (N : HashOutput) (w : WCT9.Witness) (A : Nat) : Word :=
  BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (A - 2048) 8))

theorem finalEndpointWindow (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (i : Fin (chainCount lay)) (k : Nat) (hk : k + 8 ≤ 16) :
    window (ClaudeWCT.W9.T3M.witList N w) (leafBufferSlot lay i.val + k) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values i)) k 8 := by
  have hb := ClaudeWCT.W9.T3M.leafBufferSlot_bounds lay i.val i.isLt
  rw [← window_window' _ _ 16 _ 8 hk]
  have h16 : window (ClaudeWCT.W9.T3M.witList N w) (leafBufferSlot lay i.val) 16 =
      bytesLE 16 ((w.signature.layers lay).values i) := by
    rw [ClaudeWCT.W9.T3M.witList_split, window_append_right _ _ _ _ (by
      simp only [List.length_append, ClaudeWCT.W9.T3M.headerBytes_length,
        ClaudeWCT.W9.T3M.wctBytes_length, ClaudeWCT.W9.T3M.layers_length]; omega)]
    simp only [List.length_append, ClaudeWCT.W9.T3M.headerBytes_length,
      ClaudeWCT.W9.T3M.wctBytes_length, ClaudeWCT.W9.T3M.layers_length]
    rw [window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.T3M.leafBuffersBytes_length]; omega)]
    exact ClaudeWCT.W9.T3M.win_leafBuffersBytes w.signature lay i
  rw [h16]

theorem endpointMem_eq (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (i : Fin (chainCount lay)) (k : Nat) (hk : k + 8 ≤ 16) :
    preBufferMem N w (2048 + chainBlock lay i.val + 48 + k) =
      serializedMem N w (2048 + leafBufferSlot lay i.val + k) := by
  unfold preBufferMem serializedMem
  rw [show 2048 + chainBlock lay i.val + 48 + k - 2048 = chainBlock lay i.val + 48 + k by omega,
    show 2048 + leafBufferSlot lay i.val + k - 2048 = leafBufferSlot lay i.val + k by omega,
    preBufferEndpointWindow N w lay i k hk, finalEndpointWindow N w lay i k hk]

theorem bufferMem_endpoint (M : Nat → Word) (lay : Layer) (i : Nat) (hi : i < chainCount lay)
    (k : Nat) (hk : k = 0 ∨ k = 8) :
    Buffer.bufferMem M (2048 + leafBufferSlot lay i + k) =
      M (2048 + chainBlock lay i + 48 + k) := by
  fin_cases lay <;> norm_num [chainCount] at hi
  all_goals interval_cases i <;> rcases hk with rfl | rfl
  all_goals norm_num [Buffer.bufferMem, Buffer.lowerWord, Buffer.lowerIndex,
    leafBufferSlot, leafBufferBase, chainBlock, layerBase, pathSlots, chainCount]

end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer chainCount readLE)
open SigGolfCandidate.T3M (window zeros)
open ClaudeWCT.W9.T3M (leafBufferSlot leafBufferBase)
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def bufferZeroAddresses : List Nat := [22944, 22952, 23632, 23640, 23648, 23656, 23680, 23688, 24368, 24376, 24384, 24392, 24416, 24424, 25104, 25112, 25120, 25128, 25136, 25144, 25152, 25160, 26032, 26040]
def bufferEndpointAddresses : List Nat := (List.finRange 4).flatMap fun lay =>
  (List.range (chainCount lay)).flatMap fun i =>
    [2048 + leafBufferSlot lay i, 2048 + leafBufferSlot lay i + 8]
theorem buffer_address_coverage : ∀ i : Fin 390,
    22928 + 8 * i.val ∈ bufferEndpointAddresses ++ bufferZeroAddresses := by decide +kernel

theorem bufferMem_zeroAddress (M : Nat → Word) (A : Nat) (h : A ∈ bufferZeroAddresses) :
    Buffer.bufferMem M A = 0 := by
  simp only [bufferZeroAddresses, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Buffer.bufferMem]

theorem serializedMem_zeroAddress (N : HashOutput) (w : WCT9.Witness) (A : Nat)
    (h : A ∈ bufferZeroAddresses) : serializedMem N w A = 0 := by
  simp only [bufferZeroAddresses, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 3 + 16) 8)) = 0
    rw [finalBufferWindow N w 3 16 8 (by decide), lowerBufferWindow w.signature 3 (by decide) 16 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 3 + 24) 8)) = 0
    rw [finalBufferWindow N w 3 24 8 (by decide), lowerBufferWindow w.signature 3 (by decide) 24 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 3 + 704) 8)) = 0
    rw [finalBufferWindow N w 3 704 8 (by decide), lowerBufferWindow w.signature 3 (by decide) 704 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 3 + 712) 8)) = 0
    rw [finalBufferWindow N w 3 712 8 (by decide), lowerBufferWindow w.signature 3 (by decide) 712 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 3 + 720) 8)) = 0
    rw [finalBufferWindow N w 3 720 8 (by decide), lowerBufferWindow w.signature 3 (by decide) 720 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 3 + 728) 8)) = 0
    rw [finalBufferWindow N w 3 728 8 (by decide), lowerBufferWindow w.signature 3 (by decide) 728 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 2 + 16) 8)) = 0
    rw [finalBufferWindow N w 2 16 8 (by decide), lowerBufferWindow w.signature 2 (by decide) 16 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 2 + 24) 8)) = 0
    rw [finalBufferWindow N w 2 24 8 (by decide), lowerBufferWindow w.signature 2 (by decide) 24 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 2 + 704) 8)) = 0
    rw [finalBufferWindow N w 2 704 8 (by decide), lowerBufferWindow w.signature 2 (by decide) 704 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 2 + 712) 8)) = 0
    rw [finalBufferWindow N w 2 712 8 (by decide), lowerBufferWindow w.signature 2 (by decide) 712 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 2 + 720) 8)) = 0
    rw [finalBufferWindow N w 2 720 8 (by decide), lowerBufferWindow w.signature 2 (by decide) 720 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 2 + 728) 8)) = 0
    rw [finalBufferWindow N w 2 728 8 (by decide), lowerBufferWindow w.signature 2 (by decide) 728 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 1 + 16) 8)) = 0
    rw [finalBufferWindow N w 1 16 8 (by decide), lowerBufferWindow w.signature 1 (by decide) 16 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 1 + 24) 8)) = 0
    rw [finalBufferWindow N w 1 24 8 (by decide), lowerBufferWindow w.signature 1 (by decide) 24 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 1 + 704) 8)) = 0
    rw [finalBufferWindow N w 1 704 8 (by decide), lowerBufferWindow w.signature 1 (by decide) 704 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 1 + 712) 8)) = 0
    rw [finalBufferWindow N w 1 712 8 (by decide), lowerBufferWindow w.signature 1 (by decide) 712 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 1 + 720) 8)) = 0
    rw [finalBufferWindow N w 1 720 8 (by decide), lowerBufferWindow w.signature 1 (by decide) 720 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 1 + 728) 8)) = 0
    rw [finalBufferWindow N w 1 728 8 (by decide), lowerBufferWindow w.signature 1 (by decide) 728 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 0 + 0) 8)) = 0
    rw [finalBufferWindow N w 0 0 8 (by decide), topBufferWindow w.signature 0 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 0 + 8) 8)) = 0
    rw [finalBufferWindow N w 0 8 8 (by decide), topBufferWindow w.signature 8 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 0 + 16) 8)) = 0
    rw [finalBufferWindow N w 0 16 8 (by decide), topBufferWindow w.signature 16 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 0 + 24) 8)) = 0
    rw [finalBufferWindow N w 0 24 8 (by decide), topBufferWindow w.signature 24 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 0 + 896) 8)) = 0
    rw [finalBufferWindow N w 0 896 8 (by decide), topBufferWindow w.signature 896 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl
  · change BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase 0 + 904) 8)) = 0
    rw [finalBufferWindow N w 0 904 8 (by decide), topBufferWindow w.signature 904 (by decide) (by decide)]
    norm_num [zeros, readLE] <;> rfl

end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer chainCount readLE)
open SigGolfCandidate.T3M (window zeros wordsOf)
open ClaudeWCT.W9.T3M (leafBufferSlot leafBufferBase chainBlock layerBase pathSlots)
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem mem_bufferEndpointAddresses {A : Nat} (h : A ∈ bufferEndpointAddresses) :
    ∃ (lay : Layer) (i k : Nat), i < chainCount lay ∧ (k = 0 ∨ k = 8) ∧
      A = 2048 + leafBufferSlot lay i + k := by
  simp only [bufferEndpointAddresses, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at h
  obtain ⟨lay, _, i, hi, h | h⟩ := h
  · exact ⟨lay,i,0,hi,Or.inl rfl,by simpa using h⟩
  · exact ⟨lay,i,8,hi,Or.inr rfl,h⟩

theorem bufferMem_serializer (N : HashOutput) (w : WCT9.Witness) (A : Nat)
    (hlo : 2048 ≤ A) (hhi : A < 26080) (halign : A % 8 = 0) :
    Buffer.bufferMem (preBufferMem N w) A = serializedMem N w A := by
  by_cases hprefix : A < 22928
  · rw [Buffer.bufferMem, if_neg (by omega), if_neg (by omega)]
    unfold preBufferMem serializedMem
    rw [preBufferPrefix N w _ 8 (by omega)]
  by_cases hfooter : 26048 ≤ A
  · rw [Buffer.bufferMem, if_pos ⟨hfooter,hhi,halign⟩]
    unfold preBufferMem serializedMem
    rw [show A - 3120 - 2048 = 20880 + (A - 26048) by omega,
      show A - 2048 = 24000 + (A - 26048) by omega,
      preBufferWinTail N w _ 8 (by omega), ClaudeWCT.W9.T3M.win_tail N w _ 8 (by omega)]
  · have hidx : (A - 22928) / 8 < 390 := by omega
    have h := buffer_address_coverage ⟨(A - 22928) / 8,hidx⟩
    have he : 22928 + 8 * ((A - 22928) / 8) = A := by omega
    simp only [he,List.mem_append] at h
    rcases h with h | h
    · obtain ⟨lay,i,k,hi,hk,rfl⟩ := mem_bufferEndpointAddresses h
      rw [bufferMem_endpoint _ lay i hi k hk]
      exact endpointMem_eq N w lay ⟨i,hi⟩ k (by rcases hk with rfl | rfl <;> omega)
    · rw [bufferMem_zeroAddress _ _ h,serializedMem_zeroAddress N w _ h]

theorem bufferMem_original_congr (M M' : Nat → Word) (A : Nat)
    (hlo : 2048 ≤ A) (hhi : A < 26080) (halign : A % 8 = 0)
    (hmem : ∀ B, 2048 ≤ B → B < 22960 → B % 8 = 0 → M B = M' B) :
    Buffer.bufferMem M A = Buffer.bufferMem M' A := by
  by_cases hprefix : A < 22928
  · rw [Buffer.bufferMem, if_neg (by omega), if_neg (by omega),
      Buffer.bufferMem, if_neg (by omega), if_neg (by omega)]
    exact hmem A hlo (by omega) halign
  by_cases hfooter : 26048 ≤ A
  · rw [Buffer.bufferMem, if_pos ⟨hfooter,hhi,halign⟩,
      Buffer.bufferMem, if_pos ⟨hfooter,hhi,halign⟩]
    exact hmem (A-3120) (by omega) (by omega) (by omega)
  · have hidx : (A - 22928) / 8 < 390 := by omega
    have h := buffer_address_coverage ⟨(A - 22928) / 8,hidx⟩
    have he : 22928 + 8 * ((A - 22928) / 8) = A := by omega
    simp only [he,List.mem_append] at h
    rcases h with h | h
    · obtain ⟨lay,i,k,hi,hk,rfl⟩ := mem_bufferEndpointAddresses h
      rw [bufferMem_endpoint _ lay i hi k hk,bufferMem_endpoint _ lay i hi k hk]
      have hb : 2048 ≤ 2048 + chainBlock lay i + 48 + k ∧
          2048 + chainBlock lay i + 48 + k < 22960 ∧
          (2048 + chainBlock lay i + 48 + k) % 8 = 0 := by
        fin_cases lay <;> rcases hk with rfl | rfl
        all_goals norm_num [chainBlock,layerBase,pathSlots,chainCount] at hi ⊢ <;> omega
      exact hmem _ hb.1 hb.2.1 hb.2.2
    · rw [bufferMem_zeroAddress _ _ h,bufferMem_zeroAddress _ _ h]

theorem bufferMem_words (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hmem : ∀ i < 2614, M (2048 + 8*i) = (wordsOf (preBufferWitList N w)).getD i 0)
    (i : Nat) (hi : i < 3004) :
    Buffer.bufferMem M (2048 + 8*i) = (wordsOf (ClaudeWCT.W9.T3M.witList N w)).getD i 0 := by
  have hm : ∀ B, 2048 ≤ B → B < 22960 → B % 8 = 0 → M B = preBufferMem N w B := by
    intro B hB hB' h8
    have hj : (B-2048)/8 < 2614 := by omega
    have he : B = 2048 + 8*((B-2048)/8) := by omega
    have h := hmem _ hj
    rw [wordsOf_getD' _ 2614 (preBufferWitList_length N w) _ hj] at h
    unfold preBufferMem
    have hz : 8*((B-2048)/8) = B-2048 := by omega
    rw [hz] at h
    simpa only [Nat.add_sub_of_le hB] using h
  rw [bufferMem_original_congr M (preBufferMem N w) _ (by omega) (by omega) (by omega) hm,
    bufferMem_serializer N w _ (by omega) (by omega) (by omega),
    wordsOf_getD' _ 3004 (ClaudeWCT.W9.T3M.witList_length_eq N w) i hi]
  unfold serializedMem
  congr 3 <;> omega

end ClaudeWCT.W9.Machine.Expand.Compact2
