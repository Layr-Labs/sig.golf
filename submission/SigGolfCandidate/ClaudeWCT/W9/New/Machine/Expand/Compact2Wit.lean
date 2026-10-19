import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Final
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.WitV5

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer height chainCount LayerSignature route readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap window_flatMap_const
  window_full window_zeros window_take zeros wordsOf layerBytes layerBytes_length layerBytes_merkle layerBytes_chain)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (headerBytes wctBytes regionBytes layerRegion tailBytes lowerPathBytes headerBytes_length
  regionBytes_length regionLen regionCell regionCell_length
  wct_prefix wctBytes_length layers_length tailBytes_length)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 layerRegionV6 layerBytesBCV6 bcTopBlockV6 wctBytesV6_length
  witListV6_length layerRegionV6_length layersV6_length headerBytesV5 headerBytesV5_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
open ClaudeWCT.W9.T3M (pathSlots layerBase layerBase_ge layerEnd_le layerRegion_length layer_prefix regionBase)
theorem window_window' (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
section
variable (N : HashOutput) (w : WCT9.Witness)
theorem v6_head (o : Nat) (h : o + 8 ≤ 64) : window (witListV6 N w) o 8 = window (headerBytesV5 w) o 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_left _ _ _ _ (by rw [headerBytesV5_length]; omega)]
theorem v6_region (k : Nat) (hk : k < 9) (j : Nat) (hj : j + 8 ≤ 896) :
    window (witListV6 N w) (64 + 896 * k + j) 8 =
      window (regionBytes (WCT9.child N ⟨k, hk⟩).val (w.signature.openings ⟨k, hk⟩) (zeros 16) (zeros 16)) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
    window_append_left _ _ _ _ (by rw [wctBytesV6_length]; omega),
    show 64 + 896 * k + j - 64 = 896 * k + j by omega]
  unfold wctBytesV6
  rw [window_flatMap_const _ _ 896 (fun k => ClaudeWCT.W9.Machine.Expand.regionBytesV6_length _ _) k (by simp; omega)
    j 8 (by omega)]
  simp only [List.getElem_finRange, Fin.cast_mk, ClaudeWCT.W9.Machine.Expand.regionBytesV6]
def layOffV6 (lay : Layer) : Nat := (![0, 4224, 7424, 10560] : Layer → Nat) lay
theorem v6_layer (lay : Layer) (j : Nat) (hj : j + 8 ≤ 64 * vBlocks lay) :
    window (witListV6 N w) (8136 + layOffV6 lay + j) 8 = window (layerRegionV6 N w lay) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
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
      p ≠ 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 40)
    (hhi : p ≠ ClaudeWCT.W9.T3M.lowerHiSlot lay leaf) :
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
    unfold ClaudeWCT.W9.T3M.lowerHiSlot at hhi ⊢
    rw [if_neg (by omega), if_neg (by omega)]
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
theorem lvDst_eq (lay : Layer) (hl : lay.val ≠ 0) : lvDst lay.val - WIT = ClaudeWCT.W9.T3M.layerBase lay + 856 ∧
    pathTop lay.val = 16 * ClaudeWCT.W9.T3M.pathSlots lay ∧
    chDst lay.val - WIT = ClaudeWCT.W9.T3M.layerBase lay + 856 + 16 * ClaudeWCT.W9.T3M.pathSlots lay ∧
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
/-- C4: past the 768-byte path area the top region holds the chain blocks in both layouts. -/
theorem layerRegion_top_tail (p : Nat) (hp : 768 ≤ p) (n : Nat) :
    window (layerRegion N w 0) p n = window (layerRegionV6 N w 0) p n := by
  unfold layerRegion layerRegionV6 gapV6
  rw [if_pos (show (0 : Layer).val = 0 from rfl), if_pos (show (0 : Layer).val = 0 from rfl)]
  have hK : ((SigGolfCandidate.T3M.layerBytes (0 : Layer) (route (WCT9.digestIndex N) 0).1
      (w.signature.layers 0)).take (64 * height (0 : Layer))).length = 768 := by
    rw [List.length_take, SigGolfCandidate.T3M.layerBytes_length]; decide
  have hT : (ClaudeWCT.W9.T3M.topPathBytes (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)).length = 768 := by
    rw [ClaudeWCT.W9.T3M.topPathBytes_length]; rfl
  rw [List.append_assoc, List.append_assoc]
  rw [window_append_right _ _ _ _ (by rw [hT]; exact hp), hT]
  conv_rhs => rw [window_append_right _ _ _ _ (by rw [hK]; exact hp), hK]
  rw [vGap_top, show ClaudeWCT.W9.T3M.topChainBlocks - chainCount (0 : Layer) = 2 from rfl]

theorem rootOff_eq_hi (L : Layer) (hL : L.val ≠ 0) (idx : Nat) :
    rootOff L.val (lroute L.val idx) = ClaudeWCT.W9.T3M.lowerHiSlot L (route idx L).1 := by
  unfold rootOff ClaudeWCT.W9.T3M.lowerHiSlot
  rw [plan_eq, lroute_eq L hL]
  congr 3
  unfold rootJ; fin_cases L <;> simp_all [height]
end ident2
theorem ofNat_readLE_zeros8 : BitVec.ofNat 64 (readLE (zeros 8)) = 0 := by decide
section chainarea
variable (N : HashOutput) (w : WCT9.Witness)
theorem lower_cc (L : Layer) (hL : L.val ≠ 0) : chainCount L = 43 := by
  fin_cases L <;> simp_all [chainCount]
theorem lower_area (L : Layer) (hL : L.val ≠ 0) : ClaudeWCT.W9.T3M.chainArea L = 2248 := by
  unfold ClaudeWCT.W9.T3M.chainArea; rw [if_neg hL]
/-- Pairing stage 1: the value of chain `42 - b` (staging chain block `b`) as staged at `WIT`. -/
theorem v6_chainval (L : Layer) (hL : L.val ≠ 0) (b : Nat) (hb : b < 43) (d : Nat) (hd : d = 0 ∨ d = 8) :
    v6M N w (WIT + (8136 + layOffV6 L + 64 * height L + (64 * b + 48 + d))) =
      BitVec.ofNat 64 (readLE (window (bytesLE 16 (ClaudeWCT.W9.T3M.lsValue (w.signature.layers L) (42 - b))) d 8)) := by
  have hcc := lower_cc L hL
  have hlo : 8136 + layOffV6 L + 64 * (height L + chainCount L) ≤ 21832 ∧ layOffV6 L % 64 = 0 := by
    fin_cases L <;> decide
  have hh1 := ClaudeWCT.W9.T3M.height_pos' L
  have hvb := vBlocks_low L hL
  rw [v6M_eq N w _ (by omega) (by omega),
    show 8136 + layOffV6 L + 64 * height L + (64 * b + 48 + d) =
      8136 + layOffV6 L + (64 * height L + (64 * b + 48 + d)) by omega,
    v6_layer N w L _ (by omega)]
  unfold layerRegionV6 layerBytesBCV6
  rw [if_neg hL, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega),
    ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length, window_drop,
    show 64 + (64 * height L + (64 * b + 48 + d) - 64) =
      (64 * height L + 64 * (chainCount L - 1 - (42 - b)) + 48) + d by rw [hcc]; omega,
    win8_of_16 _ _ _ (by omega),
    SigGolfCandidate.T3M.layerBytes_chain L _ _ ⟨42 - b, by omega⟩ 48 (by omega),
    window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
    window_full _ _ (bytesLE_length _ _)]
  unfold ClaudeWCT.W9.T3M.lsValue
  rw [dif_pos (by omega)]
/-- Pairing stage 1: an 8-byte word of a pair block of a lower chain area. -/
theorem lc_word {lay : Layer} (ls : LayerSignature lay) (m r : Nat) (hm : m < 21) (hr : r < 104) (h8 : r % 8 = 0) :
    window (ClaudeWCT.W9.T3M.lowerChainBytes ls) (104 * m + r) 8 =
      if r = 16 ∨ r = 24 then window (bytesLE 16 (ClaudeWCT.W9.T3M.lsValue ls (2 * (20 - m) + 1))) (r - 16) 8
      else if r = 88 ∨ r = 96 then window (bytesLE 16 (ClaudeWCT.W9.T3M.lsValue ls (2 * (20 - m) + 2))) (r - 88) 8
      else zeros 8 := by
  unfold ClaudeWCT.W9.T3M.lowerChainBytes
  rw [List.append_assoc, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.T3M.pairs_length]; omega),
    window_flatMap_const _ _ 104 (ClaudeWCT.W9.T3M.pairBytes_length ls) m (by simp; omega) r 8 (by omega)]
  have hidx : ((List.range 21).reverse)[m]'(by simp <;> omega) = 20 - m := by simp <;> omega
  rw [hidx]
  unfold ClaudeWCT.W9.T3M.pairBytes
  by_cases h1 : r < 16
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega), window_zeros _ _ _ (by omega),
      if_neg (by omega), if_neg (by omega)]
  by_cases h2 : r < 32
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 16).length = 16 by simp [zeros],
      if_pos (by omega)]
  by_cases h3 : r < 88
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      show (zeros 16 ++ bytesLE 16 (ClaudeWCT.W9.T3M.lsValue ls (2 * (20 - m) + 1))).length = 32 by
        simp [zeros, bytesLE_length],
      window_zeros _ _ _ (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      show (zeros 16 ++ bytesLE 16 (ClaudeWCT.W9.T3M.lsValue ls (2 * (20 - m) + 1)) ++ zeros 56).length = 88 by
        simp [zeros, bytesLE_length],
      if_neg (by omega), if_pos (by omega)]
/-- Pairing stage 1: an 8-byte word of chain 0's block at the end of a lower chain area. -/
theorem lc_tail {lay : Layer} (ls : LayerSignature lay) (q : Nat) (h1 : 2184 ≤ q) (h2 : q + 8 ≤ 2248) (h8 : q % 8 = 0) :
    window (ClaudeWCT.W9.T3M.lowerChainBytes ls) q 8 =
      if 2232 ≤ q then window (bytesLE 16 (ClaudeWCT.W9.T3M.lsValue ls 0)) (q - 2232) 8 else zeros 8 := by
  unfold ClaudeWCT.W9.T3M.lowerChainBytes
  rw [List.append_assoc, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.T3M.pairs_length]; omega),
    ClaudeWCT.W9.T3M.pairs_length]
  by_cases h : 2232 ≤ q
  · rw [if_pos h, window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 48).length = 48 by simp [zeros],
      show q - 2184 - 48 = q - 2232 by omega]
  · rw [if_neg h, window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega)]
/-- Pairing stage 1: the pair copy + zero fill rebuilds the witness's lower chain area. -/
theorem chOut_eq (L : Layer) (hL : L.val ≠ 0) (q : Nat) (hq : q + 8 ≤ 2248) (h8 : q % 8 = 0) :
    chOut (v6M N w) L.val q =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.lowerChainBytes (w.signature.layers L)) q 8)) := by
  obtain ⟨_, _, _, e4⟩ := lvDst_eq L hL
  have hS : ∀ s, chSrc L.val - SNAP2 + WIT + s = WIT + (8136 + layOffV6 L + 64 * height L + s) := by
    intro s; omega
  unfold chOut
  by_cases hlo : q < 2184
  · obtain ⟨m, r, hm, hr, rfl⟩ : ∃ m r, m < 21 ∧ r < 104 ∧ q = 104 * m + r :=
      ⟨q / 104, q % 104, by omega, Nat.mod_lt _ (by norm_num), by omega⟩
    have hr8 : r % 8 = 0 := by omega
    rw [lc_word _ m r hm hr hr8, show (104 * m + r) / 104 = m by omega, show (104 * m + r) % 104 = r by omega]
    unfold PairCopy.isVal PairCopy.srcOff
    by_cases hv : r = 16 ∨ r = 24 ∨ r = 88 ∨ r = 96
    · rw [if_pos ⟨hlo, hv⟩, hS]
      rcases hv with rfl | rfl | rfl | rfl
      · rw [if_pos rfl, if_pos (Or.inl rfl), show 128 * m + 112 = 64 * (2 * m + 1) + 48 + 0 by omega,
          v6_chainval N w L hL _ (by omega) 0 (Or.inl rfl), show 42 - (2 * m + 1) = 2 * (20 - m) + 1 by omega]
      · rw [if_neg (by omega), if_pos rfl, if_pos (Or.inr rfl), show 128 * m + 120 = 64 * (2 * m + 1) + 48 + 8 by omega,
          v6_chainval N w L hL _ (by omega) 8 (Or.inr rfl), show 42 - (2 * m + 1) = 2 * (20 - m) + 1 by omega]
      · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos (Or.inl rfl),
          show 128 * m + 48 = 64 * (2 * m) + 48 + 0 by omega,
          v6_chainval N w L hL _ (by omega) 0 (Or.inl rfl), show 42 - 2 * m = 2 * (20 - m) + 2 by omega]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (Or.inr rfl),
          show 128 * m + 56 = 64 * (2 * m) + 48 + 8 by omega,
          v6_chainval N w L hL _ (by omega) 8 (Or.inr rfl), show 42 - 2 * m = 2 * (20 - m) + 2 by omega]
    · rw [if_neg (fun h => hv h.2), if_neg (by omega), if_neg (by omega), if_neg (by omega), ofNat_readLE_zeros8]
  · rw [if_neg (fun h => hlo h.1), lc_tail _ q (by omega) hq h8]
    by_cases ht : 2232 ≤ q
    · rw [if_pos (by omega), if_pos ht, hS,
        show 2688 + (q - 2184) = 64 * 42 + 48 + (q - 2232) by omega,
        v6_chainval N w L hL 42 (by omega) _ (by omega)]
    · rw [if_neg (by omega), if_neg ht, ofNat_readLE_zeros8]
end chainarea
section ident3
variable (N : HashOutput) (w : WCT9.Witness)
/-- Pairing stage 1: a word of a lower layer region of the final witness after the second pass. -/
theorem zone_low (L : Layer) (hL : L.val ≠ 0) (o : Nat) (h1 : ClaudeWCT.W9.T3M.layerBase L ≤ o)
    (h2 : o + 8 ≤ ClaudeWCT.W9.T3M.layerBase L + (16 * ClaudeWCT.W9.T3M.pathSlots L + 2248))
    (h8 : o % 8 = 0) :
    BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) o 8)) =
      if o - ClaudeWCT.W9.T3M.layerBase L < 16 * ClaudeWCT.W9.T3M.pathSlots L then
        pathOut (v6M N w) L.val (lroute L.val (WCT9.digestIndex N)) (o - ClaudeWCT.W9.T3M.layerBase L)
      else chOut (v6M N w) L.val (o - ClaudeWCT.W9.T3M.layerBase L - 16 * ClaudeWCT.W9.T3M.pathSlots L) := by
  have hW : WIT = 0x800 := rfl
  set leaf := (route (WCT9.digestIndex N) L).1 with hleafdef
  have hleaf : leaf < 2 ^ height L := ClaudeWCT.W9.T3M.route_leaf_lt _ _
  have hps : 16 * ClaudeWCT.W9.T3M.pathSlots L ≤ 16 * 25 ∧ ClaudeWCT.W9.T3M.layerBase L % 8 = 0 ∧
      ClaudeWCT.W9.T3M.pathSlots L ≥ 20 := by
    fin_cases L <;> simp_all [ClaudeWCT.W9.T3M.pathSlots, ClaudeWCT.W9.T3M.layerBase]
  have hlo : 8136 + layOffV6 L + 64 * (height L + chainCount L) ≤ 21832 ∧ layOffV6 L % 64 = 0 := by
    fin_cases L <;> decide
  have hh1 := ClaudeWCT.W9.T3M.height_pos' L
  have harea := lower_area L hL
  have hvb := vBlocks_low L hL
  rw [show o = ClaudeWCT.W9.T3M.layerBase L + (o - ClaudeWCT.W9.T3M.layerBase L) by omega,
    ClaudeWCT.W9.T3M.win_layerRegion N w L _ 8 (by omega), Nat.add_sub_cancel_left]
  unfold layerRegion
  rw [if_neg hL]
  by_cases hp : o - ClaudeWCT.W9.T3M.layerBase L < 16 * ClaudeWCT.W9.T3M.pathSlots L
  · rw [if_pos hp, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.T3M.lowerPathBytes_length]; omega)]
    unfold pathOut
    have hro := rootOff_eq_hi L hL (WCT9.digestIndex N)
    rw [← hleafdef] at hro
    by_cases hrt : o - ClaudeWCT.W9.T3M.layerBase L = rootOff L.val (lroute L.val (WCT9.digestIndex N))
    · rw [if_pos hrt, hrt, hro, ClaudeWCT.W9.T3M.lowerPath_hi hL hleaf]
      decide
    rw [if_neg hrt]
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
        omega) (fun hh => hrt (by rw [hh, ← hro, lroute_eq L hL]))]
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
      have e6 := v6_block (leaf := leaf) (w.signature.layers L) (w.counters (Fin.ofNat 4 (L.val - 1))) ⟨j, hj⟩ d
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
      ClaudeWCT.W9.T3M.lowerPathBytes_length, chOut_eq N w L hL _ (by omega) (by omega)]
end ident3
/-- Pairing stage 1: final witness words of the layer regions above the top path area (`[8864, 20104)`) are the
second pass's output (`out2old` at staging offset `8 i + 856`). -/
theorem compact2_words (N : HashOutput) (w : WCT9.Witness) (i : Nat) (h1 : 8864 ≤ 8 * i) (h2 : 8 * i < 20104) :
    BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (8 * i) 8)) =
      out2old (v6M N w) (WCT9.digestIndex N) (8 * i + 856) := by
  unfold out2old
  rw [if_neg (show ¬ 8 * i + 856 < 8952 by omega)]
  by_cases htop : 8 * i + 856 < 13176
  · rw [if_pos htop]
    have hw7 := ClaudeWCT.W9.T3M.win_layerRegion N w 0 (8 * i - 8096) 8
      (by simp [ClaudeWCT.W9.T3M.pathSlots, ClaudeWCT.W9.T3M.chainArea, ClaudeWCT.W9.T3M.topChainBlocks]; omega)
    have hw6 := v6_layer N w 0 (8 * i - 8096) (by rw [vBlocks_vals.1]; omega)
    rw [show ClaudeWCT.W9.T3M.layerBase 0 + (8 * i - 8096) = 8 * i by simp [ClaudeWCT.W9.T3M.layerBase]; omega]
      at hw7
    rw [hw7, layerRegion_top_tail N w _ (by omega),
      show WIT + (8 * i + 856 - 816) = WIT + (8136 + layOffV6 0 + (8 * i - 8096)) by simp [layOffV6]; omega,
      v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6]; omega), hw6]
  rw [if_neg htop, if_pos (show 8 * i + 856 < 20960 by omega)]
  have hW : WIT = 0x800 := rfl
  have key : ∀ L : Layer, L.val ≠ 0 → zoneLay (8 * i + 856) = L.val → ClaudeWCT.W9.T3M.layerBase L ≤ 8 * i →
      8 * i + 8 ≤ ClaudeWCT.W9.T3M.layerBase L + (16 * ClaudeWCT.W9.T3M.pathSlots L + 2248) →
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (8 * i) 8)) =
        (if 8 * i + 856 - (lvDst (zoneLay (8 * i + 856)) - WIT) < pathTop (zoneLay (8 * i + 856)) then
          pathOut (v6M N w) (zoneLay (8 * i + 856)) (lroute (zoneLay (8 * i + 856)) (WCT9.digestIndex N))
            (8 * i + 856 - (lvDst (zoneLay (8 * i + 856)) - WIT))
        else chOut (v6M N w) (zoneLay (8 * i + 856)) (8 * i + 856 - (chDst (zoneLay (8 * i + 856)) - WIT))) := by
    intro L hL hz h1 h2
    obtain ⟨e1, e2, e3, e4⟩ := lvDst_eq L hL
    rw [hz, e1, e2, e3, zone_low N w L hL (8 * i) h1 h2 (by omega),
      show 8 * i + 856 - (ClaudeWCT.W9.T3M.layerBase L + 856) = 8 * i - ClaudeWCT.W9.T3M.layerBase L by omega,
      show 8 * i + 856 - (ClaudeWCT.W9.T3M.layerBase L + 856 + 16 * ClaudeWCT.W9.T3M.pathSlots L) =
        8 * i - ClaudeWCT.W9.T3M.layerBase L - 16 * ClaudeWCT.W9.T3M.pathSlots L by omega]
  by_cases hz1 : 8 * i + 856 < 15824
  · exact key 1 (by decide) (by unfold zoneLay; rw [if_pos hz1]; rfl) (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
      (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots]; omega)
  · by_cases hz2 : 8 * i + 856 < 18392
    · exact key 2 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_pos hz2]; rfl)
        (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
        (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots]; omega)
    · exact key 3 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_neg hz2]; rfl)
        (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
        (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots]; omega)

/-- C4: the second pass leaves the top path area in the old 64-byte stride layout (`layerRegionV6 N w 0`); the
post-pass re-places it. -/
theorem compact2_top_old (N : HashOutput) (w : WCT9.Witness) (i : Nat) (h1 : 8096 ≤ 8 * i) (h2 : 8 * i < 8864) :
    out2old (v6M N w) (WCT9.digestIndex N) (8 * i + 856) =
      BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * i - 8096) 8)) := by
  have hw6 := v6_layer N w 0 (8 * i - 8096) (by rw [vBlocks_vals.1]; omega)
  unfold out2old
  rw [if_neg (by omega), if_pos (by omega),
    show WIT + (8 * i + 856 - 816) = WIT + (8136 + layOffV6 0 + (8 * i - 8096)) by simp [layOffV6, WIT]; omega,
    v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6]; omega), hw6]
/-- Pairing stage 1: the staged rho / digest counter (second-pass offsets 20960 .. 20984) are the witness tail. -/
theorem tail_words (N : HashOutput) (w : WCT9.Witness) (t : Nat) (ht : t < 4) :
    out2old (v6M N w) (WCT9.digestIndex N) (20960 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (23208 + 8 * t) 8)) := by
  rw [ClaudeWCT.W9.T3M.win_tail N w _ _ (by omega)]
  have hrho : ∀ d, d + 8 ≤ 16 → window (tailBytes w) d 8 = window (witListV6 N w) d 8 := fun d hd => by
    rw [v6_head N w _ (by omega)]
    unfold tailBytes headerBytesV5
    simp only [List.append_assoc]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [bytesLE_length]; omega)]
  unfold out2old
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [if_pos (by norm_num), show 8 * 0 = 0 from rfl, hrho 0 (by omega), ← v6M_eq N w 0 (by omega) (by omega),
      Nat.add_zero]
  · rw [if_neg (by norm_num), if_pos (by norm_num), show 8 * 1 = 8 from rfl, hrho 8 (by omega),
      ← v6M_eq N w 8 (by omega) (by omega)]
  · rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num), show 8 * 2 = 16 from rfl]
    unfold tailBytes
    simp only [List.append_assoc]
    rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
      show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
      window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega), ofNat_readLE_zeros8]
  · rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), show 8 * 3 = 24 from rfl,
      ClaudeWCT.W9.T3M.tail_counter_window, v6M_eq N w 16 (by omega) (by omega), v6_head N w _ (by omega)]
    have hh : window (headerBytesV5 w) 16 8 = bytesLE 4 w.digestCounter ++ zeros 4 := by
      unfold headerBytesV5
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
/-! ### Pairing stage 1: the leaf buffers written by the layout block -/
def layOf (k : Nat) : Layer := Fin.ofNat 4 (3 - Layout.grpK k)
def iK (k : Nat) : Nat := k - 43 * Layout.grpK k
def kOf (lay : Layer) (i : Nat) : Nat := 43 * (3 - lay.val) + i
theorem buf_table : ∀ k < 181, iK k < chainCount (layOf k) ∧
    Layout.slotK k = 2904 + ClaudeWCT.W9.T3M.leafBufferSlot (layOf k) (iK k) ∧
    Layout.sK k = 2904 + ClaudeWCT.W9.T3M.chainBlock (layOf k) (iK k) + ClaudeWCT.W9.T3M.valueOff (layOf k) (iK k) ∧
    11768 ≤ Layout.sK k ∧ Layout.sK k + 16 ≤ 23008 ∧ Layout.slotK k % 8 = 0 := by
  decide +kernel
theorem buf_table2 : ∀ lay : Layer, ∀ i < chainCount lay, kOf lay i < 181 ∧
    Layout.slotK (kOf lay i) = 2904 + ClaudeWCT.W9.T3M.leafBufferSlot lay i := by
  decide +kernel
theorem hitVal_hit (M : Nat → Word) (k : Nat) (hk : k < 181) (A : Nat)
    (h : Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16) :
    Layout.hitVal M 181 A = M (Layout.sK k + (A - Layout.slotK k)) := by
  have key : ∀ j, k < j → j ≤ 181 → Layout.hitVal M j A = M (Layout.sK k + (A - Layout.slotK k)) := by
    intro j
    induction j with
    | zero => intro h1; omega
    | succ j ih =>
      intro h1 h2
      rw [Layout.hitVal_succ M j A (by omega)]
      by_cases hjk : j = k
      · subst hjk; rw [if_pos h]
      · have := Layout.slot_mono k j (by omega) (by omega)
        rw [if_neg (by omega)]
        exact ih (by omega) (by omega)
  exact key 181 hk le_rfl
theorem hitVal_miss (M : Nat → Word) (A : Nat)
    (h : ∀ k < 181, ¬ (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) : Layout.hitVal M 181 A = 0 := by
  have hn : (List.range 181).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) = none := by
    rw [List.find?_eq_none]; intro k hk; simpa using h k (List.mem_range.mp hk)
  unfold Layout.hitVal; rw [hn]
theorem bufferMem_low (M : Nat → Word) (A : Nat) (hA : A < 23008) (h1 : A ≠ 1240) : Buffer.bufferMem M A = M A := by
  unfold Buffer.bufferMem Layout.lbMem Layout.itMem
  rw [if_neg h1, if_neg (by omega), if_neg (by omega)]
section buffers
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_value (lay : Layer) (i : Nat) (hi : i < chainCount lay) (d : Nat) (hd : d + 8 ≤ 16) :
    window (ClaudeWCT.W9.T3M.witList N w) (ClaudeWCT.W9.T3M.chainBlock lay i + ClaudeWCT.W9.T3M.valueOff lay i + d) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values ⟨i, hi⟩)) d 8 := by
  have hv : ClaudeWCT.W9.T3M.lsValue (w.signature.layers lay) i = (w.signature.layers lay).values ⟨i, hi⟩ := by
    simp [ClaudeWCT.W9.T3M.lsValue, hi]
  rw [← window_window' _ _ 16 d 8 hd,
    ClaudeWCT.W9.T3M.win_chain N w lay ⟨i, hi⟩ _ (by unfold ClaudeWCT.W9.T3M.valueOff; split <;> omega)]
  unfold ClaudeWCT.W9.T3M.chainCell ClaudeWCT.W9.T3M.valueOff
  by_cases hG : WCT9.isG lay i = true
  · simp only [hG, if_true]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _), hv]
  · simp only [hG, if_false, Bool.false_eq_true]
    rw [window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
      window_full _ _ (bytesLE_length _ _), hv]
theorem win_slot (lay : Layer) (i : Nat) (hi : i < chainCount lay) (d : Nat) (hd : d + 8 ≤ 16) :
    window (ClaudeWCT.W9.T3M.witList N w) (ClaudeWCT.W9.T3M.leafBufferSlot lay i + d) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values ⟨i, hi⟩)) d 8 := by
  have hb := ClaudeWCT.W9.T3M.leafBufferSlot_bounds lay i hi
  rw [← window_window' _ _ 16 d 8 hd, ClaudeWCT.W9.T3M.witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, ClaudeWCT.W9.T3M.headerBytes_length, ClaudeWCT.W9.T3M.wctBytes_length,
      ClaudeWCT.W9.T3M.layers_length]
    omega)]
  simp only [List.length_append, ClaudeWCT.W9.T3M.headerBytes_length, ClaudeWCT.W9.T3M.wctBytes_length,
    ClaudeWCT.W9.T3M.layers_length]
  rw [window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.T3M.leafBuffersBytes_length]; omega),
    show 80 + 8016 + 12008 = 20104 by decide,
    ClaudeWCT.W9.T3M.win_leafBuffersBytes w.signature lay ⟨i, hi⟩]
theorem lb_zero (sig : WCT9.Signature) (lay : Layer) (off : Nat) (h8 : off % 8 = 0)
    (hlen : off + 8 ≤ ClaudeWCT.W9.T3M.leafBufferLen lay)
    (hz : ∀ i < chainCount lay, ¬ (ClaudeWCT.W9.T3M.leafBufferSlot lay i - ClaudeWCT.W9.T3M.leafBufferBase lay ≤ off ∧
      off < ClaudeWCT.W9.T3M.leafBufferSlot lay i - ClaudeWCT.W9.T3M.leafBufferBase lay + 16)) :
    window (ClaudeWCT.W9.T3M.leafBufferBytes sig lay) off 8 = zeros 8 := by
  unfold ClaudeWCT.W9.T3M.leafBufferSlot at hz
  simp only [Nat.add_sub_cancel_left] at hz
  unfold ClaudeWCT.W9.T3M.leafBufferBytes
  by_cases ht : lay = 0
  · subst ht
    simp only [eq_self_iff_true, if_true, ↓reduceIte] at hz ⊢
    have hl : ClaudeWCT.W9.T3M.leafBufferLen 0 = 912 := rfl
    have hc : chainCount (0 : Layer) = 52 := rfl
    have hE := ClaudeWCT.W9.T3M.endpointBytes_length sig 0
    rw [hc] at hz hE
    by_cases h1 : off < 64
    · rw [window_append_left _ _ _ _ (by simp [zeros, hE]; omega),
        window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega)]
    by_cases h2 : 896 ≤ off
    · rw [window_append_right _ _ _ _ (by simp [zeros, hE]; omega), window_zeros _ _ _ (by simp [zeros, hE]; omega)]
    exfalso; have h := hz ((off - 64) / 16) (by omega); omega
  · simp only [ht, if_false] at hz ⊢
    have hc : chainCount lay = 43 := lower_cc lay (fun h => ht (Fin.ext h))
    have hl : ClaudeWCT.W9.T3M.leafBufferLen lay ≤ 736 ∧ 720 ≤ ClaudeWCT.W9.T3M.leafBufferLen lay := by
      unfold ClaudeWCT.W9.T3M.leafBufferLen; rw [if_neg ht]; split <;> omega
    have hE := ClaudeWCT.W9.T3M.endpointBytes_length sig lay
    rw [hc] at hz hE
    have htl : ((ClaudeWCT.W9.T3M.endpointBytes sig lay).take 16).length = 16 := by
      rw [List.length_take, hE]; decide
    have hdl : ((ClaudeWCT.W9.T3M.endpointBytes sig lay).drop 16).length = 672 := by
      rw [List.length_drop, hE]
    have hzl : (zeros (if lay.val = 1 then 16 else 32)).length = ClaudeWCT.W9.T3M.leafBufferLen lay - 704 := by
      unfold ClaudeWCT.W9.T3M.leafBufferLen; rw [if_neg ht]; simp [zeros]; split <;> rfl
    by_cases h0 : off < 16
    · exfalso; have h := hz 0 (by omega); simp only [if_pos rfl, ↓reduceIte] at h; omega
    by_cases h1 : off < 32
    · rw [window_append_left _ _ _ _ (by simp [zeros, htl, hdl]; omega),
        window_append_left _ _ _ _ (by simp [zeros, htl]; omega),
        window_append_right _ _ _ _ (by rw [htl]; omega), htl, window_zeros _ _ _ (by simp [zeros]; omega)]
    by_cases h2 : 704 ≤ off
    · rw [window_append_right _ _ _ _ (by simp [zeros, htl, hdl]; omega), window_zeros _ _ _ (by
        simp only [List.length_append, htl, hdl, zeros, List.length_replicate] at hzl ⊢; omega)]
    exfalso; have h := hz ((off - 16) / 16) (by omega); rw [if_neg (by omega)] at h; omega
theorem buf_zero (o : Nat) (h1 : 20104 ≤ o) (h2 : o < 23208) (h8 : o % 8 = 0)
    (hz : ∀ lay : Layer, ∀ i < chainCount lay,
      ¬ (ClaudeWCT.W9.T3M.leafBufferSlot lay i ≤ o ∧ o < ClaudeWCT.W9.T3M.leafBufferSlot lay i + 16)) :
    window (ClaudeWCT.W9.T3M.witList N w) o 8 = zeros 8 := by
  have go : ∀ lay : Layer, ClaudeWCT.W9.T3M.leafBufferBase lay ≤ o →
      o + 8 ≤ ClaudeWCT.W9.T3M.leafBufferBase lay + ClaudeWCT.W9.T3M.leafBufferLen lay →
      window (ClaudeWCT.W9.T3M.witList N w) o 8 = zeros 8 := by
    intro lay hb he
    have hs : ∀ i, ClaudeWCT.W9.T3M.leafBufferBase lay ≤ ClaudeWCT.W9.T3M.leafBufferSlot lay i := by
      intro i; unfold ClaudeWCT.W9.T3M.leafBufferSlot; omega
    rw [show o = ClaudeWCT.W9.T3M.leafBufferBase lay + (o - ClaudeWCT.W9.T3M.leafBufferBase lay) by omega,
      ClaudeWCT.W9.T3M.win_leafBuffer N w lay _ 8 (by omega)]
    apply lb_zero _ lay _ (by fin_cases lay <;> simp [ClaudeWCT.W9.T3M.leafBufferBase] at hb ⊢ <;> omega) (by omega)
    intro i hi h
    have := hs i
    exact hz lay i hi ⟨by omega, by omega⟩
  by_cases a3 : o < 20840
  · exact go 3 (by simp [ClaudeWCT.W9.T3M.leafBufferBase]; omega) (by simp [ClaudeWCT.W9.T3M.leafBufferBase, ClaudeWCT.W9.T3M.leafBufferLen]; omega)
  by_cases a2 : o < 21576
  · exact go 2 (by simp [ClaudeWCT.W9.T3M.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.T3M.leafBufferBase, ClaudeWCT.W9.T3M.leafBufferLen]; omega)
  by_cases a1 : o < 22296
  · exact go 1 (by simp [ClaudeWCT.W9.T3M.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.T3M.leafBufferBase, ClaudeWCT.W9.T3M.leafBufferLen]; omega)
  · exact go 0 (by simp [ClaudeWCT.W9.T3M.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.T3M.leafBufferBase, ClaudeWCT.W9.T3M.leafBufferLen]; omega)
/-- Pairing stage 1: the leaf buffers and the tail after the layout block. -/
theorem buffer_words (M : Nat → Word)
    (hM : ∀ o, 8864 ≤ o → o < 20104 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) o 8)))
    (hT : ∀ t < 4, M (23008 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (23208 + 8 * t) 8)))
    (i : Nat) (h1 : 20104 ≤ 8 * i) (h2 : 8 * i < 23240) :
    Buffer.bufferMem M (2904 + 8 * i) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (8 * i) 8)) := by
  unfold Buffer.bufferMem Layout.lbMem Layout.itMem
  rw [if_neg (by omega)]
  by_cases ht : 23208 ≤ 8 * i
  · rw [if_pos (by omega), show 2904 + 8 * i - 3104 = 23008 + 8 * ((8 * i - 23208) / 8) by omega,
      hT _ (by omega), show 23208 + 8 * ((8 * i - 23208) / 8) = 8 * i by omega]
  rw [if_neg (by omega), if_pos (by omega)]
  by_cases hs : ∃ k, k < 181 ∧ Layout.slotK k ≤ 2904 + 8 * i ∧ 2904 + 8 * i < Layout.slotK k + 16
  · obtain ⟨k, hk, ha, hb⟩ := hs
    obtain ⟨hi, hsl, hsk, hk1, hk2, hk8⟩ := buf_table k hk
    rw [hitVal_hit M k hk _ ⟨ha, hb⟩]
    set d := 2904 + 8 * i - Layout.slotK k with hd
    have hd8 : d = 0 ∨ d = 8 := by omega
    rw [show Layout.sK k + d = 2904 + (ClaudeWCT.W9.T3M.chainBlock (layOf k) (iK k) +
        ClaudeWCT.W9.T3M.valueOff (layOf k) (iK k) + d) by omega,
      hM _ (by omega) (by omega) (by
        have := (Layout.tab_facts.2.2.2.2.2.2.2.2 k hk).1
        omega),
      win_value N w _ _ hi d (by omega),
      show 8 * i = ClaudeWCT.W9.T3M.leafBufferSlot (layOf k) (iK k) + d by omega,
      win_slot N w _ _ hi d (by omega)]
  · have hn : ∀ k < 181, ¬ (Layout.slotK k ≤ 2904 + 8 * i ∧ 2904 + 8 * i < Layout.slotK k + 16) :=
      fun k hk h => hs ⟨k, hk, h⟩
    rw [hitVal_miss M _ hn, buf_zero N w (8 * i) h1 (by omega) (by omega) (fun lay j hj h => by
      obtain ⟨hk, he⟩ := buf_table2 lay j hj
      exact hn _ hk ⟨by omega, by omega⟩), ofNat_readLE_zeros8]
end buffers

section topPost
variable (N : HashOutput) (w : WCT9.Witness)
end topPost
/-! ### C4: the top path area after the post-pass -/
open SigGolfCandidate.T3 (route height LayerSignature)
open SigGolfCandidate.T3M (layerBytes layerBytes_merkle window_append_left window_append_right window_full)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand (layerRegionV6)
/-- The post-pass's table slot is the witness's sibling slot (`topSibSlot`). -/
theorem ppSlot_eq_sib (leaf : Nat) (hl : leaf < 4096) (j : Nat) (hj : j < 12) :
    16 * Buffer.Post.ppSlot leaf j = ClaudeWCT.W9.T3M.topSibSlot leaf j := by
  have hs : ∀ b, b < 2 → SigGolfCandidate.T3M.sibOff b = 48 * (1 - b) := fun b hb => by
    unfold SigGolfCandidate.T3M.sibOff; split <;> omega
  unfold Buffer.Post.ppSlot
  by_cases h6 : j < 6
  · rw [if_pos h6, ClaudeWCT.W9.T3M.topSibSlot_lo h6]
    unfold slotA ClaudeWCT.W9.T3M.topSibA ClaudeWCT.W9.T3M.topSlotA
    rw [hs _ (Nat.mod_lt _ (by norm_num))]; ring
  · rw [if_neg h6, ClaudeWCT.W9.T3M.topSibSlot_hi (by omega) hj, Nat.mod_eq_of_lt (show leaf / 64 < 64 by omega)]
    unfold slotB ClaudeWCT.W9.T3M.topSibB ClaudeWCT.W9.T3M.topSlotB
    rw [hs _ (Nat.mod_lt _ (by norm_num))]; ring
/-- The old (pre-C4) top layout holds sibling `j` at `64 (11 - j) + sibOff`. -/
theorem oldTop_sib (leaf : Nat) (ls : LayerSignature 0) (j : Nat) (hj : j < height (0 : Layer)) (d : Nat)
    (hd : d = 0 ∨ d = 8) :
    window (layerBytes 0 leaf ls) (Buffer.Post.ppOld leaf j - 11000 + d) 8 = window (bytesLE 16 (ls.path ⟨j, hj⟩)) d 8 := by
  have hb : leaf / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h12 : j < 12 := lt_of_lt_of_eq hj ClaudeWCT.W9.T3M.height_top
  have hm := layerBytes_merkle 0 leaf ls ⟨j, hj⟩ (48 * (1 - leaf / 2 ^ j % 2)) (by omega)
  simp only [Fin.val_mk] at hm
  have hin : window (if leaf / 2 ^ j % 2 = 1 then bytesLE 16 (ls.path ⟨j, hj⟩) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path ⟨j, hj⟩)) (48 * (1 - leaf / 2 ^ j % 2)) 16 = bytesLE 16 (ls.path ⟨j, hj⟩) := by
    rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ j) with h | h
    · rw [h, if_neg (by decide), show 48 * (1 - 0) = (zeros 48).length by simp [zeros],
        window_append_right _ _ _ _ le_rfl, Nat.sub_self, window_full _ _ (bytesLE_length _ _)]
    · rw [h, if_pos rfl, show 48 * (1 - 1) = 0 from rfl, window_append_left _ _ _ _ (by rw [bytesLE_length]),
        window_full _ _ (bytesLE_length _ _)]
  rw [show Buffer.Post.ppOld leaf j - 11000 + d = 64 * (height (0 : Layer) - 1 - j) + 48 * (1 - leaf / 2 ^ j % 2) + d by
      unfold Buffer.Post.ppOld Buffer.Post.ppBit; rw [ClaudeWCT.W9.T3M.height_top]; omega,
    ← window_window' _ _ 16 d 8 (by omega), hm, hin]
/-- The top path area after the post-pass is the witness's plan-placed area. -/
theorem postMem_top (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * q) 8)))
    (q : Nat) (hq : q < 96) :
    Buffer.Post.ppPlace (Buffer.bufferMem M) (route (WCT9.digestIndex N) 0).1 12 (11000 + 8 * q) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (8096 + 8 * q) 8)) := by
  have hw := ClaudeWCT.W9.T3M.win_topPath N w (8 * q) 8 (by omega)
  rw [show ClaudeWCT.W9.T3M.layerBase 0 = 8096 from rfl] at hw
  rw [hw]
  -- Campaign R6: the staged top region is `gapV6` of the layer bytes; its first 768 bytes (the path area) are
  -- the layer bytes' path blocks.
  have hl6 : ∀ q' < 96, window (layerRegionV6 N w 0) (8 * q') 8 =
      window (layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) (8 * q') 8 := by
    intro q' hq'
    unfold layerRegionV6 gapV6
    rw [if_pos (show (0 : Layer).val = 0 from rfl), List.append_assoc,
      window_append_left _ _ _ _ (by
        rw [List.length_take, SigGolfCandidate.T3M.layerBytes_length]
        have h12 : height (0 : Layer) = 12 := rfl
        have h52 : chainCount (0 : Layer) = 52 := rfl
        omega),
      window_take _ _ _ _ (by have h12 : height (0 : Layer) = 12 := rfl; omega)]
  have hold2 : ∀ q' < 96, M (11000 + 8 * q') = BitVec.ofNat 64 (readLE (window
      (layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) (8 * q') 8)) :=
    fun q' hq' => by rw [hold q' hq', hl6 q' hq']
  clear hold hl6
  have hl : (route (WCT9.digestIndex N) 0).1 < 4096 := by
    have h1 : (route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; exact Nat.mod_lt _ (by norm_num)
  generalize (route (WCT9.digestIndex N) 0).1 = leaf at hl hold2 ⊢
  generalize w.signature.layers 0 = ls at hold2 ⊢
  by_cases hs : ∃ j, j < 12 ∧ 16 * Buffer.Post.ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * Buffer.Post.ppSlot leaf j + 16
  · obtain ⟨j, hj, h1, h2⟩ := hs
    have hj' : j < height (0 : Layer) := lt_of_lt_of_eq hj ClaudeWCT.W9.T3M.height_top.symm
    have he := ppSlot_eq_sib leaf hl j hj
    have hpo := Buffer.Post.ppOld_lt leaf j
    have hpb := Buffer.Post.ppBit_lt leaf j
    have hpo' : 11000 ≤ Buffer.Post.ppOld leaf j := by unfold Buffer.Post.ppOld; omega
    obtain ⟨D, hD8, hDq⟩ : ∃ D, (D = 0 ∨ D = 8) ∧ 8 * q = 16 * Buffer.Post.ppSlot leaf j + D :=
      ⟨8 * q - 16 * Buffer.Post.ppSlot leaf j, by omega, by omega⟩
    rw [hDq, show 11000 + (16 * Buffer.Post.ppSlot leaf j + D) = Buffer.Post.ppNew leaf j + D by
        unfold Buffer.Post.ppNew; omega,
      Buffer.Post.ppPlace_hit _ leaf hl j hj _ hD8,
      bufferMem_low _ _ (by omega) (by omega),
      show Buffer.Post.ppOld leaf j + D = 11000 + 8 * ((Buffer.Post.ppOld leaf j - 11000 + D) / 8) by omega,
      hold2 _ (by omega),
      show 8 * ((Buffer.Post.ppOld leaf j - 11000 + D) / 8) = Buffer.Post.ppOld leaf j - 11000 + D by omega,
      oldTop_sib leaf ls j hj' D hD8, he, ← window_window' _ _ 16 D 8 (by omega),
      ClaudeWCT.W9.T3M.topPath_sib leaf ls ⟨j, hj'⟩]
  · have hm : ∀ j < 12, ¬ (16 * Buffer.Post.ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * Buffer.Post.ppSlot leaf j + 16) :=
      fun j hj h => hs ⟨j, hj, h⟩
    rw [Buffer.Post.ppPlace_miss _ leaf q hq hm,
      ClaudeWCT.W9.T3M.topPath_zero leaf ls (by omega) (fun j => by
        have hj : j.val < 12 := lt_of_lt_of_eq j.isLt ClaudeWCT.W9.T3M.height_top
        have := hm j.val hj
        rw [← ppSlot_eq_sib leaf hl j.val hj]
        omega)]
    decide

/-- Pairing stage 1: the final witness words `[8096, 23240)` after the buffer pass and the top post-pass. -/
theorem postMem_words (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hM : ∀ o, 8864 ≤ o → o < 20104 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) o 8)))
    (hT : ∀ t < 4, M (23008 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (23208 + 8 * t) 8)))
    (hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * q) 8)))
    (i : Nat) (h1 : 1012 ≤ i) (h2 : i < 2905) :
    Buffer.Post.ppPlace (Buffer.bufferMem M) (route (WCT9.digestIndex N) 0).1 12 (2904 + 8 * i) =
      (wordsOf (ClaudeWCT.W9.T3M.witList N w)).getD i 0 := by
  have hl : (route (WCT9.digestIndex N) 0).1 < 4096 := by
    have h1 : (route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; exact Nat.mod_lt _ (by norm_num)
  rw [wordsOf_getD' _ 2905 (ClaudeWCT.W9.T3M.witList_length_eq N w) i h2]
  by_cases htop : 8 * i < 8864
  · rw [show 2904 + 8 * i = 11000 + 8 * (i - 1012) by omega, postMem_top N w M hold (i - 1012) (by omega),
      show 8096 + 8 * (i - 1012) = 8 * i by omega]
  rw [Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by omega)]
  by_cases hb : 8 * i < 20104
  · rw [bufferMem_low _ _ (by omega) (by omega)]
    exact hM _ (by omega) hb (by omega)
  · exact buffer_words N w M hM hT i (by omega) (by omega)

end ClaudeWCT.W9.Machine.Expand.Compact2
