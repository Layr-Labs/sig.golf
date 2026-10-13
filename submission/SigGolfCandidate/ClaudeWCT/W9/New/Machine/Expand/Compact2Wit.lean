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
/-- Serialized output of the in-place compactor, before the endpoint-buffer pass (nested FTS r1-1: header 176,
regions 8080, layers, tail; 21792 bytes from `WOUT`). -/
def preBufferWitList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++ tailBytes w
theorem preBufferWitList_length (N : HashOutput) (w : WCT9.Witness) : (preBufferWitList N w).length = 21792 := by
  unfold preBufferWitList
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length, tailBytes_length]

theorem preBufferWitList_split (N : HashOutput) (w : WCT9.Witness) :
    preBufferWitList N w = ((headerBytes N w ++ wctBytes N w.signature) ++ (List.finRange 4).flatMap (layerRegion N w)) ++
      tailBytes w := rfl

theorem preBufferPrefix (N : HashOutput) (w : WCT9.Witness) (off n : Nat) (h : off + n ≤ 21760) :
    window (preBufferWitList N w) off n = window (ClaudeWCT.W9.T3M.witList N w) off n := by
  have hp : (headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w)).length =
      21760 := by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [preBufferWitList_split, ClaudeWCT.W9.T3M.witList_split]
  exact (window_append_left _ _ off n (by rw [hp]; exact h)).trans
    (window_append_left _ _ off n (by rw [hp]; exact h)).symm

theorem preBufferWinTail (N : HashOutput) (w : WCT9.Witness) (off n : Nat) (h : off + n ≤ 32) :
    window (preBufferWitList N w) (21760 + off) n = window (tailBytes w) off n := by
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
  rw [show layerBase lay + j - (176 + 8080) = (layerBase lay - 8256) + j by omega, key]

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
theorem v6_layer (lay : Layer) (j : Nat) (hj : j + 8 ≤ 64 * (height lay + chainCount lay)) :
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
/-! ### Nested FTS (r1-1): region and header windows of the final witness -/
section regionsplit
open ClaudeWCT.W9.T3M (merkleBytes chainBytes leafBytes topBlockBytes merkleBytes_length chainBytes_length
  ite_slot_length zeros_len)
def rA (c : Nat) (op : WCT9.Opening) : List UInt8 :=
  merkleBytes c op ++ chainBytes op ++ zeros 48 ++ bytesLE 16 (op.values 0) ++ zeros 16
def rB (c : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 5).flatMap (fun i => bytesLE 16 (op.values i.succ)) ++ zeros 16 ++
    (if c / 2 ^ 5 % 2 = 1 then bytesLE 16 (op.path 5) else zeros 16) ++ zeros 16
def rC (c : Nat) (op : WCT9.Opening) : List UInt8 := if c / 2 ^ 5 % 2 = 0 then bytesLE 16 (op.path 5) else zeros 16
theorem regionBytes_split (c : Nat) (op : WCT9.Opening) (pL pZ : List UInt8) :
    regionBytes c op pL pZ = rA c op ++ (pL ++ (rB c op ++ (pZ ++ rC c op))) := by
  simp only [regionBytes, leafBytes, topBlockBytes, rA, rB, rC, List.append_assoc]
theorem rA_length (c : Nat) (op : WCT9.Opening) : (rA c op).length = 720 := by
  simp only [rA, List.length_append, merkleBytes_length, chainBytes_length, zeros_len, bytesLE_length]
theorem rB_length (c : Nat) (op : WCT9.Opening) : (rB c op).length = 128 := by
  simp only [rB, List.length_append, ite_slot_length, zeros_len, List.length_flatMap, bytesLE_length]
  simp
theorem win5 (A P B Q C : List UInt8) (hA : A.length = 720) (hP : P.length = 16) (hB : B.length = 128)
    (hQ : Q.length = 16) (j : Nat) (hj : j % 8 = 0) (hj' : j + 8 ≤ 896) :
    window (A ++ (P ++ (B ++ (Q ++ C)))) j 8 =
      if j < 720 then window A j 8 else if j < 736 then window P (j - 720) 8
      else if j < 864 then window B (j - 736) 8 else if j < 880 then window Q (j - 864) 8
      else window C (j - 880) 8 := by
  by_cases h1 : j < 720
  · rw [if_pos h1, window_append_left _ _ _ _ (by omega)]
  rw [if_neg h1, window_append_right _ _ _ _ (by omega), hA]
  by_cases h2 : j < 736
  · rw [if_pos h2, window_append_left _ _ _ _ (by omega)]
  rw [if_neg h2, window_append_right _ _ _ _ (by omega), hP, show j - 720 - 16 = j - 736 by omega]
  by_cases h3 : j < 864
  · rw [if_pos h3, window_append_left _ _ _ _ (by omega)]
  rw [if_neg h3, window_append_right _ _ _ _ (by omega), hB, show j - 736 - 128 = j - 864 by omega]
  by_cases h4 : j < 880
  · rw [if_pos h4, window_append_left _ _ _ _ (by omega)]
  rw [if_neg h4, window_append_right _ _ _ _ (by omega), hQ, show j - 864 - 16 = j - 880 by omega]
/-- The part of a region word that does not depend on the pads. -/
def regFix (c : Nat) (op : WCT9.Opening) (j : Nat) : List UInt8 :=
  if j < 720 then window (rA c op) j 8 else if j < 864 then window (rB c op) (j - 736) 8
  else window (rC c op) (j - 880) 8
theorem region_win8 (c : Nat) (op : WCT9.Opening) (pL pZ : List UInt8) (hL : pL.length = 16)
    (hZ : pZ.length = 16) (j : Nat) (hj : j % 8 = 0) (hj' : j + 8 ≤ 896) :
    window (regionBytes c op pL pZ) j 8 =
      if 720 ≤ j ∧ j < 736 then window pL (j - 720) 8
      else if 864 ≤ j ∧ j < 880 then window pZ (j - 864) 8 else regFix c op j := by
  rw [regionBytes_split, win5 _ _ _ _ _ (rA_length c op) hL (rB_length c op) hZ j hj hj']
  unfold regFix
  by_cases h1 : j < 720
  · rw [if_pos h1, if_neg (show ¬ (720 ≤ j ∧ j < 736) by omega), if_neg (show ¬ (864 ≤ j ∧ j < 880) by omega),
      if_pos h1]
  rw [if_neg h1]
  by_cases h2 : j < 736
  · rw [if_pos h2, if_pos (show 720 ≤ j ∧ j < 736 by omega)]
  rw [if_neg h2, if_neg (show ¬ (720 ≤ j ∧ j < 736) by omega)]
  by_cases h3 : j < 864
  · rw [if_pos h3, if_neg (show ¬ (864 ≤ j ∧ j < 880) by omega), if_neg h1, if_pos h3]
  rw [if_neg h3]
  by_cases h4 : j < 880
  · rw [if_pos h4, if_pos (show 864 ≤ j ∧ j < 880 by omega)]
  · rw [if_neg h4, if_neg (show ¬ (864 ≤ j ∧ j < 880) by omega), if_neg h1, if_neg h3]
theorem zeros_win (t : Nat) (ht : t + 8 ≤ 16) : window (zeros 16) t 8 = zeros 8 := window_zeros _ _ _ ht
theorem hdr_win (S1 C S2 : List UInt8) (h1 : S1.length = 16) (hC : C.length = 4) (h2 : S2.length = 16)
    (o : Nat) (ho : o % 8 = 0) (ho' : o + 8 ≤ 176) :
    window (S1 ++ (zeros 16 ++ (C ++ (zeros 108 ++ (S2 ++ zeros 16))))) o 8 =
      if o < 16 then window S1 o 8 else if o = 32 then C ++ zeros 4
      else if 144 ≤ o ∧ o < 160 then window S2 (o - 144) 8 else zeros 8 := by
  by_cases a : o < 16
  · rw [if_pos a, window_append_left _ _ _ _ (by omega)]
  rw [if_neg a, window_append_right _ _ _ _ (by omega), h1]
  by_cases b : o < 32
  · rw [window_append_left _ _ _ _ (by rw [zeros_len]; omega), window_zeros _ _ _ (by omega), if_neg (by omega),
      if_neg (by omega)]
  rw [window_append_right _ _ _ _ (by rw [zeros_len]; omega), zeros_len]
  by_cases c : o = 32
  · subst c
    rw [if_pos rfl]
    show ((C ++ (zeros 108 ++ (S2 ++ zeros 16))).drop (32 - 16 - 16)).take 8 = C ++ zeros 4
    rw [show 32 - 16 - 16 = 0 from rfl, List.drop_zero, List.take_append,
      List.take_of_length_le (by omega), hC, List.take_append_of_le_length (by rw [zeros_len]; omega)]
    simp [zeros, List.take_replicate]
  rw [if_neg c, window_append_right _ _ _ _ (by omega), hC]
  by_cases d : o < 144
  · rw [window_append_left _ _ _ _ (by rw [zeros_len]; omega), window_zeros _ _ _ (by omega), if_neg (by omega)]
  rw [window_append_right _ _ _ _ (by rw [zeros_len]; omega), zeros_len]
  by_cases e : o < 160
  · rw [if_pos ⟨by omega, e⟩, window_append_left _ _ _ _ (by omega), show o - 16 - 16 - 4 - 108 = o - 144 by omega]
  · rw [if_neg (by omega), window_append_right _ _ _ _ (by omega), h2, window_zeros _ _ _ (by omega)]
end regionsplit
/-- Region 0 is followed by 16 zero bytes (`wctBytes` offsets 8064..8080). -/
theorem win_region0_tail (N : HashOutput) (w : WCT9.Witness) (t : Nat) (ht : t + 8 ≤ 16) :
    window (ClaudeWCT.W9.T3M.witList N w) (8240 + t) 8 = zeros 8 := by
  rw [ClaudeWCT.W9.T3M.witList_split, window_append_left _ _ _ _ (by
      simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega),
    window_append_left _ _ _ _ (by simp only [List.length_append, headerBytes_length, wctBytes_length]; omega),
    window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    show 8240 + t - 176 = 896 * (8 - (0 : WCT9.Coord).val) + (896 + t) by simp; omega]
  have hidx : ((List.finRange 9).reverse[8 - (0 : WCT9.Coord).val]'(by simp)) = 0 := by decide
  have key := window_flatMap (List.finRange 9).reverse (regionCell N w.signature) (8 - (0 : WCT9.Coord).val)
    (by simp) (896 + t) 8 (by rw [hidx, regionCell_length]; unfold regionLen; simp; omega)
  simp only [regionCell_length] at key
  rw [wct_prefix, hidx] at key
  rw [ClaudeWCT.W9.T3M.wctBytes_eq, key]
  unfold regionCell
  rw [if_pos (show (0 : WCT9.Coord).val = 0 from rfl), window_append_right _ _ _ _ (by
    rw [regionBytes_length _ _ _ _ (ClaudeWCT.W9.T3M.prevSibL_length _ _ _) (ClaudeWCT.W9.T3M.prevSibZ_length _ _ _)];
    omega), regionBytes_length _ _ _ _ (ClaudeWCT.W9.T3M.prevSibL_length _ _ _)
      (ClaudeWCT.W9.T3M.prevSibZ_length _ _ _), show 896 + t - 896 = t by omega]
  exact window_zeros _ _ _ ht
theorem prevSibL_of (N : HashOutput) (sig : WCT9.Signature) (k : Nat) (h1 : 1 ≤ k) (h9 : k < 9) :
    ClaudeWCT.W9.T3M.prevSibL N sig k =
      if (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((sig.openings ⟨k - 1, by omega⟩).path 6)
      else zeros 16 := by
  unfold ClaudeWCT.W9.T3M.prevSibL
  rw [if_neg (by omega)]
  have e : (Fin.ofNat 9 (k - 1) : WCT9.Coord) = ⟨k - 1, by omega⟩ :=
    Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)])
  rw [e]
theorem prevSibZ_of (N : HashOutput) (sig : WCT9.Signature) (k : Nat) (h1 : 1 ≤ k) (h9 : k < 9) :
    ClaudeWCT.W9.T3M.prevSibZ N sig k =
      if (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((sig.openings ⟨k - 1, by omega⟩).path 6)
      else zeros 16 := by
  unfold ClaudeWCT.W9.T3M.prevSibZ
  rw [if_neg (by omega)]
  have e : (Fin.ofNat 9 (k - 1) : WCT9.Coord) = ⟨k - 1, by omega⟩ :=
    Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)])
  rw [e]
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
  have hsib := ClaudeWCT.W9.T3M.lowerPath_sib hleaf ls ctr j
  rw [ClaudeWCT.W9.T3M.lowerSibSlot_eq, ClaudeWCT.W9.T3M.pathOff_lower hlay] at hsib
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
      have hc := ClaudeWCT.W9.T3M.lowerPath_ctr hleaf ls ctr hlay
      have hr := ClaudeWCT.W9.T3M.lowerPath_rowPad hleaf ls ctr
      unfold ClaudeWCT.W9.T3M.lowerCtrSlot at hc hr
      rw [ClaudeWCT.W9.T3M.pathOff_lower hlay] at hc hr
      rw [← htop] at hc hr
      rw [show (8 : Nat) = 4 + 4 from rfl, window_split, hc,
        show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 4 =
          16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 0 from rfl,
        ← window_window' _ _ 12 0 4 (by omega), hr, window_zeros _ _ _ (by omega)]
    · rw [if_neg (by omega)]
      have hp := ClaudeWCT.W9.T3M.lowerPath_pad hleaf ls ctr (j := j.val) j.isLt (Or.inl (by omega))
      rw [ClaudeWCT.W9.T3M.pathOff_lower hlay] at hp
      rw [show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 =
        16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 0 from rfl, win8_of_16 _ _ _ (by omega), hp,
        window_zeros _ _ _ (by omega)]
  · subst h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    by_cases htop : j.val = height lay - 1
    · have hr := ClaudeWCT.W9.T3M.lowerPath_rowPad hleaf ls ctr
      unfold ClaudeWCT.W9.T3M.lowerCtrSlot at hr
      rw [ClaudeWCT.W9.T3M.pathOff_lower hlay] at hr
      rw [← htop] at hr
      rw [show 16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 40 =
          16 * (ClaudeWCT.W9.T3M.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 4 by omega,
        ← window_window' _ _ 12 4 8 (by omega), hr, window_zeros _ _ _ (by omega)]
    · have hp := ClaudeWCT.W9.T3M.lowerPath_pad hleaf ls ctr (j := j.val) j.isLt (Or.inl (by omega))
      rw [ClaudeWCT.W9.T3M.pathOff_lower hlay] at hp
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
    rw [ClaudeWCT.W9.T3M.lowerSibSlot_eq, ClaudeWCT.W9.T3M.pathOff_lower hlay]
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
    rw [ClaudeWCT.W9.T3M.pathOff_lower hlay, if_neg (by omega)]
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
theorem lvDst_eq (lay : Layer) (hl : lay.val ≠ 0) : lvDst lay.val - WIT + 832 = ClaudeWCT.W9.T3M.layerBase lay ∧
    pathTop lay.val = 16 * ClaudeWCT.W9.T3M.pathSlots lay ∧
    chDst lay.val - WIT + 832 = ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay ∧
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
/-! ### Campaign S2: the top region of the final witness (plan-placed path area, then the chains) -/
section identTop
variable (N : HashOutput) (w : WCT9.Witness)
theorem route_top_leaf (idx : Nat) : (route idx 0).1 = idx / 2 ^ 19 % 4096 := by
  unfold route; simp [height]
theorem tOff_topPlan (j leaf : Nat) : tOff j (trow j leaf) = ClaudeWCT.W9.T3M.topPlan leaf j := by
  unfold tOff trow ClaudeWCT.W9.T3M.topPlan; split <;> rfl
theorem trow_bit (j leaf : Nat) (hj : j < 12) (hl : leaf < 4096) :
    trow j leaf / 2 ^ (j % 6) % 2 = leaf / 2 ^ j % 2 := by
  unfold trow
  split
  · rename_i h; rw [Nat.mod_eq_of_lt h, ClaudeWCT.W9.T3M.top_bit_lo (leaf := leaf) h]
  · rename_i h; rw [ClaudeWCT.W9.T3M.top_bit_hi (leaf := leaf) hl (by omega) hj, show j % 6 = j - 6 by omega]
theorem tsibS_slot (j leaf : Nat) (hj : j < 12) (hl : leaf < 4096) :
    tsibS j leaf = ClaudeWCT.W9.T3M.lowerSibSlot 0 leaf j ∧
      16 * tplan j (trow j leaf) = ClaudeWCT.W9.T3M.pathOff 0 leaf j := by
  have hp := tplan_ok j (trow j leaf) hj (trow_lt j leaf)
  rw [ClaudeWCT.W9.T3M.lowerSibSlot_eq, ClaudeWCT.W9.T3M.pathOff_top, ← tOff_topPlan j leaf]
  unfold tsibS
  rw [trow_bit j leaf hj hl, sibOff_eq _ (Nat.mod_lt _ (by norm_num))]
  exact ⟨by omega, hp.1⟩
/-- The staged (V6) top windows: level `j` at `64 (11 - j)`, sibling at `sibOff`, zeros elsewhere. -/
theorem v6_block_top (leaf : Nat) (ls : LayerSignature 0) (j : Fin (height 0)) (d : Nat) (hd : d % 8 = 0)
    (hd' : d + 8 ≤ 64) :
    window (layerBytes 0 leaf ls) (64 * (height 0 - 1 - j.val) + d) 8 =
      if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) then window (bytesLE 16 (ls.path j)) 0 8
      else if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 then window (bytesLE 16 (ls.path j)) 8 8
      else zeros 8 := by
  rw [show 64 * (height 0 - 1 - j.val) + d = 64 * (height 0 - 1 - j.val) + (d - d % 16) + d % 16 by omega,
    win8_of_16 _ _ _ (by omega), layerBytes_merkle 0 leaf ls j (d - d % 16) (by omega),
    window_window' _ _ _ _ _ (by omega), show d - d % 16 + d % 16 = d by omega]
  have hbk := block_win (bytesLE 16 (ls.path j)) (bytesLE_length _ _) (decide (leaf / 2 ^ j.val % 2 = 1)) d hd hd'
  simp only [decide_eq_true_eq] at hbk
  rw [hbk]
  unfold SigGolfCandidate.T3M.sibOff
  by_cases hb : leaf / 2 ^ j.val % 2 = 1 <;> simp [hb]
/-- The final top windows (plan-placed): same content as the staged ones. -/
theorem v7_block_top {leaf : Nat} (hleaf : leaf < 2 ^ height 0) (ls : LayerSignature 0) (ctr : BitVec 32)
    (j : Fin (height 0)) (d : Nat) (hd' : d + 8 ≤ 64)
    (hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) ∨
      d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 ∨ d = 32 ∨ d = 40) :
    window (lowerPathBytes 0 leaf ls ctr) (ClaudeWCT.W9.T3M.pathOff 0 leaf j.val + d) 8 =
      if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) then window (bytesLE 16 (ls.path j)) 0 8
      else if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 then window (bytesLE 16 (ls.path j)) 8 8
      else zeros 8 := by
  have hs := sibOff_vals (leaf / 2 ^ j.val % 2)
  have hsib := ClaudeWCT.W9.T3M.lowerPath_sib hleaf ls ctr j
  rw [ClaudeWCT.W9.T3M.lowerSibSlot_eq] at hsib
  rcases hdv with h | h | h | h
  · subst h
    rw [if_pos rfl, show ClaudeWCT.W9.T3M.pathOff 0 leaf j.val + SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) =
      ClaudeWCT.W9.T3M.pathOff 0 leaf j.val + SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 0 from rfl,
      win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_pos rfl, show ClaudeWCT.W9.T3M.pathOff 0 leaf j.val +
      (SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8) = ClaudeWCT.W9.T3M.pathOff 0 leaf j.val +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 by omega, win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_neg (by omega)]
    have hp := ClaudeWCT.W9.T3M.lowerPath_pad hleaf ls ctr (j := j.val) j.isLt (Or.inr rfl)
    rw [show ClaudeWCT.W9.T3M.pathOff 0 leaf j.val + 32 = ClaudeWCT.W9.T3M.pathOff 0 leaf j.val + 32 + 0 from rfl,
      win8_of_16 _ _ _ (by omega), hp, window_zeros _ _ _ (by omega)]
  · subst h
    rw [if_neg (by omega), if_neg (by omega)]
    have hp := ClaudeWCT.W9.T3M.lowerPath_pad hleaf ls ctr (j := j.val) j.isLt (Or.inr rfl)
    rw [show ClaudeWCT.W9.T3M.pathOff 0 leaf j.val + 40 = ClaudeWCT.W9.T3M.pathOff 0 leaf j.val + 32 + 8 by omega,
      win8_of_16 _ _ _ (by omega), hp, window_zeros _ _ _ (by omega)]
theorem zone_toppath (o : Nat) (h1 : 8256 ≤ o) (h2 : o + 8 ≤ 8256 + 784) (h8 : o % 8 = 0) :
    BitVec.ofNat 64 (readLE (window (preBufferWitList N w) o 8)) =
      topPathOut (v6M N w) (WCT9.digestIndex N / 2 ^ 19 % 4096) (o - 8256) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  set leaf := (route (WCT9.digestIndex N) 0).1 with hleafdef
  have hleaf : leaf < 2 ^ height 0 := ClaudeWCT.W9.T3M.route_leaf_lt _ _
  have hl4 : leaf < 4096 := by simpa [height] using hleaf
  have hrl : WCT9.digestIndex N / 2 ^ 19 % 4096 = leaf := by rw [hleafdef, route_top_leaf]
  rw [hrl]
  have hps : 16 * ClaudeWCT.W9.T3M.pathSlots 0 = 784 := rfl
  have hw7 := preBufferWinLayer N w 0 (o - 8256) 8 (by simp [ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
  rw [show ClaudeWCT.W9.T3M.layerBase 0 + (o - 8256) = o by simp [ClaudeWCT.W9.T3M.layerBase]; omega] at hw7
  rw [hw7]
  unfold layerRegion
  rw [window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.T3M.lowerPathBytes_length, hps]; omega)]
  rw [← hleafdef]
  unfold topPathOut
  cases h : (List.range 12).find? (fun j => decide (tvHit leaf j (o - 8256))) with
  | none =>
    simp only
    have hz : ∀ i ∈ List.range 8, ClaudeWCT.W9.T3M.lowerPathByte 0 leaf (w.signature.layers 0)
        (w.counters (Fin.ofNat 4 ((0 : Layer).val - 1))) (o - 8256 + i) = (fun _ => (0 : UInt8)) i := by
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [ClaudeWCT.W9.T3M.lowerPathByte_free (w.signature.layers 0) _ (fun j => by
        have hn := List.find?_eq_none.mp h j.val (List.mem_range.mpr (by simpa [height] using j.isLt))
        have h' : ¬ tvHit leaf j.val (o - 8256) := fun hh => hn (decide_eq_true hh)
        have hj12 : j.val < 12 := by simpa [height] using j.isLt
        have hs := (tsibS_slot j.val leaf hj12 hl4).1
        have hb := tsib_bounds j.val leaf hj12
        unfold tvHit at h'
        unfold tpadS at hb h'
        omega)]
      rw [if_neg (by simp)]
    unfold lowerPathBytes
    rw [ClaudeWCT.W9.T3M.window_map_range _ _ _ _ (by rw [hps]; omega), List.map_congr_left hz]
    simp [List.map_const']
    rfl
  | some j =>
    simp only
    obtain ⟨hj, hp'⟩ := lvs_find_some h
    have hh : tvHit leaf j (o - 8256) := of_decide_eq_true hp'
    obtain ⟨hs1, hs2⟩ := tsibS_slot j leaf hj hl4
    have hb := tsib_bounds j leaf hj
    have hbit := trow_bit j leaf hj hl4
    have hbl : leaf / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hso := sibOff_eq _ hbl
    unfold tvHit at hh
    unfold tpadS at hh hb
    unfold tsibS at hh hb hs1
    rw [hbit] at hh hb
    set d := o - 8256 - 16 * tplan j (trow j leaf) with hd
    have hh0 : height 0 = 12 := rfl
    have hl0 : layOffV6 0 = 0 := rfl
    have hd8 : d % 8 = 0 := by omega
    have hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, by simp [height]; omega⟩ : Fin (height 0)).val % 2) ∨
        d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, by simp [height]; omega⟩ : Fin (height 0)).val % 2) + 8 ∨
        d = 32 ∨ d = 40 := by
      simp only; rw [hso]; omega
    have e7 := v7_block_top hleaf (w.signature.layers 0) (w.counters (Fin.ofNat 4 ((0 : Layer).val - 1)))
      ⟨j, by simp [height]; omega⟩ d (by omega) hdv
    simp only at e7
    rw [show o - 8256 = ClaudeWCT.W9.T3M.pathOff 0 leaf j + d by omega, e7,
      show tvSrc j - SNAP2 + WIT + d = WIT + (8136 + layOffV6 0 + (64 * (height 0 - 1 - j) + d)) by
        have hh0 : height 0 = 12 := rfl
        have hl0 : layOffV6 0 = 0 := rfl
        unfold tvSrc; rw [hh0, hl0]; omega,
      v6M_eq N w _ (by omega) (by simp [layOffV6, height]; omega), v6_layer N w 0 _ (by simp [height, chainCount]; omega)]
    unfold layerRegionV6
    rw [if_pos (show ((0 : Layer).val = 0) from rfl), ← hleafdef]
    have e6 := v6_block_top leaf (w.signature.layers 0) ⟨j, by simp [height]; omega⟩ d (by omega) (by omega)
    simp only at e6
    rw [e6]
theorem zone_topch (o : Nat) (h1 : 8256 + 784 ≤ o) (h2 : o + 8 ≤ 8256 + 4240) (h8 : o % 8 = 0) :
    BitVec.ofNat 64 (readLE (window (preBufferWitList N w) o 8)) = v6M N w (WIT + (o - 832) + 696) := by
  have hW : WIT = 0x800 := rfl
  have hps : 16 * ClaudeWCT.W9.T3M.pathSlots 0 = 784 := rfl
  have hw7 := preBufferWinLayer N w 0 (o - 8256) 8 (by simp [ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
  rw [show ClaudeWCT.W9.T3M.layerBase 0 + (o - 8256) = o by simp [ClaudeWCT.W9.T3M.layerBase]; omega] at hw7
  rw [hw7]
  unfold layerRegion
  rw [window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.T3M.lowerPathBytes_length, hps]; omega),
    ClaudeWCT.W9.T3M.lowerPathBytes_length, hps, window_drop,
    show WIT + (o - 832) + 696 = WIT + (8136 + layOffV6 0 + (64 * height 0 + (o - 8256 - 784))) by
        simp [layOffV6, height]; omega,
    v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6, height]; omega),
    v6_layer N w 0 _ (by simp [height, chainCount]; omega)]
  unfold layerRegionV6
  rw [if_pos (show ((0 : Layer).val = 0) from rfl)]
end identTop
section ident2
variable (N : HashOutput) (w : WCT9.Witness)
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
        rw [ClaudeWCT.W9.T3M.lowerSibSlot_eq, ClaudeWCT.W9.T3M.pathOff_lower hL]
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
      have hpbnd := ClaudeWCT.W9.T3M.lower_win_bound L leaf hleaf j hj
      have hsbnd := ClaudeWCT.W9.T3M.lower_sib_bound L leaf hleaf j hj
      rw [ClaudeWCT.W9.T3M.pathOff_lower hL] at hpbnd
      rw [ClaudeWCT.W9.T3M.lowerSibSlot_eq, ClaudeWCT.W9.T3M.pathOff_lower hL] at hsbnd
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
/-! ### Nested FTS (r1-1): the final assembly against the witness (header and regions) -/
section model
variable (N : HashOutput) (w : WCT9.Witness)
/-- Hold word `j` of coordinate `c` in the honest run: the halves of its top sibling, then the flag `1 - bit6`. -/
def holdModel (c j : Nat) : Word :=
  if h : c < 9 then
    if j = 0 then BitVec.ofNat 64 (readLE (window (bytesLE 16 ((w.signature.openings ⟨c, h⟩).path 6)) 0 8))
    else if j = 1 then BitVec.ofNat 64 (readLE (window (bytesLE 16 ((w.signature.openings ⟨c, h⟩).path 6)) 8 8))
    else BitVec.ofNat 64 (1 - (WCT9.child N ⟨c, h⟩).val / 2 ^ 6 % 2)
  else 0
/-- Model of the memory entering the second pass: the staging layout at `WIT` and the hold words. -/
def vM (B : Nat) : Word :=
  if 0x380000 ≤ B ∧ B < 0x380000 + 288 then holdModel N w ((B - 0x380000) / 32) ((B - 0x380000) % 32 / 8)
  else v6M N w B
theorem vM_wit (x : Nat) (hx : x < 8 * 2729) : vM N w (WIT + x) = v6M N w (WIT + x) := by
  have hW : WIT = 0x800 := rfl
  unfold vM; rw [if_neg (by omega)]
theorem vM_hold (c : Nat) (hc : c < 9) (j : Nat) (hj : j < 3) :
    vM N w (Compact.holdAt c + 8 * j) = holdModel N w c j := by
  have hH : Compact.holdAt c = 0x380000 + 32 * c := rfl
  unfold vM
  rw [if_pos (by omega), show (Compact.holdAt c + 8 * j - 0x380000) / 32 = c by omega,
    show (Compact.holdAt c + 8 * j - 0x380000) % 32 / 8 = j by omega]
end model
theorem R_eval (M : Nat → Word) (A : Nat) (h1 : WOUT ≤ A) (h2 : A < 9472) (h8 : A % 8 = 0) :
    regsMem (ctrMem (zMem (snapMem M))) 9 A =
      if 1392 ≤ A ∧ A < 9456 then
        M (WIT + (64 + 896 * ((9455 - A) / 896) + (A - (8560 - 896 * ((9455 - A) / 896)))))
      else if 1248 ≤ A ∧ A < 1264 then M (WIT + (32 + (A - 1248))) else 0 := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0x4c0 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold regsMem
  by_cases hr : 1392 ≤ A ∧ A < 9456
  · rw [if_pos (show 0 < 9 ∧ 9456 - 896 * 9 ≤ A ∧ A < 9456 ∧ A % 8 = 0 by omega), if_pos hr]
    unfold ctrMem zMem snapMem
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show SNAP2 + 64 + 896 * ((9455 - A) / 896) + (A - (8560 - 896 * ((9455 - A) / 896))) - SNAP2 =
        64 + 896 * ((9455 - A) / 896) + (A - (8560 - 896 * ((9455 - A) / 896))) by omega]
  · rw [if_neg (show ¬ (0 < 9 ∧ 9456 - 896 * 9 ≤ A ∧ A < 9456 ∧ A % 8 = 0) by omega), if_neg hr]
    unfold ctrMem
    by_cases hc : 1248 ≤ A ∧ A < 1264
    · rw [if_pos (show 1248 ≤ A ∧ A < 1248 + 8 * 2 ∧ (A - 1248) % 8 = 0 by omega), if_pos hc]
      unfold zMem snapMem
      rw [if_neg (by omega), if_pos (by omega), show SNAP2 + 32 + (A - 1248) - SNAP2 = 32 + (A - 1248) by omega]
    · rw [if_neg (show ¬ (1248 ≤ A ∧ A < 1248 + 8 * 2 ∧ (A - 1248) % 8 = 0) by omega), if_neg hc]
      unfold zMem
      rw [if_pos (by omega)]
theorem R_hold (M : Nat → Word) (c : Nat) (hc : c < 9) (j : Nat) (hj : j < 24) :
    regsMem (ctrMem (zMem (snapMem M))) 9 (Compact.holdAt c + j) = M (Compact.holdAt c + j) := by
  have hH : Compact.holdAt c = 0x380000 + 32 * c := rfl
  have hWO : WOUT = 0x4c0 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  unfold regsMem ctrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem plMem_at (M : Nat → Word) (Q : Nat) (hQ : Q ≤ 9) (A c0 : Nat)
    (hA : ∀ c < Q, c ≠ c0 → A < hdst c ∨ hdst c + 160 ≤ A) :
    plMem M Q A = if c0 < Q then
      (if A = hslot M c0 + 8 then M (Compact.holdAt c0 + 8) else if A = hslot M c0 then M (Compact.holdAt c0)
        else M A) else M A := by
  induction Q with
  | zero => rw [if_neg (Nat.not_lt_zero _)]; rfl
  | succ Q ih =>
    have ih' := ih (by omega) (fun c hc hne => hA c (by omega) hne)
    show (if A = hslot M Q + 8 then M (Compact.holdAt Q + 8) else if A = hslot M Q then M (Compact.holdAt Q)
      else plMem M Q A) = _
    rw [ih']
    by_cases hq : Q = c0
    · subst hq
      rw [if_pos (show Q < Q + 1 by omega), if_neg (show ¬ Q < Q by omega)]
    · have hb := hslot_bound M Q
      have hw := hA Q (by omega) hq
      rw [if_neg (show ¬ A = hslot M Q + 8 by omega), if_neg (show ¬ A = hslot M Q by omega)]
      by_cases hlt : c0 < Q
      · rw [if_pos hlt, if_pos (show c0 < Q + 1 by omega)]
      · rw [if_neg hlt, if_neg (show ¬ c0 < Q + 1 by omega)]
theorem ofNat_readLE_zeros8 : BitVec.ofNat 64 (readLE (zeros 8)) = 0 := by decide
theorem hdrV5_ctr (w : WCT9.Witness) (t : Nat) (ht : t = 0 ∨ t = 8) :
    window (headerBytesV5 w) (32 + t) 8 = if t = 0 then bytesLE 4 (w.counters 3) ++ zeros 4 else zeros 8 := by
  rw [show headerBytesV5 w = (bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12) ++
      (bytesLE 4 (w.counters 3) ++ zeros 28) by simp only [headerBytesV5, List.append_assoc],
    window_append_right _ _ _ _ (by simp [bytesLE_length, zeros]),
    show (bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12).length = 32 by
      simp [bytesLE_length, zeros], show 32 + t - 32 = t by omega]
  rcases ht with rfl | rfl
  · rw [if_pos rfl]
    show ((bytesLE 4 (w.counters 3) ++ zeros 28).drop 0).take 8 = bytesLE 4 (w.counters 3) ++ zeros 4
    rw [List.drop_zero, List.take_append, List.take_of_length_le (by rw [bytesLE_length]; omega),
      bytesLE_length]
    simp [zeros, List.take_replicate]
  · rw [if_neg (by decide), window_append_right _ _ _ _ (by rw [bytesLE_length]; omega), bytesLE_length]
    exact window_zeros _ _ _ (by omega)
section final
variable (N : HashOutput) (w : WCT9.Witness)
theorem hslot_model (c : Nat) (hc : c < 9) :
    hslot (regsMem (ctrMem (zMem (snapMem (vM N w)))) 9) c =
      hdst c + 144 * (1 - (WCT9.child N ⟨c, hc⟩).val / 2 ^ 6 % 2) := by
  have hb : (WCT9.child N ⟨c, hc⟩).val / 2 ^ 6 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold hslot
  rw [R_hold _ c hc 16 (by omega), show Compact.holdAt c + 16 = Compact.holdAt c + 8 * 2 by omega,
    vM_hold N w c hc 2 (by omega)]
  unfold holdModel
  rw [dif_pos hc, if_neg (show ¬ (2 : Nat) = 0 by decide), if_neg (show ¬ (2 : Nat) = 1 by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega)]
theorem R_holdw (c : Nat) (hc : c < 9) (t : Nat) (ht : t < 2) :
    regsMem (ctrMem (zMem (snapMem (vM N w)))) 9 (Compact.holdAt c + 8 * t) =
      BitVec.ofNat 64 (readLE (window (bytesLE 16 ((w.signature.openings ⟨c, hc⟩).path 6)) (8 * t) 8)) := by
  rw [R_hold _ c hc (8 * t) (by omega), vM_hold N w c hc t (by omega)]
  unfold holdModel
  rw [dif_pos hc]
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
  · rw [if_pos rfl]
  · rw [if_neg (show ¬ (1 : Nat) = 0 by decide), if_pos rfl]
theorem R_region (k : Nat) (hk : k < 9) (j : Nat) (hj : j % 8 = 0) (hj' : j + 8 ≤ 896) :
    regsMem (ctrMem (zMem (snapMem (vM N w)))) 9 (8560 - 896 * k + j) =
      BitVec.ofNat 64 (readLE (window (regionBytes (WCT9.child N ⟨k, hk⟩).val (w.signature.openings ⟨k, hk⟩)
        (zeros 16) (zeros 16)) j 8)) := by
  have hWO : WOUT = 0x4c0 := rfl
  rw [R_eval _ _ (by omega) (by omega) (by omega),
    if_pos (show 1392 ≤ 8560 - 896 * k + j ∧ 8560 - 896 * k + j < 9456 by omega),
    show (9455 - (8560 - 896 * k + j)) / 896 = k by omega,
    show 8560 - 896 * k + j - (8560 - 896 * k) = j by omega,
    vM_wit N w _ (by omega), v6M_eq N w _ (by omega) (by omega), v6_region N w k hk j hj']
theorem R_ctr (t : Nat) (ht : t = 0 ∨ t = 8) :
    regsMem (ctrMem (zMem (snapMem (vM N w)))) 9 (1248 + t) =
      BitVec.ofNat 64 (readLE (if t = 0 then bytesLE 4 (w.counters 3) ++ zeros 4 else zeros 8)) := by
  have hWO : WOUT = 0x4c0 := rfl
  rw [R_eval _ _ (by omega) (by omega) (by omega),
    if_neg (show ¬ (1392 ≤ 1248 + t ∧ 1248 + t < 9456) by omega),
    if_pos (show 1248 ≤ 1248 + t ∧ 1248 + t < 1264 by omega), show 1248 + t - 1248 = t by omega,
    vM_wit N w _ (by omega), v6M_eq N w _ (by omega) (by omega), v6_head N w _ (by omega), hdrV5_ctr w t ht]
theorem R_zero (A : Nat) (h1 : WOUT ≤ A) (h2 : A < 9472) (h8 : A % 8 = 0) (hn1 : ¬ (1392 ≤ A ∧ A < 9456))
    (hn2 : ¬ (1248 ≤ A ∧ A < 1264)) : regsMem (ctrMem (zMem (snapMem (vM N w)))) 9 A = 0 := by
  rw [R_eval _ _ h1 h2 h8, if_neg hn1, if_neg hn2]
set_option maxHeartbeats 2000000 in
/-- Nested FTS (r1-1): every word of the header and of the nine regions (offsets below 8256 from `WOUT`) after
the final assembly is the corresponding word of the witness. -/
theorem wct_words (o : Nat) (ho : o < 8256) (h8 : o % 8 = 0) :
    stMem (vM N w) (WOUT + o) = BitVec.ofNat 64 (readLE (window (preBufferWitList N w) o 8)) := by
  have hWO : WOUT = 0x4c0 := rfl
  rw [preBufferPrefix N w o 8 (by omega)]
  unfold stMem
  by_cases hh : o < 176
  · -- the header (coordinate 8's top sibling and the L3 counter)
    have hb : (WCT9.child N 8).val / 2 ^ 6 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have e8 : (⟨8, by omega⟩ : WCT9.Coord) = 8 := rfl
    have hs := hslot_model N w 8 (by omega)
    rw [e8] at hs
    have hd8 : hdst 8 = 1216 := rfl
    rw [plMem_at _ 9 le_rfl _ 8 (fun c hc hne => by unfold hdst; omega), if_pos (show 8 < 9 by omega), hs, hd8,
      ClaudeWCT.W9.T3M.win_header N w o 8 (by omega), ClaudeWCT.W9.T3M.headerBytes_eq,
      hdr_win _ _ _ (ClaudeWCT.W9.T3M.ite_slot_length _ _) (bytesLE_length _ _) (ClaudeWCT.W9.T3M.ite_slot_length _ _)
        o h8 (by omega)]
    have hw1 := R_holdw N w 8 (by omega) 1 (by omega)
    have hw0 := R_holdw N w 8 (by omega) 0 (by omega)
    rw [e8] at hw1 hw0
    simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at hw1 hw0
    by_cases e1 : WOUT + o = 1216 + 144 * (1 - (WCT9.child N 8).val / 2 ^ 6 % 2) + 8
    · rw [if_pos e1, hw1]
      rcases (show (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 ∨ (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 by omega) with hb | hb
      · have h152 : o = 152 := by omega
        simp only [h152, hb, show ¬ (152 : Nat) < 16 by decide, show ¬ (152 : Nat) = 32 by decide,
          show (144 ≤ (152 : Nat) ∧ (152 : Nat) < 160) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte, show (152 : Nat) - 144 = 8 from rfl]
      · have h8' : o = 8 := by omega
        simp only [h8', hb, show (8 : Nat) < 16 by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
    rw [if_neg e1]
    by_cases e0 : WOUT + o = 1216 + 144 * (1 - (WCT9.child N 8).val / 2 ^ 6 % 2)
    · rw [if_pos e0, hw0]
      rcases (show (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 ∨ (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 by omega) with hb | hb
      · have h144 : o = 144 := by omega
        simp only [h144, hb, show ¬ (144 : Nat) < 16 by decide, show ¬ (144 : Nat) = 32 by decide,
          show (144 ≤ (144 : Nat) ∧ (144 : Nat) < 160) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte, show (144 : Nat) - 144 = 0 from rfl]
      · have h0 : o = 0 := by omega
        simp only [h0, hb, show (0 : Nat) < 16 by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
    rw [if_neg e0]
    by_cases hc : o = 32 ∨ o = 40
    · rcases hc with hc | hc
      · rw [show WOUT + o = 1248 + 0 by omega, R_ctr N w 0 (Or.inl rfl)]
        simp only [hc, show ¬ (32 : Nat) < 16 by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
      · rw [show WOUT + o = 1248 + 8 by omega, R_ctr N w 8 (Or.inr rfl)]
        simp only [hc, show ¬ (40 : Nat) < 16 by decide, show ¬ (40 : Nat) = 32 by decide,
          show ¬ (144 ≤ (40 : Nat) ∧ (40 : Nat) < 160) by decide, show ¬ (8 : Nat) = 0 by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
    · rw [R_zero N w _ (by omega) (by omega) (by omega) (by omega) (by omega), eq_comm]
      rcases (show (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 ∨ (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 by omega) with hb | hb
      · by_cases a : o < 16
        · simp only [a, hb, show ¬ ((0 : Nat) = 1) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
          rw [window_zeros _ _ _ (by omega), ofNat_readLE_zeros8]
        · have hn : ¬ (o = 32) := by omega
          have hm : ¬ (144 ≤ o ∧ o < 160) := by omega
          simp only [a, hn, hm, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte, ofNat_readLE_zeros8]
      · by_cases m : 144 ≤ o ∧ o < 160
        · have a : ¬ o < 16 := by omega
          have hn : ¬ (o = 32) := by omega
          simp only [a, hn, m, hb, show ¬ ((1 : Nat) = 0) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
          rw [window_zeros _ _ _ (by omega), ofNat_readLE_zeros8]
        · have a : ¬ o < 16 := by omega
          have hn : ¬ (o = 32) := by omega
          simp only [a, hn, m, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte, ofNat_readLE_zeros8]
  by_cases hz : 8240 ≤ o
  · -- the 16 zero bytes after region 0
    rw [plMem_at _ 9 le_rfl _ 9 (fun c hc _ => by unfold hdst; omega), if_neg (show ¬ 9 < 9 by omega),
      R_zero N w _ (by omega) (by omega) (by omega) (by omega) (by omega),
      show o = 8240 + (o - 8240) by omega, win_region0_tail N w _ (by omega), ofNat_readLE_zeros8]
  -- region k at offset j
  obtain ⟨k, j, hk, hj, rfl⟩ : ∃ k j, k < 9 ∧ j < 896 ∧ o = 176 + 896 * (8 - k) + j :=
    ⟨8 - (o - 176) / 896, (o - 176) % 896, by omega, Nat.mod_lt _ (by norm_num), by omega⟩
  have hj8 : j % 8 = 0 := by omega
  have hA : WOUT + (176 + 896 * (8 - k) + j) = 8560 - 896 * k + j := by omega
  rw [show 176 + 896 * (8 - k) + j = regionBase (⟨k, hk⟩ : WCT9.Coord).val + j by
      unfold regionBase; rfl,
    ClaudeWCT.W9.T3M.win_region N w ⟨k, hk⟩ j 8 (by omega),
    region_win8 _ _ _ _ (ClaudeWCT.W9.T3M.prevSibL_length _ _ _) (ClaudeWCT.W9.T3M.prevSibZ_length _ _ _) j hj8
      (by omega), show regionBase (⟨k, hk⟩ : WCT9.Coord).val + j = 176 + 896 * (8 - k) + j by unfold regionBase; rfl,
    hA]
  by_cases hp : 1 ≤ k ∧ 720 ≤ j ∧ j < 880
  · -- the pads of region k may hold coordinate k - 1's top sibling
    have hs := hslot_model N w (k - 1) (by omega)
    have hdk : hdst (k - 1) = 9280 - 896 * k := by unfold hdst; omega
    rw [plMem_at _ 9 le_rfl _ (k - 1) (fun c hc hne => by unfold hdst; omega), if_pos (show k - 1 < 9 by omega),
      hs, hdk, show (⟨k, hk⟩ : WCT9.Coord).val = k from rfl, prevSibL_of N w.signature k hp.1 hk,
      prevSibZ_of N w.signature k hp.1 hk]
    have hw1 := R_holdw N w (k - 1) (by omega) 1 (by omega)
    have hw0 := R_holdw N w (k - 1) (by omega) 0 (by omega)
    simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at hw1 hw0
    have hb : (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases e1 : 8560 - 896 * k + j = 9280 - 896 * k + 144 * (1 - (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2) + 8
    · rw [if_pos e1, hw1]
      rcases (show (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 0 ∨
          (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 1 by omega) with hb' | hb'
      · have hj' : j = 872 := by omega
        simp only [hj', hb', show ¬ (720 ≤ (872 : Nat) ∧ (872 : Nat) < 736) by decide,
          show (864 ≤ (872 : Nat) ∧ (872 : Nat) < 880) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte, show (872 : Nat) - 864 = 8 from rfl]
      · have hj' : j = 728 := by omega
        simp only [hj', hb', show (720 ≤ (728 : Nat) ∧ (728 : Nat) < 736) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte,
          show (728 : Nat) - 720 = 8 from rfl]
    rw [if_neg e1]
    by_cases e0 : 8560 - 896 * k + j = 9280 - 896 * k + 144 * (1 - (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2)
    · rw [if_pos e0, hw0]
      rcases (show (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 0 ∨
          (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 1 by omega) with hb' | hb'
      · have hj' : j = 864 := by omega
        simp only [hj', hb', show ¬ (720 ≤ (864 : Nat) ∧ (864 : Nat) < 736) by decide,
          show (864 ≤ (864 : Nat) ∧ (864 : Nat) < 880) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte, show (864 : Nat) - 864 = 0 from rfl]
      · have hj' : j = 720 := by omega
        simp only [hj', hb', show (720 ≤ (720 : Nat) ∧ (720 : Nat) < 736) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte,
          show (720 : Nat) - 720 = 0 from rfl]
    rw [if_neg e0, R_region N w k hk j hj8 (by omega),
      region_win8 _ _ _ _ (ClaudeWCT.W9.T3M.zeros_len 16) (ClaudeWCT.W9.T3M.zeros_len 16) j hj8 (by omega)]
    rcases (show (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 0 ∨
        (WCT9.child N ⟨k - 1, by omega⟩).val / 2 ^ 6 % 2 = 1 by omega) with hb' | hb'
    · have hn : ¬ (864 ≤ j ∧ j < 880) := by omega
      simp only [hb', hn, show ¬ ((0 : Nat) = 1) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
    · have hn : ¬ (720 ≤ j ∧ j < 736) := by omega
      simp only [hb', hn, show ¬ ((1 : Nat) = 0) by decide, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
  · -- no top sibling lands in this word
    rw [plMem_at _ 9 le_rfl _ 9 (fun c hc _ => by unfold hdst; omega), if_neg (show ¬ 9 < 9 by omega),
      R_region N w k hk j hj8 (by omega),
      region_win8 _ _ _ _ (ClaudeWCT.W9.T3M.zeros_len 16) (ClaudeWCT.W9.T3M.zeros_len 16) j hj8 (by omega)]
    by_cases hpad : (720 ≤ j ∧ j < 736) ∨ (864 ≤ j ∧ j < 880)
    · have k0 : k = 0 := by omega
      subst k0
      have hL : ClaudeWCT.W9.T3M.prevSibL N w.signature (⟨0, hk⟩ : WCT9.Coord).val = zeros 16 := by
        unfold ClaudeWCT.W9.T3M.prevSibL; rw [if_pos rfl]
      have hZ : ClaudeWCT.W9.T3M.prevSibZ N w.signature (⟨0, hk⟩ : WCT9.Coord).val = zeros 16 := by
        unfold ClaudeWCT.W9.T3M.prevSibZ; rw [if_pos rfl]
      rw [hL, hZ]
    · have n1 : ¬ (720 ≤ j ∧ j < 736) := by omega
      have n2 : ¬ (864 ≤ j ∧ j < 880) := by omega
      simp only [n1, n2, and_self, and_true, true_and, eq_self_iff_true, ↓reduceIte]
end final
set_option maxHeartbeats 2000000 in
theorem compact2_words (N : HashOutput) (w : WCT9.Witness) (i : Nat) (hi : i < 2724) :
    (wordsOf (preBufferWitList N w)).getD i 0 =
      if 8 * i < 8256 then stMem (vM N w) (WOUT + 8 * i)
      else out2old (v6M N w) (WCT9.digestIndex N) (8 * i - 832) := by
  rw [wordsOf_getD' _ 2724 (by rw [preBufferWitList_length]) i hi]
  by_cases hw : 8 * i < 8256
  · rw [if_pos hw, wct_words N w (8 * i) hw (by omega)]
  rw [if_neg hw]
  unfold out2old
  rw [if_neg (show ¬ 8 * i - 832 < 64 by omega), if_neg (show ¬ 8 * i - 832 < 7424 by omega)]
  by_cases htp : 8 * i - 832 < 8208
  · rw [if_pos htp, zone_toppath N w (8 * i) (by omega) (by omega) (by omega),
      show 8 * i - 8256 = 8 * i - 832 - 7424 by omega]
  rw [if_neg htp]
  by_cases htop : 8 * i - 832 < 11664
  · rw [if_pos htop]; exact zone_topch N w (8 * i) (by omega) (by omega) (by omega)
  rw [if_neg htop]
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  by_cases hlow : 8 * i - 832 < 20928
  · rw [if_pos hlow]
    have hW : WIT = 0x800 := rfl
    have key : ∀ L : Layer, L.val ≠ 0 → zoneLay (8 * i - 832) = L.val → ClaudeWCT.W9.T3M.layerBase L ≤ 8 * i →
        8 * i + 8 ≤ ClaudeWCT.W9.T3M.layerBase L + (16 * ClaudeWCT.W9.T3M.pathSlots L + 64 * chainCount L) →
        BitVec.ofNat 64 (readLE (window (preBufferWitList N w) (8 * i) 8)) =
          (if 8 * i - 832 - (lvDst (zoneLay (8 * i - 832)) - WIT) < pathTop (zoneLay (8 * i - 832)) then
            pathOut (v6M N w) (zoneLay (8 * i - 832)) (lroute (zoneLay (8 * i - 832)) (WCT9.digestIndex N))
              (8 * i - 832 - (lvDst (zoneLay (8 * i - 832)) - WIT))
          else v6M N w (chSrc (zoneLay (8 * i - 832)) - SNAP2 + WIT +
            (8 * i - 832 - (chDst (zoneLay (8 * i - 832)) - WIT)))) := by
      intro L hL hz h1 h2
      obtain ⟨e1, e2, e3, e4⟩ := lvDst_eq L hL
      have hb := ClaudeWCT.W9.T3M.layerBase_ge L
      have e1' : lvDst L.val - WIT = ClaudeWCT.W9.T3M.layerBase L - 832 := by omega
      have e3' : chDst L.val - WIT = ClaudeWCT.W9.T3M.layerBase L - 832 + 16 * ClaudeWCT.W9.T3M.pathSlots L := by
        omega
      rw [hz, e1', e2, e3', e4, zone_low N w L hL (8 * i) h1 h2 (by omega),
        show 8 * i - 832 - (ClaudeWCT.W9.T3M.layerBase L - 832) = 8 * i - ClaudeWCT.W9.T3M.layerBase L by omega]
      by_cases hc : 8 * i - ClaudeWCT.W9.T3M.layerBase L < 16 * ClaudeWCT.W9.T3M.pathSlots L
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, show 8136 + layOffV6 L + 64 * height L + (8 * i - ClaudeWCT.W9.T3M.layerBase L -
          16 * ClaudeWCT.W9.T3M.pathSlots L) + WIT = 8136 + layOffV6 L + 64 * height L + WIT +
          (8 * i - 832 - (ClaudeWCT.W9.T3M.layerBase L - 832 + 16 * ClaudeWCT.W9.T3M.pathSlots L)) by omega]
    by_cases hz1 : 8 * i - 832 < 14784
    · exact key 1 (by decide) (by unfold zoneLay; rw [if_pos hz1]; rfl) (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
        (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
    · by_cases hz2 : 8 * i - 832 < 17856
      · exact key 2 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_pos hz2]; rfl)
          (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
          (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
      · exact key 3 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_neg hz2]; rfl)
          (by simp [ClaudeWCT.W9.T3M.layerBase]; omega)
          (by simp [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, chainCount]; omega)
  · rw [if_neg hlow]
    have hrho : ∀ t, t + 8 ≤ 16 → window (preBufferWitList N w) (21760 + t) 8 = window (witListV6 N w) t 8 :=
        fun t ht => by
      rw [preBufferWinTail N w _ _ (by omega), v6_head N w _ (by omega)]
      unfold tailBytes headerBytesV5
      simp only [List.append_assoc]
      rw [window_append_left _ _ _ _ (by simp [bytesLE_length]; omega),
        window_append_left _ _ _ _ (by simp [bytesLE_length]; omega)]
    rcases (show 8 * i = 21760 ∨ 8 * i = 21768 ∨ 8 * i = 21776 ∨ 8 * i = 21784 by omega) with h | h | h | h
    · rw [if_pos (show 8 * i - 832 = 20928 by omega), h, show (21760 : Nat) = 21760 + 0 from rfl, hrho 0 (by omega),
        show WIT = WIT + 0 from rfl, v6M_eq N w 0 (by omega) (by omega)]
    · rw [if_neg (show ¬ 8 * i - 832 = 20928 by omega), if_pos (show 8 * i - 832 = 20936 by omega), h,
        show (21768 : Nat) = 21760 + 8 from rfl, hrho 8 (by omega), v6M_eq N w 8 (by omega) (by omega)]
    · rw [if_neg (show ¬ 8 * i - 832 = 20928 by omega), if_neg (show ¬ 8 * i - 832 = 20936 by omega),
        if_pos (show 8 * i - 832 = 20944 by omega), h, show (21776 : Nat) = 21760 + 16 from rfl,
        preBufferWinTail N w _ _ (by omega)]
      unfold tailBytes
      simp only [List.append_assoc]
      rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
        show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
        window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega)]
      rfl
    · rw [if_neg (show ¬ 8 * i - 832 = 20928 by omega), if_neg (show ¬ 8 * i - 832 = 20936 by omega),
        if_neg (show ¬ 8 * i - 832 = 20944 by omega), h, show (21784 : Nat) = 21760 + 24 from rfl,
        preBufferWinTail N w _ _ (by omega), ClaudeWCT.W9.T3M.tail_counter_window, v6M_eq N w 16 (by omega) (by omega),
        v6_head N w _ (by omega)]
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

theorem preBufferEndpointWindow (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (i : Fin (chainCount lay)) (k : Nat) (hk : k + 8 ≤ 16) :
    window (preBufferWitList N w) (chainBlock lay i.val + 48 + k) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values i)) k 8 := by
  have hi := i.isLt
  have he := ClaudeWCT.W9.T3M.layerEnd_le lay
  have hb : chainBlock lay i.val + 48 + k + 8 ≤ 21760 := by unfold chainBlock; omega
  rw [preBufferPrefix N w _ _ hb]
  rw [show chainBlock lay i.val + 48 + k = (chainBlock lay i.val + 48) + k from rfl,
    ← window_window' _ _ 16 _ 8 hk, ClaudeWCT.W9.T3M.win_chain N w lay i 48 (by omega),
    window_append_right _ _ _ _ (by simp [zeros]),
    show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]

theorem finalBufferWindow (N : HashOutput) (w : WCT9.Witness) (lay : Layer)
    (off n : Nat) (h : off + n ≤ leafBufferLen lay) :
    window (ClaudeWCT.W9.T3M.witList N w) (leafBufferBase lay + off) n =
      window (leafBufferBytes w.signature lay) off n := by
  have hbase : 21760 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hbound : leafBufferBase lay + leafBufferLen lay ≤ 24880 := by fin_cases lay <;> decide
  rw [ClaudeWCT.W9.T3M.witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]; omega)]
  simp only [List.length_append, headerBytes_length, wctBytes_length, layers_length]
  rw [window_append_left _ _ _ _ (by rw [leafBuffersBytes_length]; omega)]
  have hi : 3 - lay.val < (List.finRange 4).reverse.length := by simp; omega
  have he : (List.finRange 4).reverse[3 - lay.val]'hi = lay := by fin_cases lay <;> rfl
  have hp : (((List.finRange 4).reverse.take (3 - lay.val)).map
      (fun l => (leafBufferBytes w.signature l).length)).sum = leafBufferBase lay - 21760 := by
    simp only [leafBufferBytes_length]; fin_cases lay <;> decide
  have hw := SigGolfCandidate.T3M.window_flatMap (List.finRange 4).reverse (leafBufferBytes w.signature)
    (3 - lay.val) hi off n (by rw [he, leafBufferBytes_length]; exact h)
  rw [hp, he] at hw
  simpa only [leafBuffersBytes, show leafBufferBase lay + off - (176 + 8080 + 13504) = leafBufferBase lay - 21760 + off by omega]
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
  BitVec.ofNat 64 (readLE (window (preBufferWitList N w) (A - 1216) 8))
def serializedMem (N : HashOutput) (w : WCT9.Witness) (A : Nat) : Word :=
  BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (A - 1216) 8))

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
    preBufferMem N w (1216 + chainBlock lay i.val + 48 + k) =
      serializedMem N w (1216 + leafBufferSlot lay i.val + k) := by
  unfold preBufferMem serializedMem
  rw [show 1216 + chainBlock lay i.val + 48 + k - 1216 = chainBlock lay i.val + 48 + k by omega,
    show 1216 + leafBufferSlot lay i.val + k - 1216 = leafBufferSlot lay i.val + k by omega,
    preBufferEndpointWindow N w lay i k hk, finalEndpointWindow N w lay i k hk]

theorem bufferMem_endpoint (M : Nat → Word) (lay : Layer) (i : Nat) (hi : i < chainCount lay)
    (k : Nat) (hk : k = 0 ∨ k = 8) :
    Buffer.bufferMem M (1216 + leafBufferSlot lay i + k) =
      M (1216 + chainBlock lay i + 48 + k) := by
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

def bufferZeroAddresses : List Nat := [22992, 23000, 23680, 23688, 23696, 23704, 23728, 23736, 24416, 24424, 24432, 24440, 24464, 24472, 25152, 25160, 25168, 25176, 25184, 25192, 25200, 25208, 26080, 26088]
def bufferEndpointAddresses : List Nat := (List.finRange 4).flatMap fun lay =>
  (List.range (chainCount lay)).flatMap fun i =>
    [1216 + leafBufferSlot lay i, 1216 + leafBufferSlot lay i + 8]
theorem buffer_address_coverage : ∀ i : Fin 390,
    22976 + 8 * i.val ∈ bufferEndpointAddresses ++ bufferZeroAddresses := by decide +kernel

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
      A = 1216 + leafBufferSlot lay i + k := by
  simp only [bufferEndpointAddresses, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at h
  obtain ⟨lay, _, i, hi, h | h⟩ := h
  · exact ⟨lay,i,0,hi,Or.inl rfl,by simpa using h⟩
  · exact ⟨lay,i,8,hi,Or.inr rfl,h⟩

theorem bufferMem_serializer (N : HashOutput) (w : WCT9.Witness) (A : Nat)
    (hlo : 1216 ≤ A) (hhi : A < 26128) (halign : A % 8 = 0) :
    Buffer.bufferMem (preBufferMem N w) A = serializedMem N w A := by
  by_cases hprefix : A < 22976
  · rw [Buffer.bufferMem, if_neg (by omega), if_neg (by omega)]
    unfold preBufferMem serializedMem
    rw [preBufferPrefix N w _ 8 (by omega)]
  by_cases hfooter : 26096 ≤ A
  · rw [Buffer.bufferMem, if_pos ⟨hfooter,hhi,halign⟩]
    unfold preBufferMem serializedMem
    rw [show A - 3120 - 1216 = 21760 + (A - 26096) by omega,
      show A - 1216 = 24880 + (A - 26096) by omega,
      preBufferWinTail N w _ 8 (by omega), ClaudeWCT.W9.T3M.win_tail N w _ 8 (by omega)]
  · have hidx : (A - 22976) / 8 < 390 := by omega
    have h := buffer_address_coverage ⟨(A - 22976) / 8,hidx⟩
    have he : 22976 + 8 * ((A - 22976) / 8) = A := by omega
    simp only [he,List.mem_append] at h
    rcases h with h | h
    · obtain ⟨lay,i,k,hi,hk,rfl⟩ := mem_bufferEndpointAddresses h
      rw [bufferMem_endpoint _ lay i hi k hk]
      exact endpointMem_eq N w lay ⟨i,hi⟩ k (by rcases hk with rfl | rfl <;> omega)
    · rw [bufferMem_zeroAddress _ _ h,serializedMem_zeroAddress N w _ h]

theorem bufferMem_original_congr (M M' : Nat → Word) (A : Nat)
    (hlo : 1216 ≤ A) (hhi : A < 26128) (halign : A % 8 = 0)
    (hmem : ∀ B, 1216 ≤ B → B < 23008 → B % 8 = 0 → M B = M' B) :
    Buffer.bufferMem M A = Buffer.bufferMem M' A := by
  by_cases hprefix : A < 22976
  · rw [Buffer.bufferMem, if_neg (by omega), if_neg (by omega),
      Buffer.bufferMem, if_neg (by omega), if_neg (by omega)]
    exact hmem A hlo (by omega) halign
  by_cases hfooter : 26096 ≤ A
  · rw [Buffer.bufferMem, if_pos ⟨hfooter,hhi,halign⟩,
      Buffer.bufferMem, if_pos ⟨hfooter,hhi,halign⟩]
    exact hmem (A-3120) (by omega) (by omega) (by omega)
  · have hidx : (A - 22976) / 8 < 390 := by omega
    have h := buffer_address_coverage ⟨(A - 22976) / 8,hidx⟩
    have he : 22976 + 8 * ((A - 22976) / 8) = A := by omega
    simp only [he,List.mem_append] at h
    rcases h with h | h
    · obtain ⟨lay,i,k,hi,hk,rfl⟩ := mem_bufferEndpointAddresses h
      rw [bufferMem_endpoint _ lay i hi k hk,bufferMem_endpoint _ lay i hi k hk]
      have hb : 1216 ≤ 1216 + chainBlock lay i + 48 + k ∧
          1216 + chainBlock lay i + 48 + k < 23008 ∧
          (1216 + chainBlock lay i + 48 + k) % 8 = 0 := by
        fin_cases lay <;> rcases hk with rfl | rfl
        all_goals norm_num [chainBlock,layerBase,pathSlots,chainCount] at hi ⊢ <;> omega
      exact hmem _ hb.1 hb.2.1 hb.2.2
    · rw [bufferMem_zeroAddress _ _ h,bufferMem_zeroAddress _ _ h]

theorem bufferMem_words (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hmem : ∀ i < 2724, M (1216 + 8*i) = (wordsOf (preBufferWitList N w)).getD i 0)
    (i : Nat) (hi : i < 3114) :
    Buffer.bufferMem M (1216 + 8*i) = (wordsOf (ClaudeWCT.W9.T3M.witList N w)).getD i 0 := by
  have hm : ∀ B, 1216 ≤ B → B < 23008 → B % 8 = 0 → M B = preBufferMem N w B := by
    intro B hB hB' h8
    have hj : (B-1216)/8 < 2724 := by omega
    have he : B = 1216 + 8*((B-1216)/8) := by omega
    have h := hmem _ hj
    rw [wordsOf_getD' _ 2724 (preBufferWitList_length N w) _ hj] at h
    unfold preBufferMem
    have hz : 8*((B-1216)/8) = B-1216 := by omega
    rw [hz] at h
    simpa only [Nat.add_sub_of_le hB] using h
  rw [bufferMem_original_congr M (preBufferMem N w) _ (by omega) (by omega) (by omega) hm,
    bufferMem_serializer N w _ (by omega) (by omega) (by omega),
    wordsOf_getD' _ 3114 (ClaudeWCT.W9.T3M.witList_length_eq N w) i hi]
  unfold serializedMem
  congr 3 <;> omega

end ClaudeWCT.W9.Machine.Expand.Compact2
