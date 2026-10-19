import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.T3 (HashOutput Layer height chainCount)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3 (LayerSignature route)
open SigGolfCandidate.T3M (layerBytes)
open ClaudeWCT.W9.T3M (headerBytes chainBytes leafBytes regionBytes)
def bcTopBlockV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  if leaf / 2 ^ (height lay - 1) % 2 = 1 then
    bytesLE 16 (ls.path (WCT9.topLevel lay)) ++ zeros 16 ++ bytesLE 4 ctr ++ zeros 28
  else zeros 32 ++ bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path (WCT9.topLevel lay))
def layerBytesBCV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  bcTopBlockV6 lay leaf ls ctr ++ (layerBytes lay leaf ls).drop 64
/-- Campaign R6: dead chain blocks of the expander's staging region: the top keeps main's 54 chain blocks
(`topChainBlocks`), so the blocks of main's chains 52/53 (directly above the path blocks) stay zero. -/
def vGap (lay : Layer) : Nat := if lay.val = 0 then ClaudeWCT.W9.T3M.topChainBlocks - chainCount lay else 0
/-- Campaign R6: 64-byte blocks of the staging region of layer `lay` (top 12 + 2 + 52 = 66, as main). -/
def vBlocks (lay : Layer) : Nat := height lay + vGap lay + chainCount lay
/-- Campaign R6: insert the dead blocks after the path blocks. -/
def gapV6 (lay : Layer) (L : List UInt8) : List UInt8 :=
  L.take (64 * height lay) ++ zeros (64 * vGap lay) ++ L.drop (64 * height lay)
theorem vGap_top : vGap 0 = 2 := rfl
theorem vGap_low (lay : Layer) (h : lay.val ≠ 0) : vGap lay = 0 := by unfold vGap; rw [if_neg h]
theorem gapV6_low (lay : Layer) (h : lay.val ≠ 0) (L : List UInt8) : gapV6 lay L = L := by
  unfold gapV6; rw [vGap_low lay h]; simp [zeros]
theorem vBlocks_low (lay : Layer) (h : lay.val ≠ 0) : vBlocks lay = height lay + chainCount lay := by
  unfold vBlocks; rw [vGap_low lay h, Nat.add_zero]
theorem vBlocks_vals : vBlocks 0 = 66 ∧ vBlocks 1 = 50 ∧ vBlocks 2 = 49 ∧ vBlocks 3 = 49 := by decide
def layerRegionV6 (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then gapV6 lay (layerBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay))
  else layerBytesBCV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
    (w.counters (Fin.ofNat 4 (lay.val - 1)))
/-- Staging region of the compaction pass (nested FTS): the witness region with both pads zero (896 bytes). -/
def regionBytesV6 (child : Nat) (op : WCT9.Opening) : List UInt8 := regionBytes child op (zeros 16) (zeros 16)
/-- Header of the first-pass scratch layout at 0x800 (the frontier's 64-byte header: rho, digest counter, L3
counter). Machine internal; the final witness uses `ClaudeWCT.W9.T3M.headerBytes`. -/
def headerBytesV5 (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++ zeros 28
theorem headerBytesV5_length (w : WCT9.Witness) : (headerBytesV5 w).length = 64 := by
  simp [headerBytesV5, zeros, bytesLE_length]
def wctBytesV6 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytesV6 (WCT9.child N k).val (sig.openings k)
def witListV6 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytesV5 w ++ wctBytesV6 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
def merkleBytesV5 (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 7).reverse.flatMap fun l =>
    if child / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48 else zeros 48 ++ bytesLE 16 (op.path l)
/-- Expand scratch region (T8): merkle 448 | chains 5..1 (320) | 48 zeros | leaf 128 | 80 zeros = 1024 bytes. -/
def regionBytesV5 (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  merkleBytesV5 child op ++ chainBytes op ++ zeros 48 ++ leafBytes op (zeros 16) ++ zeros 80
def wctBytesV5 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytesV5 (WCT9.child N k).val (sig.openings k)
def witListV5 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytesV5 w ++ wctBytesV5 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
theorem leafBytesZ_length (op : WCT9.Opening) : (ClaudeWCT.W9.T3M.leafBytes op (zeros 16)).length = 128 :=
  ClaudeWCT.W9.T3M.leafBytes_length _ _ (by simp [zeros])
theorem leafBytesZ_length' (op : WCT9.Opening) :
    (ClaudeWCT.W9.T3M.leafBytes op (List.replicate 16 0)).length = 128 :=
  ClaudeWCT.W9.T3M.leafBytes_length _ _ (by simp)
theorem merkleBytesV5_length (c : Nat) (op : WCT9.Opening) : (merkleBytesV5 c op).length = 448 := by
  unfold merkleBytesV5
  rw [List.length_flatMap]
  have : ∀ l : Fin 7, (if c / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (op.path l)).length = 64 := fun l => by
    split <;> simp [zeros, bytesLE_length]
  simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem regionBytesV5_length (c : Nat) (op : WCT9.Opening) : (regionBytesV5 c op).length = 1024 := by
  simp only [regionBytesV5, List.length_append, merkleBytesV5_length, ClaudeWCT.W9.T3M.chainBytes_length,
    leafBytesZ_length, leafBytesZ_length', zeros, List.length_replicate]
theorem wctBytesV5_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV5 N sig).length = 9216 := by
  unfold wctBytesV5
  rw [List.length_flatMap]
  simp only [regionBytesV5_length, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem bcTopBlockV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (bcTopBlockV6 lay leaf ls ctr).length = 64 := by
  unfold bcTopBlockV6; split <;> simp [zeros, bytesLE_length]
theorem height_pos (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem layerBytesBCV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (layerBytesBCV6 lay leaf ls ctr).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytesBCV6
  rw [List.length_append, bcTopBlockV6_length, List.length_drop, SigGolfCandidate.T3M.layerBytes_length]
  have := height_pos lay
  have : 64 ≤ 64 * (height lay + chainCount lay) := by nlinarith
  omega
theorem gapV6_length (lay : Layer) (L : List UInt8) (hL : L.length = 64 * (height lay + chainCount lay)) :
    (gapV6 lay L).length = 64 * vBlocks lay := by
  unfold gapV6 vBlocks
  simp only [List.length_append, List.length_take, List.length_drop, hL, zeros, List.length_replicate]
  rw [Nat.min_eq_left (by nlinarith)]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]; omega
theorem layerRegionV6_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegionV6 N w lay).length = 64 * vBlocks lay := by
  unfold layerRegionV6; split
  · exact gapV6_length _ _ (SigGolfCandidate.T3M.layerBytes_length _ _ _)
  · rename_i h
    rw [layerBytesBCV6_length]; unfold vBlocks; rw [vGap_low lay h, Nat.add_zero]
theorem layersV6_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegionV6 N w)).length = 13696 := by
  simp only [List.length_flatMap, layerRegionV6_length]
  simp [List.finRange, vBlocks, vGap, ClaudeWCT.W9.T3M.topChainBlocks, height, chainCount]

theorem witListV5_length (N : HashOutput) (w : WCT9.Witness) : (witListV5 N w).length = 22984 := by
  unfold witListV5
  simp only [List.length_append, headerBytesV5_length, wctBytesV5_length, zeros,
    List.length_replicate, layersV6_length]
theorem regionBytesV6_length (c : Nat) (op : WCT9.Opening) : (regionBytesV6 c op).length = 896 :=
  ClaudeWCT.W9.T3M.regionBytes_length _ _ _ _ (by simp [zeros]) (by simp [zeros])
theorem wctBytesV6_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV6 N sig).length = 8064 := by
  unfold wctBytesV6
  rw [List.length_flatMap]
  simp only [regionBytesV6_length, List.map_const', List.length_finRange, List.sum_replicate,
    smul_eq_mul]
theorem witListV6_length (N : HashOutput) (w : WCT9.Witness) : (witListV6 N w).length = 21832 := by
  unfold witListV6
  simp only [List.length_append, headerBytesV5_length, wctBytesV6_length, zeros,
    List.length_replicate, layersV6_length]
section region
open ClaudeWCT.W9.T3M (chainBytes_length)
variable (c : Nat) (op : WCT9.Opening)
theorem region_merkleV5 (o n : Nat) (h : o + n ≤ 448) :
    window (regionBytesV5 c op) o n = window (merkleBytesV5 c op) o n := by
  unfold regionBytesV5
  rw [window_append_left _ _ _ _ (by simp only [List.length_append, merkleBytesV5_length, chainBytes_length, leafBytesZ_length, leafBytesZ_length', zeros, List.length_replicate]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length]; omega)]
theorem region_tailV5 (o n : Nat) (h0 : 944 ≤ o) (h : o + n ≤ 1024) :
    window (regionBytesV5 c op) o n = zeros n := by
  unfold regionBytesV5
  rw [window_append_right _ _ _ _ (by simp only [List.length_append, merkleBytesV5_length, chainBytes_length, leafBytesZ_length, leafBytesZ_length', zeros, List.length_replicate]; omega)]
  simp only [List.length_append, merkleBytesV5_length, chainBytes_length, leafBytesZ_length, leafBytesZ_length', zeros,
    List.length_replicate]
  exact window_zeros _ _ _ (by omega)
theorem merkleBytesV5_window (l : Fin 7) (o : Nat) (ho : o + 16 ≤ 64) :
    window (merkleBytesV5 c op) (64 * (6 - l.val) + o) 16 =
      window (if c / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48
        else zeros 48 ++ bytesLE 16 (op.path l)) o 16 := by
  have hl := l.isLt
  unfold merkleBytesV5
  rw [window_flatMap_const _ _ 64 (fun j => by split <;> simp [zeros, bytesLE_length]) (6 - l.val)
    (by simp; omega) o 16 ho]
  have hj : ((List.finRange 7).reverse[6 - l.val]'(by simp; omega)) = l := by
    rw [List.getElem_reverse]; ext; simp; omega
  rw [hj]
end region
end ClaudeWCT.W9.Machine.Expand
