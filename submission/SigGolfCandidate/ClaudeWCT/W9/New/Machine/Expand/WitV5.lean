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
def layerRegionV6 (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then layerBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
  else layerBytesBCV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
    (w.counters (Fin.ofNat 4 (lay.val - 1)))
def wctBytesV6 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytes (WCT9.child N k).val (sig.openings k)
def witListV6 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes w ++ wctBytesV6 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
def merkleBytesV5 (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 7).reverse.flatMap fun l =>
    if child / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48 else zeros 48 ++ bytesLE 16 (op.path l)
def regionBytesV5 (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  merkleBytesV5 child op ++ chainBytes op ++ zeros 48 ++ leafBytes op ++ zeros 16
def wctBytesV5 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytesV5 (WCT9.child N k).val (sig.openings k)
def witListV5 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes w ++ wctBytesV5 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
theorem merkleBytesV5_length (c : Nat) (op : WCT9.Opening) : (merkleBytesV5 c op).length = 448 := by
  unfold merkleBytesV5
  rw [List.length_flatMap]
  have : ∀ l : Fin 7, (if c / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (op.path l)).length = 64 := fun l => by
    split <;> simp [zeros, bytesLE_length]
  simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem regionBytesV5_length (c : Nat) (op : WCT9.Opening) : (regionBytesV5 c op).length = 1024 := by
  simp only [regionBytesV5, List.length_append, merkleBytesV5_length, ClaudeWCT.W9.T3M.chainBytes_length,
    ClaudeWCT.W9.T3M.leafBytes_length, zeros, List.length_replicate]
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
theorem layerRegionV6_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegionV6 N w lay).length = 64 * (height lay + chainCount lay) := by
  unfold layerRegionV6; split
  · exact SigGolfCandidate.T3M.layerBytes_length _ _ _
  · exact layerBytesBCV6_length _ _ _ _
theorem layersV6_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegionV6 N w)).length = 13696 := by
  simp only [List.length_flatMap, layerRegionV6_length]
  simp [List.finRange, height, chainCount]
theorem witListV5_length (N : HashOutput) (w : WCT9.Witness) : (witListV5 N w).length = 22984 := by
  unfold witListV5
  simp only [List.length_append, ClaudeWCT.W9.T3M.headerBytes_length, wctBytesV5_length, zeros,
    List.length_replicate, layersV6_length]
theorem wctBytesV6_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV6 N sig).length = 8064 := by
  unfold wctBytesV6
  rw [List.length_flatMap]
  simp only [ClaudeWCT.W9.T3M.regionBytes_length, List.map_const', List.length_finRange, List.sum_replicate,
    smul_eq_mul]
theorem witListV6_length (N : HashOutput) (w : WCT9.Witness) : (witListV6 N w).length = 21832 := by
  unfold witListV6
  simp only [List.length_append, ClaudeWCT.W9.T3M.headerBytes_length, wctBytesV6_length, zeros,
    List.length_replicate, layersV6_length]
section region
open ClaudeWCT.W9.T3M (chainBytes_length leafBytes_length)
variable (c : Nat) (op : WCT9.Opening)
theorem region_merkleV5 (o n : Nat) (h : o + n ≤ 448) :
    window (regionBytesV5 c op) o n = window (merkleBytesV5 c op) o n := by
  unfold regionBytesV5
  rw [window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length]; omega)]
theorem region_chainV5 (o n : Nat) (h0 : 448 ≤ o) (h : o + n ≤ 832) :
    window (regionBytesV5 c op) o n = window (chainBytes op) (o - 448) n := by
  unfold regionBytesV5
  rw [window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytesV5_length]; omega), merkleBytesV5_length]
theorem region_prefixV5 (o n : Nat) (h0 : 832 ≤ o) (h : o + n ≤ 880) :
    window (regionBytesV5 c op) o n = zeros n := by
  unfold regionBytesV5
  rw [window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length]; omega)]
  simp only [List.length_append, merkleBytesV5_length, chainBytes_length]
  exact window_zeros _ _ _ (by omega)
theorem region_leafV5 (o n : Nat) (h0 : 880 ≤ o) (h : o + n ≤ 1008) :
    window (regionBytesV5 c op) o n = window (leafBytes op) (o - 880) n := by
  unfold regionBytesV5
  rw [window_append_left _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, leafBytes_length, zeros]; omega),
    window_append_right _ _ _ _ (by simp [merkleBytesV5_length, chainBytes_length, zeros]; omega)]
  simp only [List.length_append, merkleBytesV5_length, chainBytes_length, zeros, List.length_replicate]
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
