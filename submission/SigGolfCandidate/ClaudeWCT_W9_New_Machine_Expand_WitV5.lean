import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Honest

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
/-- T51: chain blocks of a staging region. The top keeps #938's 54 blocks (chain `i` at block `53 - i` below the
path blocks; the blocks of chains 51..53 are never written and stay zero). -/
def chainSlotsV6 (lay : Layer) : Nat := if lay.val = 0 then 54 else chainCount lay
theorem chainSlotsV6_lower (lay : Layer) (hl : lay.val ≠ 0) : chainSlotsV6 lay = chainCount lay := by
  simp [chainSlotsV6, hl]
theorem chainSlotsV6_ge (lay : Layer) : chainCount lay ≤ chainSlotsV6 lay := by
  fin_cases lay <;> decide
/-- T51: a staging region without its counter block. The top inserts the 3 zero blocks of #938's chains 51..53
between its 12 path blocks and its 51 chain blocks. -/
def layerBytesV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  if lay.val = 0 then (layerBytes lay leaf ls).take 768 ++ zeros 192 ++ (layerBytes lay leaf ls).drop 768
  else layerBytes lay leaf ls
def layerRegionV6 (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then layerBytesV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
  else layerBytesBCV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
    (w.counters (Fin.ofNat 4 (lay.val - 1)))
/-- Staging region of the compaction pass (896 bytes). r3w (witness stack): the FTS content of the staging is dead
(the finish pass zeroes `[1152, 11000)` and rebuilds the FTS block from the signature), so only its length matters. -/
def regionBytesV6 (_child : Nat) (_op : WCT9.Opening) : List UInt8 := zeros 896
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
/-- Expand scratch region (1024 bytes). r3w: dead FTS content (see `regionBytesV6`); only the length matters. -/
def regionBytesV5 (_child : Nat) (_op : WCT9.Opening) : List UInt8 := zeros 1024
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
  simp only [regionBytesV5, zeros, List.length_replicate]
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
theorem layerBytesV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerBytesV6 lay leaf ls).length = 64 * (height lay + chainSlotsV6 lay) := by
  unfold layerBytesV6 chainSlotsV6
  split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    have e1 : (zeros 192 : List UInt8).length = 192 := List.length_replicate ..
    have h1 : height (0 : Layer) = 12 := rfl
    have h2 : chainCount (0 : Layer) = 51 := rfl
    rw [List.length_append, List.length_append, List.length_take, List.length_drop,
      SigGolfCandidate.T3M.layerBytes_length, e1, h1, h2]
    simp
  · rw [SigGolfCandidate.T3M.layerBytes_length]
theorem layerRegionV6_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegionV6 N w lay).length = 64 * (height lay + chainSlotsV6 lay) := by
  unfold layerRegionV6; split
  · exact layerBytesV6_length _ _ _
  · rename_i h
    rw [layerBytesBCV6_length]
    simp [chainSlotsV6, h]
theorem layersV6_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegionV6 N w)).length = 13696 := by
  simp only [List.length_flatMap, layerRegionV6_length]
  decide

theorem witListV5_length (N : HashOutput) (w : WCT9.Witness) : (witListV5 N w).length = 22984 := by
  unfold witListV5
  simp only [List.length_append, headerBytesV5_length, wctBytesV5_length, zeros,
    List.length_replicate, layersV6_length]
theorem regionBytesV6_length (c : Nat) (op : WCT9.Opening) : (regionBytesV6 c op).length = 896 := by
  simp only [regionBytesV6, zeros, List.length_replicate]
theorem wctBytesV6_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV6 N sig).length = 8064 := by
  unfold wctBytesV6
  rw [List.length_flatMap]
  simp only [regionBytesV6_length, List.map_const', List.length_finRange, List.sum_replicate,
    smul_eq_mul]
theorem witListV6_length (N : HashOutput) (w : WCT9.Witness) : (witListV6 N w).length = 21832 := by
  unfold witListV6
  simp only [List.length_append, headerBytesV5_length, wctBytesV6_length, zeros,
    List.length_replicate, layersV6_length]
end ClaudeWCT.W9.Machine.Expand
