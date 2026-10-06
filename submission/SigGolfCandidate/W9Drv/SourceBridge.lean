import SigGolfCandidate.W9Machine.WctN600Contract
import SigGolfCandidate.W9Machine.WctN600C1Bridge
import SigGolfCandidate.W9Machine.WctSourceWords
import SigGolfCandidate.W9Machine.WctPackedHeader
import SigGolfCandidate.W9Machine.WctTraceProgram
import SigGolfCandidate.ClaudeWCT.WCT9.Basic

section
set_option autoImplicit false
namespace W9Machine
open OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT
theorem chainLow_canonical (index coord child chain step : Nat)
    (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128) (ht : chain < 7) (hs : step < 3) :
    V3.chainLow index coord child chain step = WCT9.ftsChainLow index coord child chain step := by
  rw [chainLow_add _ _ _ _ _ ht hs, chainPrefix_value _ _ _ hk hj]
  unfold WCT9.ftsChainLow
  rw [Nat.mod_eq_of_lt (by omega : chain < 8), Nat.mod_eq_of_lt (by omega : step < 4),
    Nat.mod_eq_of_lt (by omega : coord < 16), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi]
  omega
theorem chainInput_canonical (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 7) (hs : step < 3) :
    V3.chainInput index coord child chain step a b c value =
      ClaudeWCT.W9.T3M.wctChainInputP index coord child chain step a b c value := by
  change _ = blk4 a (WCT9.ftsChainHeaderP index coord child chain step b) c value
  rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
      (chainInput_length _ _ _ _ _ _ _ _ _),
    ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _),
    wordsOf_chainInput, wordsOf_blk4]
  simp only [dlo, dhi, WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high,
    chainLow_canonical _ _ _ _ _ hi hk hj ht hs]
theorem chainP_canonical (index coord child chain start count : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 7) (hbound : start + count ≤ 3) :
    V3.chainP index coord child chain start count a b c value =
      ClaudeWCT.W9.T3M.wctChainP index coord child chain start count a b c value := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
    simp only [V3.chainP, ClaudeWCT.W9.T3M.wctChainP, List.range'_succ, List.foldlM_cons]
    rw [chainInput_canonical _ _ _ _ _ _ _ _ _ hi hk hj ht (by omega)]
    congr 1
    funext v
    exact ih (start + 1) v (by omega)
def canonicalChains (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728) :
    M (List Digest) :=
  (List.finRange 7).mapM fun t =>
    let d := WCT9.digit rank t
    ClaudeWCT.W9.T3M.wctChainP index k.val j.val t.val (3 - d) d
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).1
      (ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val)
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).2
      (ClaudeWCT.W9.T3M.wreveal w k.val t.val d)
theorem chainProgram_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 728) (hi : index < 2 ^ 31) :
    V3.chainProgram w index k j rank = canonicalChains w index k j rank := by
  unfold V3.chainProgram canonicalChains
  congr 1
  funext t
  have hd := WCT9.digit_le_three rank t
  rw [chainP_canonical _ _ _ _ _ _ _ _ _ _ hi k.isLt j.isLt t.isLt (by omega)]
  have hb : V3.chainPadB w k.val t.val = ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val := by
    simp only [V3.chainPadB, ClaudeWCT.W9.T3M.wcHeaderPad,
      V3.chainOffset, V3.regionOffset, ClaudeWCT.W9.T3M.wctChainBlock,
      ClaudeWCT.W9.T3M.regionBase, Nat.add_assoc]
    rw [show ClaudeWCT.W9.T3M.wdig w = W9Machine.wdig w from rfl, W9Machine.wdig_hi]
    congr 2 <;> omega
  rw [hb]
  rfl
end W9Machine
end
section
namespace W9Drv
open W9Machine SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open OracleComp
open SigGolfCandidate.T3 (Digest M shortHash header)
open SphincsSecurity (bytesLE bytesLE_length)
theorem nodeLow_add (k : Fin 9) (index : Nat) : V3.nodeLow k.val index = 1 + 3 * 256 + (4+k.val)*65536 + index*2^32 := by
  unfold V3.nodeLow
  fin_cases k <;> norm_num only [Nat.reduceAdd, Nat.reduceShiftLeft, Nat.reduceOr]
  all_goals rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by decide)]
  all_goals simp [Nat.shiftLeft_eq, Nat.add_comm]
theorem node_header_bytes (k : Fin 9) (index heap : Nat) (hi : index < 2^31) (hh : heap < 2^32) :
    bytesLE 8 (BitVec.ofNat 64 (V3.nodeLow k.val index)) ++ bytesLE 8 (BitVec.ofNat 64 heap) =
      bytesLE 16 (ClaudeWCT.WCT9.wctNodeHeader k.val index heap) := by
  have hb (lo hi : BitVec 64) : bytesLE 8 lo ++ bytesLE 8 hi = bytesLE 16 (hi ++ lo) := by
    apply readLE_inj (by simp [bytesLE_length])
    simp only [readLE_append, bytesLE_length, readLE_bytesLE, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
    omega
  rw [hb, ClaudeWCT.WCT9.wctNodeHeader_eq _ _ _ (by have := k.isLt; omega) (by omega) hh]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  rw [nodeLow_add]
  have hk := k.isLt
  have hlt : 1 + 3 * 256 + (4 + k.val) * 65536 + index * 2^32 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt (by omega : heap < 2^64), Nat.mod_eq_of_lt hlt,
    ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega
theorem nodeInput_canonical (k : Fin 9) (index heap : Nat) (left pad right : Digest)
    (hi : index < 2^31) (hh : heap < 2^32) :
    shortHash (V3.nodeInput k.val index heap left pad right) =
      ClaudeWCT.W9.T3M.wctNodeHashP k.val index heap left pad right := by
  have e := node_header_bytes k index heap hi hh
  unfold V3.nodeInput ClaudeWCT.W9.T3M.wctNodeHashP nodeHashP
  rw [List.append_assoc (bytesLE 16 left)]
  erw [e]
  rfl
def coordTail (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) : M (Digest × Digest) := do
  let leaf ← ClaudeWCT.WCT9.leafHash index k.val j.val ends
  let top ← (List.finRange 6).foldlM (fun value level => do
    let other := ClaudeWCT.W9.T3M.wsib w k.val j.val level.val
    let pair := if j.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.W9.T3M.wctNodeHashP k.val index
      (2 ^ (6 - level.val) + j.val / 2 ^ (level.val + 1))
      pair.1 (ClaudeWCT.W9.T3M.wmpad w k.val j.val level.val) pair.2) leaf
  let other := ClaudeWCT.W9.T3M.wsib w k.val j.val 6
  pure (if j.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
theorem wctCoordP_split (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 600) (hi : index < 2 ^ 31) :
    ClaudeWCT.W9.T3M.wctCoordP w index k j rank =
      (N600.program w index k j rank >>= coordTail w index k j) := by
  unfold N600.program
  rw [chainProgram_canonical w index k j (N600.embed rank) hi, (show N600.embed = ClaudeWCT.WCT9.embed from N600.embed_eq_c1)]
  rfl
theorem leafInput_canonical (k index j : Nat) (ends : List Digest) (h : ends.length = 7) :
    shortHash (V3.leafInput k index j ends) = ClaudeWCT.WCT9.leafHash index k j ends := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5, e6], _ =>
    simp only [V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, V3.leafFields, ClaudeWCT.WCT9.leafHash,
      List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc,
      ClaudeWCT.WCT9.leaf_header_eq]
    rfl
theorem heap_eq (j l : Nat) (hj : j < 128) (hl : l < 6) :
    (128 + j) / 2 ^ (l + 1) = 2 ^ (6 - l) + j / 2 ^ (l + 1) := by
  interval_cases l <;> norm_num [Nat.add_div] <;> omega
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem childProgram_canonical (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (hends : ends.length = 7) (hi : index < 2^31) :
    (V3.childProgram w index k j ends >>= fun p => pure (p.left, p.right)) =
      coordTail w index k j ends := by
  unfold V3.childProgram coordTail
  rw [leafInput_canonical _ _ _ _ hends]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext leaf
  have hf : (List.range 6).foldlM (fun value level =>
        shortHash (V3.nodeInput k.val index ((128+j.val)/2^(level+1))
          (if j.val/2^level%2=0 then value else V3.sibling w k.val j.val level)
          (V3.nodePad w k.val j.val level)
          (if j.val/2^level%2=0 then V3.sibling w k.val j.val level else value))) leaf =
      (List.finRange 6).foldlM (fun value level =>
        let other := ClaudeWCT.W9.T3M.wsib w k.val j.val level.val
        let pair := if j.val/2^level.val%2=0 then (value,other) else (other,value)
        ClaudeWCT.W9.T3M.wctNodeHashP k.val index (2 ^ (6 - level.val) + j.val / 2 ^ (level.val + 1))
          pair.1 (ClaudeWCT.W9.T3M.wmpad w k.val j.val level.val) pair.2) leaf := by
    rw [← finRange_map_val (n := 6), List.foldlM_map]
    congr 1
    funext value level
    have hl := level.isLt
    have hh : 2 ^ (6 - level.val) + j.val / 2 ^ (level.val + 1) < 2^32 := by
      have hj := j.isLt
      interval_cases (level.val) <;> omega
    rw [heap_eq j.val level.val j.isLt hl, nodeInput_canonical k index _ _ _ _ hi hh]
    simp only [V3.sibling, V3.nodePad]
    by_cases hb : j.val / 2 ^ level.val % 2 = 0 <;> simp [hb]
  rw [hf]
  congr 1
  funext value
  simp only [V3.orderPair, V3.sibling]
  have hb : j.val/64%2=0 ∨ j.val/64%2=1 := by omega
  rcases hb with hb | hb <;> simp only [show 2^6=64 from rfl, hb] <;> rfl
theorem digAt_of_eq {X Y : MachineState} {a : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 a) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (a + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y a d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
end W9Drv
end
