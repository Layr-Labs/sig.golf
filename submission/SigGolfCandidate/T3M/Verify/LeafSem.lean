import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout
import SigGolfCandidate.T3M.Verify.LayerSem

section


set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def keepLfAll (lay : Nat) : List Reg :=
  if lay = 0 then [.x1, .x2, .x7, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23,
    .x25, .x26, .x28, .x29, .x31, .x30]
  else [.x1, .x2, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23,
    .x6, .x26, .x29, .x31, .x30] ++ (if lay = 1 then [] else [.x25, .x28])
/-- Campaign R6: the 8 final tails at `ckTail d` (after the checksum chain 51 with digit `d`): main's tail without
the `bne` (7 words ending in the leaf `jalr`). There is no tail reject: the checksum range was checked by the
checksum dispatch (`ckDispR`), and the R6 verifier has no final digit-sum check. -/
def fusedLeafCheck6 (d : Nat) : Bool :=
  specB (lfAllowed 0) [] (gkL 0) (runAt (leafK 0) [] (Nonbinary.ckTail d) [.jmp]) (specLf 0) [] (postLf 0) (keepLfAll 0)
theorem fusedLeafChecks6 : (List.range 8).all fusedLeafCheck6 = true := by decide +kernel
theorem fusedLeafCheck6_at (d : Nat) (hd : d < 8) : fusedLeafCheck6 d = true :=
  List.all_eq_true.mp fusedLeafChecks6 d (List.mem_range.mpr hd)
end SigGolfCandidate.T3M
end

section


section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3 OracleComp
theorem mapM_congr' {α β : Type} {f g : α → M β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (by simp), mapM_congr' l (fun y hy => h y (by simp [hy]))]
theorem finRange_mapM {β : Type} (n : Nat) (g : Nat → M β) :
    (List.finRange n).mapM (fun i => g i.val) = (List.range n).mapM g := by
  have e : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp
  rw [← e, List.mapM_map]; rfl
theorem foldlM_app_mapM (f : Nat → M Digest) : ∀ (n a : Nat) (acc : List Digest),
    (List.range' a n).foldlM (fun e i => do let v ← f i; pure (e ++ [v])) acc =
      (fun l => acc ++ l) <$> (List.range' a n).mapM f
  | 0, a, acc => by simp
  | n + 1, a, acc => by
    rw [List.range'_succ, List.foldlM_cons, List.mapM_cons]
    simp only [bind_assoc, pure_bind, foldlM_app_mapM f n (a + 1), map_bind, bind_map_left, map_pure]
    congr 1; funext v
    rw [← bind_pure_comp]
    congr 1; funext l; simp
namespace QCtx
theorem sum_range'_eq (f g : Nat → Nat) (a n : Nat) (h : ∀ i, a ≤ i → i < a + n → f i = g i) :
    ((List.range' a n).map f).sum = ((List.range' a n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have := List.mem_range'_1.mp hi
  exact h i this.1 this.2
end QCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
theorem chainCount_lower (lay : Layer) (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem decode_lower_sum (lay : Layer) (hlay : lay ≠ 0) (value : Digest) (ds : List Nat)
    (h : decode lay value = some ds) : ds.length = 43 ∧ ds.sum = target lay := by
  unfold decode at h
  split at h
  · cases h
  · simp only [if_neg hlay] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have hl : (dataDigits lay value).length = 42 := by simp [dataDigits, dataCount, hlay]
      refine ⟨by simp [hl], ?_⟩
      rw [List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · cases h
theorem sum_dig (c : LCtx) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0) (hl : D.length = 43) :
    ((List.range' 0 43).map c.dig).sum = D.sum := by
  have hE : D = (List.range' 0 43).map fun i => D.getD i 0 := by
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range']
    rw [show 0 + 1 * i = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  conv_rhs => rw [hE]
  exact QCtx.sum_range'_eq _ _ 0 43 (fun i _ hi => hD i (by omega))
end LCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem leafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = projHash (leafHalfHigh lay leaf) (T3.leafInput lay tree leaf ends) := rfl
def dw (e : Digest) : List (BitVec 64) := [e.extractLsb' 0 64, e.extractLsb' 64 64]
theorem flatMap_length16 : ∀ (L : List Digest), (L.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * L.length
  | [] => rfl
  | e :: L => by
    rw [List.flatMap_cons, List.length_append, flatMap_length16 L, SphincsSecurity.bytesLE_length]; simp; ring
abbrev leafWord (lay : Layer) (tree leaf : Nat) : BitVec 64 := T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)
/-- C3: the verifier's leaf input (top pad and tweak high word from the witness). Campaign R6: the top leaf's
32-byte gap after the tweak is witness memory too (`wtopLeafGap`, hashed as found); lower leaves ignore it. -/
abbrev lfIn (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (tree leaf : Nat) (ends : List Digest) : List UInt8 :=
  ClaudeWCT.WCT9.leafInputWG lay tree leaf (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w lay)
    (ClaudeWCT.W9.T3M.wtopLeafGap w) ends
/-- Campaign R6: the top leaf input `pad | tweak | gap.1 | gap.2 | 52 ends` (896 bytes). -/
theorem leafInput_top (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (gap : Digest × Digest)
    (ends : List Digest) :
    ClaudeWCT.WCT9.leafInputWG 0 tree leaf pad hi gap ends =
      SphincsSecurity.bytesLE 16 pad ++ SphincsSecurity.bytesLE 16 (hi ++ leafWord 0 tree leaf) ++
        SphincsSecurity.bytesLE 16 gap.1 ++ SphincsSecurity.bytesLE 16 gap.2 ++
        ends.flatMap (SphincsSecurity.bytesLE 16) := by
  unfold ClaudeWCT.WCT9.leafInputWG ClaudeWCT.WCT9.leafTweakW; rw [if_pos rfl]
/-- Campaign R6: lower leaves ignore the top gap. -/
theorem leafInputWG_low (lay : Layer) (h : lay ≠ 0) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (gap : Digest × Digest) (ends : List Digest) :
    ClaudeWCT.WCT9.leafInputWG lay tree leaf pad hi gap ends = ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends := by
  simp only [ClaudeWCT.WCT9.leafInputWG, ClaudeWCT.WCT9.leafInputW, if_neg h]
theorem leafHashWG_low (lay : Layer) (h : lay ≠ 0) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (gap : Digest × Digest) (ends : List Digest) :
    ClaudeWCT.WCT9.leafHashWG lay tree leaf pad hi gap ends = ClaudeWCT.WCT9.leafHashW lay tree leaf pad hi ends := by
  unfold ClaudeWCT.WCT9.leafHashWG ClaudeWCT.WCT9.leafHashW; rw [leafInputWG_low lay h]

theorem leafInput_low (lay : Layer) (h : lay ≠ 0) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (ends : List Digest) :
    ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends =
      SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++ SphincsSecurity.bytesLE 16 (hi ++ leafWord lay tree leaf) ++
        (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16) := by
  simp only [ClaudeWCT.WCT9.leafInputW, ClaudeWCT.WCT9.leafTweakW, if_neg h]
theorem readWords_digs (t : MachineState) : ∀ (L : List Digest) (A : Nat),
    (∀ j < L.length, DigAt t (A + 16 * j) (L.getD j 0)) →
      t.readWords (BitVec.ofNat 64 A) (2 * L.length) = L.flatMap dw
  | [], _, _ => rfl
  | e :: L, A, h => by
    rw [List.length_cons, show 2 * (L.length + 1) = 2 + 2 * L.length by ring, readWords_add, readWords_two,
      show A + 8 * 2 = A + 16 by ring, readWords_digs t L (A + 16) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show A + 16 * (j + 1) = A + 16 + 16 * j by ring, List.getD_cons_succ] at this),
      List.flatMap_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0.1, h0.2]; rfl
theorem getD_drop1 (L : List Digest) (j : Nat) : (L.drop 1).getD j 0 = L.getD (j + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2; omega
theorem lowLeaf_hashInput (t : MachineState) (lay : Layer) (hlay : lay ≠ 0) (tree leaf : Nat) (pad : Digest)
    (hi : BitVec 64) (ends : List Digest)
    (off : Nat) (hoff : off % 16 = 0) (hbound : off + 1472 < 2 ^ 64)
    (hn : ends.length = 43) (h10 : t.getReg .x10 = BitVec.ofNat 64 (off + 768))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 704) (hS : ∀ j < 43, DigAt t (off + slotL j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 (off + 784)) = leafWord lay tree leaf)
    (hT1 : t.getMem (BitVec.ofNat 64 (off + 792)) = hi) :
    hashInput t = toQ (pad64 (ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends)) ∧
      (toQ (pad64 (ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends))).blocks = 11 := by
  have hl : (ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends).length = 64 * (10 + 1) := by
    rw [leafInput_low lay hlay, List.length_append, List.length_append, flatMap_length16,
      SphincsSecurity.bytesLE_length, SphincsSecurity.bytesLE_length, List.length_drop, hn] <;> norm_num
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 10 (off + 768) hl h10 (by omega) (by omega) (by simpa using h11) (by omega)
  rw [leafInput_low lay hlay, wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), Verify.wordsOf_append64, wordsOf_bytesLE16,
    wordsOf_flatMap16, show 8 * (10 + 1) = 2 + (2 + 2 * (ends.drop 1).length) by simp [hn],
    readWords_add, readWords_add, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotL 0 = 768 from rfl] at e0
  rw [show (off + 768) + 8 * 2 = (off + 784) by omega, show (off + 784) + 8 = (off + 792) by omega, show (off + 784) + 8 * 2 = (off + 800) by omega,
    e0.1, show (off + 768) + 8 = ((off + 768) : Nat) + 8 by omega, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) (off + 800) (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show off + slotL (j + 1) = (off + 800) + 16 * j by unfold slotL; simp; omega] at this)]
  rfl
/-- Campaign R6: the top leaf buffer `25200 + [pad | tweak | gap | 52 ends at slotT j = 25264 + 16 j]`. -/
theorem topLeaf_hashInput (t : MachineState) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (gap : Digest × Digest) (ends : List Digest)
    (hn : ends.length = 52) (h10 : t.getReg .x10 = BitVec.ofNat 64 25200)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 896) (hS : ∀ j < 52, DigAt t (slotT j) (ends.getD j 0))
    (hZ : DigAt t 25200 pad) (hG1 : DigAt t 25232 gap.1) (hG2 : DigAt t 25248 gap.2)
    (hT0 : t.getMem (BitVec.ofNat 64 25216) = leafWord 0 tree leaf)
    (hT1 : t.getMem (BitVec.ofNat 64 25224) = hi) :
    hashInput t = toQ (pad64 (ClaudeWCT.WCT9.leafInputWG 0 tree leaf pad hi gap ends)) ∧
      (toQ (pad64 (ClaudeWCT.WCT9.leafInputWG 0 tree leaf pad hi gap ends))).blocks = 14 := by
  have hl : (ClaudeWCT.WCT9.leafInputWG 0 tree leaf pad hi gap ends).length = 64 * (13 + 1) := by
    rw [leafInput_top, List.length_append, List.length_append, List.length_append, List.length_append,
      flatMap_length16, SphincsSecurity.bytesLE_length, SphincsSecurity.bytesLE_length,
      SphincsSecurity.bytesLE_length, SphincsSecurity.bytesLE_length, hn]
  have hZ0 : t.getMem (BitVec.ofNat 64 25200) = pad.extractLsb' 0 64 := hZ.1
  have hZ1 : t.getMem (BitVec.ofNat 64 25208) = pad.extractLsb' 64 64 := hZ.2
  have hA0 : t.getMem (BitVec.ofNat 64 25232) = gap.1.extractLsb' 0 64 := hG1.1
  have hA1 : t.getMem (BitVec.ofNat 64 25240) = gap.1.extractLsb' 64 64 := hG1.2
  have hB0 : t.getMem (BitVec.ofNat 64 25248) = gap.2.extractLsb' 0 64 := hG2.1
  have hB1 : t.getMem (BitVec.ofNat 64 25256) = gap.2.extractLsb' 64 64 := hG2.2
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 13 25200 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [leafInput_top, wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), Verify.wordsOf_append64, wordsOf_bytesLE16,
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_flatMap16,
    show 8 * (13 + 1) = 2 + (2 + (2 + (2 + 2 * ends.length))) by simp [hn],
    readWords_add, readWords_add, readWords_add, readWords_add, readWords_two, readWords_two, readWords_two,
    readWords_two]
  rw [show 25200 + 8 * 2 = 25216 by rfl, show 25216 + 8 = 25224 by rfl, show 25216 + 8 * 2 = 25232 by rfl,
    show 25232 + 8 * 2 = 25248 by rfl, show 25248 + 8 * 2 = 25264 by rfl,
    show 25200 + 8 = (25208 : Nat) by rfl, show 25232 + 8 = (25240 : Nat) by rfl,
    show 25248 + 8 = (25256 : Nat) by rfl, hZ0, hZ1, hA0, hA1, hB0, hB1, hT0, hT1,
    readWords_digs t ends 25264 (fun j hj => by
      have := hS j (by omega)
      rwa [show slotT j = 25264 + 16 * j by unfold slotT; omega] at this)]
  rfl
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def lfBase (lay : Nat) : Nat := bufferBase lay
def lfBytes (lay : Nat) : Nat := if lay = 0 then 896 else 704
def lfBlocks (lay : Nat) : Nat := if lay = 0 then 14 else 11
def lfSlot (lay j : Nat) : Nat := if lay = 0 then slotT j else bufferBias lay + slotL j
def stabBits (lay : Nat) : Nat := if lay = 1 then 7 else 6
def lfKeepK (lay : Nat) : List (Reg × Word) :=
  [(.x2, 0x7fc00), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x30, 7), (if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))),
   (.x9, BitVec.ofNat 64 TOPB9)] ++
  (if lay = 0 then [] else [(.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x6, 0x10000), (.x27, 0x3fe00)])
def lfK (lay : Nat) : List (Reg × Word) := postLf lay ++ lfKeepK lay
structure LeafOut (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest)
    (u : MachineState) : Prop where
  pc : u.pc = pcOf (stabW lay.val ((route index lay).1 % 2 ^ stabBits lay.val))
  glob : Glob (lfK lay.val) w pk u
  s7 : lay = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1)
  t5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2
  len : ends.length = chainCount lay
  ends : ∀ j < chainCount lay, DigAt u (lfSlot lay.val j) (ends.getD j 0)
  T0 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 16)) =
    T3.hyperWord lay.val ((route index lay).2 * 2 ^ height lay + (route index lay).1)
  /-- C3: the leaf tweak's high word is witness memory (`wleafHigh`). -/
  T1 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 24)) = ClaudeWCT.W9.T3M.wleafHigh w lay
  orig : Verify.Orig w (fun o => 8096 ≤ o ∧
    o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) u
  /-- C3: the top leaf's leading 16 bytes are the witness pad (`wtopLeafPad`). -/
  topPad : lay = 0 → DigAt u 25200 (ClaudeWCT.W9.T3M.wtopLeafPad w)
  /-- Campaign R6: the top leaf's 32-byte gap after the tweak is the witness gap (`wtopLeafGap`, hashed as found). -/
  topGap : lay = 0 → DigAt u 25232 (ClaudeWCT.W9.T3M.wtopLeafGap w).1 ∧ DigAt u 25248 (ClaudeWCT.W9.T3M.wtopLeafGap w).2
  bufferOrig : lay ≠ 0 → Verify.Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 23208) u
theorem LeafOut.hashInput {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {index : Nat} {lay : Layer} {ends : List Digest}
    {u : MachineState} (h : LeafOut w pk index lay ends u) :
    hashInput u = toQ (pad64 (lfIn w lay (route index lay).2 (route index lay).1 ends)) ∧
      (toQ (pad64 (lfIn w lay (route index lay).2 (route index lay).1 ends))).blocks = lfBlocks lay.val := by
  have h10 := h.glob.1 (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11 := h.glob.1 (.x11, BitVec.ofNat 64 (lfBytes lay.val)) (by simp [lfK, postLf, lfBytes])
  have hT0 := h.T0
  have hT1 := h.T1
  have hS := h.ends
  have hn := h.len
  by_cases h0 : lay = 0
  · subst h0
    exact topLeaf_hashInput u _ _ _ _ _ ends hn h10 h11 hS (h.topPad rfl) (h.topGap rfl).1 (h.topGap rfl).2 hT0 hT1
  · have hc := LCtx.chainCount_lower lay h0
    have hv : lay.val ≠ 0 := fun hv => h0 (Fin.ext hv)
    simp only [lfBase, lfBytes, lfSlot, lfBlocks, if_neg hv] at h10 h11 hT0 hT1 hS ⊢
    rw [hc] at hn hS
    have hb : bufferBase lay.val = bufferBias lay.val + 768 := by
      fin_cases lay <;> first | exact absurd rfl h0 | rfl
    have hm : bufferBias lay.val % 16 = 0 := by fin_cases lay <;> decide +kernel
    have hbd : bufferBias lay.val + 1472 < 2 ^ 64 := by fin_cases lay <;> decide +kernel
    rw [hb] at h10 hT0 hT1
    have e : lfIn w lay (route index lay).2 (route index lay).1 ends = ClaudeWCT.WCT9.leafInputW lay (route index lay).2
        (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w lay) ends :=
      leafInputWG_low lay h0 _ _ _ _ _ _
    rw [e]
    exact lowLeaf_hashInput u lay h0 _ _ _ _ ends (bufferBias lay.val) hm hbd hn h10 h11 hS hT0 hT1

theorem glob_frame {gk gk' : List (Reg × Word)} {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (hG : Glob gk w pk s) (hf : Frame s t W)
    (hW : ∀ A, W A → 544 ≤ A ∧ (A < 0xB58 ∨ 0xB98 ≤ A) ∧ A < 2 ^ 23) (hk : ∀ p ∈ gk', t.getReg p.1 = p.2) :
    Glob gk' w pk t := by
  obtain ⟨-, hH, hP, hZ, hh, hD⟩ := hG
  have hn : ∀ A, A < 544 → ¬ W A := fun A hA h => by have := hW A h; omega
  refine ⟨hk, fun j hj4 hj => ?_, ⟨?_, ?_⟩, fun a ha => ?_, ?_, ?_⟩
  · rw [hf.get (by unfold WIT; omega) (fun h => by have := hW _ h; unfold WIT at this; omega)]; exact hH j hj4 hj
  · exact (hf.get (A := 0xA0) (by norm_num) (hn _ (by norm_num))).trans hP.1
  · exact (hf.get (A := 0xA8) (by norm_num) (hn _ (by norm_num))).trans hP.2
  · have ha' : a < 544 := by simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
    rw [hf.get (by omega) (hn _ ha')]; exact hZ a ha
  · unfold PHalf CTRW at *; rw [hf.get (by norm_num) (hn _ (by norm_num))]; exact hh
  · exact hD.congr (fun A hA hB => hf.get (by omega) (fun hw => by
      have := hW A hw
      unfold Verify.TAB at hA
      omega))
theorem land4 (n k : Nat) : n &&& (4 * (2 ^ k - 1)) = 4 * (n / 4 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (4 : Nat) = 2 ^ 2 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h2 : 2 ≤ j
  · simp only [h2, decide_true, Bool.true_and, show j - 2 + 2 = j by omega]
    by_cases hj : j - 2 < k
    · simp [hj]
    · simp [hj]
  · simp [h2]
theorem stabMask_eq (lay : Nat) : stabMask lay = 4 * (2 ^ stabBits lay - 1) := by
  unfold stabMask stabBits; split <;> rfl
theorem tgtLf0_eval (t : MachineState) (leaf : Nat) (hl : leaf < 4096)
    (h31 : t.getReg .x31 = BitVec.ofNat 64 leaf) :
    (tgtLf 0).eval t = pcOf (stabW 0 (leaf % 2 ^ stabBits 0)) := by
  change ((((t.getReg .x31 &&& BitVec.ofNat 64 63) + BitVec.ofNat 64 1117) <<< ((BitVec.ofNat 64 9).toNat % 64)) +
      BitVec.ofNat 64 320) &&& ~~~(1#64) = BitVec.ofNat 64 (0x1000 + 4 * (142032 + 128 * (leaf % 64)))
  have hm : (t.getReg .x31 &&& BitVec.ofNat 64 63) = BitVec.ofNat 64 (leaf % 64) := by
    rw [h31]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_andc _ 63 (by norm_num), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hmod : leaf % 2 ^ 64 = leaf := Nat.mod_eq_of_lt (by omega)
    rw [hmod, show (63 : Nat) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hm, ofNat_add_ofNat]
  have hs : (BitVec.ofNat 64 (leaf % 64 + 1117) <<< ((BitVec.ofNat 64 9).toNat % 64)) + BitVec.ofNat 64 320 =
      BitVec.ofNat 64 (0x1000 + 4 * (142032 + 128 * (leaf % 64))) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, toNat_sll _ 9 (by norm_num), BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hs, even_andNot1' _ (by omega)]
theorem stabBits_le (lay : Layer) : stabBits lay.val ≤ hL lay.val := by fin_cases lay <;> decide +kernel
theorem stabIdx_lt (lay : Nat) : stabIdx lay < 2 ^ 32 := by
  unfold stabIdx
  rcases lay with _ | _ | _ | _ | n <;> simp
/-- Campaign R6: the machine state at a final tail `ckTail d` (after the checksum chain 51 with digit `d < 8`): the
52 chain ends at `slotT j = 25264 + 16 j`, the witness pad at 25200, the witness gap at 25232/25248, the tweak high
word at 25224 (all witness memory as found). -/
structure TopLeafReady (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : ∃ d, d < 8 ∧ t.pc = pcOf (Nonbinary.ckTail d)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index 0).1)
  t5 : t.getReg .x31 = BitVec.ofNat 64 (route index 0).1
  word : t.getReg .x28 = leafWord 0 (route index 0).2 (route index 0).1
  len : ends.length = 52
  ends : ∀ j < 52, DigAt t (slotT j) (ends.getD j 0)
  orig : Verify.Orig w (fun o => 8096 ≤ o ∧
    o < ClaudeWCT.W9.T3M.layerBase 0 + 16 * ClaudeWCT.W9.T3M.pathSlots 0) t
  /-- C3: the top leaf pad and tweak high word are witness memory. -/
  topPad : DigAt t 25200 (ClaudeWCT.W9.T3M.wtopLeafPad w)
  /-- Campaign R6: the 32-byte gap after the tweak is witness memory (`wtopLeafGap`). -/
  topGap : DigAt t 25232 (ClaudeWCT.W9.T3M.wtopLeafGap w).1 ∧ DigAt t 25248 (ClaudeWCT.W9.T3M.wtopLeafGap w).2
  topHi : t.getMem (BitVec.ofNat 64 25224) = ClaudeWCT.W9.T3M.wleafHigh w 0
theorem lfKeepK_keep : (lfKeepK 0).all (fun p => decide (p.1 ∈ keepLfAll 0)) = true := by decide +kernel
/-- Campaign R6: the final tail (7 steps, no sum check) stores the leaf label and jumps to the top merkle entry. -/
theorem leafT_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (ends : List Digest) (t : MachineState) (ht : TopLeafReady w pk index c ends t) :
    ∃ u, Steps image t 7 7 u ∧ LeafOut w pk index 0 ends u := by
  obtain ⟨d, hd, hp⟩ := ht.pc
  obtain ⟨u, hu⟩ := spec_run (fusedLeafCheck6_at d hd) t hp ht.glob.1 (by simp [specLf]) (by simp)
  have hst := hu.steps
  rw [show (specLf 0).steps = 7 from rfl, show (specLf 0).cycles = 7 from rfl] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf 0) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 25216⟩, .reg .x28)] A := by
    intro A; rw [hu.mem]; simp [specLf, bufferBase]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 25216 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    simp
    omega
  have hlf := leaf_lt index 0
  refine ⟨?_, ?_, ?_, ?_, ht.len, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.spc (tgtLf 0) (by simp [specLf])]
    exact tgtLf0_eval t _ hlf ht.t5
  · have hGu := hu.glob _ w pk ht.glob (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have hkp : p.1 ∈ keepLfAll 0 := by
        have := List.all_eq_true.mp lfKeepK_keep p hp
        simpa using this
      rw [hkeep _ hkp]
      exact ht.keep p hp
  · intro _
    rw [hkeep .x23 (by simp [keepLfAll]), ht.s7]
  · intro h; exact absurd rfl h
  · intro j hj
    have hj' : j < 52 := hj
    have e := ht.ends j hj'
    simp only [lfSlot, if_pos rfl]
    have hsl : 25264 ≤ slotT j ∧ slotT j ≤ 26080 := by unfold slotT; omega
    exact ⟨(hfr (slotT j) (by omega) (by omega)).trans e.1,
      (hfr (slotT j + 8) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase (0 : Layer).val + 16 = 25216 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval]
    exact ht.word
  · rw [show lfBase (0 : Layer).val + 24 = 25224 from rfl, hfr 25224 (by norm_num) (by norm_num)]
    exact ht.topHi
  · exact (hu.orig_const ht.orig).mono (fun o ho => ⟨ho, by
      have hhi : o < 8864 := ho.2
      simp only [lfAllowed, bufferBase, List.getD_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      unfold WIT
      constructor <;> omega⟩)
  · intro _
    exact ⟨(hfr 25200 (by norm_num) (by norm_num)).trans ht.topPad.1,
      (hfr (25200 + 8) (by norm_num) (by norm_num)).trans ht.topPad.2⟩
  · intro _
    exact ⟨⟨(hfr 25232 (by norm_num) (by norm_num)).trans ht.topGap.1.1,
      (hfr (25232 + 8) (by norm_num) (by norm_num)).trans ht.topGap.1.2⟩,
      ⟨(hfr 25248 (by norm_num) (by norm_num)).trans ht.topGap.2.1,
      (hfr (25248 + 8) (by norm_num) (by norm_num)).trans ht.topGap.2.2⟩⟩
  · intro h; exact (h rfl).elim
end SigGolfCandidate.T3M
end
end

namespace SigGolfCandidate.T3M.LCtx
open SigGolfCandidate.T3
theorem canonical_decode_lower_sum (lay : Layer) (hlay : lay ≠ 0) (value : Digest) (ds : List Nat)
    (h : canonicalDecode lay value = some ds) : ds.length = 43 ∧ ds.sum = canonicalTarget lay := by
  have hd : decode (1 : Layer) value = some ds := by
    simpa only [canonicalDecode, ClaudeWCT.WCT9.CanonicalPolicy.decode,
      ClaudeWCT.WCT9.CanonicalPolicy.normalLayer, if_neg hlay] using h
  simpa only [canonicalTarget, ClaudeWCT.WCT9.CanonicalPolicy.normalLayer, if_neg hlay] using
    decode_lower_sum (1 : Layer) (by decide) value ds hd
end SigGolfCandidate.T3M.LCtx
