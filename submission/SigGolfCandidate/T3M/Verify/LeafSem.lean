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
def tailRejBr (d : Bool) : Br := ⟨.ne, .reg .x24, kw 0, d⟩
def lfDirsT : List Dir := [.br false, .jmp]
def specLfT : Spec := { specLf 0 with steps := 13, brs := [tailRejBr false], cycles := 13 }
def specRejT : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], (specLf 0).mem, rejEcall, true, 13, [tailRejBr true], none, 13⟩
def fusedLeafCheck (dB dC : Nat) : Bool :=
  specB [] [] baseK (runAt (leafK 0) [] (Nonbinary.pcX 17 dB dC) lfDirsT) specLfT [] (postLf 0) (keepLfAll 0)
def tailRejCheck (dB dC : Nat) : Bool :=
  specB [] [] [] (runAt (leafK 0) [] (Nonbinary.pcX 17 dB dC) [.br true]) specRejT [] [] []
theorem fusedLeafChecks : ((List.range 16).all fun k => fusedLeafCheck (k / 4) (k % 4)) = true := by
  decide +kernel
theorem tailRejChecks : ((List.range 16).all fun k => tailRejCheck (k / 4) (k % 4)) = true := by
  decide +kernel
theorem fusedLeafCheck_at (dB dC : Nat) (hB : dB < 4) (hC : dC < 4) :
    fusedLeafCheck dB dC = true := by
  have h := List.all_eq_true.mp fusedLeafChecks (4*dB+dC) (List.mem_range.mpr (by omega))
  have hd : (4*dB+dC)/4=dB := by omega
  have hm : (4*dB+dC)%4=dC := by omega
  simpa [hd, hm] using h
theorem tailRejCheck_at (dB dC : Nat) (hB : dB < 4) (hC : dC < 4) :
    tailRejCheck dB dC = true := by
  have h := List.all_eq_true.mp tailRejChecks (4*dB+dC) (List.mem_range.mpr (by omega))
  have hd : (4*dB+dC)/4=dB := by omega
  have hm : (4*dB+dC)%4=dC := by omega
  simpa [hd, hm] using h
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
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++ SphincsSecurity.bytesLE 16 (header 2 lay.val tree 0 leaf) ++
    (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16)
theorem leafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := rfl
def dw (e : Digest) : List (BitVec 64) := [e.extractLsb' 0 64, e.extractLsb' 64 64]
theorem flatMap_length16 : ∀ (L : List Digest), (L.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * L.length
  | [] => rfl
  | e :: L => by
    rw [List.flatMap_cons, List.length_append, flatMap_length16 L, SphincsSecurity.bytesLE_length]; simp; ring
theorem leafInput_length (lay : Layer) (tree leaf : Nat) (ends : List Digest) (h : 1 ≤ ends.length) :
    (leafInput lay tree leaf ends).length = 16 * (ends.length + 1) := by
  unfold leafInput
  rw [List.length_append, List.length_append, flatMap_length16, SphincsSecurity.bytesLE_length,
    SphincsSecurity.bytesLE_length, List.length_drop]
  omega
theorem wordsOf_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    wordsOf (leafInput lay tree leaf ends) =
      dw (ends.getD 0 0) ++ [BitVec.ofNat 64 (hdr0 2 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf)] ++
        (ends.drop 1).flatMap dw := by
  unfold leafInput
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_flatMap16]
  rfl
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
theorem lowLeaf_hashInput (t : MachineState) (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 43) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x300)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 704) (hS : ∀ j < 43, DigAt t (slotL j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x310) = BitVec.ofNat 64 (hdr0 2 lay.val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x318) = BitVec.ofNat 64 (hdr1 tree leaf)) :
    hashInput t = toQ (pad64 (leafInput lay tree leaf ends)) ∧ (toQ (pad64 (leafInput lay tree leaf ends))).blocks = 11 := by
  have hl : (leafInput lay tree leaf ends).length = 64 * (10 + 1) := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 10 0x300 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [wordsOf_leafInput, show 8 * (10 + 1) = 2 + (2 + 2 * (ends.drop 1).length) by simp [hn],
    readWords_add, readWords_add, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotL 0 = 0x300 from rfl] at e0
  rw [show 0x300 + 8 * 2 = 0x310 by rfl, show 0x310 + 8 = 0x318 by rfl, show 0x310 + 8 * 2 = 0x320 by rfl,
    e0.1, show 0x300 + 8 = (0x300 : Nat) + 8 from rfl, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x320 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotL (j + 1) = 0x320 + 16 * j by unfold slotL; simp; omega] at this)]
  rfl
theorem topLeaf_hashInput (t : MachineState) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 54) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x200)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 896) (hS : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x210) = BitVec.ofNat 64 (hdr0 2 (0 : Layer).val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x218) = BitVec.ofNat 64 (hdr1 tree leaf))
    (hZ0 : t.getMem (BitVec.ofNat 64 0x570) = 0) (hZ1 : t.getMem (BitVec.ofNat 64 0x578) = 0) :
    hashInput t = toQ (pad64 (leafInput 0 tree leaf ends)) ∧ (toQ (pad64 (leafInput 0 tree leaf ends))).blocks = 14 := by
  have hl0 : (leafInput 0 tree leaf ends).length = 880 := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  have hl : (pad64 (leafInput 0 tree leaf ends)).length = 64 * (13 + 1) := by
    unfold pad64; rw [List.length_append, List.length_replicate, hl0]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 13 0x200 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [Verify.wordsOf_pad64 _ (by rw [hl0]), hl0, wordsOf_leafInput,
    show 8 * (13 + 1) = 2 + (2 + (2 * (ends.drop 1).length + 2)) by simp [hn],
    readWords_add, readWords_add, readWords_add, readWords_two, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotT 0 = 0x200 from rfl] at e0
  have hd : (ends.drop 1).length = 53 := by simp [hn]
  rw [show 0x200 + 8 * 2 = 0x210 by rfl, show 0x210 + 8 = 0x218 by rfl, show 0x210 + 8 * 2 = 0x220 by rfl,
    e0.1, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x220 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotT (j + 1) = 0x220 + 16 * j by unfold slotT; simp; omega] at this),
    hd, show 0x220 + 8 * (2 * 53) = 0x570 by rfl, show 0x570 + 8 = 0x578 by rfl, hZ0, hZ1]
  simp [List.append_assoc, dw]
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def lfBase (lay : Nat) : Nat := if lay = 0 then 512 else 768
def lfBytes (lay : Nat) : Nat := if lay = 0 then 896 else 704
def lfBlocks (lay : Nat) : Nat := if lay = 0 then 14 else 11
def lfSlot (lay j : Nat) : Nat := if lay = 0 then slotT j else slotL j
def stabBits (lay : Nat) : Nat := if lay = 1 then 7 else 6
def lfKeepK (lay : Nat) : List (Reg × Word) :=
  [(.x2, 0x3fe00), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x30, 7), (if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))),
   (.x1, BitVec.ofNat 64 TOPBASE)] ++
  (if lay = 0 then [] else [(.x9, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x6, 0x10000),
    (.x8, BitVec.ofNat 64 0x400000)])
def lfK (lay : Nat) : List (Reg × Word) := postLf lay ++ lfKeepK lay
structure LeafOut (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState) :
    Prop where
  pc : u.pc = pcOf (stabW lay.val ((route index lay).1 % 2 ^ stabBits lay.val))
  glob : Glob (lfK lay.val) w pk u
  s7 : lay = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1)
  t5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2
  len : ends.length = chainCount lay
  ends : ∀ j < chainCount lay, DigAt u (lfSlot lay.val j) (ends.getD j 0)
  T0 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 16)) = BitVec.ofNat 64 (hdr0 2 lay.val (route index lay).2 0)
  T1 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 24)) =
    BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1)
  zero : lay = 0 → u.getMem (BitVec.ofNat 64 0x570) = 0 ∧ u.getMem (BitVec.ofNat 64 0x578) = 0
  orig : Verify.Orig w (fun o => 8136 ≤ o ∧ o < ClaudeWCT.W9.T3M.layerBase lay + 64 * height lay) u
theorem LeafOut.hashInput {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {index : Nat} {lay : Layer} {ends : List Digest}
    {u : MachineState} (h : LeafOut w pk index lay ends u) :
    hashInput u = toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends)) ∧
      (toQ (pad64 (leafInput lay (route index lay).2 (route index lay).1 ends))).blocks = lfBlocks lay.val := by
  have h10 := h.glob.1 (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11 := h.glob.1 (.x11, BitVec.ofNat 64 (lfBytes lay.val)) (by simp [lfK, postLf, lfBytes])
  have hT0 := h.T0
  have hT1 := h.T1
  have hS := h.ends
  have hn := h.len
  by_cases h0 : lay = 0
  · subst h0
    have r := topLeaf_hashInput u _ _ ends hn h10 h11 hS hT0 hT1 (h.zero rfl).1 (h.zero rfl).2
    exact ⟨r.1, r.2⟩
  · have hc := LCtx.chainCount_lower lay h0
    have hv : lay.val ≠ 0 := fun hv => h0 (Fin.ext hv)
    simp only [lfBase, lfBytes, lfSlot, lfBlocks, if_neg hv] at h10 h11 hT0 hT1 hS ⊢
    rw [hc] at hn hS
    exact lowLeaf_hashInput u lay _ _ ends hn h10 h11 hS hT0 hT1
theorem glob_frame {gk gk' : List (Reg × Word)} {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (hG : Glob gk w pk s) (hf : Frame s t W)
    (hW : ∀ A, W A → 0x140 ≤ A ∧ (A < 0x800 ∨ 0x840 ≤ A) ∧ A < 2 ^ 23) (hk : ∀ p ∈ gk', t.getReg p.1 = p.2) :
    Glob gk' w pk t := by
  obtain ⟨-, hH, hP, hZ, hh, hD⟩ := hG
  have hn : ∀ A, A < 0x140 → ¬ W A := fun A hA h => by have := hW A h; omega
  refine ⟨hk, fun j hj => ?_, ⟨?_, ?_⟩, fun a ha => ?_, ?_, ?_⟩
  · rw [hf.get (by unfold WIT; omega) (fun h => by have := hW _ h; unfold WIT at this; omega)]; exact hH j hj
  · exact (hf.get (A := 0xA0) (by norm_num) (hn _ (by norm_num))).trans hP.1
  · exact (hf.get (A := 0xA8) (by norm_num) (hn _ (by norm_num))).trans hP.2
  · have ha' : a < 0x140 := by simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
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
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (4096 + leaf)) :
    (tgtLf 0).eval t = pcOf (stabW 0 (leaf % 2 ^ stabBits 0)) := by
  change (((t.getReg .x23 &&& BitVec.ofNat 64 63) + BitVec.ofNat 64 2042) <<< ((BitVec.ofNat 64 8).toNat % 64)) &&&
      ~~~(1#64) = BitVec.ofNat 64 (0x1000 + 4 * (129664 + 64 * (leaf % 64)))
  have hm : (t.getReg .x23 &&& BitVec.ofNat 64 63) = BitVec.ofNat 64 (leaf % 64) := by
    rw [h23]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_andc _ 63 (by norm_num), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hmod : (4096 + leaf) % 2 ^ 64 = 4096 + leaf := Nat.mod_eq_of_lt (by omega)
    rw [hmod, show (63 : Nat) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hm, ofNat_add_ofNat]
  have hs : (BitVec.ofNat 64 (leaf % 64 + 2042) <<< ((BitVec.ofNat 64 8).toNat % 64)) =
      BitVec.ofNat 64 (0x1000 + 4 * (129664 + 64 * (leaf % 64))) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sll _ 8 (by norm_num), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hs, even_andNot1' _ (by omega)]
theorem stabBits_le (lay : Layer) : stabBits lay.val ≤ hL lay.val := by fin_cases lay <;> decide
theorem stabIdx_lt (lay : Nat) : stabIdx lay < 2 ^ 32 := by
  unfold stabIdx
  rcases lay with _ | _ | _ | _ | n <;> simp
theorem hw2_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 2 lay.val = hdr0 2 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring
structure TopLeafReady (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : ∃ dB dC, dB < 4 ∧ dC < 4 ∧ t.pc = pcOf (Nonbinary.pcX 17 dB dC)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (2 ^ hL 0 + (route index 0).1)
  t5 : True
  tp : t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index 0).2 (route index 0).1)
  len : ends.length = 54
  ends : ∀ j < 54, DigAt t (slotT j) (ends.getD j 0)
  orig : Verify.Orig w (fun o => 8136 ≤ o ∧ o < ClaudeWCT.W9.T3M.layerBase 0 + 64 * height 0) t
  s8 : t.getReg .x24 = 0
theorem leafT_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (ends : List Digest) (t : MachineState) (ht : TopLeafReady w pk index c ends t) :
    ∃ u, Steps image t 13 13 u ∧ LeafOut w pk index 0 ends u := by
  obtain ⟨dB, dC, hB, hC, hp⟩ := ht.pc
  obtain ⟨u, hu⟩ := spec_run (fusedLeafCheck_at dB dC hB hC) t hp ht.glob.1
    (by
      intro b hb
      simp only [specLfT, List.mem_singleton] at hb
      subst hb
      simp [Br.holds, tailRejBr, CmpOp.eval, E.eval, kw, ht.s8]) (by simp)
  have hst := hu.steps
  rw [show specLfT.steps = 13 from rfl, show specLfT.cycles = 13 from rfl] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf 0) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0),
      (⟨none, BitVec.ofNat 64 536⟩, .reg .x4), (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))] A := by
    intro A; rw [hu.mem]; simp [specLfT, specLf]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 1400 → A ≠ 1392 → A ≠ 536 → A ≠ 528 →
      u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega
  have htr := tree_lt index 0 hidx
  have hlf := leaf_lt index 0
  refine ⟨?_, ?_, ?_, ?_, ht.len, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rw [hu.spc (tgtLf 0) (by simp [specLfT, specLf])]
    exact tgtLf0_eval t _ hlf ht.s7
  · have hGu := hu.glob _ w pk ht.glob (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have hkp : p.1 ∈ keepLfAll 0 := by
        change p ∈ lfKeepK 0 at hp
        simp [lfKeepK] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepLfAll]
      rw [hkeep _ hkp]
      exact ht.keep p hp
  · intro _
    rw [hkeep .x23 (by simp [keepLfAll]), ht.s7]
    rfl
  · intro h; exact absurd rfl h
  · intro j hj
    have hj' : j < 54 := hj
    have e := ht.ends j hj'
    simp only [lfSlot, if_pos rfl]
    have hsl : slotT j = 512 ∨ (544 ≤ slotT j ∧ slotT j ≤ 1376) := by unfold slotT; split <;> omega
    exact ⟨(hfr (slotT j) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (slotT j + 8) (by omega) (by omega) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase (0 : Layer).val + 16 = 528 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval, kw]
    exact hw2_hdr0 0 _ htr |>.symm ▸ rfl
  · rw [show lfBase (0 : Layer).val + 24 = 536 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    exact ht.tp
  · rw [show (0x570 : Nat) = 1392 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_neg (by norm_num),
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · rw [show (0x578 : Nat) = 1400 by norm_num, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    rfl
  · exact (hu.orig_const ht.orig).mono (fun o ho => ⟨ho, by simp⟩)
theorem leafT_reject (t : MachineState)
    (hp : ∃ dB dC, dB < 4 ∧ dC < 4 ∧ t.pc = pcOf (Nonbinary.pcX 17 dB dC))
    (hk : KnownOK (leafK 0) t) (h24 : t.getReg .x24 ≠ 0) :
    ∃ u, Steps image t 13 13 u ∧ fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 1 := by
  obtain ⟨dB, dC, hB, hC, hpc⟩ := hp
  obtain ⟨u, hu⟩ := spec_run (tailRejCheck_at dB dC hB hC) t hpc hk
    (by
      intro b hb
      simp only [specRejT, List.mem_singleton] at hb
      subst hb
      simp [Br.holds, tailRejBr, CmpOp.eval, E.eval, kw]
      exact h24) (by simp)
  refine ⟨u, hu.steps, hu.ecall rfl, ?_, ?_⟩
  · exact hu.regs (.x5, kw 1) (by simp [specRejT])
  · exact hu.regs (.x10, kw 1) (by simp [specRejT])
end SigGolfCandidate.T3M
end
end
