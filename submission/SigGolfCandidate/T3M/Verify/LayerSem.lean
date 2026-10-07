import SigGolfCandidate.T3M.Verify.LayerRuns
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Verify.ChainGood
import SigGolfCandidate.T3M.Verify.LowerDecode

section

section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.preK lay else
  (T3M.preK lay).filter (fun p => p.1 != .x10 && p.1 != .x12) ++
    [(.x22, BitVec.ofNat 64 (s6v (lay + 1)))]
def bK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.bK lay else
  (T3M.bK lay).filter (fun p => p.1 != .x10) ++
    [(.x10, BitVec.ofNat 64 (x10In lay))]
def ctrE (lay : Nat) : E :=
  if lay = 3 then T3M.ctrE lay else .un (.ld .wu 0) (.ld (kw (x10In lay + 32)))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay, kw 0x400000, d⟩
def headerWrites (lay : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (x10In lay + 24)⟩, tp0E lay),
   (⟨none, BitVec.ofNat 64 (x10In lay + 16)⟩, kw (hw 4 lay))]
def specA (lay p : Nat) : Spec :=
  if lay = 3 then T3M.specA lay p else
  ⟨if lay = 0 then [(.x4, tp0E lay), (.x23, s7E lay), (.x3, ctrE lay), (.x12, .reg .x12)]
   else [(.x4, tp0E lay), (.x23, s7E lay), (.x31, treeE lay), (.x3, ctrE lay),
     (.x28, .bin .sll (.reg (rReg lay)) (kw 16)), (.x12, .reg .x12)],
   headerWrites lay, p + stepsA lay, true, stepsA lay,
   [ctrBr lay false], none, stepsA lay⟩
def rejA (lay p : Nat) : Spec :=
  if lay = 3 then T3M.rejA lay p else
  ⟨[(.x5, kw 1), (.x10, kw 1)], headerWrites lay,
   rejEcall, true, stepsA lay + 3, [ctrBr lay true], none, stepsA lay + 3⟩
def bKB (lay : Nat) : List (Reg × Word) := (bK lay).filter (fun p => p.1 != .x12)
def oblB : List Oblig := [.valid ⟨some (.reg .x12), 8⟩ 8, .valid ⟨some (.reg .x12), 0⟩ 8]
def allowed (lay : Nat) : List Nat :=
  if lay = 3 then [] else [x10In lay + 16, x10In lay + 24]
def setupCheck (lay p : Nat) : Bool :=
  specB (allowed lay) [] baseK (runAt (preK lay) [] (setupPc lay p) [.br (setupAcceptDir lay)])
    (specA lay p) [] (bK lay) keepA &&
  specB (allowed lay) [] [] (runAt (preK lay) [] (setupPc lay p) [.br (!setupAcceptDir lay)]) (rejA lay p) [] [] []
def copyCheck (lay p : Nat) : Bool :=
  setupCheck lay p &&
  (if lay = 0 then true else
    specB [] [] baseK (runAt (bKB lay) [] (p + stepsA lay + 1)
      [.br false, .br false, .jmp]) (specBl lay p) oblB (postBlC lay p) keepB &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1)
      [.br false, .br true]) (rejCk lay) oblB [] [] &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1)
      [.br true]) rejSpare oblB [] [])
def layerCheck (lay lo n : Nat) : Bool :=
  (List.range' lo n).all fun c => copyCheck lay (trPc lay c)
end SigGolfCandidate.T3M.BC
end
section
namespace SigGolfCandidate.T3M.BC
set_option maxRecDepth 100000
theorem layerCheck_3 : layerCheck 3 0 1 = true := by decide +kernel
theorem layerCheck_2 : layerCheck 2 0 64 = true := by decide +kernel
theorem layerCheck_1 : layerCheck 1 0 64 = true := by decide +kernel
theorem layerCheck_0a : layerCheck 0 0 64 = true := by decide +kernel
theorem layerCheck_0b : layerCheck 0 64 64 = true := by decide +kernel
end SigGolfCandidate.T3M.BC
end
end

section


namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def CounterWord : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (j : Nat),
  LoadKind.wu.fromWord (wword w j) 0 = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wle32 w (8 * j)).toNat
theorem counterWord : CounterWord := fun w j => by
  apply BitVec.eq_of_toNat_eq
  simp [LoadKind.fromWord, extractWord32, wword_toNat, ClaudeWCT.W9.T3M.wle32,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, ← Nat.mul_assoc]
set_option maxRecDepth 100000
theorem nCopy_eq : nCopy 3 = 1 ∧ nCopy 2 = 64 ∧ nCopy 1 = 64 ∧ nCopy 0 = 128 := by decide
theorem copyCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : copyCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ lo n, layerCheck lay lo n = true → lo ≤ c → c < lo + n → copyCheck lay (trPc lay c) = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · by_cases h : c < 64
    · exact hall 0 64 layerCheck_0a (by omega) (by omega)
    · exact hall 64 64 layerCheck_0b (by omega) (by omega)
  · exact hall 0 64 layerCheck_1 (by omega) (by omega)
  · exact hall 0 64 layerCheck_2 (by omega) (by omega)
  · exact hall 0 1 layerCheck_3 (by omega) (by omega)
def CounterPadBytes : Prop := ∀ (c : BitVec 32) (pad : BitVec 96),
  SphincsSecurity.bytesLE 4 c ++ SphincsSecurity.bytesLE 12 pad =
    SphincsSecurity.bytesLE 16 (pad ++ c)
theorem counterPadBytes : CounterPadBytes := fun c pad => by
  apply readLE_inj (by simp [SphincsSecurity.bytesLE_length])
  simp only [readLE_append, SphincsSecurity.bytesLE_length, readLE_bytesLE, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt c.isLt, Nat.shiftLeft_eq]
  omega
def CounterPadExtract : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (o : Nat),
  (w.extractLsb' (8 * (o + 4)) 96 ++ ClaudeWCT.W9.T3M.wle32 w o) = ClaudeWCT.W9.T3M.wdig w o
theorem counterPadExtract : CounterPadExtract := fun w o =>
  BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)
end SigGolfCandidate.T3M.BC
end

section




section
namespace SigGolfCandidate.T3M.Verify
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar7_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 63) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0x8e38e38e38e38e38 := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat ≤ 0x0e38e38e38e38e38 := by
    have hb' : b.toNat % 2 ^ 63 = b.toNat := Nat.mod_eq_of_lt hb
    have he := Nat.and_mod_two_pow (a := b.toNat) (b := (~~~M).toNat) (n := 63)
    rw [hb', Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hb)] at he
    rw [BitVec.toNat_and, he]
    simpa [hM] using (Nat.and_le_right : b.toNat &&& ((~~~M).toNat % 2 ^ 63) ≤ (~~~M).toNat % 2 ^ 63)
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
theorem swar2_period : ∀ i : Fin 62,
    (0x3333333333333333#64).getLsbD i.val = !(0x3333333333333333#64).getLsbD (i.val + 2) := by
  decide
theorem swar2_shift (x : BitVec 64) :
    (x >>> 2) &&& 0x3333333333333333#64 = (x &&& ~~~0x3333333333333333#64) >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 62
  · have hp := swar2_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 2 + i = i + 2 by omega]
    simp [show i + 2 < 64 by omega]
  · have hx : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar2_low (x : BitVec 64) : (x &&& ~~~0x3333333333333333#64).toNat % 4 = 0 := by
  have h7 : (x &&& ~~~0x3333333333333333#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 2
    · have : (0x3333333333333333#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      simp [this]
    · have : (3#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 3 < 2 ^ 2 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar2_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 34) :
    ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64)) +
      (((a + b) - ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64))) >>> 2) =
    ((a >>> 2) &&& 0x3333333333333333#64) + (a &&& 0x3333333333333333#64) +
      ((b >>> 2) &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64) := by
  rw [swar2_shift a, swar2_shift b]
  set M : BitVec 64 := 0x3333333333333333#64 with hM
  have la := swar2_low a
  have lb := swar2_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0xcccccccccccccccc := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat < 2 ^ 34 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_left hb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 2 = ((a &&& ~~~M) >>> 2) + ((b &&& ~~~M) >>> 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
end SigGolfCandidate.T3M.Verify
end
section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
open ClaudeWCT.WCT9 (LayerMsg)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
def layerEnd (lay : Nat) : Nat := [12360,15560,18696,21832].getD lay 0
def MsgAt (w : ClaudeWCT.W9.T3M.WBytes) (lay : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  match msg with
  | .forest root => lay = 3 ∧ DigAt s 256 root
  | .pair left right => lay < 3 ∧ DigAt s (x10In lay) left ∧
      DigAt s (x10In lay + 48) right ∧
      (∀ j, j = 4 ∨ j = 5 →
        s.getMem (BitVec.ofNat 64 (x10In lay + 8 * j)) =
          wword w ((x10In lay - WIT) / 8 + j))
structure LayerIn (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index lay : Nat) (msg : LayerMsg)
    (s : MachineState) : Prop where
  lay4 : lay < 4
  idx : index < 2 ^ 31
  copy : ∃ c, c < nCopy lay ∧ s.pc = pcOf (T3M.setupPc lay (trPc lay c))
  glob : Glob (preK lay) w pk s
  route : s.getReg (rReg lay) = BitVec.ofNat 64 (index / 2 ^ below lay)
  msg : MsgAt w lay msg s
  orig : Verify.Orig w (fun o => 8136 ≤ o ∧ o < layerEnd lay) s
  hdr3 : lay = 3 → s.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + 3 * 2 ^ 48) ∧
    s.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 22152
  dst0 : lay = 0 → ∃ d, s.getReg .x12 = BitVec.ofNat 64 d ∧ (d = 14408 ∨ d = 14456)
  dstL : lay = 1 ∨ lay = 2 → ∃ d, s.getReg .x12 = BitVec.ofNat 64 d ∧ (d = x10In lay ∨ d = x10In lay + 48)
  tp0 : lay = 0 → s.getReg .x4 = BitVec.ofNat 64 (hdr1 (T3.route index 0).2 (T3.route index 0).1)
structure EncPre (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index lay c : Nat)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc lay c + stepsA lay)
  glob : Glob (bK lay) w pk t
  tp : ∀ L : Layer, L.val = lay →
    t.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index L).2 (route index L).1)
  s7 : ∀ L : Layer, L.val = lay →
    t.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay (route index L).1)
  t5 : ∀ L : Layer, L.val = lay → lay ≠ 0 →
    t.getReg .x31 = BitVec.ofNat 64 (route index L).2
  orig : Verify.Orig w (fun o => 8136 ≤ o ∧ o < layerEnd lay) t
  hdr3 : lay = 3 → t.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + 3 * 2 ^ 48) ∧
    t.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 22152
  index3 : lay = 3 → t.getReg .x22 = BitVec.ofNat 64 index
  packed12 : lay = 1 ∨ lay = 2 →
    t.getReg .x28 = BitVec.ofNat 64 ((index / 2 ^ below lay) * 65536)
  dst0 : lay = 0 → ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ (d = 14408 ∨ d = 14456)
  dstL : lay = 1 ∨ lay = 2 → ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ (d = x10In lay ∨ d = x10In lay + 48)
def rejectSteps (lay : Nat) : Nat := stepsA lay + if lay = 3 then 1 else 3
def EncodingSetup : Prop :=
  ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ((ClaudeWCT.W9.T3M.wbcCtr w lay).toNat ≥ T3.counterLimit →
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
  ((ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < T3.counterLimit →
    ∃ t, Steps image s (stepsA lay.val) (stepsA lay.val) t ∧
      fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w lay) (ClaudeWCT.W9.T3M.wbcPad w lay))) ∧
      ∃ c, c < nCopy lay.val ∧ EncPre w pk index lay.val c t)
def layerLoop (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) : Nat → LayerMsg → T3.M (Option Digest)
  | 0, .forest root => pure (some root)
  | 0, .pair _ _ => pure none
  | n + 1, msg => ClaudeWCT.W9.T3M.layersBC w index (n + 1) msg
end SigGolfCandidate.T3M.BC
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
def layerEnd (lay : Nat) : Nat := [12360,15560,18696,21832].getD lay 0
theorem hL_eq (lay : Layer) : hL lay.val = height lay := by fin_cases lay <;> rfl
def slotT (i : Nat) : Nat := if i = 0 then 512 else 528 + 16 * i
theorem below_eq (lay : Layer) : below lay.val = (![19, 12, 6, 0] : Layer → Nat) lay := by fin_cases lay <;> rfl
theorem tgtL_eq (lay : Layer) : tgtL lay.val = target lay := by fin_cases lay <;> rfl
abbrev LayerIn := BC.LayerIn
theorem route_fst (index : Nat) (lay : Layer) : (route index lay).1 = index / 2 ^ below lay.val % 2 ^ hL lay.val := by
  simp only [route, below_eq, hL_eq]
theorem route_snd (index : Nat) (lay : Layer) : (route index lay).2 = index / 2 ^ (below lay.val + hL lay.val) := by
  simp only [route, below_eq, hL_eq]
theorem leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ hL lay.val := by
  rw [route_fst]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
theorem hL_le (lay : Layer) : 6 ≤ hL lay.val ∧ hL lay.val ≤ 12 := by fin_cases lay <;> decide
theorem tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  rw [route_snd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
theorem tree_actual_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 < 2 ^ (31 - height lay) := by
  rw [route_snd]
  fin_cases lay <;> norm_num [below, hL, height] at * <;> omega
theorem routed_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  rw [route_snd, route_fst, ← hL_eq]
  fin_cases lay <;> norm_num [below, hL] at * <;> omega
theorem leaf_lt32 (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h1 := leaf_lt index lay
  have h2 := (hL_le lay).2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega : hL lay.val ≤ 32))
theorem route_evals (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) (s : MachineState)
    (h : s.getReg (rReg lay.val) = BitVec.ofNat 64 (index / 2 ^ below lay.val)) :
    (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 ∧
      (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 ∧
      (tpE lay.val).eval s = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1) ∧
      (s7E lay.val).eval s = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
  have hl := leaf_lt index lay
  have ht := tree_lt index lay hidx
  have hl32 := leaf_lt32 index lay
  have hU : index / 2 ^ below lay.val < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlE : (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 := by
    rw [route_fst]
    unfold leafE
    split
    · rename_i h0
      have hl0 : lay = 0 := Fin.ext h0
      subst hl0
      simp only [E.eval]
      rw [show rReg (0 : Layer).val = .x31 from rfl] at h
      rw [h]; congr 1
      simp only [show below (0 : Layer).val = 19 from rfl, show hL (0 : Layer).val = 12 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [E.eval, BinOp.eval, h, kw]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hU, Nat.mod_eq_of_lt (show 2 ^ hL lay.val - 1 < 2 ^ 64 by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega),
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)))]
  have htE : (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 := by
    rw [route_snd]
    simp only [treeE, E.eval, BinOp.eval, h, kw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU,
      Nat.mod_eq_of_lt (show hL lay.val < 2 ^ 64 by have := (hL_le lay).2; omega),
      Nat.mod_eq_of_lt (show hL lay.val < 64 by have := (hL_le lay).2; omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  refine ⟨hlE, htE, ?_, ?_⟩
  · by_cases h0 : lay.val = 0
    ·
      have hz : (route index lay).2 = 0 := by
        have : lay = 0 := Fin.ext h0
        subst this
        rw [route_snd]; exact Nat.div_eq_of_lt (by simpa [below, hL] using hidx)
      simp only [tpE, if_pos h0, E.eval, BinOp.eval, hlE, kw]
      rw [hz, hdr1_eq _ _ (by norm_num) hl32]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
        show 32 % 64 = 32 from rfl, Nat.shiftLeft_eq]
      have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      ring
    simp only [tpE, if_neg h0, E.eval, BinOp.eval, hlE, htE, kw]
    rw [hdr1_eq _ _ ht hl32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
      show 32 % 64 = 32 from rfl, Nat.mod_eq_of_lt (show (route index lay).2 < 2 ^ 64 by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 32 < 2 ^ 64 by
        have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
        omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (route index lay).2 + 2 ^ 32 * (route index lay).1 < 2 ^ 64 by omega)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ht]
    ring
  · by_cases h0 : lay.val = 0
    · have hb0 : s7Bias lay.val = 2 ^ hL lay.val := by rw [h0]; rfl
      simp only [s7E, if_pos h0, E.eval, BinOp.eval, hlE, kw, dispatchHeap, hb0]
      apply BitVec.eq_of_toNat_eq
      have hp : 2 ^ hL lay.val < 2 ^ 64 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hL_le lay).2; omega
      rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt hp,
        Nat.mod_eq_of_lt (show 2 ^ hL lay.val + (route index lay).1 < 2 ^ 64 by
          have : 2 * 2 ^ hL lay.val ≤ 2 ^ 13 := by
            rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)
          omega)]
      rw [Nat.lor_comm, show 2 ^ hL lay.val = 2 ^ hL lay.val * 1 by ring, ← Nat.two_pow_add_eq_or_of_lt hl]
    · simp only [s7E, if_neg h0, E.eval, BinOp.eval, hlE, kw]
      change BitVec.ofNat 64 (route index lay).1 + BitVec.ofNat 64 (s7Bias lay.val) =
        BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1)
      rw [ofNat_add_ofNat]
      simp [dispatchHeap, Nat.add_comm]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 lowerSpare lowerWord)
theorem ctrE_eval (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) (hH : WitHdr w s) :
    (ctrE 3).eval s = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wbcCtr w 3).toNat := by
  have hw := hH 4 (by decide) (by decide)
  rw [show WIT + 8 * 4 = 0x810 + 8 * ((3 + 1) / 2) by unfold WIT; rfl] at hw
  show LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 (0x810 + 8 * ((3 + 1) / 2)))) (4 * ((3 + 1) % 2)) = _
  rw [hw]
  exact BC.counterWord w 4
theorem ctr_lt (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) : (ClaudeWCT.W9.T3M.wbcCtr w lay).toNat < 2 ^ 32 :=
  (ClaudeWCT.W9.T3M.wbcCtr w lay).isLt
theorem copy_parts (lay p : Nat) (h : BC.copyCheck lay p = true) :
    specB (BC.allowed lay) [] baseK (runAt (BC.preK lay) [] (T3M.setupPc lay p) [.br (T3M.setupAcceptDir lay)]) (BC.specA lay p) [] (BC.bK lay) keepA = true ∧
    specB (BC.allowed lay) [] [] (runAt (BC.preK lay) [] (T3M.setupPc lay p) [.br (!T3M.setupAcceptDir lay)]) (BC.rejA lay p) [] [] [] = true ∧
    (lay ≠ 0 →
      specB [] [] baseK (runAt (BC.bKB lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) BC.oblB
        (postBlC lay p) keepB = true ∧
      specB [] [] [] (runAt (BC.bKB lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) BC.oblB [] [] = true ∧
      specB [] [] [] (runAt (BC.bKB lay) [] (p + stepsA lay + 1) [.br true]) rejSpare BC.oblB [] [] = true) := by
  unfold BC.copyCheck BC.setupCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun h0 => ?_⟩
  rw [if_neg h0] at h3; simp only [Bool.and_eq_true] at h3; exact ⟨h3.1.1, h3.1.2, h3.2⟩
abbrev EncPre := BC.EncPre
theorem hw4_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 4 lay.val = hdr0 4 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring
theorem toNat_srl (x : Word) (k : Nat) (hk : k < 64) : (x >>> ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]
theorem toNat_sll (x : Word) (k : Nat) (hk : k < 64) :
    (x <<< ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq]
theorem toNat_andc (x : Word) (k : Nat) (hk : k < 2 ^ 64) : (x &&& BitVec.ofNat 64 k).toNat = x.toNat &&& k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
theorem toNat_remuc (x : Word) (k : Nat) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    (rv64_remu x (BitVec.ofNat 64 k)).toNat = x.toNat % k := by
  unfold rv64_remu
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'] at this
    simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, if_false, BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
structure AnsAt (u : MachineState) (a : BitVec 256) : Prop where
  lo : a6E.eval u = a.extractLsb' 0 64
  hi : a7E.eval u = a.extractLsb' 64 64
abbrev ansV (a : BitVec 256) : Nat := (a.extractLsb' 0 128).toNat
theorem ansV_split (a : BitVec 256) :
    ansV a = (a.extractLsb' 0 64).toNat + 2 ^ 64 * (a.extractLsb' 64 64).toNat := by
  simp only [ansV, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  generalize a.toNat = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
theorem ansV_lo (a : BitVec 256) : ansV a % 2 ^ 64 = (a.extractLsb' 0 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem ansV_hi (a : BitVec 256) : ansV a / 2 ^ 64 = (a.extractLsb' 64 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem a6E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a6E.eval u = a.extractLsb' 0 64 := h.lo
theorem a7E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a7E.eval u = a.extractLsb' 64 64 := h.hi
theorem toNat_clr63 (x : BitVec 64) : (BitVec.ofNat 64 (x.toNat % 2 ^ 63)).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_ofNat]; omega
theorem clr63_M1 (x : BitVec 64) :
    x &&& 0x71c71c71c71c71c7#64 = BitVec.ofNat 64 (x.toNat % 2 ^ 63) &&& 0x71c71c71c71c71c7#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and, toNat_clr63]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_land, Nat.testBit_mod_two_pow]
  by_cases hi : i < 63
  · simp [hi]
  · have : Nat.testBit 8198552921648689607 i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 8198552921648689607 < 2 ^ 63 by decide)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]
theorem add_clr63 (x y : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) :
    x + y = BitVec.ofNat 64 (x.toNat % 2 ^ 63) + BitVec.ofNat 64 (y.toNat % 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega
theorem sw1_bv (x y : BitVec 64) :
    (((x >>> 3) &&& 0x71c71c71c71c71c7#64) + (x &&& 0x71c71c71c71c71c7#64) +
      ((y >>> 3) &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64)).toNat = sw1 x.toNat y.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold sw1 mask3
  rfl
theorem swS1 (x y : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) :
    (((x &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64)) +
      (((x + y) - ((x &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64))) >>> 3)).toNat =
    sw1 (x.toNat % 2 ^ 63) (y.toNat % 2 ^ 63) := by
  rw [clr63_M1 x, clr63_M1 y, add_clr63 x y hx hy,
    Verify.swar7_eq _ _ (by rw [toNat_clr63]; omega), sw1_bv, toNat_clr63, toNat_clr63]
abbrev ansD (a : BitVec 256) : Digest := a.extractLsb' 0 128
theorem ansD_lo (a : BitVec 256) : (ansD a).toNat % 2 ^ 64 = (a.extractLsb' 0 64).toNat := ansV_lo a
theorem ansD_hi (a : BitVec 256) : (ansD a).toNat / 2 ^ 64 = (a.extractLsb' 64 64).toNat := ansV_hi a
theorem spare_iff (a : BitVec 256) :
    lowerSpare (ansD a) ↔ 2 ^ 63 ≤ (a.extractLsb' 0 64).toNat ∧ 2 ^ 63 ≤ (a.extractLsb' 64 64).toNat := by
  have hlo := ansD_lo a
  have hhi := ansD_hi a
  have hlt := (ansD a).isLt
  have h0 := (a.extractLsb' 0 64).isLt
  have h1 := (a.extractLsb' 64 64).isLt
  unfold lowerSpare
  constructor
  · rintro ⟨e0, e1⟩; constructor <;> omega
  · rintro ⟨e0, e1⟩; constructor <;> omega
theorem sumE_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hs : lowerSpare (ansD a)) :
    (sumE.eval u).toNat = lowSumS1 (ansD a) := by
  obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
  have he : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide
  have hs1 : (sw1E.eval u).toNat = sw1 ((a.extractLsb' 0 64).toNat % 2 ^ 63) ((a.extractLsb' 64 64).toNat % 2 ^ 63) := by
    simp only [sw1E, swLowE, E.eval, BinOp.eval, kw, M1c, he, a6E_eval h, a7E_eval h]
    exact swS1 _ _ h6 h7
  have hlo : (a.extractLsb' 0 64).toNat % 2 ^ 63 = (ansD a).toNat % 2 ^ 63 := by
    rw [← ansD_lo]; omega
  have hhi : (a.extractLsb' 64 64).toNat % 2 ^ 63 = (ansD a).toNat / 2 ^ 64 % 2 ^ 63 := by
    rw [← ansD_hi]
  unfold lowSumS1 lowSwar
  simp only [sumE, E.eval, BinOp.eval, kw]
  rw [toNat_remuc _ _ (by norm_num) (by norm_num), toNat_andc _ _ (by norm_num [M2c]), BitVec.toNat_add,
    toNat_srl _ 6 (by norm_num), hs1, hlo, hhi]
  rfl
theorem spareBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (d : Bool) :
    Br.holds u (spareBr d) ↔ d = decide (¬ lowerSpare (ansD a)) := by
  have hb : Br.holds u (spareBr d) ↔
      (!((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb)) = d := by
    simp only [spareBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a6E_eval h, a7E_eval h, kw]
    rw [show (BitVec.ofNat 64 0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_and]
  have e := spare_iff a
  have hd : decide (¬ lowerSpare (ansD a)) = !((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb) := by
    rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, decide_not, ← Bool.decide_and, decide_eq_decide.mpr e]
  rw [hb, hd]
  exact eq_comm
def ckOf (lay : Layer) (a : BitVec 256) : Nat := (tgtL lay.val + 2 ^ 64 - lowSumS1 (ansD a)) % 2 ^ 64
theorem ckBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hs : lowerSpare (ansD a)) (lay : Layer)
    (d : Bool) :
    Br.holds u (ckBr lay.val d) ↔ d = decide (¬ ckOf lay a < 8) := by
  have hS := lowSumS1_lt (ansD a)
  have hT : tgtL lay.val ≤ 198 := by fin_cases lay <;> decide
  have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
  have ht4 : ((t4E lay.val).eval u).toNat = (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 := by
    simp only [t4E, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, sumE_eval h hs, BitVec.toNat_ofNat]
    omega
  have hiff : (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 ↔ ckOf lay a < 8 := by
    unfold ckOf; omega
  have key : BitVec.ult (BitVec.ofNat 64 7) ((t4E lay.val).eval u) = decide (¬ ckOf lay a < 8) := by
    simp only [BitVec.ult, ht4, BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 7 by norm_num, decide_eq_decide]
    constructor
    · intro h1 h2
      have := hiff.mpr h2
      omega
    · intro h1
      by_contra h2
      exact h1 (hiff.mp (by omega))
  simp only [ckBr, Br.holds, CmpOp.eval]
  show BitVec.ult ((kw 7).eval u) ((t4E lay.val).eval u) = d ↔ _
  rw [show (kw 7).eval u = BitVec.ofNat 64 7 from rfl, key]; exact eq_comm
def lctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) : LCtx :=
  ⟨w, lay, 0, 0, (route index lay).2, (route index lay).1, s6v lay.val, a.extractLsb' 0 64, a.extractLsb' 64 64,
    ckOf lay a, ckSlot (ckOf lay a) + partLen (ckOf lay a)⟩
def lfS7 (lay leaf : Nat) : Nat := dispatchHeap lay leaf * 2 ^ s7Sh lay
theorem mod_pow_div_mod (v m k w : Nat) (h : k + w ≤ m) : v % 2 ^ m / 2 ^ k % 2 ^ w = v / 2 ^ k % 2 ^ w := by
  conv_rhs => rw [← Nat.mod_add_div v (2 ^ m)]
  rw [div_mod_add_pow _ _ _ _ _ h]
theorem getD_map_range (f : Nat → Nat) (n i : Nat) (h : i < n) : ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl
theorem lctx_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (hlay : lay ≠ 0)
    (ds : List Nat) (hds : decode lay (ansD a) = some ds) :
    ∀ i < 43, (lctxOf w index lay a).dig i = ds.getD i 0 := by
  rw [decode_lower_v6 lay hlay] at hds
  split at hds
  · split at hds
    · simp only [Option.some.injEq] at hds
      subst hds
      intro i hi
      unfold LCtx.dig lctxOf
      simp only []
      have hlw := lowerWord_eq (ansD a)
      by_cases h21 : i < 21
      · rw [if_pos h21, List.getD_append _ _ _ _ (by simp; omega), getD_map_range _ 42 i (by omega)]
        have e8 : (8 : Nat) ^ i = 2 ^ (3 * i) := by rw [Nat.pow_mul]
        rw [← ansD_lo, e8, hlw]
        have h1 := mod_pow_div_mod (ansD a).toNat 64 (3 * i) 3 (by omega)
        have h2 := mod_pow_div_mod (ansD a).toNat 63 (3 * i) 3 (by omega)
        have h3 := div_mod_add_pow ((ansD a).toNat % 2 ^ 63) ((ansD a).toNat / 2 ^ 64 % 2 ^ 63) (3 * i) 63 3
          (by omega)
        rw [show (2 : Nat) ^ 3 = 8 from rfl] at h1 h2 h3
        rw [h1, h3, h2]
      · by_cases h42 : i < 42
        · rw [if_neg h21, if_pos h42, List.getD_append _ _ _ _ (by simp; omega), getD_map_range _ 42 i (by omega)]
          have e8 : (8 : Nat) ^ (i - 21) = 2 ^ (3 * (i - 21)) := by rw [Nat.pow_mul]
          rw [← ansD_hi, e8, hlw, show 3 * i = 63 + 3 * (i - 21) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
            div_add_pow _ _ _ _ (le_refl _), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.sub_self,
            Nat.pow_zero, Nat.one_mul, Nat.zero_add]
          have h2 := mod_pow_div_mod ((ansD a).toNat / 2 ^ 64) 63 (3 * (i - 21)) 3 (by omega)
          rw [show (2 : Nat) ^ 3 = 8 from rfl] at h2
          exact h2.symm
        · have hi42 : i = 42 := by omega
          subst hi42
          rw [if_neg h21, if_neg h42, List.getD_append_right _ _ _ _ (by simp)]
          rw [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
          show ckOf lay a = _
          unfold ckOf
          rw [tgtL_eq]
    · cases hds
  · cases hds
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 lowerSpare lowerWord)
theorem xtrTab_bound : (xtrTab.all fun r => r.all fun x => decide (x < 160000)) = true := by decide
theorem getD_lt_of_all : ∀ (l : List Nat) (B c : Nat), 0 < B → (l.all fun x => decide (x < B)) = true →
    l.getD c 0 < B
  | [], B, c, hB, _ => by simpa using hB
  | x :: l, B, 0, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | x :: l, B, c + 1, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all l B c hB h.2
theorem getD_getD_lt : ∀ (L : List (List Nat)) (i j B : Nat), 0 < B →
    (L.all fun r => r.all fun x => decide (x < B)) = true → (L.getD i []).getD j 0 < B
  | [], i, j, B, hB, _ => by simpa using hB
  | r :: L, 0, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all r B j hB h.1
  | r :: L, i + 1, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_getD_lt L i j B hB h.2
theorem trPc_lt (lay c : Nat) : trPc lay c < 160000 :=
  getD_getD_lt xtrTab lay c 160000 (by norm_num) xtrTab_bound
theorem packedRouteE_eval (lay : Layer) (tree leaf : Nat) (s : MachineState)
    (ht : tree < 2 ^ 32) (hl : leaf < 2 ^ height lay)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 (hdr1 tree leaf))
    (htree1 : lay.val = 1 → tree < 65536)
    (h30 : s.getReg .x31 = BitVec.ofNat 64 tree)
    (h22 : lay.val = 3 → s.getReg .x22 = BitVec.ofNat 64 (tree * 2 ^ height lay + leaf))
    (h28 : lay.val = 1 ∨ lay.val = 2 →
      s.getReg .x28 = BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536))
    (hP : s.getMem (BitVec.ofNat 64 (hdrA lay.val)) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48)) :
    (packedRouteE lay.val).eval s = BitVec.ofNat 64 (packedPrefix lay tree leaf) := by
  by_cases h3 : lay.val = 3
  · have hsmall : (tree * 2 ^ height lay + leaf) * 65536 + 128 < 2 ^ 48 := by omega
    simp only [packedRouteE, if_pos h3, E.eval, BinOp.eval, kw, h22 h3, hP]
    rw [ofNat_shl']
    change BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) |||
      BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536) = _
    have hb : BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) =
        BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) ||| BitVec.ofNat 64 128 := by
      rw [ofNat_or_add _ _ 48 (by decide)]
      apply congrArg (BitVec.ofNat 64); ring
    have hp : BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536) ||| 128#64 =
        BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536 + 128) := by
      simpa only [show (2 : Nat) ^ 16 = 65536 from rfl] using
        ofNat_or_add 128 (tree * 2 ^ height lay + leaf) 16 (by decide)
    rw [hb, BitVec.or_assoc, BitVec.or_comm (BitVec.ofNat 64 128), hp,
      ofNat_or_add _ _ 48 (by omega)]
    apply congrArg (BitVec.ofNat 64)
    unfold packedPrefix packedHi
    rw [Nat.mod_eq_of_lt hr]
    ring
  by_cases h12 : lay.val = 1 ∨ lay.val = 2
  · have hsmall : (tree * 2 ^ height lay + leaf) * 65536 + 128 < 2 ^ 48 := by omega
    simp only [packedRouteE, if_neg h3, if_pos h12, E.eval, BinOp.eval, kw, h28 h12, hP]
    rw [BitVec.or_comm]
    change BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) |||
      BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536) = _
    have hb : BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) =
        BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) ||| BitVec.ofNat 64 128 := by
      rw [ofNat_or_add _ _ 48 (by decide)]
      apply congrArg (BitVec.ofNat 64); ring
    have hp : BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536) ||| 128#64 =
        BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536 + 128) := by
      simpa only [show (2 : Nat) ^ 16 = 65536 from rfl] using
        ofNat_or_add 128 (tree * 2 ^ height lay + leaf) 16 (by decide)
    rw [hb, BitVec.or_assoc, BitVec.or_comm (BitVec.ofNat 64 128), hp,
      ofNat_or_add _ _ 48 (by omega)]
    apply congrArg (BitVec.ofNat 64)
    unfold packedPrefix packedHi
    rw [Nat.mod_eq_of_lt hr]
    ring
  have hh : height lay ≤ 12 := by rw [← hL_eq]; exact (hL_le lay).2
  have hl32 : leaf < 2 ^ 32 := lt_of_lt_of_le hl
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hs : (hL lay.val + 16) % 2 ^ 64 % 64 = height lay + 16 := by rw [hL_eq]; omega
  have hleaf : (if lay.val = 1 then E.bin .srl (.reg .x4) (kw 16)
      else E.bin .sll (.bin .srl (.reg .x4) (kw 32)) (kw 16)).eval s =
      BitVec.ofNat 64 (leaf * 65536) := by
    by_cases h1 : lay.val = 1
    · simp only [if_pos h1, E.eval, BinOp.eval, kw, h4, hdr1_eq tree leaf ht hl32]
      rw [ofNat_shr']
      change BitVec.ofNat 64 ((tree + 2 ^ 32 * leaf) % 2 ^ 64 / 65536) = _
      rw [Nat.mod_eq_of_lt (show tree + 2 ^ 32 * leaf < 2 ^ 64 by omega)]
      apply congrArg (BitVec.ofNat 64)
      have := htree1 h1
      omega
    · simp only [if_neg h1, E.eval, BinOp.eval, kw, h4, hdr1_eq tree leaf ht hl32]
      rw [ofNat_shr', ofNat_shl']
      change BitVec.ofNat 64 ((tree + 2 ^ 32 * leaf) % 2 ^ 64 / 2 ^ 32 * 65536) = _
      rw [Nat.mod_eq_of_lt (show tree + 2 ^ 32 * leaf < 2 ^ 64 by omega),
        show (tree + 2 ^ 32 * leaf) / 2 ^ 32 = leaf by omega]
  simp only [packedRouteE, if_neg h3, if_neg h12]
  change s.getMem (BitVec.ofNat 64 (hdrA lay.val)) |||
    (if lay.val = 1 then E.bin .srl (.reg .x4) (kw 16)
      else E.bin .sll (.bin .srl (.reg .x4) (kw 32)) (kw 16)).eval s |||
    (s.getReg .x31 <<< ((BitVec.ofNat 64 (hL lay.val + 16)).toNat % 64)) = _
  rw [hleaf, h30, hP, ofNat_shl']
  change BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) |||
    BitVec.ofNat 64 (leaf * 65536) |||
    BitVec.ofNat 64 (tree * 2 ^ ((hL lay.val + 16) % 2 ^ 64 % 64)) = _
  rw [hs]
  have hb : BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + lay.val * 2 ^ 48) =
      BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) ||| BitVec.ofNat 64 128 := by
    rw [ofNat_or_add _ _ 48 (by decide)]
    apply congrArg (BitVec.ofNat 64); ring
  rw [hb]
  have hj : BitVec.ofNat 64 (leaf * 65536) ||| BitVec.ofNat 64 (tree * 2 ^ (height lay + 16)) =
      BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536) := by
    rw [BitVec.or_comm, ofNat_or_add _ tree (height lay + 16) (by
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hl (by decide : 0 < 65536))]
    apply congrArg (BitVec.ofNat 64)
    rw [Nat.pow_add]; ring
  have hor (a b c d : Word) : ((a ||| b) ||| c) ||| d = a ||| ((c ||| d) ||| b) := by
    ac_rfl
  calc
    _ = BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) |||
        ((BitVec.ofNat 64 (leaf * 65536) ||| BitVec.ofNat 64 (tree * 2 ^ (height lay + 16))) |||
          BitVec.ofNat 64 128) := hor _ _ _ _
    _ = BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) |||
        BitVec.ofNat 64 ((tree * 2 ^ height lay + leaf) * 65536 + 128) := by
      rw [hj]
      apply congrArg (fun x : Word => BitVec.ofNat 64 ((193 * 256 + lay.val) * 2 ^ 48) ||| x)
      simpa only [show (2 : Nat) ^ 16 = 65536 by norm_num] using
        ofNat_or_add 128 (tree * 2 ^ height lay + leaf) 16 (by decide)
    _ = _ := by
      rw [ofNat_or_add _ _ 48 (by omega)]
      apply congrArg (BitVec.ofNat 64)
      unfold packedPrefix packedHi
      rw [Nat.mod_eq_of_lt hr]
      ring
theorem origW_of {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} (hO : Verify.Orig w P s) (A : Nat)
    (hA : WIT + 16 ≤ A) (h8 : (A - WIT) % 8 = 0) (hx : A - WIT < WX) (hP : P (A - WIT)) : OrigW w s A := by
  have := hO.word (A - WIT) h8 hx hP
  rw [show WIT + (A - WIT) = A by omega] at this
  unfold OrigW
  rw [this, wword, show 64 * ((A - WIT) / 8) = 8 * (A - 0x800) by unfold WIT at *; omega]
theorem knownOK_cons (p : Reg × Word) (ps : List (Reg × Word)) (s : MachineState)
    (hp : s.getReg p.1 = p.2) (hps : KnownOK ps s) : KnownOK (p :: ps) s := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact hps q hq
theorem knownOK_at (ps : List (Reg × Word)) (s : MachineState) (i : Nat) (p : Reg × Word)
    (hk : KnownOK ps s) (he : ps[i]? = some p) : s.getReg p.1 = p.2 :=
  hk p (List.mem_of_getElem? he)
theorem ofNat64_add_zero_bridge (v : Word) (n : Nat) (h : v = BitVec.ofNat 64 n) :
    v = BitVec.ofNat 64 (n + 0) := by simpa only [Nat.add_zero] using h
theorem knownOK_seventeen (s : MachineState)
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 : Reg × Word}
    (h0 : s.getReg p0.1 = p0.2) (h1 : s.getReg p1.1 = p1.2)
    (h2 : s.getReg p2.1 = p2.2) (h3 : s.getReg p3.1 = p3.2)
    (h4 : s.getReg p4.1 = p4.2) (h5 : s.getReg p5.1 = p5.2)
    (h6 : s.getReg p6.1 = p6.2) (h7 : s.getReg p7.1 = p7.2)
    (h8 : s.getReg p8.1 = p8.2) (h9 : s.getReg p9.1 = p9.2)
    (h10 : s.getReg p10.1 = p10.2) (h11 : s.getReg p11.1 = p11.2)
    (h12 : s.getReg p12.1 = p12.2) (h13 : s.getReg p13.1 = p13.2)
    (h14 : s.getReg p14.1 = p14.2) (h15 : s.getReg p15.1 = p15.2)
    (h16 : s.getReg p16.1 = p16.2) :
    KnownOK [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16] s := by
  iterate 17
    refine knownOK_cons _ _ _ ?_ ?_
    rotate_left
  · intro q hq; cases hq
  all_goals assumption
theorem lctxOf_known (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat)
    (s : MachineState) (hk : KnownOK (postBl lay.val p) s)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (packedPrefix lay (route index lay).2 (route index lay).1))
    (h4 : s.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1))
    (h16 : s.getReg .x16 = a.extractLsb' 0 64)
    (h17 : s.getReg .x17 = a.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 (ckOf lay a)) :
    KnownOK (lctxOf w index lay a).known s := by
  unfold LCtx.known
  refine knownOK_seventeen s ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact knownOK_at _ s 0 (.x5, 0) hk rfl
  · exact knownOK_at _ s 7 (.x11, 64) hk rfl
  · exact knownOK_at _ s 8 (.x7, 1) hk rfl
  · exact knownOK_at _ s 9 (.x13, 2) hk rfl
  · exact knownOK_at _ s 10 (.x19, 3) hk rfl
  · exact knownOK_at _ s 11 (.x20, 4) hk rfl
  · exact knownOK_at _ s 12 (.x21, 5) hk rfl
  · exact knownOK_at _ s 13 (.x26, 6) hk rfl
  · exact ofNat64_add_zero_bridge _ _ h28
  · exact knownOK_at _ s 4 (.x2, 0x3fe00) hk rfl
  · exact knownOK_at _ s 16 (.x15, 0x40000) hk rfl
  · exact knownOK_at _ s 17 (.x22, BitVec.ofNat 64 (s6v lay.val)) hk rfl
  · exact h4
  · exact knownOK_at _ s 2 (.x27, BitVec.ofNat 64 (0x401 + 65536 * lay.val)) hk rfl
  · exact h16
  · exact h17
  · exact h29
theorem encB_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t)
    (a : BitVec 256) :
    (decode lay (ansD a) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 23 ∧ cy ≤ 26) ∧
    (decode lay (ansD a) ≠ none → ∃ s0, Steps image (writeHash t a) (bSt lay.val) (bCy lay.val) s0 ∧
        (lctxOf w index lay a).ok ∧
        (∀ p ∈ (lctxOf w index lay a).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay a).Orig0 s0 ∧
        (lctxOf w index lay a).ChainIn s0 0 [] s0 ∧ Glob (chainK lay.val) w pk s0 ∧
        Verify.Orig w (fun o => 8136 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1) ∧
        s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2 ∧
        s0.getReg .x9 = BitVec.ofNat 64 FBASE) := by
  set u := writeHash t a with hu
  have hcc := copy_parts lay.val (trPc lay.val c) (BC.copyCheck_at lay.val c lay.isLt hc)
  have hB := hcc.2.2 (fun h => hlay (Fin.ext h))
  have hkt : KnownOK (BC.bK lay.val) t := ht.glob.1
  obtain ⟨d, h12, hdc⟩ : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧
      (if lay.val = 3 then d = 256 else (d = x10In lay.val ∨ d = x10In lay.val + 48)) := by
    by_cases h3 : lay.val = 3
    · refine ⟨256, hkt (.x12, 256) ?_, by rw [if_pos h3]⟩
      unfold BC.bK; rw [if_pos h3]; simp [bK, h3]
    · have h12' : lay.val = 1 ∨ lay.val = 2 := by
        have := lay.isLt; have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h); omega
      obtain ⟨d, hd, hdd⟩ := ht.dstL h12'
      exact ⟨d, hd, by rw [if_neg h3]; exact hdd⟩
  have hdv : d = 256 ∨ d = 17608 ∨ d = 17656 ∨ d = 20744 ∨ d = 20792 := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals simp [x10In] at hdc; omega
  have hku : KnownOK (BC.bK lay.val) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hkuB : KnownOK (BC.bKB lay.val) u := fun p hp => hku p (List.mem_of_mem_filter hp)
  have hx12u : u.getReg .x12 = BitVec.ofNat 64 d := by rw [hu, writeHash_getReg]; exact h12
  have hobl : ∀ o ∈ BC.oblB, o.holds u := by
    intro o ho
    simp only [BC.oblB, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;>
      simp only [Oblig.holds, Addr.eval, E.eval, hx12u] <;>
      rcases hdv with rfl | rfl | rfl | rfl | rfl <;> decide
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hans : AnsAt u a := by
    constructor
    · simp only [a6E, E.eval]
      rw [hx12u, hu]
      exact writeHash_at0 t a d h12 (by omega)
    · simp only [a7E, E.eval, BinOp.eval, kw]
      rw [hx12u, hu, ofNat_add_ofNat]
      exact writeHash_at8 t a d h12 (by omega)
  have hdec := decode_lower_v6 lay hlay (ansD a)
  have hS := lowSumS1_lt (ansD a)
  constructor
  · intro hnone
    by_cases hs : lowerSpare (ansD a)
    · have hck : ¬ ckOf lay a < 8 := by
        intro hck
        rw [hdec, if_pos hs, if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
        cases hnone
      obtain ⟨v, hv⟩ := spec_run hB.2.1 u hpcu hkuB (by
        intro b hb; simp only [rejCk, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact (ckBr_iff hans hs lay true).mpr (by rw [decide_eq_true hck])
        · exact (spareBr_iff hans false).mpr (by rw [decide_eq_false (not_not_intro hs)])) hobl
      exact ⟨v, 20, 23, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejCk]),
        hv.regs (.x10, kw 1) (by simp [rejCk]), by norm_num, by norm_num⟩
    · obtain ⟨v, hv⟩ := spec_run hB.2.2 u hpcu hkuB (by
        intro b hb; simp only [rejSpare, List.mem_singleton] at hb; subst hb
        exact (spareBr_iff hans true).mpr (by rw [decide_eq_true hs])) hobl
      exact ⟨v, 7, 7, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejSpare]),
        hv.regs (.x10, kw 1) (by simp [rejSpare]), by norm_num, by norm_num⟩
  · intro hsome
    have hs : lowerSpare (ansD a) := by
      by_contra hs
      apply hsome; rw [hdec, if_neg hs]
    have hck : ckOf lay a < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_pos hs, if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
    obtain ⟨s0, hs0⟩ := spec_run hB.1 u hpcu hkuB (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hs lay false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (spareBr_iff hans false).mpr (by rw [decide_eq_false (not_not_intro hs)])) hobl
    set L := lctxOf w index lay a with hL
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := by
      have hk0 := hs0.known
      by_cases h3 : lay.val = 3
      · rw [postBlC, if_pos h3] at hk0
        have e22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) := by
          rw [hs0.regs (.x22, .ld (kw (TOPLOAD - 8))) (by simp [specBl, h3]), h3]
          change u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = _
          have hd3 : d = 256 := by rw [if_pos h3] at hdc; exact hdc
          rw [hu, writeHash_frame t a d (TOPLOAD - 8) h12 (by unfold TOPLOAD; omega)
            (by omega) (Or.inr (by unfold TOPLOAD; omega))]
          exact (ht.hdr3 h3).2
        intro q hq
        simp only [postBl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | rfl | rfl | rfl
        · exact hk0 q (List.mem_append_left _ hq)
        · exact e22
        · exact hk0 _ (by simp)
        · exact hk0 _ (by simp)
      · rw [postBlC, if_neg h3] at hk0
        exact hk0
    have hkeep := hs0.keep
    have e29 : ((t4E lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val ≤ 198 := by fin_cases lay <;> decide
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide
      have hle : lowSumS1 (ansD a) ≤ tgtL lay.val ∧ tgtL lay.val - lowSumS1 (ansD a) < 8 := by
        unfold ckOf at hck; omega
      have hcv : ckOf lay a = tgtL lay.val - lowSumS1 (ansD a) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4E, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumE_eval hans hs, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, rfl,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_, ?_, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide
      · simp only [hL, lctxOf]; omega
      · simpa only [hL, lctxOf, hL_eq] using leaf_lt index lay
      · simp only [hL, lctxOf]; exact h6
      · simp only [hL, lctxOf]; exact h7
    have hGu : Glob (BC.bK lay.val) w pk u :=
      Glob_writeHash ht.glob a d h12 (by rcases hdv with rfl | rfl | rfl | rfl | rfl <;> decide)
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : Verify.Orig w (fun o => 8136 ≤ o ∧ o < layerEnd lay.val) u := by
      have := Orig_writeHash ht.orig a d h12 (by omega)
      have hxl : lay.val ≠ 3 → x10In lay.val = WIT + layerEnd lay.val := by
        fin_cases lay <;> decide
      have hL8 : layerEnd lay.val % 8 = 0 := by
        fin_cases lay <;> decide
      intro j hj hp
      refine this j hj ⟨hp, ?_⟩
      have hp2 := hp.2
      by_cases h3 : lay.val = 3
      · rw [if_pos h3] at hdc
        exact Or.inr (by unfold WIT; omega)
      · rw [if_neg h3] at hdc
        have hx := hxl h3
        exact Or.inl (by omega)
    have hOs0 : Verify.Orig w (fun o => 8136 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc tgtl rfl]
      simp only [tgtl, E.eval, BinOp.eval, a6E_eval hans, kw]
      have hk0 : L.kOf 0 = (a.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (a.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((a.extractLsb' 0 64) <<< ((BitVec.ofNat 64 9).toNat % 64) &&& BitVec.ofNat 64 0x3fe00) =
          BitVec.ofNat 64 (512 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 9 (by norm_num), show (0x3fe00 : Nat) = 512 * (2 ^ 9 - 1) by norm_num,
          land_mask _ _ (le_refl _), field_shl _ _ _ (le_refl _) (le_refl _), hk0, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 512 * ((a.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      rw [hm]
      have e2 : BitVec.ofNat 64 (512 * L.kOf 0) + BitVec.ofNat 64 260384 =
          BitVec.ofNat 64 (0x1000 + 4 * entW 0 (L.kOf 0)) := by
        rw [ofNat_add_ofNat]; congr 1; unfold entW ttabIdx; omega
      rw [e2, even_andNot1' _ (by omega)]
      unfold LCtx.startPc; simp
    have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_, ?_⟩
    · apply lctxOf_known w index lay a (trPc lay.val c) s0 hko
      · rw [hs0.regs (.x28, packedRouteE lay.val) (by simp [specBl])]
        simpa only [Nat.add_zero] using packedRouteE_eval lay _ _ u
          (tree_lt index lay hidx) (by simpa only [hL_eq] using leaf_lt index lay)
          (routed_lt index lay hidx)
          (by rw [hu, writeHash_getReg, ht.tp lay rfl]) (by
            intro h1
            obtain rfl : lay = 1 := Fin.ext h1
            rw [route_snd, show below (1 : Layer).val = 12 from rfl,
              show T3M.hL (1 : Layer).val = 7 from rfl]
            norm_num
            omega)
          (by rw [hu, writeHash_getReg, ht.t5 lay rfl (fun h => hlay (Fin.ext h))]) (by
            intro h3
            rw [hu, writeHash_getReg, ht.index3 h3]
            congr 1
            obtain rfl : lay = 3 := Fin.ext h3
            rw [route_fst, route_snd, ← hL_eq (3 : Layer),
              show below (3 : Layer).val = 0 from rfl]
            simp only [Nat.zero_add, pow_zero, Nat.div_one]
            simpa only [Nat.add_comm, Nat.mul_comm] using
              (Nat.mod_add_div index (2 ^ T3M.hL (3 : Layer).val)).symm) (by
            intro h12'
            rw [hu, writeHash_getReg, ht.packed12 h12']
            have he : (route index lay).2 * 2 ^ height lay + (route index lay).1 =
                index / 2 ^ T3M.below lay.val := by
              rw [route_fst, route_snd, ← hL_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
              simpa only [Nat.add_comm, Nat.mul_comm] using
                (Nat.mod_add_div (index / 2 ^ T3M.below lay.val) (2 ^ T3M.hL lay.val))
            simpa only [BC.below, T3M.below] using
              congrArg (fun q : Nat => BitVec.ofNat 64 (q * 65536)) he.symm) (by
            by_cases h3 : lay.val = 3
            · have hd3 : d = 256 := by rw [if_pos h3] at hdc; exact hdc
              rw [hdrA, if_pos h3, hu, writeHash_frame t a d (TOPLOAD + 32) h12 (by unfold TOPLOAD; omega)
                (by omega) (Or.inr (by unfold TOPLOAD; omega)), h3]
              exact (ht.hdr3 h3).1
            · rw [hdrA, if_neg h3]
              exact hGu.2.2.2.2.2.prefix lay.val lay.isLt)
      · rw [hkeep .x4 (by simp [keepB]), hu, writeHash_getReg, ht.tp lay rfl]
      · rw [hs0.regs (.x16, a6E) (by simp [specBl]), a6E_eval hans]
      · rw [hs0.regs (.x17, a7E) (by simp [specBl]), a7E_eval hans]
      · rw [hs0.regs (.x29, t4E lay.val) (by simp [specBl]), e29]
    · intro i hi hi' k hk
      have hb := L.blk_props hLok i hi'
      have hS6 : L.S6 = s6v lay.val := rfl
      apply origW_of hOs0 _ (by unfold WIT; omega) (by
          unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
        (by unfold WIT WX; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
      simp only [LCtx.blk, hS6]
      unfold WIT
      fin_cases lay <;> simp [s6v, layerEnd] <;> omega
    · rw [hs0.regs (.x23, .bin .sll (.reg .x23) (kw (s7Sh lay.val))) (by simp [specBl])]
      simp only [E.eval, BinOp.eval, kw]
      rw [hu, writeHash_getReg, ht.s7 lay rfl]
      have hsh : s7Sh lay.val < 64 := by unfold s7Sh; split_ifs <;> omega
      have hb : s7Bias lay.val ≤ 4096 := by fin_cases lay <;> decide
      have hl := leaf_lt32 index lay
      have hD : dispatchHeap lay.val (route index lay).1 < 2 ^ 64 := by unfold dispatchHeap; omega
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sll _ _ hsh, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD]
      rfl
    · rw [hkeep .x31 (by simp [keepB]), hu, writeHash_getReg, ht.t5 lay rfl (fun h => hlay (Fin.ext h))]
    · exact hko (.x9, BitVec.ofNat 64 FBASE) (by simp [postBl])
end SigGolfCandidate.T3M
end
end
