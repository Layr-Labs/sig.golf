import SigGolfCandidate.T3M.Verify.LayerRuns

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
  (if lay = 0 then
    specB [] [] [] (runAt [] [96160] (p + stepsA lay + 1) [])
      (specTopCall p) [] [] keepTopCall
  else
    specB [] [] baseK (runAt (bKB lay) [] (p + stepsA lay + 1)
      [.br false, .br false, .jmp]) (specBl lay p) oblB (postBlC lay p) keepB &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1)
      [.br false, .br true]) (rejCk lay) oblB [] [] &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1)
      [.br true]) (rejRng 62) oblB [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) (lfDirs lay))
    (specLf lay) [] (postLf lay) keepLf
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
def CounterWord : Prop := ∀ (w : WBytes) (j : Nat),
  LoadKind.wu.fromWord (wword w j) 0 = BitVec.ofNat 64 (wle32 w (8 * j)).toNat
theorem counterWord : CounterWord := fun w j => by
  apply BitVec.eq_of_toNat_eq
  simp [LoadKind.fromWord, extractWord32, wword_toNat, wle32,
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
def CounterPadExtract : Prop := ∀ (w : WBytes) (o : Nat),
  (w.extractLsb' (8 * (o + 4)) 96 ++ wle32 w o) = wdig w o
theorem counterPadExtract : CounterPadExtract := fun w o =>
  BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)
end SigGolfCandidate.T3M.BC
end
