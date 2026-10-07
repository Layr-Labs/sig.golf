import SigGolfCandidate.T3M.Verify.LayerRuns
import SigGolfCandidate.T3M.Verify.ChainRuns

section


section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.preK lay else
  (T3M.preK lay).filter (fun p => p.1 != .x10 && p.1 != .x12) ++
    [(.x22, BitVec.ofNat 64 (s6v (lay + 1)))]
def bK (lay c : Nat) : List (Reg × Word) :=
  if lay = 3 then T3M.bK lay else
  (T3M.bK lay).filter (fun p => p.1 != .x10) ++
    [(.x10, BitVec.ofNat 64 (rowA lay c))]
def ctrE (lay c : Nat) : E :=
  if lay = 3 then T3M.ctrE lay else .un (.ld .wu 0) (.ld (kw (rowA lay c + 32)))
def ctrBr (lay c : Nat) (d : Bool) : Br := ⟨if lay = 3 then .ltu else .geu, ctrE lay c, kw 0x400000, d⟩
def headerWrites (lay c : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (rowA lay c + 24)⟩, kw 1),
   (⟨none, BitVec.ofNat 64 (rowA lay c + 16)⟩, .reg .x28)]
def specA (lay c : Nat) : Spec :=
  if lay = 3 then T3M.specA lay (trPc lay c) else
  ⟨if lay = 0 then [(.x23, s7E lay), (.x3, ctrE lay c), (.x12, .reg .x12)]
   else [(.x23, s7E lay), (.x31, treeE lay), (.x3, ctrE lay c), (.x12, .reg .x12)],
   headerWrites lay c, trPc lay c + stepsA lay, true, stepsA lay,
   [ctrBr lay c false], none, stepsA lay⟩
def rejA (lay c : Nat) : Spec :=
  if lay = 3 then T3M.rejA lay (trPc lay c) else
  ⟨[(.x5, kw 1), (.x10, kw 1)], headerWrites lay c,
   rejEcall, true, stepsA lay + 3, [ctrBr lay c true], none, stepsA lay + 3⟩
def keepA (lay : Nat) : List Reg := if lay = 3 then [.x22] else if lay = 0 then [.x28, .x31] else [.x28]
def bKB (lay c : Nat) : List (Reg × Word) := (bK lay c).filter (fun p => p.1 != .x12)
def oblB : List Oblig := [.valid ⟨some (.reg .x12), 8⟩ 8, .valid ⟨some (.reg .x12), 0⟩ 8]
def allowed (lay c : Nat) : List Nat :=
  if lay = 3 then [2064, 2072] else [rowA lay c + 16, rowA lay c + 24]
def setupCheck (lay c : Nat) : Bool :=
  specB (allowed lay c) [] baseK (runAt (preK lay) [] (setupPc lay (trPc lay c)) [.br (setupAcceptDir lay)])
    (specA lay c) [] (bK lay c) (keepA lay) &&
  specB (allowed lay c) [] [] (runAt (preK lay) [] (setupPc lay (trPc lay c)) [.br (!setupAcceptDir lay)])
    (rejA lay c) [] [] []
def copyCheck (lay c : Nat) : Bool :=
  setupCheck lay c &&
  (if lay = 0 then true else
    specB [] [] baseK (runAt (bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br false, .br false, .jmp]) (specBl lay (trPc lay c)) oblB (postBlC lay (trPc lay c)) keepB &&
    specB [] [] [] (runAt (bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br false, .br true]) (rejCk lay) oblB [] [] &&
    specB [] [] [] (runAt (bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br true]) rejSpare oblB [] [])
def layerCheck (lay lo n : Nat) : Bool :=
  (List.range' lo n).all fun c => copyCheck lay c
end SigGolfCandidate.T3M.BC
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def keepLfL : List Reg := [.x1, .x2, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23, .x6, .x25,
  .x26, .x29, .x31, .x30, .x28, .x14]
def lfSlotCheck (lay c : Nat) : Bool :=
  specB [] [] baseK (runAt (leafK lay) [] (ckSlot c + partLen c) (lfDirs lay)) (specLf lay) [] (postLf lay) keepLfL
set_option maxRecDepth 100000 in
theorem lfSlotChecks : ([1, 2, 3].all fun lay => (List.range 8).all fun c => lfSlotCheck lay c) = true := by
  decide +kernel
theorem lfSlotCheck_at (lay c : Nat) (h0 : lay ≠ 0) (h4 : lay < 4) (hc : c < 8) : lfSlotCheck lay c = true := by
  have h := List.all_eq_true.mp lfSlotChecks lay (by simp; omega)
  exact List.all_eq_true.mp h c (List.mem_range.mpr hc)
end SigGolfCandidate.T3M
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
theorem copyCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : copyCheck lay c = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ lo n, layerCheck lay lo n = true → lo ≤ c → c < lo + n → copyCheck lay c = true :=
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
