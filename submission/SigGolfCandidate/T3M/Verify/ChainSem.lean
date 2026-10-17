import SigGolfCandidate.T3M.Verify.PackedHeader
import SigGolfCandidate.T3M.Verify.Mem
import SigGolfCandidate.T3M.Verify.ChainRuns

section
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
 theorem land_mask_pow (n p k : Nat) :
    n &&& (2^p * (2^k - 1)) = 2^p * (n / 2^p % 2^k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hp : p ≤ j
  · simp only [hp, decide_true, Bool.true_and, show j-p+p=j by omega]
    exact Bool.and_comm _ _
  · simp [hp]
 theorem field_shl_pow (W s p k : Nat) (hs : s ≤ p) (hpk : p+k ≤ 64) :
    W * 2^s % 2^64 / 2^p % 2^k = W / 2^(p-s) % 2^k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < k
  · simp only [hj, decide_true, Bool.true_and, show j+p<64 by omega, show s≤j+p by omega]
    rw [show j+p-s=j+(p-s) by omega]
  · simp [hj]
 theorem shE_mask_new (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w = W)
    (b k : Nat) (hb : b < 64) (hk : k ≤ 9) :
    ((shE w b).eval s &&& BitVec.ofNat 64 ((if b=9 then 512 else 1024)*(2^k-1))).toNat =
      (if b=9 then 512 else 1024)*(W.toNat / 2^b % 2^k) := by
  have hpow : 2^k ≤ 2^9 := Nat.pow_le_pow_right (by norm_num) hk
  by_cases h9 : b=9
  · subst b
    simp only [shE, if_true, E.eval, hw]
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact land_mask_pow _ 9 k
  · simp only [if_neg h9]
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (1024:Nat)=2^10 from rfl,
      land_mask_pow]
    congr 1
    unfold shE
    rw [if_neg h9]
    split_ifs with h10
    · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show 10-b<2^64 by omega), Nat.mod_eq_of_lt (show 10-b<64 by omega),
        Nat.shiftLeft_eq, field_shl_pow _ _ _ _ (by omega) (by omega), show 10-(10-b)=b by omega]
    · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show b-10<2^64 by omega), Nat.mod_eq_of_lt (show b-10<64 by omega),
        Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        show 2^(b-10)*2^10=2^b by rw [←Nat.pow_add]; congr 1; omega]
 theorem lowerImm_even (t : Nat) : lowerImm t % 2 = 0 := by
  unfold lowerImm
  split_ifs <;> decide +kernel
 theorem entW_address (t k : Nat) (ht : t<14) (hk : k<512) :
    pcOf (entW t k) = BitVec.ofNat 64
      ((if t=1 ∨ t=8 then 512 else 1024)*k+lowerImm t) := by
  apply BitVec.eq_of_toNat_eq
  interval_cases t <;> simp only [entW, lowerImm, pcOf, BitVec.toNat_ofNat] <;> norm_num <;> omega
 theorem entW_valid (t k : Nat) (ht : t<14) (hk : k<512) (hl : rankFloor t ≤ k) :
    entW t k < 133760 := by
  interval_cases t <;> norm_num [entW, lowerImm, rankFloor] at * <;> omega
 theorem entW_fault_address (t k : Nat) (ht : t<14) (hk : k<rankFloor t) :
    (pcOf (entW t k)).toNat < 0x1000 := by
  have hk' : k<512 := by unfold rankFloor at hk; split_ifs at hk <;> omega
  rw [entW_address t k ht hk',BitVec.toNat_ofNat]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  interval_cases t <;> norm_num [lowerImm, rankFloor] at * <;> omega
end SigGolfCandidate.T3M
end

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
abbrev vimage : Image := Images.verifyImage
theorem piece_steps {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 257214) (s : MachineState)
    (hpc : s.pc = pcOf p) (ho : ∀ o ∈ r.st.obl, o.holds s) :
    Steps vimage s r.steps r.cycles (r.toState s) :=
  symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)
theorem piece_ecall {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 257214) (s : MachineState)
    (ho : ∀ o ∈ r.st.obl, o.holds s) (hst : r.stop = .ecall) :
    fetch vimage (r.toState s) = some (.base .ECALL) :=
  symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst
theorem ofNat_add_off (x a b k : Nat) (h : b ≤ x + a) (h2 : x + a + k < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k) =
      BitVec.ofNat 64 (x + a - b + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem ofNat_add_off0 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) = BitVec.ofNat 64 (x + a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem ofNat_add_off48 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a + 48 < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) + 48 = BitVec.ofNat 64 (x + a - b + 48) := by
  rw [ofNat_add_off0 x a b h (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (48 : Word).toNat = 48 from rfl]
  omega
theorem valid_ofNat (A w : Nat) (hA : A + w ≤ 2 ^ 24) (ha : A % w = 0) :
    accessValid (BitVec.ofNat 64 A) w = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by simp only [MEMORY_BYTES]; omega, ha⟩
def OrigW (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A - Verify.WIT)) 64
theorem wdig_lo (w : ClaudeWCT.W9.T3M.WBytes) (off : Nat) :
    (ClaudeWCT.W9.T3M.wdig w off).extractLsb' 0 64 = w.extractLsb' (8 * off) 64 := by
  unfold ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem wdig_hi (w : ClaudeWCT.W9.T3M.WBytes) (off : Nat) :
    (ClaudeWCT.W9.T3M.wdig w off).extractLsb' 64 64 = w.extractLsb' (8 * (off + 8)) 64 := by
  unfold ClaudeWCT.W9.T3M.wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (off + 8) = 8 * off + 64 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize w.toNat / 2 ^ (8 * off) = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem DigAt_origW {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {A : Nat} (h0 : OrigW w s A) (h1 : OrigW w s (A + 8))
    (hA : Verify.WIT ≤ A) : DigAt s A (ClaudeWCT.W9.T3M.wdig w (A - Verify.WIT)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 - Verify.WIT = A - Verify.WIT + 8 by omega]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
def chainRegs : List Reg := [.x10, .x12, .x25, .x3, .x14]
def Keeps (r : Result) (ws : List Reg) : Prop := ∀ x, x ∉ ws → r.st.regs.get x = RegFile.init.get x
theorem Keeps.reg {r : Result} {ws : List Reg} (h : Keeps r ws) (s : MachineState) {x : Reg} (hx : x ∉ ws) :
    (r.toState s).getReg x = s.getReg x := by
  rw [Result.toState_getReg, h x hx, RegFile.init_get_eval]
theorem ne_of_not_mem {x r : Reg} {ws : List Reg} (hx : x ∉ ws) (hr : r ∈ ws) : x ≠ r := by
  rintro rfl; exact hx hr
theorem headJ_keeps (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) :
    Keeps (headJ rb off first tgt) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headR_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) :
    Keeps (headR rb off d slot p) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headR]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem rungR_keeps (d : Nat) (slot : Option Nat) (p : Nat) : Keeps (rungR d slot p) [.x12] := by
  intro x hx
  simp only [rungR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl
theorem copyJ_keeps (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) :
    Keeps (copyJ rb off slot first tgt) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyJ, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyF_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyF rb off slot p) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyF, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyN_keeps (rb : Reg) (off : Word) (slot tgt : Nat) : Keeps (copyN rb off slot tgt) [.x3, .x14] := by
  intro x hx
  simp only [copyN, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headJH_keeps (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) :
    Keeps (headJH rb off tgt i d slot) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headRH_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) :
    Keeps (headRH rb off d slot p i) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headRV_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) :
    Keeps (headRV rb off d slot p i) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRV]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyFH_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyFH rb off slot p) [.x3, .x14] := by
  intro x hx
  simp only [copyFH, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem xJ_keeps (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Keeps (xJ w b mreg imm) [.x14] := by
  intro x hx
  simp only [xJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem ctabX_keeps : Keeps ctabX [.x14] := by
  intro x hx
  simp only [ctabX]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem retR_keeps : Keeps retR [] := fun _ _ => rfl
theorem rungRB_keeps (d : Nat) (slot : Option Nat) (p : Nat) : Keeps (rungRB d slot p) [.x12] := by
  intro x hx
  simp only [rungRB]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl

theorem copyNB_keeps (rb : Reg) (off : Word) (slot tgt : Nat) (g : Bool := false) :
    Keeps (copyNB rb off slot tgt g) [.x3, .x14] := by
  intro x hx
  simp only [copyNB, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headJHB_keeps (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) (g : Bool := false) :
    Keeps (headJHB rb off tgt i d slot g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJHB]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headRHB_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) (g : Bool := false) :
    Keeps (headRHB rb off d slot p i g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRHB]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headRVB_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) (g : Bool := false) :
    Keeps (headRVB rb off d slot p i g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRVB]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem copyFHB_keeps (rb : Reg) (off : Word) (slot p : Nat) (g : Bool := false) :
    Keeps (copyFHB rb off slot p g) [.x3, .x14] := by
  intro x hx
  simp only [copyFHB, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
@[simp] theorem gVal_false : gVal false = 48 := rfl
@[simp] theorem gOut_false : gOut false = 48 := rfl
/-- Pairing stage 1: the padded chain step input in the format `g` (F: `chainInputP`; G: value first). -/
def chainInputL (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : HashInput :=
  if g then SphincsSecurity.bytesLE 16 v ++
      SphincsSecurity.bytesLE 16 (chainHeaderP lay tree leaf i step headerPad) ++
      SphincsSecurity.bytesLE 16 p0 ++ SphincsSecurity.bytesLE 16 p1
  else chainInputP lay tree leaf i step p0 p1 headerPad v
theorem chainInputL_length (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : (chainInputL lay tree leaf i step p0 p1 headerPad v g).length = 64 * (0 + 1) := by
  unfold chainInputL; split
  · simp only [List.length_append, SphincsSecurity.bytesLE_length]
  · exact chainInputP_length _ _ _ _ _ _ _ _ _
theorem wordsOf_chainInputL (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : wordsOf (chainInputL lay tree leaf i step p0 p1 headerPad v g) =
      if g then [v.extractLsb' 0 64, v.extractLsb' 64 64,
        (chainHeader lay tree leaf i step).extractLsb' 0 64, headerPad,
        p0.extractLsb' 0 64, p0.extractLsb' 64 64, p1.extractLsb' 0 64, p1.extractLsb' 64 64]
      else [p0.extractLsb' 0 64, p0.extractLsb' 64 64,
        (chainHeader lay tree leaf i step).extractLsb' 0 64, headerPad,
        p1.extractLsb' 0 64, p1.extractLsb' 64 64, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  unfold chainInputL; split
  · rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
      wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
      wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
      wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
    have hlo : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 0 64 =
        (chainHeader lay tree leaf i step).extractLsb' 0 64 := BitVec.extractLsb'_append_eq_right
    have hhi : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 64 64 = headerPad :=
      BitVec.extractLsb'_append_eq_left
    rw [hlo, hhi]; rfl
  · exact wordsOf_chainInputP _ _ _ _ _ _ _ _ _
/-- On a lower layer the format of chain `i` is `isG`. -/
theorem chainInputL_eq (lay : Layer) (hl : lay ≠ 0) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word)
    (v : Digest) : chainInputL lay tree leaf i step p0 p1 headerPad v (lowerG i) =
      ClaudeWCT.W9.T3M.chainInputPW lay tree leaf i step p0 p1 headerPad v := by
  have : ClaudeWCT.WCT9.isG lay i = lowerG i := by simp [ClaudeWCT.WCT9.isG, lowerG, hl]
  unfold chainInputL ClaudeWCT.W9.T3M.chainInputPW; rw [this]
structure LCtx where
  w : ClaudeWCT.W9.T3M.WBytes
  lay : Layer
  i0 : Nat
  koff : Nat
  tree : Nat
  leaf : Nat
  S6 : Nat
  d0 : Word
  d1 : Word
  ck : Nat
  ret : Nat
  bufferBound : S6 - 520 + 2248 ≤ Verify.WIT + ClaudeWCT.W9.T3M.leafBufferBase lay
namespace LCtx
/-- Pairing stage 1: chain `i`'s block (`x22 = S6` is the chain area + 520). -/
def blk (c : LCtx) (i : Nat) : Nat := c.S6 - 520 + lowerSlot i
/-- Address of chain `i`'s supplied value (F: block + 48, G: block start). -/
def vAt (c : LCtx) (i : Nat) : Nat := c.blk i + gVal (lowerG i)
/-- Hash destination of an interior step (F: block + 48; G: block - 16, so the high half lands on the value). -/
def oAt (c : LCtx) (i : Nat) : Nat := if lowerG i then c.blk i - 16 else c.blk i + 48
def dig (c : LCtx) (i : Nat) : Nat :=
  if i < 21 then c.d0.toNat / 8 ^ i % 8 else if i < 42 then c.d1.toNat / 8 ^ (i - 21) % 8 else c.ck
def w0 (c : LCtx) (i : Nat) : Nat := i + c.koff + packedPrefix c.lay c.tree c.leaf
def w1 (c : LCtx) : Nat := hdr1 c.tree c.leaf
def pad0At (c : LCtx) (i : Nat) : Nat := c.blk i + (if lowerG i then 32 else 0)
def pad1At (c : LCtx) (i : Nat) : Nat := c.blk i + (if lowerG i then 48 else 32)
def pad0 (c : LCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad0At i - Verify.WIT)
def pad1 (c : LCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad1At i - Verify.WIT)
def padHeader (c : LCtx) (i : Nat) : Word := c.w.extractLsb' (8 * (c.blk i - Verify.WIT + 24)) 64
def val (c : LCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.vAt i - Verify.WIT)
def bufferOffset (c : LCtx) : Nat := Verify.WIT + ClaudeWCT.W9.T3M.leafBufferBase c.lay - 768
def bufferSlot (c : LCtx) (i : Nat) : Nat := c.bufferOffset + slotL i
def bufferSafe (c : LCtx) (i : Nat) : Prop :=
  c.dig i = 7 ∧ (i = 0 ∨ i = 1 ∨ (0 < i ∧ i % 3 ≠ 0 ∧ c.dig (i-1) = 7))
instance (c : LCtx) (i : Nat) : Decidable (c.bufferSafe i) := by unfold bufferSafe; infer_instance
def bufferEnd (c : LCtx) (i : Nat) : Nat :=
  c.bufferSlot i + (if 1 < i ∧ c.dig (i-1) ≠ 7 then 16 else 0)
/-- Pairing stage 1: the bytes chain `j` writes: its header word and the 32-byte hash destination. -/
def chainWr (c : LCtx) (j A : Nat) : Prop :=
  (c.blk j + 16 ≤ A ∧ A < c.blk j + 24) ∨ (c.oAt j ≤ A ∧ A < c.oAt j + 32)
/-- C3 (frame shape adapted from b3cc11b): chain 0's final step writes `[slot 0 - 16, slot 0 + 16)` (its slot gets
the HIGH half, third disjunct) and never the leaf tweak `[slot 0 + 16, slot 0 + 32)`, whose high word stays witness
memory (`wleafHigh`); the other chains write from `slot 1` on (first disjunct); pairing stage 1: chain blocks are
written as `chainWr` (second disjunct). -/
def bufferWr (c : LCtx) (i A : Nat) : Prop :=
  (c.bufferSlot c.i0 ≤ A ∧ A < c.bufferEnd i ∧ (c.i0 = 0 → c.bufferSlot 1 ≤ A)) ∨
    (∃ j, c.i0 ≤ j ∧ j < i ∧ c.chainWr j A) ∨
    (c.i0 = 0 ∧ 0 < i ∧ c.bufferSlot 0 - 16 ≤ A ∧ A < c.bufferSlot 0 + 16)
/-- C3: write address of the final step of chain `i` (`slotL`, or 16 below it for chain 0). -/
def outSlot (c : LCtx) (i : Nat) : Nat := c.bufferOffset + outL i
/-- C3 + pairing stage 1: the half of chain `i`'s step-`m` answer the image keeps (chain 0's last step, and every
interior step of a G chain). -/
def stepHigh (i m : Nat) : Bool := decide (m = 6 ∧ i = 0) || (lowerG i && decide (m < 6))
def bufferOrig (c : LCtx) (s0 : MachineState) : Prop :=
  ∀ i, c.i0 ≤ i → i ≤ 42 → ∀ k < 2, OrigW c.w s0 (c.bufferSlot i + 8*k)
def bufferVal (c : LCtx) (i : Nat) : Digest :=
  if c.bufferSafe i then ClaudeWCT.W9.T3M.wdig c.w (c.bufferSlot i - Verify.WIT) else c.val i


def ok (c : LCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.koff ≤ 16 ∧ c.S6 % 8 = 0 ∧ Verify.WIT + 8096 + 520 ≤ c.S6 ∧
    c.S6 + 1744 ≤ 0x7000 ∧ c.ck ≤ 8 ∧ c.ret = ckSlot c.ck + partLen c.ck ∧ c.i0 ≤ 42 ∧
    c.tree < 2 ^ (31 - height c.lay) ∧ c.leaf < 2 ^ height c.lay ∧
    2 ^ 63 ≤ c.d0.toNat ∧ 2 ^ 63 ≤ c.d1.toNat
def x28v (c : LCtx) : Nat := packedPrefix c.lay c.tree c.leaf + c.koff + 385
theorem x28v_eq (c : LCtx) (h0 : c.koff = 0) : c.x28v = packedPrefix c.lay c.tree c.leaf + 385 := by
  generalize hp : packedPrefix c.lay c.tree c.leaf = q
  unfold x28v; rw [hp]; omega
def known (c : LCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 c.x28v), (.x2, 0x7fc00), (.x27, 0x3fe00), (.x5, 0),
   (.x22, BitVec.ofNat 64 c.S6),
   (.x16, c.d0), (.x17, c.d1), (.x29, 7#64 - BitVec.ofNat 64 c.ck),
   (.x4, BitVec.ofNat 64 c.bufferOffset)]
def kOf (c : LCtx) (t : Nat) : Nat := c.dig (3 * t) + 8 * c.dig (3 * t + 1) + 64 * c.dig (3 * t + 2)
def tb (c : LCtx) (i : Nat) : Nat := triBase (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tB (c : LCtx) (i : Nat) : Nat := pcB (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tC (c : LCtx) (i : Nat) : Nat := pcC (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tX (c : LCtx) (i : Nat) : Nat := pcX (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def startPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ckSlot c.ck
  else if i % 3 = 0 then entW (i / 3) (c.kOf (i / 3))
  else if i % 3 = 1 then c.tB i + (if 1 < i ∧ c.dig (i-1) = 7 ∧ c.dig i = 7 then 4 else 0) else c.tC i
def rungPc (c : LCtx) (i m : Nat) : Nat :=
  if i % 3 = 0 ∧ i ≠ 42 then c.tb i + 2 * m
  else c.startPc i + 3 + 2 * (m - c.dig i) - (if c.dig i = 6 then 1 else 0)
def endPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ckSlot c.ck + partLen c.ck
  else if i % 3 = 0 then c.tB i + (if 0 < i ∧ c.dig i = 7 ∧ c.dig (i+1) = 7 then 4 else 0)
  else if i % 3 = 1 then c.tC i else c.tX i
def Wr (c : LCtx) (i : Nat) (A : Nat) : Prop := c.bufferWr i A

def WrIn (c : LCtx) (i : Nat) (A : Nat) : Prop := c.Wr i A ∨ c.chainWr i A
def Orig0 (c : LCtx) (s0 : MachineState) : Prop :=
  (∀ i, c.i0 ≤ i → i ≤ 42 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ c.bufferOrig s0
def Base (c : LCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (c.bufferSlot (c.i0 + j)) (acc.getD j 0))
def ChainIn (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    s.pc = pcOf (c.startPc i)
def HdrOk (c : LCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 256 = 128 + i + c.koff ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 16 = packedHi c.lay c.tree c.leaf ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i
def StepInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    c.HdrOk i s ∧ DigAt s (c.vAt i) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    s.getReg .x12 = BitVec.ofNat 64 (c.oAt i) ∧ s.pc = pcOf (c.rungPc i m)
def PreHash (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 256 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i ∧ DigAt t (c.vAt i) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = 6 then c.outSlot i else c.oAt i) ∧
    t.pc = pcOf (c.rungPc i m + (if m = 6 then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)
def EndInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 - c.i0 ∧
    Verify.DataOK s0 ∧ s.pc = pcOf (c.endPc i)
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem memEval_one (s : MachineState) (k : Addr) (v : E) (a A : Nat) (h : k.eval s = BitVec.ofNat 64 a)
    (ha : a < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k, v)] (BitVec.ofNat 64 A) = if A = a then v.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h, memEval_nil]
  by_cases e : A = a
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha).mp h')), if_neg e]
theorem memEval_two (s : MachineState) (k1 k2 : Addr) (v1 v2 : E) (a1 a2 A : Nat)
    (h1 : k1.eval s = BitVec.ofNat 64 a1) (h2 : k2.eval s = BitVec.ofNat 64 a2) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k1, v1), (k2, v2)] (BitVec.ofNat 64 A) =
      if A = a1 then v1.eval s else if A = a2 then v2.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h1, memEval_one s k2 v2 a2 A h2 ha2 hA]
  by_cases e : A = a1
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha1).mp h')), if_neg e]
theorem replaceByte_toNat (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide +kernel
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
theorem stepByte (w : Word) (L J m : Nat) (hL : L < 256) (hm : m < 256) (hJ : J < 2 ^ 48)
    (h1 : w.toNat % 256 = L) (h2 : w.toNat / 2 ^ 16 = J) :
    StoreKind.merge .b w 1 (BitVec.ofNat 64 m) = BitVec.ofNat 64 (L + 256 * m + 2 ^ 16 * J) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show L + 256 * m + 2 ^ 16 * J < 2 ^ 64 by omega)]
  generalize w.toNat = x at *
  norm_num at h1 h2 ⊢
  omega
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem lowerSlot_props (i : Nat) (hi : i ≤ 42) :
    lowerSlot i % 8 = 0 ∧ 16 ≤ lowerSlot i ∧ lowerSlot i ≤ 2184 ∧ (0 < i → lowerSlot i ≤ 2120) := by
  unfold lowerSlot; split_ifs <;> omega
theorem blk_props (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    c.blk i % 8 = 0 ∧ Verify.WIT + 8096 + 16 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, -, h64, hlo, hhi, -⟩ := hc
  have := lowerSlot_props i hi
  unfold blk Verify.WIT at *; refine ⟨?_, ?_, ?_⟩ <;> omega
theorem vAt_eq (c : LCtx) (i : Nat) : c.vAt i = c.blk i + (if lowerG i then 0 else 48) := by
  unfold vAt gVal; cases lowerG i <;> simp
theorem vAt_bound (c : LCtx) (i : Nat) : (c.vAt i + 16 ≤ c.blk i + 16 ∧ c.blk i ≤ c.vAt i) ∨
    (c.blk i + 48 = c.vAt i) := by
  rw [vAt_eq]; cases lowerG i <;> simp
theorem oAt_props (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    c.oAt i % 8 = 0 ∧ Verify.WIT + 8096 ≤ c.oAt i ∧ c.oAt i + 32 ≤ 0x7000 ∧ c.oAt i + 16 ≤ c.vAt i + 16 ∧
      c.vAt i + 16 ≤ c.oAt i + 32 ∧ (lowerG i = true → c.oAt i + 16 = c.vAt i) ∧
      (lowerG i = false → c.oAt i = c.vAt i) := by
  have hb := c.blk_props hc i hi
  rw [vAt_eq]; unfold oAt
  cases h : lowerG i <;> simp <;> omega
/-- Every byte a chain writes lies in its layer's chain area (chain 0's destination spills 16 bytes past it). -/
theorem chainWr_range (c : LCtx) (hc : c.ok) {j A : Nat} (hj : j ≤ 42) (h : c.chainWr j A) :
    c.S6 - 520 ≤ A ∧ A < c.S6 - 520 + 2248 + (if j = 0 then 16 else 0) := by
  have hlo := hc.2.2.2.2.1
  have := lowerSlot_props j hj
  unfold chainWr oAt blk at h
  simp only [lowerG, lowerSlot, decide_eq_true_eq] at h this ⊢
  split_ifs at h this ⊢ <;> omega
theorem chainWr_range' (c : LCtx) {j A : Nat} (hj : j ≤ 42) (h : c.chainWr j A) :
    c.S6 - 520 ≤ A ∧ A < c.S6 - 520 + 2264 := by
  have := lowerSlot_props j hj
  unfold chainWr oAt blk at h
  simp only [lowerG, lowerSlot, decide_eq_true_eq] at h this ⊢
  split_ifs at h this ⊢ <;> omega
/-- Coarse shape of the chain frame (the chain blocks lumped into the chain area). -/
theorem Wr_range (c : LCtx) {i A : Nat} (hi : i ≤ 43) (h : c.Wr i A) :
    (c.bufferSlot c.i0 ≤ A ∧ A < c.bufferEnd i ∧ (c.i0 = 0 → c.bufferSlot 1 ≤ A)) ∨
      (c.S6 - 520 ≤ A ∧ A < c.S6 - 520 + 2264) ∨
      (c.i0 = 0 ∧ 0 < i ∧ c.bufferSlot 0 - 16 ≤ A ∧ A < c.bufferSlot 0 + 16) := by
  rcases h with h | ⟨j, -, hji, hj⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (c.chainWr_range' (by omega) hj))
  · exact Or.inr (Or.inr h)
/-- Pairing stage 1: a chain processed earlier never wrote a byte of a later chain's 64-byte block. -/
theorem chainWr_disj (c : LCtx) {j k A : Nat} (hjk : j < k) (hk : k ≤ 42) (h : c.chainWr j A) :
    A < c.blk k ∨ c.blk k + 64 ≤ A := by
  unfold chainWr oAt blk at h
  unfold blk
  simp only [lowerG, lowerSlot, decide_eq_true_eq] at h ⊢
  split_ifs at h ⊢ <;> omega
/-- A chain's own writes miss its pads and its header pad word. -/
theorem chainWr_self (c : LCtx) (hc : c.ok) {i A : Nat} (hi : i ≤ 42) (h : c.chainWr i A) :
    ¬ (c.blk i + (if lowerG i then 32 else 0) ≤ A ∧ A < c.blk i + (if lowerG i then 32 else 0) + 16) ∧
    ¬ (c.blk i + (if lowerG i then 48 else 32) ≤ A ∧ A < c.blk i + (if lowerG i then 48 else 32) + 16) ∧
    ¬ (c.blk i + 24 ≤ A ∧ A < c.blk i + 32) := by
  have hb := c.blk_props hc i hi
  unfold chainWr oAt at h
  cases hg : lowerG i <;> simp [hg] at h ⊢ <;> omega
theorem slotL_mono (i j : Nat) (h : i ≤ j) : slotL i ≤ slotL j := by unfold slotL; split_ifs <;> omega
theorem slotL_props (i : Nat) (hi : i ≤ 42) : slotL i % 16 = 0 ∧ 768 ≤ slotL i ∧ slotL i + 32 ≤ 0x5D0 := by
  unfold slotL; split <;> omega
theorem bufferSlot_props (c : LCtx) (i : Nat) (hi : i ≤ 42) :
    c.bufferSlot i % 8 = 0 ∧ 23008 ≤ c.bufferSlot i ∧ c.bufferSlot i + 32 ≤ 25920 := by
  have hb : 20104 ≤ ClaudeWCT.W9.T3M.leafBufferBase c.lay ∧
      ClaudeWCT.W9.T3M.leafBufferBase c.lay ≤ 22296 ∧
      ClaudeWCT.W9.T3M.leafBufferBase c.lay % 8 = 0 := by
    generalize c.lay = lay
    fin_cases lay <;> decide +kernel
  have hs := slotL_props i hi
  unfold bufferSlot bufferOffset Verify.WIT
  omega

theorem bufferEnd_bounds (c : LCtx) (i : Nat) :
    c.bufferSlot i ≤ c.bufferEnd i ∧ c.bufferEnd i ≤ c.bufferSlot i + 16 := by
  unfold bufferEnd; split <;> omega

theorem bufferEnd_mono (c : LCtx) (i : Nat) : c.bufferEnd i ≤ c.bufferEnd (i+1) := by
  have h := c.bufferEnd_bounds i
  have h' := c.bufferEnd_bounds (i+1)
  unfold bufferSlot slotL at *
  split_ifs at * <;> omega

theorem bufferWr_mono (c : LCtx) (i A : Nat) : c.bufferWr i A → c.bufferWr (i+1) A := by
  intro h
  have hm := c.bufferEnd_mono i
  unfold bufferWr at *
  rcases h with h | ⟨j, hj0, hji, hj⟩ | h
  · left; exact ⟨h.1, by omega, h.2.2⟩
  · right; left; exact ⟨j, hj0, by omega, hj⟩
  · right; right; omega

theorem bufferWr_copy (c : LCtx) (i A : Nat) (hi0 : c.i0 ≤ i) (hiz : 0 < i)
    (hlo : c.bufferSlot i ≤ A) (hhi : A < c.bufferSlot i + 16) : c.bufferWr (i+1) A := by
  have h := c.bufferEnd_bounds (i+1)
  have hmon := slotL_mono c.i0 i hi0
  unfold bufferWr bufferSlot at *
  left
  unfold slotL at *
  split_ifs at * <;> omega

theorem bufferWr_hash (c : LCtx) (i A : Nat) (hi0 : c.i0 ≤ i) (hiz : 0 < i) (hn : c.dig i ≠ 7)
    (hlo : c.bufferSlot i ≤ A) (hhi : A < c.bufferSlot i + 32) : c.bufferWr (i+1) A := by
  have he : c.bufferEnd (i+1) = c.bufferSlot (i+1) + (if 0 < i then 16 else 0) := by
    simp only [bufferEnd, Nat.add_sub_cancel]
    split_ifs <;> omega
  have hmon := slotL_mono c.i0 i hi0
  unfold bufferWr
  left
  rw [he]
  unfold bufferSlot slotL at *
  split_ifs at * <;> omega

theorem outSlot_ne (c : LCtx) (i : Nat) (hi : i ≠ 0) : c.outSlot i = c.bufferSlot i := by
  unfold outSlot bufferSlot outL; rw [if_neg hi]
theorem outSlot_zero (c : LCtx) : c.outSlot 0 + 16 = c.bufferSlot 0 := by
  unfold outSlot bufferSlot outL slotL; simp
theorem bufferWr_hash0 (c : LCtx) (A : Nat) (hi0 : c.i0 = 0)
    (hlo : c.outSlot 0 ≤ A) (hhi : A < c.outSlot 0 + 32) : c.bufferWr 1 A := by
  have e := c.outSlot_zero
  unfold bufferWr
  right; right; omega
theorem stepHigh_lt (i m : Nat) (hm : m < 6) : stepHigh i m = lowerG i := by
  unfold stepHigh; cases lowerG i <;> simp <;> omega
theorem stepHigh_six (i : Nat) : stepHigh i 6 = decide (i = 0) := by
  unfold stepHigh; simp
theorem bufferSafe_end (c : LCtx) (i : Nat) (hs : c.bufferSafe i) :
    c.bufferEnd i = c.bufferSlot i := by
  rcases hs.2 with h | h | h
  · simp [bufferEnd,h]
  · simp [bufferEnd,h]
  · simp [bufferEnd,h.2.2]

theorem bufferSafe_protected (c : LCtx) (hc : c.ok) (i A : Nat) (hi : i ≤ 42) (hs : c.bufferSafe i)
    (hb : c.blk 0 + 64 ≤ c.bufferSlot 0) (ha : c.bufferSlot i ≤ A) : ¬c.bufferWr i A := by
  rw [bufferWr,c.bufferSafe_end i hs]
  rintro (h | ⟨j, -, hji, hj⟩ | h)
  · unfold bufferSlot slotL at *; split_ifs at * <;> omega
  · have hr := c.chainWr_range hc (by omega) hj
    have h0 : c.blk 0 = c.S6 - 520 + 2184 := rfl
    have hz : i ≠ 0 := by omega
    unfold bufferSlot slotL at *
    split_ifs at * <;> omega
  · unfold bufferSlot slotL at *; split_ifs at * <;> omega

theorem bufferVal_at {c : LCtx} (hc : c.ok) {s0 t : MachineState} (h0 : c.bufferOrig s0)
    {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hs : c.bufferSafe i)
    (hb : c.blk 0 + 64 ≤ c.bufferSlot 0) (hF : Frame s0 t (c.bufferWr i)) :
    DigAt t (c.bufferSlot i) (c.bufferVal i) := by
  have hp := c.bufferSlot_props i hi.2
  have o0 := h0 i hi.1 hi.2 0 (by omega)
  have o1 := h0 i hi.1 hi.2 1 (by omega)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at o0 o1
  have f0 := hF (c.bufferSlot i) (by omega) (c.bufferSafe_protected hc i _ hi.2 hs hb (by omega))
  have f1 := hF (c.bufferSlot i+8) (by omega) (c.bufferSafe_protected hc i _ hi.2 hs hb (by omega))
  have hW : Verify.WIT ≤ c.bufferSlot i := by unfold Verify.WIT; omega
  have t0 : OrigW c.w t (c.bufferSlot i) := by unfold OrigW at *; rw [f0]; exact o0
  have t1 : OrigW c.w t (c.bufferSlot i+8) := by unfold OrigW at *; rw [f1]; exact o1
  rw [bufferVal,if_pos hs]
  exact DigAt_origW t0 t1 hW
theorem bufferSlot_mono (c : LCtx) (i j : Nat) (h : i ≤ j) :
    c.bufferSlot i ≤ c.bufferSlot j := by
  have := slotL_mono i j h
  unfold bufferSlot
  omega

theorem bufferSlot_gap (c : LCtx) (i j : Nat) (h : i < j) :
    c.bufferSlot i + 16 ≤ c.bufferSlot j := by
  unfold bufferSlot slotL
  split_ifs <;> omega

theorem bufferArea_slot (c : LCtx) : c.S6 - 520 + 2248 ≤ c.bufferSlot 0 := by
  have hs : c.bufferSlot 0 = Verify.WIT + ClaudeWCT.W9.T3M.leafBufferBase c.lay := by
    unfold bufferSlot bufferOffset Verify.WIT
    rw [show slotL 0 = 768 from rfl]
    have : 20104 ≤ ClaudeWCT.W9.T3M.leafBufferBase c.lay := by
      generalize c.lay = lay; fin_cases lay <;> decide +kernel
    omega
  rw [hs]
  exact c.bufferBound
theorem bufferBound_slot (c : LCtx) : c.blk 0 + 64 ≤ c.bufferSlot 0 := by
  have := c.bufferArea_slot
  unfold blk; rw [show lowerSlot 0 = 2184 from rfl]; omega

theorem block_before_buffer (c : LCtx) (i j : Nat) (hi : i ≤ 42) : c.blk i + 64 ≤ c.bufferSlot j := by
  have h := c.bufferArea_slot
  have hm := c.bufferSlot_mono 0 j (by omega)
  have := lowerSlot_props i hi
  unfold blk at *
  omega

theorem block_gap_buffer (c : LCtx) (i j : Nat) (hi : 0 < i) (hi42 : i ≤ 42) :
    c.blk i + 80 ≤ c.bufferSlot j := by
  have h := c.bufferArea_slot
  have hm := c.bufferSlot_mono 0 j (by omega)
  have := (lowerSlot_props i hi42).2.2.2 hi
  unfold blk at *
  omega

theorem bufferE_eval' (c : LCtx) {s : MachineState}
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (k : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 k)).eval s = BitVec.ofNat 64 (c.bufferOffset + k) := by
  rw [addC_eval]
  simp only [E.eval, h4, ofNat_add_ofNat]
theorem bufferE_eval (c : LCtx) {s : MachineState}
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 (slotL i))).eval s = BitVec.ofNat 64 (c.bufferSlot i) := by
  rw [addC_eval]
  simp only [E.eval, h4, ofNat_add_ofNat, bufferSlot]

theorem bufferAddr_eval (c : LCtx) {s : MachineState}
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i k : Nat) :
    (⟨some (.reg .x4), BitVec.ofNat 64 (slotL i+k)⟩ : Addr).eval s =
      BitVec.ofNat 64 (c.bufferSlot i+k) := by
  simp only [Addr.eval, E.eval, h4, ofNat_add_ofNat, bufferSlot, Nat.add_assoc]

theorem WrIn_next (c : LCtx) (i A : Nat) (hi0 : c.i0 ≤ i) (hi42 : i ≤ 42)
    (h : c.WrIn i A) : c.Wr (i+1) A := by
  rcases h with h | h
  · exact c.bufferWr_mono i A h
  · exact Or.inr (Or.inl ⟨i, hi0, by omega, h⟩)

theorem base_off (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S6 + (offL i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  have := lowerSlot_props i hi
  unfold offL blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S6 + lowerSlot i - 520 = c.S6 - 520 + lowerSlot i by
    omega]
theorem base_off0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    BitVec.ofNat 64 c.S6 + offL i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  have := lowerSlot_props i hi
  unfold offL blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S6 + lowerSlot i - 520 = c.S6 - 520 + lowerSlot i by
    omega]
/-- The hash destination register of an interior step (`gOut`). -/
theorem oAt_eval (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) (x : Word) (hx : x = BitVec.ofNat 64 (c.blk i)) :
    x + gOut (lowerG i) = BitVec.ofNat 64 (c.oAt i) := by
  have hb := c.blk_props hc i hi
  subst hx
  unfold oAt
  cases hg : lowerG i
  · simp only [Bool.false_eq_true, if_false]
    rw [show gOut false = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · simp only [if_true]
    rw [show gOut true = BitVec.ofNat 64 18446744073709551600 by unfold gOut; rfl, BitVec.ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show c.blk i + 18446744073709551600 = (c.blk i - 16) + 2^64 by omega,
      Nat.add_mod_right]
theorem known_get (c : LCtx) {s : MachineState} (h : ∀ p ∈ c.known, s.getReg p.1 = p.2) {r : Reg} {v : Word}
    (hm : (r, v) ∈ c.known) : s.getReg r = v := h _ hm
theorem w0_hdr0 (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 8) :
    BitVec.ofNat 64 (c.w0 i + 256 * m) = (chainHeader c.lay c.tree c.leaf (i + c.koff) m).extractLsb' 0 64 := by
  rw [chainHeader_low_bounded _ _ _ _ _ (by have := hc.2.2.1; omega) hm
    hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1]
  congr 1; unfold w0; omega
theorem w0_lt (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) : c.w0 i + 256 * m < 2 ^ 64 := by
  obtain ⟨-, -, hk, -⟩ := hc
  have hh := packedHi_lt c.lay c.tree c.leaf
  unfold w0 packedPrefix; omega
theorem w1_lt (c : LCtx) : c.w1 < 2 ^ 64 := hdr1_lt _ _
set_option maxRecDepth 20000 in
theorem chain_hashInput (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 8) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.pad0At i) (c.pad0 i)) (hp1 : DigAt t (c.pad1At i) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 256 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i)
    (hv : DigAt t (c.vAt i) v) :
    hashInput t = toQ (chainInputL c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) (c.padHeader i) v
      (lowerG i)) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputL_length _ _ _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputL, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two]
  rw [vAt_eq] at hv
  simp only [pad0At, pad1At] at hp0 hp1
  split
  · rename_i hg
    simp only [hg, if_true, Nat.add_zero] at hv hp0 hp1
    rw [hv.1, hv.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp0.1, hp0.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hp1.1, hp1.2, w0_hdr0 c hc i m hi hm]
    rfl
  · rename_i hg
    simp only [hg, Bool.false_eq_true, if_false, Nat.add_zero] at hv hp0 hp1
    rw [hp0.1, hp0.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_hdr0 c hc i m hi hm]
    rfl
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem orig_frame {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := (c.blk_props hc i hi.2)
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1 i hi.1 hi.2 k hk
/-- Pairing stage 1: no chain processed before chain `i` (nor a buffer write) touched chain `i`'s block. -/
theorem notWr_block (c : LCtx) (hc : c.ok) {i A : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (h1 : c.blk i ≤ A)
    (h2 : A < c.blk i + 64) : ¬ c.Wr i A := by
  have hbb := c.block_before_buffer i c.i0 hi.2
  have harea := c.bufferArea_slot
  have hls := lowerSlot_props i hi.2
  rintro (h | ⟨j, -, hji, hj⟩ | h)
  · omega
  · rcases c.chainWr_disj hji hi.2 hj with h' | h' <;> omega
  · have : 0 < i := h.2.1
    have := hls.2.2.2 this
    unfold blk at h1 h2
    omega
theorem orig_at {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i A : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hA1 : c.blk i ≤ A) (hA2 : A + 8 ≤ c.blk i + 64)
    (hA8 : (A - c.blk i) % 8 = 0) (hW : ¬ W A) : OrigW c.w t A := by
  have e : A = c.blk i + 8 * ((A - c.blk i) / 8) := by omega
  rw [e] at hW ⊢
  exact orig_frame hF h0 hc hi (by omega) hW
theorem dig_at {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i A : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hA1 : c.blk i ≤ A) (hA2 : A + 16 ≤ c.blk i + 64)
    (hA8 : (A - c.blk i) % 8 = 0) (hW0 : ¬ W A) (hW1 : ¬ W (A + 8)) :
    DigAt t A (ClaudeWCT.W9.T3M.wdig c.w (A - Verify.WIT)) := by
  have hb := c.blk_props hc i hi.2
  exact DigAt_origW (orig_at hF h0 hc hi hA1 (by omega) hA8 hW0) (orig_at hF h0 hc hi (by omega) (by omega)
    (by omega) hW1) (by omega)
theorem pads_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : c.i0 ≤ i ∧ i ≤ 42) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.pad0At i) (c.pad0 i) ∧ DigAt t (c.pad1At i) (c.pad1 i) := by
  have hb := c.blk_props hc i hi.2
  unfold pad0 pad1
  by_cases hg : lowerG i = true
  · have e0 : c.pad0At i = c.blk i + 32 := by simp [pad0At, hg]
    have e1 : c.pad1At i = c.blk i + 48 := by simp [pad1At, hg]
    have nc : ∀ A, c.chainWr i A → A < c.blk i + 24 := by
      intro A h; unfold chainWr oAt at h; simp only [hg, if_true] at h; omega
    have nW : ∀ A, c.blk i + 32 ≤ A → A < c.blk i + 64 → ¬ c.WrIn i A := by
      intro A h1 h2 hw
      rcases hw with hw | hw
      · exact c.notWr_block hc hi (by omega) h2 hw
      · have := nc A hw; omega
    rw [e0, e1]
    exact ⟨dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega)),
      dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega))⟩
  · have e0 : c.pad0At i = c.blk i := by simp [pad0At, hg]
    have e1 : c.pad1At i = c.blk i + 32 := by simp [pad1At, hg]
    have nc : ∀ A, c.chainWr i A → (c.blk i + 16 ≤ A ∧ A < c.blk i + 24) ∨ c.blk i + 48 ≤ A := by
      intro A h; unfold chainWr oAt at h; simp only [hg, Bool.false_eq_true, if_false] at h; omega
    have nW : ∀ A, c.blk i ≤ A → A < c.blk i + 48 → (A < c.blk i + 16 ∨ c.blk i + 32 ≤ A) → ¬ c.WrIn i A := by
      intro A h1 h2 h3 hw
      rcases hw with hw | hw
      · exact c.notWr_block hc hi h1 (by omega) hw
      · have := nc A hw; omega
    rw [e0, e1]
    exact ⟨dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega))
        (nW _ (by omega) (by omega) (by omega)),
      dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega))
        (nW _ (by omega) (by omega) (by omega))⟩
theorem rungPc_succ (c : LCtx) (i m : Nat) (hd : c.dig i ≤ m) : c.rungPc i (m + 1) = c.rungPc i m + 2 := by
  unfold rungPc; split_ifs <;> omega
theorem dig_lt (c : LCtx) (hc : c.ok) (i : Nat) (hi : i < 42) : c.dig i < 8 := by
  unfold dig; split_ifs <;> omega
theorem dig42 (c : LCtx) : c.dig 42 = c.ck := by unfold dig; simp
set_option maxHeartbeats 1000000 in
theorem rungPc_end (c : LCtx) (i : Nat) (hi : i ≤ 42) (hd : c.dig i < 7) : c.rungPc i 6 + 3 = c.endPc i := by
  by_cases h42 : i = 42
  · subst h42
    have e := c.dig42
    unfold rungPc endPc startPc partLen
    simp only [show ¬ (42 % 3 = 0 ∧ (42 : Nat) ≠ 42) by decide +kernel, if_false, if_true, e] at hd ⊢
    split_ifs <;> omega
  · have e1 : i % 3 = 1 → c.dig (3 * (i / 3) + 1) = c.dig i := fun h => by rw [show 3 * (i / 3) + 1 = i by omega]
    have e2 : i % 3 = 2 → c.dig (3 * (i / 3) + 2) = c.dig i := fun h => by rw [show 3 * (i / 3) + 2 = i by omega]
    unfold rungPc endPc startPc tb tB tC tX pcX pcC pcB partLen
    simp only [if_neg h42]
    split_ifs <;> omega
theorem prehash_step (c : LCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputL c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) (c.padHeader i) v
        (lowerG i)) ∧
      ∀ a : BitVec 256,
        (m < 6 → c.StepInv s0 i acc (m + 1) (Verify.vHalf (stepHigh i m) a) (writeHash t a)) ∧
        (m = 6 → c.EndInv s0 i (acc ++ [Verify.vHalf (stepHigh i m) a]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  have ho := c.oAt_props hc i hi.2
  have hs := c.bufferSlot_props i hi.2
  have hs0 := c.bufferSlot_props 0 (by omega)
  have hw0 := c.outSlot_zero
  have hwi : i ≠ 0 → c.outSlot i = c.bufferSlot i := c.outSlot_ne i
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide +kernel)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide +kernel)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  have hwb : c.outSlot i % 8 = 0 ∧ c.outSlot i + 32 ≤ 25920 := by
    by_cases hi0 : i = 0
    · subst hi0; omega
    · rw [hwi hi0]; omega
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = 6 then c.outSlot i else c.oAt i) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi.2 (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm6 => ?_, fun hm6 => ?_⟩
    ·
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.oAt i) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; exact h)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.oAt i ≤ A ∧ A < c.oAt i + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      have hhdr : c.oAt i + 32 ≤ c.blk i + 16 ∨ c.blk i + 32 ≤ c.oAt i := by
        unfold oAt; cases lowerG i <;> simp <;> omega
      have hnew : DigAt (writeHash t a) (c.vAt i) (Verify.vHalf (stepHigh i m) a) := by
        rw [stepHigh_lt i m (by omega)]
        cases hg : lowerG i
        · rw [(ho.2.2.2.2.2.2 hg).symm, Verify.vHalf_false]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
        · rw [(ho.2.2.2.2.2.1 hg).symm, Verify.vHalf_true]
          exact DigAt.writeHash_hi t a _ d12 (by omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        h25, ⟨?_, ?_, ?_⟩, hnew,
        by rw [getReg_writeHash]; exact h10, by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
        have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
        have : c.oAt i + 32 ≤ c.blk i + 80 := by unfold oAt; cases lowerG i <;> simp <;> omega
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0 packedPrefix; have := hc.2.2.1; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0 packedPrefix; have := hc.2.2.1; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    ·
      subst hm6
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.outSlot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have hpcE : (writeHash t a).pc = pcOf (c.endPc i) := by
        have hd7 : c.dig i < 7 := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi.2 hd7, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
      by_cases hi0 : i = 0
      · subst hi0
        have hz : c.i0 = 0 := by omega
        have hacc : acc.length = 0 := by omega
        have fW : Frame s0 (writeHash t a) (c.Wr (0 + 1)) := (hF.trans fr).mono (by
          intro A _ h
          rcases h with h | h
          · exact c.WrIn_next 0 A hi.1 hi.2 h
          · exact c.bufferWr_hash0 A hz h.1 h.2)
        refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen]; omega,
          h25, hpcE⟩
        rw [List.length_append, List.length_singleton] at hj
        have hj2 : j = acc.length := by omega
        subst hj2
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
          show c.i0 + acc.length = 0 by omega]
        have hh : stepHigh 0 6 = true := by decide
        rw [hh, Verify.vHalf_true, ← hw0]
        exact DigAt.writeHash_hi t a _ d12 (by omega)
      · have d12' : t.getReg .x12 = BitVec.ofNat 64 (c.bufferSlot i) := by rw [d12, hwi hi0]
        have fr' := hdst _ d12' (by omega)
        have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr').mono (by
          intro A _ h
          rcases h with h | h
          · exact c.WrIn_next i A hi.1 hi.2 h
          · exact c.bufferWr_hash i A hi.1 (by omega) (by omega) h.1 h.2)
        have hh : stepHigh i 6 = false := by unfold stepHigh; simp [hi0]
        rw [hh, Verify.vHalf_false]
        refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen]; omega,
          h25, hpcE⟩
        · rw [List.length_append, List.length_singleton] at hj
          by_cases hjl : j < acc.length
          · have hj' := hS j hjl
            have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
            have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
            have hmono : c.bufferSlot (c.i0 + j) + 16 ≤ c.bufferSlot i := by unfold bufferSlot slotL; split_ifs <;> omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
            exact hj'.frame fr' (by omega) (by omega) (by omega)
          · have hj2 : j = acc.length := by omega
            subst hj2
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
              show c.i0 + acc.length = i by omega]
            exact DigAt.writeHash_lo t a _ d12' (by omega)
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem posE_eval (c : LCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (m : Nat) (hm : m ≤ 6) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  interval_cases m
  · rfl
  · exact kr .x7 1 (by simp [known]) (by decide +kernel)
  · exact kr .x13 2 (by simp [known]) (by decide +kernel)
  · exact kr .x19 3 (by simp [known]) (by decide +kernel)
  · exact kr .x20 4 (by simp [known]) (by decide +kernel)
  · exact kr .x21 5 (by simp [known]) (by decide +kernel)
  · exact kr .x26 6 (by simp [known]) (by decide +kernel)
theorem w0_low (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) :
    (BitVec.ofNat 64 (c.w0 i + 256 * m)).toNat % 256 = 128 + i + c.koff ∧
      (BitVec.ofNat 64 (c.w0 i + 256 * m)).toNat / 2 ^ 16 = packedHi c.lay c.tree c.leaf := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi hm)]
  have := hc.2.2.1
  unfold w0 packedPrefix; constructor <;> omega
theorem rung_piece (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i ≤ 42) (hm : m ≤ 6) (hp : p < 257214)
    (hrun : vrun p 3 = some (rungRB m (if m = 6 then some (outL i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = 6 → t.getReg .x12 = BitVec.ofNat 64 (c.outSlot i)) ∧ (m < 6 → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 256 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = 6 then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  set r := rungRB m (if m = 6 then some (outL i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungRB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 17⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (17 : Word) = BitVec.ofNat 64 17 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun hp s hpc hobl
  have hec := piece_ecall hrun hp s hobl (by simp [hr, rungRB])
  have hn : r.steps = (if m = 6 then 2 else 1) ∧ r.cycles = (if m = 6 then 2 else 1) := by
    simp only [hr, rungRB]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungRB_keeps m (if m = 6 then some (outL i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 1 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungRB]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h6 => ?_, fun h6 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungRB, if_pos h6]
    rw [RegFile.get_set_self _ _ (by decide +kernel)]
    exact c.bufferE_eval' ((hR .x4 (by decide +kernel)).trans (hk (.x4, BitVec.ofNat 64 c.bufferOffset) (by simp [known]))) (outL i)
  · rw [Result.toState_getReg]
    simp only [hr, rungRB, if_neg (show m ≠ 6 by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have := c.lay.isLt
    have hkoff := hc.2.2.1
    rw [stepByte _ _ _ _ (by omega) (by omega) (packedHi_lt _ _ _) hl hj]
    congr 1; unfold w0 packedPrefix; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungRB]
    by_cases h6 : m = 6 <;> simp [h6, E.eval]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem not_mem_sub {x : Reg} {ws : List Reg} (hx : x ∉ chainRegs) (h : ws ⊆ chainRegs) : x ∉ ws :=
  fun hm => hx (h hm)
theorem w0_low0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    (BitVec.ofNat 64 (c.w0 i)).toNat % 256 = 128 + i + c.koff ∧
      (BitVec.ofNat 64 (c.w0 i)).toNat / 2 ^ 16 = packedHi c.lay c.tree c.leaf := by
  have := c.w0_low hc i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this
theorem rung_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hp : c.rungPc i m < 257214)
    (hrun : vrun (c.rungPc i m) 3 = some (rungRB m (if m = 6 then some (outL i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi.2 hm hp hrun s hpc hR h10 hH
  have hvb := c.vAt_bound i
  have hs := c.bufferSlot_props i hi.2
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
    have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide +kernel)]; exact h10
  · by_cases h6 : m = 6
    · rw [h12a h6, if_pos h6]
    · rw [h12b (by omega), h12, if_neg h6]
  · rw [hpc']
theorem val_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.vAt i) (c.val i) := by
  unfold val
  rw [vAt_eq]
  cases hg : lowerG i <;> simp only [Bool.false_eq_true, if_true, if_false] <;>
    exact dig_at hF h0 hc hi (by omega) (by omega) (by omega) (c.notWr_block hc hi (by omega) (by omega))
      (c.notWr_block hc hi (by omega) (by omega))
theorem Wr_mono (c : LCtx) (i : Nat) (A : Nat) (h : c.Wr i A) : c.WrIn i A := Or.inl h
theorem bv385 (a b : Nat) :
    BitVec.ofNat 64 (a + 385) + (BitVec.ofNat 64 b - BitVec.ofNat 64 385) = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem header_load (c : LCtx) {s : MachineState} (i d : Nat)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 c.x28v) :
    (hLoad i d).eval s = BitVec.ofNat 64 (c.w0 i + 256 * d) := by
  rw [hLoad, addC_eval]
  show s.getReg .x28 + (BitVec.ofNat 64 (i + 256 * d) - BitVec.ofNat 64 385) = _
  rw [h28, LCtx.x28v, bv385]
  congr 1
  unfold w0
  omega
theorem padHeader_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0)
    {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hF : Frame s0 t (c.Wr i)) :
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i := by
  have hb := c.blk_props hc i hi.2
  have h := orig_at hF h0 hc hi (A := c.blk i + 24) (by omega) (by omega) (by omega)
    (c.notWr_block hc hi (by omega) (by omega))
  simpa only [OrigW, padHeader, show c.blk i + 24 - Verify.WIT = c.blk i - Verify.WIT + 24 by omega] using h
theorem fetch_pc_congr {u v : MachineState} (h : u.pc = v.pc) : fetch vimage u = fetch vimage v := by
  unfold fetch; rw [h]
theorem headJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 257214) (hp1 : c.rungPc i (c.dig i) + landOff (c.dig i) < 257214)
    (hrun1 : vrun (c.startPc i) 7 = some (headJHB .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i
      (c.dig i) (hSlot i (c.dig i)) (lowerG i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 =
      some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  have hs := c.bufferSlot_props i hi.2
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE : ∀ k, k ≤ 80 → (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
    intro k hk'
    simp only [kAt, Addr.eval, E.eval, h22]
    exact c.base_off hc i hi.2 k hk'
  set r := headJHB .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i))
    (lowerG i) with hr
  have htable := c.header_load i (c.dig i)
    (kr _ _ (by simp [known]) (by decide +kernel))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJHB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun1 hp0 s hpc hobl
  have hn : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headJHB_keeps .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i))
    (lowerG i)
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i hi.2
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 256 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headJHB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA, htable]
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hp24 := padHeader_at hc h0 hi hF
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hvb := c.vAt_bound i
  have hpcT : (r.toState s).pc = pcOf (c.rungPc i (c.dig i) + landOff (c.dig i)) := by
    rw [Result.toState_pc]; simp only [hr, headJHB, E.eval]
  have hec : fetch vimage (r.toState s) = some (.base .ECALL) := by
    have hE := piece_ecall hrun2 hp1 (r.toState s) (by simp [ecallR, SymState.init]) rfl
    rw [← hE]
    apply fetch_pc_congr
    rw [hpcT, Result.toState_pc]; simp only [ecallR, E.eval]
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
    have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega)]; exact hp24
  · rw [Result.toState_getReg]; simp only [hr, headJHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headJHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    by_cases h6 : c.dig i = 6
    · simp only [hSlot, h6, if_true, E.eval]
      exact c.bufferE_eval' h4 (outL i)
    · simp only [hSlot, h6, if_false]
      rw [addC_eval]; exact c.oAt_eval hc i hi.2 _ a0e
  · rw [hpcT]; simp only [landOff]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem kAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h22]
  exact c.base_off hc i hi k hk
theorem lAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (lAt .x22 (offL i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h22]
  rw [c.base_off hc i hi k hk]
theorem copy_mem (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i : Nat)
    (hi : i ≤ 42) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMemB .x22 (offL i) (slotL i) (lowerG i)) (BitVec.ofNat 64 A) =
      if A = c.bufferSlot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = c.bufferSlot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := c.bufferSlot_props i hi
  have hg : gVal (lowerG i) ≤ 48 := by unfold gVal; split <;> omega
  unfold copyMemB
  rw [memEval_two s _ _ _ _ (c.bufferSlot i + 8) (c.bufferSlot i) A (c.bufferAddr_eval h4 i 8) (by simpa using c.bufferAddr_eval h4 i 0) (by omega) (by omega) hA,
    c.lAt_eval hc h22 i hi _ (by omega), c.lAt_eval hc h22 i hi _ (by omega)]
  simp only [vAt, Nat.add_assoc]
theorem copy_obl (c : LCtx) (hc : c.ok) {s : MachineState}
    (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset) (i : Nat)
    (hi : i ≤ 42) : ∀ o ∈ copyOblB .x22 (offL i) (slotL i) (lowerG i), o.holds s := by
  have hb := c.blk_props hc i hi
  have hg : gVal (lowerG i) = 0 ∨ gVal (lowerG i) = 48 := by unfold gVal; split <;> simp
  have hs := c.bufferSlot_props i hi
  simp only [copyOblB, copyObl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro o ((rfl | rfl) | (rfl | rfl))
  · show accessValid ((⟨some (.reg .x4), BitVec.ofNat 64 (slotL i+8)⟩ : Addr).eval s) 8 = true
    rw [c.bufferAddr_eval h4 i 8]
    exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((⟨some (.reg .x4), BitVec.ofNat 64 (slotL i)⟩ : Addr).eval s) 8 = true
    rw [show (⟨some (.reg .x4), BitVec.ofNat 64 (slotL i)⟩ : Addr).eval s = BitVec.ofNat 64 (c.bufferSlot i) by simpa using c.bufferAddr_eval h4 i 0]
    exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x22 (offL i) (gVal (lowerG i) + 8)).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi _ (by omega)]
    exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x22 (offL i) (gVal (lowerG i))).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi _ (by omega)]
    exact valid_ofNat _ _ (by omega) (by omega)
theorem copy_post (c : LCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (hiz : 0 < i) (acc : List Digest) (hlen : acc.length = i - c.i0) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (c.bufferSlot (c.i0 + j)) (acc.getD j 0))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      memEval s (copyMemB .x22 (offL i) (slotL i) (lowerG i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (c.bufferSlot (c.i0 + j)) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi.2
  have hbb := c.block_before_buffer i c.i0 hi.2
  have hs := c.bufferSlot_props i hi.2
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = c.bufferSlot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = c.bufferSlot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h22 h4 i hi.2 A hA)
  have hfr : Frame s t (fun A => A = c.bufferSlot i + 8 ∨ A = c.bufferSlot i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have hlo := hc.2.2.2.2.1
    have hsm := c.bufferSlot_mono c.i0 i hi.1
    rcases h with h | h
    · exact c.bufferWr_mono i A h
    · exact c.bufferWr_copy i A hi.1 hiz (by omega) (by omega)
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
      have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
      have hmono : c.bufferSlot (c.i0 + j) + 16 ≤ c.bufferSlot i := by unfold bufferSlot slotL; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        show c.i0 + acc.length = i by omega]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2
theorem copyJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hiz : 0 < i) (first : Bool)
    (hfirst : first = true → i = 0 ∧ c.koff = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 257214)
    (hrun : vrun (c.startPc i) 7 = some (copyNB .x22 (offL i) (slotL i) (c.endPc i) (lowerG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyNB .x22 (offL i) (slotL i) (c.endPc i) (lowerG i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyNB] using c.copy_obl hc h22 h4 i (by omega))
  have hkeep := copyNB_keeps .x22 (offL i) (slotL i) (c.endPc i) (lowerG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ hiz acc hlen hF hS h22 h4
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl
theorem copyF_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hi0 : i ≠ 0) (hp0 : c.startPc i < 257214)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFHB .x22 (offL i) (slotL i) (c.startPc i) (lowerG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyFHB .x22 (offL i) (slotL i) (c.startPc i) (lowerG i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyFHB] using c.copy_obl hc h22 h4 i (by omega))
  have hkeep := copyFHB_keeps .x22 (offL i) (slotL i) (c.startPc i) (lowerG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ (Nat.pos_of_ne_zero hi0) acc hlen hF hS
    h22 h4 (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFHB, E.eval]; rw [hend]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem headR_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hi0 : i ≠ 0) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 257214)
    (hrp : c.rungPc i (c.dig i) + (if c.dig i = 6 then 2 else 1) = c.startPc i + 4)
    (hrun : vrun (c.startPc i) 8 =
      some (headRVB .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i (lowerG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i (by omega)
  have hs := c.bufferSlot_props i (by omega)
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = BitVec.ofNat 64 c.bufferOffset := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h22 i (by omega)
  set r := headRVB .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i (lowerG i)
    with hr
  have htable := c.header_load i (c.dig i)
    (kr _ _ (by simp [known]) (by decide +kernel))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRVB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun hp0 s hpc hobl
  have hec := piece_ecall hrun hp0 s hobl (by simp [hr, headRVB])
  have hn : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRVB_keeps .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i
    (lowerG i)
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i (by omega)
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 256 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRVB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA, htable]
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hp24 := padHeader_at hc h0 ⟨hi.1, by omega⟩ hF
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 ⟨hi.1, by omega⟩ hF
  have hvb := c.vAt_bound i
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := c.bufferSlot_props (c.i0 + j) (by omega)
    have hgap := c.block_gap_buffer i (c.i0 + j) (by omega) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega)]; exact hp24
  · rw [Result.toState_getReg]; simp only [hr, headRVB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRVB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    by_cases h6 : c.dig i = 6
    · simp only [h6, if_true, E.eval]
      rw [c.outSlot_ne i hi0]
      exact c.bufferE_eval h4 i
    · simp only [h6, if_false]
      rw [addC_eval]; exact c.oAt_eval hc i (by omega) _ a0e
  · rw [Result.toState_pc, hrp]; simp only [hr, headRVB, E.eval]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem land_mask (n k : Nat) (hk : k ≤ 9) :
    n &&& (512 * (2 ^ k - 1)) = 512 * (n / 512 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (512 : Nat) = 2 ^ 9 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h9 : 9 ≤ j
  · simp only [h9, decide_true, Bool.true_and, show j - 9 + 9 = j by omega]
    by_cases hj : j - 9 < k
    · simp [hj]
    · simp [hj]
  · simp [h9]
theorem even_andNot1' (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]
theorem tab_target (a base b off : Nat) (h : off ≤ base) (ha : a + base + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 base + (BitVec.ofNat 64 b - BitVec.ofNat 64 off) =
      BitVec.ofNat 64 (a + (base - off) + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem field_shl (W s k : Nat) (hs : s ≤ 9) (hk : k ≤ 9) :
    W * 2 ^ s % 2 ^ 64 / 512 % 2 ^ k = W / 2 ^ (9 - s) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, show (512 : Nat) = 2 ^ 9 by norm_num,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < k
  · simp only [hj, decide_true, Bool.true_and, show j + 9 < 64 by omega, show s ≤ j + 9 by omega]
    rw [show j + 9 - s = j + (9 - s) by omega]
  · simp [hj]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem dig8_shift (X t' m : Nat) : X / 8 ^ (3 * t' + m) % 8 = X / 2 ^ (9 * t') / 8 ^ m % 8 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add, show (8 : Nat) ^ (3 * t') = 2 ^ (9 * t') by
    rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul]; ring_nf]
theorem kOf_eq (c : LCtx) (t : Nat) (ht : t < 14) :
    c.kOf t = (if t < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * (t % 7)) % 512 := by
  unfold kOf dig
  by_cases h7 : t < 7
  · simp only [h7, if_true, show 3 * t < 21 by omega, show 3 * t + 1 < 21 by omega, show 3 * t + 2 < 21 by omega]
    rw [show t % 7 = t by omega]
    have e0 : c.d0.toNat / 8 ^ (3 * t) % 8 = c.d0.toNat / 2 ^ (9 * t) % 8 := by
      have := dig8_shift c.d0.toNat t 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d0.toNat / 2 ^ (9 * t) = Y
    norm_num
    omega
  · simp only [h7, if_false, show ¬ 3 * t < 21 by omega, show ¬ 3 * t + 1 < 21 by omega,
      show ¬ 3 * t + 2 < 21 by omega, show 3 * t < 42 by omega, show 3 * t + 1 < 42 by omega,
      show 3 * t + 2 < 42 by omega, if_true]
    rw [show t % 7 = t - 7 by omega, show 3 * t + 1 - 21 = 3 * (t - 7) + 1 by omega,
      show 3 * t + 2 - 21 = 3 * (t - 7) + 2 by omega, show 3 * t - 21 = 3 * (t - 7) by omega]
    have e0 : c.d1.toNat / 8 ^ (3 * (t - 7)) % 8 = c.d1.toNat / 2 ^ (9 * (t - 7)) % 8 := by
      have := dig8_shift c.d1.toNat (t - 7) 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d1.toNat / 2 ^ (9 * (t - 7)) = Y
    norm_num
    omega
theorem kOf_lt (c : LCtx) (t : Nat) (ht : t < 14) : c.kOf t < 512 := by
  rw [c.kOf_eq t ht]; exact Nat.mod_lt _ (by norm_num)
theorem x_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (t : Nat) (ht : t < 13) (hi : c.i0 ≤ 3 * t + 2) (hp : c.tX (3 * t + 2) < 257214)
    (hrun : vrun (c.tX (3 * t + 2)) 5 = some (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7))
      (if t=0 ∨ t=7 then .x27 else .x2)
      (BitVec.ofNat 64 (lowerImm (t+1)))))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3 * t + 2) acc s) :
    ∃ u, Steps vimage s (if 9 * ((t + 1) % 7) = 9 then 2 else 3)
      (if 9 * ((t + 1) % 7) = 9 then 2 else 3) u ∧ c.ChainIn s0 (3 * t + 3) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  set r := xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7))
    (if t=0 ∨ t=7 then .x27 else .x2)
    (BitVec.ofNat 64 (lowerImm (t+1))) with hr
  have hst := piece_steps hrun hp s hpc' (by simp [hr, xJ])
  have hkeep := xJ_keeps (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7))
    (if t=0 ∨ t=7 then .x27 else .x2)
    (BitVec.ofNat 64 (lowerImm (t+1)))
  have hW : s.getReg (if t + 1 < 7 then .x16 else .x17) = (if t + 1 < 7 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide +kernel)
    · exact kr .x17 c.d1 (by simp [known]) (by decide +kernel)
  have h2 : s.getReg (if t=0 ∨ t=7 then .x27 else .x2) =
      BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*(2^9-1)) := by
    have h6 := kr .x27 0x3fe00 (by simp [known]) (by decide +kernel)
    have h2 := kr .x2 0x7fc00 (by simp [known]) (by decide +kernel)
    split_ifs <;> simp_all <;> omega
  have hm := shE_mask_new s _ _ hW (9 * ((t + 1) % 7)) 9 (by omega) (le_refl _)
  have himm := lowerImm_even (t+1)
  have hk1 := c.kOf_lt (t + 1) (by omega)
  have hrow : ((if t + 1 < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * ((t + 1) % 7)) % 2 ^ 9) = c.kOf (t + 1) := by
    rw [c.kOf_eq (t + 1) (by omega)]; rfl
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr bufferWr at h ⊢; rcases h with h | h | h
      · exact Or.inl h
      · right; left; obtain ⟨j, h1, h2, h3⟩ := h; exact ⟨j, h1, by omega, h3⟩
      · right; right; exact ⟨h.1, by omega, h.2.2⟩), hS⟩, by omega, h25, ?_⟩⟩
  rw [Result.toState_pc]
  simp only [hr, xJ, E.eval, BinOp.eval]
  rw [h2]
  have e : ((shE (if t + 1 < 7 then Reg.x16 else Reg.x17) (9 * ((t + 1) % 7))).eval s &&&
      BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*(2^9-1))) =
      BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*c.kOf (t+1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [hm,hrow,BitVec.toNat_ofNat]
    symm; apply Nat.mod_eq_of_lt; split_ifs <;> omega
  rw [e, ofNat_add_ofNat, even_andNot1' _ (by split_ifs <;> omega)]
  have e2 : BitVec.ofNat 64 ((if 9*((t+1)%7)=9 then 512 else 1024)*c.kOf (t+1) +
      (lowerImm (t+1))) = pcOf (entW (t+1) (c.kOf (t+1))) := by
    rw [entW_address _ _ (by omega) hk1]
    congr 1
    split_ifs <;> omega
  rw [e2]
  unfold startPc
  rw [if_neg (by omega), if_pos (by omega), show (3*t+3)/3=t+1 by omega]
theorem xbfJ_keeps (w : Reg) (imm : Word) : Keeps (xbfJ w imm) [.x14] := by
  intro x hx
  simp only [xbfJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem srl54_spare (W : Word) (hW : 2 ^ 63 ≤ W.toNat) : W.toNat / 2 ^ 54 = 512 + W.toNat / 2 ^ 54 % 512 := by
  have := W.isLt
  omega
theorem xbf_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (t : Nat) (ht : t = 5 ∨ t = 12) (hi : c.i0 ≤ 3 * t + 2) (hp : c.tX (3 * t + 2) < 257214)
    (hrun : vrun (c.tX (3 * t + 2)) 4 = some (xbfJ (if t + 1 < 7 then .x16 else .x17)
      (BitVec.ofNat 64 (lowerImm (t+1)))))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3 * t + 2) acc s) :
    ∃ u, Steps vimage s 3 3 u ∧ c.ChainIn s0 (3 * t + 3) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  set r := xbfJ (if t + 1 < 7 then .x16 else .x17) (BitVec.ofNat 64 (lowerImm (t+1))) with hr
  have hst := piece_steps hrun hp s hpc' (by simp [hr, xbfJ])
  have hkeep := xbfJ_keeps (if t + 1 < 7 then .x16 else .x17) (BitVec.ofNat 64 (lowerImm (t+1)))
  have hW : s.getReg (if t + 1 < 7 then .x16 else .x17) = (if t + 1 < 7 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide +kernel)
    · exact kr .x17 c.d1 (by simp [known]) (by decide +kernel)
  have h2 := kr .x2 0x7fc00 (by simp [known]) (by decide +kernel)
  have himm := lowerImm_even (t+1)
  have hk1 := c.kOf_lt (t + 1) (by omega)
  have hrow : (if t + 1 < 7 then c.d0 else c.d1).toNat / 2^54 %512 = c.kOf (t+1) := by
    rw [c.kOf_eq (t+1) (by omega)]; rcases ht with rfl|rfl <;> rfl
  have hm := shE_mask_new s _ _ hW 54 9 (by omega) (le_refl _)
  have e : ((if t+1<7 then c.d0 else c.d1) >>> (44 : Nat)) &&& (0x7fc00 : Word) = BitVec.ofNat 64 (1024*c.kOf (t+1)) := by
    apply BitVec.eq_of_toNat_eq
    have hm' : (((if t+1<7 then c.d0 else c.d1) >>> (44 : Nat)) &&& (0x7fc00 : Word)).toNat =
        1024*((if t+1<7 then c.d0 else c.d1).toNat/2^54%512) := by
      simpa [shE, E.eval, BinOp.eval, hW] using hm
    rw [hm',hrow,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1024*c.kOf (t+1)<2^64 by omega)]
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr bufferWr at h ⊢; rcases h with h | h | h
      · exact Or.inl h
      · right; left; obtain ⟨j, h1, h2, h3⟩ := h; exact ⟨j, h1, by omega, h3⟩
      · right; right; exact ⟨h.1, by omega, h.2.2⟩), hS⟩, by omega, h25, ?_⟩⟩
  rw [Result.toState_pc]
  simp only [hr,xbfJ,E.eval,BinOp.eval,hW,h2]
  rw [show ((44:Word).toNat%64)=44 from rfl,e,ofNat_add_ofNat,even_andNot1' _ (by omega)]
  have e2 : BitVec.ofNat 64 (1024*c.kOf (t+1)+(lowerImm (t+1))) = pcOf (entW (t+1) (c.kOf (t+1))) := by
    rw [entW_address _ _ (by omega) hk1]
    rcases ht with rfl|rfl <;> simp <;> congr 1 <;> omega
  rw [e2]
  unfold startPc
  rw [if_neg (by omega),if_pos (by omega),show (3*t+3)/3=t+1 by omega]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
def ChainOut (c : LCtx) (s0 : MachineState) (n : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr n) acc s ∧ acc.length = n - c.i0 ∧ s.pc = pcOf c.ret
theorem next_inline (c : LCtx) (s0 : MachineState) (i : Nat) (hi : i < 42) (h2 : i % 3 ≠ 2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) : c.ChainIn s0 (i + 1) acc s := by
  obtain ⟨hB, hlen, h25, hpc⟩ := hs
  refine ⟨hB, hlen.trans (by omega), h25, ?_⟩
  rw [hpc]
  simp only [endPc, startPc, show i ≠ 42 by omega, show i + 1 ≠ 42 by omega, if_false]
  by_cases h0 : i % 3 = 0
  · rw [if_pos h0, if_neg (show (i + 1) % 3 ≠ 0 by omega), if_pos (show (i + 1) % 3 = 1 by omega)]
    unfold tB; rw [show (i + 1) / 3 = i / 3 by omega]
    simp only [Nat.add_sub_cancel]
    simp only [show (1 < i+1) ↔ (0 < i) by omega]
  · rw [if_neg h0, if_pos (show i % 3 = 1 by omega), if_neg (show (i + 1) % 3 ≠ 0 by omega),
      if_neg (show (i + 1) % 3 ≠ 1 by omega)]
    unfold tC; rw [show (i + 1) / 3 = i / 3 by omega]
theorem x13_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (_hi : c.i0 ≤ 41) (hp : c.tX 41 < 257214) (hrun : vrun (c.tX 41) 4 = some ctabX)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 41 acc s) :
    ∃ u, Steps vimage s 3 3 u ∧ c.ChainIn s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX 41) := by rw [hpc]; unfold endPc; simp
  have hst := piece_steps hrun hp s hpc' (by simp [ctabX])
  have h15 : s.getReg .x2 = BitVec.ofNat 64 0x7fc00 := kr .x2 0x7fc00 (by simp [known]) (by decide +kernel)
  have h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 c.ck := kr .x29 _ (by simp [known]) (by decide +kernel)
  have hck := hc.2.2.2.2.2.2.1
  refine ⟨ctabX.toState s, hst, ⟨⟨fun x hx => (ctabX_keeps.reg s (not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr bufferWr at h ⊢; rcases h with h | h | h
      · exact Or.inl h
      · right; left; obtain ⟨j, h1, h2, h3⟩ := h; exact ⟨j, h1, by omega, h3⟩
      · right; right; exact ⟨h.1, by omega, h.2.2⟩), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [ctabX, E.eval, BinOp.eval, h15, h29]
    have e2 : BitVec.ofNat 64 0x7fc00 - (7#64 - BitVec.ofNat 64 c.ck) <<< ((12 : Word).toNat % 64) + (1844 : Word) =
        BitVec.ofNat 64 (0x1000 + 4 * ckSlot c.ck) := by
      have hk : c.ck ≤ 8 := hck
      generalize c.ck = k at hk ⊢
      unfold ckSlot
      interval_cases k <;> decide +kernel
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc; simp
theorem endPc_42_lt (c : LCtx) (hc : c.ok) : c.endPc 42 < 257214 := by
  have := hc.2.2.2.2.2.2.1
  unfold endPc ckSlot partLen; simp only [if_true]; split_ifs <;> omega
theorem ckend_out (c : LCtx) (hc : c.ok) {s0 : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 42 acc s) : c.ChainOut s0 43 acc s := by
  obtain ⟨hB, hlen, -, hpc⟩ := hs
  refine ⟨hB, hlen, ?_⟩
  rw [hpc, hc.2.2.2.2.2.2.2.1]
  unfold endPc; simp
end LCtx
end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M.LCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

theorem buffer_skip_base (c : LCtx) (hc : c.ok) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hs : c.bufferSafe i)
    (acc : List Digest) (hlen : acc.length = i-c.i0) (hB : c.Base s0 (c.Wr i) acc s) :
    c.Base s0 (c.Wr (i+1)) (acc ++ [c.bufferVal i]) s := by
  obtain ⟨hR,hF,hA⟩ := hB
  refine ⟨hR, hF.mono (fun A _ h => c.bufferWr_mono i A h), ?_⟩
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  by_cases hl : j < acc.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD]
    exact hA j hl
  · have hj' : j = acc.length := by omega
    subst hj'
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
      show c.i0+acc.length=i by omega]
    exact bufferVal_at hc h0.2 hi hs c.bufferBound_slot hF

theorem buffer_skip_inline (c : LCtx) (hc : c.ok) {s0 s : MachineState} (h0 : c.Orig0 s0)
    (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hSafe : c.bufferSafe i)
    (hpc : c.startPc i = c.endPc i) (acc : List Digest) (hs : c.ChainIn s0 i acc s) :
    c.EndInv s0 i (acc ++ [c.bufferVal i]) s := by
  obtain ⟨hB,hlen,h25,hp⟩ := hs
  refine ⟨c.buffer_skip_base hc s0 s h0 i hi hSafe acc hlen hB, ?_, h25, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · rwa [← hpc]

theorem buffer_skip_jump (c : LCtx) (hc : c.ok) {s0 s : MachineState} (h0 : c.Orig0 s0)
    (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hSafe : c.bufferSafe i)
    (hp : c.startPc i < 257214) (hrun : vrun (c.startPc i) 1 = some (skipJB (c.endPc i)))
    (acc : List Digest) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 1 1 t ∧ c.EndInv s0 i (acc ++ [c.bufferVal i]) t := by
  obtain ⟨hB,hlen,h25,hpc⟩ := hs
  set r := skipJB (c.endPc i)
  have hst := piece_steps hrun hp s hpc (by intro o ho; exact (List.not_mem_nil ho).elim)
  have hmem : ∀ A, (r.toState s).getMem A = s.getMem A := by
    intro A
    rw [Result.toState_getMem]
    rfl
  have hreg : ∀ x, (r.toState s).getReg x = s.getReg x := by
    intro x
    rw [Result.toState_getReg]
    exact RegFile.init_get_eval s x
  have hb := c.buffer_skip_base hc s0 s h0 i hi hSafe acc hlen hB
  refine ⟨r.toState s, hst, ⟨fun x hx => (hreg x).trans (hb.1 x hx), ?_, ?_⟩, ?_, h25, ?_⟩
  · intro A hA hn; rw [hmem]; exact hb.2.1 A hA hn
  · intro j hj; rcases hb.2.2 j hj with ⟨h1,h2⟩; exact ⟨(hmem _).trans h1,(hmem _).trans h2⟩
  · simp only [List.length_append,List.length_singleton]; omega
  · rw [Result.toState_pc]; rfl
end SigGolfCandidate.T3M.LCtx
