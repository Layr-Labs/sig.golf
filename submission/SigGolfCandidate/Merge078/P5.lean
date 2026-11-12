import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge076
import SigGolfCandidate.Merge077
import SigGolfCandidate.Merge078.P1

set_option debug.skipKernelTC true
set_option linter.all false

-- ==== merged from T3M_Expand_Layers ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chainCount height)
open SigGolfCandidate.T3M.Search (NODE NOUT ENC)
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chain chainInput shortHash pad64 zero16 header chainCount height
  width maxDigit route recoverLayer leafHash nodeHash)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option maxHeartbeats 2000000
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open OracleComp SigGolfCandidate.T3
open ClaudeWCT
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost)
open ClaudeWCT
set_option autoImplicit false
def HalfAt (t : MachineState) (D k : Nat) (v : BitVec 32) : Prop :=
  (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = v
def HalfFrame (s t : MachineState) (n : Nat) : Prop :=
  ∀ D k, (D = 0x3ce8 ∨ D = 0x4968 ∨ D = 0x55a8 ∨ D = 0x820 ∨ D = 0x810 ∨ D = 0x818) → k < 2 → (∀ lay : Layer, lay.val < n → ¬ (lD lay = D ∧ lk lay = k)) →
    (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = (s.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32
def lRegs : List Reg :=
  [.x1, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
    .x25, .x26, .x27, .x28, .x29, .x30, .x31]
def LayerOut (t : MachineState) (sig : WCT9.Signature) (index : Nat) (lay : Layer) (c : BitVec 32) : Prop :=
  HalfAt t (lD lay) (lk lay) c ∧ (∀ i < chainCount lay, DigAt t (lWC lay - 64 * i + 48) (lval (WCT9.toT3Signature sig) lay i)) ∧
    (∀ j < height lay, DigAt t (lWM lay - 64 * j + sideOff (route index lay).1 j) (lpath (WCT9.toT3Signature sig) lay j))
theorem ltable (lay : Layer) :
    0x7000 ≤ lP lay ∧ lP lay + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616 ∧ lP lay % 8 = 0 ∧
    lWC lay % 8 = 0 ∧ lWM lay % 8 = 0 ∧ 0x800 + 64 * (height lay - 1) ≤ lWM lay ∧
    lWM lay + 64 + 64 * (chainCount lay - 1) ≤ lWC lay ∧ lWC lay + 64 ≤ 0x7000 ∧ lD lay + 8 ≤ 0x7000 ∧
    0x810 ≤ lD lay ∧ lk lay < 2 := by
  fin_cases lay <;> decide
theorem fin_ofNat_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := by
  simp [Fin.ofNat, Nat.mod_eq_of_lt hn]
theorem replaceWord32_get (w : BitVec 64) (k : Nat) (hk : k < 2) (v : BitVec 32) :
    (replaceWord32 w k v).extractLsb' (32 * k) 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : Nat.testBit 4294967295 i = true := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
  interval_cases k <;>
  · simp only [replaceWord32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    simp (config := { decide := true }) [show i < 64 by omega, show 32 + i < 64 by omega, hi, hm]
theorem replaceWord32_other (w : BitVec 64) (k k' : Nat) (hk : k < 2) (hk' : k' < 2) (hne : k ≠ k')
    (v : BitVec 32) : (replaceWord32 w k v).extractLsb' (32 * k') 32 = w.extractLsb' (32 * k') 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : Nat.testBit 4294967295 i = true := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
  have hm2 : Nat.testBit 4294967295 (32 + i) = false := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp
  interval_cases k <;> interval_cases k' <;> simp at hne <;>
  · simp only [replaceWord32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    simp (config := { decide := true }) [show i < 64 by omega, show 32 + i < 64 by omega, hi, hm, hm2]
theorem rlWit_range {lay : Layer} {leaf A : Nat} (h : RlWit lay leaf (lWC lay) (lWM lay) A) :
    lWM lay - 64 * (height lay - 1) ≤ A ∧ A + 8 ≤ lWC lay + 64 := by
  have htab := ltable lay
  rcases h with ⟨i, hi, h | h⟩ | ⟨j, hj, h | h⟩ <;>
    first | omega | (have := sideOff_le leaf j; omega)
theorem ltable_disj (lay lay' : Layer) (h : lay ≠ lay') :
    lWC lay + 64 ≤ lWM lay' - 64 * (height lay' - 1) ∨ lWC lay' + 64 ≤ lWM lay - 64 * (height lay - 1) := by
  fin_cases lay <;> fin_cases lay' <;> simp_all <;> decide
theorem lhalf_inj (lay lay' : Layer) (h1 : lD lay = lD lay') (h2 : lk lay = lk lay') : lay = lay' := by
  fin_cases lay <;> fin_cases lay' <;> simp_all [lD, lk]
theorem ltable_lo (lay : Layer) : 0x2c48 ≤ lWM lay - 64 * (height lay - 1) := by
  fin_cases lay <;> decide
theorem counter_ne_wit (counter lay : Layer) (leaf : Nat) :
    ¬ RlWit lay leaf (lWC lay) (lWM lay) (lD counter) := by
  intro h
  unfold RlWit at h
  rcases h with ⟨i, hi, h⟩ | ⟨j, hj, h⟩
  · fin_cases counter <;> fin_cases lay <;> norm_num [lD, lWC, chainCount] at * <;> omega
  · unfold sideOff at h
    fin_cases counter <;> fin_cases lay <;> norm_num [lD, lWM, height] at * <;> split_ifs at h <;> omega
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route chainCount height)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost)
open ClaudeWCT
set_option autoImplicit false
section step
variable {sk : BitVec 256}
end step
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand
abbrev HalfFrame := BC.HalfFrame
abbrev lRegs := BC.lRegs
abbrev LayerOut := BC.LayerOut
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Expand.BC
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ComposeBack ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests)
set_option linter.unusedSimpArgs false
section init
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312)
include hd
end init
sym_block zblk := symRun { noAlias := true } zeroBlk (pcOf 42719) 20
theorem zero_spec {im : Image} (hZ : CodeAt im (pcOf 42719) zeroBlk) (s : MachineState) (hpc : s.pc = pcOf 42719) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 30 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      (∀ A, A < 2 ^ 64 → (A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) → t.getMem (BitVec.ofNat 64 A) = 0) ∧
      RegsExcept s t [.x19, .x29] ∧
      Frame s t (fun A => A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) := by
  refine ⟨_, symRun_sound zblk hZ s hpc (by simp [zblk.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, zblk.res, E.eval]
  · simp [zblk.res, rv_simp]
  · intro A hA h
    simp only [Result.toState_getMem, zblk.res]
    t3n []
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · ex_regs zblk.res
  · intro A hA hn
    simp only [Result.toState_getMem, zblk.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
-- [h2 lane] removed front_pre30 (record word 0); H2Front.front_pre30' is the H2 version
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput Layer LayerSignature height chainCount)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit sideOff height_le)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
theorem readWords_blocks (t : MachineState) : ∀ (bs : List (List Word)) (A : Nat),
    (∀ b ∈ bs, b.length = 8) → (∀ k < bs.length, t.readWords (BitVec.ofNat 64 (A + 64 * k)) 8 = bs.getD k []) →
    t.readWords (BitVec.ofNat 64 A) (8 * bs.length) = bs.flatten
  | [], _, _, _ => rfl
  | b :: bs, A, hl, h => by
    rw [List.length_cons, show 8 * (bs.length + 1) = 8 + 8 * bs.length by ring, readWords_add,
      show A + 8 * 8 = A + 64 by ring, List.flatten_cons]
    congr 1
    · simpa using h 0 (by simp)
    · refine readWords_blocks t bs (A + 64) (fun x hx => hl x (by simp [hx])) (fun k hk => ?_)
      have := h (k + 1) (by simp; omega)
      rw [show A + 64 * (k + 1) = A + 64 + 64 * k by ring] at this
      simpa using this
theorem wordsOf_flatMap64 {α : Type} (f : α → List UInt8) (hf : ∀ x, (f x).length = 64) :
    ∀ (xs : List α), wordsOf (xs.flatMap f) = xs.flatMap (fun x => wordsOf (f x))
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by rw [hf]), wordsOf_flatMap64 f hf xs]
theorem wordsOf_dig_zeros48 (d : Digest) :
    wordsOf (bytesLE 16 d ++ SigGolfCandidate.T3M.zeros 48) =
      [d.extractLsb' 0 64, d.extractLsb' 64 64, 0, 0, 0, 0, 0, 0] := by
  rw [wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16,
    show SigGolfCandidate.T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl
theorem wordsOf_zeros48_dig (d : Digest) :
    wordsOf (SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 d) =
      [0, 0, 0, 0, 0, 0, d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by rfl), wordsOf_bytesLE16,
    show SigGolfCandidate.T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl
def lBase (lay : Layer) : Nat := ![0x2c48, 0x3CC8, 0x4948, 0x5588] lay
/-- T51: the top staging region keeps #938's 54 chain blocks (`chainSlotsV6`): chain 0's block is the last of 54. -/
theorem lBase_eq (lay : Layer) : lWM lay = lBase lay + 64 * (height lay - 1) ∧
    lWC lay = lBase lay + 64 * height lay + 64 * (chainSlotsV6 lay - 1) := by
  fin_cases lay <;> decide

def mkWords (leaf j : Nat) (p : Digest) : List Word :=
  if leaf / 2 ^ j % 2 = 1 then [p.extractLsb' 0 64, p.extractLsb' 64 64, 0, 0, 0, 0, 0, 0]
  else [0, 0, 0, 0, 0, 0, p.extractLsb' 0 64, p.extractLsb' 64 64]
def chWords (v : Digest) : List Word := [0, 0, 0, 0, 0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64]
/-- T51: the 64-byte blocks of a staging region (`layerBytesV6`): the path blocks, the zero blocks of #938's top
chains 51..53 (`chainSlotsV6 lay - chainCount lay` of them, none below the top), then the chain blocks. -/
def layBlocks (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List (List Word) :=
  (List.finRange (height lay)).reverse.map (fun j => mkWords leaf j.val (ls.path j)) ++
    (List.replicate (chainSlotsV6 lay - chainCount lay) (chWords 0) ++
      (List.finRange (chainCount lay)).reverse.map (fun i => chWords (ls.values i)))
theorem length_flatMap_const {α : Type} (f : α → List UInt8) (c : Nat) (hf : ∀ x, (f x).length = c) :
    ∀ (xs : List α), (xs.flatMap f).length = c * xs.length
  | [] => by simp
  | x :: xs => by rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f c hf xs]; simp; ring
theorem flatMap_eq_flatten {α β : Type} (f : α → List β) (g : α → List β) (h : ∀ x, f x = g x) :
    ∀ (xs : List α), xs.flatMap f = (xs.map g).flatten
  | [] => rfl
  | x :: xs => by rw [List.flatMap_cons, List.map_cons, List.flatten_cons, h, flatMap_eq_flatten f g h xs]
theorem layerBytes_words' (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    wordsOf (SigGolfCandidate.T3M.layerBytes lay leaf ls) =
      ((List.finRange (height lay)).reverse.map (fun j => mkWords leaf j.val (ls.path j))).flatten ++
        ((List.finRange (chainCount lay)).reverse.map (fun i => chWords (ls.values i))).flatten := by
  unfold SigGolfCandidate.T3M.layerBytes
  have hm : ∀ j : Fin (height lay), ((if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++
      SigGolfCandidate.T3M.zeros 48 else SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.path j))).length = 64 := by
    intro j; split_ifs <;> simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  have hc : ∀ i : Fin (chainCount lay), (SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.values i)).length = 64 := by
    intro i; simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  rw [wordsOf_append _ _ (by rw [length_flatMap_const _ 64 hm]; omega),
    wordsOf_flatMap64 _ hm, wordsOf_flatMap64 _ hc]
  rw [flatMap_eq_flatten _ (fun j => mkWords leaf j.val (ls.path j)) (fun j => by
      unfold mkWords
      split_ifs
      · exact wordsOf_dig_zeros48 _
      · exact wordsOf_zeros48_dig _),
    flatMap_eq_flatten _ (fun i => chWords (ls.values i)) (fun i => wordsOf_zeros48_dig _)]
theorem mk_block (t : MachineState) (B leaf j : Nat) (p : Digest) (hp : DigAt t (B + sideOff leaf j) p)
    (hz : ∀ r < 8, 8 * r ≠ sideOff leaf j → 8 * r ≠ sideOff leaf j + 8 →
      t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = mkWords leaf j p := by
  rw [readWords_eight]
  unfold mkWords
  unfold sideOff at hp hz
  split_ifs at hp hz ⊢ with hb
  · simp only [Nat.add_zero] at hp
    rw [hp.1, hp.2, show B + 16 = B + 8 * 2 by ring, hz 2 (by omega) (by omega) (by omega),
      show B + 24 = B + 8 * 3 by ring, hz 3 (by omega) (by omega) (by omega),
      show B + 32 = B + 8 * 4 by ring, hz 4 (by omega) (by omega) (by omega),
      show B + 40 = B + 8 * 5 by ring, hz 5 (by omega) (by omega) (by omega),
      show B + 48 = B + 8 * 6 by ring, hz 6 (by omega) (by omega) (by omega),
      show B + 56 = B + 8 * 7 by ring, hz 7 (by omega) (by omega) (by omega)]
  · have h0 := hz 0 (by omega) (by omega) (by omega)
    have h1 := hz 1 (by omega) (by omega) (by omega)
    have h2 := hz 2 (by omega) (by omega) (by omega)
    have h3 := hz 3 (by omega) (by omega) (by omega)
    have h4 := hz 4 (by omega) (by omega) (by omega)
    have h5 := hz 5 (by omega) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
      show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hp.1,
      show B + 56 = B + 48 + 8 by ring, hp.2]
theorem ch_block (t : MachineState) (B : Nat) (v : Digest) (hv : DigAt t (B + 48) v)
    (hz : ∀ r < 6, t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = chWords v := by
  rw [readWords_eight]
  have h0 := hz 0 (by omega); have h1 := hz 1 (by omega); have h2 := hz 2 (by omega)
  have h3 := hz 3 (by omega); have h4 := hz 4 (by omega); have h5 := hz 5 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
    show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hv.1,
    show B + 56 = B + 48 + 8 by ring, hv.2]
  rfl
theorem getD_rev_finRange_map {β : Type} (n : Nat) (f : Fin n → β) (d : β) (k : Nat) (hk : k < n) :
    ((List.finRange n).reverse.map f).getD k d = f ⟨n - 1 - k, by omega⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by simp; omega)]
  simp [show n - 1 - k < n by omega]
/-- T51: inserting the 192 zero bytes after the 768-byte path area inserts 24 zero words. -/
theorem wordsOf_padTop (L : List UInt8) (h8 : L.length % 8 = 0) (h : 768 ≤ L.length) :
    wordsOf (L.take 768 ++ SigGolfCandidate.T3M.zeros 192 ++ L.drop 768) =
      (wordsOf L).take 96 ++ List.replicate 24 0 ++ (wordsOf L).drop 96 := by
  have htl : (L.take 768).length = 768 := by simp; omega
  have hz : (SigGolfCandidate.T3M.zeros 192 : List UInt8).length = 192 := List.length_replicate ..
  have hR : wordsOf L = wordsOf (L.take 768) ++ wordsOf (L.drop 768) := by
    conv_lhs => rw [← List.take_append_drop 768 L]
    exact wordsOf_append _ _ (by rw [htl])
  have hlt : (wordsOf (L.take 768)).length = 96 := length_wordsOf 96 _ (by rw [htl])
  rw [hR, List.take_left' hlt, List.drop_left' hlt,
    wordsOf_append _ _ (by rw [List.length_append, htl, hz]), wordsOf_append _ _ (by rw [htl]),
    show SigGolfCandidate.T3M.zeros 192 = List.replicate (8 * 24) 0 from rfl, wordsOf_replicate_zero]
theorem mkWords_length (leaf j : Nat) (p : Digest) : (mkWords leaf j p).length = 8 := by
  unfold mkWords; split_ifs <;> rfl
theorem layerBytesV6_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    wordsOf (layerBytesV6 lay leaf ls) = (layBlocks lay leaf ls).flatten := by
  unfold layerBytesV6 layBlocks
  split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    have hL := SigGolfCandidate.T3M.layerBytes_length 0 leaf ls
    have h63 : 64 * (height (0 : Layer) + chainCount (0 : Layer)) = 4032 := rfl
    rw [wordsOf_padTop _ (by rw [hL, h63]) (by rw [hL, h63]; omega), layerBytes_words']
    have hMf : ((List.map (fun j : Fin (height (0 : Layer)) => mkWords leaf j.val (ls.path j))
        (List.finRange (height (0 : Layer))).reverse).flatten).length = 96 := by
      rw [List.length_flatten, List.map_map]
      simp only [Function.comp_def, mkWords_length]
      simp
      rfl
    rw [List.take_left' hMf, List.drop_left' hMf, List.flatten_append, List.flatten_append]
    have hz : (List.replicate (chainSlotsV6 (0 : Layer) - chainCount (0 : Layer)) (chWords 0)).flatten =
        List.replicate 24 (0 : Word) := by decide
    rw [hz, List.append_assoc]
  · rename_i h
    rw [layerBytes_words', chainSlotsV6_lower lay h, Nat.sub_self, List.replicate_zero, List.nil_append,
      List.flatten_append]
theorem layer_words (t : MachineState) (lay : Layer) (leaf : Nat) (ls : LayerSignature lay)
    (hv : ∀ i (h : i < chainCount lay), DigAt t (lWC lay - 64 * i + 48) (ls.values ⟨i, h⟩))
    (hp : ∀ j (h : j < height lay), DigAt t (lWM lay - 64 * j + sideOff leaf j) (ls.path ⟨j, h⟩))
    (hz : ∀ A, lBase lay ≤ A → A < lBase lay + 64 * (height lay + chainSlotsV6 lay) →
      ¬ RlWit lay leaf (lWC lay) (lWM lay) A → t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainSlotsV6 lay)) =
      wordsOf (layerBytesV6 lay leaf ls) := by
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  have hH := height_le lay
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hS := chainSlotsV6_ge lay
  have hso : ∀ j, sideOff leaf j = 0 ∨ sideOff leaf j = 48 := fun j => by unfold sideOff; split_ifs <;> simp
  rw [layerBytesV6_words]
  have hlen : (layBlocks lay leaf ls).length = height lay + chainSlotsV6 lay := by
    simp [layBlocks]; omega
  have hl8 : ∀ b ∈ layBlocks lay leaf ls, b.length = 8 := by
    intro b hb
    simp only [layBlocks, List.mem_append, List.mem_map, List.mem_replicate] at hb
    rcases hb with ⟨j, _, rfl⟩ | ⟨_, rfl⟩ | ⟨i, _, rfl⟩
    · exact mkWords_length _ _ _
    · rfl
    · rfl
  have key := readWords_blocks t (layBlocks lay leaf ls) (lBase lay) hl8 (fun k hk => by
    rw [hlen] at hk
    by_cases hkH : k < height lay
    · rw [layBlocks, List.getD_append _ _ _ _ (by simp; omega), getD_rev_finRange_map _ _ _ _ hkH]
      obtain ⟨j, hj⟩ : ∃ j, j = height lay - 1 - k := ⟨_, rfl⟩
      have hB : lBase lay + 64 * k = lWM lay - 64 * j := by omega
      have e : (⟨height lay - 1 - k, by omega⟩ : Fin (height lay)) = ⟨j, by omega⟩ := Fin.ext hj.symm
      rw [hB, e]
      refine mk_block t _ leaf j _ (hp j (by omega)) (fun r hr h1 h2 => hz _ (by omega) (by omega) ?_)
      rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    · rw [layBlocks, List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_reverse,
        List.length_finRange]
      by_cases hkP : k - height lay < chainSlotsV6 lay - chainCount lay
      · -- T51: a zero block of #938's top chains 51..53
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_replicate,
          if_pos (by omega)]
        simp only [Option.getD_some]
        have hnot : ∀ r < 8, ¬ RlWit lay leaf (lWC lay) (lWM lay) (lBase lay + 64 * k + 8 * r) := by
          intro r hr
          rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
          · omega
          · omega
          · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
          · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
        have z : ∀ r < 8, t.getMem (BitVec.ofNat 64 (lBase lay + 64 * k + 8 * r)) = 0 :=
          fun r hr => hz _ (by omega) (by omega) (hnot r hr)
        refine ch_block t _ 0 ⟨?_, ?_⟩ (fun r hr => z r (by omega))
        · rw [show lBase lay + 64 * k + 48 = lBase lay + 64 * k + 8 * 6 by ring, z 6 (by omega)]; decide
        · rw [show lBase lay + 64 * k + 48 + 8 = lBase lay + 64 * k + 8 * 7 by ring, z 7 (by omega)]; decide
      · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_replicate,
          getD_rev_finRange_map _ _ _ _ (by omega)]
        obtain ⟨i, hi⟩ : ∃ i, i = chainCount lay - 1 - (k - height lay - (chainSlotsV6 lay - chainCount lay)) :=
          ⟨_, rfl⟩
        have hB : lBase lay + 64 * k = lWC lay - 64 * i := by omega
        have e : (⟨chainCount lay - 1 - (k - height lay - (chainSlotsV6 lay - chainCount lay)), by omega⟩ :
            Fin (chainCount lay)) = ⟨i, by omega⟩ := Fin.ext hi.symm
        rw [hB, e]
        refine ch_block t _ _ (hv i (by omega)) (fun r hr => hz _ (by omega) (by omega) ?_)
        rintro (⟨i', hi', h | h⟩ | ⟨j', hj', h | h⟩)
        · omega
        · omega
        · rcases hso j' with h4 | h4 <;> omega
        · rcases hso j' with h4 | h4 <;> omega)
  rw [hlen] at key
  exact key
theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
theorem ctr_words (c : BitVec 32) (m : Nat) :
    wordsOf (bytesLE 4 c ++ SigGolfCandidate.T3M.zeros (4 + 8 * m)) = BitVec.ofNat 64 c.toNat :: List.replicate m 0 := by
  have hc : SigGolfCandidate.T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [SigGolfCandidate.T3M.readLE_append, SigGolfCandidate.T3M.readLE_bytesLE,
      SigGolfCandidate.T3M.readLE_replicate_zero]
    simp
  rw [show SigGolfCandidate.T3M.zeros (4 + 8 * m) = List.replicate 4 0 ++ List.replicate (8 * m) 0 by
      simp [SigGolfCandidate.T3M.zeros, List.replicate_add],
    ← List.append_assoc, wordsOf_append8 _ _ (by simp [bytesLE_length]), hc, wordsOf_replicate_zero]
theorem headerW_words (w : WCT9.Witness) :
    wordsOf (headerBytesV5 w) =
      [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64, BitVec.ofNat 64 w.digestCounter.toNat,
        0, BitVec.ofNat 64 (w.counters 3).toNat, 0, 0, 0] := by
  unfold headerBytesV5
  simp only [List.append_assoc]
  rw [show SigGolfCandidate.T3M.zeros 12 = SigGolfCandidate.T3M.zeros (4 + 8 * 1) from rfl,
    show SigGolfCandidate.T3M.zeros 28 = SigGolfCandidate.T3M.zeros (4 + 8 * 3) from rfl]
  rw [wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, ← List.append_assoc (bytesLE 4 _),
    wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3M.zeros]), ctr_words, ctr_words]
  rfl
def bcWords (leaf j : Nat) (p : Digest) (c : BitVec 32) : List Word :=
  if leaf / 2 ^ j % 2 = 1 then [p.extractLsb' 0 64, p.extractLsb' 64 64, 0, 0, BitVec.ofNat 64 c.toNat, 0, 0, 0]
  else [0, 0, 0, 0, BitVec.ofNat 64 c.toNat, 0, p.extractLsb' 0 64, p.extractLsb' 64 64]
theorem bcTop_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (c : BitVec 32) :
    wordsOf (bcTopBlockV6 lay leaf ls c) = bcWords leaf (height lay - 1) (ls.path (WCT9.topLevel lay)) c := by
  unfold bcTopBlockV6 bcWords
  split_ifs with hb
  · simp only [List.append_assoc]
    rw [show SigGolfCandidate.T3M.zeros 28 = SigGolfCandidate.T3M.zeros (4 + 8 * 3) from rfl]
    rw [wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16,
      wordsOf_append _ _ (by simp [SigGolfCandidate.T3M.zeros]),
      show SigGolfCandidate.T3M.zeros 16 = List.replicate (8 * 2) 0 from rfl, wordsOf_replicate_zero, ctr_words]
    rfl
  · simp only [List.append_assoc]
    rw [show SigGolfCandidate.T3M.zeros 12 = SigGolfCandidate.T3M.zeros (4 + 8 * 1) from rfl]
    rw [wordsOf_append _ _ (by simp [SigGolfCandidate.T3M.zeros]),
      show SigGolfCandidate.T3M.zeros 32 = List.replicate (8 * 4) 0 from rfl, wordsOf_replicate_zero,
      ← List.append_assoc (bytesLE 4 _), wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3M.zeros]), ctr_words,
      wordsOf_bytesLE16]
    rfl
theorem wordsOf_drop64 (l : List UInt8) (h : 64 ≤ l.length) :
    wordsOf (l.drop 64) = (wordsOf l).drop 8 := by
  conv_rhs => rw [← List.take_append_drop 64 l]
  rw [wordsOf_append _ _ (by simp; omega), List.drop_left' (length_wordsOf 8 _ (by simp; omega))]
theorem layerBytesBC_words (lay : Layer) (hl : lay.val ≠ 0) (leaf : Nat) (ls : LayerSignature lay) (c : BitVec 32) :
    wordsOf (layerBytesBCV6 lay leaf ls c) =
      bcWords leaf (height lay - 1) (ls.path (WCT9.topLevel lay)) c ++ (layBlocks lay leaf ls).flatten.drop 8 := by
  unfold layerBytesBCV6
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  rw [wordsOf_append _ _ (by rw [bcTopBlockV6_length]), bcTop_words,
    wordsOf_drop64 _ (by rw [SigGolfCandidate.T3M.layerBytes_length]; omega), ← layerBytesV6_words]
  unfold layerBytesV6
  rw [if_neg hl]
theorem layerBC_words (t : MachineState) (lay : Layer) (hl : lay.val ≠ 0) (leaf : Nat) (ls : LayerSignature lay)
    (c : BitVec 32)
    (hv : ∀ i (h : i < chainCount lay), DigAt t (lWC lay - 64 * i + 48) (ls.values ⟨i, h⟩))
    (hp : ∀ j (h : j < height lay), DigAt t (lWM lay - 64 * j + sideOff leaf j) (ls.path ⟨j, h⟩))
    (hc : t.getMem (BitVec.ofNat 64 (lBase lay + 32)) = BitVec.ofNat 64 c.toNat)
    (hz : ∀ A, lBase lay ≤ A → A < lBase lay + 64 * (height lay + chainCount lay) →
      ¬ RlWit lay leaf (lWC lay) (lWM lay) A → A ≠ lBase lay + 32 → t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
      wordsOf (layerBytesBCV6 lay leaf ls c) := by
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  have hS := chainSlotsV6_lower lay hl
  rw [hS] at hWC
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hlB : lBase lay + 64 * (height lay + chainCount lay) < 2 ^ 64 := by fin_cases lay <;> decide
  have hso : ∀ j, sideOff leaf j = 0 ∨ sideOff leaf j = 48 := fun j => by unfold sideOff; split_ifs <;> simp
  have hRne : ∀ A, RlWit lay leaf (lWC lay) (lWM lay) A → A ≠ lBase lay + 32 := by
    rintro A (⟨i, hi, h | h⟩ | ⟨j, hj, h | h⟩) he
    · omega
    · omega
    · rcases eq_or_ne j (height lay - 1) with rfl | hne
      · rcases hso (height lay - 1) with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases hso j with h4 | h4 <;> rw [h4] at h <;> omega
    · rcases eq_or_ne j (height lay - 1) with rfl | hne
      · rcases hso (height lay - 1) with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases hso j with h4 | h4 <;> rw [h4] at h <;> omega
  set t' := t.setMem (BitVec.ofNat 64 (lBase lay + 32)) 0 with ht'
  have g' : ∀ A, A < 2 ^ 64 → A ≠ lBase lay + 32 → t'.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA hne
    have hne' : BitVec.ofNat 64 A ≠ BitVec.ofNat 64 (lBase lay + 32) := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (show lBase lay + 32 < 2 ^ 64 by omega)]
        at this
      exact hne this
    simp only [ht', MachineState.setMem, MachineState.getMem, beq_iff_eq, hne', if_false]
  have g0 : t'.getMem (BitVec.ofNat 64 (lBase lay + 32)) = 0 := by
    simp only [ht', MachineState.setMem, MachineState.getMem, beq_self_eq_true, if_true]
  have dig' : ∀ A d, A + 16 ≤ 2 ^ 64 → A ≠ lBase lay + 32 → A + 8 ≠ lBase lay + 32 → DigAt t A d → DigAt t' A d :=
    fun A d h1 h2 h3 hd => ⟨(g' A (by omega) h2).trans hd.1, (g' (A + 8) (by omega) h3).trans hd.2⟩
  have hW' := layer_words t' lay leaf ls
    (fun i h => dig' _ _ (by omega) (hRne _ (Or.inl ⟨i, h, Or.inl rfl⟩)) (hRne _ (Or.inl ⟨i, h, Or.inr rfl⟩))
      (hv i h))
    (fun j h => dig' _ _ (by rcases hso j with h4 | h4 <;> omega) (hRne _ (Or.inr ⟨j, h, Or.inl rfl⟩))
      (hRne _ (Or.inr ⟨j, h, Or.inr rfl⟩)) (hp j h))
    (fun A h1 h2 hn => by
      by_cases he : A = lBase lay + 32
      · rw [he, g0]
      · rw [g' A (by omega) he]; exact hz A h1 (by rw [hS] at h2; exact h2) hn he)
  rw [layerBytesV6_words, hS] at hW'
  rw [layerBytesBC_words lay hl]
  have eM : 8 * (height lay + chainCount lay) = 8 + (8 * (height lay + chainCount lay) - 8) := by omega
  rw [eM, readWords_add] at hW' ⊢
  have hlow : t.readWords (BitVec.ofNat 64 (lBase lay + 8 * 8)) (8 * (height lay + chainCount lay) - 8) =
      t'.readWords (BitVec.ofNat 64 (lBase lay + 8 * 8)) (8 * (height lay + chainCount lay) - 8) := by
    have F : Frame t' t (fun A => A = lBase lay + 32) := fun A hA hn => (g' A hA hn).symm
    exact frame_readWords F _ _ (by omega) (fun i _ h => by omega)
  have hl8 : (t'.readWords (BitVec.ofNat 64 (lBase lay)) 8).length = 8 := SigGolfCandidate.Rv.readWords_length _ _ _
  rw [hlow, ← hW', List.drop_left' hl8]
  congr 1
  have hp1 := hp (height lay - 1) (by omega)
  rw [show lWM lay - 64 * (height lay - 1) = lBase lay by omega] at hp1
  have hzt : ∀ r < 8, 8 * r ≠ sideOff leaf (height lay - 1) → 8 * r ≠ sideOff leaf (height lay - 1) + 8 → r ≠ 4 →
      t.getMem (BitVec.ofNat 64 (lBase lay + 8 * r)) = 0 := by
    intro r hr h1 h2 h4
    refine hz _ (by omega) (by omega) ?_ (by omega)
    rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
    · omega
    · omega
    · rcases eq_or_ne j' (height lay - 1) with rfl | hne
      · omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    · rcases eq_or_ne j' (height lay - 1) with rfl | hne
      · omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
  rw [readWords_eight]
  unfold bcWords
  unfold sideOff at hp1 hzt
  have htl : ls.path (WCT9.topLevel lay) = ls.path ⟨height lay - 1, by omega⟩ := rfl
  rw [htl]
  split_ifs at hp1 hzt ⊢ with hb
  · simp only [Nat.add_zero] at hp1
    rw [hp1.1, hp1.2, show lBase lay + 16 = lBase lay + 8 * 2 by ring, hzt 2 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 24 = lBase lay + 8 * 3 by ring, hzt 3 (by omega) (by omega) (by omega) (by omega), hc,
      show lBase lay + 40 = lBase lay + 8 * 5 by ring, hzt 5 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 48 = lBase lay + 8 * 6 by ring, hzt 6 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 56 = lBase lay + 8 * 7 by ring, hzt 7 (by omega) (by omega) (by omega) (by omega)]
  · have h0 := hzt 0 (by omega) (by omega) (by omega) (by omega)
    have h1 := hzt 1 (by omega) (by omega) (by omega) (by omega)
    have h2 := hzt 2 (by omega) (by omega) (by omega) (by omega)
    have h3 := hzt 3 (by omega) (by omega) (by omega) (by omega)
    have h5 := hzt 5 (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    rw [h0, h1, show lBase lay + 16 = lBase lay + 8 * 2 by ring, h2, show lBase lay + 24 = lBase lay + 8 * 3 by ring,
      h3, hc, show lBase lay + 40 = lBase lay + 8 * 5 by ring, h5, hp1.1,
      show lBase lay + 56 = lBase lay + 48 + 8 by ring, hp1.2]
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV)
open SigGolfCandidate.T3M (window window_flatMap_const zeros)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
theorem readWords_ext (t : MachineState) : ∀ (L : List Word) (A : Nat),
    (∀ i, i < L.length → t.getMem (BitVec.ofNat 64 (A + 8 * i)) = L.getD i 0) →
    t.readWords (BitVec.ofNat 64 A) L.length = L
  | [], _, _ => rfl
  | w :: L, A, h => by
    rw [List.length_cons, show L.length + 1 = 1 + L.length by ring, readWords_add, readWords_one]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0, readWords_ext t L (A + 8 * 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show A + 8 * (i + 1) = A + 8 * 1 + 8 * i by ring] at this
      simpa using this)]
    rfl
-- [h2 lane] removed expandN_split: with H2, `expandN` is the searching expander; H2Search.expandN_splitS replaces it
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PrePassInit ====
section

/-! # T51 DEC from the real initial state

E8 (P1): word 0 is `j 60734` (the pre-pass, 185 steps, then `j 54569` = DEC). From `w9init` with the 5,188-byte signature
`b`, the pre-pass rebuilds DEC's T1 layout (`unpackB b`) and DEC writes the expander's inflated slot layout
`SharedCodec.inflatedRead 0 (SharedCodec.digC b)` (332 slots at `0x7000`) and the hint at `0x66000`, zeroes its
temporaries and jumps to word 1 (`dec_init_r6`, at most 2,347 cycles; N7g 2,271). NBZ5R (NB): DEC (NR2) divides
the field `N` by 88 and rejects a non-canonical `N ≥ nCanon = R * 88` at `j 354` (`dec_reject_nc`), which is exactly
a decoded hint `≥ 8464`. -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
-- (open dropped: nothing it names is in this part)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem dropTake_getD {α : Type} (l : List α) (d : α) (a i : Nat) (hi : i < 8) :
    ((l.drop a).take 8).getD i d = l.getD (a + i) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi, List.getElem?_drop]

theorem bytes_getD {n : Nat} (x : Bytes n) (i : Nat) (hi : i < n) :
    (bytes x).getD i 0 = x.extractLsb' (8 * i) 8 := by
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

end ClaudeWCT.W9.Machine.Expand.PrePass
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactLoop ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCoord ====
section

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt planBytes)
open ClaudeWCT.W9.T3M (authBase authRoot)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {c : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (hc : c < 128)
include h19 hc
end eval
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt child_bits)
set_option linter.unusedSimpArgs false
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
theorem find_none {p : Nat → Bool} {L : Nat} (h : (List.range L).find? p = none) (l : Nat) (hl : l < L) :
    p l = false := by
  have := List.find?_eq_none.mp h l (List.mem_range.mpr hl)
  simpa using this
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactRun ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PairCopy ====
section

/-! # Pairing stage 1: the lower-chain pair copy block (expand words 48000 .. 48017)

The witness constructor's lower-layer chain copy (`jal ra,48000` at 42241 / 42414 / 42563, with `a0` = the staging
chain area of the layer (43 blocks of 64 bytes, chain 42 first, value at block offset 48) and `a1` = the final paired
chain area) runs

```
48000  addi a2,zero,21
48001  ld t1,48(a0);  sd t1,88(a1)     -- F chain 2p+2's value  -> pair offset 88
       ld t1,56(a0);  sd t1,96(a1)
       ld t1,112(a0); sd t1,16(a1)     -- G chain 2p+1's value  -> pair offset 16
       ld t1,120(a0); sd t1,24(a1)
       addi a0,a0,128; addi a1,a1,104; addi a2,a2,-1; bne a2,zero,48001
48013  ld t1,48(a0); sd t1,48(a1); ld t1,56(a0); sd t1,56(a1)   -- chain 0's value at offset 48 of its F block
       jalr zero,0(ra)
```

It writes only value words; the pair gaps keep the constructor's zero fill. -/

namespace ClaudeWCT.W9.Machine.Expand.PairCopy
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false

/-- The whole block at 48000 (18 words). -/
def cPCode : List (BitVec 32) := cPC0 ++ cPCL ++ cPCT
theorem cPCode_length : cPCode.length = 18 := rfl
section
variable {im : Image} (hc : Code im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.PairCopy
end
