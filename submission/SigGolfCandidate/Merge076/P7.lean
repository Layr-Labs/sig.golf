import SigGolfCandidate.ExpandLabel
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076.P1

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def remaining (s : MachineState) : Word := s.getReg .x15 - s.getReg .x20 - 1
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
def hpK (lay : T3.Layer) : Nat := if lay = 0 then 26 else 24
section blocks
variable (s : MachineState)
theorem lbu_word1027 : decodeInstruction (0x000e4a03 : BitVec 32) = some (.base (.LBU .x20 .x28 0)) := rfl
theorem ex_ne (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
  fun he => h ((ofNat_inj hx hy).mp he)
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image}          
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
variable {im : Image}          
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
/-- T51 KMAX steps from 1158 to 1031 (1158 `j 54532`, the cap ladder, `j 1031`). -/
def kmaxSteps (i : Nat) : Nat := if i < 27 then 5 else if i < 48 then 8 else if i < 50 then 11 else 12
theorem pe_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
/-- T51 top G: 49311 `j 54543`, GT 54543..54552 (`t1 := 4 - [27 <= i < 48] + [i = 48]`, 7 for chain 0), 49315
`ld t2,24(t3)`: the step at which the G chain writes LOW (`gTerm`: `maxDigit 0 i - 1`; chain 0 never) and the header
high word. -/
def gTerm (i : Nat) : Nat := if i = 0 then 7 else SigGolfCandidate.T3.maxDigit 0 i - 1
def gtK (i : Nat) : Nat := if i = 0 then 12 else 11
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image}           (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Grind
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest nonceBytes pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (lowerZeroBits lowerNonceCap lowerZeroOk lowerNodeInputN lowerNodeHashN lowerNonceSearch
  lowerNodeAt)
theorem extractByte_toNat_g (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
section blocks
variable {im : Image}           (s : MachineState)

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

/-- The top-tree node word (heaps `< 4096`) never passes the stub's lower-tree test (L-hyper A: `w >> 28 = 0`). -/
theorem top_pass (heap : Nat) (hh : heap < 4096) : BitVec.ofNat 64 heap >>> 28 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  norm_num; omega

/-! U16b grind stub: the classification path, the loop setup and the zero test. -/

section cls
variable {im : Image}          

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image}          

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

/-- The stub's zero test on the used half's top byte is `lowerZeroOk`. -/
theorem zero_test (v : Digest) (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    ((extractByte (v.extractLsb' 64 64) 7).zeroExtend 64 >>> ((BitVec.ofNat 64 (8 - b)).toNat % 64) = 0#64) ↔
      v.toNat / 2 ^ (128 - b) = 0 := by
  have hv := v.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 - b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 - b < 64 by omega)]
  have e : ((extractByte (v.extractLsb' 64 64) 7).zeroExtend 64 >>> (8 - b)).toNat = v.toNat / 2 ^ (128 - b) := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, extractByte_toNat_g, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h1 : v.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact hv
    rw [Nat.mod_eq_of_lt h1, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    have h2 : v.toNat / 2 ^ (64 + 8 * 7) < 256 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), show 256 * 2 ^ (64 + 8 * 7) = 2 ^ 128 by norm_num]; exact hv
    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 64 + 8 * 7 + (8 - b) = 128 - b by omega]
  constructor
  · intro h; rw [← e, h]; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; rw [e, h]; rfl

/-! U16b grind stub: the found exit and the search loop. -/

section sim
variable {im : Image} {sk : BitVec 256}
theorem tb_half {β : Type} {s : MachineState} {input : List UInt8} {W : Nat} (high : Bool)
    {f : Digest → SigGolfCandidate.T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (ClaudeWCT.WCT9.halfOf high a)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (ClaudeWCT.WCT9.halfHash high input >>= f) Q := by
  rw [ClaudeWCT.WCT9.halfHash_eq, bind_assoc]
  simp only [pure_bind]
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem tb_pub {β : Type} {s : MachineState} {input : List UInt8} {W : Nat}
    {f : SigGolfCandidate.T3.HashOutput → SigGolfCandidate.T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (SigGolfCandidate.T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
end sim

section found
variable {im : Image}          

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

theorem cap_le (lay heap : Nat) : lowerNonceCap lay heap ≤ 2048 := by
  unfold ClaudeWCT.WCT9.lowerNonceCap ClaudeWCT.WCT9.lowerZeroBits; split_ifs <;> norm_num
section loop
variable {im : Image}           (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image}           {sk : BitVec 256}

end pass

end Grind


end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
section tb
variable {image : Image} {sk : BitVec 256}
theorem tb_foldlM_vals {γ : Type} {n : Nat} (f : γ → Fin n → T3.M γ) (W : Nat)
    (Inv : Nat → γ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) acc t, Inv i.val acc t → TBSim image sk t W (f acc i) (Inv (i.val + 1))) :
    ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      Inv k acc t → TBSim image sk t (xs.length * W) (xs.foldlM f acc) (Inv (k + xs.length)) := by
  intro xs
  induction xs with
  | nil => intro k acc t _ ht; simpa using TBSim.pure (image := image) (sk := sk) ht
  | cons x xs ih =>
    intro k acc t hidx ht
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    rw [List.foldlM_cons]
    have h1 := hbody x acc t (by rw [hidx.1]; exact ht)
    rw [hidx.1] at h1
    refine (TBSim.bind (W₂ := xs.length * W) h1 (fun acc' t' ht' => ?_)).mono
      (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h)
    have := ih (k + 1) acc' t' (by simpa using hidx.2) ht'
    rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
section chain
variable {sk : BitVec 256}
/-- T51: the top chain caps of KMAX (`maxDigit 0 i`; `n4` is unused), lower layers 7. -/
def endpoint (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) else 7
/-- Extra cycles of the cap selection on the top (1030 `j 1158`, KMAX). -/
def endpointExtra (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then 1 + SharedRecover.kmaxSteps i else 0
/-- Cycle budget of one chain step: the T51 top G step runs GT (+7 cycles). -/
def stepW (lay : Layer) : Nat := if lay = 0 then 74 else 67
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image}                              [PackedBlocks.Code im] {sk : BitVec 256}
theorem wordsOf_chainInputW_G {lay : Layer} {i : Nat} (hG : ClaudeWCT.WCT9.isG lay i = true) (tree leaf step : Nat)
    (v : Digest) :
    wordsOf (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v) =
      [v.extractLsb' 0 64, v.extractLsb' 64 64, (chainHeader lay tree leaf i step).extractLsb' 0 64,
        (chainHeader lay tree leaf i step).extractLsb' 64 64, 0, 0, 0, 0] := by
  rw [ClaudeWCT.WCT9.chainInputW_G hG]
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16,
    wordsOf_bytesLE16]
  rfl
/-- The step at which a G chain writes LOW (T51 top: `gTerm`; lower: 6). -/
def gTermL (lay : Layer) (i : Nat) : Nat := if lay = 0 then SharedRecover.gTerm i else SigGolfCandidate.T3.maxDigit lay i - 1
theorem endpoint_top (i n4 : Nat) : SigGolfCandidate.T3.maxDigit 0 i = endpoint 0 i n4 := by
  simp [SigGolfCandidate.T3.maxDigit, endpoint]

end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
theorem shr_and_mask (a k m : Nat) (ha : a < 2 ^ 64) (hm : m ≤ 64) :
    BitVec.ofNat 64 a >>> k &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a / 2 ^ k % 2 ^ m) := by
  rw [ofNat_shr _ _ ha, ofNat_and_mask _ _ hm]
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
def lE (lay : Layer) : Nat := ![318, 295, 272, 249] lay
def lD (lay : Layer) : Nat := ![0x3ce8, 0x4968, 0x55a8, 0x820] lay
def lWM (lay : Layer) : Nat := ![0x2f08, 0x3e48, 0x4A88, 0x56C8] lay
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def entryCode249 : List (BitVec 32) := seg_249.set 4 (0xc900893 : BitVec 32)
sym_block entryBlock249 := symRun {noAlias := true} entryCode249 (pcOf 249) 200
def entryCode272 : List (BitVec 32) := seg_272.set 4 (0xc900893 : BitVec 32)
sym_block entryBlock272 := symRun {noAlias := true} entryCode272 (pcOf 272) 200
class EntryCode (im : Image) : Prop where
  code249 : CodeAt im (pcOf 249) entryCode249
  code272 : CodeAt im (pcOf 272) entryCode272
  code295 : CodeAt im (pcOf 295) seg_295
  code318 : CodeAt im (pcOf 318) seg_318
  code262 : CodeAt im (pcOf 262) seg_262
  code285 : CodeAt im (pcOf 285) seg_285
  code308 : CodeAt im (pcOf 308) seg_308
  code332 : CodeAt im (pcOf 332) seg_332
variable {im : Image} [EntryCode im]
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
theorem so3_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (b + 7) ∧ t.getReg .x21 = BitVec.ofNat 64 21 ∧
      t.getReg .x20 = BitVec.ofNat 64 0 ∧ t.getReg .x25 = BitVec.ofNat 64 SEL ∧
      RegsExcept s t [.x20, .x21, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_3 hK.2.1) (codeAt_k_3 hK) s hpc (by simp [st_3, blk354_3.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_3, blk354_3.res, E.eval]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_3, blk354_3.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_3, blk354_3.res, rv_simp]
theorem so40_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 40)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 43) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_40 hK.2.1) (codeAt_k_40 hK) s hpc (by simp [st_40, blk354_40.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_40, blk354_40.res, E.eval]
  · simp [st_40, blk354_40.res, rv_simp]
  · simp [st_40, blk354_40.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_40, blk354_40.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_40, blk354_40.res, rv_simp]
theorem so52_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 52)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x23 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x24 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 53)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_52 hK.2.1) (codeAt_k_52 hK) s hpc (by simp [st_52, blk354_52.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_52, rebase, blk354_52.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_52, blk354_52.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_52, blk354_52.res, rv_simp]
theorem so101_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 101)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_101 hK.2.1) (codeAt_k_101 hK) s hpc (by simp [st_101, blk354_101.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_101, blk354_101.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · simp [st_101, blk354_101.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_101, blk354_101.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_101, blk354_101.res, rv_simp]
end blocks
section sort
variable {image : Image} {b : Nat}
theorem exch {rlo rhi : Reg} {o nxt : Nat}
    (hsw : ∀ s : MachineState, s.pc = pcOf (b + o) → ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = s.getReg rhi ∧ t.getReg rhi = s.getReg rlo ∧ RegsExcept s t [.x7, rlo, rhi] ∧
      Frame s t (fun _ => False))
    (s : MachineState) (x y : Nat)
    (hpc : s.pc = if x ≤ y then pcOf (b + nxt) else pcOf (b + o))
    (hlo : s.getReg rlo = BitVec.ofNat 64 x) (hhi : s.getReg rhi = BitVec.ofNat 64 y) :
    ∃ k t, Steps image s k k t ∧ k ≤ 3 ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = BitVec.ofNat 64 (min x y) ∧ t.getReg rhi = BitVec.ofNat 64 (max x y) ∧
      RegsExcept s t [.x7, rlo, rhi] ∧ Frame s t (fun _ => False) := by
  by_cases h : x ≤ y
  · rw [if_pos h] at hpc
    refine ⟨0, s, Steps.refl s, by omega, hpc, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [hlo, Nat.min_eq_left h]
    · rw [hhi, Nat.max_eq_right h]
  · rw [if_neg h] at hpc
    obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := hsw s hpc
    refine ⟨3, t, h1, le_refl _, h2, ?_, ?_, h5, h6⟩
    · rw [h3, hhi, Nat.min_eq_right (by omega)]
    · rw [h4, hlo, Nat.max_eq_left (by omega)]
end sort
section loop
variable {image : Image} {b : Nat}
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
section blocks
variable {image : Image} {d b : Nat}
end blocks
structure DsPre (d : Nat) (s : MachineState) (rho : Digest) (m : T3.Message) : Prop where
  pc : s.pc = pcOf d
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
-- (open dropped: nothing it names is in this part)
def ExpandDataOK (im : Image) : Prop :=
  im.data = lplanBytes ++ planBytes ++ expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
-- (open dropped: nothing it names is in this part)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
-- (open dropped: nothing it names is in this part)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
-- (open dropped: nothing it names is in this part)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
section pieces
variable {im : Image}
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
def windowOK (n : Nat) (ws : List (BitVec 32)) : Bool :=
  (List.range ws.length).all fun i => expLook (n + i) == ws[i]?
theorem micro_step {im : Image} {pc : Word} {w : BitVec 32} {i : Instruction} {m : Micro}
    (hc : CodeAt im pc [w]) (hd : decodeInstruction w = some i) (hcl : classify i = some m)
    {s t : MachineState} (hpc : s.pc = pc) (he : m.exec s = some t) :
    Steps im s 1 (instructionCycles i) t := by
  have hf : fetch im s = some i := (hc.fetch s hpc).trans hd
  have := Steps.step (image := im) hf ((classify_sound hcl s).trans he) (Steps.refl t)
  simpa using this
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
theorem extractLsb'_256_toNat (a : BitVec 256) (w : Nat) :
    (a.extractLsb' (64 * w) 64).toNat = a.toNat / 2 ^ (64 * w) % 2 ^ 64 := by
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem mod_div_mod (X k m : Nat) (h : k + m ≤ 64) : X % 2 ^ 64 / 2 ^ k % 2 ^ m = X / 2 ^ k % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < m
  · simp only [hi, decide_true, Bool.true_and]
    have : i + k < 64 := by omega
    simp [this]
  · simp [hi]
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
def base : Nat := 3164
def seg_0 : List (BitVec 32) := [16777327]
def seg_1 : List (BitVec 32) := [1049235,1049875,115]
def seg_4 : List (BitVec 32) := [100678403,125841795,52547987,19,0x5491b193]
def seg_9 : List (BitVec 32) := [0xfe0180e3]
def seg_10 : List (BitVec 32) := [727827,35347219,1049491,29038483,66359,6784947,2098835,3148179,4196883,5245587,6294803,7343891,34281619,5175,0x84040413,16772663,0x600e0e13,4407,0xffc10113,20151,0x4a4e8e93,52279,0x4a4c0c13,67110291]
def seg_34 : List (BitVec 32) := [0x6003803,545171,0x7f1f193,33657363,23224883,21077907,0xffefb3,8493971,31165363,0x60178d93,19,5789459,2586419,25626419,0x42000493,458983]
def seg_50 : List (BitVec 32) := [0x6803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x44000493,458983]
def seg_68 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x46000493,458983]
def seg_86 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x48000493,458983]
def seg_104 : List (BitVec 32) := [0x7003803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x4a000493,458983]
def seg_122 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x4c000493,458983]
def seg_140 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x4e000493,458983]
def seg_158 : List (BitVec 32) := [0x7803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x50000493,458983]
def seg_176 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x52000493,458983]
/-- Nested FTS (r1-1): the forest hash is replaced by copying `(L8, R8)` from the forest-buffer pair 8 (`0x520`) to
`0x100` (copied to the L3 encoding block by 39142) and to the encoding R slot `0x20290`; 203 is now a NOP. -/
def seg_194 : List (BitVec 32) := [1375744387,1384134403,271593507,283128867,1392521603,1400911619,134711,675166243,686701603]
def seg_203 : List (BitVec 32) := [19]
def seg_204 : List (BitVec 32) := [0x6f92206f]
def layout : SigGolfCandidate.Rv.Layout := [(0, seg_0), (1, seg_1), (4, seg_4), (9, seg_9), (10, seg_10), (34, seg_34), (50, seg_50), (68, seg_68), (86, seg_86), (104, seg_104), (122, seg_122), (140, seg_140), (158, seg_158), (176, seg_176), (194, seg_194), (203, seg_203), (204, seg_204)]
def code : List (BitVec 32) := layoutCode layout
theorem window : windowOK base code = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
def leafO : Nat := 816
def sixLevels (k index j : Nat) (path : Nat → Digest) (root : Digest) : M Digest :=
  (List.range 6).foldlM (fun value l =>
    let other := path l
    let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.WCT9.wctNodeHash k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2) root
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
def cClrL : List (BitVec 32) := [0x00053023,0x00850513,0xfeb56ce3]
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

/-- Code words of the compact/nested-FTS expansion that the paired expander keeps from the reference image. Stage 2
(C2 + C3, from #866): also the trampolines `43472 .. 43488` (`Compact2.cETail`, the footer's LE64(1) at `WIT + 24`,
and `Compact2.cRT 1..3`, the lower root windows' row-tweak pads). -/
def compactScope (n : Nat) : Bool :=
  decide ((33000≤n ∧ n<33285) ∨ (41108≤n ∧ n<42719) ∨ (43472≤n ∧ n<43489) ∨ (43951≤n ∧ n≤44043) ∨ (43500≤n ∧ n<43761))
namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
end PairCopy
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
section code
variable {im : Image}                        
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def compactChunkAllowed (c : Nat) : Prop :=
  c=128 ∨ c=129 ∨ c=130 ∨ (160≤c ∧ c≤166) ∨ c=169 ∨ c=170 ∨ c=171 ∨ c=172
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
def cSnap : List (BitVec 32) := [5431,2147812627,3212727,361875,5687,2861958675,4221563119]
def pregAt (c : Nat) : Nat := 33122 + 6 * c
def cCh2 : List (BitVec 32) := [3228983,3833922835,17847,1896187283,1591,361104915,1954566383]
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
def lvSrc (lay j : Nat) : Nat :=
  0x310000 + 8136 + 64 * ((if lay = 1 then 66 else if lay = 2 then 116 else 165) + (if lay = 1 then 6 else 5) - j)
def lvH (lay : Nat) : Nat := if lay = 1 then 7 else 6
def LPLAN : Nat := 0xff9400
def LPlanAt (t : MachineState) : Prop :=
  ∀ k < 192, t.getMem (BitVec.ofNat 64 (LPLAN + 8 * k)) = bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * k)).take 8)
/-! ### C4: the top-path plan table of the expander's post-pass (data offset 26496 = legacy offset 2944) -/
def lvRow (lay r : Nat) : Nat := if lay = 1 then 64 + r else r
set_option maxRecDepth 100000 in
theorem lplan1_ok : ∀ r < 128, ∀ j < 7,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * (64 + r))).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 1 r).getD j 0) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lplan2_ok : ∀ r < 64, ∀ j < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * r)).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0) ∧
    (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 3 r).getD j 0 = (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lowerPlan_lt : (∀ r < 128, ∀ j < 7, (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 1 r).getD j 0 + 4 ≤ 25) ∧
    (∀ r < 64, ∀ j < 6, (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0 + 4 ≤ 20) := by
  decide +kernel
def plan (lay r j : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan (Fin.ofNat 4 lay) r).getD j 0
theorem plan_ok (lay r j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay) (hj : j < lvH lay) :
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * lvRow lay r)).take 8)) j =
      BitVec.ofNat 64 (plan lay r j) ∧ plan lay r j + 4 ≤ (if lay = 1 then 25 else 20) := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hr hj
  unfold plan lvRow
  interval_cases lay
  · simp only [if_true] at hr hj ⊢
    exact ⟨lplan1_ok r (by omega) j hj, lowerPlan_lt.1 r (by omega) j hj⟩
  · simp only [show (2 : Nat) ≠ 1 by decide, if_false] at hr hj ⊢
    exact ⟨(lplan2_ok r (by omega) j hj).1, lowerPlan_lt.2 r (by omega) j hj⟩
  · simp only [show (3 : Nat) ≠ 1 by decide, if_false] at hr hj ⊢
    rw [show (Fin.ofNat 4 3 : SigGolfCandidate.T3.Layer) = 3 from rfl, (lplan2_ok r (by omega) j hj).2]
    exact ⟨(lplan2_ok r (by omega) j hj).1, lowerPlan_lt.2 r (by omega) j hj⟩
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
theorem lvH_le (lay : Nat) : lvH lay ≤ 7 := by unfold lvH; split <;> omega
theorem valid8 (X : Nat) (h : X + 8 ≤ 16777216) (h8 : X % 8 = 0) : accessValid (BitVec.ofNat 64 X) 8 = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [show MEMORY_BYTES = 16777216 from rfl]; omega, h8⟩
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
