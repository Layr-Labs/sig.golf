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
import SigGolfCandidate.Merge076.P2
import SigGolfCandidate.Merge076.P4
import SigGolfCandidate.Merge076.P5
import SigGolfCandidate.Merge076.P6
import SigGolfCandidate.Merge076.P7

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
section blocks
variable (s : MachineState)
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image} [Code im]
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
variable {im : Image} [Code im]
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
theorem fetch_49328 (hpc : s.pc = pcOf 49328) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_49328 (im := im)).fetch s hpc).trans rfl
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
section blocks
variable {im : Image} [Code im] (s : MachineState)

theorem b2_spec (hpc : s.pc = pcOf 54811) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if (s.getReg .x31 >>> 28) = 0#64 then pcOf 54875 else pcOf 54814) ∧
      RegsExcept s t [.x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54811 54814 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gB2 hc s hpc (by simp [gB2.res, rv_simp]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x31 >>> 28) = 0#64 <;> simp [gB2.res, E.eval, CmpOp.eval, BinOp.eval, hc]
  · intro r hr; simp at hr; cases r <;> simp_all [gB2.res, rv_simp] <;> rfl
  · intro A _ _; simp [gB2.res, rv_simp]

theorem b3a_spec (hpc : s.pc = pcOf 54823) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if (s.getReg .x7).ult 64#64 then pcOf 54826 else pcOf 54825) ∧
      t.getReg .x29 = 64#64 ∧ RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54823 54825 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gB3a hc s hpc (by simp [gB3a.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x7).ult 64#64 = true <;> simp [gB3a.res, E.eval, CmpOp.eval, hc]
  · simp only [Result.toState_getReg, gB3a.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gB3a.res, rv_simp] <;> rfl
  · intro A _ _; simp [gB3a.res, rv_simp]

theorem b3b_spec (hpc : s.pc = pcOf 54824) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if (s.getReg .x7).ult (s.getReg .x29) then pcOf 54826 else pcOf 54825) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54824 54825 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gB3b hc s hpc (by simp [gB3b.res, rv_simp]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x7).ult (s.getReg .x29) = true <;> simp [gB3b.res, E.eval, CmpOp.eval, hc]
  · intro r hr; cases r <;> simp_all [gB3b.res, rv_simp] <;> rfl
  · intro A _ _; simp [gB3b.res, rv_simp]

theorem j1138_spec (hpc : s.pc = pcOf 1138) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54800 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound gJ (Code.codeAt_1138 (im := im)) s hpc (by simp [gJ.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [gJ.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp_all [gJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [gJ.res, rv_simp]

theorem pA_spec (hpc : s.pc = pcOf 60128) :
    ∃ t, Steps im s 5 5 t ∧
      t.pc = (if ((s.getReg .x31 &&& 255#64) + 0xffffffffffffff80#64).ult 16#64 = true then pcOf 60133 else pcOf 60140) ∧
      t.getReg .x7 = (s.getReg .x31 &&& 255#64) + 0xffffffffffffff80#64 ∧ t.getReg .x29 = 256#64 ∧
      RegsExcept s t [.x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60128 60133 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pA hc s hpc (by simp [pA.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : ((s.getReg .x31 &&& 255#64) + 0xffffffffffffff80#64).ult 16#64 = true <;>
      simp [pA.res, E.eval, CmpOp.eval, BinOp.eval, hc]
  all_goals try (simp only [Result.toState_getReg, pA.res]; t3n []; done)
  · intro r hr; simp at hr; cases r <;> simp_all [pA.res, rv_simp] <;> rfl
  · intro A _ _; simp [pA.res, rv_simp]

theorem pB_spec (hpc : s.pc = pcOf 60133) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if (s.getReg .x7).ult 4#64 = true then pcOf 60140 else pcOf 60136) ∧
      t.getReg .x29 = 0#64 ∧ RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60133 60136 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pB hc s hpc (by simp [pB.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x7).ult 4#64 = true <;> simp [pB.res, E.eval, CmpOp.eval, hc]
  · simp only [Result.toState_getReg, pB.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pB.res, rv_simp] <;> rfl
  · intro A _ _; simp [pB.res, rv_simp]

theorem pC_spec (hpc : s.pc = pcOf 60136) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if (s.getReg .x7).ult 8#64 = true then pcOf 60140 else pcOf 60139) ∧
      t.getReg .x29 = 8#64 ∧ RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60136 60139 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pC hc s hpc (by simp [pC.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x7).ult 8#64 = true <;> simp [pC.res, E.eval, CmpOp.eval, hc]
  · simp only [Result.toState_getReg, pC.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pC.res, rv_simp] <;> rfl
  · intro A _ _; simp [pC.res, rv_simp]

theorem pD_spec (hpc : s.pc = pcOf 60139) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 54872 ∧ t.getReg .x30 = s.getReg .x30 + 16#64 ∧
      RegsExcept s t [.x29, .x30] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60139 60142 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pD hc s hpc (by simp [pD.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pD.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, pD.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pD.res, rv_simp] <;> rfl
  · intro A _ _; simp [pD.res, rv_simp]

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

theorem lowerNodeWord_eq (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3) (ht : tree < 2 ^ T3.hyperW (lay - 1))
    (hh : heap < 128) :
    ClaudeWCT.WCT9.lowerNodeWord (lay - 1) tree heap = BitVec.ofNat 64 (lowTw lay tree heap) := by
  unfold ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerAdd lowTw
  rewrite [if_pos (T3.hyperHonest_of (by omega) ht), LH.hyperWord_eq_honest (by omega) ht, ofNat_add_ofNat]
  apply congrArg (BitVec.ofNat 64)
  omega
section cls
variable {im : Image} [Code im]

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image} [Code im]

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

theorem nonce_words (n : Nat) (hn : n < 2 ^ 64) : wordsOf (nonceBytes n) = [BitVec.ofNat 64 n, 0] :=
  nonce_words_aux n hn

theorem wordsOf_inputN (lay tree heap n : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3) (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh : heap < 128)
    (hn : n < 2 ^ 64) (l r : Digest) :
    wordsOf (lowerNodeInputN lay tree heap n l r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (lowTw lay tree heap), 0, BitVec.ofNat 64 n, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  unfold lowerNodeInputN
  rw [wordsOf_append _ _ (by simp [bytesLE_length, nonceBytes]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, nonce_words n hn, wordsOf_bytesLE16]
  have e : ClaudeWCT.WCT9.merkleTweak lay tree heap = 0#64 ++ BitVec.ofNat 64 (lowTw lay tree heap) := by
    unfold ClaudeWCT.WCT9.merkleTweak ClaudeWCT.WCT9.lowerTweak
    rw [if_neg (by omega), lowerNodeWord_eq lay tree heap h1 h3 ht hh]
  have hhi : (0#64 ++ BitVec.ofNat 64 (lowTw lay tree heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [e, SigGolfCandidate.T3.append64_low, hhi, wordsOf_bytesLE16]
  rfl

/-- Facts at the fold hash (word 1138) of a lower node. -/
structure StubIn (t : MachineState) (lay tree heap : Nat) (l r : Digest) : Prop where
  pc : t.pc = pcOf 1138
  x5 : t.getReg .x5 = 0
  x10 : t.getReg .x10 = BitVec.ofNat 64 NODE
  x11 : t.getReg .x11 = BitVec.ofNat 64 64
  x12 : t.getReg .x12 = BitVec.ofNat 64 NOUT
  w0 : t.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64
  w8 : t.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64
  w16 : t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (lowTw lay tree heap)
  w24 : t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0
  w32 : t.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  w40 : t.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  w48 : t.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64
  w56 : t.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64
  h1 : 1 ≤ lay
  h3 : lay ≤ 3
  ht : tree < 2 ^ T3.hyperW (lay - 1)
  hh2 : 2 ≤ heap
  hh : heap < 128

/-- Words not written by the stub keep their value; the node words are read back. -/
theorem hashInput_N {t u : MachineState} {lay tree heap : Nat} {l r : Digest} (F : StubIn t lay tree heap l r)
    {W : Nat → Prop} (hf : Frame t u W) (hW : ∀ X, NODE ≤ X → X < NODE + 64 → X ≠ NODE + 32 → ¬ W X)
    (n : Nat) (hn : n < 2 ^ 64) (h10 : u.getReg .x10 = BitVec.ofNat 64 NODE)
    (h11 : u.getReg .x11 = BitVec.ofNat 64 64) (hpad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n) :
    hashInput u = toQ (pad64 (lowerNodeInputN lay tree heap n l r)) := by
  rw [pad64_of_aligned _ (by rw [inputN_length])]
  have g : ∀ X, NODE ≤ X → X < NODE + 64 → X ≠ NODE + 32 → u.getMem (BitVec.ofNat 64 X) = t.getMem (BitVec.ofNat 64 X) :=
    fun X h1 h2 h3 => hf.get (by simp only [NODE] at h2; omega) (hW X h1 h2 h3)
  refine hashInput_toQ u _ 0 NODE (inputN_length _ _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [wordsOf_inputN lay tree heap n F.h1 F.h3 F.ht F.hh hn, readWords_eight,
    g _ (by simp) (by simp) (by simp), g _ (by simp) (by simp) (by simp), g _ (by simp) (by simp) (by simp),
    g _ (by simp) (by simp) (by simp), hpad, g _ (by simp) (by simp) (by simp), g _ (by simp) (by simp) (by simp),
    g _ (by simp) (by simp) (by simp), F.w0, F.w8, F.w16, F.w24, F.w40, F.w48, F.w56]

section sim
variable {im : Image} {sk : BitVec 256}
end sim

section found
variable {im : Image} [Code im]

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

section loop
variable {im : Image} [Code im] (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image} [Code im] {sk : BitVec 256}

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
theorem tb_mapM_finRange {δ : Type} (n : Nat) (f : Fin n → T3.M δ) (W : Nat) (Inv : List δ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) (pre : List δ) t, pre.length = i.val → Inv pre t →
      TBSim image sk t W (f i) (fun d u => Inv (pre ++ [d]) u)) {s : MachineState} (h0 : Inv [] s) :
    TBSim image sk s (n * W) ((List.finRange n).mapM f) (fun ds u => ds.length = n ∧ Inv ds u) := by
  have := tb_mapM_idx f Fin.val W Inv (List.finRange n) [] (by rw [finRange_map_val]; simp)
    (fun x _ pre' t h1 h2 => hbody x pre' t h1 h2) h0
  simpa using this
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
theorem blocks_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length']), blocks_toQ ⟨by rw [chainInput_length']; omega,
    by rw [chainInput_length']⟩, chainInput_length']
theorem ChainCtx.frame {lay tree leaf i : Nat} {t u : MachineState} (h : ChainCtx lay tree leaf i t)
    {l : List Reg} (hl : Reg.x5 ∉ l ∧ Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x18 ∉ l ∧ Reg.x19 ∉ l) (hr : RegsExcept t u l) (hf : Frame t u StepW) :
    ChainCtx lay tree leaf i u where
  x5 := by rw [hr.get hl.1]; exact h.x5
  x8 := by rw [hr.get hl.2.1]; exact h.x8
  x9 := by rw [hr.get hl.2.2.1]; exact h.x9
  x18 := by rw [hr.get hl.2.2.2.1]; exact h.x18
  x19 := by rw [hr.get hl.2.2.2.2]; exact h.x19
  z0 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z0
  z8 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z8
section chain
variable {sk : BitVec 256}
theorem not_ChW_of {lay : T3.Layer} {WC k A : Nat} (hk : k ≤ 58) (h1 : WC + 64 ≤ A) (h2 : A < CHAIN + 16 ∨ CHAIN + 112 ≤ A)
    (h3 : A < LEAFPK ∨ LEAFPK + 16 * 60 ≤ A) : ¬ ChW lay WC k A := by
  unfold ChW StepW
  rintro (h | ⟨c, hc, h | h⟩ | ⟨c, _, h | h⟩) <;> simp only [CHAIN, LEAFPK] at h h2 h3 <;>
    first | omega | (unfold slotOff at h; split_ifs at h <;> omega)
structure ChainsInv (t0 : MachineState) (lay : Layer) (tree leaf P WC n n4 : Nat) (vals : Nat → Digest)
    (ends : List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1010
  ctx : ChainCtx lay.val tree leaf ends.length t
  x23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * ends.length)
  slots : ∀ j < ends.length, DigAt t (LEAFPK + slotOff lay j) (ends.getD j 0)
  wvals : ∀ j < ends.length, DigAt t (WC - 64 * j + 48) (vals j)
  regs : RegsExcept t0 t oneRegs
  frame : Frame t0 t (ChW lay WC ends.length)
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
variable {im : Image} [Code im]                    [PackedBlocks.Code im] {sk : BitVec 256}
/-- Witness stack: on a G chain (lower odd, or top even `≤ 50`) the step keeps the high half exactly when it is not the
step `gTermL` (T51: `maxDigit - 1`; top chain 0 keeps the high half on every step). -/
theorem gHigh_eq {lay : Layer} {i m : Nat} (hG : ClaudeWCT.WCT9.isG lay i = true)
    (hm : m < SigGolfCandidate.T3.maxDigit lay i) :
    ClaudeWCT.WCT9.chainHigh lay i m = decide (m ≠ gTermL lay i) := by
  apply Bool.eq_iff_iff.mpr
  rw [ClaudeWCT.WCT9.chainHigh_eq_true, decide_eq_true_iff]
  rcases ClaudeWCT.WCT9.isG_eq_true.mp hG with ⟨hl, hi⟩ | ⟨hl, hi, hi50⟩
  · have hmd : SigGolfCandidate.T3.maxDigit lay i = 7 := by simp [SigGolfCandidate.T3.maxDigit, hl]
    have hg : gTermL lay i = 6 := by simp [gTermL, hl, hmd]
    rw [hmd] at hm
    rw [hg]
    constructor
    · rintro (⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h, _, _⟩)
      · omega
      · omega
      · exact absurd h hl
    · intro h; exact Or.inl ⟨hl, Or.inr ⟨hi, by omega⟩⟩
  · subst hl
    have hg : gTermL 0 i = SharedRecover.gTerm i := by simp [gTermL]
    rw [hg]
    unfold SharedRecover.gTerm
    constructor
    · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
      · exact absurd rfl h
      · by_cases h0 : i = 0
        · rw [if_pos h0]
          have : SigGolfCandidate.T3.maxDigit 0 i = 5 := by subst h0; rfl
          omega
        · rw [if_neg h0]; omega
    · intro h
      refine Or.inr ⟨rfl, ⟨hi, hi50⟩, ?_⟩
      by_cases h0 : i = 0
      · exact Or.inr h0
      · rw [if_neg h0] at h; exact Or.inl (by omega)

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
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [EntryCode im]
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_entry : EntryCode Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel

end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem installed_code : Code Images.expandImage := by
  constructor <;> (apply codeAt_t51_at <;> decide)

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
end blocks
section sort
variable {image : Image} {b : Nat}
theorem sort_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ k t, Steps image s k k t ∧ k ≤ 20 ∧ t.pc = pcOf (b + 51) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 0 0) ∧
      t.getReg .x23 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 1 0) ∧
      t.getReg .x24 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 2 0) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, h6, h22, h23, h24, r1, f1⟩ := so31_spec hK s hpc u hu h28
  obtain ⟨k2, t2, s2, k2le, p2, a22, a23, r2, f2⟩ :=
    exch (so40_spec hK) t1 _ _ p1 h22 h23
  have b24 : t2.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) := by
    rw [r2.get (by decide), h24]
  obtain ⟨t3, s3, p3, r3, f3⟩ := so43_spec hK t2 p2 _ _ (by omega) (by omega) b24 a23
  obtain ⟨k4, t4, s4, k4le, p4, a23', a24, r4, f4⟩ :=
    exch (so44_spec hK) t3 (max (u / 16 % 128) (u / 2 ^ 11 % 128))
      (u / 2 ^ 18 % 128) p3 (by rw [r3.get (by decide), a23]) (by rw [r3.get (by decide), b24])
  have b22 : t4.getReg .x22 = BitVec.ofNat 64 (min (u / 16 % 128) (u / 2 ^ 11 % 128)) := by
    rw [r4.get (by decide), r3.get (by decide), a22]
  obtain ⟨t5, s5, p5, r5, f5⟩ := so47_spec hK t4 p4 _ _ (by omega) (by omega) a23' b22
  obtain ⟨k6, t6, s6, k6le, p6, a22', a23'', r6, f6⟩ :=
    exch (so48_spec hK) t5 _ _ p5
      (by rw [r5.get (by decide), b22]) (by rw [r5.get (by decide), a23'])
  refine ⟨9 + k2 + 1 + k4 + 1 + k6, t6, ?_, by omega, p6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6
    exact this
  · rw [r6.get (by decide), r5.get (by decide), r4.get (by decide), r3.get (by decide),
      r2.get (by decide), h6]
  · rw [a22']; rfl
  · rw [a23'']; rfl
  · rw [r6.get (by decide), r5.get (by decide), a24]; rfl
  · exact ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide))
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (by simp)
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
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
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
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
theorem run_cap (d : Bool) : run expLook [41060, 41054] 41052 [.br d] = some (resCap d) := by
  have h := chk_cap
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
section pieces
variable {im : Image}
theorem cap_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 41052) (S : Nat)
    (hS : S < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if S ≤ 789 then pcOf 41054 else pcOf 41060) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hce : capE.eval s = BitVec.ofNat 64 (if S < 790 then 1 else 0) := by
    simp only [capE, cst, E.eval, h20, BinOp.eval, BitVec.ult, toNat_ofNat_lt hS,
      toNat_ofNat_lt (show 790 < 2 ^ 64 by decide +kernel)]
    by_cases h : S < 790 <;> simp [h]
  have hbr : ∀ b ∈ (resCap (decide ¬ (S ≤ 789))).brs, b.holds s := by
    intro b hb
    simp only [resCap, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hce]
    by_cases h0 : S ≤ 789
    · simp only [show S < 790 by omega, if_true, h0, not_true_eq_false, decide_false]; decide +kernel
    · simp only [show ¬ S < 790 by omega, if_false, h0, not_false_eq_true, decide_true]; decide +kernel
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_cap _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hp]; simp only [resCap]
  by_cases h0 : S ≤ 789
  · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
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
theorem jal_x0_step {im : Image} {n m : Nat} {w : BitVec 32} {imm : BitVec 21}
    (hc : CodeAt im (pcOf n) [w]) (hd : decodeInstruction w = some (.base (.JAL .x0 imm)))
    (hoff : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcOf n) : Steps im s 1 1 (s.setPC (pcOf m)) := by
  have h := micro_step (m := .jal .x0 (signExtend21 imm)) hc hd rfl hpc (t := s.setPC (pcOf m)) (by
    simp only [Micro.exec, MachineState.setReg, hpc, Option.some.injEq]
    have e : signExtend21 imm = BitVec.ofNat 64 (signExtend21 imm).toNat := by simp
    rw [e, pcOf_add_lit n m _ hoff])
  exact h
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
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
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
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

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
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
def rLv (lay j : Nat) : Result := rLvs.getD (lvIdx lay j) RLv10.res
theorem rLv_eq (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay - 1) :
    rLv lay j = ⟨⟨lvRegs j (lvSrc lay j) (lvDst lay), lvMem j (lvSrc lay j) (lvDst lay),
      lvObl j (lvSrc lay j) (lvDst lay)⟩, .c (pcOf (lvAt lay j + 23)), .endOfCode, 23, 23⟩ := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
theorem run_lv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay - 1) :
    symRun cfgC (cLv lay j) (pcOf (lvAt lay j)) 40 = some (rLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
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
