import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_Search
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Defs
set_option Elab.async false

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
set_option maxRecDepth 100000 in
/-- Expand joint-cost cap test `S < 790` (nested FTS joint cap 789). -/
def capE : E := .bin .sltu (.reg .x20) (cst 790)
def resCap (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, capE)], [], []⟩, if d then pcOf 41060 else pcOf 41054, false, 2, 2, [⟨.eq, capE, .c 0, d⟩], none⟩
theorem chk_cap : (optBeq (run expLook [41060, 41054] 41052 [.br true]) (resCap true) &&
    optBeq (run expLook [41060, 41054] 41052 [.br false]) (resCap false)) = true := by decide +kernel
theorem run_cap (d : Bool) : run expLook [41060, 41054] 41052 [.br d] = some (resCap d) := by
  have h := chk_cap
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem expCostBytes_length : expCostBytes.length = 16384 := by decide +kernel
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
