import SigGolfCandidate.T3M.Verify.Mem
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
abbrev selC (a : HashOutput) (c : Nat) : Selection := (selections a).getD c ⟨0, []⟩
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FCtx where
  pk : Digest
  w : ClaudeWCT.W9.T3M.WBytes
  a : HashOutput
namespace FCtx
def idx (F : FCtx) : Nat := ClaudeWCT.WCT9.digestIndex F.a
def sel (F : FCtx) (c : Nat) : Selection := selC F.a c
def g (F : FCtx) (s : Nat) : Nat := T3M.selLeaf (F.sel (s / 3)) (s % 3)
theorem idx_lt (F : FCtx) : F.idx < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt F.a
end FCtx
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
def layerPc : Nat := 32951
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
structure FtsOut (F : FCtx) (root : Digest) (u : MachineState) : Prop where
  glob : Glob baseK F.w F.pk u
  idx : u.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : u.pc = pcOf layerPc
  root : DigAt u WIT root
  wit : Orig F.w (fun o => (32 ≤ o ∧ o < 64) ∨ (8000 ≤ o ∧ o < 21472)) u
  a2 : u.getReg .x12 = BitVec.ofNat 64 WIT
  s10 : u.getReg .x26 = 6
  heapOne : u.getReg .x7 = 1
  heapTwo : u.getReg .x13 = 2
  heapSeven : u.getReg .x30 = 7
  heapThree : u.getReg .x19 = 3
  heapFour : u.getReg .x20 = 4
  heapFive : u.getReg .x21 = 5
  coordStep : u.getReg .x6 = 0x10000
  topBase : u.getReg .x9 = BitVec.ofNat 64 TOPB9
  top : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
    BitVec.ofNat 64 (topWords.getD k 0)
  top8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21776
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
def afterFts (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (r : Option Digest) : T3.M Bool :=
  match r with
  | some root => do
      let __x ← ClaudeWCT.W9.T3M.layersBC w index 4 (.forest root)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput)
def AfterGoodBudget (acceptCycles : Nat) : Prop :=
  ∀ (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (Q : Prop), Q →
    ∀ (a : HashOutput) (root : Digest) (u : MachineState),
      FtsOut ⟨pk, w, a⟩ root u →
      GoodQ u 8050 8050 Q acceptCycles (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some root)) Kb)
end SigGolfCandidate.T3M.Verify
