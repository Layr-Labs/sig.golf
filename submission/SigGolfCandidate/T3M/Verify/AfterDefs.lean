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
def layerPc : Nat := 850
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
/-- State after the nested FTS (pc 850, before the R9 copy): tree 8's top pair in the L3 block's left slot (witness
offset 0) and in the virtual Z slot (offset 144). -/
structure FtsOut (F : FCtx) (top : Digest × Digest) (u : MachineState) : Prop where
  glob : Glob baseK F.w F.pk u
  idx : u.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : u.pc = pcOf layerPc
  left : DigAt u WIT top.1
  right : DigAt u (WIT + 144) top.2
  wit : Orig F.w (fun o => (32 ≤ o ∧ o < 48) ∨ (8256 ≤ o ∧ o < 24800)) u
  base : u.getReg .x8 = BitVec.ofNat 64 (WIT + 176)
  a1 : u.getReg .x11 = 64
  /-- The fold hand-off `a2` of coordinate 8: the L3 encoding hash writes its digest there. -/
  a2 : u.getReg .x12 = BitVec.ofNat 64 1200 ∨ u.getReg .x12 = BitVec.ofNat 64 1344
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
  top8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21200
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
def afterFts (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (r : Option (Digest × Digest)) : T3.M Bool :=
  match r with
  | some top => do
      let __x ← ClaudeWCT.W9.T3M.layersBC w index 4 (.pair top.1 top.2)
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
    ∀ (a : HashOutput) (top : Digest × Digest) (u : MachineState),
      FtsOut ⟨pk, w, a⟩ top u →
      GoodQ u 8050 8050 Q acceptCycles (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb)
end SigGolfCandidate.T3M.Verify
