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
def layerPc : Nat := 854
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)
/-- State after the nested FTS (pc 854, with the pair already in the L3 row): tree 8's top pair in the L3 block's left slot (witness
offset 0) and right slot (offset 48). -/
structure FtsOut (F : FCtx) (top : Digest × Digest) (u : MachineState) : Prop where
  /-- C4 (D7, adapted from b3cc11b): the FTS setup no longer loads `s2` (x18); the L3 block loads it from `d0`. -/
  glob : Glob [(.x5, 0)] F.w F.pk u
  idx : u.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : u.pc = pcOf layerPc
  left : DigAt u WIT top.1
  right : DigAt u (WIT + 48) top.2
  /-- C3 (stage 2): witness word 3 (the L3 encoding's row-tweak high word, honest 1) is still original; the merged
  singleton (Cm) writes its left top value at `WIT` with its junk half at `WIT - 16`, so `WIT + 16 .. WIT + 48` is
  untouched by the FTS. -/
  wit : Orig F.w (fun o => (24 ≤ o ∧ o < 48) ∨ (8096 ≤ o ∧ o < 23208)) u
  base : u.getReg .x8 = BitVec.ofNat 64 (WIT + 80)
  a1 : u.getReg .x11 = 64
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
  top8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21280
  /-- `a2` after coordinate 8's last heap hash (Cm: `WIT - 16` for the high-half left top node, `WIT + 48` for the
  low-half right top node); the L3 encoding writes there. -/
  a2 : u.getReg .x12 = BitVec.ofNat 64 2888 ∨ u.getReg .x12 = BitVec.ofNat 64 2952
  /-- C4 (D7): the stack word `ld s2,-304(s1)` reads (0xFFF). -/
  d0 : u.getMem (BitVec.ofNat 64 (TOPB9 - 304)) = 0xFFF
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)
def afterFts (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (r : Option (Digest × Digest)) : T3.M Bool :=
  match r with
  | some top => do
      let __x ← ClaudeWCT.W9.T3M.layersCanonicalBC w index 4 (.pair top.1 top.2)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
end SigGolfCandidate.T3M.Verify
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput)
/-- Configuration (1)+(2): the hash hypothesis is read with the witness top-choice hint `wtopHigh w`
(`HashOkBy floors high`, path-aware credit). -/
def AfterGoodBudget (acceptCycles : Nat) : Prop :=
  ∀ (floors : T3.Layer → Nat), CreditFloors floors →
  ∀ (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (Q : Prop), Q →
    ∀ (a : HashOutput) (top : Digest × Digest) (u : MachineState),
      FtsOut ⟨pk, w, a⟩ top u →
      GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) u 8050 8050 Q acceptCycles
        (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb)
end SigGolfCandidate.T3M.Verify
