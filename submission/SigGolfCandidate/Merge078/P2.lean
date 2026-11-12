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
/-- U16b: the grind stub's record of a lower layer after its climb: the fold nonces of the three ground folds
`height lay - 4 + m` at `recB lay + 16 - 8 m` (classes 8..15, 4..7, 2..3) and the fold-0 parent heap at `+ 24`. -/
def RecAt (t : MachineState) (lay : Layer) (leaf : Nat) (ns : List Nat) : Prop :=
  ns.length = height lay - 1 ∧
    (∀ m, m < 3 → t.getMem (BitVec.ofNat 64 (SharedRecover.Grind.recB lay.val + 16 - 8 * m)) =
      BitVec.ofNat 64 (ns.getD (height lay - 4 + m) 0)) ∧
    t.getMem (BitVec.ofNat 64 (SharedRecover.Grind.recB lay.val + 24)) = BitVec.ofNat 64 (2 ^ (height lay - 1) + leaf / 2) ∧
    t.getMem (BitVec.ofNat 64 (SharedRecover.Grind.recB lay.val + 256)) = BitVec.ofNat 64 (ns.getD (height lay - 5) 0)
def RlPairPost (s0 : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat)
    (res : (Digest × Digest) × List Nat) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC res.1.1 ∧ DigAt t (ENC + 48) res.1.2 ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval sig lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath sig lay j)) ∧
    RegsExcept s0 t rlRegs ∧
    Frame s0 t (fun A => ((RlScratch A ∨ RlWit lay (route index lay).1 WC WM A) ∨ A = ENC + 48 ∨ A = ENC + 56) ∨
      RecW lay A) ∧
    RecAt t lay (route index lay).1 res.2
/-- U16b: the lower-layer recovery with the fold nonces (`WCT9.recoverLayerPairW` body: `chainW`, `lowerLeafHash`
and the ground node `lowerNodeAt`), unfolded. -/
def recoverLayerPairNW (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    T3.M ((Digest × Digest) × List Nat) :=
  ((List.finRange (chainCount lay)).mapM fun i => ClaudeWCT.WCT9.chainW lay (route index lay).2 (route index lay).1
      i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)) >>=
    fun ends => ClaudeWCT.WCT9.lowerLeafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
      (List.finRange (height lay - 1)).foldlM (fun (st : Digest × List Nat) j => do
        let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
        let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (st.1, other) else (other, st.1)
        let r ← ClaudeWCT.WCT9.lowerNodeAt lay.val (route index lay).2
          (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1)) pair.1 pair.2
        pure (r.2, st.2 ++ [r.1])) (value, []) >>= fun st =>
        pure (if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0 then
          (st.1, (sig.layers lay).path (WCT9.topLevel lay)) else
          ((sig.layers lay).path (WCT9.topLevel lay), st.1), st.2)
/-- C2 + C3 (FULL): the lower-layer recovery of the current scheme (S23's `WCT9.recoverLayerPair` body, with
`chainW`, `lowerLeafHash` and `lowerNodeHash`), unfolded. -/
def recoverLayerPairN (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    T3.M (Digest × Digest) :=
  ((List.finRange (chainCount lay)).mapM fun i => ClaudeWCT.WCT9.chainW lay (route index lay).2 (route index lay).1
      i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)) >>=
    fun ends => ClaudeWCT.WCT9.lowerLeafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
      (List.finRange (height lay - 1)).foldlM (fun value j => do
        let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
        let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
        ClaudeWCT.WCT9.lowerNodeHash lay.val (route index lay).2
          (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1)) pair.1 pair.2) value >>= fun top =>
        pure (if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0 then
          (top, (sig.layers lay).path (WCT9.topLevel lay)) else
          ((sig.layers lay).path (WCT9.topLevel lay), top))
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open OracleComp SigGolfCandidate.T3
open ClaudeWCT
/-- U16b: `WCT9.recoverLayerPairW` has the body `recoverLayerPairNW` (`chainW`, `lowerLeafHash`, `lowerNodeAt`). -/
theorem recoverLayerPairW_eqN (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    WCT9.recoverLayerPairW sig index lay digits = SigGolfCandidate.T3M.Expand.recoverLayerPairNW sig index lay digits :=
  rfl
/-- img-v6: one layer of the expansion; the top layer re-derives its 11 node nonces (`WCT9.topFoldN`).
Result: message, folded top node (0 for lower layers) and the top nonces (U16b: the fold nonces on a lower layer). -/
def recoverMsg (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (WCT9.LayerMsg × Digest × List Nat) :=
  if lay = 0 then do
    let vn ← WCT9.topFoldN sig index digits
    let root ← WCT9.topNode index vn.1 (WCT9.topSib sig)
    pure (.forest root, vn.1, vn.2)
  else do
    let (pair, ns) ← WCT9.recoverLayerPairW sig index lay digits
    pure (.pair pair.1 pair.2, 0, ns)
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
def entryOf : Nat → Nat
  | 0 => 342
  | n + 1 => lE (Fin.ofNat 4 n)
theorem lR2_eq (n : Nat) (hn : n < 4) : lR2 (Fin.ofNat 4 n) = entryOf n := by
  interval_cases n <;> rfl
def SigLayersAt (s : MachineState) (sig : WCT9.Signature) : Prop :=
  ∀ lay : Layer, (∀ i (h : i < chainCount lay), DigAt s (lP lay + 16 * i) ((sig.layers lay).values ⟨i, h⟩)) ∧
    (∀ j (h : j < height lay), DigAt s (lP lay + 16 * chainCount lay + 16 * j) ((sig.layers lay).path ⟨j, h⟩))
structure LZero (s : MachineState) : Prop where
  c0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  c8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  e40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
structure LInv (sig : WCT9.Signature) (index n : Nat) (value : WCT9.LayerMsg) (s : MachineState) : Prop where
  pc : s.pc = pcOf (entryOf n)
  hn : n ≤ 4
  x5 : s.getReg .x5 = 0
  hidx : index < 2 ^ 31
  idx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt s ENC (Search.BC.left value)
  right : n ≠ 0 → DigAt s (ENC + 48) (Search.BC.right value)
  terminal : n = 0 → ∃ root, value = .forest root
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  sigl : SigLayersAt s sig
  z : LZero s
  table : Search.TableOK s
  cf : Search.CfTableOK 0 s
  reward : Search.Reward.RewardTablesOK s
def RlScratch (A : Nat) : Prop := Expand.RlScratch A ∨ A = ENC + 48 ∨ A = ENC + 56
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route chainCount height)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT
def RecoverPost (s0 : MachineState) (sig : WCT9.Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat)
    (mv : WCT9.LayerMsg × Digest × List Nat) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC (Search.BC.left mv.1) ∧
    (lay ≠ 0 → DigAt t (ENC + 48) (Search.BC.right mv.1)) ∧
    (lay = 0 → ∃ root, mv.1 = .forest root) ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval (WCT9.toT3Signature sig) lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath (WCT9.toT3Signature sig) lay j)) ∧
    RegsExcept s0 t rlRegs ∧ Frame s0 t (fun A => (RlScratch A ∨ RlWit lay (route index lay).1 WC WM A) ∨ RecW lay A) ∧
    (lay = 0 → TopBlkG (WCT9.toT3Signature sig) index lay mv.2.1 t) ∧
    (lay = 0 → NoncesAt t mv.2.2 (route index lay).1) ∧
    (lay ≠ 0 → RecAt t lay (route index lay).1 mv.2.2)
theorem topProg_eq (sig : WCT9.Signature) (index : Nat) (digits : List Nat) :
    (WCT9.topFoldN sig index digits >>= fun vn => WCT9.topNode index vn.1 (WCT9.topSib sig) >>= fun root =>
      pure (vn, root)) = topProg (WCT9.toT3Signature sig) index 0 digits (by decide) := by
  simp only [WCT9.topFoldN, WCT9.topEnds, bind_assoc]
  rfl
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
theorem rl_mk_finish {tc : MachineState} {sig : Signature} {lay : Layer} {tree leaf P WM j : Nat}
    {value : Digest} {u : MachineState} (hj : j < height lay) (hlow : lay ≠ 0) (hfinal : j + 1 = height lay) (htree : tree < 2 ^ 32) (hleaf : leaf < 2 ^ height lay)
    (hP0 : 0x7000 ≤ P) (hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hWM8 : WM % 8 = 0) (hWM : 0x800 + 64 * (height lay - 1) ≤ WM) (hWM' : WM + 64 ≤ 0x7000)
    (c5 : tc.getReg .x5 = 0) (c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val)
    (c9 : tc.getReg .x9 = BitVec.ofNat 64 tree) (c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf)
    (c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay))
    (cpath : DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j))
    (cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0) (cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (hI : MkInv tc sig lay leaf P WM j value u) (ret : Nat) (c1 : tc.getReg .x1 = pcOf ret) :
    ∃ t k, Steps im u k k t ∧ k ≤ 45 ∧ t.pc = pcOf ret ∧
      DigAt t ENC (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
      DigAt t (ENC + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value) ∧
      (∀ q < height lay, DigAt t (WM - 64 * q + sideOff leaf q) (lpath sig lay q)) ∧
      RegsExcept tc t mkRegs ∧
      Frame tc t (fun A => MkW lay leaf WM (height lay) A ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) ∧
      (∀ A, A < 2 ^ 64 → 0x700000 ≤ A → t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A)) := by
  have hH := height_le lay
  have hlay := lay.isLt
  have hleaf' : leaf < 2 ^ 12 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) hH)
  have g : ∀ r, r ∉ mkRegs → u.getReg r = tc.getReg r := fun r h => hI.regs.get h
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1076_spec (im := im) u hI.pc j (height lay) (by omega) (by omega) hI.x20
    (by rw [g _ (by decide)]; exact c15)
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ := rl1077_spec (im := im) t1 p1 leaf j (by omega) (by omega)
    (by rw [r1.get (by decide), g _ (by decide)]; exact c18) (by rw [r1.get (by decide)]; exact hI.x20)
  have fu2 : Frame u t2 (fun _ => False) := (f1.trans f2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u t2 [.x28] := (r1.trans r2).mono (by decide)
  have hpu : DigAt u (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) :=
    cpath.frame hI.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
      (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
  set P' := P + 16 * chainCount lay + 16 * j with hP'def
  set M := WM - 64 * j with hMdef
  have h22 : t2.getReg .x22 = BitVec.ofNat 64 P' := by rw [ru2.get (by decide)]; exact hI.x22
  have h24 : t2.getReg .x24 = BitVec.ofNat 64 M := by rw [ru2.get (by decide)]; exact hI.x24
  have hco := curOff_le lay leaf j
  have hval2 : DigAt t2 (NOUT + curOff lay leaf j) value :=
    hI.val.frame fu2 (by simp only [NOUT]; omega) (by simp) (by simp)
  have hpu2 : DigAt t2 P' (lpath sig lay j) := hpu.frame fu2 (by omega) (by simp) (by simp)
  have hn32 : t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT, RecW]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn32]
  have hn40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT, RecW]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn40]
  obtain ⟨t3, k3, s3, hk3, p3, nl, nr, wsib, r3, f3⟩ : ∃ t3 k3, Steps im t2 k3 k3 t3 ∧ k3 ≤ 22 ∧
      t3.pc = pcOf 1117 ∧
      DigAt t3 NODE (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
      DigAt t3 (NODE + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value) ∧
      DigAt t3 (M + sideOff leaf j) (lpath sig lay j) ∧
      RegsExcept t2 t3 [.x6, .x7, .x29, .x30] ∧
      Frame t2 t3 (fun A => A = M + sideOff leaf j ∨ A = M + sideOff leaf j + 8 ∨ A = NODE ∨ A = NODE + 8 ∨
        A = NODE + 48 ∨ A = NODE + 56) := by
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · rw [if_pos hb] at p2
      obtain ⟨t3, s3, p3, m48, m56, n0, n8, n48, n56, r3, f3⟩ := rl1099_spec (im := im) t2 p2 lay.val (by omega)
        (by rw [ru2.get (by decide), g _ (by decide)]; exact c8) P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 48 := by unfold sideOff; rw [if_neg (by omega)]
      have hc0 := curOff_bit0 lay hb hj
      refine ⟨t3, 22, s3, le_rfl, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_pos hb]; rw [hc0] at hval2; exact ⟨n0.trans hval2.1, n8.trans hval2.2⟩
      · rw [if_pos hb]; exact ⟨n48.trans hpu2.1, n56.trans hpu2.2⟩
      · rw [hso]; exact ⟨m48.trans hpu2.1, by rw [show M + 48 + 8 = M + 56 by omega]; exact m56.trans hpu2.2⟩
      · rw [hso]; exact f3
    · rw [if_neg hb] at p2
      obtain ⟨t3, s3, p3, m0, m8, n0, n8, n48, n56, r3, f3⟩ := rl1080_spec (im := im) t2 p2 P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 0 := by unfold sideOff; rw [if_pos (by omega)]
      have hval2 : DigAt t2 NOUT value := by
        have := hval2; rwa [curOff_bit1 lay hb, Nat.add_zero] at this
      refine ⟨t3, 19, s3, by omega, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_neg hb]; exact ⟨n0.trans hpu2.1, n8.trans hpu2.2⟩
      · rw [if_neg hb]; exact ⟨n48.trans hval2.1, n56.trans hval2.2⟩
      · rw [hso]; exact ⟨m0.trans hpu2.1, m8.trans hpu2.2⟩
      · rw [hso]; simpa using f3
  have g3' : RegsExcept tc t3 mkRegs := ((hI.regs.trans ru2).trans r3).mono (by decide)
  have g3 : ∀ r, r ∉ mkRegs → t3.getReg r = tc.getReg r := fun r h => g3'.get h
  have hz : BCBlocks.remaining t3 = 0 := by
    rw [bc_remaining hj hH (by rw [g3 _ (by decide)]; exact c15)
      (by rw [r3.get (by decide), ru2.get (by decide)]; exact hI.x20)]
    rw [show height lay - j - 1 = 0 by omega]; rfl
  have hl : t3.getReg .x8 ≠ 0 := by
    rw [g3 _ (by decide), c8]
    intro he
    have hv := congrArg BitVec.toNat he
    change lay.val % 2 ^ 64 = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    exact hlow (Fin.ext hv)
  obtain ⟨t, st, pt, m0, m8, m48, m56, rt, ft⟩ := BCBlocks.finish_spec (im := im) t3 p3 ret hz hl
    (by rw [g3 _ (by decide)]; exact c1)
  refine ⟨t, 1 + 3 + k3 + 18, ((s1.trans s2).trans s3).trans st, by omega, pt,
    ⟨m0.trans nl.1, m8.trans nl.2⟩, ⟨m48.trans nr.1, m56.trans nr.2⟩, ?_, ?_, ?_, ?_⟩
  rotate_left 3
  · intro A hA hA7
    rw [ft.get hA (by simp only [BCBlocks.ENC]; omega), f3.get hA (by
      have := sideOff_le leaf j
      have hMb : M ≤ WM := by rw [hMdef]; exact Nat.sub_le _ _
      simp only [NODE]; omega), fu2.get hA (fun h => h)]
  rotate_right 3
  · intro q hq
    have hs := sideOff_le leaf q
    by_cases he : q = j
    · subst q
      exact wsib.frame ft (by omega) (by simp only [BCBlocks.ENC]; omega) (by simp only [BCBlocks.ENC]; omega)
    · have hqj : q < j := by omega
      have hw := hI.wit q hqj
      have hs2 := sideOff_le leaf j
      have hne : WM - 64 * q + sideOff leaf q + 16 ≤ M + sideOff leaf j ∨ M + 64 ≤ WM - 64 * q + sideOff leaf q := by
        unfold sideOff at hs hs2 ⊢; split_ifs <;> omega
      exact ((hw.frame fu2 (by omega) (by simp) (by simp)).frame f3 (by omega)
        (by simp only [NODE]; omega) (by simp only [NODE]; omega)).frame ft (by omega)
        (by simp only [BCBlocks.ENC]; omega) (by simp only [BCBlocks.ENC]; omega)
  · exact (g3'.trans rt).mono (by decide)
  · have fall := ((hI.frame.trans fu2).trans f3).trans ft
    refine fall.mono (fun A hA h => ?_)
    rcases h with ((h | h) | h) | h
    · left
      unfold MkW at h
      rcases h with h | h | h | h | h | h | h | ⟨q, hq, hqv⟩ | h
      all_goals first
        | exact mkW_of (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
        | exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
        | exact mkW_wit (by omega) hqv
    · exact h.elim
    · left
      rcases h with h | h | h | h | h | h
      · exact mkW_wit hj (Or.inl h)
      · exact mkW_wit hj (Or.inr h)
      all_goals exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
    · exact Or.inr h

/-- U16b: the lower climb invariant: `MkInv` plus the fold nonces so far and the stub's record of them. -/
def LowInv (tc : MachineState) (sig : Signature) (lay : Layer) (leaf P WM : Nat) (j : Nat) (acc : Digest × List Nat)
    (w : MachineState) : Prop :=
  MkInv tc sig lay leaf P WM j acc.1 w ∧ acc.2.length = j ∧
    (∀ k < j, ClaudeWCT.WCT9.lowerZeroBits lay.val (2 ^ (height lay - k - 1) + leaf / 2 ^ (k + 1)) ≠ 0 →
      w.getMem (BitVec.ofNat 64 (Grind.recA lay.val (2 ^ (height lay - k - 1) + leaf / 2 ^ (k + 1)))) =
        BitVec.ofNat 64 (acc.2.getD k 0)) ∧
    (0 < j → w.getMem (BitVec.ofNat 64 (Grind.recB lay.val + 24)) = BitVec.ofNat 64 (2 ^ (height lay - 1) + leaf / 2))
theorem ground_e (lay e heap : Nat) (c1 : 2 ^ e ≤ heap) (hg : ClaudeWCT.WCT9.lowerZeroBits lay heap ≠ 0) : e ≤ 4 := by
  have h16 : heap < 32 := by
    unfold ClaudeWCT.WCT9.lowerZeroBits at hg; split_ifs at hg <;> omega
  by_contra hc
  have : 2 ^ 5 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega
theorem recA_ne_of_class (lay e e' : Nat) (hne : e ≠ e') (h3 : e ≤ 4) (h3' : e' ≤ 4) (h1 : 1 ≤ e) (h1' : 1 ≤ e')
    {h h' : Nat} (c1 : 2 ^ e ≤ h) (c2 : h < 2 ^ (e + 1)) (c3 : 2 ^ e' ≤ h') (c4 : h' < 2 ^ (e' + 1)) :
    Grind.recA lay h ≠ Grind.recA lay h' := by
  unfold Grind.recA
  interval_cases e <;> interval_cases e' <;> simp only [Nat.reducePow, Nat.reduceAdd, pow_one] at c1 c2 c3 c4 ⊢ <;>
    first | (exfalso; omega) | (split_ifs <;> omega)

theorem recoverLayerPair_tbsim {sk : BitVec 256} {s0 : MachineState} {wsig : WCT9.Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 (WCT9.toT3Signature wsig) index lay digits P WC WM ret) (hlow : lay ≠ 0) :
    TBSim im sk s0 (rlCost lay) (recoverLayerPairNW wsig index lay digits)
      (RlPairPost s0 (WCT9.toT3Signature wsig) index lay WC WM ret) := by
  let sig := WCT9.toT3Signature wsig
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
  have htrH : lay.val ≠ 0 → tree < 2 ^ T3.hyperW (lay.val - 1) := fun h0 => LH.route_tree_honest index hpre.hidx lay h0
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hN := chainCount_cases' lay
  have hlay := lay.isLt
  have hPb := hpre.hP'
  have hWC := hpre.hWC
  have hWMC := hpre.hWMC
  have hWM := hpre.hWM
  have hP0 := hpre.hP
  obtain ⟨t1, st1, p1, x19, l16, l24, -, r1, f1⟩ := rl997_spec (im := im) s0 hpre.pc lay tree leaf
    (by have := SigGolfCandidate.T3M.LH.route_honest index hpre.hidx lay; dsimp [tree, leaf]; exact this)
    hpre.x8 hpre.x9 hpre.x18 hpre.x15
  have f1g : ∀ A, A < 2 ^ 64 → A ≠ LEAFPK → A ≠ LEAFPK + 8 → A ≠ LEAFPK + 16 → A ≠ LEAFPK + 24 →
      t1.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 h3 h4 => f1.get hA (by rintro (h | h | h | h) <;> contradiction)
  have hI0 : ChainsInv t1 lay tree leaf P WC (chainCount lay) (csN4 lay) (lval sig lay) [] t1 := by
    refine ⟨p1, ⟨?_, ?_, ?_, ?_, x19, ?_, ?_⟩, ?_, fun j hj => absurd hj (by simp), fun j hj => absurd hj (by simp),
      RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [r1.get (by decide), hpre.x5]
    · rw [r1.get (by decide), hpre.x8]
    · rw [r1.get (by decide), hpre.x9]
    · rw [r1.get (by decide), hpre.x18]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide) (by decide), hpre.c0]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide) (by decide), hpre.c8]
    · rw [r1.get (by decide), hpre.x23]; simp
  unfold recoverLayerPairNW
  refine (TBSim.steps st1 (TBSim.bind (W₂ := 10 + 8 * leafBlocks' lay + 13 + climbW lay)
    (rl_chains (im := im) (sk := sk) hpre r1 f1 hI0) (fun ends u hu => ?_))).mono (by unfold rlCost; omega) (fun _ _ h => h)
  obtain ⟨hlen, hC⟩ := hu
  have hN58 : chainCount lay ≤ 58 := by omega
  obtain ⟨v1, sv1, pv1, rv1, fv1⟩ := rl1010_spec (im := im) u hC.pc (chainCount lay) (chainCount lay) (by omega) (by omega)
    (by rw [hC.ctx.x19, hlen]) (by rw [hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  rw [if_pos (le_refl _)] at pv1
  obtain ⟨v2, sv2, pv2, h10, h11, h12, rv2, fv2⟩ := rl1063_spec (im := im) v1 pv1 (chainCount lay) (by omega)
    (by rw [rv1.get (by decide), hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  have fu2 : Frame u v2 (fun _ => False) := (fv1.trans fv2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u v2 [.x6, .x10, .x11, .x12] := (rv1.trans rv2).mono (by decide)
  have fs2 : Frame s0 v2 (fun A => ((A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨
      ChW lay WC ends.length A) ∨ False) := (f1.trans hC.frame).trans fu2
  have hn43 : chainCount lay = 43 := chainCount_ne0 lay hlow
  have hhd16 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inl rfl) (by omega)), l16]
  have hhd24 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inr rfl) (by omega)), l24]
  have hw : v2.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks' lay) =
      wordsOf (pad64 (T3.leafInput lay tree leaf ends)) := by
    rw [leafInput_words' lay tree leaf ends hlen]
    have h0 : DigAt v2 LEAFPK (ends.getD 0 0) := by
      have := (hC.slots 0 (by omega)).frame fu2 (by simp only [slotOff, if_neg hlow]; decide) (by simp) (by simp)
      simpa [slotOff, hlow] using this
    have hrest : DigsAt v2 (LEAFPK + 32) (ends.drop 1) := by
      intro c hc
      simp only [List.length_drop] at hc
      have := (hC.slots (c + 1) (by omega)).frame fu2 (by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega)
        (by simp) (by simp)
      simp only [slotOff, if_neg hlow, if_neg (show c + 1 ≠ 0 by omega)] at this
      rw [show LEAFPK + 32 + 16 * c = LEAFPK + (16 * (c + 1) + 16) by ring]
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
    have hhd : v2.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [T3.hyperWord lay.val (tree * 2 ^ height lay + leaf), 0] := by
      rw [readWords_two, hhd16, show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, hhd24]
    have hb : 8 * leafBlocks' lay = 2 + (2 + 2 * (ends.drop 1).length) := by
      simp only [List.length_drop, hlen, leafBlocks', hn43]
    rw [hb, readWords_add, readWords_add, h0.words, hhd, hrest.words]
    simp only [List.append_assoc]
  have hl := leafInput_length' lay tree leaf ends hlen
  have hB : 1 ≤ leafBlocks' lay := by rcases leafBlocks'_cases lay with h | h <;> omega
  have h11' : v2.getReg .x11 = BitVec.ofNat 64 (64 * leafBlocks' lay) := by
    rw [h11]; unfold leafBlocks'; congr 1; omega
  have hq : hashInput v2 = toQ (pad64 (T3.leafInput lay tree leaf ends)) := by
    refine hashInput_toQ v2 _ (leafBlocks' lay - 1) LEAFPK (by rw [hl]; congr 1; omega) h10 (by decide) (by decide)
      (by rw [h11']; congr 2; omega) (by rcases leafBlocks'_cases lay with h | h <;> omega)
      (by rw [show 8 * (leafBlocks' lay - 1 + 1) = 8 * leafBlocks' lay by omega]; exact hw)
  have hblk : (toQ (pad64 (T3.leafInput lay tree leaf ends))).blocks = leafBlocks' lay := by
    rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
  have hv : hashArgumentsValid v2 = true :=
    hashArgs_const v2 LEAFPK (64 * leafBlocks' lay) NOUT h10 h11' h12 (by decide)
      (by rcases leafBlocks'_cases lay with h | h <;> omega) (by rcases leafBlocks'_cases lay with h | h <;>
        simp only [LEAFPK] <;> omega) (by decide) (by decide)
  have rs2 : RegsExcept s0 v2 oneRegs := ((r1.trans hC.regs).trans ru2).mono (by decide)
  have h5 : v2.getReg .x5 = 0 := by rw [rs2.get (by decide), hpre.x5]
  rw [ClaudeWCT.WCT9.lowerLeafHash_eq]
  unfold ClaudeWCT.WCT9.lowerHash
  refine (TBSim.steps (sv1.trans sv2) (tb_halfHash_bind' (im := im) (W := 13 + climbW lay) _ (fetch_1072 (im := im) v2 pv2) h5 hv hq
    (fun a => ?_))).mono (by rw [hblk]; omega) (fun _ _ h => h)
  set tc := writeHash v2 a with htc
  have pc3 : tc.pc = pcOf 1073 := by rw [htc, pc_writeHash, pv2, pcOf_add4]
  have rtc : RegsExcept s0 tc oneRegs := fun r hr => by rw [htc, getReg_writeHash]; exact rs2 r hr
  have fwc := Frame.writeHash v2 a NOUT h12 (by decide)
  have ftc : Frame s0 tc (fun A => (((A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨
      ChW lay WC ends.length A) ∨
      False) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) := fs2.trans fwc
  have hfar' : ∀ A, A < 2 ^ 64 → WC + 64 ≤ A → (A < CHAIN ∨ CHAIN + 112 ≤ A) → (A < LEAFPK ∨ LEAFPK + 960 ≤ A) →
      (A < NOUT ∨ NOUT + 32 ≤ A) → tc.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    refine ftc.get hA ?_
    rintro (((h | h) | h) | h)
    · simp only [CHAIN, LEAFPK] at h h2 h3; omega
    · exact not_ChW_of (by omega) h1 (by simp only [CHAIN] at h2 ⊢; omega) (by simp only [LEAFPK] at h3 ⊢; omega) h
    · exact h
    · simp only [NOUT] at h h4; omega
  obtain ⟨v4, sv4, pv4, x20, x22, rv4, fv4⟩ := rl1073_spec (im := im) tc pc3 P (chainCount lay) (by omega)
    (by rw [rtc.get (by decide), hpre.x16]) (by rw [rtc.get (by decide), hpre.x26])
  have hM0 : MkInv tc sig lay leaf P WM 0 (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay.val leaf) a) v4 := by
    refine ⟨pv4, x20, by rw [x22]; congr 1, ?_, by omega, ?_, fun j hj => absurd hj (by omega), rv4.mono (by decide),
      fv4.mono (fun _ _ h => h.elim)⟩
    · rw [rv4.get (by decide), rtc.get (by decide), hpre.x24]; congr 1
    · rw [curOff_zero]
      exact (digAt_half v2 a NOUT h12 (by decide) _).frame fv4 (by split_ifs <;> decide) (by simp) (by simp)
  have c5 : tc.getReg .x5 = 0 := by rw [rtc.get (by decide), hpre.x5]
  have c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [rtc.get (by decide), hpre.x8]
  have c9 : tc.getReg .x9 = BitVec.ofNat 64 tree := by rw [rtc.get (by decide), hpre.x9]
  have c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf := by rw [rtc.get (by decide), hpre.x18]
  have c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay) := by rw [rtc.get (by decide), hpre.x15]
  have cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n32]
  have cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n40]
  have cpath : ∀ j < height lay, DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) := by
    intro j hj
    have hp := hpre.path j hj
    have e : lpath sig lay j = (sig.layers lay).path ⟨j, hj⟩ := by unfold lpath; rw [dif_pos hj]
    rw [e]
    exact ⟨(hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega)
      (by simp only [NOUT]; omega)).trans hp.1, (hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega)
      (by simp only [LEAFPK]; omega) (by simp only [NOUT]; omega)).trans hp.2⟩
  have hH7 : height lay ≤ 7 := by fin_cases lay <;> simp_all [height]
  have hH6 : 6 ≤ height lay := by fin_cases lay <;> simp_all [height]
  have hlv : lay.val ≠ 0 := fun h => hlow (Fin.ext h)
  have hl1 : 1 ≤ lay.val := by omega
  have hl3 : lay.val ≤ 3 := by omega
  have hthr : Grind.recThr lay.val = 2 ^ (height lay - 1) := by
    unfold Grind.recThr; fin_cases lay <;> simp_all [height]
  -- heap of fold `k`: `2 ^ (H - k - 1) ≤ heap < 2 ^ (H - k)`
  have hheapk : ∀ k, k < height lay - 1 → 2 ^ (height lay - k - 1) ≤ 2 ^ (height lay - k - 1) + leaf / 2 ^ (k + 1) ∧
      2 ^ (height lay - k - 1) + leaf / 2 ^ (k + 1) < 2 ^ (height lay - k - 1 + 1) := by
    intro k hk
    have e : 2 ^ height lay = 2 ^ (k + 1) * 2 ^ (height lay - k - 1) := by rw [← Nat.pow_add]; congr 1; omega
    have hq : leaf / 2 ^ (k + 1) < 2 ^ (height lay - k - 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e]; exact hleaf
    have h2 : 2 ^ (height lay - k - 1 + 1) = 2 ^ (height lay - k - 1) * 2 := Nat.pow_succ 2 _
    rw [h2]
    generalize leaf / 2 ^ (k + 1) = Y at hq ⊢
    generalize 2 ^ (height lay - k - 1) = X at hq ⊢
    omega
  have hfold := tb_foldlM_valsW (im := im) (sk := sk)
    (fun (st : Digest × List Nat) (j : Fin (height lay - 1)) => do
      let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
      let pair := if leaf / 2 ^ j.val % 2 = 0 then (st.1, other) else (other, st.1)
      let r ← ClaudeWCT.WCT9.lowerNodeAt lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2
      pure (r.2, st.2 ++ [r.1])) (lowFoldW lay) (LowInv tc sig lay leaf P WM) (height lay - 1)
    (fun i acc w hi hw => by
      obtain ⟨hI, hlen, hrec, h24⟩ := hw
      refine TBSim.bind (W₂ := 0) ((rl_mk_stepL (im := im) (sk := sk) (by omega) (Or.inl (by omega)) htree htrH hleaf
        hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM (by omega) c5 c8 c9 c18 c15 (cpath i.val (by omega)) cn32 cn40 hI
        (Or.inl hlow) hlow (by omega)).mono le_rfl (fun _ _ h => h)) (fun r w' h => TBSim.pure ⟨h.1, ?_, ?_, ?_⟩)
        |>.mono (by omega) (fun _ _ h => h)
      · simp [hlen]
      · intro k hk hg
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · obtain ⟨c1, c2⟩ := hheapk k (by omega)
          obtain ⟨c3, c4⟩ := hheapk i.val (by omega)
          rw [h.2.2.2.2.2 (Grind.recA lay.val (2 ^ (height lay - k - 1) + leaf / 2 ^ (k + 1)))
            (by have := Grind.recA_cases lay.val (2 ^ (height lay - k - 1) + leaf / 2 ^ (k + 1)) hl1 hl3; omega)
            ⟨hlv, by unfold Grind.recA Grind.recB; split_ifs <;> omega⟩
            (fun ⟨hg', he⟩ => recA_ne_of_class lay.val (height lay - k - 1) (height lay - i.val - 1) (by omega)
              (ground_e lay.val _ _ c1 hg) (ground_e lay.val _ _ c3 hg') (by omega) (by omega) c1 c2 c3 c4 he)
            (fun ⟨_, he⟩ => Grind.recA_cases lay.val _ hl1 hl3 |>.2.2.2 he),
            hrec k hk hg, List.getD_append _ _ _ _ (by omega)]
        · rw [h.2.2.2.1 hg, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]; rfl
      · intro hpos
        obtain ⟨c3, c4⟩ := hheapk i.val (by omega)
        by_cases h0 : i.val = 0
        · rw [h.2.2.2.2.1 (by rw [hthr, h0, Nat.sub_zero]; omega)]
          rw [h0]; simp
        · rw [h.2.2.2.2.2 (Grind.recB lay.val + 24) (by unfold Grind.recB; omega)
            ⟨hlv, Or.inl ⟨by unfold Grind.recB; omega, by unfold Grind.recB; omega⟩⟩
            (fun ⟨_, he⟩ => (Grind.recA_cases lay.val _ hl1 hl3).2.2.2 he.symm)
            (fun ⟨hth, _⟩ => by
              rw [hthr] at hth
              have : 2 ^ (height lay - i.val - 1 + 1) ≤ 2 ^ (height lay - 1) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              omega), h24 (by omega)])
    (List.finRange (height lay - 1)) 0 (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay.val leaf) a, []) v4
    (by rw [finRange_map_val]; simp) (by simp)
    ⟨hM0, rfl, fun k hk => absurd hk (by omega), fun h => absurd h (by omega)⟩
  have hHp : 0 < height lay := by fin_cases lay <;> decide
  simp only [List.length_finRange, Nat.zero_add] at hfold
  have hcw : climbW lay = ((List.range' 0 (height lay - 1)).map (lowFoldW lay)).sum + 81 := by
    unfold climbW; rw [if_neg hlow]
  refine (TBSim.steps sv4 (TBSim.bind (W₂ := 45) hfold (fun st w hw => ?_))).mono (by omega) (fun _ _ h => h)
  obtain ⟨hwI, hwlen, hwrec, hw24⟩ := hw
  obtain ⟨t, k, st, hk, pt, pl, pr, pwi, rt, ft, ftu⟩ := rl_mk_finish (im := im) (by omega) hlow (by omega)
    htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM (by omega)
    c5 c8 c9 c18 c15 (cpath (height lay - 1) (by omega)) cn32 cn40 hwI ret
    (by rw [rtc.get (by decide)]; exact hpre.x1)
  have hpath : lpath sig lay (height lay - 1) = (wsig.layers lay).path (WCT9.topLevel lay) := by
    unfold lpath
    rw [dif_pos (by omega)]
    rfl
  -- the finish (BC blocks) does not touch the record slots
  have ftR : ∀ A, A < 2 ^ 64 → RecW lay A → t.getMem (BitVec.ofNat 64 A) = w.getMem (BitVec.ofNat 64 A) :=
    fun A hA hR => ftu A hA (by unfold RecW at hR; omega)
  refine (TBSim.steps st (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  refine ⟨pt, ?_, ?_, ?_, pwi, (rtc.trans rt).mono (by decide), ?_, ?_⟩
  · simpa only [hpath, hleaf_def, apply_ite Prod.fst, Prod.fst] using pl
  · simpa only [hpath, hleaf_def, apply_ite Prod.snd, Prod.snd] using pr
  · intro i hi
    have hv := hC.wvals i (by omega)
    have hWi : WM + 64 ≤ WC - 64 * i + 48 := by omega
    exact (((hv.frame fu2 (by omega) (by simp) (by simp)).frame fwc (by omega)
      (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)).frame ft (by omega)
      (by rintro (h | h); exact not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega) (by omega) (by omega) h; simp only [ENC] at h; omega)
      (by rintro (h | h); exact not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega) (by omega) (by omega) h; simp only [ENC] at h; omega))
  · refine (ftc.trans ft).mono (fun A hA h => ?_)
    by_cases hR : RecW lay A
    · exact Or.inr hR
    refine Or.inl ?_
    rcases h with (((hX | hC) | hF) | hN) | hT
    · left; left
      unfold RlScratch
      rcases hX with h | h | h | h <;> simp only [CHAIN, LEAFPK] at h ⊢ <;> omega
    · unfold ChW StepW at hC
      rcases hC with (h | h) | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · left; left; unfold RlScratch; omega
      · left; left; unfold RlScratch; omega
      · have hlt := slotOff_lt lay (show c < chainCount lay by omega)
        left; left; unfold RlScratch; simp only [LEAFPK] at h ⊢; omega
      · left; right; left; exact ⟨c, by omega, h⟩
    · exact hF.elim
    · left; left; unfold RlScratch; omega
    · rcases hT with hM | hE
      · unfold MkW at hM
        rcases hM with h | h | h | h | h | h | h | ⟨j, hj, h⟩ | h
        all_goals first
          | (rcases h with h | h | h <;> first | (left; left; unfold RlScratch; omega) | exact absurd h hR)
          | (left; left; unfold RlScratch; omega) | (left; right; right; exact ⟨j, hj, h⟩)
      · unfold RlScratch
        simp only [ENC] at hE
        simp only [ENC]
        omega
  · -- the record of the four ground folds and the fold-0 heap
    refine ⟨by simpa using hwlen, fun m hm => ?_, ?_, ?_⟩
    · obtain ⟨c1, c2⟩ := hheapk (height lay - 4 + m) (by omega)
      have hcl : height lay - (height lay - 4 + m) - 1 = 3 - m := by omega
      rw [hcl] at c1 c2
      have hrA : Grind.recA lay.val (2 ^ (height lay - (height lay - 4 + m) - 1) + leaf / 2 ^ (height lay - 4 + m + 1)) =
          Grind.recB lay.val + 16 - 8 * m := by
        rw [hcl]; unfold Grind.recA
        interval_cases m <;> simp only [Nat.reducePow, Nat.reduceSub] at c1 c2 ⊢ <;> split_ifs <;> omega
      have hg : ClaudeWCT.WCT9.lowerZeroBits lay.val
          (2 ^ (height lay - (height lay - 4 + m) - 1) + leaf / 2 ^ (height lay - 4 + m + 1)) ≠ 0 := by
        rw [hcl]; unfold ClaudeWCT.WCT9.lowerZeroBits
        interval_cases m <;> simp only [Nat.reducePow, Nat.reduceSub] at c1 c2 ⊢ <;> split_ifs <;> omega
      have := hwrec (height lay - 4 + m) (by omega) hg
      rw [hrA] at this
      rw [ftR _ (by unfold Grind.recB; omega) ⟨hlv, Or.inl ⟨by unfold Grind.recB; omega, by unfold Grind.recB; omega⟩⟩, this]
    · rw [ftR _ (by unfold Grind.recB; omega) ⟨hlv, Or.inl ⟨by unfold Grind.recB; omega, by unfold Grind.recB; omega⟩⟩,
        hw24 (by omega)]
    · obtain ⟨c1, c2⟩ := hheapk (height lay - 5) (by omega)
      have hcl : height lay - (height lay - 5) - 1 = 4 := by omega
      rw [hcl] at c1 c2
      have hrA : Grind.recA lay.val (2 ^ (height lay - (height lay - 5) - 1) + leaf / 2 ^ (height lay - 5 + 1)) =
          Grind.recB lay.val + 256 := by
        rw [hcl]; unfold Grind.recA; simp only [Nat.reducePow, Nat.reduceAdd] at c1 c2 ⊢; split_ifs <;> omega
      have hg : ClaudeWCT.WCT9.lowerZeroBits lay.val
          (2 ^ (height lay - (height lay - 5) - 1) + leaf / 2 ^ (height lay - 5 + 1)) ≠ 0 := by
        rw [hcl]; unfold ClaudeWCT.WCT9.lowerZeroBits; simp only [Nat.reducePow, Nat.reduceAdd] at c1 c2 ⊢
        split_ifs <;> omega
      have := hwrec (height lay - 5) (by omega) hg
      rw [hrA] at this
      rw [ftR _ (by unfold Grind.recB; omega) ⟨hlv, Or.inr (by unfold Grind.recB; omega)⟩, this]

theorem recoverMsg_tbsim {sk : BitVec 256} {s0 : MachineState} {sig : WCT9.Signature} {index : Nat} {lay : Layer}
    {digits : List Nat} {P WC WM ret : Nat}
    (hpre : RlPre s0 (WCT9.toT3Signature sig) index lay digits P WC WM ret) :
    TBSim im sk s0 (rlCost lay) (recoverMsg sig index lay digits) (RecoverPost s0 sig index lay WC WM ret) := by
  unfold recoverMsg
  split_ifs with ht
  · subst ht
    have hprog : (do
        let vn ← WCT9.topFoldN sig index digits
        let root ← WCT9.topNode index vn.1 (WCT9.topSib sig)
        pure (WCT9.LayerMsg.forest root, vn.1, vn.2)) =
        (fun r : (Digest × List Nat) × Digest => (WCT9.LayerMsg.forest r.2, r.1.1, r.1.2)) <$>
          topProg (WCT9.toT3Signature sig) index 0 digits (by decide) := by
      rw [← topProg_eq]
      simp only [map_bind, map_pure]
    rw [hprog, map_eq_bind_pure_comp]
    refine (TBSim.bind (W₂ := 0) (recoverTop_tbsim (im := im) hpre rfl (by decide)) (fun r t h => ?_)).mono (by omega)
      (fun _ _ h => h)
    obtain ⟨⟨pc, enc, cv, pv, regs, frame⟩, blk, non⟩ := h
    refine TBSim.pure ⟨pc, enc, (fun hn => False.elim (hn rfl)), (fun _ => ⟨r.2, rfl⟩), cv, pv, regs, ?_,
      fun _ => blk, fun _ => non, fun hne => absurd rfl hne⟩
    exact frame.mono (by intro A hA h; rcases h with h | h; exact Or.inl (Or.inl (Or.inl h)); exact Or.inl (Or.inr h))
  · rw [recoverLayerPairW_eqN]
    refine (TBSim.bind (W₂ := 0) (recoverLayerPair_tbsim (im := im) hpre ht) (fun res t h => ?_)).mono (by omega)
      (fun _ _ h => h)
    rcases res with ⟨pair, ns⟩
    obtain ⟨pc, enc, right, cv, pv, regs, frame, recat⟩ := h
    refine TBSim.pure ⟨pc, enc, (fun _ => right), (fun he => False.elim (ht he)), cv, pv, regs, ?_,
      fun he => False.elim (ht he), fun he => False.elim (ht he), fun _ => recat⟩
    exact frame.mono (by
      intro A hA h
      rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h)

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

section
variable {im : Image} (hc : Code im)
include hc
end
end ClaudeWCT.W9.Machine.Expand.PairCopy
end
