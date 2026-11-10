import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge076
import SigGolfCandidate.Merge077

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
def RlPairPost (s0 : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat)
    (pair : Digest × Digest) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC pair.1 ∧ DigAt t (ENC + 48) pair.2 ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval sig lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath sig lay j)) ∧
    RegsExcept s0 t rlRegs ∧
    Frame s0 t (fun A => (RlScratch A ∨ RlWit lay (route index lay).1 WC WM A) ∨ A = ENC + 48 ∨ A = ENC + 56)
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
/-- C2 + C3 (FULL): `WCT9.recoverLayerPair` has the C2 + C3 body (`chainW`, `lowerLeafHash`, `lowerNodeHash`). -/
theorem recoverLayerPair_eqN (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    WCT9.recoverLayerPair sig index lay digits = SigGolfCandidate.T3M.Expand.recoverLayerPairN sig index lay digits :=
  rfl
/-- img-v6: one layer of the expansion; the top layer re-derives its 11 node nonces (`WCT9.topFoldN`).
Result: message, folded top node (0 for lower layers) and the top nonces ([] for lower layers). -/
def recoverMsg (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    M (WCT9.LayerMsg × Digest × List Nat) :=
  if lay = 0 then do
    let vn ← WCT9.topFoldN sig index digits
    let root ← WCT9.topNode index vn.1 (WCT9.topSib sig)
    pure (.forest root, vn.1, vn.2)
  else do
    let pair ← WCT9.recoverLayerPair sig index lay digits
    pure (.pair pair.1 pair.2, 0, [])
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
def HalfAt (t : MachineState) (D k : Nat) (v : BitVec 32) : Prop :=
  (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = v
def HalfFrame (s t : MachineState) (n : Nat) : Prop :=
  ∀ D k, (D = 0x3ce8 ∨ D = 0x4968 ∨ D = 0x55a8 ∨ D = 0x820 ∨ D = 0x810 ∨ D = 0x818) → k < 2 → (∀ lay : Layer, lay.val < n → ¬ (lD lay = D ∧ lk lay = k)) →
    (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = (s.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32
def lRegs : List Reg :=
  [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
    .x25, .x26, .x27, .x28, .x29, .x30, .x31]
def RlScratch (A : Nat) : Prop := Expand.RlScratch A ∨ A = ENC + 48 ∨ A = ENC + 56
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
def RecoverPost (s0 : MachineState) (sig : WCT9.Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat)
    (mv : WCT9.LayerMsg × Digest × List Nat) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC (Search.BC.left mv.1) ∧
    (lay ≠ 0 → DigAt t (ENC + 48) (Search.BC.right mv.1)) ∧
    (lay = 0 → ∃ root, mv.1 = .forest root) ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval (WCT9.toT3Signature sig) lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath (WCT9.toT3Signature sig) lay j)) ∧
    RegsExcept s0 t rlRegs ∧ Frame s0 t (fun A => RlScratch A ∨ RlWit lay (route index lay).1 WC WM A) ∧
    (lay = 0 → TopBlkG (WCT9.toT3Signature sig) index lay mv.2.1 t) ∧
    (lay = 0 → NoncesAt t mv.2.2 (route index lay).1)
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
      Frame tc t (fun A => MkW leaf WM (height lay) A ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
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
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn32]
  have hn40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
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
    ⟨m0.trans nl.1, m8.trans nl.2⟩, ⟨m48.trans nr.1, m56.trans nr.2⟩, ?_, ?_, ?_⟩
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
        | exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
        | exact mkW_wit (by omega) hqv
    · exact h.elim
    · left
      rcases h with h | h | h | h | h | h
      · exact mkW_wit hj (Or.inl h)
      · exact mkW_wit hj (Or.inr h)
      all_goals exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
    · exact Or.inr h

theorem recoverLayerPair_tbsim {sk : BitVec 256} {s0 : MachineState} {wsig : WCT9.Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 (WCT9.toT3Signature wsig) index lay digits P WC WM ret) (hlow : lay ≠ 0) :
    TBSim im sk s0 (rlCost lay) (recoverLayerPairN wsig index lay digits)
      (RlPairPost s0 (WCT9.toT3Signature wsig) index lay WC WM ret) := by
  let sig := WCT9.toT3Signature wsig
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
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
    (by have hidx := hpre.hidx; dsimp [tree, leaf]; fin_cases lay <;> norm_num [route, height] at * <;> omega)
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
  unfold recoverLayerPairN
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
  have hfold := tb_foldlM_finRange (image := im) (sk := sk) (height lay - 1)
    (fun value j => do
      let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
      let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      ClaudeWCT.WCT9.lowerNodeHash lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2)
    (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.lowerHigh lay.val leaf) a) 81
    (fun j value w => MkInv tc sig lay leaf P WM j value w)
    (fun i acc w hw => (rl_mk_step (im := im) (by omega) (Or.inl (by omega)) htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM (by omega)
      c5 c8 c9 c18 c15 (cpath i.val (by omega)) cn32 cn40 hw (Or.inl hlow)).mono le_rfl (fun _ _ h => h.1)) hM0
  have hHp : 0 < height lay := by fin_cases lay <;> decide
  have hcw : climbW lay = height lay * 81 := by unfold climbW; rw [if_neg hlow]
  refine (TBSim.steps sv4 (TBSim.bind (W₂ := 45) hfold (fun root w hw => ?_))).mono (by omega) (fun _ _ h => h)
  obtain ⟨t, k, st, hk, pt, pl, pr, pwi, rt, ft⟩ := rl_mk_finish (im := im) (by omega) hlow (by omega)
    htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM (by omega)
    c5 c8 c9 c18 c15 (cpath (height lay - 1) (by omega)) cn32 cn40 hw ret
    (by rw [rtc.get (by decide)]; exact hpre.x1)
  have hpath : lpath sig lay (height lay - 1) = (wsig.layers lay).path (WCT9.topLevel lay) := by
    unfold lpath
    rw [dif_pos (by omega)]
    rfl
  refine (TBSim.steps st (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  refine ⟨pt, ?_, ?_, ?_, pwi, (rtc.trans rt).mono (by decide), ?_⟩
  · simpa only [hpath, hleaf_def, apply_ite Prod.fst, Prod.fst] using pl
  · simpa only [hpath, hleaf_def, apply_ite Prod.snd, Prod.snd] using pr
  · intro i hi
    have hv := hC.wvals i (by omega)
    have hWi : WM + 64 ≤ WC - 64 * i + 48 := by omega
    exact (((hv.frame fu2 (by omega) (by simp) (by simp)).frame fwc (by omega)
      (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)).frame ft (by omega)
      (by rintro (h | h); exact not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega) (by omega) h; simp only [ENC] at h; omega)
      (by rintro (h | h); exact not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega) (by omega) h; simp only [ENC] at h; omega))
  · refine (ftc.trans ft).mono (fun A hA h => ?_)
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
        all_goals first | (left; left; unfold RlScratch; omega) | (left; right; right; exact ⟨j, hj, h⟩)
      · unfold RlScratch
        simp only [ENC] at hE
        simp only [ENC]
        omega

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
      fun _ => blk, fun _ => non⟩
    exact frame.mono (by intro A hA h; rcases h with h | h; exact Or.inl (Or.inl h); exact Or.inr h)
  · rw [recoverLayerPair_eqN]
    refine (TBSim.bind (W₂ := 0) (recoverLayerPair_tbsim (im := im) hpre ht) (fun pair t h => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨pc, enc, right, cv, pv, regs, frame⟩ := h
    refine TBSim.pure ⟨pc, enc, (fun _ => right), (fun he => False.elim (ht he)), cv, pv, regs, ?_,
      fun he => False.elim (ht he), fun he => False.elim (ht he)⟩
    exact frame.mono (by intro A hA h; rcases h with (h | h) | h; exact Or.inl (Or.inl h); exact Or.inr h; exact Or.inl (Or.inr h))

end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ComposeBack ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
theorem extractByte_toNat_e (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
theorem word_ext_bytes_e {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat_e] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega
theorem extractByte_or8_e (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)
theorem extractByte_bytesToWordLE_e (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8_e _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl
theorem bytesToWordLE_bytes_e {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes_e
  intro i hi
  rw [extractByte_bytesToWordLE_e _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_e]
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
theorem bytes_length_e {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV bytesToWordLE_bytes_e bytes_length_e extractByte_bytesToWordLE_e)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests)
set_option linter.unusedSimpArgs false
def w9init (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) : MachineState :=
  (((((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 (dataBase im)) im.data).writeBytesAsWords (BitVec.ofNat 64 0x6620) (bytes m)).writeBytesAsWords
    (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords (BitVec.ofNat 64 0x7000) (bytes σ))).setReg .x2
    (BitVec.ofNat 64 (dataBase im))
set_option maxRecDepth 100000 in
theorem hdrBankBytes_length : hdrBankBytes.length = 4608 := by decide +kernel
set_option maxRecDepth 100000 in
theorem planBytes_length : planBytes.length = 1024 := by decide +kernel
set_option maxRecDepth 100000 in
theorem lplanBytes_length : lplanBytes.length = 1536 := by decide +kernel
theorem data_length {im : Image} (hd : ExpandDataOK im) : im.data.length = 27648 := by
  rw [hd, List.length_append, List.length_append, List.length_append, List.length_append, lplanBytes_length,
    planBytes_length, ESearch.expCostBytes_length, hdrBankBytes_length, Search.expandLegacyData_length]
theorem dataBase_eq {im : Image} (hd : ExpandDataOK im) : dataBase im = Compact2.LPLAN := by
  unfold dataBase
  rw [data_length hd]
  rfl
theorem data_drop_plan {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 1536 = planBytes ++ expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [hd, List.append_assoc, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [lplanBytes_length]),
    List.drop_eq_nil_of_le (by rw [lplanBytes_length]), List.nil_append, List.append_assoc, List.append_assoc]
theorem data_drop_cost {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 2560 = expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 2560 = 1536 + 1024 from rfl, ← List.drop_drop, data_drop_plan hd, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [planBytes_length]),
    List.drop_eq_nil_of_le (by rw [planBytes_length]), List.nil_append, List.append_assoc]
theorem data_drop_bank {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 18944 = hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 18944 = 2560 + 16384 from rfl, ← List.drop_drop, data_drop_cost hd, List.append_assoc,
    List.drop_append_of_le_length (by rw [ESearch.expCostBytes_length]),
    List.drop_eq_nil_of_le (by rw [ESearch.expCostBytes_length]), List.nil_append]
theorem data_drop_legacy {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 23552 = SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 23552 = 18944 + 4608 from rfl, ← List.drop_drop, data_drop_bank hd,
    List.drop_append_of_le_length (by rw [hdrBankBytes_length]),
    List.drop_eq_nil_of_le (by rw [hdrBankBytes_length]), List.nil_append]
section init
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312)
include hd
theorem w9init_getMem (A : Nat) (hA : A < 2 ^ 64) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5312 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x6620 ≤ A ∧ A < 0x6640 ∧ (A - 0x6620) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x6620)).take 8)
      else if Compact2.LPLAN ≤ A ∧ A < Compact2.LPLAN + 27648 ∧ (A - Compact2.LPLAN) % 8 = 0 then
        bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x6620 A (by rw [bytes_length_e]; decide) hA, dataBase_eq hd,
    getMem_writeBytesAsWords _ _ Compact2.LPLAN A (by rw [data_length hd]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e, data_length hd]
  rfl
theorem w9init_data (A : Nat) (h1 : Compact2.LPLAN ≤ A) (h2 : A < Compact2.LPLAN + 27648)
    (h3 : (A - Compact2.LPLAN) % 8 = 0) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) = bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8) := by
  unfold Compact2.LPLAN at h1 h2 h3
  rw [w9init_getMem hd _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by unfold Compact2.LPLAN; omega)]
omit hd in
theorem w9init_pc : (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl
end init
theorem data_plan {im : Image} (hd : ExpandDataOK im) (o : Nat) (ho : o + 8 ≤ 1024) :
    (im.data.drop (1536 + o)).take 8 = (planBytes.drop o).take 8 := by
  rw [← List.drop_drop, data_drop_plan hd, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [planBytes_length]; omega),
    List.take_append_of_le_length (by simp [planBytes_length]; omega)]
theorem data_lplan {im : Image} (hd : ExpandDataOK im) (o : Nat) (ho : o + 8 ≤ 1536) :
    (im.data.drop o).take 8 = (lplanBytes.drop o).take 8 := by
  rw [hd, List.append_assoc, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [lplanBytes_length]; omega),
    List.take_append_of_le_length (by simp [lplanBytes_length]; omega)]
theorem w9init_plan {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    PlanAt (w9init im m pk σ) := by
  intro k hk
  rw [w9init_data hd _ _ _ _ (by unfold PLAN Compact2.LPLAN; omega) (by unfold PLAN Compact2.LPLAN; omega)
      (by unfold PLAN Compact2.LPLAN; omega),
    show PLAN + 8 * k - Compact2.LPLAN = 1536 + 8 * k by unfold PLAN Compact2.LPLAN; omega, data_plan hd _ (by omega)]
theorem w9init_lplan {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    Compact2.LPlanAt (w9init im m pk σ) := by
  intro k hk
  rw [w9init_data hd _ _ _ _ (by unfold Compact2.LPLAN; omega) (by unfold Compact2.LPLAN; omega)
      (by unfold Compact2.LPLAN; omega),
    show Compact2.LPLAN + 8 * k - Compact2.LPLAN = 8 * k by omega, data_lplan hd _ (by omega)]
/-- C4 (adapted from b3cc11b's `w9init_toptab`): the two top-path plan tables of the post-pass (legacy data offsets
2944 / 3456 = data offsets 26496 / 27008). -/
theorem w9init_toptab {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    Compact2.TopTabAt (w9init im m pk σ) := by
  have key : ∀ o : Nat, (im.data.drop (23552 + o)).take 8 =
      (SigGolfCandidate.T3M.Images.expandLegacyData.drop o).take 8 := fun o => by
    rw [← List.drop_drop, data_drop_legacy hd]
  have tk : ∀ (L : List (BitVec 8)) (a k : Nat), 8 * k + 8 ≤ 512 →
      (((L.drop a).take 512).drop (8 * k)).take 8 = (L.drop (a + 8 * k)).take 8 := fun L a k hk => by
    rw [List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [w9init_data hd _ _ _ _ (by unfold Compact2.TOPA Compact2.LPLAN; omega)
        (by unfold Compact2.TOPA Compact2.LPLAN; omega) (by unfold Compact2.TOPA Compact2.LPLAN; omega),
      show Compact2.TOPA + 8 * k - Compact2.LPLAN = 23552 + (2944 + 8 * k) by unfold Compact2.TOPA Compact2.LPLAN; omega,
      key]
    unfold Compact2.topABytes
    rw [tk _ _ _ (by omega)]
  · rw [w9init_data hd _ _ _ _ (by unfold Compact2.TOPB Compact2.LPLAN; omega)
        (by unfold Compact2.TOPB Compact2.LPLAN; omega) (by unfold Compact2.TOPB Compact2.LPLAN; omega),
      show Compact2.TOPB + 8 * k - Compact2.LPLAN = 23552 + (3456 + 8 * k) by unfold Compact2.TOPB Compact2.LPLAN; omega,
      key]
    unfold Compact2.topBBytes
    rw [tk _ _ _ (by omega)]
-- [h2 lane] removed front_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
-- [h2 lane] removed front_pre30: a fact about the record's original expand word 0 / 342, which H2 replaces
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

Word 0 is `j 54569` (DEC). From `w9init` with the 5,195-byte signature `b`, DEC writes the expander's inflated slot
layout `SharedCodec.inflatedRead 0 (SharedCodec.digC b)` (332 slots at `0x7000`) and the hint at `0x66000`, rejects a
hint `≥ 7744` at `j 354`, zeroes its temporaries and jumps to word 1 (2,006 steps in all). -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.Expand (bytes_length_e bytesToWordLE_bytes_e word_ext_bytes_e extractByte_bytesToWordLE_e
  extractByte_toNat_e)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `w9init` memory before the signature write (independent of the signature). -/
def preSig (im : Image) (m : Message) (pk : PublicKey) : MachineState :=
  ((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 (dataBase im)) im.data).writeBytesAsWords (BitVec.ofNat 64 0x6620) (bytes m)).writeBytesAsWords
    (BitVec.ofNat 64 0xA0) (bytes pk)

theorem w9_getMem (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (hn : n ≤ 5248) (σ : Bytes n) (A : Nat)
    (hA : A < 2 ^ 64) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 8 * ((n + 7) / 8) ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else (preSig im m pk).getMem (BitVec.ofNat 64 A) := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; omega) hA,
    bytes_length_e]
  rfl

theorem w9_getReg (im : Image) (m : Message) (pk : PublicKey) {n n' : Nat} (σ : Bytes n) (σ' : Bytes n') (r : Reg) :
    (w9init im m pk σ).getReg r = (w9init im m pk σ').getReg r := by
  unfold w9init
  by_cases h : r = .x2
  · subst h
    rw [MachineState.getReg_setReg_eq (by decide), MachineState.getReg_setReg_eq (by decide)]
  · rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]
    simp only [MachineState.getReg_writeBytesAsWords]

theorem w9_getReg_zero (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) (r : Reg)
    (h : r ≠ .x2) : (w9init im m pk σ).getReg r = 0 := by
  unfold w9init
  rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]
  simp only [MachineState.getReg_writeBytesAsWords]
  cases r <;> rfl

def jalTo0 (w : BitVec 32) (n : Nat) : Option Nat :=
  match decodeInstruction w with
  | some (.base (.JAL .x0 imm)) =>
    let a := (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64
    if 0x1000 ≤ a ∧ a % 4 = 0 then some ((a - 0x1000) / 4) else none
  | _ => none
theorem jalTo0_sound {w : BitVec 32} {n m : Nat} (h : jalTo0 w n = some m) :
    ∃ imm, decodeInstruction w = some (.base (.JAL .x0 imm)) ∧
      (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64 := by
  unfold jalTo0 at h
  split at h
  · rename_i imm hd
    refine ⟨imm, hd, ?_⟩
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
      rw [Nat.mod_eq_of_lt (a := 0x1000 + 4 * _) (by omega)]
      omega
    · cases h
  · cases h

theorem entry_code0 : CodeAt Images.expandImage (pcOf 0) [0x4a43506f] :=
  codeAt_expand_current_chunk (by decide) (by decide) (by decide +kernel)

theorem w9_pc (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) :
    (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl

theorem entry_step0 (s : MachineState) (hpc : s.pc = pcOf 0) :
    Steps Images.expandImage s 1 1 (s.setPC (pcOf 54569)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo0_sound (show jalTo0 (0x4a43506f#32) 0 = some 54569 by decide +kernel)
  exact jal_x0_step entry_code0 hd hoff s hpc

theorem dropTake_getD {α : Type} (l : List α) (d : α) (a i : Nat) (hi : i < 8) :
    ((l.drop a).take 8).getD i d = l.getD (a + i) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi, List.getElem?_drop]

theorem bytes_getD {n : Nat} (x : Bytes n) (i : Nat) (hi : i < n) :
    (bytes x).getD i 0 = x.extractLsb' (8 * i) 8 := by
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

/-- The DEC entry memory of the real initial state holds the 5,195-byte signature. -/
theorem w9_sigMem (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    SigMem (w9init Images.expandImage m pk b).getMem b := by
  constructor
  · intro j hj
    rw [w9_getMem _ _ _ (by decide) b _ (by omega), if_pos (by omega), show 0x7000 + 8 * j - 0x7000 = 8 * j by omega]
    exact bytesToWordLE_bytes_e b j (by omega)
  · rw [w9_getMem _ _ _ (by decide) b _ (by omega), if_pos (by omega), show 0x8448 - 0x7000 = 5192 by rfl]
    have hbyte : ∀ i, i < 3 → (bytesToWordLE (((bytes b).drop 5192).take 8)).toNat / 2 ^ (8 * i) % 256 =
        b.toNat / 2 ^ (8 * 5192) / 2 ^ (8 * i) % 256 := by
      intro i hi
      rw [← extractByte_toNat_e, extractByte_bytesToWordLE_e _ _ (by omega), dropTake_getD _ _ _ _ (by omega),
        bytes_getD b _ (by omega), BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        ← Nat.pow_add, show 8 * 5192 + 8 * i = 8 * (5192 + i) by omega]
    have h0 := hbyte 0 (by omega)
    have h1 := hbyte 1 (by omega)
    have h2 := hbyte 2 (by omega)
    rw [show 64 * 649 = 8 * 5192 by rfl]
    generalize (bytesToWordLE (((bytes b).drop 5192).take 8)).toNat = W at h0 h1 h2
    generalize b.toNat / 2 ^ (8 * 5192) = B at h0 h1 h2
    norm_num at h0 h1 h2 ⊢
    omega

/-- DEC, accepting, from any state at word 0 holding the signature. -/
theorem dec_gen (s0 : MachineState) (b : SharedCodec.CBytes) (hpc : s0.pc = pcOf 0) (hsig : SigMem s0.getMem b)
    (hh : (SharedCodec.sigDecC b).policyHints.toNat < 7744) :
    ∃ u, Steps Images.expandImage s0 2006 2006 u ∧ u.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30], u.getReg r = 0) ∧
      RegsExcept s0 u [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30] ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat ∧
      Frame s0 u (fun A => A = 417792 ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  have st0 := entry_step0 s0 hpc
  have e : (s0.setPC (pcOf 54569)).getMem = s0.getMem := funext fun _ => MachineState.getMem_setPC
  have hsig1 : SigMem (s0.setPC (pcOf 54569)).getMem b := by rw [e]; exact hsig
  obtain ⟨t, st, tp, tz, tr, tm, th, tf⟩ := dec_run (s0.setPC (pcOf 54569)) rfl (by rw [hint_toNat hsig1]; exact hh)
  refine ⟨t, st0.trans st, tp, tz, fun r hr => (tr r hr).trans MachineState.getReg_setPC, ?_,
    th.trans (hint_eq hsig1), fun A hA hn => (tf A hA hn).trans MachineState.getMem_setPC⟩
  intro k hk
  have e0 := (tm k 0 hk (by omega)).trans (decOut_eq hsig1 k 0 hk (by omega))
  have e1 := (tm k 1 hk (by omega)).trans (decOut_eq hsig1 k 1 hk (by omega))
  unfold slotA at e0 e1
  rw [Nat.mul_zero, Nat.add_zero] at e0
  exact ⟨e0, e1⟩

/-- DEC, accepting: from the real initial state, word 0 + DEC reach word 1 with `w9init`'s registers, the inflated
slot layout of the decoded signature at `0x7000`, the hint at `0x66000`; only the hint word and `[0x70d0, 0x84c0)`
are written. -/
theorem dec_init (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hh : (SharedCodec.sigDecC b).policyHints.toNat < 7744) :
    ∃ u, Steps Images.expandImage (w9init Images.expandImage m pk b) 2006 2006 u ∧ u.pc = pcOf 1 ∧
      (∀ r, u.getReg r = (w9init Images.expandImage m pk b).getReg r) ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat ∧
      Frame (w9init Images.expandImage m pk b) u (fun A => A = 417792 ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨u, su, up, uz, ur, ui, uh, uf⟩ := dec_gen _ b (w9_pc Images.expandImage m pk b) (w9_sigMem m pk b) hh
  refine ⟨u, su, up, ?_, ui, uh, uf⟩
  intro r
  by_cases hr : r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30]
  · rw [uz r hr, w9_getReg_zero _ _ _ _ _ (by intro e; subst e; simp at hr)]
  · exact ur r hr

/-- DEC, rejecting: a hint `≥ 7744` sends the expander to word 354 (the failure exit) after 80 steps. -/
theorem dec_reject (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hh : 7744 ≤ (SharedCodec.sigDecC b).policyHints.toNat) :
    ∃ u, Steps Images.expandImage (w9init Images.expandImage m pk b) 80 80 u ∧ u.pc = pcOf 354 := by
  generalize hs0 : w9init Images.expandImage m pk b = s0
  have hpc : s0.pc = pcOf 0 := by rw [← hs0]; exact w9_pc Images.expandImage m pk b
  have hsig : SigMem s0.getMem b := by rw [← hs0]; exact w9_sigMem m pk b
  have st0 := entry_step0 s0 hpc
  have e : (s0.setPC (pcOf 54569)).getMem = s0.getMem := funext fun _ => MachineState.getMem_setPC
  have hsig1 : SigMem (s0.setPC (pcOf 54569)).getMem b := by rw [e]; exact hsig
  obtain ⟨t, st, tp, -, -, -⟩ := d1_spec (s0.setPC (pcOf 54569)) rfl
  rw [if_neg (by rw [hint_toNat hsig1]; omega)] at tp
  have hc : CodeAt Images.expandImage (pcOf 54647) [0xfadca06f] :=
    codeAt_t51_at 54647 (by decide) (by decide) (by decide)
  obtain ⟨imm, hd, hoff⟩ := jalTo0_sound (show jalTo0 (0xfadca06f#32) 54647 = some 354 by decide +kernel)
  exact ⟨_, (st0.trans st).trans (jal_x0_step hc hd hoff t tp), rfl⟩

end ClaudeWCT.W9.Machine.Expand.PrePass
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactLoop ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
def copied (s0 : MachineState) (src dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then s0.getMem (BitVec.ofNat 64 (src + (A - dst)))
  else s0.getMem (BitVec.ofNat 64 A)
def zeroed (s0 : MachineState) (dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then 0 else s0.getMem (BitVec.ofNat 64 A)
theorem ofNat_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) + 18446744073709551615#64 = BitVec.ofNat 64 n := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, ofNat_add_ofNat,
    show n + 1 + (2 ^ 64 - 1) = n + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]
macro "c_regs" res:ident : tactic =>
  `(tactic| (intro r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             cases r <;> simp_all [rv_simp, $res:ident] <;> rfl))
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem copy_iter (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1)) (hn : n + 1 < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if n = 0 then pcOf 42136 else pcOf 42130) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src + 8) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst then s.getMem (BitVec.ofNat 64 src) else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RCopy (code_cCopy hc) s hpc (by
    simp [RCopy.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopy.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RCopy.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RCopy.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RCopy.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RCopy.res
  · intro A hA
    simp only [Result.toState_getMem, RCopy.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h10, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem copy_ret (s : MachineState) (hpc : s.pc = pcOf 42136) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RCopyRet (code_copyRet hc) s hpc (by simp [RCopyRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopyRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RCopyRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure CopyInv (s : MachineState) (src dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42130 else pcOf 42136)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (src + 8 * i)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x6, .x10, .x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst i A
theorem copy_loop (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∀ i, i ≤ n → ∃ t, Steps im s (6 * i) (6 * i) t ∧ CopyInv s src dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h10, by simpa using h11,
      by simpa using h12, fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold copied; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42130 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u10, u11, u12, ru, mu⟩ := copy_iter hc t hpc' (src + 8 * i) (dst + 8 * i) (n - i - 1)
      hI.x10 hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u10, show src + 8 * i + 8 = src + 8 * (i + 1) by ring]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (src + 8 * i)) = s.getMem (BitVec.ofNat 64 (src + 8 * i)) := by
        rw [hI.mem _ (by omega)]; unfold copied; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold copied
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show dst + 8 * i - dst = 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem copy_spec (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n ret : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (6 * n + 1) (6 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst n A) := by
  obtain ⟨t, st, hI⟩ := copy_loop hc s hpc src dst n h10 h11 h12 hn hn' hs hs' hd hd' hov n le_rfl
  have hpc' : t.pc = pcOf 42136 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := copy_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
set_option maxRecDepth 20000 in
theorem zero_iter (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1))
    (hn : n + 1 < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if n = 0 then pcOf 42141 else pcOf 42137) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧
      RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = if A = dst then 0 else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RZero (code_cZero hc) s hpc (by
    simp [RZero.res, rv_simp, accessValid_iff, h11, BitVec.toNat_ofNat]
    refine ⟨?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZero.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RZero.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RZero.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RZero.res
  · intro A hA
    simp only [Result.toState_getMem, RZero.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem zero_ret (s : MachineState) (hpc : s.pc = pcOf 42141) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RZeroRet (code_zeroRet hc) s hpc (by simp [RZeroRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZeroRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RZeroRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure ZeroInv (s : MachineState) (dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42137 else pcOf 42141)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst i A
theorem zero_loop (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hn' : n < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (4 * i) (4 * i) t ∧ ZeroInv s dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h11, by simpa using h12,
      fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold zeroed; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42137 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u11, u12, ru, mu⟩ := zero_iter hc t hpc' (dst + 8 * i) (n - i - 1)
      hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      rw [mu A hA, hI.mem A hA]
      unfold zeroed
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem zero_spec (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n ret : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n)
    (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32) (hd : dst % 8 = 0)
    (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∃ t, Steps im s (4 * n + 1) (4 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst n A) := by
  obtain ⟨t, st, hI⟩ := zero_loop hc s hpc dst n h11 h12 hn hn' hd hd' n le_rfl
  have hpc' : t.pc = pcOf 42141 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := zero_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
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
/-- r3w: the staging slot of sibling level `l` (levels `0..4` from the plan table, level 5 the fixed staging block
`+832`, as the compaction code writes it; the witness layer's own `authSibOff 5` moved to `784`). -/
def authSibOff (c l : Nat) : Nat :=
  if l < 5 then ClaudeWCT.W9.T3M.authSibOff c l else 832 + 48 * (1 - c / 2 ^ 5 % 2)
def bitE (l : Nat) : E :=
  if l < 6 then .bin .and (.bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))) (.c 1#64)
  else .bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))
def nbE (l : Nat) : E := .bin .xor (bitE l) (.c 1#64)
def t6E (l : Nat) : E := .bin .add (.bin .sll (nbE l) (.c 4#64)) (.bin .sll (nbE l) (.c 5#64))
def hwE (l : Nat) : E :=
  .un (.ld .hu (2 * (l % 4))) (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld)
/-- Nested FTS (r1-1): level 5 targets the fixed staging block `+832` (`addi t3,zero,832`, no plan load). -/
def dstE (l : Nat) : E :=
  if l < 5 then .bin .add (.bin .add (.reg .x9) (hwE l)) (t6E l)
  else if l = 5 then .bin .add (.bin .add (.reg .x9) (.c 832#64)) (t6E l) else .bin .add (.reg .x9) (hwE l)
def a3E (l : Nat) : E := .bin .add (.reg .x8) (t6E l)
def srcE (l o : Nat) : E :=
  if 64 * (6 - l) + o = 0 then a3E l else .bin .add (a3E l) (.c (BitVec.ofNat 64 (64 * (6 - l) + o)))
def sibRegs (l : Nat) : RegFile :=
  ((((RegFile.init.set .x13 (a3E l)).set .x28 (dstE l)).set .x29 (srcE l 0).ld).set .x30 (srcE l 8).ld).set .x31
    (t6E l)
/-- r3w (witness stack): store shift of sibling level `l` of coordinate `k` (`sd t4,-sh(t3)`; level 5 one block
further down). The FTS content of the staging is dead (rebuilt by the finish pass), only the frame matters. -/
def sh (k l : Nat) : Nat := if k = 0 then 0 else if l < 5 then 48 * (k - 1) else 48 * k
def shOff (k l o : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - sh k l + o)
theorem sh_le (k l : Nat) : sh k l ≤ 48 * k ∧ sh k l % 16 = 0 := by
  unfold sh; split_ifs <;> omega
theorem ofNat_shOff (X k l o : Nat) (hk : k < 9) (h : sh k l ≤ X) :
    BitVec.ofNat 64 X + shOff k l o = BitVec.ofNat 64 (X - sh k l + o) := by
  have := sh_le k l
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  unfold shOff
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64]
  omega
/-- r3w: destination of sibling level `l` of coordinate `k` (region base `D`). -/
def sdst (c D k l : Nat) : Nat := D - sh k l + authSibOff c l
def sibMem (k l : Nat) : SymMem :=
  [(⟨some (dstE l), shOff k l 8⟩, (srcE l 8).ld), (⟨some (dstE l), shOff k l 0⟩, (srcE l 0).ld)]
def sibObl4 (k l : Nat) : List Oblig :=
  [.valid ⟨some (dstE l), shOff k l 8⟩ 8, .valid ⟨some (dstE l), shOff k l 0⟩ 8,
    .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l) + 8)⟩ 8, .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l))⟩ 8]
def sibOblP (l : Nat) : List Oblig := [.align8 (.reg .x20), .valid ⟨some (.reg .x20), BitVec.ofNat 64 (2 * l)⟩ 2]
def sibObl (k l : Nat) : List Oblig := sibObl4 k l ++ (if l = 5 then [] else sibOblP l)
set_option maxRecDepth 20000 in
theorem run_sib (k l : Nat) (hk : k < 9) (hl : l < 6) : symRun cfgC (cSib k l) (pcOf (sibAt k l)) 40 =
    some ⟨⟨sibRegs l, sibMem k l, sibObl k l⟩, .c (pcOf (sibAt k l + sibLen l)), .endOfCode, sibLen l, sibLen l⟩ := by
  interval_cases k <;> interval_cases l <;> kernel_rfl
def srcOff (c l : Nat) : Nat := 64 * (6 - l) + 48 * (1 - c / 2 ^ l % 2)
def planHW (c l : Nat) : Nat := if l < 6 then authBase c l else authRoot c
set_option maxRecDepth 100000 in
theorem planHW_ok : ∀ r < 64, ∀ l < 5,
    LoadKind.hu.fromWord (bytesToWordLE ((planBytes.drop (8 * (2 * r + l / 4))).take 8)) (2 * (l % 4)) =
      BitVec.ofNat 64 (planHW r l) := by
  decide +kernel
theorem authSibOff_ok : ∀ c < 128, ∀ l < 5, authSibOff c l % 16 = 0 ∧ authSibOff c l + 16 ≤ 320 := by
  decide +kernel
theorem authSibOff_five (c : Nat) : authSibOff c 5 = 832 + 48 * (1 - c / 2 ^ 5 % 2) := by
  unfold authSibOff; rw [if_neg (by norm_num)]
theorem auth6_ok (c : Nat) (hc : c < 128) (l : Nat) (hl : l < 6) :
    authSibOff c l % 16 = 0 ∧ authSibOff c l + 16 ≤ 896 ∧ (l < 5 → authSibOff c l + 16 ≤ 320) ∧
      (l = 5 → 832 ≤ authSibOff c l) := by
  by_cases h : l < 5
  · have := authSibOff_ok c hc l h
    exact ⟨this.1, by omega, fun _ => this.2, fun h5 => by omega⟩
  · obtain rfl : l = 5 := by omega
    rw [authSibOff_five]
    have : c / 2 ^ 5 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    refine ⟨by omega, by omega, fun h => by omega, fun _ => by omega⟩
theorem planHW_mod (c l : Nat) : planHW (c % 64) l = planHW c l := by
  unfold planHW authBase authRoot; rw [Nat.mod_mod]
section eval
variable {s : MachineState} {c : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (hc : c < 128)
include h19 hc
theorem bitE_eval (l : Nat) (hl : l < 7) : (bitE l).eval s = BitVec.ofNat 64 (c / 2 ^ l % 2) := by
  apply BitVec.eq_of_toNat_eq
  unfold bitE
  split
  · simp only [E.eval, BinOp.eval, h19, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show l < 64 by omega), show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod,
      Nat.mod_eq_of_lt (show c / 2 ^ l % 2 < 2 ^ 64 from lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))]
  · have hl6 : l = 6 := by omega
    subst hl6
    simp only [E.eval, BinOp.eval, h19, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
    norm_num
    omega
theorem nbE_eval (l : Nat) (hl : l < 7) : (nbE l).eval s = BitVec.ofNat 64 (1 - c / 2 ^ l % 2) := by
  have hb := bitE_eval h19 hc l hl
  simp only [nbE, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem t6E_eval (l : Nat) (hl : l < 7) : (t6E l).eval s = BitVec.ofNat 64 (48 * (1 - c / 2 ^ l % 2)) := by
  have hb := nbE_eval h19 hc l hl
  simp only [t6E, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem a3E_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) :
    (a3E l).eval s = BitVec.ofNat 64 (S + 48 * (1 - c / 2 ^ l % 2)) := by
  simp only [a3E, E.eval, BinOp.eval, h8, t6E_eval h19 hc l hl, ofNat_add_ofNat]
theorem srcE_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (o : Nat) :
    (srcE l o).eval s = BitVec.ofNat 64 (S + srcOff c l + o) := by
  unfold srcE srcOff
  split
  · rw [a3E_eval h19 hc l hl h8]; congr 1; omega
  · simp only [E.eval, BinOp.eval, a3E_eval h19 hc l hl h8, ofNat_add_ofNat]; congr 1; omega
end eval
theorem hwE_eval {s : MachineState} {c : Nat} (hc : c < 128)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s) (l : Nat) (hl : l < 5) :
    (hwE l).eval s = BitVec.ofNat 64 (planHW c l) := by
  have hr : c % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hw : (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld).eval s =
      bytesToWordLE ((planBytes.drop (8 * (2 * (c % 64) + l / 4))).take 8) := by
    split
    · simp only [E.eval, h20]
      rw [show l / 4 = 0 by omega, show PLAN + 16 * (c % 64) = PLAN + 8 * (2 * (c % 64) + 0) by ring]
      exact hp _ (by omega)
    · simp only [E.eval, BinOp.eval, h20, ofNat_add_ofNat]
      rw [show l / 4 = 1 by omega, show PLAN + 16 * (c % 64) + 8 = PLAN + 8 * (2 * (c % 64) + 1) by ring]
      exact hp _ (by omega)
  simp only [hwE, E.eval, UnOp.eval]
  rw [hw, planHW_ok (c % 64) hr l hl, planHW_mod]
theorem authSibOff_eq (c l : Nat) (hl : l < 5) :
    authSibOff c l = if l < 6 then planHW c l + 48 * (1 - c / 2 ^ l % 2) else planHW c l := by
  unfold authSibOff ClaudeWCT.W9.T3M.authSibOff planHW SigGolfCandidate.T3M.sibOff
  rw [if_pos hl]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  split_ifs <;> omega
theorem dstE_eval {s : MachineState} {c D : Nat} (hc : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (l : Nat) (hl : l < 6) :
    (dstE l).eval s = BitVec.ofNat 64 (D + authSibOff c l) := by
  by_cases hl5 : l < 5
  · rw [authSibOff_eq c l (by omega), if_pos (show l < 6 by omega)]
    simp only [dstE, if_pos hl5, E.eval, BinOp.eval, h9, hwE_eval hc h20 hp l hl5, t6E_eval h19 hc l (by omega),
      ofNat_add_ofNat]
    rw [Nat.add_assoc]
  · obtain rfl : l = 5 := by omega
    rw [authSibOff_five]
    simp only [dstE, show ¬ (5 : Nat) < 5 by decide, if_false, if_true, E.eval, BinOp.eval, h9,
      t6E_eval h19 hc 5 (by omega), ofNat_add_ofNat]
    rw [Nat.add_assoc]
theorem srcOff_bound (c l : Nat) : srcOff c l + 16 ≤ 448 ∧ srcOff c l % 16 = 0 := by
  unfold srcOff
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  constructor <;> omega
theorem sibRegs_get (l : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x13, .x28, .x29, .x30, .x31]) :
    ((sibRegs l).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h13, h28, h29, h30, h31⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
/-! Nested FTS (r1-1): level 6. The word at `sibAt k 6` jumps to the trampoline `P6(k)` (words
`33000 + 13 k`), which loads coordinate `k`'s top sibling from the scratch region (`x8 + 48 (1 - bit6)`) and
stores it with the flag `1 - bit6` to the hold slot `0x380000 + 32 k`; the final assembly places it. -/
def cJ6s : List (BitVec 32) := [4187975791,3776933999,3365892207,2954850415,2543808623,4279201903,3868160111,3457118319,3046076527]
def cP6s : List (List (BitVec 32)) := [[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,31338531,32388131,33437731,109084783],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,64892963,65942563,66992163,520126575],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,98447395,99496995,100546595,931168367],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,132001827,133051427,134101027,1342210159],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,165556259,166605859,167655459,1753251951],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,199110691,200160291,201209891,17858671],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,232665123,233714723,234764323,428900463],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,266219555,267269155,268318755,839942255],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,299773987,300823587,301873187,1250984047]]
def cJ6 (k : Nat) : List (BitVec 32) := [cJ6s.getD k 0]
def cP6 (k : Nat) : List (BitVec 32) := cP6s.getD k []
def p6At (k : Nat) : Nat := 33000 + 13 * k
def p6tE : E := .bin .add (.bin .sll (nbE 6) (.c 5#64)) (.bin .sll (nbE 6) (.c 4#64))
def a6E : E := .bin .add p6tE (.reg .x8)
def p6Regs : RegFile :=
  ((((RegFile.init.set .x13 a6E).set .x28 (.c 0x380000#64)).set .x29 (E.ld a6E)).set .x30
    (E.ld (.bin .add a6E (.c 8#64)))).set .x31 (nbE 6)
def p6Mem (k : Nat) : SymMem :=
  [(⟨none, BitVec.ofNat 64 (holdAt k + 16)⟩, nbE 6), (⟨none, BitVec.ofNat 64 (holdAt k + 8)⟩, E.ld (.bin .add a6E (.c 8#64))),
    (⟨none, BitVec.ofNat 64 (holdAt k)⟩, E.ld a6E)]
def p6Obl : List Oblig := [.valid ⟨some a6E, 8#64⟩ 8, .valid ⟨some a6E, 0#64⟩ 8]
theorem run_j6 (k : Nat) (hk : k < 9) : symRun cfgC (cJ6 k) (pcOf (sibAt k 6)) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf (p6At k)), .jump, 1, 1⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_p6 (k : Nat) (hk : k < 9) : symRun cfgC (cP6 k) (pcOf (p6At k)) 40 =
    some ⟨⟨p6Regs, p6Mem k, p6Obl⟩, .c (pcOf (coordAt k + 109)), .jump, 13, 13⟩ := by
  interval_cases k <;> kernel_rfl
theorem p6Regs_get (s : MachineState) (r : Reg) (hr : r ∉ [.x13, .x28, .x29, .x30, .x31]) :
    (p6Regs.get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h13, h28, h29, h30, h31⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sib_spec (k l : Nat) (hk : k < 9) (hl : l < 6) (s : MachineState) (hpc : s.pc = pcOf (sibAt k l))
    (c S D : Nat) (hcl : c < 128) (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)))
    (hp : PlanAt s) (hS : S % 16 = 0) (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0)
    (hD' : D + 896 ≤ MEMORY_BYTES) (hsh : 48 * k ≤ D) :
    ∃ t, Steps im s (sibLen l) (sibLen l) t ∧ t.pc = pcOf (sibAt k l + sibLen l) ∧
      RegsExcept s t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = sdst c D k l + 8 then s.getMem (BitVec.ofNat 64 (S + srcOff c l + 8))
        else if A = sdst c D k l then s.getMem (BitVec.ofNat 64 (S + srcOff c l))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have ha := auth6_ok c hcl l hl
  have hso := srcOff_bound c l
  have hd := dstE_eval hcl h19 h20 hp h9 l hl
  have hs0 := srcE_eval h19 hcl l (by omega) h8 0
  have hs8 := srcE_eval h19 hcl l (by omega) h8 8
  have ha3 := a3E_eval h19 hcl l (by omega) h8
  have hrun := run_sib k l hk hl
  have hshl := sh_le k l
  have e8 := ofNat_shOff (D + authSibOff c l) k l 8 hk (by omega)
  have e0 := ofNat_shOff (D + authSibOff c l) k l 0 hk (by omega)
  have hobl : Oblig.all s (sibObl k l) := by
    rw [Oblig.all_iff]
    intro o ho
    unfold sibObl at ho
    rw [List.mem_append] at ho
    rcases ho with ho | ho
    swap
    · split at ho
      · simp at ho
      · simp only [sibOblP, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold PLAN; omega
        · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
          unfold PLAN; omega
    simp only [sibObl4, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hd, e8, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, hd, e0, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + (64 * (6 - l) + 8) = S + srcOff c l + 8 by unfold srcOff; omega]
      omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + 64 * (6 - l) = S + srcOff c l by unfold srcOff; omega]
      omega
  refine ⟨_, symRun_sound hrun (code_cSib hc k l hk hl) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    rw [Result.toState_getReg]
    exact sibRegs_get l s r hr
  · intro A hA
    unfold sdst
    simp only [Result.toState_getMem, sibMem, memEval_cons, memEval_nil, Addr.eval, E.eval, hd, hs0, hs8, e8, e0,
      Nat.add_zero]
    have hbig : D - sh k l + authSibOff c l + 8 < 2 ^ 64 := by omega
    have q8 : D + authSibOff c l - sh k l + 8 = D - sh k l + authSibOff c l + 8 := by omega
    have q0 : D + authSibOff c l - sh k l = D - sh k l + authSibOff c l := by omega
    rw [q8, q0]
    by_cases h1 : A = D - sh k l + authSibOff c l + 8
    · subst h1; simp
    · rw [if_neg (fun h => h1 ((ofNat_inj hA hbig).mp h)), if_neg h1]
      by_cases h2 : A = D - sh k l + authSibOff c l
      · subst h2; simp
      · rw [if_neg (fun h => h2 ((ofNat_inj hA (by omega)).mp h)), if_neg h2]
theorem code_cJ6 (k : Nat) (hk : k < 9) : CodeAt im (pcOf (sibAt k 6)) (cJ6 k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cP6 (k : Nat) (hk : k < 9) : CodeAt im (pcOf (p6At k)) (cP6 k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sib6_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (sibAt k 6)) (c S : Nat)
    (hcl : c < 128) (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h19 : s.getReg .x19 = BitVec.ofNat 64 c)
    (hS : S % 16 = 0) (hS' : S + 448 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf (coordAt k + 109) ∧ RegsExcept s t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = holdAt k + 16 then BitVec.ofNat 64 (1 - c / 2 ^ 6 % 2)
        else if A = holdAt k + 8 then s.getMem (BitVec.ofNat 64 (S + srcOff c 6 + 8))
        else if A = holdAt k then s.getMem (BitVec.ofNat 64 (S + srcOff c 6))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨t1, hj, r1, m1, p1⟩ : ∃ t1, Steps im s 1 1 t1 ∧ (∀ r, t1.getReg r = s.getReg r) ∧
      (∀ A, t1.getMem A = s.getMem A) ∧ t1.pc = pcOf (p6At k) := by
    refine ⟨_, symRun_sound (run_j6 k hk) (code_cJ6 hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_⟩
    · intro r; rw [Result.toState_getReg]; cases r <;> rfl
    · intro A; simp [rv_simp]
    · simp [Result.toState_pc, E.eval]
  have hnb := nbE_eval (s := t1) (by rw [r1]; exact h19) hcl 6 (by omega)
  have h48 : p6tE.eval t1 = BitVec.ofNat 64 (48 * (1 - c / 2 ^ 6 % 2)) := by
    simp only [p6tE, E.eval, BinOp.eval, hnb]
    have : c / 2 ^ 6 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases (show c / 2 ^ 6 % 2 = 0 ∨ c / 2 ^ 6 % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
  have hso := srcOff_bound c 6
  have ha6 : a6E.eval t1 = BitVec.ofNat 64 (S + srcOff c 6) := by
    simp only [a6E, E.eval, BinOp.eval, h48, r1, h8, ofNat_add_ofNat]
    congr 1; unfold srcOff; omega
  have ha8 : (E.bin .add a6E (.c 8#64)).eval t1 = BitVec.ofNat 64 (S + srcOff c 6 + 8) := by
    simp only [E.eval, BinOp.eval, ha6, ofNat_add_ofNat]
  have hobl : Oblig.all t1 p6Obl := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [p6Obl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, ha6, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, ha6, BitVec.add_zero, accessValid_iff, BitVec.toNat_ofNat]; omega
  have hp := symRun_sound (run_p6 k hk) (code_cP6 hc k hk) t1 p1 hobl
  refine ⟨_, (hj.trans hp).of_eq rfl rfl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    rw [Result.toState_getReg, p6Regs_get t1 r hr, r1]
  · intro A hA
    simp only [Result.toState_getMem, p6Mem, memEval_cons, memEval_nil, Addr.eval, hnb, ha6, ha8, E.eval, BinOp.eval,
      ofNat_add_ofNat, m1]
    have hH : holdAt k + 16 < 2 ^ 64 := by unfold holdAt; omega
    by_cases e1 : A = holdAt k + 16
    · subst e1; simp
    · rw [if_neg (fun h => e1 ((ofNat_inj hA hH).mp h)), if_neg e1]
      by_cases e2 : A = holdAt k + 8
      · subst e2; simp
      · rw [if_neg (fun h => e2 ((ofNat_inj hA (by omega)).mp h)), if_neg e2]
        by_cases e3 : A = holdAt k
        · subst e3; simp
        · rw [if_neg (fun h => e3 ((ofNat_inj hA (by omega)).mp h)), if_neg e3]
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
def SNAP : Nat := 0x200000
def rHead (k : Nat) : Result :=
  [RHead0.res, RHead1.res, RHead2.res, RHead3.res, RHead4.res, RHead5.res, RHead6.res, RHead7.res, RHead8.res].getD k
    RHead0.res
def rMid (k : Nat) : Result :=
  [RMid0.res, RMid1.res, RMid2.res, RMid3.res, RMid4.res, RMid5.res, RMid6.res, RMid7.res, RMid8.res].getD k RMid0.res
theorem run_head (k : Nat) (hk : k < 9) : symRun cfgC (cHead k) (pcOf (coordAt k)) 40 = some (rHead k) := by
  interval_cases k
  exacts [RHead0, RHead1, RHead2, RHead3, RHead4, RHead5, RHead6, RHead7, RHead8]
theorem run_mid (k : Nat) (hk : k < 9) : symRun cfgC (cMid k) (pcOf (coordAt k + 6)) 40 = some (rMid k) := by
  interval_cases k
  exacts [RMid0, RMid1, RMid2, RMid3, RMid4, RMid5, RMid6, RMid7, RMid8]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem start_spec (s : MachineState) (hpc : s.pc = pcOf 41108) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 0x840 ∧
      t.getReg .x11 = BitVec.ofNat 64 SNAP ∧ t.getReg .x12 = BitVec.ofNat 64 1152 ∧ t.getReg .x1 = pcOf 41115 ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RStart (code_cStart hc) s hpc (by simp [RStart.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RStart.res, E.eval]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]; rfl
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · c_regs RStart.res
  · intro A _ _; rfl
theorem regs_spec (s : MachineState) (hpc : s.pc = pcOf 41115) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (coordAt 0) ∧ t.getReg .x8 = BitVec.ofNat 64 SNAP ∧
      t.getReg .x9 = BitVec.ofNat 64 0x840 ∧ t.getReg .x18 = BitVec.ofNat 64 PLAN ∧
      RegsExcept s t [.x8, .x9, .x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RRegs (code_cRegs hc) s hpc (by simp [RRegs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RRegs.res, E.eval, coordAt]
  · simp [RRegs.res, rv_simp]; rfl
  · simp [RRegs.res, rv_simp]
  · simp [RRegs.res, rv_simp]; rfl
  · c_regs RRegs.res
  · intro A _ _; rfl
theorem final_spec (s : MachineState) (hpc : s.pc = pcOf 42120) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (0x800 + 9280) ∧
      t.getReg .x11 = BitVec.ofNat 64 (0x800 + 8128) ∧ t.getReg .x12 = BitVec.ofNat 64 1713 ∧
      t.getReg .x1 = pcOf 42127 ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RFinal (code_cFinal hc) s hpc (by simp [RFinal.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RFinal.res, E.eval]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · c_regs RFinal.res
  · intro A _ _; rfl
theorem halt_spec (s : MachineState) (hpc : s.pc = pcOf 42127) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42142 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RHalt (code_cHalt hc) s hpc (by simp [RHalt.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RHalt.res, E.eval]
  · c_regs RHalt.res
  · intro A _ _; rfl
end
def headX6 (k : Nat) : E :=
  .bin .srl (E.c (BitVec.ofNat 64 (0x60 + 8 * (WCT9.childBase k / 64)))).ld (.c (BitVec.ofNat 64 (WCT9.childBase k % 64)))
def headRegs (k : Nat) : RegFile :=
  ((((RegFile.init.set .x6 (headX6 k)).set .x19 (.bin .and (headX6 k) (.c 127#64))).set .x11 (.reg .x9)).set .x12
    (.c 40#64)).set .x1 (.c (pcOf (coordAt k + 6)))
def midRegs (k : Nat) : RegFile :=
  (((RegFile.init.set .x10 (.bin .add (.reg .x8) (.c 448#64))).set .x11 (.bin .add (.reg .x9) (.c 320#64))).set .x12
    (.c 72#64)).set .x1 (.c (pcOf (coordAt k + 10)))
theorem rHead_eq (k : Nat) (hk : k < 9) : rHead k = ⟨⟨headRegs k, [], []⟩, .c (pcOf 42137), .jump, 6, 6⟩ := by
  interval_cases k <;> kernel_rfl
theorem rMid_eq (k : Nat) (hk : k < 9) : rMid k = ⟨⟨midRegs k, [], []⟩, .c (pcOf 42130), .jump, 4, 4⟩ := by
  interval_cases k <;> kernel_rfl
theorem headRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x6, .x11, .x12, .x19]) :
    ((headRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h6, h11, h12, h19⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem midRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x10, .x11, .x12]) :
    ((midRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h10, h11, h12⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem childBase_shift (k : Nat) (hk : k < 9) : WCT9.childBase k % 64 + 7 ≤ 64 ∧ WCT9.childBase k / 64 < 4 := by
  interval_cases k <;> decide
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem head_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (D : Nat) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42137 ∧
      t.getReg .x19 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase k % 128) ∧
      t.getReg .x11 = BitVec.ofNat 64 D ∧ t.getReg .x12 = BitVec.ofNat 64 40 ∧ t.getReg .x1 = pcOf (coordAt k + 6) ∧
      RegsExcept s t [.x1, .x6, .x11, .x12, .x19] ∧ Frame s t (fun _ => False) := by
  have hrun := run_head k hk
  rw [rHead_eq k hk] at hrun
  obtain ⟨hsh, hw⟩ := childBase_shift k hk
  refine ⟨_, symRun_sound hrun (code_cHead hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, headRegs, headX6, RegFile.set, RegFile.get, E.eval, BinOp.eval]
    have hm := hN (WCT9.childBase k / 64) hw
    rw [hm]
    apply BitVec.eq_of_toNat_eq
    have := child_bits N (WCT9.childBase k / 64) (WCT9.childBase k % 64) hsh
    rw [Nat.div_add_mod] at this
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 64 by omega)]
    rw [this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num) : N.toNat / 2 ^ WCT9.childBase k % 128 < 2 ^ 64)]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval, h9]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact headRegs_get k s r hr
  · intro A _ _; rfl
theorem mid_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 6)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (S + 448) ∧
      t.getReg .x11 = BitVec.ofNat 64 (D + 320) ∧ t.getReg .x12 = BitVec.ofNat 64 72 ∧
      t.getReg .x1 = pcOf (coordAt k + 10) ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  have hrun := run_mid k hk
  rw [rMid_eq k hk] at hrun
  refine ⟨_, symRun_sound hrun (code_cMid hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact midRegs_get k s r hr
  · intro A _ _; rfl
theorem row_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 10)) (c : Nat)
    (hcl : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (coordAt k + 13) ∧ t.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)) ∧
      RegsExcept s t [.x7, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_row k hk) (code_cRow hc k hk) s hpc (by simp [RRow.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RRow.res, RegFile.get, E.eval, BinOp.eval, h19, h18]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl, SigGolfCandidate.T3M.Search.ofNat_and_mask c 6 (by norm_num)]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; ring
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h20⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem step_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 109)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (coordAt k + 111) ∧ t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧
      t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧ RegsExcept s t [.x8, .x9] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_step k hk) (code_cStep hc k hk) s hpc (by simp [RStep.res, rv_simp]), ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8', h9'⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
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
def sibLev (c j : Nat) : Option Nat :=
  (List.range 6).find? fun l => authSibOff c l = 8 * j ∨ authSibOff c l + 8 = 8 * j
def sibSrc (c j : Nat) : Option Nat :=
  (sibLev c j).map fun l => if authSibOff c l = 8 * j then srcOff c l else srcOff c l + 8
/-- The hold slot of coordinate `k`: its top sibling and the flag `1 - bit6`. -/
def holdMem (M : Nat → Word) (c S k : Nat) (A : Nat) (rest : Word) : Word :=
  if A = holdAt k + 16 then BitVec.ofNat 64 (1 - c / 2 ^ 6 % 2)
  else if A = holdAt k + 8 then M (S + srcOff c 6 + 8)
  else if A = holdAt k then M (S + srcOff c 6) else rest
def sibsMem (M : Nat → Word) (c S D k L : Nat) (A : Nat) : Word :=
  match (List.range L).find? (fun l => A = sdst c D k l ∨ A = sdst c D k l + 8) with
  | some l => if A = sdst c D k l then M (S + srcOff c l) else M (S + srcOff c l + 8)
  | none => M A
theorem find_range_succ (p : Nat → Bool) (L : Nat) :
    (List.range (L + 1)).find? p = match (List.range L).find? p with
      | some l => some l
      | none => if p L then some L else none := by
  rw [List.range_succ, List.find?_append]
  cases h : (List.range L).find? p with
  | some l => rfl
  | none => simp only [List.find?_cons, List.find?_nil, Option.none_or]; cases hp : p L <;> simp [hp]
theorem find_some {p : Nat → Bool} {L l : Nat} (h : (List.range L).find? p = some l) : l < L ∧ p l = true :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), List.find?_some h⟩
theorem find_none {p : Nat → Bool} {L : Nat} (h : (List.range L).find? p = none) (l : Nat) (hl : l < L) :
    p l = false := by
  have := List.find?_eq_none.mp h l (List.mem_range.mpr hl)
  simpa using this
theorem auth_disj (c : Nat) (hc : c < 128) (l l' : Nat) (hl : l < 6) (hl' : l' < 6) (hne : l ≠ l') :
    authSibOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authSibOff c l := by
  by_cases h : l < 5 ∧ l' < 5
  · have e1 : authSibOff c l = ClaudeWCT.W9.T3M.authSibOff c l := if_pos h.1
    have e2 : authSibOff c l' = ClaudeWCT.W9.T3M.authSibOff c l' := if_pos h.2
    rw [e1, e2]
    exact ClaudeWCT.W9.T3M.auth_sib_disjoint c hc l h.1 l' h.2 hne
  · have a := auth6_ok c hc l hl
    have b := auth6_ok c hc l' hl'
    rcases (show l = 5 ∨ l' = 5 by omega) with e | e
    · have := a.2.2.2 e; have := b.2.2.1 (by omega); omega
    · have := b.2.2.2 e; have := a.2.2.1 (by omega); omega
theorem sdst_disj (c D k : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (l l' : Nat) (hl : l < 6) (hl' : l' < 6)
    (hne : l ≠ l') : sdst c D k l + 16 ≤ sdst c D k l' ∨ sdst c D k l' + 16 ≤ sdst c D k l := by
  have a := auth6_ok c hc l hl
  have b := auth6_ok c hc l' hl'
  have hd := auth_disj c hc l l' hl hl' hne
  have A1 : (l < 5 ∧ authSibOff c l + 16 ≤ 320) ∨ (l = 5 ∧ 832 ≤ authSibOff c l) := by
    by_cases h : l < 5
    · exact Or.inl ⟨h, a.2.2.1 h⟩
    · exact Or.inr ⟨by omega, a.2.2.2 (by omega)⟩
  have B1 : (l' < 5 ∧ authSibOff c l' + 16 ≤ 320) ∨ (l' = 5 ∧ 832 ≤ authSibOff c l') := by
    by_cases h : l' < 5
    · exact Or.inl ⟨h, b.2.2.1 h⟩
    · exact Or.inr ⟨by omega, b.2.2.2 (by omega)⟩
  unfold sdst sh
  rcases A1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases B1 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> split_ifs <;> omega
theorem sdst_bound (c D k l : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hl : l < 6) :
    D - 48 * k ≤ sdst c D k l ∧ sdst c D k l + 16 ≤ D + 896 ∧ sdst c D k l % 16 = (D - sh k l) % 16 := by
  obtain ⟨a1, a2, -, -⟩ := auth6_ok c hc l hl
  have := sh_le k l
  unfold sdst
  omega
theorem sibsMem_succ (M : Nat → Word) (c S D k L : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hL : L < 6) (A : Nat) :
    sibsMem M c S D k (L + 1) A =
      if A = sdst c D k L + 8 then M (S + srcOff c L + 8)
      else if A = sdst c D k L then M (S + srcOff c L) else sibsMem M c S D k L A := by
  unfold sibsMem
  rw [find_range_succ]
  cases h : (List.range L).find? (fun l => decide (A = sdst c D k l ∨ A = sdst c D k l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have hd := sdst_disj c D k hc hk l L (by omega) hL (by omega)
    simp only
    rw [if_neg (show ¬ A = sdst c D k L + 8 by omega), if_neg (show ¬ A = sdst c D k L by omega)]
  | none =>
    simp only
    by_cases h1 : A = sdst c D k L + 8
    · have h2 : ¬ A = sdst c D k L := by omega
      rw [if_pos (show decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h1]),
        if_pos h1]
      simp only
      rw [if_neg h2]
    · by_cases h2 : A = sdst c D k L
      · rw [if_pos (show decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h2]),
          if_neg h1, if_pos h2]
        simp only
        rw [if_pos h2]
      · rw [if_neg (show ¬ decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h1, h2]),
          if_neg h1, if_neg h2]
def zcMem (M : Nat → Word) (S D : Nat) (A : Nat) : Word :=
  if D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0 then M (S + 448 + (A - D - 320))
  else if D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0 then 0 else M A
/-- Staging region of coordinate `k` after its zero/copy calls and its six sibling stores (r3w: the sibling
stores of coordinate `k ≥ 2` land below `D`, in the previous region). -/
def coordMem (M : Nat → Word) (c S D k : Nat) (A : Nat) : Word := sibsMem (zcMem M S D) c S D k 6 A
theorem sibsMem_out (M : Nat → Word) (c S D k L : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hL : L ≤ 6) (A : Nat)
    (hA : A < D - 48 * k ∨ D + 896 ≤ A) : sibsMem M c S D k L A = M A := by
  unfold sibsMem
  cases h : (List.range L).find? (fun l => decide (A = sdst c D k l ∨ A = sdst c D k l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have := sdst_bound c D k l hc hk (by omega)
    omega
  | none => rfl
def sibsCyc (L : Nat) : Nat := 14 * L
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem sibs_spec (k : Nat) (hk : k < 9) (c S D : Nat) (hcl : c < 128) (hS : S % 16 = 0)
    (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0) (hDS : D + 896 ≤ S) (hDP : D + 896 ≤ PLAN)
    (hsh : 48 * k ≤ D) (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (coordAt k + 13)) (h8 : u.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : u.getReg .x9 = BitVec.ofNat 64 D) (h19 : u.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : u.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt u) :
    ∀ L ≤ 6, ∃ t, Steps im u (sibsCyc L) (sibsCyc L) t ∧ t.pc = pcOf (coordAt k + 13 + sibsCyc L) ∧
      RegsExcept u t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = sibsMem M0 c S D k L A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  intro L hL
  induction L with
  | zero => exact ⟨u, Steps.refl u, by simpa [sibsCyc] using hpc, RegsExcept.refl u _, fun A hA => hM A hA⟩
  | succ L ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hpL : t.pc = pcOf (sibAt k L) := by
      rw [pt, show coordAt k + 13 + sibsCyc L = sibAt k L by unfold sibAt sibsCyc; omega]
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega), sibsMem_out M0 c S D k L hcl hsh (by omega) _ (by omega), ← hM _ (by omega)]
      exact hp j hj
    obtain ⟨t', st', pt', rt', mt'⟩ := sib_spec hc k L hk (by omega) t hpL c S D hcl
      (by rw [rt.get (by decide), h8]) (by rw [rt.get (by decide), h9]) (by rw [rt.get (by decide), h19])
      (by rw [rt.get (by decide), h20]) hpt hS hS' hD (by omega) hsh
    have hcyc : sibsCyc L + sibLen L = sibsCyc (L + 1) := by unfold sibsCyc sibLen; split <;> omega
    refine ⟨t', (st.trans st').of_eq hcyc hcyc, ?_, (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    · rw [pt', show sibAt k L + sibLen L = coordAt k + 13 + sibsCyc (L + 1) by
        unfold sibAt; rw [← hcyc]; unfold sibsCyc; omega]
    · have hso := srcOff_bound c L
      rw [mt' A hA, sibsMem_succ M0 c S D k L hcl hsh (by omega) A, mt (S + srcOff c L + 8) (by omega),
        mt (S + srcOff c L) (by omega), mt A hA,
        sibsMem_out M0 c S D k L hcl hsh (by omega) (S + srcOff c L + 8) (Or.inr (by omega)),
        sibsMem_out M0 c S D k L hcl hsh (by omega) (S + srcOff c L) (Or.inr (by omega))]
set_option maxRecDepth 20000 in
theorem coord_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (hp : PlanAt s) (S D : Nat) (h8 : s.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN)
    (hS : S % 16 = 0) (hD : D % 16 = 0) (hDS : D + 896 ≤ S) (hS' : S + 1024 ≤ MEMORY_BYTES)
    (hDP : D + 896 ≤ PLAN) (hsh : 48 * k ≤ D) :
    ∃ t, Steps im s 707 707 t ∧ t.pc = pcOf (coordAt k + 111) ∧
      t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧ t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        holdMem (fun B => s.getMem (BitVec.ofNat 64 B)) (N.toNat / 2 ^ WCT9.childBase k % 128) S k A
          (coordMem (fun B => s.getMem (BitVec.ofNat 64 B)) (N.toNat / 2 ^ WCT9.childBase k % 128) S D k A) := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  obtain ⟨c, hcdef⟩ : ∃ c, c = N.toNat / 2 ^ WCT9.childBase k % 128 := ⟨_, rfl⟩
  rw [← hcdef]
  have hcl : c < 128 := by rw [hcdef]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨t1, s1, p1, r19, r11, r12, r1, g1, f1⟩ := head_spec hc k hk s hpc N hN D h9
  rw [← hcdef] at r19
  obtain ⟨t2, s2, p2, g2, m2⟩ := zero_spec hc t1 p1 D 40 (coordAt k + 6) r11 r12 r1 (by norm_num) (by norm_num)
    (by omega) (by omega)
  obtain ⟨t3, s3, p3, q10, q11, q12, q1, g3, f3⟩ := mid_spec hc k hk t2 p2 S D
    (by rw [g2.get (by decide), g1.get (by decide), h8]) (by rw [g2.get (by decide), g1.get (by decide), h9])
  obtain ⟨t4, s4, p4, g4, m4⟩ := copy_spec hc t3 p3 (S + 448) (D + 320) 72 (coordAt k + 10) q10 q11 q12 q1
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨t5, s5, p5, w20, g5, f5⟩ := row_spec hc k hk t4 p4 c hcl
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), r19])
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h18])
  have hz : ∀ X < 2 ^ 64, t3.getMem (BitVec.ofNat 64 X) = zeroed t1 D 40 X := fun X hX => by
    rw [f3 X hX (fun h => h), m2 X hX]
  have hM5 : ∀ A < 2 ^ 64, t5.getMem (BitVec.ofNat 64 A) =
      zcMem (fun B => s.getMem (BitVec.ofNat 64 B)) S D A := by
    intro A hA
    rw [f5 A hA (fun h => h), m4 A hA]
    unfold copied zcMem
    by_cases h1 : D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0
    · rw [if_pos (show D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0 by omega), if_pos h1,
        hz _ (by omega)]
      unfold zeroed
      rw [if_neg (by omega), f1 _ (by omega) (fun h => h),
        show S + 448 + (A - (D + 320)) = S + 448 + (A - D - 320) by omega]
    · rw [if_neg (show ¬ (D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0) by omega), if_neg h1,
        hz A hA]
      unfold zeroed
      by_cases h2 : D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0
      · rw [if_pos (show D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0 by omega), if_pos h2]
      · rw [if_neg (show ¬ (D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0) by omega), if_neg h2,
          f1 A hA (fun h => h)]
  have hp5 : PlanAt t5 := fun j hj => by
    rw [hM5 _ (by omega)]
    unfold zcMem
    rw [if_neg (show ¬ (D + 320 ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 896 ∧ (PLAN + 8 * j - D - 320) % 8 = 0) by omega),
      if_neg (show ¬ (D ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 320 ∧ (PLAN + 8 * j - D) % 8 = 0) by omega)]
    exact hp j hj
  have e8 : t5.getReg .x8 = BitVec.ofNat 64 S := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h8]
  have e9 : t5.getReg .x9 = BitVec.ofNat 64 D := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h9]
  have e19 : t5.getReg .x19 = BitVec.ofNat 64 c := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), r19]
  obtain ⟨t6, s6, p6, g6, m6⟩ := sibs_spec hc k hk c S D hcl hS (by omega) hD (by omega) (by omega) hsh t5 _ hM5
    p5 e8 e9 e19 w20 hp5 6 le_rfl
  obtain ⟨t6', s6', p6', g6', m6'⟩ := sib6_spec hc k hk t6
    (by rw [p6, show coordAt k + 13 + sibsCyc 6 = sibAt k 6 by unfold sibsCyc sibAt; omega]) c S hcl
    (by rw [g6.get (by decide), e8]) (by rw [g6.get (by decide), e19]) hS (by omega)
  obtain ⟨t7, s7, p7, w8, w9, g7, f7⟩ := step_spec hc k hk t6' p6' S D
    (by rw [g6'.get (by decide), g6.get (by decide), e8]) (by rw [g6'.get (by decide), g6.get (by decide), e9])
  have hzS : ∀ o, o < 448 → t6.getMem (BitVec.ofNat 64 (S + o)) = s.getMem (BitVec.ofNat 64 (S + o)) := by
    intro o ho
    rw [m6 _ (by omega), sibsMem_out _ c S D k 6 hcl hsh le_rfl _ (Or.inr (by omega))]
    unfold zcMem; rw [if_neg (by omega), if_neg (by omega)]
  have hso := srcOff_bound c 6
  refine ⟨t7, (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s6').trans s7).of_eq
    (by unfold sibsCyc; omega) (by unfold sibsCyc; omega), p7, w8, w9,
    (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g6').trans g7).mono (by decide),
    fun A hA => ?_⟩
  rw [f7 A hA (fun h => h), m6' A hA]
  unfold holdMem
  split_ifs
  · rfl
  · rw [show S + srcOff c 6 + 8 = S + (srcOff c 6 + 8) by omega, hzS _ (by omega)]
  · rw [hzS _ (by omega)]
  · rw [m6 A hA]; rfl
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
/-- Hold word `j` (0, 1: top sibling; 2: flag `1 - bit6`) of coordinate `k`, read from the snapshot. -/
def holdW (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) : Word :=
  if j = 0 then M (SNAP + 1024 * k + srcOff (cs k) 6)
  else if j = 1 then M (SNAP + 1024 * k + srcOff (cs k) 6 + 8)
  else BitVec.ofNat 64 (1 - cs k / 2 ^ 6 % 2)
/-- The written hold words of the first `K` coordinates. -/
abbrev InHold (K A : Nat) : Prop :=
  0x380000 ≤ A ∧ A < 0x380000 + 32 * K ∧ (A - 0x380000) % 8 = 0 ∧ (A - 0x380000) % 32 < 24
/-- Memory after the first `K` coordinates (r3w: recursive; coordinate `k ≥ 2` also writes into region `k - 1`). -/
def allMem (M : Nat → Word) (cs : Nat → Nat) : Nat → Nat → Word
  | 0, A => M A
  | K + 1, A => holdMem (allMem M cs K) (cs K) (SNAP + 1024 * K) K A
      (coordMem (allMem M cs K) (cs K) (SNAP + 1024 * K) (0x840 + 896 * K) K A)
def finalWord (M : Nat → Word) (cs : Nat → Nat) (i : Nat) : Word :=
  if i < 8 then M (0x800 + 8 * i)
  else if i < 1016 then
    match sibSrc (cs ((i - 8) / 112)) ((i - 8) % 112) with
    | some o => M (0x840 + 1024 * ((i - 8) / 112) + o)
    | none => if (i - 8) % 112 < 40 then 0 else M (0x840 + 1024 * ((i - 8) / 112) + 448 + 8 * ((i - 8) % 112 - 40))
  else M (0x800 + 8 * (i + 144))
theorem sibSrc_lt {c j o : Nat} (h : sibSrc c j = some o) : o + 8 ≤ 448 ∧ o % 8 = 0 := by
  unfold sibSrc at h
  cases hl : sibLev c j with
  | none => rw [hl] at h; simp at h
  | some l =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have := srcOff_bound c l
    split at h <;> omega
theorem coordMem_congr (M M' : Nat → Word) (c S D k A : Nat) (hDS : D + 896 ≤ S)
    (hS : ∀ o < 1024, M (S + o) = M' (S + o)) (hA : M A = M' A) :
    coordMem M c S D k A = coordMem M' c S D k A := by
  have hz : ∀ o < 1024, zcMem M S D (S + o) = zcMem M' S D (S + o) := fun o ho => by
    unfold zcMem; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact hS o ho
  have hzA : zcMem M S D A = zcMem M' S D A := by
    unfold zcMem
    split_ifs
    · rw [Nat.add_assoc]; exact hS _ (by omega)
    · rfl
    · exact hA
  unfold coordMem sibsMem
  split
  · rename_i l hl
    have := srcOff_bound c l
    split
    · exact hz _ (by omega)
    · rw [Nat.add_assoc]; exact hz _ (by omega)
  · exact hzA
theorem coordMem_out (M : Nat → Word) (c S D k A : Nat) (hc : c < 128) (hk : 48 * k ≤ D)
    (h : A < D - 48 * k ∨ D + 896 ≤ A) : coordMem M c S D k A = M A := by
  unfold coordMem
  rw [sibsMem_out _ c S D k 6 hc hk le_rfl A h]
  unfold zcMem; rw [if_neg (by omega), if_neg (by omega)]
theorem holdMem_congr (M M' : Nat → Word) (c S k A : Nat) (r r' : Word)
    (h1 : M (S + srcOff c 6) = M' (S + srcOff c 6)) (h2 : M (S + srcOff c 6 + 8) = M' (S + srcOff c 6 + 8))
    (hr : r = r') : holdMem M c S k A r = holdMem M' c S k A r' := by
  unfold holdMem; rw [h1, h2, hr]
theorem allMem_out (M : Nat → Word) (cs : Nat → Nat) (hcs : ∀ k, cs k < 128) (K : Nat) (hK : K ≤ 9) (A : Nat)
    (hA : A < 0x840 ∨ 0x840 + 896 * K ≤ A) (hH : ¬ InHold K A) : allMem M cs K A = M A := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hh : holdAt K = 0x380000 + 32 * K := rfl
    simp only [allMem]
    unfold holdMem
    rw [if_neg (fun e => hH (by unfold InHold; omega)), if_neg (fun e => hH (by unfold InHold; omega)),
      if_neg (fun e => hH (by unfold InHold; omega)),
      coordMem_out _ _ _ _ _ _ (hcs K) (by omega) (by omega)]
    exact ih (by omega) (by omega) (fun h => hH (by unfold InHold at h ⊢; omega))
theorem allMem_hold (M : Nat → Word) (cs : Nat → Nat) (hcs : ∀ k, cs k < 128) :
    ∀ K ≤ 9, ∀ k < K, ∀ j < 3, allMem M cs K (holdAt k + 8 * j) = holdW M cs k j := by
  have hSN : SNAP = 0x200000 := rfl
  intro K hK
  induction K with
  | zero => intro k hk; omega
  | succ K ih =>
    intro k hk j hj
    have hh : ∀ k, holdAt k = 0x380000 + 32 * k := fun _ => rfl
    have hso := srcOff_bound (cs K) 6
    simp only [allMem]
    unfold holdMem
    by_cases hkK : k = K
    · rw [hkK]
      unfold holdW
      interval_cases j
      · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos rfl,
          allMem_out _ _ hcs K (by omega) _ (Or.inr (by omega)) (by unfold InHold; omega)]
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos rfl,
          allMem_out _ _ hcs K (by omega) _ (Or.inr (by omega)) (by unfold InHold; omega)]
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by simp only [hh]; omega), if_neg (by simp only [hh]; omega), if_neg (by simp only [hh]; omega),
        coordMem_out _ _ _ _ _ _ (hcs K) (by omega) (Or.inr (by simp only [hh]; omega))]
      exact ih (by omega) k (by omega) j hj
/-- Hold word `j` of coordinate `k` in terms of the first-pass scratch regions at `0x840`. -/
def holdVal (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) : Word :=
  if j = 0 then M (0x840 + 1024 * k + srcOff (cs k) 6)
  else if j = 1 then M (0x840 + 1024 * k + srcOff (cs k) 6 + 8)
  else BitVec.ofNat 64 (1 - cs k / 2 ^ 6 % 2)
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem coords_spec (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf (coordAt 0)) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) (h8 : s.getReg .x8 = BitVec.ofNat 64 SNAP) (h9 : s.getReg .x9 = BitVec.ofNat 64 0x840)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∀ K ≤ 9, ∃ t, Steps im s (707 * K) (707 * K) t ∧ t.pc = pcOf (coordAt K) ∧
      t.getReg .x8 = BitVec.ofNat 64 (SNAP + 1024 * K) ∧ t.getReg .x9 = BitVec.ofNat 64 (0x840 + 896 * K) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        allMem (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  have hSN : SNAP = 0x200000 := rfl
  intro K hK
  induction K with
  | zero =>
    exact ⟨s, Steps.refl s, hpc, by simpa using h8, by simpa using h9, RegsExcept.refl s _, fun A hA => rfl⟩
  | succ K ih =>
    obtain ⟨t, st, pt, t8, t9, rt, mt⟩ := ih (by omega)
    have hcs : ∀ k, N.toNat / 2 ^ WCT9.childBase k % 128 < 128 := fun _ => Nat.mod_lt _ (by norm_num)
    have hNt : OutAt t 0x60 N := fun j hj => by
      rw [mt _ (by omega), allMem_out _ _ hcs K (by omega) _ (Or.inl (by omega)) (by unfold InHold; omega)]
      exact hN j hj
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega), allMem_out _ _ hcs K (by omega) _ (Or.inr (by omega)) (by unfold InHold; omega)]
      exact hp j hj
    obtain ⟨t', st', pt', t8', t9', rt', mt'⟩ := coord_spec hc K (by omega) t pt N hNt hpt (SNAP + 1024 * K)
      (0x840 + 896 * K) t8 t9 (by rw [rt.get (by decide), h18]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), ?_, ?_, ?_, (rt.trans rt').mono (by decide),
      fun A hA => ?_⟩
    · rw [pt', show coordAt K + 111 = coordAt (K + 1) by unfold coordAt; ring]
    · rw [t8', show SNAP + 1024 * K + 1024 = SNAP + 1024 * (K + 1) by ring]
    · rw [t9', show 0x840 + 896 * K + 896 = 0x840 + 896 * (K + 1) by ring]
    · have e := coordMem_congr (fun B => t.getMem (BitVec.ofNat 64 B))
        (allMem (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K)
        (N.toNat / 2 ^ WCT9.childBase K % 128) (SNAP + 1024 * K) (0x840 + 896 * K) K A (by omega)
        (fun o ho => mt _ (by omega)) (mt A hA)
      have hso := srcOff_bound (N.toNat / 2 ^ WCT9.childBase K % 128) 6
      rw [mt' A hA, holdMem_congr _ (allMem (fun B => s.getMem (BitVec.ofNat 64 B))
        (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K) _ _ _ _ _ _ (mt _ (by omega)) (mt _ (by omega)) e]
      rfl
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
set_option maxRecDepth 20000 in
theorem run_spec_framed (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf 41108) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) :
    ∃ t, Steps im s 23576 23576 t ∧ t.pc = pcOf 42142 ∧ RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12,
        .x13, .x18, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      (∀ i < 2729, (i < 8 ∨ 1016 ≤ i) → t.getMem (BitVec.ofNat 64 (0x800 + 8 * i)) =
        finalWord (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i) ∧
      (∀ k < 9, ∀ j < 3, t.getMem (BitVec.ofNat 64 (holdAt k + 8 * j)) =
        holdVal (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) k j) ∧
      ∀ A < 2 ^ 64, (A < 0x800 ∨ 0x800 + 8 * 2729 ≤ A) →
        (A < SNAP ∨ SNAP + 9216 ≤ A) → ¬ InHold 9 A →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  have hSN : SNAP = 0x200000 := rfl
  have hcs : ∀ k, N.toNat / 2 ^ WCT9.childBase k % 128 < 128 := fun _ => Nat.mod_lt _ (by norm_num)
  obtain ⟨u1, s1, p1, a10, a11, a12, a1, g1, f1⟩ := start_spec hc s hpc
  obtain ⟨u2, s2, p2, g2, m2⟩ := copy_spec hc u1 p1 0x840 SNAP 1152 41115 a10 a11 a12 a1 (by norm_num)
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (Or.inr (by omega))
  obtain ⟨u3, s3, p3, b8, b9, b18, g3, f3⟩ := regs_spec hc u2 p2
  have hM3 : ∀ A < 2 ^ 64, u3.getMem (BitVec.ofNat 64 A) = copied u1 0x840 SNAP 1152 A := fun A hA => by
    rw [f3 A hA (fun h => h), m2 A hA]
  have hlo : ∀ A < SNAP, u3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [hM3 A (by omega)]; unfold copied; rw [if_neg (by omega), f1 A (by omega) (fun h => h)]
  have hsn : ∀ o, o < 9216 → o % 8 = 0 →
      u3.getMem (BitVec.ofNat 64 (SNAP + o)) = s.getMem (BitVec.ofNat 64 (0x840 + o)) := fun o ho ho' => by
    rw [hM3 _ (by omega)]; unfold copied
    rw [if_pos (by omega), f1 _ (by omega) (fun h => h), show SNAP + o - SNAP = o by omega]
  have hN3 : OutAt u3 0x60 N := fun j hj => by rw [hlo _ (by omega)]; exact hN j hj
  have hp3 : PlanAt u3 := fun j hj => by
    rw [hM3 _ (by omega)]; unfold copied
    rw [if_neg (by omega), f1 _ (by omega) (fun h => h)]; exact hp j hj
  obtain ⟨u4, s4, p4, c8, c9, g4, m4⟩ := coords_spec hc N u3 p3 hN3 hp3 b8 b9 b18 9 le_rfl
  obtain ⟨u5, s5, p5, d10, d11, d12, d1, g5, f5⟩ := final_spec hc u4 (by rw [p4]; rfl)
  obtain ⟨u6, s6, p6, g6, m6⟩ := copy_spec hc u5 p5 (0x800 + 9280) (0x800 + 8128) 1713 42127 d10 d11 d12 d1
    (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega) (Or.inl (by norm_num))
  obtain ⟨u7, s7, p7, g7, f7⟩ := halt_spec hc u6 p6
  have h4 : ∀ A < 2 ^ 64, u5.getMem (BitVec.ofNat 64 A) =
      allMem (fun B => u3.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) 9 A :=
    fun A hA => by rw [f5 A hA (fun h => h), m4 A hA]
  refine ⟨u7, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).of_eq (by norm_num)
    (by norm_num), p7, (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).mono (by decide)),
    fun i hi hi' => ?_, fun k hk j hj => ?_, fun A hA hA' hSnap hH => ?_⟩
  rotate_left
  · have hH : holdAt k = 0x380000 + 32 * k := rfl
    have hso := srcOff_bound (N.toNat / 2 ^ WCT9.childBase k % 128) 6
    rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
    unfold copied
    rw [if_neg (by omega), h4 _ (by omega), allMem_hold _ _ hcs 9 le_rfl k hk j hj]
    unfold holdW holdVal
    beta_reduce
    split_ifs
    · try dsimp only
      rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · try dsimp only
      rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · rfl
  · rw [f7 A hA (fun h => h), m6 A hA]
    unfold copied
    rw [if_neg (by omega), h4 A hA, allMem_out _ _ hcs 9 le_rfl A (by omega) hH, hM3 A hA]
    unfold copied
    rw [if_neg (by omega), f1 A hA (fun h => h)]
  rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
  unfold copied finalWord
  by_cases ht : 1016 ≤ i
  · rw [if_pos (show 0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0 by omega), if_neg (show ¬ i < 8 by omega),
      if_neg (show ¬ i < 1016 by omega), h4 _ (by omega),
      allMem_out _ _ hcs 9 le_rfl _ (Or.inr (by omega)) (by unfold InHold; omega)]
    rw [hlo _ (by omega),
      show 0x800 + 9280 + (0x800 + 8 * i - (0x800 + 8128)) = 0x800 + 8 * (i + 144) by omega]
  · have h8 : i < 8 := by omega
    rw [if_neg (show ¬ (0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0) by omega), h4 _ (by omega), if_pos h8,
      allMem_out _ _ hcs 9 le_rfl _ (Or.inl (by omega)) (by unfold InHold; omega), hlo _ (by omega)]
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
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC ofNat_sub_one)
set_option linter.unusedSimpArgs false

/-- The whole block at 48000 (18 words). -/
def cPCode : List (BitVec 32) := cPC0 ++ cPCL ++ cPCT
theorem cPCode_length : cPCode.length = 18 := rfl
sym_block RPC0 := symRun cfgC cPC0 (pcOf 48000) 40
sym_block RPCL := symRun cfgC cPCL (pcOf 48001) 40
sym_block RPCT := symRun cfgC cPCT (pcOf 48013) 40

/-- Source offset (in a 128-byte staging block pair) of a written pair offset. -/
def srcOff (r : Nat) : Nat := if r = 16 then 112 else if r = 24 then 120 else if r = 88 then 48 else 56
def isVal (r : Nat) : Prop := r = 16 ∨ r = 24 ∨ r = 88 ∨ r = 96
instance (r : Nat) : Decidable (isVal r) := by unfold isVal; infer_instance
/-- Memory after `i` loop iterations. -/
def pcMem (M : Nat → Word) (src dst i A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 104 * i ∧ isVal ((A - dst) % 104) then
    M (src + 128 * ((A - dst) / 104) + srcOff ((A - dst) % 104)) else M A
/-- Memory after the whole block (21 pairs and chain 0's value). -/
def pairCopyMem (M : Nat → Word) (src dst A : Nat) : Word :=
  if A = dst + 104 * 21 + 48 then M (src + 128 * 21 + 48)
  else if A = dst + 104 * 21 + 56 then M (src + 128 * 21 + 56)
  else pcMem M src dst 21 A

section
variable {im : Image} (hc : Code im)
include hc
set_option maxRecDepth 20000 in
theorem pc_iter (s : MachineState) (hpc : s.pc = pcOf 48001) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1)) (hn : n + 1 < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 128 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 104 ≤ MEMORY_BYTES)
    (hov : dst + 104 ≤ src) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if n = 0 then pcOf 48013 else pcOf 48001) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src + 128) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst + 104) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst + 24 then s.getMem (BitVec.ofNat 64 (src + 120))
        else if A = dst + 16 then s.getMem (BitVec.ofNat 64 (src + 112))
        else if A = dst + 96 then s.getMem (BitVec.ofNat 64 (src + 56))
        else if A = dst + 88 then s.getMem (BitVec.ofNat 64 (src + 48))
        else s.getMem (BitVec.ofNat 64 A)) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RPCL hc.cL s hpc (by
    simp [RPCL.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RPCL.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RPCL.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RPCL.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RPCL.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    cases r <;> simp_all [rv_simp, RPCL.res] <;> rfl
  · intro A hA
    have k24 := ofNat_inj hA (show dst + 24 < 2 ^ 64 by omega)
    have k16 := ofNat_inj hA (show dst + 16 < 2 ^ 64 by omega)
    have k96 := ofNat_inj hA (show dst + 96 < 2 ^ 64 by omega)
    have k88 := ofNat_inj hA (show dst + 88 < 2 ^ 64 by omega)
    simp only [Result.toState_getMem, RPCL.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, h10, h11,
      ofNat_add_ofNat, k24, k16, k96, k88]

structure PCInv (s : MachineState) (src dst i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < 21 then pcOf 48001 else pcOf 48013)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (src + 128 * i)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 104 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (21 - i)
  regs : RegsExcept s t [.x6, .x10, .x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = pcMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst i A

theorem pc_loop (s : MachineState) (hpc : s.pc = pcOf 48001) (src dst : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 21)
    (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∀ i, i ≤ 21 → ∃ t, Steps im s (12 * i) (12 * i) t ∧ PCInv s src dst i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos (by omega)], by simpa using h10, by simpa using h11,
      by simpa using h12, fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold pcMem; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 48001 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u10, u11, u12, ru, mu⟩ := pc_iter hc t hpc' (src + 128 * i) (dst + 104 * i) (20 - i)
      hI.x10 hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : 20 - i = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u10, show src + 128 * i + 128 = src + 128 * (i + 1) by ring]
    · rw [u11, show dst + 104 * i + 104 = dst + 104 * (i + 1) by ring]
    · rw [u12, show 20 - i = 21 - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      have hsrc : ∀ x, x < 128 → t.getMem (BitVec.ofNat 64 (src + 128 * i + x)) =
          s.getMem (BitVec.ofNat 64 (src + 128 * i + x)) := fun x hx => by
        rw [hI.mem _ (by omega)]; unfold pcMem; rw [if_neg (by omega)]
      rw [mu A hA, hsrc 120 (by omega), hsrc 112 (by omega), hsrc 56 (by omega), hsrc 48 (by omega), hI.mem A hA]
      unfold pcMem
      by_cases hn : dst + 104 * i ≤ A ∧ A < dst + 104 * i + 104
      · have hq : (A - dst) / 104 = i := by omega
        have hr : (A - dst) % 104 = A - (dst + 104 * i) := by omega
        by_cases a24 : A = dst + 104 * i + 24
        · subst a24; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a24]
        by_cases a16 : A = dst + 104 * i + 16
        · subst a16; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a16]
        by_cases a96 : A = dst + 104 * i + 96
        · subst a96; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a96]
        by_cases a88 : A = dst + 104 * i + 88
        · subst a88; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a88, if_neg (fun h => by unfold isVal at h; omega), if_neg (fun h => by unfold isVal at h; omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        by_cases hin : dst ≤ A ∧ A < dst + 104 * i ∧ isVal ((A - dst) % 104)
        · rw [if_pos hin, if_pos ⟨hin.1, by omega, hin.2.2⟩]
        · rw [if_neg hin, if_neg (fun h => hin ⟨h.1, by omega, h.2.2⟩)]

set_option maxRecDepth 100000 in
/-- The whole pair copy block: from 48000 back to `ret` (`ra`), 1 + 12 * 21 + 5 = 258 steps. -/
theorem pairCopy_spec (s : MachineState) (hpc : s.pc = pcOf 48000) (src dst ret : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h1 : s.getReg .x1 = pcOf ret)
    (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∃ t, Steps im s 258 258 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = pairCopyMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u12, ur, uf⟩ : ∃ u, Steps im s 1 1 u ∧ u.pc = pcOf 48001 ∧
      u.getReg .x12 = BitVec.ofNat 64 21 ∧ RegsExcept s u [.x12] ∧ Frame s u (fun _ => False) := by
    refine ⟨_, symRun_sound RPC0 hc.c0 s hpc (by simp [RPC0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [RPC0.res, E.eval]
    · simp [RPC0.res, rv_simp] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [RPC0.res, rv_simp] <;> rfl
    · intro A _ _; simp [RPC0.res, rv_simp]
  obtain ⟨t, st, hI⟩ := pc_loop hc u pu src dst (by rw [ur.get (by simp)]; exact h10)
    (by rw [ur.get (by simp)]; exact h11) u12 hs hs' hd hov 21 le_rfl
  have tpc : t.pc = pcOf 48013 := by rw [hI.pc, if_neg (by omega)]
  have hobl : Oblig.all t RPCT.res.st.obl := by
    simp [RPCT.res, rv_simp, accessValid_iff, hI.x10, hI.x11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; omega
  have sT := symRun_sound RPCT hc.cT t tpc hobl
  have hmu : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => uf.get hA (by simp)
  refine ⟨_, ((su.trans st).trans sT).of_eq (by simp [RPCT.res]) (by simp [RPCT.res]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RPCT.res, E.eval]
    rw [hI.regs.get (by simp), ur.get (by simp), h1]
    exact pcOf_and_not1 ret
  · have r3 : RegsExcept t (RPCT.res.toState t) [.x6] := by
      intro r hr; simp at hr; cases r <;> simp_all [RPCT.res, rv_simp] <;> rfl
    exact ((ur.trans hI.regs).trans r3).mono (by simp)
  · intro A hA
    have k48 := ofNat_inj hA (show dst + 104 * 21 + 48 < 2 ^ 64 by omega)
    have k56 := ofNat_inj hA (show dst + 104 * 21 + 56 < 2 ^ 64 by omega)
    have e : ∀ x, x < 128 → t.getMem (BitVec.ofNat 64 (src + 128 * 21 + x)) =
        s.getMem (BitVec.ofNat 64 (src + 128 * 21 + x)) := fun x hx => by
      rw [hI.mem _ (by omega)]; unfold pcMem; rw [if_neg (by omega)]; exact hmu _ (by omega)
    simp only [Result.toState_getMem, RPCT.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, hI.x10,
      hI.x11, ofNat_add_ofNat, k48, k56]
    rw [show src + 128 * 21 + 56 = src + 128 * 21 + 56 from rfl, e 56 (by omega), e 48 (by omega), hI.mem A hA]
    unfold pairCopyMem pcMem
    have hso : srcOff ((A - dst) % 104) ≤ 120 := by unfold srcOff; split_ifs <;> omega
    split_ifs <;> first | rfl | (exact hmu _ (by omega)) | omega
end
end ClaudeWCT.W9.Machine.Expand.PairCopy
end
