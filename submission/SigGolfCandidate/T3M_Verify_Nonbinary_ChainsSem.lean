import SigGolfCandidate.T3M_Verify_ChainSem
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsLayout

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
structure NCtx where
  w : ClaudeWCT.W9.T3M.WBytes
  tree : Nat
  leaf : Nat
  S3 : Nat
  digits : Nat → Nat
  ret : Nat
namespace NCtx
/-- Charge 86: chain `i`'s block (`= WIT + chainBlock 0 i` for `S3 = 14128`). -/
def blk (c : NCtx) (i : Nat) : Nat := c.S3 - 1664 + topSlot i
/-- Address of the supplied value (G: block start, F: block + 48). -/
def vAt (c : NCtx) (i : Nat) : Nat := c.blk i + 48 * (i % 2)
/-- Hash destination of an interior step (G: block - 16, so the high half lands on the value; F: block + 48). -/
def oAt (c : NCtx) (i : Nat) : Nat := c.blk i + 64 * (i % 2) - 16
/-- The two pads (G: +32, +48; F: +0, +32). -/
def pad0At (c : NCtx) (i : Nat) : Nat := c.blk i + 32 - 32 * (i % 2)
def pad1At (c : NCtx) (i : Nat) : Nat := c.blk i + 48 - 16 * (i % 2)
def dig (c : NCtx) (i : Nat) : Nat := c.digits i
def topMax (i : Nat) : Nat := mx (i / 3)
def last (i : Nat) : Nat := topMax i - 1
/-- The half of the step-`m` answer the image keeps (`= WCT9.chainHigh 0 i m`): G chains keep the high half on
interior steps. -/
def topHigh (i m : Nat) : Bool := topG i && decide (m + 1 < topMax i)
def «prefix» (c : NCtx) : Nat := 128 + 193 * 2 ^ 56 + ((c.tree * 2 ^ 12 + c.leaf) % 2 ^ 32) * 2 ^ 16
def w0 (c : NCtx) (i : Nat) : Nat := c.prefix + i
def w1 (c : NCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad0At i - Verify.WIT)
def pad1 (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.pad1At i - Verify.WIT)
def padHeader (c : NCtx) (i : Nat) : Word := (ClaudeWCT.W9.T3M.wdig c.w (c.blk i - Verify.WIT + 16)).extractLsb' 64 64
def val (c : NCtx) (i : Nat) : Digest := ClaudeWCT.W9.T3M.wdig c.w (c.vAt i - Verify.WIT)
def ok (c : NCtx) : Prop :=
  c.tree = 0 ∧ c.leaf < 4096 ∧ c.S3 % 8 = 0 ∧ Verify.WIT + 8336 + 1664 ≤ c.S3 ∧ c.S3 + 2064 ≤ 0x5000 ∧
    c.ret < 209920
def known (c : NCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x30, 7), (.x28, BitVec.ofNat 64 (c.prefix + 385)), (.x8, BitVec.ofNat 64 c.S3), (.x9, BitVec.ofNat 64 0xffbf10), (.x4, 24704)]
def kOf (c : NCtx) (q : Nat) : Nat :=
  c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2)
def qb (c : NCtx) (i : Nat) : Nat := gbase (i/3) (c.kOf (i/3))
def qB (c : NCtx) (i : Nat) : Nat := gB (i/3) (c.kOf (i/3))
def qC (c : NCtx) (i : Nat) : Nat := gC (i/3) (c.kOf (i/3))
def qX (c : NCtx) (i : Nat) : Nat := gX (i/3) (c.kOf (i/3))
def entPc (c : NCtx) (q : Nat) : Nat := entW q (c.kOf q)
/-- Slot index of group 17 (campaign T8D): the top field `d51 + 8 d52` (bits 122..127). -/
def k17 (c : NCtx) : Nat := c.dig 51 + 8 * c.dig 52
/-- Start of the group-17 chain code (chains 51/52 in `BLOCK[k17]`, chain 53 in `SUFFIX[d53]`). -/
def bufferSafe (c : NCtx) (i : Nat) : Prop :=
  c.dig i = topMax i ∧
    (i = 0 ∨ (0 < i ∧ i % 3 ≠ 0 ∧ c.dig (i-1) = topMax (i-1)))
instance (c : NCtx) (i : Nat) : Decidable (c.bufferSafe i) := by
  unfold bufferSafe; infer_instance
def bufferEnd (c : NCtx) (i : Nat) : Nat :=
  slot i + (if i = 0 ∨ c.dig (i-1) = topMax (i-1) then 0 else 16)
def bufferOrig (c : NCtx) (s0 : MachineState) : Prop :=
  ∀ i, i < 54 → ∀ k < 2, OrigW c.w s0 (slot i + 8*k)
def bufferVal (c : NCtx) (i : Nat) : Digest :=
  if c.bufferSafe i then ClaudeWCT.W9.T3M.wdig c.w (slot i - Verify.WIT) else c.val i
def r8Start (c : NCtx) (i : Nat) : Nat :=
  if i = 51 then blkW c.k17 else if i = 52 then blkW c.k17 + partLen 17 (c.dig 51) else sufW (c.dig 53) (decide (c.dig 52=7))
def startPc (c : NCtx) (i : Nat) : Nat :=
  if i < 51 then (if i%3=0 then leadPc (i/3) (c.kOf (i/3)) else if i%3=1 then c.qB i else c.qC i)
  else c.r8Start i
def rungPc (c : NCtx) (i m : Nat) : Nat :=
  if i%3=0 ∧ i < 51 then c.qb i+2*m
  else c.startPc i + (if c.dig i = last i then 2 else 3) + 2*(m-c.dig i)
def endPc (c : NCtx) (i : Nat) : Nat :=
  if i < 51 then (if i%3=0 then c.qB i else if i%3=1 then c.qC i else c.qX i)
  else c.r8Start i + partLen 17 (c.dig i)-(if c.bufferSafe i then 4 else 0)
/-- Bytes written before chain `i` (charge 86): the leaf buffer, the pairs `p < i / 2` (the F chain of pair `p` spills
its junk 16 bytes into pair `p - 1`, chain 1 past the area), and the G half `[pair, pair + 40)` of pair `i / 2` when
`i` is odd. -/
def Wr (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  (slot 0 ≤ A ∧ A < c.bufferEnd i) ∨ (c.S3 + 104 * (27 - i / 2) ≤ A + 1664 ∧ A < c.S3 + 1160) ∨
    (i % 2 = 1 ∧ c.S3 + 104 * (26 - i / 2) ≤ A + 1664 ∧ A + 1664 < c.S3 + 104 * (26 - i / 2) + 40)
/-- Chain `i`'s own writes: its header word and the 32-byte destination of its interior steps. -/
def WrIn (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 24) ∨ (c.oAt i ≤ A ∧ A < c.oAt i + 32)
def Orig0 (c : NCtx) (s0 : MachineState) : Prop :=
  ((∀ i, i < 54 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ c.bufferOrig s0) ∧ Verify.DataOK s0
def Base (c : NCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
def ChainIn (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i ∧ s.pc = pcOf (c.startPc i)
def HdrOk (c : NCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 8 = 128 + i ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i
def StepInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i ∧
    c.HdrOk i s ∧ DigAt s (c.vAt i) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    (m < last i → s.getReg .x12 = BitVec.ofNat 64 (c.oAt i)) ∧ s.pc = pcOf (c.rungPc i m)
def PreHash (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i ∧ DigAt t (c.vAt i) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = last i then slot i else c.oAt i) ∧
    t.pc = pcOf (c.rungPc i m + (if m = last i then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)
def EndInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 ∧ s.pc = pcOf (c.endPc i)
theorem topSlot_props (i : Nat) (hi : i < 54) : topSlot i % 8 = 0 ∧ 16 ≤ topSlot i ∧ topSlot i + 64 ≤ 2808 := by
  unfold topSlot; omega
theorem topG_eq (i : Nat) : topG i = T3.topIsG i := by simp [topG, T3.topIsG]
theorem topG_isG (i : Nat) : topG i = ClaudeWCT.WCT9.isG 0 i := by rw [ClaudeWCT.WCT9.isG_top_eq, topG_eq]
theorem topG_lt (i : Nat) (hi : i < 54) : topG i = decide (i % 2 = 0) := by
  unfold topG; by_cases h : i % 2 = 0 <;> simp [h] <;> omega
theorem topSlot_eq (i : Nat) : topSlot i = ClaudeWCT.W9.T3M.chainSlot 0 i := by
  unfold topSlot ClaudeWCT.W9.T3M.chainSlot; simp only [Fin.val_zero, if_true]; split <;> omega
theorem blk_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    c.blk i % 8 = 0 ∧ Verify.WIT + 8352 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x5000 := by
  obtain ⟨-, -, h64, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold blk Verify.WIT at *; refine ⟨?_, ?_, ?_⟩ <;> omega
/-- Chain `i`'s block lies in pair `i / 2` (`[pair, pair + 104)` with `pair = S3 - 1664 + 104 (26 - i / 2)`). -/
theorem blk_eq (c : NCtx) (i : Nat) (hi : i < 54) :
    c.blk i = c.S3 - 1664 + 104 * (26 - i / 2) + 16 + 24 * (i % 2) := by
  unfold blk topSlot; omega
theorem vAt_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    c.vAt i % 8 = 0 ∧ c.vAt i = c.blk i + 48 * (i % 2) := by
  have hb := c.blk_props hc i hi
  unfold vAt; omega
theorem oAt_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    c.oAt i % 8 = 0 ∧ Verify.WIT + 8336 ≤ c.oAt i ∧ c.oAt i + 32 ≤ 0x5000 ∧
      c.oAt i + 16 = c.blk i + 64 * (i % 2) := by
  have hb := c.blk_props hc i hi
  unfold oAt; omega
theorem oAt_G (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) (hg : topG i = true) : c.oAt i + 16 = c.vAt i := by
  have hb := c.blk_props hc i hi
  rw [topG_lt i hi] at hg; simp at hg
  unfold oAt vAt; omega
theorem oAt_F (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) (hg : topG i = false) : c.oAt i = c.vAt i := by
  have hb := c.blk_props hc i hi
  rw [topG_lt i hi] at hg; simp at hg
  unfold oAt vAt; omega
theorem topHigh_eq (i m : Nat) : topHigh i m = ClaudeWCT.WCT9.chainHigh 0 i m := by
  rw [ClaudeWCT.WCT9.chainHigh_top_eq]
  unfold topHigh T3.topChainHigh
  rw [topG_eq]
  congr 2
  unfold topMax mx maxDigit
  simp only [ite_true]
  by_cases h : i < 51
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]
theorem slot_props (i : Nat) (hi : i < 54) : slot i % 16 = 0 ∧ 25248 ≤ slot i ∧ slot i + 32 ≤ 26128 := by
  unfold slot; omega
theorem base_off (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S3 + (off i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold off blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S3 + topSlot i - 1664 = c.S3 - 1664 + topSlot i by
    omega]
theorem base_off0 (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    BitVec.ofNat 64 c.S3 + off i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  have := topSlot_props i hi
  unfold off blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S3 + topSlot i - 1664 = c.S3 - 1664 + topSlot i by
    omega]
/-- The hash destination register of an interior step (`gOut`). -/
theorem oAt_eval (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) (x : Word) (hx : x = BitVec.ofNat 64 (c.blk i)) :
    x + gOut (topG i) = BitVec.ofNat 64 (c.oAt i) := by
  have hb := c.blk_props hc i hi
  subst hx
  rw [topG_lt i hi]
  unfold oAt
  by_cases h : i % 2 = 0
  · simp only [h, decide_true]
    rw [show gOut true = BitVec.ofNat 64 18446744073709551600 by unfold gOut; rfl, BitVec.ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show c.blk i + 18446744073709551600 = (c.blk i + 64 * 0 - 16) + 2^64 by
      omega, Nat.add_mod_right]
  · simp only [h, decide_false]
    rw [show gOut false = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
    congr 1; omega
theorem prefix_props (c : NCtx) : c.prefix % 2 ^ 16 = 128 ∧ c.prefix < 2 ^ 64 := by
  have h := Nat.mod_lt (c.tree * 2 ^ 12 + c.leaf) (by norm_num : 0 < 2 ^ 32)
  unfold «prefix»
  constructor <;> omega
theorem w0_lt (c : NCtx) (i m : Nat) (hi : i < 54) (hm : m < 256) : c.w0 i + 2 ^ 8 * m < 2 ^ 64 := by
  have h := Nat.mod_lt (c.tree * 2 ^ 12 + c.leaf) (by norm_num : 0 < 2 ^ 32)
  unfold w0 «prefix»; omega
theorem w0_header (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 54) (hm : m < 8) :
    BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) = (chainHeader 0 c.tree c.leaf i m).extractLsb' 0 64 := by
  rw [chainHeader_low_bounded _ _ _ _ _ (by omega) hm
    (by rw [hc.1]; decide +kernel) hc.2.1]
  congr 1
  simp only [w0, «prefix», packedPrefix, packedHi, show height 0 = 12 from rfl, Fin.val_zero,
    Nat.zero_mul, Nat.add_zero]
  ring
set_option maxRecDepth 20000 in
theorem chain_hashInput (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 54) (hm : m < 8) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.pad0At i) (c.pad0 i)) (hp1 : DigAt t (c.pad1At i) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i)
    (hv : DigAt t (c.vAt i) v) :
    hashInput t = toQ (chainInputL 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i)) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputL_length _ _ _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputL, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two]
  rw [topG_lt i hi]
  by_cases hg : i % 2 = 0
  · have ev : c.vAt i = c.blk i := by unfold vAt; omega
    have e0 : c.pad0At i = c.blk i + 32 := by unfold pad0At; omega
    have e1 : c.pad1At i = c.blk i + 48 := by unfold pad1At; omega
    rw [ev] at hv; rw [e0] at hp0; rw [e1] at hp1
    rw [if_pos (by simpa using hg)]
    rw [hv.1, hv.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp0.1, hp0.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hp1.1, hp1.2, w0_header c hc i m hi hm]
    rfl
  · have h1 : i % 2 = 1 := by omega
    have ev : c.vAt i = c.blk i + 48 := by unfold vAt; omega
    have e0 : c.pad0At i = c.blk i := by unfold pad0At; omega
    have e1 : c.pad1At i = c.blk i + 32 := by unfold pad1At; omega
    rw [ev] at hv; rw [e0] at hp0; rw [e1] at hp1
    rw [if_neg (by simpa using hg)]
    rw [hp0.1, hp0.2, show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
      show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
      show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
      show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_header c hc i m hi hm]
    rfl
/-- On the top layer the format of chain `i` is `topG i` (`= WCT9.isG 0 i`). -/
theorem chainInputL_top (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest) :
    chainInputL 0 tree leaf i step p0 p1 headerPad v (topG i) =
      ClaudeWCT.W9.T3M.chainInputPW 0 tree leaf i step p0 p1 headerPad v := by
  unfold chainInputL ClaudeWCT.W9.T3M.chainInputPW; rw [topG_isG]
theorem orig_frame {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : i < 54) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := c.blk_props hc i hi
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1.1 i hi k hk
/-- No chain processed before chain `i` (nor a buffer write) touched chain `i`'s block. -/
theorem notWr_block (c : NCtx) (hc : c.ok) {i A : Nat} (hi : i < 54) (h1 : c.blk i ≤ A) (h2 : A < c.blk i + 64) :
    ¬ c.Wr i A := by
  have hb := c.blk_props hc i hi
  have he := c.blk_eq i hi
  have hs := slot_props 0 (by omega)
  have hlo := hc.2.2.2.1
  unfold Wr
  omega
theorem dig_at {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i A : Nat} (hi : i < 54) (hA1 : c.blk i ≤ A) (hA2 : A + 16 ≤ c.blk i + 64)
    (hA8 : (A - c.blk i) % 8 = 0) (hW0 : ¬ W A) (hW1 : ¬ W (A + 8)) :
    DigAt t A (ClaudeWCT.W9.T3M.wdig c.w (A - Verify.WIT)) := by
  have hb := c.blk_props hc i hi
  have e0 : c.blk i + 8 * ((A - c.blk i) / 8) = A := by omega
  have e1 : c.blk i + 8 * ((A - c.blk i) / 8 + 1) = A + 8 := by omega
  have o0 := orig_frame hF h0 hc hi (k := (A - c.blk i) / 8) (by omega) (by rw [e0]; exact hW0)
  have o1 := orig_frame hF h0 hc hi (k := (A - c.blk i) / 8 + 1) (by omega) (by rw [e1]; exact hW1)
  rw [e0] at o0; rw [e1] at o1
  exact DigAt_origW o0 o1 (by omega)
theorem pads_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : i < 54) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.pad0At i) (c.pad0 i) ∧ DigAt t (c.pad1At i) (c.pad1 i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ A, c.blk i ≤ A → A < c.blk i + 64 → (A < c.blk i + 16 ∨ c.blk i + 24 ≤ A) →
      (i % 2 = 0 → c.blk i + 16 ≤ A) → (i % 2 = 1 → A < c.blk i + 48) → ¬ c.WrIn i A := by
    intro A h1 h2 h3 h4 h5 hw
    rcases hw with hw | hw | hw
    · exact c.notWr_block hc hi h1 h2 hw
    · omega
    · unfold oAt at hw; omega
  unfold pad0 pad1
  have e0 : c.pad0At i = c.blk i + 32 - 32 * (i % 2) := rfl
  have e1 : c.pad1At i = c.blk i + 48 - 16 * (i % 2) := rfl
  rw [e0, e1]
  refine ⟨dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))
      (nW _ (by omega) (by omega) (by omega) (by omega) (by omega)),
    dig_at hF h0 hc hi (by omega) (by omega) (by omega) (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))
      (nW _ (by omega) (by omega) (by omega) (by omega) (by omega))⟩
theorem val_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : i < 54)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.vAt i) (c.val i) := by
  have hb := c.blk_props hc i hi
  unfold val
  have ev : c.vAt i = c.blk i + 48 * (i % 2) := rfl
  rw [ev]
  exact dig_at hF h0 hc hi (by omega) (by omega) (by omega) (c.notWr_block hc hi (by omega) (by omega))
    (c.notWr_block hc hi (by omega) (by omega))
theorem topMax_bounds (i : Nat) : 3 ≤ topMax i ∧ topMax i ≤ 7 := by
  unfold topMax mx; split <;> omega
theorem topMax_hi (i : Nat) (hi : 51 ≤ i) : topMax i = 7 := by
  unfold topMax mx; rw [if_neg (by omega)]
theorem topMax_lo (i : Nat) (hi : i < 51) : topMax i = 4 := by
  unfold topMax mx; rw [if_pos (by omega)]
theorem last_bounds (i : Nat) : 2 ≤ last i ∧ last i ≤ 6 := by
  have := topMax_bounds i; unfold last; omega
theorem rungPc_succ (c : NCtx) (i m : Nat) (hd : c.dig i ≤ m) :
    c.rungPc i (m+1) = c.rungPc i m+2 := by
  unfold rungPc; split_ifs <;> omega
def DigitsOk (c : NCtx) : Prop := ∀i,i<54 → c.dig i ≤ topMax i
theorem dig_group_le (c : NCtx) (hd : c.DigitsOk) (q k : Nat) (hq : q<18) (hk : k<3) :
    c.dig (3*q+k) ≤ mx q := by
  have h := hd (3*q+k) (by omega)
  simpa only [topMax,show (3*q+k)/3=q by omega] using h
theorem kOf_lt (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q < (mx q+1)^3 := by
  have h0 := c.dig_group_le hd q 0 hq (by decide +kernel)
  have h1 := c.dig_group_le hd q 1 hq (by decide +kernel)
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> omega
theorem kOf_digits (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    c.kOf q%(mx q+1)=c.dig (3*q) ∧
    c.kOf q/(mx q+1)%(mx q+1)=c.dig (3*q+1) ∧
    c.kOf q/(mx q+1)^2=c.dig (3*q+2) := by
  have h0 := c.dig_group_le hd q 0 hq (by decide +kernel)
  have h1 := c.dig_group_le hd q 1 hq (by decide +kernel)
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  simp only [Nat.add_zero] at h0
  unfold kOf mx at *
  split_ifs at * <;> exact ⟨by omega,by omega,by omega⟩
theorem kdig_kOf (c : NCtx) (hd : c.DigitsOk) (q : Nat) (hq : q<18) :
    kdig q (c.kOf q) 0=c.dig (3*q) ∧ kdig q (c.kOf q) 1=c.dig (3*q+1) ∧ kdig q (c.kOf q) 2=c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits hd q hq
  have h2 := c.dig_group_le hd q 2 hq (by decide +kernel)
  unfold kdig
  simp only [pow_zero,Nat.div_one,pow_one]
  refine ⟨k1,k2,?_⟩
  rw [k3]; exact Nat.mod_eq_of_lt (by omega)
theorem bufferEnd_bounds (c : NCtx) (i : Nat) :
    slot i ≤ c.bufferEnd i ∧ c.bufferEnd i ≤ slot i + 16 := by
  unfold bufferEnd; split <;> omega

theorem bufferEnd_mono (c : NCtx) (i : Nat) : c.bufferEnd i ≤ c.bufferEnd (i+1) := by
  have h := c.bufferEnd_bounds i
  have h' := c.bufferEnd_bounds (i+1)
  unfold slot at *; omega

theorem Wr_mono (c : NCtx) (i : Nat) :
    ∀ A, c.Wr i A → c.Wr (i+1) A := by
  intro A h
  have hm := c.bufferEnd_mono i
  unfold Wr at *
  rcases h with h | h | h
  · left; omega
  · right; left; omega
  · right; left; omega

/-- Chain `i`'s own writes are among the writes before chain `i + 1`. -/
theorem WrIn_next (c : NCtx) (hc : c.ok) (i A : Nat) (hi : i < 54) (h : c.WrIn i A) : c.Wr (i+1) A := by
  have hlo := hc.2.2.2.1
  rcases h with h | h | h
  · exact c.Wr_mono i A h
  · have he := c.blk_eq i hi
    unfold Wr; right
    by_cases h2 : i % 2 = 0
    · right; omega
    · left; omega
  · have he := c.blk_eq i hi
    unfold oAt at h
    unfold Wr; right
    by_cases h2 : i % 2 = 0
    · right; omega
    · left; omega

theorem Wr_copy (c : NCtx) (i A : Nat)
    (hlo : slot i ≤ A) (hhi : A < slot i + 16) : c.Wr (i+1) A := by
  have h := c.bufferEnd_bounds (i+1)
  unfold Wr slot at *
  left; omega

theorem Wr_hash (c : NCtx) (i A : Nat) (hn : c.dig i ≠ topMax i)
    (hlo : slot i ≤ A) (hhi : A < slot i + 32) : c.Wr (i+1) A := by
  have he : c.bufferEnd (i+1) = slot (i+1)+16 := by
    simp [bufferEnd, hn]
  unfold Wr slot at *
  left; omega

theorem bufferSafe_end (c : NCtx) (i : Nat) (hs : c.bufferSafe i) :
    c.bufferEnd i = slot i := by
  rcases hs.2 with h | h
  · simp [bufferEnd, h]
  · simp [bufferEnd, h.2.2]

theorem bufferSafe_protected (c : NCtx) (i A : Nat) (hs : c.bufferSafe i)
    (hb : c.S3 + 1160 ≤ slot 0) (ha : slot i ≤ A) : ¬ c.Wr i A := by
  rw [Wr, c.bufferSafe_end i hs]
  unfold slot at *
  omega

theorem bufferVal_at {c : NCtx} {s0 t : MachineState} (h0 : c.bufferOrig s0)
    {i : Nat} (hi : i < 54) (hs : c.bufferSafe i)
    (hb : c.S3 + 1160 ≤ slot 0) (hF : Frame s0 t (c.Wr i)) :
    DigAt t (slot i) (c.bufferVal i) := by
  have hp := slot_props i hi
  have o0 := h0 i hi 0 (by omega)
  have o1 := h0 i hi 1 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1
  have f0 := hF (slot i) (by omega) (c.bufferSafe_protected i _ hs hb (by omega))
  have f1 := hF (slot i+8) (by omega) (c.bufferSafe_protected i _ hs hb (by omega))
  have t0 : OrigW c.w t (slot i) := by unfold OrigW at *; rw [f0]; exact o0
  have t1 : OrigW c.w t (slot i+8) := by unfold OrigW at *; rw [f1]; exact o1
  rw [bufferVal, if_pos hs]
  exact DigAt_origW t0 t1 (by unfold Verify.WIT; omega)


theorem bufferSafe_source (c : NCtx) (digits : List Nat)
    (hd : ∀ j, j < 54 → digits.getD j 0 = c.dig j)
    (i : Nat) (hi : i < 54) : c.bufferSafe i ↔ ClaudeWCT.WCT9.safeZeroCopy 0 digits i := by
  have hm : ∀ j, maxDigit 0 j = topMax j := by
    intro j
    unfold maxDigit topMax mx
    simp only [ite_true]
    split_ifs <;> omega
  unfold bufferSafe ClaudeWCT.WCT9.safeZeroCopy
  rw [hd i hi, hm]
  by_cases hz : i = 0
  · simp [hz]
  · rw [hd (i-1) (by omega), hm]
    simp

theorem bufferSlot_source (i : Nat) :
    slot i - Verify.WIT = ClaudeWCT.W9.T3M.leafBufferSlot 0 i := by
  simp [slot, ClaudeWCT.W9.T3M.leafBufferSlot, ClaudeWCT.W9.T3M.leafBufferBase, Verify.WIT]
  omega

theorem bufferVal_source (c : NCtx) (digits : List Nat)
    (hd : ∀ j, j < 54 → digits.getD j 0 = c.dig j)
    (hS : c.S3 = 14128) (i : Nat) (hi : i < 54) :
    c.bufferVal i = ClaudeWCT.W9.T3M.wvalueFor c.w 0 digits i := by
  unfold bufferVal ClaudeWCT.W9.T3M.wvalueFor
  simp only [← c.bufferSafe_source digits hd i hi, bufferSlot_source]
  split
  · rfl
  · unfold val ClaudeWCT.W9.T3M.wvalue
    apply congrArg (ClaudeWCT.W9.T3M.wdig c.w)
    have hv : ClaudeWCT.W9.T3M.valueOff 0 i = 48 * (i % 2) := by
      unfold ClaudeWCT.W9.T3M.valueOff; rw [← topG_isG, topG_lt i hi]
      by_cases h : i % 2 = 0 <;> simp [h] <;> omega
    rw [hv]
    simp only [vAt, blk, hS, ClaudeWCT.W9.T3M.chainBlock, ClaudeWCT.W9.T3M.layerBase,
      ClaudeWCT.W9.T3M.pathSlots, Matrix.cons_val_zero, Verify.WIT, ← topSlot_eq]
    omega

theorem bufferVal_nonmax (c : NCtx) (i : Nat) (h : c.dig i ≠ topMax i) :
    c.bufferVal i = c.val i := by simp [bufferVal, bufferSafe, h]

theorem rungPc_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 54) (hd : c.dig i < topMax i) :
    c.rungPc i (last i) + 3 = c.endPc i := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last; omega
  have hlq : last i+1=mx (i/3) := hl
  by_cases h51 : i < 51
  · obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds (i/3) (by omega)
    have hdq : c.dig i < mx (i/3) := hd
    by_cases h0 : i%3=0
    · have ei : 3*(i/3)=i := by omega
      have hskip : skipA (i/3) (c.kOf (i/3))=false := by
        simp [skipA,k1,ei,Nat.ne_of_lt hdq]
      simp only [rungPc,endPc,qb,qB,h0,h51,true_and,if_true,gB,hskip,Bool.false_eq_true,if_false,Nat.sub_zero]
      unfold last topMax at *
      omega
    · by_cases h1 : i%3=1
      · have ei : 3*(i/3)+1=i := by omega
        have hskip : skipB (i/3) (c.kOf (i/3))=false := by
          simp [skipB,k2,ei,Nat.ne_of_lt hdq]
        simp only [rungPc,endPc,startPc,h0,h1,h51,false_and,if_true,if_false,qC,gC,hskip,Bool.false_eq_true,Nat.sub_zero,k2,ei]
        change c.qB i + (if c.dig i=last i then 2 else 3) + 2*(last i-c.dig i)+3 = c.qB i+partLen (i/3) (c.dig i)
        unfold partLen
        rw [if_neg (Nat.ne_of_lt hdq)]
        split_ifs <;> omega
      · have ei : 3*(i/3)+2=i := by omega
        have hskip : skipC (i/3) (c.kOf (i/3))=false := by
          simp [skipC,k3,ei,Nat.ne_of_lt hdq]
        simp only [rungPc,endPc,startPc,h0,h1,h51,false_and,if_true,if_false,qX,gX,hskip,Bool.false_eq_true,Nat.sub_zero,k3,ei]
        change c.qC i + (if c.dig i=last i then 2 else 3) + 2*(last i-c.dig i)+3 = c.qC i+partLen (i/3) (c.dig i)
        unfold partLen
        rw [if_neg (Nat.ne_of_lt hdq)]
        split_ifs <;> omega
  · have h7 := topMax_hi i (by omega)
    have hn : ¬ c.bufferSafe i := fun h => Nat.ne_of_lt hd h.1
    simp only [rungPc,endPc,startPc,h51,and_false,if_false,hn,Nat.sub_zero]
    unfold partLen
    simp only [mx,show ¬ (17:Nat)<17 by decide,if_false]
    have hd7 : c.dig i < 7 := by omega
    simp only [if_neg (Nat.ne_of_lt hd7)]
    split_ifs <;> omega
theorem posE_eval (c : NCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i m : Nat) (hm : m ≤ last i) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hm3 : m ≤ 6 := by have := last_bounds i; omega
  interval_cases m
  · rfl
  · exact kr .x7 1 (by simp [known]) (by decide +kernel)
  · exact kr .x13 2 (by simp [known]) (by decide +kernel)
  · exact kr .x19 3 (by simp [known]) (by decide +kernel)
  · exact kr .x20 4 (by simp [known]) (by decide +kernel)
  · exact kr .x21 5 (by simp [known]) (by decide +kernel)
  · exact kr .x26 6 (by simp [known]) (by decide +kernel)
theorem w0_low (c : NCtx) (i m : Nat) (hi : i < 54) (hm : m < 256) :
    (BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m)).toNat % 2 ^ 8 = 128 + i ∧
      (BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m)).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt c i m hi hm)]
  have hp := c.prefix_props
  unfold w0; constructor <;> omega
theorem w0_low0 (c : NCtx) (i : Nat) (hi : i < 54) :
    (BitVec.ofNat 64 (c.w0 i)).toNat % 2 ^ 8 = 128 + i ∧
      (BitVec.ofNat 64 (c.w0 i)).toNat / 2 ^ 16 = c.prefix / 2 ^ 16 := by
  have := w0_low c i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this
def tableJump (c : NCtx) (i : Nat) : Nat := if (i%3=0 ∧ i<51) ∧ rowInl (i/3) (c.kOf (i/3))=false then 1 else 0
def chainCost (c : NCtx) (i d : Nat) : Nat :=
  if d=topMax i then (if c.bufferSafe i then 0 else 4+c.tableJump i)
  else 4+c.tableJump i+9*(topMax i-d)-(if d+1=topMax i then 1 else 0)
def chainsCost (c : NCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => c.chainCost j (c.dig j)).sum
end NCtx
end SigGolfCandidate.T3M.Nonbinary
